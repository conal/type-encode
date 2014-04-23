{-# LANGUAGE TypeOperators, Rank2Types, ConstraintKinds, FlexibleContexts, CPP #-}
{-# LANGUAGE ViewPatterns, TupleSections #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fcontext-stack=34 #-}  -- for N32

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  TypeEncode.Plugin
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Type-encode algebraic types. To test, compile and
-- 
--   cd ../../test; hermit Test.hs -v0 -opt=TypeEncode.Plugin +Test Auto.hss
----------------------------------------------------------------------

-- #define OnlyLifted

module TypeEncode.Plugin
  ( -- * Core utilities
    apps, apps', callSplitT, callNameSplitT, unCall, unCall1
    -- * HERMIT utilities
  , liftedKind, unliftedKind
  , ReExpr, ReCore, OkCM, TransformU, findTyConT
    -- * Type encoding
  , encodeOf, decodeOf
  , reCaseR, reConstructR, encodeTypesR, plugin
  , externals
  ) where

import Prelude hiding (id,(.),foldr)

import Control.Category (Category(..))
import Data.Functor ((<$>))
import Data.Foldable (Foldable(..))
import Control.Monad (mplus)
import Control.Arrow (Arrow(..),(>>>))
import Data.List (intercalate)
#ifdef OnlyLifted
import Data.List (isSuffixOf)
#endif
import Data.Maybe (fromMaybe)
import Text.Printf (printf)
import Control.Monad.IO.Class (MonadIO)

-- GHC
import Unique(hasKey)
import PrelNames (
  liftedTypeKindTyConKey,unliftedTypeKindTyConKey,constraintKindTyConKey,
  eitherTyConName)

import HERMIT.Monad (newIdH,HasModGuts(..),HasHscEnv(..))
import HERMIT.Context (BoundVars)
-- Note that HERMIT.Dictionary re-exports HERMIT.Dictionary.*
import HERMIT.Dictionary (findIdT, callT, callNameT, callDataConT)
-- import HERMIT.Dictionary (traceR)
import HERMIT.External (External,external,ExternalName)
import HERMIT.GHC hiding (FastString(..))
import HERMIT.Kure hiding (apply)
import HERMIT.Plugin (hermitPlugin,phase,interactive)

{--------------------------------------------------------------------
    Misc
--------------------------------------------------------------------}

-- | Unary transformation
type Unop a = a -> a

-- | Binary transformation
type Binop a = a -> Unop a

-- Binary leaf tree. Used to construct balanced nested sum and product types.
data Tree a = Empty | Leaf a | Branch (Tree a) (Tree a)
  deriving (Show,Functor,Foldable)

toTree :: [a] -> Tree a
toTree []  = Empty
toTree [a] = Leaf a
toTree xs  = Branch (toTree l) (toTree r)
 where
   (l,r) = splitAt (length xs `div` 2) xs

foldMapT :: b -> (a -> b) -> Binop b -> Tree a -> b
foldMapT e l b = h
 where
   h Empty        = e
   h (Leaf a)     = l a
   h (Branch u v) = b (h u) (h v)

foldT :: a -> Binop a -> Tree a -> a
foldT e b = foldMapT e id b

#if 0

-- I could almost use fold (from Data.Foldable) along with EitherTy and PairTy
-- monoids, each newtype-wrapping Type:

newtype PairTy = PairTy Type

instance Monoid PairTy where
  mempty = PairTy unitTy
  PairTy u `mappend` PairTy v = PairTy (u `pairTy` v)

newtype EitherTy = EitherTy Type

instance Monoid EitherTy where
  mempty = EitherTy voidTy
  EitherTy u `mappend` EitherTy v = EitherTy (u `eitherTy` v)

-- Sadly, voidTy and eitherTy require looking up names. I'm tempted to use
-- unsafePerformIO to give pure interfaces to all of these lookups.
-- However, I don't know how, since I'm using TransformU rather than IO.

#endif

{--------------------------------------------------------------------
    Core utilities
--------------------------------------------------------------------}

-- Form an application to type and value arguments.
apps :: Id -> [Type] -> [CoreExpr] -> CoreExpr
apps f ts es
  | tyArity f /= length ts =
      error $ printf "apps: Id %s wants %d type arguments but got %d."
                     (var2String f) arity ntys
  | otherwise = mkCoreApps (varToCoreExpr f) (map Type ts ++ es)
 where
   arity = tyArity f
   ntys  = length ts

-- Note: With unlifted types, mkCoreApps might make a case expression.
-- If we don't want to, maybe use mkApps.

-- Number of type arguments.
tyArity :: Id -> Int
tyArity = length . fst . splitForAllTys . varType

-- exprType gives an obscure warning when given a Type expression.
exprType' :: CoreExpr -> Type
exprType' (Type {}) = error "exprType': given a Type"
exprType' e         = exprType e

isType :: CoreExpr -> Bool
isType (Type {}) = True
isType _         = False

pairTy :: Binop Type
pairTy a b = mkBoxedTupleTy [a,b]

tcApp0 :: TyCon -> Type
tcApp0 tc = TyConApp tc []

tcApp2 :: TyCon -> Binop Type
tcApp2 tc a b = TyConApp tc [a,b]

isPairTy :: Type -> Bool
isPairTy (TyConApp tc [_,_]) = isBoxedTupleTyCon tc
isPairTy _                   = False

isEitherTy :: Type -> Bool
isEitherTy (TyConApp tc [_,_]) = tyConName tc == eitherTyConName
isEitherTy _                   = False

isUnitTy :: Type -> Bool
isUnitTy (TyConApp tc []) = tc == unitTyCon
isUnitTy _                = False

isBoolTy :: Type -> Bool
isBoolTy (TyConApp tc []) = tc == boolTyCon
isBoolTy _                = False

#ifdef OnlyLifted

dcUnboxedArg :: DataCon -> Bool
dcUnboxedArg = isSuffixOf "#" . uqName . dataConName

-- TODO: use unliftedType instead of dcUnboxedArg.

#endif

liftedKind :: Kind -> Bool
liftedKind (TyConApp tc []) =
  any (tc `hasKey`) [liftedTypeKindTyConKey, constraintKindTyConKey]
liftedKind _                = False

unliftedKind :: Kind -> Bool
unliftedKind (TyConApp tc []) = tc `hasKey` unliftedTypeKindTyConKey
unliftedKind _                = False

-- TODO: Switch to isLiftedTypeKind and isUnliftedTypeKind from Kind (in GHC).
-- When I tried earlier, I lost my inlinings. Investigate!
-- <https://github.com/conal/type-encode/issues/1>

#ifdef OnlyLifted

unliftedType :: Type -> Bool
unliftedType = unliftedKind . typeKind

#endif

splitTysVals :: [Expr b] -> ([Type], [Expr b])
splitTysVals (Type ty : rest) = first (ty :) (splitTysVals rest)
splitTysVals rest             = ([],rest)

{--------------------------------------------------------------------
    HERMIT utilities
--------------------------------------------------------------------}

-- Common context & monad constraints
-- type OkCM c m =
--   ( HasDynFlags m, Functor m, MonadThings m, MonadCatch m
--   , BoundVars c, HasModGuts m )

type OkCM c m = 
  ( BoundVars c, Functor m, HasDynFlags m, HasModGuts m, HasHscEnv m
  , MonadCatch m, MonadIO m, MonadThings m )

type TransformU b = forall c m a. OkCM c m => Transform c m a b

-- Apply a named id to type and value arguments.
apps' :: String -> [Type] -> [CoreExpr] -> TransformU CoreExpr
apps' s ts es = (\ i -> apps i ts es) <$> findIdT s

type ReExpr = RewriteH CoreExpr
type ReCore = RewriteH Core

-- | Lookup the name in the context first, then, failing that, in GHC's global
-- reader environment.
findTyConT :: String -> TransformU TyCon
findTyConT nm =
  prefixFailMsg ("Cannot resolve name " ++ nm ++ "; ") $
  contextonlyT (findTyConMG nm)

#if 0

findTyConMG :: OkCM c m => String -> c -> m TyCon
findTyConMG nm c =
    case filter isTyConName $ findNamesFromString (hermitGlobalRdrEnv c) nm of
      [n] -> lookupTyCon n
      ns  -> do dynFlags <- getDynFlags
                fail $ show (length ns) 
                     ++ " matches found: "
                     ++ intercalate ", " (showPpr dynFlags <$> ns)

#else

findTyConMG :: OkCM c m => String -> c -> m TyCon
findTyConMG nm _ =
  do rdrEnv <- mg_rdr_env <$> getModGuts
     case filter isTyConName $ findNamesFromString rdrEnv nm of
       [n] -> lookupTyCon n
       ns  -> do dynFlags <- getDynFlags
                 fail $ show (length ns) 
                      ++ " matches found: "
                      ++ intercalate ", " (showPpr dynFlags <$> ns)


-- TODO: remove context argument, simplify OkCM, etc. See where it leads.
-- <https://github.com/conal/type-encode/issues/2>

#endif

tcFind :: (TyCon -> b) -> String -> TransformU b
tcFind h = fmap h . findTyConT

tcFind0 :: String -> TransformU Type
tcFind0 = tcFind tcApp0

tcFind2 :: String -> TransformU (Binop Type)
tcFind2 = tcFind tcApp2

callSplitT :: MonadCatch m =>
              Transform c m CoreExpr (CoreExpr, [Type], [Expr CoreBndr])
callSplitT = do (f,args) <- callT
                let (tyArgs,valArgs) = splitTysVals args
                return (f,tyArgs,valArgs)

callNameSplitT :: MonadCatch m => String
               -> Transform c m CoreExpr (CoreExpr, [Type], [Expr CoreBndr])
callNameSplitT name = do (f,args) <- callNameT name
                         let (tyArgs,valArgs) = splitTysVals args
                         return (f,tyArgs,valArgs)

-- TODO: refactor with something like HERMIT's callPredT

-- | Uncall a named function
unCall :: String -> TransformH CoreExpr [CoreExpr]
unCall f = do (_f,_tys,args) <- callNameSplitT f
              return args

-- | Uncall a named function of one argument
unCall1 :: String -> ReExpr
unCall1 f = do [e] <- unCall f
               return e

-- mkVoid :: TransformU CoreExpr
-- mkVoid = Var <$> findIdT (encName "void")

mkUnit :: TransformU CoreExpr
mkUnit = return (mkCoreTup [])

mkPair :: TransformU (Binop CoreExpr)
mkPair = return $ \ u v  -> mkCoreTup [u,v]

mkPairTree :: TransformU ([CoreExpr] -> CoreExpr)
mkPairTree = do unit <- mkUnit
                pair <- mkPair
                return (foldT unit pair . toTree)

-- TODO: mkUnit, mkPair, mkPairTree needn't be in TransformU
-- <https://github.com/conal/type-encode/issues/3>

mkLR :: String -> TransformU (Type -> Type -> Unop CoreExpr)
mkLR name = do f <- findIdT name
               return $ \ tu tv a -> apps f [tu,tv] [a]

mkLeft  :: TransformU (Type -> Type -> Unop CoreExpr)
mkLeft  = mkLR "Left"

mkRight :: TransformU (Type -> Type -> Unop CoreExpr)
mkRight = mkLR "Right"

mkEither :: TransformU (Binop Type)
mkEither = tcFind2 "Data.Either.Either"

mkVoidTy :: TransformU Type
mkVoidTy = tcFind0 "TypeEncode.Encode.Void"

{--------------------------------------------------------------------
    Rewrites
--------------------------------------------------------------------}

encName :: Unop String
encName = ("TypeEncode.Encode." ++)

appsE :: String -> [Type] -> [CoreExpr] -> TransformU CoreExpr
appsE = apps' . encName

callNameEnc :: String -> TransformH CoreExpr (CoreExpr, [CoreExpr])
callNameEnc = callNameT . encName

encodeOf :: Type -> Type -> CoreExpr -> TransformU CoreExpr
encodeOf ty ty' e = do -- guardMsg (not (unliftedType ty')) "encodeOf: unlifted type"
                       appsE "encodeF" [ty,ty'] [e]

decodeOf :: Type -> Type -> CoreExpr -> TransformU CoreExpr
decodeOf ty ty' e = do -- guardMsg (not (unliftedType ty)) "decodeOf: unlifted type"
                       appsE "decodeF" [ty',ty] [e]

-- Those guards don't really fit. I want to ensure that no constructed
-- expressions are of unlifted types.

standardTy :: Type -> Bool
standardTy (coreView -> Just ty) = standardTy ty
standardTy ty = any ($ ty) [isPairTy,isEitherTy,isUnitTy]  -- ,isBoolTy

#if 0

-- Old code. Remove after handling 'case' expressions.

-- e --> decode (encode e)
decodeEncodeR :: ReExpr
decodeEncodeR = do e <- idR
                   guardMsg (not (isType e)) "Given a Type expression"
                   let ty = exprType' e
                   ty' <- encodeTy ty
                   decodeR ty ty' . encodeR ty ty'
-- TODO: Drop decodeEncodeR

encodeTy :: Type -> TransformU Type
encodeTy (coreView -> Just ty) = encodeTy ty
encodeTy (standardTy -> True)  = fail "Already a standard type"
encodeTy (TyConApp tc tcTys)   = do enc <- mkEncodeDCs
                                    return (enc tcTys (tcCons tc))
encodeTy _                     = fail "encodeTy: not handled"

type EncodeDCsT = [Type] -> Tree DataCon -> Type

mkEncodeDCs :: TransformU EncodeDCsT
mkEncodeDCs = liftM2 encodeDCs mkVoidTy mkEither

encodeDCs :: Type -> Binop Type -> EncodeDCsT
encodeDCs voidTy eitherTy tcTys dcs =
  foldT voidTy eitherTy (encodeDC tcTys <$> dcs)

#endif

-- encode @a @b u --> ((a,b),u) (with type arguments)
unEncode' :: TransformH CoreExpr ((Type,Type),CoreExpr)
unEncode' = do (_encode, [Type a, Type b, arg]) <- callNameEnc "encodeF"
               return ((a,b),arg)

-- decode @a @b u --> ((a,b),u) (with type arguments)
unDecode' :: TransformH CoreExpr ((Type,Type),CoreExpr)
unDecode' = do (_decode, [Type a, Type b, arg]) <- callNameEnc "decodeF"
               return ((a,b),arg)

-- encode u --> u (without type arguments)
unEncode :: ReExpr
unEncode = snd <$> unEncode'

-- decode e --> e (without type arguments)
unDecode :: ReExpr
unDecode = snd <$> unDecode'

-- encode (decode e) --> e
unEncodeDecode :: ReExpr
unEncodeDecode = unEncode >>> unDecode

-- To encode Bool also, remove isBoolTy from standardTy.

tcCons :: TyCon -> Tree DataCon
tcCons = toTree . tyConDataCons

encodeDC :: [Type] -> DataCon -> Type
encodeDC tcTys dc = foldT unitTy pairTy (toTree argTys)
 where
   (tvs,body) = splitForAllTys (dataConRepType dc)
   argTys     = substTysWith tvs tcTys (fst (splitFunTys body))

-- Given a constructor application of a "nonstandard", ground type, construct
-- its sum-of-products encoding and the type of that encoding.
findCon :: TransformH (DataCon, [Type], [CoreExpr]) (Type,CoreExpr)
findCon =
  do (dc, tys, args) <- idR
#ifdef OnlyLifted
     guardMsg (not (dcUnboxedArg dc)) "Unboxed constructor argument"
#endif
     inside          <- ($ args) <$> mkPairTree
     voidTy          <- mkVoidTy
     eitherTy        <- mkEither
     lft             <- mkLeft
     rht             <- mkRight
     let find :: Tree DataCon -> (Type,Maybe CoreExpr)
         find = foldMapT e l b
          where
            e = (voidTy,Nothing)
            l dc' = ( encodeDC tys dc'
                    , if dc == dc' then Just inside else Nothing )
            b (tl,mbl) (tr,mbr) =
              (eitherTy tl tr, (lft tl tr <$> mbl) `mplus` (rht tl tr <$> mbr))
     return $
       second (fromMaybe (error "findCon: Didn't find data con")) $
         find (tcCons (dataConTyCon dc))

-- Not a function and not a forall
groundType :: Type -> Bool
groundType (coreView -> Just ty) = groundType ty
groundType (FunTy {})            = False
groundType (ForAllTy {})         = False
groundType _                     = True

acceptGroundTyped :: RewriteH Type
acceptGroundTyped =
  acceptWithFailMsgR (      groundType) "Not ground"    >>>
  acceptWithFailMsgR (not . standardTy) "Already a standard type"

-- | Rewrite a constructor application, eta-expanding if necessary.
-- Must be saturated with type and value arguments.
reConstructR :: ReExpr
reConstructR = acceptWithFailMsgR (not . isType) "Given a Type"  >>>
               (arr exprType' &&& id) >>> encodeCon >>> decodeCon
 where
   encodeCon :: TransformH (Type,CoreExpr) (Type,(Type,CoreExpr))
   encodeCon = acceptGroundTyped *** (callDataConT >>> findCon)
   decodeCon :: TransformH (Type,(Type,CoreExpr)) CoreExpr
   decodeCon = do (ty,(ty',e)) <- idR
                  decodeOf ty ty' e

-- TODO: Eta-expand as necessary
-- <https://github.com/conal/type-encode/issues/4>

-- mkEitherF :: TransformU (Binop CoreExpr)
-- mkEitherF = error "mkEitherF: not yet implemented"

-- Build a tree of either applications and return the domain of the resulting
-- function. The range is given.
mkEitherTree :: Type -> Tree CoreExpr -> TransformU (Type,CoreExpr)
mkEitherTree ran funs =
  do eitherF  <- findIdT "either"
     eitherTy <- mkEither 
     let eithers :: Tree CoreExpr -> (Type,CoreExpr)
         eithers Empty          = error "empty either"  -- What to do here?
         eithers (Leaf f)       = (fst (splitFunTy (exprType' f)), f)
         eithers (Branch fs gs) =
           (eitherTy domf domg, apps eitherF [domf,ran,domg] [f,g])
          where
            (domf,f) = eithers fs
            (domg,g) = eithers gs
     return (eithers funs)

-- either :: forall a c b. (a -> c) -> (b -> c) -> Either a b -> c

case1 :: CoreExpr -> Tree Var -> CoreExpr -> TransformH a CoreExpr
case1 scrut Empty rhs =
  do wild <- constT (newIdH "wild" (exprType' scrut))
     return $
       Case scrut wild (exprType' rhs) [(DataAlt unitCon,[],rhs)]
case1 _ (Leaf _) _ = error "case1: Leaf"
case1 scrut (Branch (Leaf u) (Leaf v)) rhs =
  do wild <- constT (newIdH "wild" (exprType' scrut))
     return $
       Case scrut wild (exprType' rhs) [(DataAlt pairCon,[u,v],rhs)]
case1 scrut (Branch (Leaf u) vs) rhs =
  do v <- constT (newIdH "v" (varsType vs))
     rhsv <- case1 (Var v) vs rhs
     case1 scrut (Branch (Leaf u) (Leaf v)) rhsv
case1 scrut (Branch us (Leaf v)) rhs =
  do u <- constT (newIdH "u" (varsType us))
     rhsu <- case1 (Var u) us rhs
     case1 scrut (Branch (Leaf u) (Leaf v)) rhsu
case1 scrut (Branch us vs) rhs =
  do u <- constT (newIdH "u" (varsType us))
     rhsu <- case1 (Var u) us rhs
     v <- constT (newIdH "v" (varsType vs))
     rhsv <- case1 (Var v) vs rhsu
     case1 scrut (Branch (Leaf u) (Leaf v)) rhsv
 
-- TODO: Refactor much more neatly!
-- <https://github.com/conal/type-encode/issues/5>

varsType :: Tree Var -> Type
varsType = foldT unitTy pairTy . fmap varType

reCaseR :: ReExpr
reCaseR =
  do Case scrut _wild bodyTy alts <- idR
     let scrutTy = exprType' scrut
         (_,tyArgs) = splitAppTys scrutTy
         reAlt :: CoreAlt -> TransformH a CoreExpr
         reAlt (DataAlt con, vars, rhs) =
           do 
#ifdef OnlyLifted
              let lifteds = (not . unliftedType . varType) <$> vars
              guardMsg (and lifteds) "reCaseR: unlifted type"
#endif
              case vars of
                [var] -> return (Lam var rhs)
                _     -> do z <- constT (newIdH "z" (encodeDC tyArgs con))
                            Lam z <$> case1 (Var z) (toTree vars) rhs
         reAlt _ = fail "Alternative is not a DataAlt"
     guardMsg (not (standardTy scrutTy)) "Already a standard type"
     (scrutTy',alts') <- mkEitherTree bodyTy =<< (toTree <$> mapM reAlt alts)
     scrut' <- encodeOf scrutTy scrutTy' scrut
     return (App alts' scrut')

-- TODO: check for use of _wild
-- <https://github.com/conal/type-encode/issues/6>

-- TODO: Check that all constructors are present.
-- <https://github.com/conal/type-encode/issues/7>

unitCon, pairCon :: DataCon
unitCon = tupleCon BoxedTuple 0
pairCon = tupleCon BoxedTuple 2

-- lamPairTree = error "lamPairTree: Please implement"

-- -- | Apply a rewrite at most n times.
-- tryN :: MonadCatch m => Int -> Unop (Rewrite c m b)
-- tryN n = foldr (\ r rest -> tryR (r >>> rest)) idR . replicate n

{--------------------------------------------------------------------
    Plugin
--------------------------------------------------------------------}

plugin :: Plugin
plugin = hermitPlugin (phase 0 . interactive externals)

-- | Combination of type-decoding transformations.
encodeTypesR :: ReExpr
encodeTypesR = reConstructR <+ reCaseR

externC :: Injection a Core =>
           ExternalName -> RewriteH a -> String -> External
externC name rew help = external name (promoteR rew :: ReCore) [help]

externals :: [External]
externals =
  [ externC "un-encode-decode" unEncodeDecode "encode (decode e) -> e"
  , externC "re-construct" reConstructR "encode constructor application"
  , externC "re-case" reCaseR "encode case expression"
  , externC "encode-types" encodeTypesR
     "encode case expressions and constructor applications"
  -- , externC "decode-encode" decodeEncodeR "e --> decode (encode e)"
--   , external "try-n" ((\ n r -> promoteExprR (tryN n r)) :: Int -> ReExpr -> ReCore)
--       ["Apply a rewrite at most n times"]
  ]
