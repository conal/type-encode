{-# LANGUAGE TypeOperators, Rank2Types, ConstraintKinds, FlexibleContexts, CPP #-}
{-# LANGUAGE ViewPatterns, TupleSections #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable #-}
{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

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

module TypeEncode.Plugin (plugin) where

-- TODO: Thin imports.

import Prelude hiding (id,(.))

import Control.Category (Category(..))
import Data.Monoid (Monoid(..))
import Data.Functor ((<$>))
import Data.Foldable (Foldable(..))
import Control.Monad ((<=<))
import Control.Arrow (arr,(>>>),second)
import Data.List (intercalate,isSuffixOf)
import Data.Maybe (fromMaybe,isJust)
import Text.Printf (printf)

-- GHC
import PrelNames (eitherTyConName)

import HERMIT.Monad (newIdH,HermitM)
import HERMIT.Context (BoundVars,HasGlobalRdrEnv(..),HermitC)
import HERMIT.Core (Crumb(..),localFreeIdsExpr,CoreProg(..),bindsToProg,progToBinds)
-- Note that HERMIT.Dictionary re-exports HERMIT.Dictionary.*
import HERMIT.Dictionary
  ( observeR,findIdT,callNameT
  , rulesR,inlineR,inlineNamesR,simplifyR
  , letFloatLetR,letFloatTopR,letElimR,cleanupUnfoldR
  , etaExpandR, betaReduceR, letNonRecSubstSafeR
  , callDataConT, callSaturatedT
  -- , unshadowR   -- May need this one later
  )
import HERMIT.External (External,external,ExternalName,ExternalHelp)
import HERMIT.GHC hiding (mkStringExpr)
import HERMIT.Kure hiding (apply)
import HERMIT.Plugin (hermitPlugin,phase,interactive)

import TypeEncode.Encode (encode,decode)

{--------------------------------------------------------------------
    Misc
--------------------------------------------------------------------}

-- | Unary transformation
type Unop a = a -> a

-- | Binary transformation
type Binop a = a -> Unop a

infixl 1 <--

-- | Add post- and pre-processing
(<--) :: Category cat =>
         (b `cat` b') -> (a' `cat` a) -> ((a `cat` b) -> (a' `cat` b'))
(h <-- f) g = h . g . f

data Tree a = Leaf a | Branch (Tree a) (Tree a)
  deriving (Show,Functor,Foldable)

toTree :: [a] -> Tree a
toTree []  = error "toTree: empty list"
toTree [a] = Leaf a
toTree xs = Branch (toTree l) (toTree r)
 where
   (l,r) = splitAt (length xs `div` 2) xs

foldT :: Binop a -> Tree a -> a
foldT (#) = h
 where
   h (Leaf a)     = a
   h (Branch u v) = h u # h v

#if 0

-- I could almost use fold along with EitherTy and PairTy monoids, each
-- newtype-wrapping Type:

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

#endif

{--------------------------------------------------------------------
    Core utilities
--------------------------------------------------------------------}

apps :: Id -> [Type] -> [CoreExpr] -> CoreExpr
apps f ts es
  | tyArity f /= length ts =
      error $ printf "apps: Id %s wants %d type arguments but got %d."
                     (var2String f) arity ntys
  | otherwise = mkCoreApps (varToCoreExpr f) (map Type ts ++ es)
 where
   arity = tyArity f
   ntys  = length ts

tyArity :: Id -> Int
tyArity = length . fst . splitForAllTys . varType

apps' :: String -> [Type] -> [CoreExpr] -> TranslateU CoreExpr
apps' s ts es = (\ i -> apps i ts es) <$> findIdT s

tyNumArgs :: Type -> Int
tyNumArgs (FunTy    _ ty')       = 1 + tyNumArgs ty'
tyNumArgs (ForAllTy _ ty')       = 1 + tyNumArgs ty'
tyNumArgs (coreView -> Just ty') = tyNumArgs ty'
tyNumArgs _                      = 0

uqVarName :: Var -> String
uqVarName = uqName . varName

exprType' :: CoreExpr -> Type
exprType' (Type {}) = error "exprType': given a Type"
exprType' e = exprType e

isType :: CoreExpr -> Bool
isType (Type {}) = True
isType _         = False

pairTy :: Binop Type
pairTy a b = mkBoxedTupleTy [a,b]

tcApp0 :: TyCon -> Type
tcApp0 tc = TyConApp tc []

tcApp1 :: TyCon -> Unop Type
tcApp1 tc a = TyConApp tc [a]

tcApp2 :: TyCon -> Binop Type
tcApp2 tc a b = TyConApp tc [a,b]

{--------------------------------------------------------------------
    HERMIT utilities
--------------------------------------------------------------------}

type ReExpr = RewriteH CoreExpr
type ReCore = RewriteH Core

-- Common context & monad constraints
type OkCM c m =
  ( HasDynFlags m, Functor m, MonadThings m, MonadCatch m
  , BoundVars c, HasGlobalRdrEnv c )

type TranslateU b = forall c m a. OkCM c m => Translate c m a b

-- | Lookup the name in the context first, then, failing that, in GHC's global
-- reader environment.
findTyConT :: String -> TranslateU TyCon
findTyConT nm =
  prefixFailMsg ("Cannot resolve name " ++ nm ++ ", ") $
  contextonlyT (findTyConMG nm)

findTyConMG :: OkCM c m => String -> c -> m TyCon
findTyConMG nm c =
    case filter isTyConName $ findNamesFromString (hermitGlobalRdrEnv c) nm of
      [n] -> lookupTyCon n
      ns  -> do dynFlags <- getDynFlags
                fail $ show (length ns) 
                     ++ " matches found: "
                     ++ intercalate ", " (showPpr dynFlags <$> ns)

tcFind :: (TyCon -> b) -> String -> TranslateU b
tcFind h = fmap h . findTyConT

tcFind0 :: String -> TranslateU Type
tcFind0 = tcFind tcApp0

tcFind1 :: String -> TranslateU (Unop Type)
tcFind1 = tcFind tcApp1

tcFind2 :: String -> TranslateU (Binop Type)
tcFind2 = tcFind tcApp2

{--------------------------------------------------------------------
    Rewrites
--------------------------------------------------------------------}

encName :: Unop String
encName = ("TypeEncode.Encode." ++)

appsE :: String -> [Type] -> [CoreExpr] -> TranslateU CoreExpr
appsE = apps' . encName

callNameEnc :: String -> TranslateH CoreExpr (CoreExpr, [CoreExpr])
callNameEnc = callNameT . encName

encodeOf :: Type -> Type -> CoreExpr -> TranslateU CoreExpr
encodeOf ty ty' e = appsE "encode" [ty,ty'] [e]

decodeOf :: Type -> Type -> CoreExpr -> TranslateU CoreExpr
decodeOf ty ty' e = appsE "decode" [ty',ty] [e]

encodeR :: Type -> Type -> ReExpr
encodeR ty ty' = idR >>= encodeOf ty ty'

decodeR :: Type -> Type -> ReExpr
decodeR ty ty' = idR >>= decodeOf ty ty'

-- e --> decode (encode e)
decodeEncodeR :: ReExpr
decodeEncodeR = do e   <- idR
                   guardMsg (not (isType e)) "Given a Type expression"
                   let ty = exprType' e
                   ty' <- encodeTy ty
                   decodeR ty ty' . encodeR ty ty'

-- encode @a @b u --> ((a,b),u) (with type arguments)
unEncode' :: TranslateH CoreExpr ((Type,Type),CoreExpr)
unEncode' = do (_encode, [Type a, Type b, arg]) <- callNameEnc "encode"
               return ((a,b),arg)

-- decode @a @b u --> ((a,b),u) (with type arguments)
unDecode' :: TranslateH CoreExpr ((Type,Type),CoreExpr)
unDecode' = do (_decode, [Type a, Type b, arg]) <- callNameEnc "decode"
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

-- Do I want to encode Bool? For now, no.

mkEither :: TranslateU (Binop Type)
mkEither = tcFind2 "Data.Either.Either"

isStandardTy :: Type -> Bool
isStandardTy ty = any ($ ty) [isPairTy,isEitherTy,isUnitTy,isBoolTy]

encodeCon :: [Type] -> DataCon -> Type
encodeCon tcTys con | null argTys = unitTy
                    | otherwise   = foldT pairTy (toTree argTys)
 where
   (tvs,body) = splitForAllTys (dataConRepType con)
   argTys     = substTysWith tvs tcTys (fst (splitFunTys body))

encodeCons :: [Type] -> [DataCon] -> TranslateU Type
encodeCons _ [] =
  do voidTC <- findTyConT "TypeEncode.Encode.Void"
     return (TyConApp voidTC [])
encodeCons tcTys cons =
  do eitherTC <- findTyConT "Data.Either.Either"
     let eitherTy a b = TyConApp eitherTC [a,b]
     return (foldT eitherTy (encodeCon tcTys <$> toTree cons))

encodeTy :: Type -> TranslateU Type
encodeTy (coreView -> Just ty)                    = encodeTy ty
encodeTy (isStandardTy -> True)                   = fail "Already a standard type"
encodeTy (TyConApp (tyConDataCons -> cons) tcTys) = encodeCons tcTys cons
encodeTy _                                        = fail "encodeTy: not handled"

#if 0
-- encode (C a ... z) --> ...
encodeConApp :: ReExpr
encodeConApp = unEncode
           >>> accepterR (arr (not . isType)) >>> callDataConT
           >>> arr (\ (dc, tys, args) ->
                      findCon dc tys args
                        (tyConDataCons (dataConOrigTyCon dc)))

findCon :: DataCon -> [Type] -> [CoreExpr] -> [DataCon] -> CoreExpr

findCon dc tys args =
  fromMaybe (error "findCon: Didn't find data con") . find . toTree
 where
   find :: Tree DataCon -> Maybe CoreExpr
   find (Leaf dc') | dc == dc' = return undefined
                   | otherwise = Nothing
   find (Branch l r) =
     (foo <$> find l) `mplus` (bar <$> find r)

-- TODO: Combine reConstruct and encodeConApp dropping the unEncode', and adding
-- a decodeR.
#endif

-- Not a function and not a forall
groundType :: Type -> Bool
groundType (coreView -> Just ty) = groundType ty
groundType (FunTy {})            = False
groundType (ForAllTy {})         = False
groundType _                     = True

acceptGroundTyped :: ReExpr
acceptGroundTyped = 
  acceptWithFailMsgR (not . isType)           "Given a Type" >>>
  acceptWithFailMsgR (groundType . exprType') "Not ground"
              
-- | Rewrite a constructor application, eta-expanding if necessary.
-- Must be saturated with type and value arguments.
reConstruct :: ReExpr
reConstruct = acceptGroundTyped >>>
              do (dc, _tys, _args) <- callDataConT
                 guardMsg (not (isBoxyDC dc)) "Boxed"
                 decodeEncodeR

-- TODO: Eta-expand as necessary
-- TODO: After I fix encodeTy, maybe drop some guards in reConstruct.

isBoxyDC :: DataCon -> Bool
isBoxyDC = isSuffixOf "#" . uqName . dataConName

dcAllCons :: DataCon -> [DataCon]
dcAllCons = tyConDataCons . dataConTyCon

{--------------------------------------------------------------------
    Plugin
--------------------------------------------------------------------}

plugin :: Plugin
plugin = hermitPlugin (phase 0 . interactive externals)

externC :: Injection a Core =>
           ExternalName -> RewriteH a -> String -> External
externC name rew help = external name (promoteR rew :: ReCore) [help]

externals :: [External]
externals =
  [ externC "decode-encode" decodeEncodeR "e --> decode (encode e)"
  , externC "re-construct" reConstruct "v --> decode (encode v)"
  ]
