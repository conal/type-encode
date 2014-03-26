{-# LANGUAGE TypeOperators, Rank2Types, ConstraintKinds, FlexibleContexts #-}
{-# LANGUAGE ViewPatterns, TupleSections #-}
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
import Data.Functor ((<$>))
import Control.Monad ((<=<),liftM)
import Control.Arrow (arr,(>>>))
import Data.List (intercalate,isSuffixOf)
import Data.Maybe (isJust)
import Text.Printf (printf)

-- GHC

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

infixl 1 <--

-- | Add post- and pre-processing
(<--) :: Category cat =>
         (b `cat` b') -> (a' `cat` a) -> ((a `cat` b) -> (a' `cat` b'))
(h <-- f) g = h . g . f

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
apps' s ts es = (\ i -> apps i ts es) `liftM` findIdT s

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

{--------------------------------------------------------------------
    HERMIT utilities
--------------------------------------------------------------------}

type ReExpr = RewriteH CoreExpr
type ReCore = RewriteH Core

-- Common context & monad constraints
type OkCM c m =
  (HasDynFlags m, MonadThings m, MonadCatch m, BoundVars c, HasGlobalRdrEnv c)

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
                   ty' <- encodedTy ty
                   decodeR ty ty' . encodeR ty ty'

-- encode u --> u
unEncode :: ReExpr
unEncode = do (_encode, [Type _, arg]) <- callNameEnc "encode"
              return arg
-- decode e --> e
unDecode :: ReExpr
unDecode = do (_decode, [Type _, body]) <- callNameEnc "decode"
              return body

-- encode (decode e) --> e
unEncodeDecode :: ReExpr
unEncodeDecode = unEncode >>> unDecode

-- Stub: For now encode ty as () -> ty
encodedTy :: Type -> TranslateU Type
encodedTy ty = return (FunTy unitTy ty)

-- encodedTy = error "encodedTy: not implemented"

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
-- TODO: After I fix encodedTy, maybe drop some guards in reConstruct.

isBoxyDC :: DataCon -> Bool
isBoxyDC = isSuffixOf "#" . uqName . dataConName

-- Find a data ctor for the given Id and all of the ctors for its type
idDataCons :: Id -> Maybe (DataCon,[DataCon])
idDataCons x | isId x = dataCons (idDetails x)
 where
   dataCons :: IdDetails -> Maybe (DataCon,[DataCon])
   dataCons (DataConWorkId con) =
     (con,) <$> tyConDataCons_maybe (dataConTyCon con)
   dataCons _                   = Nothing
idDataCons _ = Nothing

-- idIsCtor :: Id -> Bool
-- idIsCtor = isJust . idDataCons

-- detailsIsCtor (DataConWrapId _) = True

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
