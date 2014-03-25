{-# LANGUAGE TypeOperators, Rank2Types, ConstraintKinds #-}
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
-- Type-encode algebraic types
----------------------------------------------------------------------

module TypeEncode.Plugin (plugin) where

-- TODO: Thin imports.

import Prelude hiding (id,(.))

import Control.Category (Category(..))
import Data.Functor ((<$>))
import Control.Monad ((<=<),liftM)
import Control.Arrow (arr,(>>>))
import Data.List (intercalate)
import Text.Printf (printf)

import HERMIT.Monad (newIdH)
import HERMIT.Context (BoundVars,HasGlobalRdrEnv(..))
import HERMIT.Core (Crumb(..),localFreeIdsExpr,CoreProg(..),bindsToProg,progToBinds)
import HERMIT.External (External,external)
import HERMIT.GHC hiding (mkStringExpr)
import HERMIT.Kure hiding (apply)
-- Note that HERMIT.Dictionary re-exports HERMIT.Dictionary.*
import HERMIT.Dictionary
  ( observeR,findIdT,callNameT
  , rulesR,inlineR,inlineNamesR,simplifyR,letFloatLetR,letFloatTopR,letElimR,cleanupUnfoldR
  , etaExpandR, betaReduceR, letNonRecSubstSafeR
  -- , unshadowR   -- May need this one later
  )
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

{--------------------------------------------------------------------
    HERMIT utilities
--------------------------------------------------------------------}

type ReExpr = RewriteH CoreExpr
type ReCore = RewriteH Core

-- Common context & monad constraints
type OkCM c m =
  (HasDynFlags m, MonadThings m, MonadCatch m, BoundVars c, HasGlobalRdrEnv c)

type TranslateU b = forall c m a. OkCM c m => Translate c m a b

{--------------------------------------------------------------------
    Rewrites
--------------------------------------------------------------------}

encName :: Unop String
encName = ("TypeEncode.Encode." ++)

appsE :: String -> [Type] -> [CoreExpr] -> TranslateU CoreExpr
appsE = apps' . encName

callNameEnc :: String -> TranslateH CoreExpr (CoreExpr, [CoreExpr])
callNameEnc = callNameT . encName

-- encode u --> u
unEncode :: ReExpr
unEncode = do (_encodeE, [Type _, arg]) <- callNameEnc "encode"
              return arg
-- decode e --> e
unDecode :: ReExpr
unDecode = do (_decodeE, [Type _, body]) <- callNameEnc "decode"
              return body

-- encode (decode e) --> e
encodeDecode :: ReExpr
encodeDecode = unEncode >>> unDecode

encodedTy :: Type -> TranslateU Type
encodedTy = error "encodedTy: not implemented"

encodeOf :: Type -> CoreExpr -> TranslateU CoreExpr
encodeOf ty e = do ty' <- encodedTy ty
                   appsE "encode" [ty,ty'] [e]

decodeOf :: Type -> CoreExpr -> TranslateU CoreExpr
decodeOf ty e = do ty' <- encodedTy ty
                   appsE "decode" [ty',ty] [e]


-- -- | Rewrite a constructor application, eta-expanding if necessary.
-- reCtor :: ReExpr
-- reCtor 

{--------------------------------------------------------------------
    Plugin
--------------------------------------------------------------------}

plugin :: Plugin
plugin = hermitPlugin (phase 0 . interactive externals)

externals :: [External]
externals = []

