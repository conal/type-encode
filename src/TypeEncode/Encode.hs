{-# LANGUAGE ExplicitForAll, EmptyDataDecls, TypeOperators #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  TypeEncode.Encode
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Simple interface for encoding & decoding types.
----------------------------------------------------------------------

module TypeEncode.Encode (EncodeCat(..),encodeF,decodeF,Void) where

class EncodeCat k where
  encode :: forall a b. a `k` b
  decode :: forall b a. b `k` a

instance EncodeCat (->) where
  encode = encodeF
  decode = decodeF

-- TODO: Eliminate the names "encodeF" and "decodeF" when I know how to
-- construct dictionaries in Core. Meanwhile, use those names in TypeEncode.Plugin.

encodeF :: forall a b. a -> b
encodeF = error "encode: not eliminated"
{-# NOINLINE encodeF #-}

decodeF :: forall b a. b -> a
decodeF = error "decode: not eliminated"
{-# NOINLINE decodeF #-}

-- The foralls here indicate the type argument order needed by the plugin.

data Void

-- TODO: Is there a standard version of Void somewhere convenient?

-- void :: Void
-- void = error "void"
