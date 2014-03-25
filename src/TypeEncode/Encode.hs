{-# LANGUAGE ExplicitForAll #-}
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

module TypeEncode.Encode (encode,decode) where

-- TODO: Maybe move encode & decode to a type class, after I know how to insert
-- dictionaries. Or leave it alone.

encode :: forall a b. a -> b
encode = error "encode: not eliminated"
{-# NOINLINE encode #-}

decode :: forall b a. b -> a
decode = error "decode: not eliminated"
{-# NOINLINE decode #-}

-- The foralls here indicate the type argument order needed by the plugin.
