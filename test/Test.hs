-- {-# LANGUAGE #-}
{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Test
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Test the plugin. To run:
-- 
--   hermit Test.hs -v0 -opt=TypeEncode.Plugin +Test Auto.hss
--   
----------------------------------------------------------------------

module Test where

-- Needed for resolving names. Is there an alternative?
import qualified TypeEncode.Encode

t1 :: Bool
t1 = True

t2 :: [Int]
t2 = [1,2,3]

