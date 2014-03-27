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
import GHC.Tuple ()
import Data.Either ()
import qualified TypeEncode.Encode

q :: Int
q = 3

t0 :: ()
t0 = ()

t1 :: Bool
t1 = True

t2 :: [Int]
t2 = [1,2,3]

t3 :: [Bool]
t3 = [True,False]

t4 :: (Int,Int)
t4 = (3,4)

t5 :: (Int,Int,Int,Int,Int)
t5 = (3,4,5,6,7)

data A = B Int | C () Bool () Int | Y Int | Z ()

t6 :: A
t6 = C () True () 3

data D = D

t7 :: D
t7 = D

data E a = E a a

t8 :: E Bool
t8 = E False True

t9 :: E ()
t9 = E () ()

fizzle :: String
fizzle = "fizzle"

newtype F a = F (a,a)

-- The next two fail. Appartently callDataConT doesn't work for newtype
-- constructors. Investigate.

t10 :: F Bool
t10 = F (False,True)

t11 :: F ()
t11 = F ((),())

