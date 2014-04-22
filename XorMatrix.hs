{-# OPTIONS_GHC -Wall #-}

module XorMatrix where

import Types

{- BE CAREFUL WITH THIS
instance Num Bool where
    (+) = (||)
    (-) = undefined
    (*) = (&&)
    abs    = error "abs doesn't make sense for bools"
    signum = error "signum doesn't make sense for bools"
    negate = not
    fromInteger 0 = False
    fromInteger _ = True
-}

data Matrix
   = M [XorEquation]

instance Show Matrix where
    show (M [])     = "[]"
    show (M (x:[])) = show x
    show (M (x:xs)) = show x ++ "\n" ++ show (M xs)

rref :: Matrix -> Matrix
rref = undefined
