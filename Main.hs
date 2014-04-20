{-# OPTIONS_GHC -Wall #-}

module Main(main) where

import SAT

main :: IO ()
main = print . solveFormula $ [[1]]
