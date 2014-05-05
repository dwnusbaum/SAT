{-# OPTIONS_GHC -Wall #-}

module Main(main) where

import ParseDimacs
import SAT

main :: IO ()
main = do
    cnf <- parseDimacsFile "/Users/devin/Downloads/sat/sat-2002-beta/submitted/aloul/Bart/bart10.shuffled.cnf"
    case cnf of
        Left err -> print err
        Right val -> print . solveFormula $ val
