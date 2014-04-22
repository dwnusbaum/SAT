{-# OPTIONS_GHC -Wall #-}

module Main(main) where

import SAT
import ParseDimacs

main :: IO ()
main = do
    cnf <- parseDimacsFile "/Users/devin/Downloads/sc13-benchmarks-random/sat/threshold/3SAT/unif-k3-r4.267-v3200-c13654-S2409522417937001450.cnf"
    case cnf of
        Left err -> print err
        Right val -> print $ solveFormula val
