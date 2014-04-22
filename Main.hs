{-# OPTIONS_GHC -Wall #-}

module Main(main) where

import SAT
import ParseDimacs

main :: IO ()
main = do
    cnf <- parseDimacsFile "/Users/devin/Downloads/sat/aloul-chnl11-13.cnf" -- "/Users/devin/Downloads/sat/appli/SAT_RACE08/cnf/aloul-chnl11-13.cnf"
    case cnf of
        Left err -> print err
        Right val -> print $ solveFormula val
