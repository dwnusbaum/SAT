{-# OPTIONS_GHC -Wall #-}

module Main(main) where

import System.Environment (getArgs)
import System.Exit        (ExitCode(..), exitFailure, exitSuccess, exitWith)

import ParseDimacs
import SAT
import Types

main :: IO ()
main = do
    [cnfPath] <- getArgs
    cnf <- parseDimacsFile cnfPath
    case cnf of
        Left err -> print err >> exitWith (ExitFailure 65) --Input file was incorrectly formatted
        Right val -> case solveFormula val of
                         (_, UNSAT) -> putStrLn "Unsatisfiable"   >> exitFailure
                         (_,   SAT) -> putStrLn "Satisfiable"     >> exitSuccess
                         (_, UNDEF) -> putStrLn "Undefined error" >> exitFailure
