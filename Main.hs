{-# OPTIONS_GHC -Wall -Werror #-}

module Main(main) where

import SAT

main :: IO ()
main = print . solve $ paper1
