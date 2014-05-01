{-# OPTIONS_GHC -Wall #-}

module Types ( SAT (..)
             , State (..)
             , Conflict (..)
             , LiteralTrail(..)
             , Formula
             , Clause
             , Literal
             , XorEquation(..)
             ) where

import Data.IntMap.Strict (IntMap)
import Data.Set           (Set)
import Data.Vector        (Vector, toList)

data SAT
   = SAT
   | UNSAT
   | UNDEF
   deriving (Eq, Show)

type Literal = Int
type Clause  = Vector Literal
type Formula = [Clause]

data LiteralTrail = T
   { litList :: [(Literal, Bool)]
   , litSet  :: Set Literal -- S.fromList $ map fst listList == litList
   }
   deriving (Show)

data Conflict = C
   { cClause  :: Clause  -- Conflict analysis clause
   , c1stLast :: Literal -- Last asserted literal of $ map negate getC
   , c2ndLast :: Literal -- Second to last asserted literal of $ map negate getC
   , cNum     :: Int     -- Number of literals of (map negate c) at currentLevel of litTrail
   }
   deriving (Show)

data State = S
   { formula       :: Formula
   , unitsQueue    :: Set Literal
   , litTrail      :: LiteralTrail
   , conflict      :: Conflict
   , conflictFlag  :: Bool
   , conflictCause :: Clause
   , reasons       :: IntMap Clause
   , variables     :: Set Literal -- Absolute value of literals in the formula
   }
   deriving (Show)

data XorEquation = XEq Clause Bool

instance Show XorEquation where
    show (XEq c b) = "[" ++ unwords (map show $ toList c) ++ " | " ++ show b ++ "]"
