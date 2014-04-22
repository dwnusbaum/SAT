module Types ( SAT (..)
             , State (..)
             , Conflict (..)
             , LiteralTrail
             , Formula
             , Clause
             , Literal
             , XorEquation(..)
             ) where

import Data.Map (Map)
import Data.Set (Set)

data SAT
   = SAT
   | UNSAT
   deriving (Eq, Show)

type Literal = Int
type Clause  = [Literal]
type Formula = [Clause]

type LiteralTrail = [(Literal, Bool)]

data Conflict = C
   { cMap     :: Map   Literal Bool -- Map of literals in conflict
   , cPartial :: Set   Literal      -- Set of literals from lower decision levels
   , cLast    :: Maybe Literal      -- Last asserted literal of cNot
   , cNum     :: !Int               -- Number of literals at currentLevel of litTrail
   }
   deriving (Show)

data State = S
   { formula  :: !Formula
   , litTrail :: !LiteralTrail
   , conflict :: Conflict
   , reasons  :: Map Literal Clause
   }
   deriving (Show)

data XorEquation = XEq Clause Bool

instance Show XorEquation where
    show (XEq c b) = "[" ++ unwords (map show c) ++ " | " ++ show b ++ "]"
