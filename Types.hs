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

import Data.Map.Strict (Map)
import Data.Set        (Set)

data SAT
   = SAT
   | UNSAT
   | UNDEF
   deriving (Eq, Show)

type Literal = Int
type Clause  = [Literal]
type Formula = [Clause]

data LiteralTrail = T
   { litList :: [(Literal, Bool)]
   , litSet  :: Set Literal -- S.fromList $ map fst listList == litList
   }
   deriving (Show)

data Conflict = C
   { cMap     :: Map Literal Bool   -- Map of literals in conflict
   , cPartial :: Set Literal        -- Set of literals from lower decision levels
   , cLast    :: Maybe Literal      -- Last asserted literal of cNot
   , cNum     :: Int                -- Number of literals at currentLevel of litTrail
   }
   deriving (Show)

data State = S
   { formula    :: Formula
   , unitsQueue :: Clause
   , litTrail   :: LiteralTrail
   , conflict   :: Conflict
   , reasons    :: Map Literal Clause
   , variables  :: Set Literal
   }
   deriving (Show)

data XorEquation = XEq Clause Bool

instance Show XorEquation where
    show (XEq c b) = "[" ++ unwords (map show c) ++ " | " ++ show b ++ "]"
