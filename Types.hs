{-# OPTIONS_GHC -Wall #-}

module Types ( SAT (..)
             , State (..)
             , Conflict (..)
             , LiteralTrail(..)
             , Literal
             , Clause
             , ClauseIndex
             , Formula
             , WatchList
             ) where

import Data.IntMap.Strict (IntMap)
import Data.Set           (Set)
import Data.Vector        (Vector)

data SAT
   = SAT
   | UNSAT
   | UNDEF
   deriving (Eq, Show)

type Literal      = Int
type Clause       = Vector Literal
type ClauseIndex  = Int
type Formula      = Vector Clause
type WatchList    = IntMap [Int]

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
   { formula       :: Formula       -- The entire boolean formula
   , litTrail      :: LiteralTrail  -- The assigned literal trail
   , watchList     :: IntMap [Int]  -- From literal to clause indices in which that lit is watched
   , watch1        :: IntMap Int    -- From clause index to 1st watched literal in clause
   , watch2        :: IntMap Int    -- From clause index to 2nd watched literal in clause
   , unitsQueue    :: Set Literal   -- The queue of unit literals that need to be propogated
   , conflict      :: Conflict      -- Stores details about the conflict while resolving it
   , conflictCause :: Clause        -- The clause that caused a conflict (if null no conflict)
   , reasons       :: IntMap Clause -- Reasons for propogating a literal
   , variables     :: Set Literal   -- Absolute value of literals in the formula
   }
   deriving (Show)
