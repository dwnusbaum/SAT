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
             , decisionLevel
             , prefixToLevel
             , lastAssertedLiteral
             , addToTrail
             ) where

import Data.IntMap.Strict (IntMap)
import Data.Set           (Set)
import Data.Vector        (Vector)

import qualified Data.IntMap.Strict as M (alter, elems, findWithDefault, insert, partitionWithKey)
import qualified Data.Set           as S (insert, member, singleton, unions)
import qualified Data.Vector        as V (elem)

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
   { currentLevel :: Int
   , trail        :: IntMap [Literal]
   , levelSets    :: IntMap (Set Literal)
   , trailSet     :: Set Literal
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

-- Literal Trail methods

decisionLevel :: LiteralTrail -> Literal -> Int
decisionLevel (T n _ lms _) l = go n
  where go 0 = 0
        go x
          | S.member l $ unsafeFind x lms = x
          | otherwise = go (x-1)

prefixToLevel :: LiteralTrail -> Int -> LiteralTrail
prefixToLevel (T _ lt lms _) i = T i trail' levSet' trailSet'
  where (trail' , _) = M.partitionWithKey (\k _ -> k <= i) lt
        (levSet', _) = M.partitionWithKey (\k _ -> k <= i) lms
        trailSet'    = S.unions $ M.elems levSet'

-- Preconditon: There is at least one literal in c that is asserted in the lit trail
lastAssertedLiteral :: LiteralTrail -> Clause -> Literal
lastAssertedLiteral (T n lt _ _) c = go n
  where go x = case filter (`V.elem` c) $ unsafeFind x lt of
                   []    -> go (x-1)
                   (l:_) -> l

addToTrail :: LiteralTrail -> Literal -> Bool -> LiteralTrail
addToTrail (T n lt lms ms) l True  = T { currentLevel = n + 1
                                       , trail        = M.insert (n+1) [l] lt
                                       , levelSets    = M.insert (n+1) (S.singleton l) lms
                                       , trailSet     = S.insert l ms
                                       }
addToTrail (T n lt lms ms) l False = T { currentLevel = n
                                       , trail        = M.alter (Just . maybe [l] (l :)) n lt
                                       , levelSets    = M.alter (Just . maybe (S.singleton l) (S.insert l)) n lms
                                       , trailSet     = S.insert l ms
                                       }

unsafeFind :: (Show a) => Int -> IntMap a -> a
unsafeFind i m = M.findWithDefault (error $ "unsafeFind: Element not found: " ++ show i ++ " in " ++ show m) i m
