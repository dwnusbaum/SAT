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

import qualified Data.Foldable      as F (foldl')
import qualified Data.IntMap.Strict as M (alter, delete, findWithDefault, insert)
import qualified Data.Set           as S (delete, fromList, insert, member)
import qualified Data.Vector        as V (toList)

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
decisionLevel (T n lt _) l = go n
  where go 0 = 0
        go x
          | l `elem` unsafeFind x lt = x
          | otherwise = go (x-1)

prefixToLevel :: LiteralTrail -> Int -> LiteralTrail
prefixToLevel t0 i = go t0
  where go t1@(T n lt ms)
          | n == i = t1
          | otherwise = go $ T (n-1) (M.delete n lt) $ F.foldl' (\st l -> S.delete l st) ms (unsafeFind n lt)

-- Preconditon: There is at least one literal in c that is asserted in the lit trail
lastAssertedLiteral :: LiteralTrail -> Clause -> Literal
lastAssertedLiteral (T n lt _) c = go n
  where go x = case filter (`S.member` c') $ unsafeFind x lt of
                   []    -> go (x-1)
                   (l:_) -> l
        c' = S.fromList . V.toList $ c

addToTrail :: LiteralTrail -> Literal -> Bool -> LiteralTrail
addToTrail (T n lt ms) l True  = T (n+1) (M.insert (n+1) [l] lt) (S.insert l ms)
addToTrail (T n lt ms) l False = T n (M.alter (Just . maybe [l] (l :)) n lt) (S.insert l ms)

unsafeFind :: (Show a) => Int -> IntMap a -> a
unsafeFind i m = M.findWithDefault (error $ "unsafeFind: Element not found: " ++ show i ++ " in " ++ show m) i m
