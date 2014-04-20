{-# OPTIONS_GHC -Wall #-}

-- Implemented from http://poincare.matf.bg.ac.rs/~filip/phd/sat-tutorial.pdf
-- This solver uses techniques through v.4 of the sovler in that paper

module SAT( Sat(..)
          , State(..)
          , Conflict(..)
          , LiteralTrail
          , Formula
          , Clause
          , Literal
          , solve
          , solveFormula
          , contradicts
          , satisfies
          ) where

import Control.Arrow (first)
import Data.Map (Map)
import Data.Maybe (fromJust, listToMaybe)
import Data.Set (Set)
--import Debug.Trace(trace, traceShow)

import qualified Data.List as L
import qualified Data.Map  as M
import qualified Data.Set  as S

data Sat
   = SAT
   | UNSAT
   deriving (Eq, Show)

type Literal = Int
type Clause = [Literal]
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

vars :: Formula -> [Literal]
vars = S.toList . S.unions . map (S.fromList . map abs)

-- Literal Trail methods

decisions :: LiteralTrail -> [Literal]
decisions = fmap fst . filter snd

decisionsTo :: LiteralTrail -> Literal -> [Literal]
decisionsTo []          _ = []
decisionsTo ((x, b):xs) l
  | x == l    = [l | b] -- If b is true, then [l], else []
  | b         = x : decisionsTo xs l
  | otherwise = decisionsTo xs l

currentLevel :: LiteralTrail -> Int
currentLevel = length . decisions

decisionLevel :: LiteralTrail -> Literal -> Int
decisionLevel ls = length . decisionsTo ls

prefixToLevel :: LiteralTrail -> Int -> LiteralTrail
prefixToLevel ls i = takeWhile (\(l, _) -> decisionLevel ls l <= i) ls

falseClause :: LiteralTrail -> Clause -> Bool
falseClause ls = all (\l -> (-l) `elem` map fst ls)

contradicts :: LiteralTrail -> Formula -> Bool
contradicts ls = any (falseClause ls)

satisfies :: LiteralTrail -> Formula -> Bool
satisfies ls = all (any (`elem` ls'))
  where ls' = map fst ls

-- Conflict resolution

-- Precondition: There is at least one conflict clause in f
getConflictClause :: LiteralTrail -> Formula -> Clause
getConflictClause ls = head . filter (falseClause ls)

addLiteral :: State -> Literal -> State
addLiteral s@(S _ ls c@(C cH cP _ cN) _) l
  | M.findWithDefault False l cH = s
  | otherwise                    = if decisionLevel ls (-l) == currentLevel ls
                                       then s { conflict = c { cMap = cH', cNum = cN + 1 } }
                                       else s { conflict = c { cMap = cH', cPartial = S.insert l cP } }
  where cH' = M.insert l True cH

removeLiteral :: State -> Literal -> State
removeLiteral s@(S _ ls c@(C cH cP _ cN) _) l =
    if decisionLevel ls (-l) == currentLevel ls
        then s { conflict = c { cMap = cH', cNum = cN - 1 } }
        else s { conflict = c { cMap = cH', cPartial = S.delete l cP } }
  where cH' = M.insert l False cH

applyConflict :: State -> State
applyConflict s@(S f ls _ _) = findLastAssertedLiteral $ foldl addLiteral s' conflictClause
  where conflictClause = getConflictClause ls f
        s' = s { conflict = C M.empty S.empty Nothing 0 }

explainEmpty :: State -> State
explainEmpty s@(S _ _ (C _ cP cL _) _)
  | cL == Nothing && S.null cP = s
  | otherwise                  = explainEmpty $ explain s $ fromJust cL

explainUIP :: State -> State
explainUIP s
  | isUIP s = s
  | otherwise = explainUIP . explain s . fromJust . cLast $ conflict s

isUIP :: State -> Bool
isUIP = (== 1) . cNum . conflict

explain :: State -> Literal -> State
explain s l = _traceX $ findLastAssertedLiteral $ resolve s (getConflictReason s l) l
  where _traceX = id -- trace ("Explained " ++ show l ++ " by " ++ show (getConflictReason s l))

resolve :: State -> Clause -> Literal -> State
resolve s c l = foldl addLiteral (removeLiteral s (-l)) $ [l' | l' <- c, l' /= l]

findLastAssertedLiteral :: State -> State
findLastAssertedLiteral s@(S _ ls c _) = s { conflict = c { cLast = lastAsserted } }
  where lastAsserted = listToMaybe [ l | l <- reverse (map fst ls), M.findWithDefault False (-l) $ cMap c ]

getConflictReason :: State -> Literal -> Clause
getConflictReason s l =
    M.findWithDefault (error $ "No reason for : " ++ show l) l (reasons s)

setConflictReason :: State -> Literal -> Clause -> State
setConflictReason s l c = s { reasons = M.insert l c $ reasons s }

-- Precondition: cL is not Nothing
learn :: State -> State
learn s = _traceX $ s { formula = formula s ++ [c'] }
  where c  = conflict s
        c' = S.toList $ S.insert (negate . fromJust $ cLast c) $ cPartial c
        _traceX = id -- trace ("Learned " ++ show c')

-- Backjumping

-- Precondition: cL is not Nothing
backjump :: State -> State
backjump s@(S _ ls c _) = _traceX $ setConflictReason (assertLiteral s' (-cL) False) (-cL) r
  where (Just cL) = cLast c
        ls' = prefixToLevel ls $ getBackJumpLevel s
        s'  = s { litTrail = ls', conflict = C M.empty S.empty Nothing 0 }
        r   = S.toList . S.insert (-cL) $ cPartial c
        _traceX = id -- trace ("Backjumping: c = " ++ show c ++ " l = " ++ show cL ++ " level = " ++ show (getBackJumpLevel s))

getBackJumpLevel :: State -> Int
getBackJumpLevel (S _ ls (C _ cP _ _) _)
  | S.null cP = 0
  | otherwise = S.findMax $ S.map (decisionLevel ls . negate) cP

-- Unit Propogation

exhaustiveUnitPropogate :: State -> State
exhaustiveUnitPropogate s0
  | contradicts ls1 f1 = s1
  | not b              = s1
  | otherwise          = exhaustiveUnitPropogate s1
  where (s1@(S f1 ls1 _ _), b) = unitPropogate s0

unitPropogate :: State -> (State, Bool)
unitPropogate s@(S f ls _ _)   = case unitClauses of
    []       -> (s, False)
    (u, r):_ -> _traceX u r (setConflictReason (assertLiteral s u False) u r, True)
  where unitClauses            = map (first head) $ filter ((== 1) . length . fst) removeFalsifiedLits
        removeFalsifiedLits    = map (first (filter (not . (`elem` ls') . negate))) $ zip removeSatisfiedClauses removeSatisfiedClauses
        removeSatisfiedClauses = filter (not . any (`elem` ls')) f
        ls' = map fst ls
        _traceX = const (const id) -- trace ("UP: " ++ show u ++ " with reason " ++ show r)

-- Deciding variable assignments

assertLiteral :: State -> Literal -> Bool -> State
assertLiteral state l d = state { litTrail = litTrail state ++ [(l, d)] }

-- Precondition: There is at least one unassigned literal in f
decide :: State -> State
decide s@(S f ls _ _) = _traceX $ assertLiteral s (head unassignedVars) True
  where unassignedVars = fst . L.partition (not . (`elem` currentLits)) . vars $ f
        currentLits    = map (abs . fst) ls
        _traceX = id -- trace ("Decided " ++ show (head unassignedVars))

-- Solver

solve :: State -> (LiteralTrail, Sat)
solve s0 =
    if contradicts ls1 f1
        then if currentLevel ls2 == 0
                 then (litTrail (learn (explainEmpty s2)), UNSAT)
                 else solve $ backjump (learn (explainUIP s2))
        else if length ls1 == length (vars f1)
                 then (ls1, SAT)
                 else solve $ decide s1
  where s1@(S f1 ls1 _ _) = exhaustiveUnitPropogate s0
        s2@(S _  ls2 _ _) = applyConflict s1

solveFormula :: Formula -> (LiteralTrail, Sat)
solveFormula = solve . \f -> S f [] (C M.empty S.empty Nothing 0) M.empty
