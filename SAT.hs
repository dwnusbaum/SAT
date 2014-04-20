{-# OPTIONS_GHC -Wall #-}

-- Implemented from http://poincare.matf.bg.ac.rs/~filip/phd/sat-tutorial.pdf
-- This solver uses techniques through v.4 of the sovler in that paper

module SAT( Sat
          , State(..)
          , Conflict(..)
          , solve
          , solveFormula
          , paper1
          ) where

import Control.Arrow (first)
import Data.Map (Map)
import Data.Set (Set)
import Debug.Trace(trace, traceShow)

import qualified Data.List as L
import qualified Data.Map  as M
import qualified Data.Set  as S

data Sat
   = SAT
   | UNSAT
   | UNDEF
   deriving (Show)

type Literal = Int
type Clause = [Literal]
type Formula = [Clause]

type LiteralTrail = [(Literal, Bool)]

data Conflict = C
   { cMap     :: Map Literal Bool -- Map of literals in conflict
   , cPartial :: Set Literal      -- Set of literals from lower decision levels
   , cLast    :: Literal          -- Last asserted literal of cNot
   , cNum     :: Int              -- Number of literals at currentLevel of litTrail
   }
   deriving (Show)

data State = S
   { formula  :: Formula
   , litTrail :: LiteralTrail
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

-- Conflict resolution

getConflictClause :: LiteralTrail -> Formula -> Clause
getConflictClause ls = head . filter (falseClause ls)

addLiteral :: State -> Literal -> State
addLiteral s@(S _ ls c@(C cH cP _ cN) _) l = if M.notMember l cH
    then let cH' = M.insert l True cH
         in if decisionLevel ls (-l) == currentLevel ls
                then s { conflict = c { cMap = cH', cNum = cN + 1 } }
                else s { conflict = c { cMap = cH', cPartial = S.insert l cP } }
    else s

removeLiteral :: State -> Literal -> State
removeLiteral s@(S _ ls c@(C cH cP _ cN) _) l =
    if decisionLevel ls (-l) == currentLevel ls
        then s { conflict = c { cMap = cH', cNum = cN - 1 } }
        else s { conflict = c { cMap = cH', cPartial = S.delete l cP } }
  where cH' = M.insert l False cH

applyConflict :: State -> State
applyConflict s@(S f ls _ _) = findLastAssertedLiteral $ foldl addLiteral s $
    trace ("Conflict: " ++ show conflictClause) conflictClause
  where conflictClause = getConflictClause ls f

explainEmpty :: State -> State
explainEmpty s@(S _ _ (C _ cP cL _) _)
  | S.null $ S.insert cL cP = s
  | otherwise      = explainEmpty $ explain s cL

explainUIP :: State -> State
explainUIP s = if not $ isUIP s then explainUIP $ explain s cL else s
  where cL = cLast $ conflict s

isUIP :: State -> Bool
isUIP = (== 1) . cNum . conflict

explain :: State -> Literal -> State
explain s l = _traceX $ findLastAssertedLiteral $ resolve s (getConflictReason s l) l
  where _traceX = trace ("Explained " ++ show l ++ " by " ++ show (getConflictReason s l))

resolve :: State -> Clause -> Literal -> State
resolve s c l = foldl addLiteral (removeLiteral s (-l)) $ S.toList . S.delete l . S.fromList $ c

findLastAssertedLiteral :: State -> State
findLastAssertedLiteral s@(S _ ls c _) = s { conflict = c { cLast = lastAsserted } }
  where lastAsserted = head [ l | l <- reverse (map fst ls), M.findWithDefault False (-l) $ cMap c ]

getConflictReason :: State -> Literal -> Clause
getConflictReason s l =
    M.findWithDefault (error $ "No reason for : " ++ show l) l (reasons s)

setConflictReason :: State -> Literal -> Clause -> State
setConflictReason s l c = s { reasons = M.insert l c $ reasons s }

learn :: State -> State
learn s = _traceX $ s { formula = formula s ++ [c'] }
  where c  = conflict s
        c' = S.toList $ S.insert (negate $ cLast c) $ cPartial c
        _traceX = trace ("Learned " ++ show c')

-- Backjumping

backjump :: State -> State
backjump s@(S _ ls (C _ cP cL _) _) = _traceX $ setConflictReason (assertLiteral s' (-cL) False) (-cL) c
  where ls' = prefixToLevel ls $ getBackJumpLevel s
        s'  = s { litTrail = ls', conflict = C M.empty S.empty 0 0 }
        c   = S.toList $ S.insert (-cL) cP
        _traceX = trace ("Backjumping: c = " ++ show c ++ " l = " ++ show cL ++ " level = " ++ show (getBackJumpLevel s))

getBackJumpLevel :: State -> Int
getBackJumpLevel (S _ ls (C _ cP _ _) _)
  | S.null cP = 0
  | otherwise = S.findMax $ S.map (decisionLevel ls . negate) cP

-- Unit Propogation

exhaustiveUnitPropogate :: State -> State
exhaustiveUnitPropogate s = let (s'@(S f ls _ _), b) = unitPropogate s in if contradicts ls f || not b
    then s'
    else exhaustiveUnitPropogate s'

unitPropogate :: State -> (State, Bool)
unitPropogate s@(S f ls _ _)   = case unitClauses of
    []       -> (s, False)
    (u, r):_ -> _traceX u r (setConflictReason (assertLiteral s u False) u r, True)
  where unitClauses            = map (first head) $ filter ((== 1) . length . fst) removeFalsifiedLits
        removeFalsifiedLits    = map (first (filter (not . (`elem` ls') . negate))) $ zip removeSatisfiedClauses removeSatisfiedClauses
        removeSatisfiedClauses = filter (not . any (`elem` ls')) f
        ls' = map fst ls
        _traceX u r = trace ("UP: " ++ show u ++ " with reason " ++ show r)

-- Deciding variable assignments

assertLiteral :: State -> Literal -> Bool -> State
assertLiteral state l d = state { litTrail = litTrail state ++ [(l, d)] }

decide :: State -> State
decide s@(S f ls _ _) = _traceX $ assertLiteral s (head unassignedVars) True
  where unassignedVars = fst . L.partition (not . (`elem` currentLits)) . vars $ f
        currentLits    = map (abs . fst) ls
        _traceX = trace ("Decided " ++ show (head unassignedVars))

-- Solver

solve :: State -> (LiteralTrail, Sat)
solve s = let s1@(S f ls _ _) = exhaustiveUnitPropogate s in
    if contradicts ls f
        then let s2@(S _ ls' _ _) = applyConflict s1 in
             if currentLevel ls' == 0
                then traceShow (learn (explainEmpty s2)) ([], UNSAT)
                else solve $ backjump (learn (explainUIP s2))
        else if length ls == length (vars f)
                then (ls, SAT)
                else solve $ decide s1

solveFormula :: Formula -> (LiteralTrail, Sat)
solveFormula = solve . \f -> S f [] (C M.empty S.empty 0 0) M.empty

-- Should return ([ (-6, False), (1, True), (2, False), (-3, False), (4, True), (-5, False), (7, True)], SAT)
paper1 :: State
paper1 = S f m (C M.empty S.empty 0 0) r
  where f = [ [-1, 2]
            , [-3, 4]
            , [-1, -3, 5]
            , [-2, -4, -5]
            , [-2, 3, 5, -6]
            , [-1, 3, -5, -6]
            , [1, -6], [1, 7]
            ]
        m = [(6, True), (1, False), (2, False), (7, True), (3, True)]
        r = M.fromList [ (1, [1, -6]), (2, [-1, 2])]

main :: IO ()
main = print . solve $ paper1

