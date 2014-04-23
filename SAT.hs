{-# OPTIONS_GHC -Wall #-}

-- Implemented from http://poincare.matf.bg.ac.rs/~filip/phd/sat-tutorial.pdf
-- This solver uses techniques through v.4 of the sovler in that paper

module SAT ( solve
           , solveFormula
           , contradicts
           , satisfies
           ) where

import Control.Arrow (first)
import Data.Maybe    (fromJust, isNothing, listToMaybe)
import Data.Set      (Set)

import qualified Data.List       as L (foldl', partition)
import qualified Data.Map.Strict as M (empty, findWithDefault, insert)
import qualified Data.Set        as S (delete, elemAt, empty, findMax, insert, map, member, notMember, null, partition, size, toList)

import Types

-- Literal Trail methods

decisions :: LiteralTrail -> [Literal]
decisions = fmap fst . filter snd . litList

decisionsTo :: LiteralTrail -> Literal -> [Literal]
decisionsTo (T ls _) l  = decisionsTo' ls
  where decisionsTo' [         ] = []
        decisionsTo' ((x, b):xs)
          | x == l    = [l | b] -- If b is true, then [l], else []
          | b         = x : decisionsTo' xs
          | otherwise = decisionsTo' xs

currentLevel :: LiteralTrail -> Int
currentLevel = length . decisions

decisionLevel :: LiteralTrail -> Literal -> Int
decisionLevel ls = length . decisionsTo ls

prefixToLevel :: LiteralTrail -> Int -> LiteralTrail
prefixToLevel t@(T ls vs) i = T ns $ L.foldl' (\st (x, _) -> S.delete x st) vs rs
  where (ns, rs) = L.partition (\(l, _) -> decisionLevel t l <= i) ls

falseClause :: Set Literal -> Clause -> Bool
falseClause ls = all (\l -> S.member (-l) ls)

contradicts :: LiteralTrail -> Formula -> Bool
contradicts (T _ vs) = any (falseClause vs)

satisfies :: LiteralTrail -> Formula -> Bool
satisfies (T _ vs) = all (any (`S.member` vs))

-- Conflict resolution

-- Precondition: There is at least one conflict clause in f
getConflictClause :: LiteralTrail -> Formula -> Clause
getConflictClause (T _ vs) = head . filter (falseClause vs)

addLiteral :: State -> Literal -> State
addLiteral s@(S _ _ ls c@(C cH cP _ cN) _) l
  | M.findWithDefault False l cH = s
  | otherwise                    = if decisionLevel ls (-l) == currentLevel ls
                                       then s { conflict = c { cMap = cH', cNum = cN + 1 } }
                                       else s { conflict = c { cMap = cH', cPartial = S.insert l cP } }
  where cH' = M.insert l True cH

removeLiteral :: State -> Literal -> State
removeLiteral s@(S _ _ ls c@(C cH cP _ cN) _) l =
    if decisionLevel ls (-l) == currentLevel ls
        then s { conflict = c { cMap = cH', cNum = cN - 1 } }
        else s { conflict = c { cMap = cH', cPartial = S.delete l cP } }
  where cH' = M.insert l False cH

applyConflict :: State -> State
applyConflict s@(S f _ ls _ _) = findLastAssertedLiteral $ L.foldl' addLiteral s' conflictClause
  where conflictClause = getConflictClause ls f
        s' = s { conflict = C M.empty S.empty Nothing 0 }

explainEmpty :: State -> State
explainEmpty s@(S _ _ _ (C _ cP cL _) _)
  | isNothing cL && S.null cP = s
  | otherwise                 = explainEmpty $ explain s $ fromJust cL

explainUIP :: State -> State
explainUIP s
  | isUIP s = s
  | otherwise = explainUIP . explain s . fromJust . cLast $ conflict s

isUIP :: State -> Bool
isUIP = (== 1) . cNum . conflict

explain :: State -> Literal -> State
explain s l = findLastAssertedLiteral $ resolve s (getConflictReason s l) l

resolve :: State -> Clause -> Literal -> State
resolve s c l = L.foldl' addLiteral (removeLiteral s (-l)) [l' | l' <- c, l' /= l]

findLastAssertedLiteral :: State -> State
findLastAssertedLiteral s@(S _ _ (T ls _) c _) = s { conflict = c { cLast = lastAsserted } }
  where lastAsserted = listToMaybe [ l | l <- L.foldl' (\st l' -> fst l' : st) [] ls, M.findWithDefault False (-l) $ cMap c ]

getConflictReason :: State -> Literal -> Clause
getConflictReason s l =
    M.findWithDefault (error $ "No reason for : " ++ show l) l (reasons s)

setConflictReason :: State -> Literal -> Clause -> State
setConflictReason s l c = s { reasons = M.insert l c $ reasons s }

-- Precondition: cL is not Nothing
learn :: State -> State
learn s = s { formula = formula s ++ [c'] }
  where c  = conflict s
        c' = S.toList $ S.insert (negate . fromJust $ cLast c) $ cPartial c

-- Backjumping

-- Precondition: cL is not Nothing
backjump :: State -> State
backjump s@(S _ _ ls c _) = setConflictReason (assertLiteral s' (-cL) False) (-cL) r
  where (Just cL) = cLast c
        ls' = prefixToLevel ls $ getBackJumpLevel s
        s'  = s { litTrail = ls', conflict = C M.empty S.empty Nothing 0 }
        r   = S.toList . S.insert (-cL) $ cPartial c

getBackJumpLevel :: State -> Int
getBackJumpLevel (S _ _ ls (C _ cP _ _) _)
  | S.null cP = 0
  | otherwise = S.findMax $ S.map (decisionLevel ls . negate) cP

-- Unit Propogation

-- Rewrite into a fold over unitLitsAndClauses from unitPropogate?
exhaustiveUnitPropogate :: State -> State
exhaustiveUnitPropogate s0
  | contradicts ls1 f1 = s1
  | not b              = s1
  | otherwise          = exhaustiveUnitPropogate s1
  where (s1@(S f1 _ ls1 _ _), b) = unitPropogate s0

unitPropogate :: State -> (State, Bool)
unitPropogate s@(S f _ (T _ vs) _ _) = case unitLitsAndClauses of
    []       -> (s, False)
    (u, r):_ -> (setConflictReason (assertLiteral s u False) u r, True)
  where unitLitsAndClauses     = map (first head) $ filter (lengthEq1 . fst) removeFalsifiedLits
        removeFalsifiedLits    = map (first (filter (\l -> S.notMember (-l) vs))) $ zip removeSatisfiedClauses removeSatisfiedClauses
        removeSatisfiedClauses = filter (not . any (`S.member` vs)) f

lengthEq1 :: [a] -> Bool
lengthEq1 (_:[]) = True
lengthEq1 _      = False

-- Deciding variable assignments

assertLiteral :: State -> Literal -> Bool -> State
assertLiteral s@(S _ _ t@(T ls vs) _ _) l d = s { litTrail = t' }
  where t' = t { litList = ls ++ [(l, d)], litSet = S.insert l vs }

-- Precondition: There is at least one unassigned literal in f
decide :: State -> State
decide s@(S _ us ls _ _) = assertLiteral s fstUnassigned True
  where fstUnassigned = S.elemAt 0 . fst . S.partition (not . (`S.member` currentLits)) $ us
        currentLits   = S.map abs $ litSet ls

-- Solver

solve :: State -> (LiteralTrail, SAT)
solve s0 =
    if contradicts ls1 f1
        then if currentLevel ls2 == 0
                 then (litTrail (learn (explainEmpty s2)), UNSAT)
                 else solve $ backjump (learn (explainUIP s2))
        else if S.size (litSet ls1) == S.size u1
                 then (ls1, SAT)
                 else solve $ decide s1
  where s1@(S f1 u1 ls1 _ _) = exhaustiveUnitPropogate s0
        s2@(S _  _  ls2 _ _) = applyConflict s1

solveFormula :: Formula -> (LiteralTrail, SAT)
solveFormula = solve . \f -> S f (uniqueVars f) (T [] S.empty) (C M.empty S.empty Nothing 0) M.empty
  where uniqueVars = L.foldl' (\st l -> S.insert (abs l) st) S.empty . concat
