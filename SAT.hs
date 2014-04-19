{-# OPTIONS_GHC -Wall #-}

module SAT where

import Control.Arrow (first)
import Data.Map (Map)
import Debug.Trace(trace, traceShow)

import qualified Data.List as L
import qualified Data.Map  as M
import qualified Data.Set  as S

{-
input: Boolean formula ϕ
output: Sat or Unsat
begin
    α := {}
    M := ObtainXorMatrix(ϕ);
    repeat
        (status, α) := PropagateUnitImplication(ϕ, α);
        if status = conﬂict
            if conﬂict at top decision level
               return Unsat;
            ϕ := AnalyzeConﬂict&AddLearntClause(ϕ, α);
            α := Backtrack(ϕ, α);
        else
            if all variables assigned
                return Sat;
            (status, ®) := Xorplex(M, α);
            if status = propagation or conﬂict
                ϕ := AddXorImplicationConﬂictClause(ϕ, M, α);
                continue;
        α := Decide(ϕ, α);
end
-}

data Sat
   = SAT
   | UNSAT
   | UNDEF
   deriving (Show)

type Literal = Int
type Clause = [Literal]
type Formula = [Clause]

type LiteralTrail = [(Literal, Bool)]

type IsDecision = Bool

data Conflict = C
   { cMap     :: Map Literal Bool --Map of literals in conflict
   , cPartial :: Clause  --List of literals from lower decision levels
   , cLast    :: Literal --Last asserted literal of (map negate conflict)
   , cNum     :: Int     --Number of literals at currentLevel of litTrail
   }
   deriving (Show)

data State = S
   { formula  :: Formula
   , litTrail :: LiteralTrail
   , conflict :: Conflict
   , reasons  :: Map Literal Clause
   }
   deriving (Show)

decisions :: LiteralTrail -> [Literal]
decisions = fmap fst . filter snd

lastDecision :: LiteralTrail -> Literal
lastDecision = last . decisions

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

prefixBeforeLastDecision :: LiteralTrail -> LiteralTrail
prefixBeforeLastDecision ls = takeWhile ((/= l) . fst) ls
  where l = lastDecision ls

vars :: Formula -> [Literal]
vars = S.toList . S.unions . map S.fromList

--Conflict resolution

getConflictClause :: LiteralTrail -> Formula -> Clause
getConflictClause ls = head . filter (falseClause ls)

addLiteral :: State -> Literal -> State
addLiteral s@(S _ ls c@(C cH cP _ cN) _) l = if M.notMember l cH
    then let cH' = M.insert l True cH
         in if decisionLevel ls (-l) == currentLevel ls
                then s { conflict = c { cMap = cH', cNum = cN + 1 } }
                else s { conflict = c { cMap = cH', cPartial = cP ++ [l] } }
    else s

removeLiteral :: State -> Literal -> State
removeLiteral s@(S _ ls c@(C cH cP _ cN) _) l =
    let cH' = M.insert l False cH
    in if decisionLevel ls (-l) == currentLevel ls
           then s { conflict = c { cMap = cH', cNum = cN - 1 } }
           else s { conflict = c { cMap = cH', cPartial = S.toList . S.delete l . S.fromList $ cP } }
{-
buildConflict :: Conflict -> Clause
buildConflict (C _ cP cL _) = cP ++ [cL]
-}

applyConflict :: State -> State
applyConflict s@(S f ls _ _) = foldl addLiteral s $ getConflictClause ls f

explainEmpty :: State -> State
explainEmpty s@(S _ _ (C _ cP cL _) _)
  | null $ cL : cP = s
  | otherwise      = explainEmpty $ explain s cL

explainUIP :: State -> State
explainUIP s@(S _ _ (C _ cP cL _) _)
  | null $ cL : cP = s
  | otherwise      = if not $ isUIP s then explainUIP $ explain s cL else s

explain :: State -> Literal -> State
explain s l = trace ("Explained " ++ show l ++ " by " ++ show (getConflictReason s l)) $
                    findLastAssertedLiteral $ resolve s (getConflictReason s l) l

resolve :: State -> Clause -> Literal -> State
resolve s c l = foldl addLiteral (removeLiteral s (-l)) $ S.toList . S.delete l . S.fromList $ c

findLastAssertedLiteral :: State -> State
findLastAssertedLiteral s@(S _ ls c _) = s { conflict = c { cLast = lastAsserted } }
  where lastAsserted = head [ l | l <- reverse (map fst ls), M.findWithDefault False (-l) $ cMap c ]

getConflictReason :: State -> Literal -> Clause
getConflictReason s l = M.findWithDefault (error "No reason for literal propogation") l (reasons s)

setConflictReason :: State -> Literal -> Clause -> State
setConflictReason s l c = s { reasons = M.insert l c $ reasons s }

isUIP :: State -> Bool
isUIP (S _ _ (C _ _ _ cN) _) = cN == 1

lastAssertedLiteral :: Clause -> LiteralTrail -> Literal
lastAssertedLiteral c = last . filter (`elem` c) . map fst

learn :: State -> State
learn s = trace ("Learned " ++ show c') $ s { formula = formula s ++ [c'] }
  where c  = conflict s
        c' = cPartial c ++ [cLast c]

--Backjumping

backjump :: State -> State
backjump s@(S _ ls (C _ cP cL _) _) = setConflictReason (assertLiteral s' (-cL) False) (-cL) $ cP ++ [cL]
  where ls' = prefixToLevel ls $ getBackJumpLevel s
        s'  = s { litTrail = ls', conflict = C M.empty [] 0 0 }

getBackJumpLevel :: State -> Int
getBackJumpLevel (S _ _  (C _ [] _ _) _) = 0
getBackJumpLevel (S _ ls (C _ cP _ _) _) = maximum $ map (decisionLevel ls . negate) cP

--Solver

falseClause :: LiteralTrail -> Clause -> Bool
falseClause ls = all (\l -> (-l) `elem` map fst ls)

contradicts :: LiteralTrail -> Formula -> Bool
contradicts ls = any (falseClause ls)

satisfies :: LiteralTrail -> Formula -> Bool
satisfies ls = all (any (`elem` ls'))
  where ls' = map fst ls

assertLiteral :: State -> Literal -> IsDecision -> State
assertLiteral state l d = state { litTrail = litTrail state ++ [(l, d)] }

decide :: State -> State
decide s@(S f ls _ _) = trace ("Decided " ++ show (head unassignedVars)) $ assertLiteral s (head unassignedVars) True
  where unassignedVars = fst . L.partition (not . (`elem` currentLits) . abs) . vars $ f
        currentLits    = map (abs . fst) ls

backtrack :: State -> State
backtrack state = assertLiteral (state { litTrail = ls' }) (-l) False
  where l   = lastDecision ls
        ls  = litTrail state
        ls' = prefixBeforeLastDecision ls

unitPropogate :: State -> State
unitPropogate s@(S f ls _ _) = foldl (\s' (u, r) -> trace ("Set " ++ show u ++ " with reason " ++ show r) $ setConflictReason (assertLiteral s' u False) u r) s unitClauses
  where unitClauses            = map (first head) $ filter ((== 1) . length . fst) removeFalsifiedLits
        removeFalsifiedLits    = map (first (filter (not . (`elem` ls') . negate))) $ zip removeSatisfiedClauses removeSatisfiedClauses
        removeSatisfiedClauses = filter (not . any (`elem` ls')) f
        ls' = map fst ls

solve :: State -> (LiteralTrail, Sat)
solve s = let s1@(S f ls _ _) = unitPropogate s in
    if contradicts ls f
        then let s2@(S _ ls' _ _) = applyConflict s1 in
             if currentLevel ls' == 0
                then traceShow (learn (explainEmpty s2)) ([], UNSAT)
                else solve $ backjump (learn (explainUIP s2))
        else if satisfies ls f
                then (ls, SAT)
                else solve $ decide s1

main :: IO ()
main = print . solve . (\f -> S f [] (C M.empty [] 0 0) M.empty) $ [[-1,2], [-3,4], [-1,-3,5], [-2,-4,-5], [-2,3,5,-6], [-1,3,-5,-6], [1,-6], [1,7]]
