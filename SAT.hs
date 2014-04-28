{-# OPTIONS_GHC -Wall #-}

-- Implemented from http://poincare.matf.bg.ac.rs/~filip/phd/sat-tutorial.pdf
-- This solver uses techniques through v.4 of the solver in that paper

module SAT ( solveFormula
           , contradicts
           , satisfies
           ) where

import Control.Arrow (first)
import Data.Maybe    (fromJust, isNothing, listToMaybe)
import Data.Set      (Set)

import qualified Data.Foldable   as F (any, foldl', foldr)
import qualified Data.List       as L (partition)
import qualified Data.Map.Strict as M (empty, findWithDefault, insert)
import qualified Data.Set        as S (delete, elemAt, empty, filter, findMax, fromList, insert, isProperSubsetOf, map, member, notMember, null, size, toList)

import Types

-- Literal Trail methods

decisions :: LiteralTrail -> [(Literal, Bool)]
decisions = filter snd . litList

decisionsTo :: LiteralTrail -> Literal -> [(Literal, Bool)]
decisionsTo (T ls _) l = filter snd . dropWhile ((/= l) . fst) $ ls

currentLevel :: LiteralTrail -> Int
currentLevel = length . decisions

decisionLevel :: LiteralTrail -> Literal -> Int
decisionLevel ls = length . decisionsTo ls

prefixToLevel :: LiteralTrail -> Int -> LiteralTrail
prefixToLevel t@(T ls ms) i = T ns $ F.foldl' (\st (x, _) -> S.delete x st) ms rs
  where (ns, rs) = L.partition (\(l, _) -> decisionLevel t l <= i) ls

-- Preconditon: There is at least one literal in c that is asserted in the lit trail
lastAssertedLiteral :: LiteralTrail -> Clause -> Literal
lastAssertedLiteral (T lt _) c = fst . head . filter (\(l, _) -> l `elem` c) $ lt

falseClause :: Set Literal -> Clause -> Bool
falseClause ls = all (\l -> S.member (-l) ls)

contradicts :: LiteralTrail -> Formula -> Bool
contradicts (T _ ms) = any (falseClause ms)

satisfies :: LiteralTrail -> Formula -> Bool
satisfies (T _ ms) = all (any (`S.member` ms))

-- Conflict resolution

-- Precondition: There is at least one conflict clause in f
getConflictClause :: LiteralTrail -> Formula -> Clause
getConflictClause (T _ ms) = head . filter (falseClause ms)

addLiteral :: State -> Literal -> State
addLiteral s@(S _ _ ls c@(C cH cP _ cN) _ _ _ _) l
  | M.findWithDefault False l cH = s
  | level == 0                   = s
  | otherwise                    = if level == currentLevel ls
                                       then s { conflict = c { cMap = cH', cNum = cN + 1 } }
                                       else s { conflict = c { cMap = cH', cPartial = S.insert l cP } }
  where level = decisionLevel ls (-l)
        cH' = M.insert l True cH

removeLiteral :: State -> Literal -> State
removeLiteral s@(S _ _ ls c@(C cH cP _ cN) _ _ _ _) l =
    if decisionLevel ls (-l) == currentLevel ls
        then s { conflict = c { cMap = cH', cNum = cN - 1 } }
        else s { conflict = c { cMap = cH', cPartial = S.delete l cP } }
  where cH' = M.insert l False cH

applyConflict :: State -> State
applyConflict s@(S f _ ls _ _ _ _ _) = findLastAssertedLiteral $ F.foldl' addLiteral s' $ getConflictClause ls f
  where s' = s { conflict = C M.empty S.empty Nothing 0, conflictFlag = False, conflictClause = [] }

explainEmpty :: State -> State
explainEmpty s@(S _ _ _ (C _ cP cL _) _ _ _ _)
  | isNothing cL && S.null cP = s
  | otherwise                 = explainEmpty $ explain s $ fromJust cL

explainUIP :: State -> State
explainUIP s
  | isUIP s = s
  | otherwise = explainUIP . explain s . fromJust . cLast $ conflict s

isUIP :: State -> Bool
isUIP = (== 1) . cNum . conflict

explainSubsumption :: State -> State
explainSubsumption s@(S _ _ lt c _ _ _ _) = F.foldl' (\st l -> if subsumes cSet (S.delete l $ S.fromList $ getConflictReason s l) then explain st l else st) s cNot'
  where (Just cL) = cLast c
        cSet  = S.insert (-cL) $ cPartial c
        cNot' = S.filter (`S.notMember` litSet lt) . S.map negate $ cSet

subsumes :: Set Literal -> Set Literal -> Bool
subsumes c1 c2 = S.isProperSubsetOf c2 c1

explain :: State -> Literal -> State
explain s l = findLastAssertedLiteral $ resolve s (getConflictReason s l) l

resolve :: State -> Clause -> Literal -> State
resolve s c l = F.foldl' addLiteral (removeLiteral s (-l)) [l' | l' <- c, l' /= l]

findLastAssertedLiteral :: State -> State
findLastAssertedLiteral s@(S _ _ (T ls _) c _ _ _ _) = s { conflict = c { cLast = lastAsserted } }
  where lastAsserted = listToMaybe $ F.foldr (\(l, _) st -> if M.findWithDefault False (-l) $ cMap c then l : st else st) [] ls

getConflictReason :: State -> Literal -> Clause
getConflictReason s l = M.findWithDefault (error $ "No reason for " ++ show l ++ " litTrail:" ++ show (litTrail s)) l (reasons s)

setConflictReason :: State -> Literal -> Clause -> State
setConflictReason s l c = s { reasons = M.insert l c $ reasons s }

-- Precondition: cL is not Nothing
learn :: State -> State
learn s = case c' of
              [    ] -> s
              (_:[]) -> s
              _      -> s { formula = c' : formula s }
  where c  = conflict s
        cP = S.toList $ cPartial c
        cL = negate . fromJust $ cLast c
        cPLast = negate . lastAssertedLiteral (litTrail s) $ map negate cP
        c' = case cP of
                 [] -> [cL]
                 _  -> cL : cPLast : filter (/= cPLast) cP

-- Backjumping

-- Precondition: cL is not Nothing
backjump :: State -> State
backjump s@(S _ _ ls c _ _ _ _) = s'
  where (Just cL) = cLast c
        ls'       = prefixToLevel ls $ getBackJumpLevel s
        s'        = s { litTrail = ls', unitsQueue = [-cL], conflict = C M.empty S.empty Nothing 0, conflictFlag = False }

getBackJumpLevel :: State -> Int
getBackJumpLevel (S _ _ ls (C _ cP _ _) _ _ _ _)
  | S.null cP = 0
  | otherwise = S.findMax $ S.map (decisionLevel ls . negate) cP

-- Two-watch literal scheme

-- Precondition: Clause has at least 1 element.  Assured by the rest of the program.
watch1 :: Clause -> Literal
watch1 = head

-- Precondition: Clause has at least 2 elements.  Assured by the rest of the program.
watch2 :: Clause -> Literal
watch2 (_:x:_) = x
watch2 _ = error "watch2: Clause was malformed."

setWatch1 :: Clause -> Literal -> Clause
setWatch1 c l = l : filter (/= l) c

-- Precondition: Clause has at least 1 element.  Assured by the rest of the program.
setWatch2 :: Clause -> Literal -> Clause
setWatch2 (c:cs) l = c : l : filter (/= l) cs
setWatch2 _      _ = error "setWatch2: Clause was malformed."

swapWatches :: Clause -> Clause
swapWatches (a:b:ls) = b : a : ls
swapWatches _        = error "swapWatches: Clause was malformed."

notifyWatches :: State -> Literal -> State
notifyWatches s0@(S f0 _ (T _ m) _ _ _ _ _) l = F.foldl' work s0' check
  where work s1@(S f1 q1 _ _ _ _ _ _) c = let c'@(w1:_) = if watch1 c == l then swapWatches c else c
                    in if S.notMember w1 m
                           then case listToMaybe . filter (\x -> S.notMember (-x) m) . drop 2 $ c' of
                                    Just l' -> s1 { formula = setWatch2 c' l' : f1 }
                                    Nothing -> if S.member (-w1) m
                                                   then s1 { formula = c' : f1, conflictFlag = True, conflictClause = c' }
                                                   else s1 { formula = c' : f1, unitsQueue = w1 : q1 } --if (S.notMember w1 q) then insert else dont
                           else s1 { formula = c' : f1 }
        needsChecked (a:b:_) = a == l || b == l
        needsChecked _       = error "notifyWatches.needsChecked: Clause was malformed."
        (check, dont) = L.partition needsChecked f0
        s0' = s0 { formula = dont }

-- Unit Propogation

-- Rewrite into a fold over unitLitsAndClauses from unitPropogate?
exhaustiveUnitPropogate :: State -> State
exhaustiveUnitPropogate s0@(S _ q _ _ cf _ _ _)
  | cf        = s0
  | null q    = s0
  | otherwise = exhaustiveUnitPropogate $ unitPropogate s0

unitPropogate :: State -> State
unitPropogate s = (assertLiteral s q False) { unitsQueue = qs }
  where (q:qs) = unitsQueue s

-- Formula Simplification

cleanFormula :: Formula -> (State, SAT)
cleanFormula = F.foldl' (uncurry cleanClause) (emptyState, UNDEF)

cleanClause :: State -> SAT -> Clause -> (State, SAT)
cleanClause s SAT   _ = (s,   SAT)
cleanClause s UNSAT _ = (s, UNSAT)
cleanClause s UNDEF c =
    if F.any (`S.member` ms) cCleanList
        then (s, UNDEF)
        else case cCleanList of
                 [    ] -> (s, UNSAT)
                 (l:[]) -> (exhaustiveUnitPropogate $ assertLiteral s l False, UNDEF)
                 _      -> if any (\l -> S.member (-l) cCleanSet) cCleanList
                               then (s , UNDEF)
                               else (s', UNDEF)
  where cCleanSet  = S.filter (\l -> S.notMember (-l) ms) . S.fromList $ c
        cCleanList = S.toList cCleanSet
        ms         = litSet $ litTrail s
        s'         = s { formula = cCleanList : formula s, variables = F.foldl' (\st l -> S.insert (abs l) st) (variables s) cCleanList }

-- Deciding variable assignments

assertLiteral :: State -> Literal -> Bool -> State
assertLiteral s@(S _ _ t@(T ls vs) _ _ _ _ _) l d = notifyWatches (s { litTrail = t' }) (-l)
  where t' = t { litList = (l, d) : ls, litSet = S.insert l vs }

-- Precondition: There is at least one unassigned literal in f
decide :: State -> State
decide s@(S _ _ ls _ _ _ _ vs) = assertLiteral s fstUnassigned True
  where fstUnassigned = S.elemAt 0 . S.filter (`S.notMember` currentLits) $ vs
        currentLits   = S.map abs $ litSet ls

-- Solver

solve :: State -> (Set Literal, SAT)
solve s0
  | conflictFlag s1 =
      if currentLevel ls1 == 0
          then (litSet $ litTrail (learn (explainEmpty s1)), UNSAT)
          else solve $ backjump (learn (explainSubsumption (explainUIP (applyConflict s1))))
  | S.size (litSet ls1) == S.size v1 = (litSet ls1, SAT)
  | otherwise = solve $ decide s1
  where s1@(S _ _ ls1 _ _ _ _ v1) = exhaustiveUnitPropogate s0

solveFormula :: Formula -> (Set Literal, SAT)
solveFormula f = case cleanFormula f of
                     (s, UNDEF) -> solve s
                     x          -> first (litSet . litTrail) x

emptyState :: State
emptyState = S [] [] (T [] S.empty) (C M.empty S.empty Nothing 0) False [] M.empty S.empty
