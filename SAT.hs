{-# OPTIONS_GHC -Wall #-}

-- Implemented from http://poincare.matf.bg.ac.rs/~filip/phd/sat-tutorial.pdf
-- This solver uses techniques through v.9 of the solver in that paper

module SAT ( solveFormula
           , satisfies
           ) where

import Control.Arrow (first)
import Data.Set      (Set)

import qualified Data.Foldable       as F  (foldl')
import qualified Data.List           as L  (span)
import qualified Data.IntMap.Strict  as M  (alter, empty, findWithDefault, insert, lookup)
import qualified Data.Vector.Mutable as MV (write)
import qualified Data.Set            as S  (delete, elemAt, empty, filter, deleteFindMin, fromList, insert, map, member, notMember, null, size, toList, union)
import qualified Data.Vector         as V  (all, any, cons, drop, dropWhile, empty, filter, foldl', fromList, head, last, length, map, singleton, snoc, takeWhile, tail, toList, modify, (!), (!?))

import Types

-- Literal Trail methods

decisions :: LiteralTrail -> [(Literal, Bool)]
decisions = filter snd . litList

decisionsTo :: LiteralTrail -> Literal -> [(Literal, Bool)]
decisionsTo (T lt _) l = filter snd . dropWhile (\(x, _) -> x /= l) $ lt

currentLevel :: LiteralTrail -> Int
currentLevel = length . decisions

decisionLevel :: LiteralTrail -> Literal -> Int
decisionLevel lt = length . decisionsTo lt

prefixToLevel :: LiteralTrail -> Int -> LiteralTrail
prefixToLevel t@(T lt ms) i = T keep $ F.foldl' (\st (x, _) -> S.delete x st) ms delete
  where (delete, keep) = L.span (\(l, _) -> decisionLevel t l >= i) lt

-- Preconditon: There is at least one literal in c that is asserted in the lit trail
lastAssertedLiteral :: LiteralTrail -> Clause -> Literal
lastAssertedLiteral (T lt _) c = fst . head . filter (\(l, _) -> S.member l c') $ lt
  where c' = S.fromList . V.toList $ c

satisfies :: Set Literal -> Formula -> Bool
satisfies ms = V.all (V.any (`S.member` ms))

-- Conflict resolution

findLastAssertedLiteral :: State -> State
findLastAssertedLiteral s@(S _ _ _ lt c _ _ _ _) = s { conflict = c { c1stLast = lastAsserted } }
  where lastAsserted = lastAssertedLiteral lt . V.map negate $ cClause c

countCurrentLevelLits :: State -> State
countCurrentLevelLits s@(S _ _ _ lt c _ _ _ _) = s { conflict = conflict' }
  where level     = currentLevel lt
        conflict' = c { cNum = V.length
                             . V.takeWhile (\l -> decisionLevel lt (-l) == level)
                             . V.dropWhile (\l -> decisionLevel lt (-l) /= level) $ cClause c }

setConflictAnalysisClause :: State -> Clause -> State
setConflictAnalysisClause s c = countCurrentLevelLits . findLastAssertedLiteral $ s { conflict = c' }
  where oppLitTrailTo0 = S.map negate . litSet $ prefixToLevel (litTrail s) 0
        c'             = (conflict s) { cClause = V.filter (`S.notMember` oppLitTrailTo0) c }

applyConflict :: State -> State
applyConflict s = setConflictAnalysisClause s $ conflictCause s

explainUIP :: State -> State
explainUIP s
  | isUIP s = s
  | otherwise = explainUIP . explain s . c1stLast . conflict $ s

isUIP :: State -> Bool
isUIP = (== 1) . cNum . conflict

{-
explainSubsumption :: State -> State
explainSubsumption s@(S _ _ lt c _ _ _ _) = F.foldl' (\st l -> if subsumes cSet (S.delete l $ S.fromList $ getReason s l) then explain st l else st) s cNot'
  where (Just cL) = c1stLast c
        cSet  = S.insert (-cL) $ cPartial c
        cNot' = S.filter (`S.notMember` litSet lt) . S.map negate $ cSet

subsumes :: Set Literal -> Set Literal -> Bool
subsumes c1 c2 = S.isProperSubsetOf c2 c1
-}

explain :: State -> Literal -> State
explain s l = case getReason s l of
  Nothing -> error ("Explain didn't find a reason for " ++ show l)
  Just  r -> setConflictAnalysisClause s $ resolve (cClause . conflict $ s) r (-l)

resolve :: Clause -> Clause -> Literal -> Clause
resolve c1 c2 l = V.fromList . S.toList . S.union c1Set $ c2Set
  where c1Set = S.delete l    . S.fromList . V.toList $ c1
        c2Set = S.delete (-l) . S.fromList . V.toList $ c2

getReason :: State -> Literal -> Maybe Clause
getReason s l = M.lookup l (reasons s)

setReason :: State -> Literal -> Clause -> State
setReason s l c = s { reasons = M.insert l c $ reasons s }

-- Precondition: cL is not Nothing
learn :: State -> State
learn s@(S f wl _ lt (C c cL _ cN) _ _ _ _)
  | c == V.singleton(-cL) = s
  | otherwise = s { formula = V.snoc f c', watchList = newWL, conflict = C c cL cLL cN }
  where cLL   = lastAssertedLiteral lt . V.filter (/= cL) . V.map negate $ c
        c'    = V.cons (-cL) . V.cons (-cLL) . V.filter (\x -> x /= (-cL) && x /= (-cLL)) $ c
        fLen  = V.length f
        newWL = M.alter (insertOrAdd fLen) (-cLL) $ M.alter (insertOrAdd fLen) (-cL) wl

-- Backjumping

-- Precondition: Formula has at least one clause, cL is not Nothing
backjump :: State -> State
backjump s@(S f _ _ lt c _ _ _ _) = assertLiteral (if level > 0 then setReason s' (-cL) r else s') (-cL) False
  where cL       = c1stLast c
        level    = getBackJumpLevel s
        r        = V.last f
        s'       = s { litTrail      = prefixToLevel lt level
                     , unitsQueue    = S.empty
                     , conflict      = C V.empty 0 0 0
                     , conflictFlag  = False
                     , conflictCause = V.empty
                     }

getBackJumpLevel :: State -> Int
getBackJumpLevel (S _ _ _ lt (C c cL cLL _) _ _ _ _)
  | c == V.singleton(-cL) = 0
  | otherwise  = decisionLevel lt cLL

-- Two-watch literal scheme

-- Precondition: Clause has at least 1 element.  Assured by the rest of the program.
watch1 :: Clause -> Literal
watch1 = V.head

-- Precondition: Clause has at least 2 elements.  Assured by the rest of the program.
watch2 :: Clause -> Literal
watch2 c = c V.! 1

setWatch1 :: Clause -> Literal -> Clause
setWatch1 c l = V.cons l . V.filter (/= l) $ c

-- Precondition: Clause has at least 1 element.  Assured by the rest of the program.
setWatch2 :: Clause -> Literal -> Clause
setWatch2 c l = V.cons (c V.! 0) . V.cons l . V.filter (/= l) . V.tail $ c

swapWatches :: Clause -> Clause
swapWatches c = V.cons (c V.! 1) . V.cons (c V.! 0) . V.drop 2 $ c

insertOrAdd :: Literal -> Maybe [Int] -> Maybe [Int]
insertOrAdd index = Just . maybe [index] (index :)

notifyWatches :: State -> Literal -> State
notifyWatches s0 l = F.foldl' loop (s0 { watchList = M.insert l [] $ watchList s0 }) $ M.findWithDefault [] l $ watchList s0
  where loop s1@(S f1 wl q1 lt@(T _ m1) _ _ _ _ _) ci
          | S.member w1 m1 = s1'
          | otherwise = case getUnwatchedNonfalsifiedLiteral lt c' of
                                  Just l' -> let c'' = setWatch2 c' l' in s1 { formula = V.modify (\v -> MV.write v ci c'') f1, watchList = M.alter (insertOrAdd ci) l' wl }
                                  Nothing -> if S.member (-w1) m1
                                                 then s1' { conflictFlag = True, conflictCause = c' }
                                                 else setReason (s1' { unitsQueue = S.insert w1 q1 }) w1 c'
          | otherwise = s1'
          where c     = f1 V.! ci
                swap  = watch1 c == l
                c'    = if swap then swapWatches c else c
                w1    = c' V.! 0
                s1'   = if swap
                            then s1 { formula = V.modify (\v -> MV.write v ci c') f1, watchList = M.alter (insertOrAdd ci) l wl }
                            else s1 { watchList = M.alter (insertOrAdd ci) l wl }

getUnwatchedNonfalsifiedLiteral :: LiteralTrail -> Clause -> Maybe Literal
getUnwatchedNonfalsifiedLiteral (T _ m) = (flip (V.!?) 0) . V.filter (\x -> S.notMember (-x) m) . V.drop 2

-- Unit Propogation

exhaustiveUnitPropogate :: State -> State
exhaustiveUnitPropogate s0@(S _ _ q _ _ cf _ _ _)
  | cf        = s0
  | S.null q  = s0
  | otherwise = exhaustiveUnitPropogate $ unitPropogate s0

-- Precondition: There is at least one element in the unitsQueue. Ensured by exhaustiveUnitPropogate
unitPropogate :: State -> State
unitPropogate s = assertLiteral (s { unitsQueue = qs }) q False
  where (q, qs) = S.deleteFindMin $ unitsQueue s

-- Formula Simplification

cleanFormula :: Formula -> (State, SAT)
cleanFormula = F.foldl' (uncurry cleanClause) (emptyState, UNDEF)

cleanClause :: State -> SAT -> Clause -> (State, SAT)
cleanClause s SAT   _ = (s,   SAT)
cleanClause s UNSAT _ = (s, UNSAT)
cleanClause s UNDEF c =
    if V.any (`S.member` ms) cCleanList
        then (s, UNDEF)
        else case V.length cCleanList of
                 0 -> (s, UNSAT)
                 1 -> (exhaustiveUnitPropogate $ assertLiteral (s { variables = S.insert (abs headCClean) $ variables s }) headCClean False, UNDEF)
                 _ -> if V.any (\l -> S.member (-l) cCleanSet) cCleanList
                          then (s , UNDEF) --Dont add tautological clause
                          else (s', UNDEF) --Otherwise add it
  where cCleanSet  = S.filter (\l -> S.notMember (-l) ms) . S.fromList . V.toList $ c
        cCleanList = V.fromList . S.toList $ cCleanSet
        headCClean = V.head cCleanList
        ms         = litSet $ litTrail s
        formulaLen = V.length $ formula s
        newWL      = M.alter (insertOrAdd formulaLen) (cCleanList V.! 1) $ M.alter (insertOrAdd formulaLen) headCClean $ watchList s
        s'         = s { formula = V.snoc (formula s) cCleanList, watchList = newWL, variables = V.foldl' (\st l -> S.insert (abs l) st) (variables s) cCleanList }

-- Deciding variable assignments

assertLiteral :: State -> Literal -> Bool -> State
assertLiteral s@(S _ _ _ t@(T lt ms) _ _ _ _ _) l d = notifyWatches (s { litTrail = t' }) (-l)
  where t' = t { litList = (l, d) : lt, litSet = S.insert l ms }

-- Precondition: There is at least one unassigned literal in f
decide :: State -> State
decide s@(S _ _ _ lt _ _ _ _ vs) = assertLiteral s fstUnassigned True
  where fstUnassigned = S.elemAt 0 . S.filter (`S.notMember` currentLits) $ vs
        currentLits   = S.map abs $ litSet lt

-- Solver

solve :: State -> (LiteralTrail, SAT)
solve s0
  | conflictFlag s1 =
      if currentLevel lt1 == 0
          then (lt1, UNSAT)
          else solve . backjump . learn . explainUIP . applyConflict $ s1
  | S.size (litSet lt1) == S.size v1 = (lt1, SAT)
  | otherwise = solve . decide $! s1
  where s1@(S _ _ _ lt1 _ _ _ _ v1) = exhaustiveUnitPropogate s0

solveFormula :: Formula -> (Bool, SAT)
solveFormula f = case cleanFormula f of
                     (s, UNDEF) -> first (flip satisfies (formula s) . litSet) . solve  $ s
                     (s,     r) -> (satisfies (litSet . litTrail $ s) (formula s), r)

emptyState :: State
emptyState = S V.empty M.empty S.empty (T [] S.empty) (C V.empty 0 0 0) False V.empty M.empty S.empty
