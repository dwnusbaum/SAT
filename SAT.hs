{-# OPTIONS_GHC -Wall #-}

-- Implemented from http://poincare.matf.bg.ac.rs/~filip/phd/sat-tutorial.pdf
-- This solver uses techniques through v.9 of the solver in that paper

module SAT ( solveFormula
           , contradicts
           , satisfies
           ) where

import Data.Maybe    (fromJust)
import Data.Set      (Set)

import qualified Data.Foldable      as F (foldl')
import qualified Data.List          as L (span)
import qualified Data.IntMap.Strict as M (alter, empty, findWithDefault, insert, lookup)
import qualified Data.Set           as S (delete, elemAt, empty, filter, deleteFindMin, fromList, insert, map, member, notMember, null, size, toList, union)
import qualified Data.Vector        as V (all, any, empty, filter, foldl', fromList, last, length, map, singleton, snoc, toList, (!), (!?))

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
  where (delete, keep) = L.span (\(l, _) -> decisionLevel t l > i) lt

-- Preconditon: There is at least one literal in c that is asserted in the lit trail
lastAssertedLiteral :: LiteralTrail -> Clause -> Literal
lastAssertedLiteral (T lt _) c = fst . head . filter (\(l, _) -> S.member l c') $ lt
  where c' = S.fromList . V.toList $ c

satisfies :: Set Literal -> Formula -> Bool
satisfies ms = V.all (V.any (`S.member` ms))

contradicts :: Set Literal -> Formula -> Bool
contradicts ms = V.any (V.all (flip S.member ms . negate))

-- Conflict resolution

findLastAssertedLiteral :: State -> State
findLastAssertedLiteral s@(S _ lt _ _ _ _ c _ _ _) = s { conflict = c { c1stLast = lastAsserted } }
  where lastAsserted = lastAssertedLiteral lt . V.map negate $ cClause c

countCurrentLevelLits :: State -> State
countCurrentLevelLits s@(S _ lt _ _ _ _ c _ _ _) = s { conflict = conflict' }
  where level     = currentLevel lt
        conflict' = c { cNum = V.length . V.filter (\l -> decisionLevel lt (-l) == level) $ cClause c }

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

explain :: State -> Literal -> State
explain s l = case getReason s l of
  Nothing -> error ("Explain didn't find a reason for " ++ show l)
  Just  r -> setConflictAnalysisClause s . resolve (cClause . conflict $ s) r $ (-l)

resolve :: Clause -> Clause -> Literal -> Clause
resolve c1 c2 l = V.fromList . S.toList $ S.union c1Set c2Set
  where c1Set = S.delete l    . S.fromList . V.toList $ c1
        c2Set = S.delete (-l) . S.fromList . V.toList $ c2

getReason :: State -> Literal -> Maybe Clause
getReason s l = M.lookup l (reasons s)

setReason :: State -> Literal -> Clause -> State
setReason s l c = s { reasons = M.insert l c $ reasons s }

-- Precondition: cL is not Nothing
learn :: State -> State
learn s@(S f lt _ _ _ _ (C c cL _ cN) _ _ _)
  | c == V.singleton(-cL) = s
  | otherwise = s' { formula = V.snoc f c, conflict = C c cL cLL cN }
  where cLL = lastAssertedLiteral lt . V.filter (/= cL) . V.map negate $ c
        ci  = V.length f
        s'  = setWatch2 ci (-cLL) . setWatch1 ci (-cL) $ s

-- Backjumping

-- Precondition: Formula has at least one clause, cL is not Nothing
backjump :: State -> State
backjump s@(S f lt _ _ _ _ c _ _ _) = assertLiteral (if level > 0 then setReason s' (-cL) r else s') (-cL) False
  where cL       = c1stLast c
        level    = getBackJumpLevel s
        r        = V.last f
        s'       = s { litTrail      = prefixToLevel lt level
                     , unitsQueue    = S.empty
                     , conflict      = C V.empty 0 0 0
                     , conflictCause = V.empty
                     }

getBackJumpLevel :: State -> Int
getBackJumpLevel (S _ lt _ _ _ _ (C c cL cLL _) _ _ _)
  | c == V.singleton(-cL) = 0
  | otherwise  = decisionLevel lt cLL

-- Two-watch literal scheme

-- Precondition: Clause has at least 1 element.  Assured by the rest of the program.
getWatch1 :: State -> ClauseIndex -> Maybe Literal
getWatch1 s ci = M.lookup ci $ watch1 s

-- Precondition: Clause has at least 2 elements.  Assured by the rest of the program.
getWatch2 :: State -> ClauseIndex -> Maybe Literal
getWatch2 s ci = M.lookup ci $ watch2 s

setWatch1 ::ClauseIndex -> Literal -> State -> State
setWatch1 ci l s = s { watchList = alterWatchList ci l wl, watch1 = M.insert ci l w1 }
  where wl = watchList s
        w1 = watch1 s

-- Precondition: Clause has at least 1 element.  Assured by the rest of the program.
setWatch2 :: ClauseIndex -> Literal -> State -> State
setWatch2 ci l s = s { watchList = alterWatchList ci l wl, watch2 = M.insert ci l w2 }
  where wl = watchList s
        w2 = watch2 s

swapWatches :: State -> ClauseIndex -> State
swapWatches s ci = s { watch1 = M.insert ci (find ci w2) w1, watch2 = M.insert ci (find ci w1) w2 }
  where w1 = watch1 s
        w2 = watch2 s
        find = M.findWithDefault (error "swapWatches: Watch did not exist for clause")

alterWatchList :: ClauseIndex -> Literal -> WatchList -> WatchList
alterWatchList i = M.alter (Just . maybe [i] (i :))

notifyWatches :: State -> Literal -> State
notifyWatches s0 l = F.foldl' loop (s0 { watchList = M.insert l [] $ watchList s0 }) $ M.findWithDefault [] l $ watchList s0
  where loop s1@(S _ lt@(T _ m1) wl _ _ q _ _ _ _) ci
          | S.member clauseW1 m1 = s1'
          | otherwise = case getUnwatchedNonfalsifiedLiteral lt clause clauseW1 clauseW2 of
                                  Just l' -> setWatch2 ci l' sSwap
                                  Nothing -> if S.member (-clauseW1) m1
                                                 then s1' { conflictCause = clause }
                                                 else setReason (s1' { unitsQueue = S.insert clauseW1 q }) clauseW1 clause
          | otherwise = s1'
          where swap     = getWatch1 s1 ci == Just l
                sSwap    = if swap then swapWatches s1 ci else s1
                clause   = (V.! ci) . formula $ sSwap
                clauseW1 = fromJust $ getWatch1 sSwap ci
                clauseW2 = fromJust $ getWatch2 sSwap ci
                s1'      = sSwap { watchList = alterWatchList ci l wl }

getUnwatchedNonfalsifiedLiteral :: LiteralTrail -> Clause -> Literal -> Literal -> Maybe Literal
getUnwatchedNonfalsifiedLiteral (T _ m) c w1 w2 = (V.!? 0) . V.filter (\x -> S.notMember (-x) m) . V.filter (\x -> x /= w1 && x /= w2) $ c

-- Unit Propogation

exhaustiveUnitPropogate :: State -> State
exhaustiveUnitPropogate s0@(S _ _ _ _ _ q _ cc _ _)
  | V.length cc > 0 = s0
  | S.null q        = s0
  | otherwise       = exhaustiveUnitPropogate $ unitPropogate s0

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
  where cCleanSet     = S.filter (\l -> S.notMember (-l) ms) . S.fromList . V.toList $ c
        cCleanList    = V.fromList . S.toList $ cCleanSet
        headCClean    = cCleanList V.! 0
        ms            = litSet $ litTrail s
        clauseIndex   = V.length $ formula s
        updateWatches = setWatch2 clauseIndex (cCleanList V.! 1) . setWatch1 clauseIndex headCClean $ s
        s'            = updateWatches { formula = V.snoc (formula s) cCleanList, variables = V.foldl' (\st l -> S.insert (abs l) st) (variables s) cCleanList }

-- Deciding variable assignments

assertLiteral :: State -> Literal -> Bool -> State
assertLiteral s l d = notifyWatches (s { litTrail = t' }) (-l)
  where t' = t { litList = (l, d) : lt, litSet = S.insert l ms }
        t@(T lt ms) = litTrail s

-- Precondition: There is at least one unassigned literal in f
decide :: State -> State
decide s@(S _ lt _ _ _ _ _ _ _ vs) = assertLiteral s fstUnassigned True
  where fstUnassigned = S.elemAt 0 . S.filter (`S.notMember` currentLits) $ vs
        currentLits   = S.map abs $ litSet lt

-- Solver

solve :: State -> (Set Literal, SAT)
solve s0
  | V.length (conflictCause s1) > 0 =
      if currentLevel lt1 == 0
          then (litSet lt1, UNSAT)
          else solve . backjump . learn . explainUIP . applyConflict $ s1
  | S.size (litSet lt1) == S.size v1 = (litSet lt1, SAT)
  | otherwise = solve . decide $ s1
  where s1@(S _ lt1 _ _ _ _ _ _ _ v1) = exhaustiveUnitPropogate $ s0

solveFormula :: Formula -> (Set Literal, SAT)
solveFormula f = case cleanFormula f of
                     (s, UNDEF) -> solve s
                     (s,     r) -> (litSet $ litTrail s, r)

emptyState :: State
emptyState = S
    { formula       = V.empty
    , litTrail      = T [] S.empty
    , watchList     = M.empty
    , watch1        = M.empty
    , watch2        = M.empty
    , unitsQueue    = S.empty
    , conflict      = C V.empty 0 0 0
    , conflictCause = V.empty
    , reasons       = M.empty
    , variables     = S.empty
    }
