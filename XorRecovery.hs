{-# OPTIONS_GHC -Wall #-}

module XorRecovery ( recoverXorClauses
                   , standardizeXorEq
                   ) where

import Data.Set (Set)

import qualified Data.Foldable as F (any)
import qualified Data.Set      as S (empty, filter, fromList, insert, map, member, size, toList, (\\))

import Types

data XorSearchRecord = SR
   { toSearch  :: [Clause]
   , searched  :: [Clause]
   , inSearch  :: Set (Set Literal)
   , foundXors :: [XorEquation]
   }
   deriving (Show)

data SearchClause = SC
   { vars         :: Set Literal
   , isPosSign    :: Bool
   }

toSearchClause :: Clause -> SearchClause
toSearchClause c = SC (S.fromList $ map abs c) $ isPositiveSign c

toXorEq :: SearchClause -> XorEquation
toXorEq (SC v s) = XEq (S.toList v) s

resetSearchRecord :: XorSearchRecord -> XorSearchRecord
resetSearchRecord (SR ts sd is f) = SR (is' ++ sd ++ ts) [] S.empty f
  where is' = S.toList . S.map S.toList $ is

addXorClause :: XorSearchRecord -> SearchClause -> XorSearchRecord
addXorClause (SR ts sd _ fxs) sc = SR (sd ++ ts) [] S.empty $ toXorEq sc : fxs

recoverXorClauses :: Formula -> (Formula, [XorEquation])
recoverXorClauses f = (toSearch result, foundXors result)
    where result = foldl findEquivalenceClause (SR f [] S.empty []) $ map toSearchClause f

findEquivalenceClause :: XorSearchRecord -> SearchClause -> XorSearchRecord
findEquivalenceClause sr@(SR ts sd is fs) sc@(SC vs _)
  | S.size is     == varsInSc = addXorClause sr sc
  | S.size is + 1 == varsInSc = findLastClause (SR (sd ++ ts) [] is fs) sc
  | null ts                   = resetSearchRecord sr
  | matches sc is (head ts)   = findEquivalenceClause srMatch sc
  | otherwise                 = findEquivalenceClause srNoMatch sc
  where size      = S.size vs
        varsInSc  = 2 ^ (size - 1)
        srMatch   = sr { toSearch = tail ts, inSearch = S.insert (S.fromList (head ts)) is }
        srNoMatch = sr { toSearch = tail ts, searched = head ts : sd }

findLastClause :: XorSearchRecord -> SearchClause -> XorSearchRecord
findLastClause sr@(SR [    ] _  _  _) _ = resetSearchRecord sr
findLastClause    (SR (t:ts) sd is fs) sc@(SC vs _)
  | S.size vsNotInT <  S.size vs
  , length t        <= S.size vs = if existsMatch
                                       then SR (sd ++ ts) [] S.empty (toXorEq sc : fs)
                                       else findLastClause (SR ts (t : sd) is fs) sc
  | otherwise = findLastClause (SR ts (t : sd) is fs) sc
  where vsNotInT    = vs S.\\ S.fromList (map abs t)
        tsInV       = S.filter (flip S.member vs . abs) (S.fromList t)
        existsMatch = any (matches sc is) $ testClauses (S.toList tsInV) (S.toList vsNotInT)
        testClauses :: [Literal] -> [Literal] -> [Clause]
        testClauses xs [    ] = [xs]
        testClauses xs (y:ys) = testClauses (xs ++ [y]) ys ++ testClauses (xs ++ [-y]) ys

matches :: SearchClause -> Set (Set Literal) -> Clause -> Bool
matches sc usedClauses newClause = signsMatch && varsMatch && not usedAlready
  where signsMatch  = isPosSign sc == isPositiveSign newClause
        varsMatch   = vars      sc == S.fromList (map abs newClause)
        usedAlready = F.any (== S.fromList newClause) usedClauses

isPositiveSign :: Clause -> Bool
isPositiveSign c = odd $ length $ filter (>0) c

standardizeXorEq :: XorEquation -> XorEquation
standardizeXorEq (XEq c b) = uncurry XEq $ foldl newState ([], b) c
  where newState (ls, b') l
          | l < 0     = (ls ++ [-l], not b')
          | otherwise = (ls ++ [ l],     b')
