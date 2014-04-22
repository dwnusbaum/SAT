{-# OPTIONS_GHC -Wall #-}

module XorMatrix where

--import Control.Arrow (first, second)
--import Control.Monad (replicateM)
import Debug.Trace

import qualified Data.Foldable as F
--import qualified Data.List as L
import qualified Data.Set as S

import Types

{- BE CAREFUL WITH THIS
instance Num Bool where
    (+) = (||)
    (-) = undefined
    (*) = (&&)
    abs    = error "abs doesn't make sense for bools"
    signum = error "signum doesn't make sense for bools"
    negate = not
    fromInteger 0 = False
    fromInteger _ = True
-}

data XorEquation = XEq Clause Bool

instance Show XorEquation where
    show (XEq c b) = "[" ++ unwords (map show c) ++ " | " ++ show b ++ "]"

data Matrix
   = M [XorEquation]

instance Show Matrix where
    show (M [])     = "[]"
    show (M (x:[])) = show x
    show (M (x:xs)) = show x ++ "\n" ++ show (M xs)

rref :: Matrix -> Matrix
rref = undefined

data XorSearchRecord = SR
   { toSearch  :: [Clause]
   , searched  :: [Clause]
   , inSearch  :: S.Set (S.Set Literal)
   , foundXors :: [XorEquation]
   }
   deriving (Show)

resetSearchRecord :: XorSearchRecord -> XorSearchRecord
resetSearchRecord (SR ts sd is f) = SR (is' ++ sd ++ ts) [] S.empty f
  where is' = S.toList . S.map S.toList $ is

addXorClause :: XorSearchRecord -> SearchClause -> XorSearchRecord
addXorClause (SR ts sd _ fxs) sc = SR (sd ++ ts) [] S.empty $ toXorEq sc : fxs

data SearchClause = SC
   { vars         :: S.Set Literal
   , isPosSign    :: Bool
   }

toXorEq :: SearchClause -> XorEquation
toXorEq (SC v s) = XEq (S.toList v) s

findEquivalenceClause :: XorSearchRecord -> SearchClause -> XorSearchRecord
findEquivalenceClause sr@(SR ts sd is fs) sc@(SC vs _)
  | S.size is     == varsInSc = addXorClause sr sc
  | S.size is + 1 == varsInSc = findLastClause (SR (sd ++ ts) [] is fs) sc
  | null ts                   = resetSearchRecord sr
  | matches sc is (head ts)   = traceShow srMatch $ findEquivalenceClause srMatch sc
  | otherwise                 = findEquivalenceClause srNoMatch sc
  where size      = S.size vs
        varsInSc  = 2 ^ (size - 1)
        srMatch   = sr { toSearch = tail ts, inSearch = S.insert (S.fromList (head ts)) is }
        srNoMatch = sr { toSearch = tail ts, searched = head ts : sd }

findLastClause :: XorSearchRecord -> SearchClause -> XorSearchRecord
findLastClause sr@(SR [    ] _  _  _) _ = resetSearchRecord sr
findLastClause    (SR (t:ts) sd is fs) sc@(SC vs _)
  | S.size vsNotInT < S.size vs = if existsMatch
                                      then SR (sd ++ ts) [] S.empty (toXorEq sc : fs)
                                      else findLastClause (SR ts (t : sd) is fs) sc
  | otherwise = findLastClause (SR ts (t : sd) is fs) sc
  where vsNotInT    = vs S.\\ S.fromList (map abs t)
        tsInV       = S.filter (flip S.member vs . abs) (S.fromList t)
        existsMatch = any (matches sc is) $ testClauses (S.toList tsInV) (S.toList vsNotInT)
        testClauses :: [Literal] -> [Literal] -> [Clause]
        testClauses xs [    ] = [xs]
        testClauses xs (y:ys) = testClauses (xs ++ [y]) ys ++ testClauses (xs ++ [-y]) ys

matches :: SearchClause -> S.Set (S.Set Literal) -> Clause -> Bool
matches sc usedClauses newClause = signsMatch && varsMatch && not usedAlready
  where signsMatch  = isPosSign sc == isPositiveSign newClause
        varsMatch   = vars      sc == S.fromList (map abs newClause)
        usedAlready = F.any (== S.fromList newClause) usedClauses

isPositiveSign :: Clause -> Bool
isPositiveSign c = odd $ length $ filter (>0) c

standardizeXEq :: XorEquation -> XorEquation
standardizeXEq (XEq c b) = uncurry XEq $ foldl work ([], b) c
    where work (ls, b') l
            | l < 0     = (ls ++ [l], not b')
            | otherwise = (ls ++ [l],     b')

main :: IO ()
main = print $ findEquivalenceClause sr sc
  where sr = SR [[-1,-2,-3], [1, -2, 3], [1, 2, -3]] [] (S.singleton (S.fromList [-1,2,3])) []
        sc = SC (S.fromList [1, 2, 3]) False

{-

1, 2, 3
4, 5, 6
7, 8, 9

-}
