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
   { toSearch :: [Clause]
   , searched :: [Clause]
   , inSearch :: Int
   , found    :: [XorEquation]
   }
   deriving (Show)

resetSearchRecord :: XorSearchRecord -> XorSearchRecord
resetSearchRecord (SR ts sd _ f) = SR (sd ++ ts) [] 0 f

data SearchClause = SC
   { vars         :: S.Set Literal
   , foundClauses :: S.Set (S.Set Literal)
   , isPosSign    :: Bool
   }

toXorEq :: SearchClause -> XorEquation
toXorEq (SC v _ s) = XEq (S.toList v) s

findEquivalenceClause :: XorSearchRecord -> SearchClause -> XorSearchRecord
findEquivalenceClause sr@(SR ts sd is fs) sc@(SC vs fcs _)
  | is     == varsInSc   = resetSearchRecord sr { found = toXorEq sc : fs }
  | is + 1 == varsInSc   = findLastClause (resetSearchRecord sr) sc
  | null ts              = resetSearchRecord sr
  | matches sc (head ts) = traceShow srMatch $ findEquivalenceClause srMatch scMatch
  | otherwise            = findEquivalenceClause srNoMatch sc
  where size      = S.size vs
        varsInSc  = 2 ^ (size - 1)
        scMatch   = sc { foundClauses = S.insert (S.fromList (head ts)) fcs }
        srMatch   = sr { toSearch = tail ts, inSearch = is + 1 }
        srNoMatch = sr { toSearch = tail ts, searched = head ts : sd }

findLastClause :: XorSearchRecord -> SearchClause -> XorSearchRecord
findLastClause sr@(SR [    ] _  _  _) _ = resetSearchRecord sr
findLastClause    (SR (t:ts) sd _ fs) sc@(SC vs _ _)
  | S.size vsNotInT < S.size vs = if existsMatch
                                      then SR (sd ++ ts) [] 0 (toXorEq sc : fs)
                                      else findLastClause (SR ts (t : sd) 0 fs) sc
  | otherwise = findLastClause (SR ts (t : sd) 0 fs) sc
  where vsNotInT    = vs S.\\ S.fromList (map abs t)
        tsInV       = S.filter (flip S.member vs . abs) (S.fromList t)
        existsMatch = any (matches sc) $ testClauses (S.toList tsInV) (S.toList vsNotInT)
        testClauses :: [Literal] -> [Literal] -> [Clause]
        testClauses xs [    ] = [xs]
        testClauses xs (y:ys) = testClauses (xs ++ [y]) ys ++ testClauses (xs ++ [-y]) ys

matches :: SearchClause -> Clause -> Bool
matches sc c = signsMatch && varsMatch && not usedAlready
  where signsMatch  = isPositiveSign c       == isPosSign sc
        varsMatch   = S.fromList (map abs c) == vars sc
        usedAlready = F.any (== S.fromList c) $ foundClauses sc

isPositiveSign :: Clause -> Bool
isPositiveSign c = odd $ length $ filter (>0) c

standardizeXEq :: XorEquation -> XorEquation
standardizeXEq (XEq c b) = uncurry XEq $ foldl work ([], b) c
    where work (ls, b') l
            | l < 0     = (ls ++ [l], not b')
            | otherwise = (ls ++ [l],     b')

main :: IO ()
main = print $ findEquivalenceClause sr sc
  where sr = SR [[1,2], [1, -2, 3], [1, 2, -3]] [] 1 []
        sc = SC (S.fromList [1, 2, 3]) (S.singleton (S.fromList [-1, 2, 3])) False

{-

1, 2, 3
4, 5, 6
7, 8, 9

-}
