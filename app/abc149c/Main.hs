{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LexicalNegation #-}
{-# LANGUAGE LambdaCase, MultiWayIf #-}
{-# LANGUAGE NPlusKPatterns #-}
{-# LANGUAGE DataKinds, PolyKinds, NoStarIsType, TypeFamilyDependencies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedRecordDot, NoFieldSelectors, DuplicateRecordFields #-}
module Main where

import Data.ByteString.Char8 qualified as B
import Data.Maybe
import Data.Ord

import Control.Arrow
import Control.Monad
import Data.Array
import Data.Bool
import Data.Char
import Data.Function
import Data.List
import Text.Printf

import Data.IntMap qualified as IM
import Data.IntSet qualified as IS
import Data.Map qualified as M
import Data.Set qualified as S
import Data.Vector qualified as V

import Debug.Trace qualified as Debug

debug :: Bool
debug = () /= ()

type I = Int
type O = Int

type Solver = I -> O

solve :: Solver
solve = \ case
    x -> case floor $ sqrt @Double $ fromIntegral x of
        m -> iter ps x where
            ps = takeWhile (m >=) primesLT1000
            iter xs = \ case
                y | all ((0 /=) . mod y) xs -> y
                  | otherwise -> iter ps (succ y)

wrap :: Solver -> ([[I]] -> [[O]])
wrap f = \ case
    [x]:_ -> case f x of
        r -> [[r]]
    _   -> error "wrap: invalid input format"

main :: IO ()
main = B.interact (encode . wrap solve . decode)

class InterfaceForOJS a where
    readB :: B.ByteString -> a
    readBs :: B.ByteString -> [a]
    readBs = map readB . B.words
    decode :: B.ByteString -> [[a]]
    decode = map readBs . B.lines

    showB :: a -> B.ByteString
    showBs :: [a] -> B.ByteString
    showBs = B.unwords . map showB
    encode :: [[a]] -> B.ByteString
    encode = B.unlines . map showBs

instance InterfaceForOJS B.ByteString where
    readB = id
    showB = id

instance InterfaceForOJS Int where
    readB = readInt
    showB = showInt

instance InterfaceForOJS String where
    readB = readStr
    showB = showStr

instance InterfaceForOJS Double where
    readB = readDbl
    showB = showDbl

instance InterfaceForOJS Char where
    readB = B.head
    showB = B.singleton
    readBs = B.unpack
    showBs = B.pack

readInt :: B.ByteString -> Int
readInt = fst . fromJust . B.readInt

showInt :: Int -> B.ByteString
showInt = B.pack . show

readStr :: B.ByteString -> String
readStr = B.unpack

showStr :: String -> B.ByteString
showStr = B.pack

readDbl :: B.ByteString -> Double
readDbl = read . B.unpack

showDbl :: Double -> B.ByteString
showDbl = B.pack . show

{- Bonsai -}
{- error -}
invalid :: a
invalid = error "invalid input"

{- debug -}
trace :: String -> a -> a
trace | debug     = Debug.trace
      | otherwise = const id

{- |
>>> combinations 2 "abcd"
["ab","ac","ad","bc","bd","cd"]
-}
combinations :: Int -> [a] -> [[a]]
combinations = \ case
    0   -> const [[]]
    n+1 -> \ case 
        []   -> []
        x:xs -> map (x:) (combinations n xs) ++ combinations (n+1) xs
    _ -> error "negative"

{- |
>>> spanCount odd [3,1,4,1,5,9]
(2,[4,1,5,9])
-}
spanCount :: (a -> Bool) -> [a] -> (Int, [a])
spanCount p = \ case
    []   -> (0,[])
    aas@(a:as)
        | p a       -> case spanCount p as of
            (c,bs)      -> (succ c, bs)
        | otherwise -> (0,aas)

{- |
>>> runLength "aaaabbbcddeeeeeefghhhh"
[('a',4),('b',3),('c',1),('d',2),('e',6),('f',1),('g',1),('h',4)]
-}
runLength :: Eq a => [a] -> [(a, Int)]
runLength = runLengthBy (==)

runLengthBy :: (a -> a -> Bool) -> [a] -> [(a, Int)]
runLengthBy eq = unfoldr phi
  where
    phi []     = Nothing
    phi (x:xs) = case spanCount (x `eq`) xs of
      (m, zs) -> Just ((x, succ m) , zs)

{- |
>>> splitEvery 3 [0 .. 10]
[[0,1,2],[3,4,5],[6,7,8],[9,10]]
-}
splitEvery :: Int -> [a] -> [[a]]
splitEvery k = \ case
    [] -> []
    xs -> case splitAt k xs of
        (ys,zs) -> ys : splitEvery k zs

{- |
>>> subsegments "yay"
[["y","a","y"],["ya","ay"],["yay"]]
-}
subsegments :: [a] -> [[[a]]]
subsegments = drop 1 . transpose . map inits . transpose . tails 

{- |
>>> mex [8,23,9,0,12,11,1,10,13,7,41,4,14,21,5,17,3,19,2,6]
15
-}
mex     ::  [Int] -> Int
mex xs  =   minform 0 (length xs, xs)

minform         ::  Int -> (Int, [Int]) -> Int
minform a (n,xs)
  | n == 0      =   a
  | m == b - a  =   minform b (n-m, vs)
  | otherwise   =   minform a (m, us)
    where  (us,vs)  =  partition (< b) xs
           b        =  a + 1 + n `div` 2
           m        = length us

{- misc -}
toTuple :: [a] -> (a,a)
toTuple = \ case
    x:y:_ -> (x,y)
    _     -> invalid

fromTuple :: (a,a) -> [a]
fromTuple (x,y) = [x,y]

countif :: (a -> Bool) -> [a] -> Int
countif = iter 0
    where
        iter a p (x:xs) = iter (bool a (succ a) (p x)) p xs
        iter a _ []     = a

{- zipper -}
type Zp a = ([a],a,[a])

toZp :: [a] -> Zp a
toZp = \ case 
    x:xs -> ([],x,xs)
    _    -> error "toZp: empty list"

fromZp :: Zp a -> [a]
fromZp = \ case
    (as,c,bs) -> foldl (flip (:)) (c:bs) as

mvL :: Zp a -> Zp a
mvL = \ case
    (a:as,c,bs) -> (as,a,c:bs)
    _           -> error "mvL: already at left-most"

mvR :: Zp a -> Zp a
mvR = \ case
    (as,c,b:bs) -> (c:as,b,bs)
    _           -> error "mvR: already at right-most"

mvLwhile :: (a -> Bool) -> Zp a -> Zp a
mvLwhile p = \ case
    ascbs@([],_,_) -> ascbs
    ascbs@(_,c,_)
        | p c       -> mvLwhile p (mvL ascbs)
        | otherwise -> ascbs

mvRwhile :: (a -> Bool) -> Zp a -> Zp a
mvRwhile p = \ case
    ascbs@(_,_,[]) -> ascbs
    ascbs@(_,c,_)
        | p c       -> mvRwhile p (mvR ascbs)
        | otherwise -> ascbs

primesLT1000 :: [Int]
primesLT1000
    = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97
      ,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199
      ,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293
      ,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397
      ,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499
      ,503,509,521,523,541,547,557,563,569,571,577,587,593,599
      ,601,607,613,617,619,631,641,643,647,653,659,661,673,677,683,691
      ,701,709,719,727,733,739,743,751,757,761,769,773,787,797
      ,809,811,821,823,827,829,839,853,857,859,863,877,881,883,887
      ,907,911,919,929,937,941,947,953,967,971,977,983,991,997]

perfects :: [Int]
perfects = [6,28,496,8128,33550336,8589869056,137438691328,2305843008139952128]
           -- [2658455991569831744654692615953842176
           -- ,191561942608236107294793378084303638130997321548169216]
