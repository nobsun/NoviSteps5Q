{-# LANGUAGE CPP #-}
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
import Control.Applicative
import Control.Monad
import Data.Array
import Data.Bits
import Data.Bool
import Data.Char
import Data.Function
import Data.List
import Text.Printf

import Data.Monoid
import Data.IntMap qualified as IM
import Data.IntSet qualified as IS
import Data.Map qualified as M
import Data.Set qualified as S
import Data.Tree qualified as T
import Data.Vector qualified as V

import Debug.Trace qualified as Debug

debug :: Bool
debug = () == ()

type I = String
type O = String

type Dom   = [I]
type Codom = O

type Solver = Dom -> Codom

solve :: Solver
solve = \ case
    ss -> bool (S.elemAt 0 cap) "satisfiable" (S.null cap) where
        cap = uncurry S.intersection $ S.fromList . map (drop 1) *** S.fromList
            $ partition (("!" ==) . take 1) ss

toDom     :: [[I]] -> Dom
toDom     = \ case
    _:ss -> concat ss
    _   -> invalid $ "toDom: " ++ show @Int __LINE__

fromCodom :: Codom -> [[O]]
fromCodom = \ case
    r -> [[r]]

wrap :: Solver -> ([[I]] -> [[O]])
wrap f = fromCodom . f . toDom

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

instance InterfaceForOJS Integer where
    readB = readInteger
    showB = showInteger

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

readInteger :: B.ByteString -> Integer
readInteger = fst . fromJust . B.readInteger

showInteger :: Integer -> B.ByteString
showInteger = B.pack . show

readStr :: B.ByteString -> String
readStr = B.unpack

showStr :: String -> B.ByteString
showStr = B.pack

readDbl :: B.ByteString -> Double
readDbl = read . B.unpack

showDbl :: Double -> B.ByteString
showDbl = B.pack . show

{- Bonsai -}

{- debug -}
trace :: String -> a -> a
trace | debug     = Debug.trace
      | otherwise = const id

tracing :: Show a => a -> a
tracing = trace . show <*> id

{- error -}
impossible :: String -> a
impossible msg = error $ msg ++ ", impossible"

invalid :: String -> a
invalid msg = error $ msg ++ ", invalid input"

{- TreeCon -}
class Functor t => TreeCon t where
    branches :: t a -> [t a]

dfs :: TreeCon t => t a  -> [t a]
dfs t = t : concatMap dfs (branches t)

bfs :: TreeCon t => t a -> [t a]
bfs = concat . levels 

levels :: TreeCon t => t a -> [[t a]]
levels t = [t] : foldr (lgzw (++)) [] (map levels (branches t))

lgzw :: (a -> a -> a) -> [a] -> [a] -> [a]
lgzw f (x:xs) (y:ys) = f x y : lgzw f xs ys
lgzw _ xs [] = xs
lgzw _ [] ys = ys

depth :: TreeCon t => t a -> Int
depth = succ . foldl' max 0 . map depth . branches

paths :: TreeCon t => t a -> [[t a]]
paths = \ case
    t | null br   -> [[t]]
      | otherwise -> [ t:p | b <- br, p <- paths b ]
        where
            br = branches t

instance TreeCon T.Tree where
    branches :: T.Tree a -> [T.Tree a]
    branches t = t.subForest

{- list -}
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
    _ -> error $ "combinations: " ++ show @Int __LINE__ ++ ", negative"

{- binominal coefficients -}
nCr :: Integral a => a -> a -> a
nCr n r
    | n < 0  || r < 0  || n < r  = error $ "nCr: " ++ show @Int __LINE__ ++ ", negative "
    | n == 0 || r == 0 || n == r = 1
    | otherwise                  = iter 1 n 1
    where
        r' = min r (n-r)
        iter p m = \ case
            q | q > r'    -> p
              | otherwise -> iter (p * m `div` q) (pred m) (succ q)

{- partial permutation -}
nPr :: Integral a => a -> a -> a
nPr n r = product (genericTake r [n, pred n .. 1])

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
>>> splice 5 "abcdefghij"
["abcde","bcdef","cdefg","defgh","efghi","fghij"]
-}
splice :: Int -> [a] -> [[a]]
splice n = (!! n) . transpose . map inits . tails

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

{- list-tuple transformations -}
toTuple :: [a] -> (a,a)
toTuple = \ case
    x:y:_ -> (x,y)
    _     -> error $ "toTuple: too short list"

fromTuple :: (a,a) -> [a]
fromTuple (x,y) = [x,y]

toTriple :: [a] -> (a,a,a)
toTriple = \ case
    (x:y:z:_) -> (x,y,z)
    _         -> error $ "toTriple: too short list"

fromTriple :: (a,a,a) -> [a]
fromTriple = \ case
    (x,y,z) -> [x,y,z]

{- counting -}
countif :: (a -> Bool) -> [a] -> Int
countif = iter 0
    where
        iter a p (x:xs) = iter (bool a (succ a) (p x)) p xs
        iter a _ []     = a

countWhile :: (a -> Bool) -> (a -> a) -> a -> Int
countWhile = iter 0 where
    iter c p f = \ case
        !x | p x       -> iter (succ c) p f (f x)
           | otherwise -> c

{- Union-Find -}
data UF
    = UF
    { parent :: IM.IntMap Int
    , size   :: IM.IntMap Int
    }

newUF :: Int -> Int -> UF
newUF s t
    = UF
    { parent = IM.fromList $ (,-1) <$> [s .. t]
    , size   = IM.fromList $ (,1)  <$> [s .. t]
    }

root :: UF -> Int -> Int
root uf = \ case
    x | p == -1   -> x
      | otherwise -> root uf p
      where
        p = uf.parent IM.! x

unite :: UF -> Int -> Int -> UF
unite uf x y = if
    | x' == y' -> uf
    | szx > szy -> update uf x' (y', szy)
    | otherwise -> update uf y' (x', szx)
    where
        x' = root uf x
        y' = root uf y
        szx = uf.size IM.! x'
        szy = uf.size IM.! y'
        update :: UF -> Int -> (Int, Int) -> UF
        update u a (b, szb)
            = u
            { parent = IM.insert b a u.parent
            , size   = IM.adjust (+ szb) a u.size
            }

isSame :: UF -> Int -> Int -> Bool
isSame uf x y = root uf x == root uf y

{- array -}
scanArray :: (Ix i, Enum i)
          => (a -> b)
          -> (b -> a -> b)
          -> (b -> b -> b -> a -> b)
          -> Array (i,i) a -> Array (i,i) b
scanArray f g h sa = ta where
    ta  = listArray (bounds sa) (phi <$> assocs sa)
    phi = \ case
        (ij@(i,j),a)
            | ij == ij0 -> f a
            | i  == i0  -> g (ta ! second pred ij) a
            | j  == j0  -> g (ta ! first  pred ij) a
            | otherwise -> h (ta ! (pred *** pred) ij) (ta ! first  pred ij) (ta ! second pred ij) a
            where
                ij0 = fst (bounds sa)
                i0  = fst ij0
                j0  = snd ij0

neighbors4 :: (Ix i, Enum i) => ((i,i),(i,i)) -> (i,i) -> [(i,i)]
neighbors4 (ij0@(i0,j0),hw@(h,w)) = \ case
    ij@(i,j) 
        | ij == ij0    -> [                second succ ij,                first succ ij]
        | ij == (i0,w) -> [second pred ij,                                first succ ij]
        | ij == hw     -> [second pred ij,                 first pred ij               ]
        | ij == (h,j0) -> [                second succ ij, first pred ij               ]
        | i  == i0     -> [second pred ij, second succ ij,                first succ ij]
        | j  == j0     -> [                second succ ij, first pred ij, first succ ij]
        | i  == h      -> [second pred ij, second succ ij, first pred ij               ]
        | j  == w      -> [second pred ij,                 first pred ij, first succ ij]
        | otherwise    -> [second pred ij, second succ ij, first pred ij, first succ ij]

neighbors4Array :: (Ix i, Enum i) => (a -> Bool, Array (i,i) a) -> Array (i,i) (S.Set (i,i))
neighbors4Array (p,a) = listArray (bounds a) (S.fromList . filter (p . (a !)) . neighbors4 (bounds a) <$> range (bounds a))

bfs4Array :: (Ix i, Enum i, Ord i)
          => Array (i,i) (S.Set (i,i)) -> (i,i) -> [S.Set (i,i)]
bfs4Array a ij = unfoldr psi (S.empty, S.singleton ij) where
    psi = \ case
        (vs,ns)
            | S.null ns' -> Nothing
            | otherwise  -> Just (ns, (vs',ns'))
            where
                ns' = S.difference (S.unions $ S.map (a !) ns) vs
                vs' = S.union vs ns

{- Cartesian Product -}
cp :: [[a]] -> [[a]]
cp = \ case
    []     -> [[]]
    xs:xss -> [ x : ys | x <- xs, ys <- yss ]
        where
            yss = cp xss

{- integer arithmetic -}

isqrt :: Integral a => a -> a
isqrt = fromInteger . sqrtI . toInteger

infixr 8 ^!

(^!) :: Num a => a -> Int -> a
(^!) x n = x^n

averageI :: Integer -> Integer -> Integer
averageI m n = (m + n) `div` 2

sqrtI :: Integer -> Integer
sqrtI = \ case
    m@(_n+2)      -> until (good m) (improve m) 1
    m | m < 0     -> error "sqrtI: negative"
      | otherwise -> m
    where 
        good x g = g ^! 2 <= x && x < succ g ^! 2
        improve x g = averageI g (x `div` g)

{- modular arithmetic -}
base :: Int
base = 10^(9::Int) + 7

madd :: Int -> Int -> Int
madd !m !n = (m + n) `mod` base

msub :: Int -> Int -> Int
msub !m = madd m . negate

mmul :: Int -> Int -> Int
mmul !m !n = m * n `mod` base

mexpt :: Int -> Int -> Int
mexpt !b = \ case
    0             -> 1
    o | odd o     -> mmul b (mexpt b (pred o))
      | otherwise -> mexpt (mmul b b) (o `div` 2)

{- prime numbers -}

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

primesLT1000000 :: () -> [Int]
primesLT1000000 () = takeWhile (1000000 >) primes

primes :: [Int]
primes = small ++ large
    where
        (p,candidates) = case roll (mkWheel small) of
            _:x:xs -> (x,xs)
            _      -> impossible $ "primes: at "++ show @Int __LINE__
        small          = [2,3,5,7]
        large          = p : filter isPrime candidates
        isPrime n      = all (not . divides n) 
                       $ takeWhile (\ pr -> pr * pr <= n) large
        divides n pr   = n `mod` pr == 0

data Wheel = Wheel Int [Int]

roll :: Wheel -> [Int]
roll (Wheel n rs) = [ n * k + r | k <- [0 ..], r <- rs ]

nextSize :: Wheel -> Int -> Wheel
nextSize (Wheel n rs) p
    = Wheel (p * n) [ r2 | k <- [0 .. pred p], r <- rs
                         , let r2 = n*k+r, r2 `mod` p /= 0 ]

mkWheel :: [Int] -> Wheel
mkWheel = foldl' nextSize w0 where
    w0 = Wheel 1 [1]

{- bits -}
bitPat :: Bits a => a -> Int -> [Bool]
bitPat a w = map (testBit a) $ reverse [0 .. pred w]

selectPat :: [Bool] -> [a] -> [a]
selectPat pat = catMaybes . zipWith (bool (const Nothing) Just) pat

{- Dummy -}
_Comparing :: Ord a => (b -> a) -> b -> b -> Ordering
_Comparing = comparing
_LiftA :: Applicative f => (a -> b) -> f a -> f b
_LiftA = liftA
_Join :: Monad m => m (m a) -> m a
_Join = join
_Printf :: PrintfType r => String -> r
_Printf = printf

_DigitToInt :: Char -> Int
_DigitToInt = digitToInt
_On :: (b -> b -> c) -> (a -> b) -> a -> a -> c
_On = on
_ISempty :: IS.IntSet
_ISempty = IS.empty
_Mempty :: Ord a => M.Map a b
_Mempty = M.empty
_Tflatten :: T.Tree a -> [a]
_Tflatten = T.flatten
_Vlength :: V.Vector a -> Int
_Vlength = V.length
