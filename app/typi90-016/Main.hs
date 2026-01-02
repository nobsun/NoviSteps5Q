{-# LANGUAGE CPP #-}
{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LexicalNegation #-}
{-# LANGUAGE LambdaCase, MultiWayIf #-}
{-# LANGUAGE NPlusKPatterns #-}
{-# LANGUAGE DataKinds, PolyKinds, NoStarIsType, TypeFamilyDependencies, UndecidableInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unused-imports, -Wno-x-partial #-}
module Main where

import Data.ByteString.Char8 qualified as B
import Data.Maybe
import Data.Ord

import Control.Arrow
import Control.Applicative
import Control.Monad
import Control.Monad.State
import Data.Array
import Data.Array.Unboxed qualified as A
import Data.Bits
import Data.Bool
import Data.Char
import Data.Function
import Data.List
import Data.List.Extra
import Data.Monoid
import Data.Tuple
import Text.Printf

import Data.IntMap qualified as IM
import Data.IntSet qualified as IS
import Data.Map qualified as M
import Data.Set qualified as S
import Data.Tree qualified as T
import Data.Sequence qualified as Q
import Data.Vector.Unboxed qualified as V

import Debug.Trace qualified as Debug

{- $setup
>>> :set -XOverloadedStrings
-}
debug :: Bool
debug = () /= ()

type I = Int
type O = Int

type Dom   = (I,I,I,I)
type Codom = O

type Solver = Dom -> Codom

solve :: Solver
solve = \ case
    (a',b',c',n) -> case sort [a',b',c'] of
        [a,b,c] -> undefined
            where
                zs = [ n - c*d | d <- [0 .. n `div` c] ]
                ys m = (b *) <$> [0 .. m `div` b]
                xs m = (a *) <$> [0 .. m `div` a]                
        _       -> impossible ""

decode :: [[I]] -> Dom
decode = \ case
    [a,b,c,n]:_ -> (a,b,c,n)
    _   -> invalid $ "toDom: " ++ show @Int __LINE__

encode :: Codom -> [[O]]
encode = \ case
    r -> [[r]]

main :: IO ()
main = B.interact (detokenize . encode . solve . decode . entokenize)

class AsToken a where
    readB :: B.ByteString -> a
    readBs :: B.ByteString -> [a]
    readBs = map readB . B.words
    entokenize :: B.ByteString -> [[a]]
    entokenize = map readBs . B.lines

    showB :: a -> B.ByteString
    showBs :: [a] -> B.ByteString
    showBs = B.unwords . map showB
    detokenize :: [[a]] -> B.ByteString
    detokenize = B.unlines . map showBs

instance AsToken B.ByteString where
    readB :: B.ByteString -> B.ByteString
    readB = id
    showB :: B.ByteString -> B.ByteString
    showB = id

instance AsToken Int where
    readB :: B.ByteString -> Int
    readB = readInt
    showB :: Int -> B.ByteString
    showB = showInt

instance AsToken Integer where
    readB :: B.ByteString -> Integer
    readB = readInteger
    showB :: Integer -> B.ByteString
    showB = showInteger

instance AsToken String where
    readB :: B.ByteString -> String
    readB = readStr
    showB :: String -> B.ByteString
    showB = showStr

instance AsToken Double where
    readB :: B.ByteString -> Double
    readB = readDbl
    showB :: Double -> B.ByteString
    showB = showDbl

instance AsToken Char where
    readB :: B.ByteString -> Char
    readB = B.head
    showB :: Char -> B.ByteString
    showB = B.singleton
    readBs :: B.ByteString -> [Char]
    readBs = B.unpack
    showBs :: [Char] -> B.ByteString
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

{- * Bonsai -}
{- ** Arithmetic -}
base :: Int
base = 10^(9::Int) + 7

factCacheSize :: Int
factCacheSize = 4 * 10 ^ (6 :: Int)

{- | ceiling divide 
>>> 7 `div` 3
2
>>> 7 `cdiv` 3
3
>>> 12 `div` 3
4
>>> 12 `cdiv` 3
4
-}
cdiv :: (Integral a) => a -> a -> a
cdiv = (negate .) . div . negate

infixl 7 `cdiv`

{- | Int exponent 
-}
(^!) :: (Num a) => a -> Int -> a
(^!) = (^)

infixr 8 ^!

{- | binominal coefficients
-}
nCr :: Integral a => a -> a -> a
nCr n r
    | n < 0  || r < 0            = error $ "nCr: " ++ show @Int __LINE__ ++ ", negative "
    | n < r                      = 0
    | n == 0 || r == 0 || n == r = 1
    | otherwise                  = iter 1 n 1
    where
        r' = min r (n-r)
        iter p m = \ case
            q | q > r'    -> p
              | otherwise -> iter (p * m `div` q) (pred m) (succ q)

{- | partial permutation
-}
nPr :: Integral a => a -> a -> a
nPr n r 
    | r == 0    = 1
    | n == 0    = 0 
    | n <  r    = 0
    | otherwise = product (genericTake r [n, pred n .. 1])

{- | factorials pool
-}
factorials :: [Integer]
factorials = scanl' (*) 1 [1 ..]

{- integer arithmetic -}
isqrt :: Integral a => a -> a
isqrt = fromInteger . sqrtI . toInteger

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
modulus :: Int
modulus = base

euclidEx :: Int -> Int -> (Int,Int,Int)
euclidEx = f 1 0 0 1 where
    f s t s' t' a = \ case
        0 -> (a, s, t)
        b -> f s' t' (s - q * s') (t - q * t') b r
            where 
                (q, r) = divMod a b

mrecip :: Int -> Int
mrecip a = case euclidEx a modulus of
    (1, s, _)  -> s `mod` modulus
    (-1, s, _) -> -s `mod` modulus
    _          -> invalid $ show @Int __LINE__

minv :: Mod -> Mod
minv (Mod m) = Mod (mrecip m)

mnCr :: Int -> Int -> Mod
mnCr n r = a * minv b where
    a = mfact n
    b = mfact r * mfact (n - r)

mfact :: Int -> Mod
mfact = (mfactab !) 

mfactab :: Array Int Mod
mfactab = listArray (0,factCacheSize) $ scanl' (*) (1 :: Mod) 
        $ Mod <$> take factCacheSize [(1 :: Int) ..]

newtype Mod = Mod Int
    deriving (Eq, Show, Read)

instance Num Mod where
    Mod m + Mod n = Mod (m `madd` n)
    Mod m * Mod n = Mod (m `mmul` n)
    negate (Mod m) = Mod (m `mmul` negate 1)
    fromInteger n = Mod (fromInteger (n `mod` fromIntegral @Int modulus))
    abs = undefined
    signum = undefined

toMod :: Int -> Mod
toMod m = Mod (m `mod` modulus)

fromMod :: Mod -> Int
fromMod (Mod m) = m

madd :: Int -> Int -> Int
madd !m !n = (m + n) `mod` modulus

msub :: Int -> Int -> Int
msub !m = madd m . negate

mmul :: Int -> Int -> Int
mmul !m !n = m * n `mod` modulus

mexpt :: Int -> Int -> Int
mexpt !b = \ case
    0             -> 1
    o | odd o     -> mmul b (mexpt b (pred o))
      | otherwise -> mexpt (mmul b b) (o `div` 2)

{- prime numbers -}
factors :: Int -> IS.IntSet
factors n = iter IS.empty (isqrt n) where
    iter s = \ case
        0 -> s
        d -> case divMod n d of
            (q,0) -> iter (IS.insert d (IS.insert q s)) (pred d)
            _     -> iter s (pred d)

primeFactors :: Int -> [Int]
primeFactors n = unfoldr f (n,2)
    where
        f = \ case
            (1,_) -> Nothing
            (m,p) | m < p^!2  -> Just (m,(1,m))
                  | otherwise -> case divMod m p of
                (q,0) -> Just (p,(q,p))
                _ | p == 2    -> f (m,3)
                  | otherwise -> f (m,p+2)

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
        isPrime n      = not $ any (divides n)
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
selectPat = \ case
    True:bs -> \ case
        y:ys    -> y : selectPat bs ys
        _       -> []
    _:bs    -> \ case
        _:ys    -> selectPat bs ys
        _       -> []
    _       -> const []

{- ** Data Structure -}

{- | TreeLike 
-}
class TreeLike t where
    branches :: t -> [t]

dfs :: TreeLike t => t -> [t]
dfs t = t : concatMap dfs (branches t)

bfs :: TreeLike t => t -> [t]
bfs = concat . levels 

levels :: TreeLike t => t -> [[t]]
levels t = [t] : foldr (lgzw (++) . levels) [] (branches t)

lgzw :: (a -> a -> a) -> [a] -> [a] -> [a]
lgzw f (x:xs) (y:ys) = f x y : lgzw f xs ys
lgzw _ xs [] = xs
lgzw _ [] ys = ys

depth :: TreeLike t => t -> Int
depth = succ . foldl' max 0 . map depth . branches

paths :: TreeLike t => t -> [[t]]
paths = \ case
    t | null br   -> [[t]]
      | otherwise -> [ t:p | b <- br, p <- paths b ]
        where
            br = branches t

instance TreeLike (T.Tree a) where
    branches :: T.Tree a -> [T.Tree a]
    branches = T.subForest

{- *** Union-Find -}
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
        p = parent uf IM.! x

unite :: UF -> Int -> Int -> UF
unite uf x y = if
    | x' == y' -> uf
    | szx > szy -> update uf x' (y', szy)
    | otherwise -> update uf y' (x', szx)
    where
        x' = root uf x
        y' = root uf y
        szx = size uf IM.! x'
        szy = size uf IM.! y'
        update :: UF -> Int -> (Int, Int) -> UF
        update u a (b, szb)
            = u
            { parent = IM.insert b a (parent u)
            , size   = IM.adjust (+ szb) a (size u)
            }

isSame :: UF -> Int -> Int -> Bool
isSame uf x y = root uf x == root uf y

{- | DeQueue
-}
class DeQueue q where
    emptyDQ :: q a
    nullDQ  :: q a -> Bool
    consDQ  :: a -> q a -> q a
    snocDQ  :: q a -> a -> q a
    dequeueL :: b -> (a -> q a -> b) -> q a -> b
    dequeueR :: b -> (q a -> a -> b) -> q a -> b

instance DeQueue Q.Seq where
    emptyDQ :: Q.Seq a
    emptyDQ = Q.empty
    nullDQ :: Q.Seq a -> Bool
    nullDQ  = Q.null
    consDQ :: a -> Q.Seq a -> Q.Seq a
    consDQ  = (Q.<|)
    snocDQ  :: Q.Seq a -> a -> Q.Seq a
    snocDQ  = (Q.|>)
    dequeueL :: b -> (a -> Q.Seq a -> b) -> Q.Seq a -> b
    dequeueL z f dq = case Q.viewl dq of
        Q.EmptyL  -> z
        a Q.:< aq -> f a aq
    dequeueR :: b -> (Q.Seq a -> a -> b) -> Q.Seq a -> b
    dequeueR z f dq = case Q.viewr dq of
        Q.EmptyR  -> z
        aq Q.:> a -> f aq a

{- *** Array -}
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
        | ij == ij0    -> filter p [                second succ ij,                first succ ij]
        | ij == (i0,w) -> filter p [second pred ij,                                first succ ij]
        | ij == hw     -> filter p [second pred ij,                 first pred ij               ]
        | ij == (h,j0) -> filter p [                second succ ij, first pred ij               ]
        | i  == i0     -> filter p [second pred ij, second succ ij,                first succ ij]
        | j  == j0     -> filter p [                second succ ij, first pred ij, first succ ij]
        | i  == h      -> filter p [second pred ij, second succ ij, first pred ij               ]
        | j  == w      -> filter p [second pred ij,                 first pred ij, first succ ij]
        | otherwise    -> filter p [second pred ij, second succ ij, first pred ij, first succ ij]
    where
        p (x,y) = and [i0 <= x, x <= h, j0 <= y, y <= w]

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

{- ** List -}
{- | recursion schemes on List
-}
cataL :: (a -> b -> b) -> b -> [a] -> b
cataL = foldr

paraL :: (a -> ([a], b) -> b) -> b -> [a] -> b
paraL phi z = \ case
    x:xs -> phi x (xs, paraL phi z xs)
    []   -> z

anaL :: (a -> Maybe (b, a)) -> a -> [b]
anaL = unfoldr

apoL :: (a -> Maybe (b, Either a [b])) -> a -> [b]
apoL psi u = case psi u of
    Nothing           -> []
    Just (y,Left v)   -> y : apoL psi v
    Just (y,Right ys) -> y : ys

{- | mapMaybeAccumL
>>> mapMaybeAccumL (\ acc x -> bool (acc, Nothing) (succ acc, Just x) (x < 5)) 0 [3,1,4,1,5,9]
(4,[3,1,4,1])
-}
mapMaybeAccumL :: (acc -> a -> (acc, Maybe b)) -> acc -> [a] -> (acc, [b])
mapMaybeAccumL phi acc0 = \ case
    []   -> (acc0, [])
    x:xs -> case phi acc0 x of
        (acc, my) -> maybe id (second . (:)) my $ mapMaybeAccumL phi acc xs

{- *** List utilities -}
{- | combinations
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

{- *** Permutations -}
{- |
>>> p0 = [1 .. 4] :: [Int]
>>> px = [3,1,4,2]
>>> inversions px
[(3,2),(1,0),(4,1),(2,0)]
>>> permToNum px
13
>>> numToPerm p0 13
[3,1,4,2]
>>> numToPerm p0 12
[3,1,2,4]
>>> numToPerm p0 14
[3,2,1,4]
>>> nextPerm [3,1,2,4]
[3,1,4,2]
>>> prevPerm [3,1,4,2]
[3,1,2,4]
-}
inversions :: Ord a => [a] -> [(a, Int)]
inversions = paraL phi [] where
    phi x (xs,ys) = (x, countif (< x) xs) : ys

permToNum :: Ord a => [a] -> Integer
permToNum xs = sum (zipWith (*) ds ws) where
    n  = length xs
    ds = toInteger . snd <$> inversions xs
    ws = reverse $ take n factorials

numToPerm :: [a] -> Integer -> [a]
numToPerm as0 n = snd $ mapAccumL phi as0 rs where
    k   = genericLength as0
    rs  = map fromInteger 
        $ reverse 
        $ snd 
        $ mapAccumL divMod n [1 .. k]
    phi as r = case splitAt r as of
        (bs,a:cs) -> (bs ++ cs,a)
        _         -> impossible $ "numToPerm: " ++ show @Int __LINE__

nextPerm :: (Ord a) => [a] -> [a]
nextPerm xs = last
    [ list [] (phi ys zs0) zs1
    | (ys, zs@(z0:z1:_)) <- zip (inits xs) (tails xs)
    , z0 < z1
    , let (zs0, zs1) = span (z0 >=) $ sort zs
    ]
    where
        phi as bs c cs = as ++ c : bs ++ cs
    
prevPerm :: (Ord a) => [a] -> [a]
prevPerm xs = last
    [ list [] (phi ys zs0) zs1
    | (ys, zs@(z0:z1:_)) <- zip (inits xs) (tails xs)
    , z0 > z1
    , let (zs0, zs1) = span (z0 <=) $ sortOn Down zs
    ]
    where
        phi as bs c cs = as ++ c : bs ++ cs

{- | spanCount
>>> spanCount odd [3,1,4,1,5,9]
(2,[4,1,5,9])
-}
spanCount :: (a -> Bool) -> [a] -> (Int, [a])
spanCount p = \ case
    x:xs | p x -> case spanCount p xs of
        (m,ys)     -> (succ m, ys)
    xs         -> (0,xs)

{- Run Length Encode -}
type RLE a = [(a, Int)]

toRLE :: Eq a => [a] -> RLE a
toRLE = unfoldr psi where
    psi = \ case
        x:xs -> case spanCount (x ==) xs of
            (m,ys) -> Just ((x, succ m), ys)
        _    -> Nothing

fromRLE :: RLE a -> [a]
fromRLE = (uncurry (flip replicate) =<<)

rleSplitAt :: Int -> RLE a -> (RLE a, RLE a)
rleSplitAt = \ case
    n+1 -> \ case
        h@(x,m+1):rs
            | n < m     -> ([(x,n+1)],(x,m-n):rs)
            | otherwise -> case rleSplitAt (n-m) rs of
                (as,bs)     -> (h:as,bs)
        _               -> ([],[])
    _   -> ([],)

{- |
>>> runLength "aaaabbbcddeeeeeefghhhh"
[('a',4),('b',3),('c',1),('d',2),('e',6),('f',1),('g',1),('h',4)]
-}
runLength :: Eq a => [a] -> [(a, Int)]
runLength = toRLE

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

{- *** Zipper -}

type Zp a = ([a],[a])

toZp :: [a] -> Zp a
toZp = ([],)

fromZp :: Zp a -> [a]
fromZp = \ case
    (as,bs) -> foldl' (flip (:)) bs as

mvL :: Zp a -> Zp a
mvL = \ case
    (a:as,bs) -> (as,a:bs)
    z         -> z

mvR :: Zp a -> Zp a
mvR = \ case
    (as,b:bs) -> (b:as,bs)
    z         -> z

mvLwhile :: (a -> Bool) -> Zp a -> Either (Zp a) (Zp a)
mvLwhile p = \ case
    aasbs@([],_)    -> Left aasbs
    aasbs@(a:as,bs)
        | p a       -> mvLwhile p (as,a:bs)
        | otherwise -> Right aasbs

mvRwhile :: (a -> Bool) -> Zp a -> Either (Zp a) (Zp a)
mvRwhile p = \ case
    asbbs@(_,[]) -> Left asbbs
    asbbs@(as,b:bs)
        | p b       -> mvRwhile p (b:as,bs)
        | otherwise -> Right asbbs

{- *** list-tuple transformations -}
toTuple :: [a] -> (a,a)
toTuple = \ case
    x:y:_ -> (x,y)
    _     -> error  "toTuple: too short list"

fromTuple :: (a,a) -> [a]
fromTuple (x,y) = [x,y]

toTriple :: [a] -> (a,a,a)
toTriple = \ case
    (x:y:z:_) -> (x,y,z)
    _         -> error "toTriple: too short list"

fromTriple :: (a,a,a) -> [a]
fromTriple = \ case
    (x,y,z) -> [x,y,z]

fst3 :: (a,b,c) -> a
fst3 (x,_,_) = x

snd3 :: (a,b,c) -> b
snd3 (_,y,_) = y

thd3 :: (a,b,c) -> c
thd3 (_,_,z) = z

{- *** counting -}
{- | countif 
>>> countif even [3,1,4,1,5,9,2,6,5,3,5,8,7,9]
4
-}
countif :: (a -> Bool) -> [a] -> Int
countif p = foldl' phi 0
    where
        phi acc x = bool acc (succ acc) (p x)

countWhile :: (a -> Bool) -> (a -> a) -> a -> Int
countWhile = iter 0 where
    iter c p f = \ case
        !x | p x       -> iter (succ c) p f (f x)
           | otherwise -> c

{- *** rotate matrix -}

rotCW :: [[a]] -> [[a]]
rotCW = transpose . reverse

rotCCW :: [[a]] -> [[a]]
rotCCW = reverse . transpose

rotPI :: [[a]] -> [[a]]
rotPI = reverse . map reverse

{- | Cartesian Product -}
cp :: [[a]] -> [[a]]
cp = \ case
    []     -> [[]]
    xs:xss -> [ x : ys | x <- xs, ys <- yss ]
        where
            yss = cp xss

{- ** Algorithm -}
{- Thining -}

thinBy :: (a -> a -> Bool) -> [a] -> [a]
thinBy cmp = foldr bump []
    where
        bump x = \ case
            []   -> singleton x
            y:ys
                | x `cmp` y -> x : ys
                | y `cmp` x -> y : ys
                | otherwise -> x:y:ys

{- 0/1 knapsack problem -}

type KsName       = String
type KsValue      = Int
type KsWeight     = Int
type KsItem       = (KsValue, KsWeight)
type KsItem3      = (KsName, KsValue, KsWeight)
type KsSelection3 = ([KsName], KsValue, KsWeight)

{- |
>>> items = (\ (x,y) -> (y,x)) <$> [(30,14),(67,31),(19,8),(50,24)] :: [(KsWeight,KsValue)]
>>> a0    = A.listArray (0,50) (repeat 0) :: A.UArray KsWeight KsValue
>>> let ?ksArray0 = a0 in swag 50 items
99
-}
swag :: (?ksArray0 :: A.UArray KsWeight KsValue)
     => KsWeight -> [(KsWeight, KsValue)] -> KsValue
swag w = maximum . A.elems . ksValues w

ksValues :: (?ksArray0 :: A.UArray KsWeight KsValue)
         => KsWeight -> [(KsWeight, KsValue)] -> A.UArray KsWeight KsValue
ksValues ubw = foldl' step ?ksArray0 where
    step aa (w,v) = A.accum max aa [(r1, s + v) | (r,s) <- A.assocs aa, let r1 = r + w, r1 <= ubw]

ksName :: KsItem3 -> KsName
ksName = fst3

ksValue :: (a,KsValue,KsWeight) -> KsValue
ksValue = snd3

ksWeight :: (a,KsValue,KsWeight) -> KsWeight
ksWeight = thd3

{- |
>>> itemList = [("Laptop",30,14)::(KsName,KsValue,KsWeight),("Television",67,31),("Jewellery",19,8),("CD Collection",50,24)]
>>> a0 = listArray (0,50) (repeat ([],0,0)) :: Array KsWeight KsSelection3
>>> let {?addName = (:); ?ksSelectionArray0 = a0} in swagDP 50 itemList
(["CD Collection","Jewellery","Laptop"],99,46)
-}
swagDP :: ( ?addName :: KsName -> [KsName] -> [KsName]
          , ?ksSelectionArray0 :: Array KsWeight KsSelection3 )
       => KsWeight -> [KsItem3] -> KsSelection3
swagDP w = maximumBy (comparing ksValue) . elems . ksSelections w

ksSelections :: ( ?addName :: KsName -> [KsName] -> [KsName]
                , ?ksSelectionArray0 :: Array KsWeight KsSelection3 )
             => KsWeight -> [KsItem3] -> Array KsWeight KsSelection3
ksSelections ubw = foldl' step ?ksSelectionArray0 where
    step aa (n,v,w) = accum better aa
                    [ (r1, (?addName n (fst3 s), v + ksValue s, w + ksWeight s))
                    | (r,s) <- assocs aa, let r1 = r + w, r1 <= ubw]
    better sn1 sn2 = if ksValue sn1 >= ksValue sn2 then sn1 else sn2

{- Yet Another Memoise -}
class MemoTable t where
    emptyMemoTable  :: Ord a => t a b
    lookupMemoTable :: Ord a => a -> t a b -> Maybe b
    insertMemoTable :: Ord a => a -> b -> t a b -> t a b

class (Monad m) => MemoTableT t m where
    emptyMemoTableT  :: Ord a => t a (m b)
    lookupMemoTableT :: Ord a => a -> t a (m b) -> Maybe (m b)
    insertMemoTableT :: Ord a => a -> m b -> t a (m b) -> t a (m b)

instance MemoTable M.Map where
    emptyMemoTable  = M.empty
    lookupMemoTable = M.lookup
    insertMemoTable = M.insert

instance MemoTableT M.Map [] where
    emptyMemoTableT  = M.empty
    lookupMemoTableT = M.lookup
    insertMemoTableT = M.insert

instance (Applicative f, Num a) => Num (f a) where
    (+) = (<*>) . ((+) <$>)
    (-) = (<*>) . ((-) <$>)
    (*) = (<*>) . ((*) <$>)
    negate = (negate <$>)
    signum = (signum <$>)
    abs    = (abs    <$>)
    fromInteger = pure . fromInteger

type Memo t a b = a -> State (t a b) b

memoise :: (MemoTable t, Ord a) => Memo t a b -> Memo t a b
memoise mf x = do prev <- find x
                  case prev of
                    Just y  -> return y
                    Nothing -> do y    <- mf x
                                  ins x y
                                  return y
               where find k  = get >>= return . lookupMemoTable k
                     ins k v = get >>= put . insertMemoTable k v

evalMemo :: (MemoTable t, Ord a) => (Memo t) a b -> a -> b
evalMemo m v = evalState (m v) emptyMemoTable

runMemo :: (MemoTable t, Ord a) => t a b -> (Memo t) a b -> a -> (b, t a b)
runMemo tb m v = runState (m v) tb

gfun :: (b -> c) -> (c -> b) -> c
gfun = (fix .) . (.)

memoising :: (Ord a, MemoTable t)
          => ((a -> State (t a b) b) -> Memo t a b) -> a -> State (t a b) b
memoising = gfun memoise

-- | makes memo function from functional specified by the second argument.
--   The first argument is only for imforming type of memo table will be used.
memo :: (MemoTable t, Ord a)
     => (a -> State (t a b) b)
     -> ((a -> State (t a b) b) -> Memo t a b)
     -> (a -> b)
memo g f = evalMemo (asTypeOf (memoising f) g)

-- | makes memo function which also takes and returns memo table
-- , which can be reused.
memo' :: (MemoTable t, Ord a)
     => ((a -> State (t a b) b) -> Memo t a b)
     -> t a b
     -> (a -> (t a b, b))
memo' = ((swap .) .) . flip runMemo . memoising

{- End of Bonsai -}
