{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use foldr" #-}
{-# HLINT ignore "Redundant bracket" #-}
module HW5 where

import Prelude hiding (and, concat, replicate, (!!), elem, filter, map)
import Data.Char (chr, isLower, ord)
import GHC.CmmToAsm.AArch64.Instr (x0)

-- Ch.05
--original Caesar encoder
encode :: Int -> String -> String
encode n xs = [shift n x | x <- xs]

shift :: Int -> Char -> Char
shift n c | isLower c = int2let $ mod (let2int c + n) 26
 | otherwise = c

let2int :: Char -> Int
let2int c = ord c - ord 'a'

int2let :: Int -> Char
int2let n = chr $ ord 'a' + n

-- Problem #1: Caesar crack

table :: [Float]
table = [8.1, 1.5, 2.8, 4.2, 12.7, 2.2, 2.0, 6.1, 7.0, 0.2, 0.8, 4.0, 2.4, 6.7, 7.5, 1.9, 0.1, 6.0, 6.3, 9.0, 2.8, 1.0, 2.4, 0.2, 2.0, 0.1]

position :: Eq a => a -> [a] -> Int
position _ [] = undefined
position x (y:ys)
    | x==y = 0
    | otherwise = position x ys +1

rotate :: Int -> [a] -> [a]
rotate x y = [ myget y ((tp+x)`mod`length y) | tp<-[0..length y-1] ]

crack :: String -> String
crack xs = encode (-factor) xs
 where
 -- minimum: exported by Prelude
 factor = position (minimum chitab) chitab
 -- 计算每种加密偏移量下的chisqr
 chitab = [chisqr (rotate n table') table | n <- [0..25]]
 -- 计算密⽂中字⺟的出现频率
 table' = freqs xs

mycount :: String -> Char -> Int
mycount "" _ = 0
mycount (x:xs) y
    | x==y = mycount xs y +1
    | otherwise = mycount xs y
--summary
freqs :: String -> [Float]
freqs x = [ (fromIntegral (mycount x (int2let tp)) / fromIntegral (length x)) * 100.0 | tp <- [0..25] ]

--feature or called likeability
--compared with table
chisqr :: [Float] -> [Float] -> Float
chisqr x y = mysum [ (myget x tp - myget y tp)^2/myget y tp | tp <- [0..(length x -1)] ]
-- End Problem #1

-- Problem #2: Pythagorean triples
pyths :: Int -> [(Int, Int, Int)]
pyths n = [ (x,y,z) | x<-[1..n] , y<-[1..n] , z<-[1..n] , x^2+y^2==z^2 ]
-- End Problem #2

divisors :: Int -> [Int]
divisors n = [ x | x<-[1..(n-1)] , n `mod` x == 0 ]

mysum :: Num a => [a] -> a
mysum [] = 0
mysum (x:xs) = x + mysum xs

-- Problem #3: perfect integers
perfects :: Int -> [Int]
perfects n = [ x | x<-[1..n] , mysum (divisors x)==x]
-- End Problem #3

myget :: [a] -> Int -> a
myget [] _ = undefined
myget (x:xs) 0 = x
myget (x:xs) n = myget xs (n-1)

-- Problem #4: scalar product
scalarProduct :: Num a => [a] -> [a] -> a
scalarProduct x y = mysum [ myget x t * myget y t | t<-[0..(length x - 1)] ]
-- End Problem #4

-- Ch.06

-- Problem #5: define prelude functions using recursions
and :: [Bool] -> Bool
and [] = True
and (x:xs) = x && and xs

concat :: [[a]] -> [a]
concat [] = []
concat (x:xs) = x ++ concat xs

replicate :: Int -> a -> [a]
replicate 0 _ = []
replicate n x = x : replicate (n-1) x

--but I  add error throw-out
(!!) :: [a] -> Int -> a
(!!) [] _ = undefined
(!!) x 0 = head x
(!!) x n = (!!) (tail x) (n-1)

elem :: Eq a => a -> [a] -> Bool
elem a [] = False
elem a (x:xs) = (x==a) || elem a xs
-- End Problem #5

-- Problem #6: merge ascending lists
merge :: Ord a => [a] -> [a] -> [a]
merge x [] = x
merge [] y = y
merge (x:xs) (y:ys) = if x<=y then x : merge xs (y:ys) else y : merge (x:xs) ys
-- End Problem #6

-- Problem #7: merge sort
msort :: Ord a => [a] -> [a]
msort [] = []
msort [x] = [x]
msort seq = merge sbseq1 sbseq2
    where
        len=length seq
        sbseq1=msort (take (len `div` 2) seq)
        sbseq2=msort (drop (len `div` 2) seq)

-- End Problem #7
