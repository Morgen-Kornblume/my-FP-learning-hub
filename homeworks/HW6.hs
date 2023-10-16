module HW6 where

import Prelude hiding (and, concat, replicate, (!!), elem, filter, map)
import Data.Char (chr)
import Data.Bits (Bits(bitSize))

-- Ch.07

-- Problem #1: desugar list comprehension using map and filter
theExpr :: (a -> Bool) -> (a -> b) -> [a] -> [b]
-- theExpr p f xs = [f x | x <- xs, p x]
theExpr p f xs = map f (filter p xs)
-- End Problem #1

-- Problem #2: redefine map/filter with foldr
filter :: (a -> Bool) -> [a] -> [a]
filter p = foldr (\x y -> if p x then x:y else y) []

map :: (a -> b) -> [a] -> [b]
map f = foldr (\x y -> f x : y) []
-- End Problem #2

-- Problem #3: error checking for binary string transmitter
type Bit = Int

bin2int :: [Bit] -> Int
bin2int = foldr (\x y -> x + 2 * y) 0

decode :: [Bit] -> String
-- modify this line to add error checking
decode bits
    | length bits `mod` 9 /= 0 = error "Invalid length"
    | otherwise = map (chr . bin2int) (chop bits)

judge :: [Bit] -> Bool
judge bits = sum (take 8 bits) `mod` 2 == sum (drop 8 bits)

chop :: [Bit] -> [[Bit]]
chop [] = []
chop bits = if judge (take 9 bits)
    then take 8 bits : chop (drop 9 bits)
    else error "Examine failed : Sth wrong happened in transmittion"
-- hint: not 'chop8' any more
-- End Problem #3
