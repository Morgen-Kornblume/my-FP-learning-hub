module HW13 where

-- Problem #1: Write a Haskell program to solve the maximum segment
--   sum problem, following the three steps in the slides.

subseg :: Int -> [(Int, Int)]
subseg n = [(i, j) | i <- [0..n-1], j <- [i..n-1]]

sumij :: [Integer] -> (Int, Int) -> Integer
sumij xs (i, j) = sum (take (j-i+1) (drop i xs))

mss :: [Integer] -> Integer
mss xs = let n = length xs
            in maximum [sumij xs (i,j) | (i,j) <- subseg n]

-- End Problem #1

-- Problem #2: Write a Haskell program to solve the maximum segment
--   sum problem, using the smart algorithm in the slides.

solve :: [Integer] -> Integer -> Integer 
solve [] m = m
solve (x:xs) m = let m' = max (x + m) 0
                  in max m' (solve xs m')

mss' :: [Integer] -> Integer
mss' xs = solve xs 0

-- End Problem #2
