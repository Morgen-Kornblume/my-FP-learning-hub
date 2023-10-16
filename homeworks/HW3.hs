{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use guards" #-}
module Main where

import System.Random
import Text.Read (Lexeme(String))

-- Problem #1: 写出阶乘函数的其他定义：
-- Part #1.1: 使用条件方程组
factGuard :: Integer -> Integer
factGuard n
  | n == 0 = 1
  | n > 0 = n * factGuard (n - 1)
  | otherwise = error "factGuard: negative argument"
-- End Part #1.1

-- Part #1.2: 使用分支表达式
factBranch :: Integer -> Integer
factBranch n = if n<0
  then error "factBranch: negative argument"
  else if n==0
    then 1
    else n * factBranch (n - 1)
-- End Part #1.2
-- End Problem #1

-- Problem #2: 猜数字小游戏
--first we generate a random integar between 1 and 100
--then we ask the user to guess the number
--if the user's guess is too high, we tell them
--if the user's guess is too low, we tell them
--if the user's guess is correct, we tell them and end the game
guessloop :: (Int,Int) -> IO ()
guessloop (x,num)
  | x>100||x<1 = do
    putStrLn "WTF?! Please enter a number between 1 and 100!"
    str1  <- getLine
    let x = read str1 :: Int
    guessloop (x,num)
  |x>num = do
    putStrLn "Too large!"
    str1  <- getLine
    let x = read str1 :: Int
    guessloop (x,num)
  |x<num = do
    putStrLn "Too small!"
    str1  <- getLine
    let x = read str1 :: Int
    guessloop (x,num)
  |x==num = do
    putStrLn "You got it!"

main :: IO ()
main = do
  num :: Int <- randomRIO (1,100)
  putStrLn "I'm thinking of a number between 1 and 100. Can you guess it?"
  --the guessing loop
  --enter guessed number x
  str1  <- getLine
  let x = read str1 :: Int
  guessloop (x,num)
-- 如果你发现这个事情有困难，请在下方告诉我们
{- Manual #2
  请在此处填写您的解答。
-}
-- End Problem #2
