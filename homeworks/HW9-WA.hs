{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
module HW9 where
import GHC.Driver.Session (tmpDir)

get_and_sum :: Int -> IO() -> Int
get_and_sum x = do
    tmp <- getLine
    let a = read tmp
    if x > 1 then return a + get_and_sum (x-1) else return a


adder :: IO ()
adder = do 
    putStr "How many numbers? "
    n <- getLine
    let sum = get_and_sum $ read n
    PutStr "The total is " ++ show sum
