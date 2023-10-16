module HW4 where

-- **=========[ Ch.03 ]=========**

-- Problem #1: What are the types of the following values?
val1 :: [Char]
val1 = ['a', 'b', 'c']

val2 :: (Char, Char, Char)
val2 = ('a', 'b', 'c')

val3 :: [(Bool, Char)]
val3 = [(False, '0'), (True, '1')]

val4 :: ([Bool], [Char])
val4 = ([False, True], ['0', '1'])

val5 :: [[a] -> [a]]
val5 = [tail, init, reverse]
-- End Problem #1

-- Problem #2: What are the types of the following functions?
second :: [a] -> a
second xs = head (tail xs)

swap :: (a, b) -> (b, a)
swap (x, y) = (y, x)

pair :: a -> b -> (a, b)
pair x y = (x, y)

double :: Num x => x -> x
double x = x * 2

palindrome :: Eq a => [a] -> Bool
palindrome xs = reverse xs == xs

twice :: (x -> x) -> x -> x
twice f x = f (f x)
-- End Problem #2

-- Problem #3: Int/Integer，show/read
--   阅读教科书，用例子（在ghci上运行）
-- Part #3.1: 展示Int/Integer的区别
{- Manual #3.1

    请把你的答案填写在这里（可以考虑直接复制命令行窗口的内容）
  示例：
    Int和Integer的区别是:
    Int的范围是-2^63 ~ 2^63-1，Integer的范围是理论无限的（只要你的内存和CPU够用）
    以下我用一个显然的例子来展示这个区别：
    可见Int类型在值越界后会变为负数最小值，而Integer则不会。
    Int的性质在此处和C++中的long long相同，而Integer则和C++中的BigInteger相同。
    =========test.hs=========
    int :: Int
    int = 2^63
    integer :: Integer
    integer = 2^63

    main :: IO ()
    main = do
    print int
    print integer
    =======result on ghci=======
    ghci> :load test.hs
    Ok, one module loaded.
    ghci> main
    -9223372036854775808
    9223372036854775808
-}
-- End Part #3.1

-- Part #3.2: show/read的用法
{- Manual #3.2

    请把你的答案填写在这里（可以考虑直接复制命令行窗口的内容）
  show 函数接受一个值作为参数，并返回该值的字符串表示。
  例如：
    Prelude>show 123
    "123"
    Prelude>show True
    "True"
    Prelude>show [1,2,3]
    "[1,2,3]"
  read 函数则接受一个字符串作为参数，并尝试将其转换为对应的值。
  例如：
    Prelude>read "123"::Int
    123
    Prelude>read "True"::Bool
    True
    Prelude>read "[1,2,3]"::[Int]
    [1,2,3]
-}
-- End Part #3.2
-- End Problem #3

-- Problem #4: Integral/Fractional
--   阅读教科书以及Prelude模块的相关文档，理解 Integral 和 Fractional
-- 两个 Type Class 中定义的函数和运算符，用例子（在 GHCi 上运行）展示每
-- 一个函数/运算符的用法。

-- Part #4.1: Integral
{- Manual #4.1

    请把你的答案填写在这里（可以考虑直接复制命令行窗口的内容）
  示例：
    Prelude>quot 1919810 114514
    16
    Prelude>rem 1919810 114514
    87586
    Prelude>div (-1919810) 114514
    -17
    Prelude>mod (-1919810) 114514
    26928
    Prelude>quotRem 1919810 114514
    (16,87586)
    Prelude>divMod (-1919810) 114514
    (-17,26928)
    Prelude>:{          
    ghci| int :: Int
    ghci| int=114514
    ghci| integer :: Integer
    ghci| integer = toInteger int
    ghci| :}
-}
-- End Part #4.1

-- Part #4.2: Fractional
{- Manual #4.2

    请把你的答案填写在这里（可以考虑直接复制命令行窗口的内容）
  示例：
    Prelude>1919810 / 114514
    16.764849712698883
    Prelude>recip (1919810/114514)
    5.964861106046953e-2
    Prelude>import Data.Ratio
    Prelude>fromRational (1 % 3) :: Double
    0.3333333333333333
-}
-- End Part #4.2
-- End Problem #4

-- **=========[ Ch.04 ]=========**

-- Problem #5: define safetail
-- Part #5.1: use a conditional expression
safetail1 :: [a] -> [a]
safetail1 xs = if null xs then [] else tail xs
-- End Part #5.1

-- Part #5.2: use guarded equations
safetail2 :: [a] -> [a]
safetail2 xs 
  | null xs = []
  | otherwise = tail xs 
-- End Part #5.2

-- Part #5.3: use pattern matching
safetail3 :: [a] -> [a]
safetail3 [] = []
safetail3 (_:xs) = xs
-- End Part #5.3
-- End Problem #5

evenadd :: Int -> Int
evenadd n = if n*2>9 then n*2-9 else n*2

-- Problem #6: Luhn algorithm
luhn :: Int -> Int -> Int -> Int -> Bool
luhn a b c d = ((evenadd a + evenadd c + b + d) `mod` 10) == 0
-- End Problem #6
