{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
module HW7 where

-- Ch.08

-- Problem #1: multiplies for natural numbers
data Nat = Zero | Succ Nat
  deriving (Show)

add :: Nat -> Nat -> Nat
add Zero     n = n
add (Succ m) n = Succ (add m n)

int_to_Nat :: Int -> Nat
int_to_Nat 0 = Zero
int_to_Nat x = Succ (int_to_Nat (x-1))

nat_to_Int :: Nat -> Int
nat_to_Int Zero = 0
nat_to_Int (Succ x) = nat_to_Int x + 1

multiplies :: Nat -> Nat -> Nat
multiplies Zero n = Zero
multiplies n Zero = Zero
multiplies (Succ m) n = add (multiplies m n) n
-- End Problem #1

-- Problem #2: folde for Exprs
data Expr
  = Val Int
  | Add Expr Expr
  | Mul Expr Expr
  deriving (Show)

-- try to figure out the suitable type yourself
--folde :: _
--folde = _
-- End Problem #2

-- Problem #3: recursive tree type
--data Tree a = _
-- End Problem #3

-- Ch.09

-- 为简便起见，我们不允许任何中间结果超出 2^32。
-- 这意味着可以提前对搜索进行剪枝：
-- 1. 任何结果均不允许超过 2^32。
-- 2. 任何指数均不允许超过 32。
-- 在大家的 64 位系统上，GHC 一般把 Int 实现为 64 位整数，因此
-- 只要严格执行上述剪枝策略，就不必担心运算溢出问题。
{-
data Op
  = Add
  | Sub
  | Mul
  | Div
  -- 提示：添加指数运算
  deriving Eq

data Expr
  = Val Int
  | App Op Expr Expr
  deriving Eq

-- 你需要完成下面的 solutions 函数

solutions :: [Int] -> Int -> [Expr]
solutions = _

-- 下面是我们为 Expr 和 Op 提供的一个 Show 的实现
-- 这并不是本次作业必需的，但是在调试过程中可能会让表达式更易读
-- 这个实现使用了 showsPrec，有关它的细节你可以参考相关文档：
-- https://hackage.haskell.org/package/base-4.15.0.0/docs/Text-Show.html#t:Show
-- 以及 Haskell 2010 Report 的 11.4 节：
-- https://www.haskell.org/onlinereport/haskell2010/haskellch11.html

instance Show Op where
  show Add = "+"
  show Sub = "-"
  show Mul = "*"
  show Div = "/"
  -- 提示：指数运算可以显示为 x ^ y

instance Show Expr where
  showsPrec _ (Val n) = shows n
  showsPrec p (App op x y)
    = showParen (p > q)
    $ showsPrec q x . showChar ' ' . shows op
    . showChar ' ' . showsPrec (succ q) y
    where q = case op of
            Add -> 6; Sub -> 6
            Mul -> 7; Div -> 7
            -- 提示：给出指数运算的优先级
            -- 可以参考Haskell定义的优先级（:info ^）
-}