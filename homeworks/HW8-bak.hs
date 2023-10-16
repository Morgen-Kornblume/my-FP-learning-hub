module HW8 where
import Numeric.Natural (Natural)

-- Ch.09

-- 为简便起见，我们不允许任何中间结果超出 2^32。
-- 这意味着可以提前对搜索进行剪枝：
-- 1. 任何结果均不允许超过 2^32。
-- 2. 任何指数均不允许超过 32。
-- 在大家的 64 位系统上，GHC 一般把 Nat 实现为 64 位整数，因此
-- 只要严格执行上述剪枝策略，就不必担心运算溢出问题。
type Nat=Natural

data Op
  = Add
  | Sub
  | Mul
  | Div
  | Exp
  -- 提示：添加指数运算
  deriving Eq

data Expr
  = Val Nat
  | App Op Expr Expr
  deriving Eq

-- 你需要完成下面的 solutions 函数

lim :: Nat
lim = 2^32

apply :: Op -> Nat -> Nat -> Nat
apply Add x y = x + y
apply Sub x y = x - y
apply Mul x y = x * y
apply Div x y = x `div` y
apply Exp x y = x ^ y

nexp :: Nat -> Nat -> Bool
nexp x y
  | y>31 = False
  | toInteger x^toInteger y>toInteger lim = False
  | otherwise = True

valid :: Op -> Nat -> Nat -> Bool
valid Add x y = x<y && x+y <lim
valid Sub x y = x > y
valid Mul x y = x<y && x/=1 && y/=1 && x*y <= lim
valid Div x y = y/=0 && x `mod` y == 0 && y/=1 
valid Exp x y = x/=1 && x/=0 && y/=1 && y<32 && nexp x y

eval :: Expr -> [Nat]
eval (Val n) = [n | n>0]
eval (App op x y) = [apply op a b | a <- eval x, b <- eval y, valid op a b]

subs :: [a] -> [[a]]
subs []= [[]]
subs (x:xs) = yss ++ map (x:) yss where yss=subs xs

interleave :: a -> [a] -> [[a]]
interleave x [] = [[x]]
interleave x (y:ys) = (x:y:ys):map (y:) (interleave x ys)

perms :: [a] -> [[a]]
perms = foldr (concatMap . interleave) [[]]

choices :: [a] -> [[a]]
choices = concatMap perms . subs

values :: Expr -> [Nat]
values (Val n) = [n]

solution :: Expr -> [Nat] -> Nat -> Bool
solution e ns n = elem (values e) (choices ns) && eval e == [n]

split :: [a] -> [([a],[a])]
split [] = []
split [_] = []
split (x:xs) = ([x],xs):[(x:ls,rs) | (ls,rs) <- split xs]

exprs :: [Nat] -> [Expr]
exprs [] = []
exprs [n] = [Val n]
exprs ns = [e | (ls,rs) <- split ns, l <- exprs ls, r <- exprs rs, e <- combine l r]

combine :: Expr -> Expr -> [Expr]
combine l r = [App op l r | op <- [Add,Sub,Mul,Div,Exp]]

solutions' :: [Nat] -> Nat -> [Expr]
solutions ns n = [e | ns' <- choices ns, e <- exprs ns', eval e == [n]]

type Result = (Expr, Nat)

results :: [Nat] -> [Result]
results [] = []
results [n] = [(Val n, n) | n > 0]
results ns = [res | (ls,rs) <- split ns, lx <- results ls, ry <- results rs, res <- combine' lx ry]

combine' :: Result -> Result -> [Result]
combine' (l,x) (r,y) = [(App op l r, apply op x y) | op <- [Add,Sub,Mul,Div], valid op x y]

solutions :: [Nat] -> Nat -> [Expr]
solutions' ns n = [e | ns' <- choices ns, (e,m) <- results ns', m == n]

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
  show Exp = "^"
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
            Exp -> 8
            -- 提示：给出指数运算的优先级
            -- 可以参考Haskell定义的优先级（:info ^）
