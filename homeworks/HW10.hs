module HW10 where

import           Prelude hiding (Applicative (..), Functor (..), Monad (..))

infixl 4 <$
infixl 1 >>, >>=
infixl 4 <*>

class Functor f where
  fmap        :: (a -> b) -> f a -> f b
  (<$)        :: a -> f b -> f a
  (<$)        =  fmap . const

class Functor f => Applicative f where
  pure :: a -> f a
  (<*>) :: f (a -> b) -> f a -> f b

class Applicative m => Monad m where
  return :: a -> m a
  return = pure
  (>>=) :: m a -> (a -> m b) -> m b
  (>>) :: m a -> m b -> m b
  m >> k = m >>= \_ -> k

-- Problem #1: Monad ((->) a)
instance Functor ((->) a) where
  fmap :: (a2 -> b) -> (a1 -> a2) -> a1 -> b
  fmap = (.)

instance Applicative ((->) a) where
  pure :: a2 -> a1 -> a2
  pure = const
  (<*>) :: (a1 -> a2 -> b) -> (a1 -> a2) -> a1 -> b
  (<*>) f g x = f x (g x)

instance Monad ((->) r) where
  (>>=) :: (r -> a) -> (a -> r -> b) -> r -> b
  (>>=) m k x = k (m x) x
-- End Problem #1

-- Problem #2: Functor, Applicative, Monad
data Expr a
  = Var a
  | Val Int
  | Add (Expr a) (Expr a)
  deriving (Show)

instance Functor Expr where
  fmap :: (a -> b) -> Expr a -> Expr b
  fmap f (Var x) = Var (f x)
  fmap _ (Val x) = Val x
  fmap f (Add x y) = Add (fmap f x) (fmap f y)

instance Applicative Expr where
  pure :: a -> Expr a
  pure = Var
  (<*>) :: Expr (a -> b) -> Expr a -> Expr b
  (<*>) (Var f) (Var x) = Var (f x)
  (<*>) (Var f) (Val x) = Val x
  (<*>) (Var f) (Add x y) = Add (fmap f x) (fmap f y)

instance Monad Expr where
  (>>=) :: Expr a -> (a -> Expr b) -> Expr b
  (>>=) m k = case m of
    Var x -> k x
    Val x -> Val x
    Add x y -> Add (x >>= k) (y >>= k)


-- Write your example here:

-- 定义一个从类型 Int 到 Expr Int 的函数
f :: Int -> Expr Int
f x = Add (Val x) (Var 3)

-- 定义一个从类型 Int 到 Expr String 的函数
g :: Int -> Expr String
g x = Var "z"

-- 定义一个 Expr Int 类型的值
expr :: Expr Int
expr = Add (Val 1) (Add (Var 2) (Var 3))

-- 使用 >>= 将 f 和 g 组合成一个新的函数
h :: Expr String
h = expr >>= f >>= g

-- And explain what the >>= operator for this type does
{- Manual #2
    ghci> expr
    Add (Val 1) (Add (Var 2) (Var 3))
    ghci> expr>>=f
    Add (Val 1) (Add (Add (Val 2) (Var 3)) (Add (Val 3) (Var 3)))
    ghci> expr>>=f>>=g
    Add (Val 1) (Add (Add (Val 2) (Var "z")) (Add (Val 3) (Var "z")))
    在这个示例中，>>= 的作用是将后面的函数按照从前到后的顺序组合起来，
    然后将组合后的函数作用于前面的表达式，可以修改其中变量的值和类型，
    而不会改变表达式的结构。
-}
-- End Problem #2
