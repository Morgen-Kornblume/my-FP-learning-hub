{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
module HW7 where
import GHC.CmmToAsm.AArch64.Instr (x0)

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
folde :: (Int -> a) -> (a->a->a) -> (a->a->a) -> Expr -> a
folde f opadd opmul (Val x) = f x
folde f opadd opmul (Add x y) = opadd (folde f opadd opmul x) (folde f opadd opmul y)
folde f opadd opmul (Mul x y) = opmul (folde f opadd opmul x) (folde f opadd opmul y)
  

size :: Expr -> Int
size = folde (const 1) (+) (+)

eval :: Expr -> Int
eval = folde id (+) (*)
-- End Problem #2

-- Problem #3: recursive tree type
data Tree a = Leaf a | Node (Tree a) (Tree a)
-- End Problem #3
