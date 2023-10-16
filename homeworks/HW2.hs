
-- Problem #1: 写出 and 函数的三种其他的定义
and1 :: Bool -> Bool -> Bool
and1 x y = if (x==True&&y==True) then True else False

and2 :: Bool -> Bool -> Bool
and2 x y | x && y =True
         | otherwise =False

bit :: Bool -> Int
bit x = if x then 1 else 0

and3 :: Bool -> Bool -> Bool
and3 x y = bit x + bit y > 1

-- End Problem #1 

-- Problem #2: 给出函数 div 的一种或多种定义




divabs :: Integer -> Integer -> Integer
divabs x y = if x-y >= 0
  then div (x-y) y + 1
  else 0

divr :: Integer -> Integer -> Integer
divr x y
  | x-y>0 = divr (x-y) y
  | x-y==0 = 0
  | otherwise = 1

div1 :: Integer -> Integer -> Integer
div1 x 0 = undefined
div1 x y
  | x*y>0 = divabs (abs x) (abs y) 
  | x*y<0 = -divabs (abs x) (abs y) - divr (abs x) (abs y)
  | x*y==0 =0



-- 如果你认为这个问题无解或者很难，请给出必要的说明。
-- （请用 undefined 代替上面的下划线，并在下面的括号中填写，不要修改第一行）
{- Manual #2
  请在此处填写您的解答。
-}
