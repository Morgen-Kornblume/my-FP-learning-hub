module HW12 where

import           Prelude hiding (Maybe (..))

-- Problem #1: Maybe, Foldable and Traversable
data Maybe a = Nothing | Just a
  deriving (Show, Eq, Ord)

instance Functor Maybe where
  fmap :: (a -> b) -> Maybe a -> Maybe b
  fmap _ Nothing = Nothing
  fmap f (Just x) = Just $ f x

instance Semigroup a => Semigroup (Maybe a) where
  (<>) :: Maybe a -> Maybe a -> Maybe a
  a <> Nothing = a
  Nothing <> b = b
  (Just a ) <> (Just b ) = Just (a <> b)

instance Semigroup a => Monoid (Maybe a) where
  mempty :: Maybe a
  mempty = Nothing


instance Foldable Maybe where
  foldMap :: Monoid m => (a -> m) -> Maybe a -> m
  foldMap _ Nothing = mempty
  foldMap f (Just x) = f x
  foldl :: (b -> a -> b) -> b -> Maybe a -> b
  foldl f b Nothing = b
  foldl f b (Just x) = f b x
  foldr :: (a -> b -> b) -> b -> Maybe a -> b
  foldr f b Nothing = b
  foldr f b (Just x) = f x b

foldMaybe :: Monoid a => Maybe a -> a
foldMaybe Nothing = mempty
foldMaybe (Just x) = x

instance Traversable Maybe where
  traverse :: Applicative f => (a -> f b) -> Maybe a -> f (Maybe b)
  traverse _ Nothing = pure Nothing
  traverse g (Just x) = Just <$> g x
-- End Problem #1

-- Problem #2: Tree, Foldable and Traversable
data Tree a = Leaf | Node (Tree a) a (Tree a)
  deriving Show

instance Functor Tree where
  fmap :: (a -> b) -> Tree a -> Tree b
  fmap _ Leaf = Leaf
  fmap f (Node l x r) = Node (fmap f l) (f x) (fmap f r)

instance Foldable Tree where
  foldMap :: Monoid m => (a -> m) -> Tree a -> m
  foldMap _ Leaf = mempty
  foldMap f (Node l x r) = foldMap f l <> f x <> foldMap f r
  foldl :: (b -> a -> b) -> b -> Tree a -> b
  foldl _ b Leaf = b
  foldl f b (Node l x r) = foldl f (f (foldl f b l) x) r
  foldr :: (a -> b -> b) -> b -> Tree a -> b
  foldr _ b Leaf = b
  foldr f b (Node l x r) = foldr f (f x (foldr f b r)) l

-- 先序和后序遍历

foldTree :: Monoid a => Tree a -> a
foldTree Leaf = mempty
foldTree (Node l x r) = foldTree l <> x <> foldTree r

instance Traversable Tree where
  traverse :: Applicative f => (a -> f b) -> Tree a -> f (Tree b)
  traverse _ Leaf = pure Leaf
  traverse g (Node l x r) = Node <$> traverse g l <*> g x <*> traverse g r
-- End Problem #2

-- Problem #3: fibonacci using zip/tail/list-comprehension
fibs :: [Integer]
fibs = 0 : 1 : zipWith (+) fibs (tail fibs)
-- End Problem #3

-- Problem #4: Newton's square root
sqroot :: Double -> Double
sqroot x = head (dropWhile notGoodEnough (iterate improve 1.0))
  where
    improve guess = (guess + x / guess) / 2
    notGoodEnough guess = abs (guess * guess - x) > 0.000001
-- End Problem #4
