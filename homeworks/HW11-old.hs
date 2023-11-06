{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use lambda-case" #-}
module HW11 where

import           Prelude hiding (Maybe (..))
import Data.Char

-- Problem #1: Extend the expression parser
newtype Parser a = P (String -> [(a,String)])

parse :: Parser a -> String -> [(a,String)]
parse (P f) = f

item :: Parser Char
item = P (\program -> case program of
                        [] -> []
                        (x:xs) -> [(x,xs)])

instance Functor Parser where
    fmap :: (a -> b) -> Parser a -> Parser b
    fmap g p = P $ \program -> case parse p program of
                                [] -> []
                                [(v,remain)]->[(g v,remain)]

instance Applicative Parser where
    pure :: a -> Parser a
    pure v = P $ \program -> [(v,program)]
    (<*>) :: Parser (a -> b) -> Parser a -> Parser b
    pg <*> px = P $ \program -> case parse pg program of
                                [] -> []
                                [(g,remain)] -> parse (g <$> px) remain

instance Monad Parser where
    (>>=) :: Parser a -> (a -> Parser b) -> Parser b
    p >>= f = P $ \program -> case parse p program of
                                [] -> []
                                [(v,remain)] -> parse (f v) remain

up1 :: Parser Char
up1 = do
    x <- item
    let y = toUpper x
    return y

class Applicative f => Alternative f where
    (<|>) :: f a -> f a -> f a
    empty :: f a

    many :: f a -> f [a]
    many v = some v <|> pure []

    some :: f a -> f [a]
    some v = (:) <$> v <*> many v

data Maybe a = Just a | Nothing deriving(Show)

instance Functor Maybe where
    fmap :: (a -> b) -> Maybe a -> Maybe b
    fmap _ Nothing = Nothing
    fmap f (Just x) = Just $ f x

instance Applicative Maybe where
    pure :: a -> Maybe a
    pure = Just
    (<*>) :: Maybe(a -> b) -> Maybe a -> Maybe b
    Nothing <*> _ = Nothing
    (Just g) <*> x = g <$> x

instance Monad Maybe where
    (>>=) :: Maybe a -> (a -> Maybe b) -> Maybe b
    Nothing >>= x = Nothing
    (Just x) >>= f = f x

instance Alternative Maybe where
    empty :: Maybe a
    empty = Nothing

    (<|>) :: Maybe a -> Maybe a -> Maybe a
    Nothing <|> r = r
    l <|> _ = l

instance Alternative Parser where
    empty :: Parser a
    empty = P $ const []

    (<|>) :: Parser a -> Parser a -> Parser a
    p <|> q = P $ \program -> case parse p program of
                                [] -> parse q program
                                sth -> sth

sat :: (Char -> Bool) -> Parser Char
sat p = do 
        x <- item
        if p x then return x else empty

char :: Char -> Parser Char
char x = sat (x==)

string :: String -> Parser String
string [] = return []
string (x:xs) = do 
                char x
                string xs
                return (x:xs)

digit :: Parser Char
digit = sat isDigit

nat :: Parser Int
nat = do xs <- some digit
         return (read xs)

int :: Parser Int
int = do char '-'
         n <- nat
         return $ -n
       <|> nat

space :: Parser ()
space = do 
        many (sat isSpace)
        return ()


token :: Parser a -> Parser a
token p = do 
            space
            v <- p
            space
            return v

integer :: Parser Int
integer = token int            

natural :: Parser Int
natural = token nat

symbol :: String -> Parser String
symbol x = token $ string x

eval :: String -> Int
eval = fst . head . parse expr

expr :: Parser Int
expr = do t <- term
          do    symbol "+"
                e <- expr
                return (t+e)
           <|>  return t
-- End Problem #1

term :: Parser Int
term = do f <- factor
          do    symbol "*"
                t <- term
                return (f*t)
           <|>  return f

factor :: Parser Int
factor = do    symbol "("
               e <- expr
               symbol ")"
               return e
          <|>  natural