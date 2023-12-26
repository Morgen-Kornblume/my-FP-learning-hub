module list where

open import natural
open import Data.Bool 
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning using (begin_; step-≡; step-≡˘; _≡⟨⟩_; _∎)

data List {l} (A : Set l) : Set l where
    []  : List A
    _::_ : (x : A) -> (xs : List A) -> List A

[_] : ∀{l} {A : Set l} -> A -> List A
[ x ] = x :: []

is_empty : ∀{l} {A : Set l} -> List A -> Bool
is_empty [] = true
is_empty _  = false

head : ∀{l} {A : Set l} -> (x : List A) -> (is_empty x ≡ false) -> A
head [] ()
head (x :: xs) _ = x

length : ∀{l} {A : Set l} -> List A -> ℕ
length [] = zero
length (x :: xs) = suc (length xs)

_++_ : ∀{l} {A : Set l} -> List A -> List A -> List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

map : ∀{l} {A B : Set l} -> (A -> B) -> List A -> List B
map f [] = []
map f (x :: xs) = f x :: map f xs

filter : ∀{l} {A : Set l} -> (A -> Bool) -> List A -> List A
filter p [] = []
filter p (x :: xs) with p x
... | true = x :: filter p xs
... | false = filter p xs

foldr : ∀{l} {A B : Set l} -> (A -> B -> B) -> B -> List A -> B
foldr f z [] = z
foldr f z (x :: xs) = f x (foldr f z xs)

length-++ : ∀{l} {A : Set l} -> (xs ys : List A) -> length (xs ++ ys) ≡ (length xs) + (length ys)
length-++ [] ys = refl
length-++ (x :: xs) ys rewrite length-++ xs ys = refl

map-++ : ∀{l} {A B : Set l} -> (f : A -> B) -> (xs ys : List A) -> map f (xs ++ ys) ≡ (map f xs) ++ (map f ys)
map-++ f [] ys = refl
map-++ f (x :: xs) ys rewrite map-++ f xs ys = refl

postulate 
    ≤ℕ-trans : ∀ {x y z : ℕ} -> x ≤ℕ y ≡ true -> y ≤ℕ z ≡ true -> x ≤ℕ z ≡ true
    ≤ℕ-suc : ∀ (x : ℕ) -> x ≤ℕ suc x ≡ true

length-filter : ∀{l} {A : Set l} -> (p : A -> Bool) -> (xs : List A) -> length (filter p xs) ≤ℕ length xs ≡ true
length-filter p [] = refl
length-filter p (x :: xs) with p x
... | true = length-filter p xs
... | false = ≤ℕ-trans {length (filter p xs)} (length-filter p xs) (≤ℕ-suc (length xs))

-- filter-idem : ∀{l} {A : Set l} -> (p : A -> Bool) -> (xs : List A) -> filter p (filter p xs) ≡ filter p xs
-- filter-idem p [] = refl
-- filter-idem p (x :: xs) with keep (p x)
-- ... | true , p' rewrite p' | p' filter-idem p xs = refl
-- ... | false , p' rewrite p' = filter-idem p xs

variable
  A : Set

takeWhile : (p : A → Bool) → List A → List A
takeWhile p [] = []
takeWhile p (x :: xs) with p x
... | true = x :: takeWhile p xs
... | false = []

replicate : ℕ → A → List A
replicate zero _ = []
replicate (suc n) a = a :: replicate n a

takeWhile-tt : ∀ (x : A) (xs : List A) (p : A → Bool) → p x ≡ true → takeWhile p (x :: xs) ≡ x :: takeWhile p xs
takeWhile-tt x xs p px rewrite px = refl

prop : (a : A) (n : ℕ)
  → (p : A → Bool)
  → p a ≡ true
    -------------------------------------
  → takeWhile p (replicate n a) ≡ replicate n a
prop a zero p _ = refl
prop a (suc n) p pa rewrite prop a n p pa | takeWhile-tt a (replicate n a) p pa | prop a n p pa = refl
