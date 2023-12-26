module HW15 where

-- How to input the Unicode characters
-- ===================================
-- ℕ    \bN
-- →    \->
-- ∷    \::
-- ≡    \==
-- ⟨    \<
-- ⟩    \>
-- ˘    \u{}

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Bool using (Bool; true; false; _∨_; if_then_else_)
open import Data.List using (List; []; _∷_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; step-≡˘; _∎)

-- Chap. 18

+-assoc : ∀ (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
+-assoc 0 y z = refl
+-assoc (suc x) y z rewrite +-assoc x y z = refl

+0 : ∀ (x : ℕ) → x + 0 ≡ x
+0 0 = refl
+0 (suc x) rewrite +0 x = refl

+-suc : ∀ (x y : ℕ) → x + suc y ≡ suc (x + y)
+-suc 0 y = refl
+-suc (suc x) y rewrite +-suc x y = refl

+-comm : ∀ (x y : ℕ) → x + y ≡ y + x
+-comm 0 y = sym (+0 y)
+-comm (suc x) y rewrite +-comm x y | +-suc y x = refl  

+-swap : ∀ (x y z : ℕ) → x + (y + z) ≡ y + (x + z)
+-swap x y z rewrite sym(+-assoc y x z) | sym(+-assoc x y z) | +-comm x y = refl

*0 : ∀ (x : ℕ) → x * 0 ≡ 0
*0 0 = refl
*0 (suc x) rewrite *0 x = refl

*-suc : ∀ (x y : ℕ) → x * suc y ≡ x + x * y
*-suc 0 y = refl
*-suc (suc x) y rewrite *-suc x y | +-swap y x (x * y) = refl

-- problem 1.1: commutativity of _*_
*-comm : (x y : ℕ) → x * y ≡ y * x
*-comm 0 y rewrite *0 y = refl
*-comm (suc x) y rewrite *-suc y x | *-comm x y = refl

+-samex : ∀ (x y z : ℕ) → y ≡ z → x + y ≡ x + z
+-samex 0 y z p = p 
+-samex (suc x) y z p rewrite +-samex x y z p = refl

*-distri : (x y z : ℕ) → x * (y + z) ≡ x * y + x * z
*-distri 0 y z = refl
*-distri (suc x) y z rewrite *-distri x y z | +-assoc y z (x * y + x * z) | +-assoc y (x * y) (z + x * z) = +-samex y (z + (x * y + x * z)) (x * y + (z + x * z)) (+-swap z (x * y) (x * z))

-- problem 1.2: associativity of _*_
*-assoc : (x y z : ℕ) → (x * y) * z ≡ x * (y * z)
*-assoc 0 y z = refl
*-assoc (suc x) y z rewrite *-assoc x y z | sym(+-assoc y z (x * y + x * z)) | *-comm (y + x * y) z | *-distri z y (x * y) | *-comm z y | *-comm z (x * y) | sym(*-assoc x y z) = refl

-- problem 2: prove the theorems.
-- remark: the standard library provides the following comparison based on decidability
--   _<?_ : (x y : ℕ) → Dec (x < y)
-- where `Dec` is the type for decidability;
-- and also the following comparison as inductive relation
--   _<_ : (x y : ℕ) → Set
-- so neither is the one we want.
-- note: read more on decidability here:
--  * stdlib: https://agda.github.io/agda-stdlib/Relation.Nullary.Decidable.Core.html#1476
--  * PLFA: https://plfa.github.io/Decidable/
-- so we just provide the same definition as given in the slides:
-- (note that stdlib use (Bool; true; false) instead of (𝔹; tt; ff))
infix 9 _≟_
_≟_ : (x y : ℕ) → Bool
zero  ≟ zero  = true
zero  ≟ suc _ = false
suc _ ≟ zero  = false
suc x ≟ suc y = x ≟ y

infix 9 _<_
_<_ : (x y : ℕ) → Bool
zero < zero  = false
zero < suc _ = true
suc _ < zero  = false
suc x < suc y = x < y

-- problem 2.1
n≮n : (n : ℕ) → n < n ≡ false
n≮n 0 = refl 
n≮n (suc n) rewrite n≮n n = refl

-- problem 2.2
<-antisym : (x y : ℕ) → x < y ≡ true → y < x ≡ false
<-antisym 0 0 ()
<-antisym (suc x) 0 ()
<-antisym 0 (suc y) p = refl
<-antisym (suc x) (suc y) p rewrite <-antisym x y p = refl

-- problem 2.3
<-trichotomy : (x y : ℕ) → x < y ∨ x ≟ y ∨ y < x ≡ true
<-trichotomy 0 0 = refl
<-trichotomy (suc x) 0 = refl
<-trichotomy 0 (suc y) = refl
<-trichotomy (suc x) (suc y) rewrite <-trichotomy x y = refl

-- Chap. 19

-- I am feeling lazy today, so let's just introduce the variables here.
-- This is equivalent to adding a `(A : Set)` to every type with a free variable `A`
variable
  A : Set

takeWhile : (p : A → Bool) → List A → List A
takeWhile p [] = []
takeWhile p (x ∷ xs) with p x
... | true = x ∷ takeWhile p xs
... | false = []

-- this function is usually named `replicate` instead of `repeat`
replicate : ℕ → A → List A
replicate 0 _ = []
replicate (suc n) a = a ∷ replicate n a

-- lemmas

takeWhile-tt : ∀ (x : A) (xs : List A) (p : A → Bool) → p x ≡ true → takeWhile p (x ∷ xs) ≡ x ∷ takeWhile p xs
takeWhile-tt x xs p px rewrite px = refl

prop : (a : A) (n : ℕ)
  → (p : A → Bool)
  → p a ≡ true
    -------------------------------------
  → takeWhile p (replicate n a) ≡ replicate n a
prop a 0 p _ = refl
prop a (suc n) p pa rewrite prop a n p pa | takeWhile-tt a (replicate n a) p pa | prop a n p pa = refl
