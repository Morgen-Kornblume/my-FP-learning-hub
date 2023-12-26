module HW16 where

-- README
-- ======
--
-- There are two bonus questions in this template.
-- They are completely optional and won't be graded.
-- Feel free to uncomment or copy the code and fill in your solution.
-- Happy coding and learning Agda!


-- How to input the Unicode characters
-- ===================================
--
-- ℕ    \bN
-- ∷    \::
-- ∙    \.
-- ≡    \==
-- ⟨    \<
-- ⟩    \>
-- ˘    \u{}
-- ≤    \le

open import Data.Nat using (ℕ; zero; suc; _≟_; _+_; _*_; _^_)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Bool using (Bool; true; false)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; step-≡˘; _∎)

-- problem 20.1
_by_matrix : (n m : ℕ) → Set
n by m matrix = Vec (Vec ℕ m) n

-- ==========================
-- example: 2 by 3 matrix = Vec (Vec ℕ 3) 2
-- (6 :: 5 :: 4 :: []) :: (3 :: 2 :: 1 :: [])
-- ==========================

-- problem 20.2
-- 20.2(a) zero matrix: all zeros
-- helper functions
zero-vec : (n : ℕ) → Vec ℕ n
zero-vec 0 = []
zero-vec (suc n) = 0 ∷ zero-vec n
--
zero-matrix : (n m : ℕ) → n by m matrix
zero-matrix 0 m = []
zero-matrix (suc n) m = zero-vec m ∷ zero-matrix n m 

-- 20.2(b) matrix indexing
module Problem-20-2-b where
  open import Data.Bool using (Bool; true; false)

  _<_ : (n m : ℕ) → Bool
  zero  < zero  = false
  zero  < suc _ = true
  suc _ < zero  = false
  suc x < suc y = x < y
-- helper functions
--  <-1same : (x y : ℕ) → (suc x) < (suc y) ≡ true → x < y ≡ true
--  <-1same x y p = p
  vector-elt : {n : ℕ} → Vec ℕ n → (i : ℕ) → i < n ≡ true → ℕ
  vector-elt {(suc n)} (x ∷ xs) 0 p = x
  vector-elt {(suc n)} (x ∷ xs) (suc i) p = vector-elt {n} xs i p
-- 
-- begin from 0,0 end in (n-1,m-1)
  matrix-elt : {n m : ℕ}
    → n by m matrix
    → (i j : ℕ)
    → i < n ≡ true
    → j < m ≡ true
    → ℕ
  matrix-elt {n} {m} (x ∷ xs) 0 j p q = vector-elt x j q
  matrix-elt {(suc n)} {m} (x ∷ xs) (suc i) j p q = matrix-elt {n} {m} xs i j p q

-- Bonus: inductive relations
-- ==========================
--
-- We have already see some downsides of `Bool`-based relations:
-- * `n < m ≡ true` tells us it _is_ true, but not _why_ it is true;
-- * `suc n < suc m ≡ true` is indistinguishable with `n < m ≡ true`;
-- * _<_ is not injective, so Agda's type checker often fails to infer things;
--
-- But we don't need to live with all these! Introducing _inductive relations_:
--
--     data _<_ : ℕ → ℕ → Set where
--       z<s : (n : ℕ) → zero < suc n
--       s<s : {n m : ℕ} → n < m → suc n < suc m
--
-- The inductive relation _<_ is defined as a data type, with these benefits:
-- * values of `n < m` tells us why `n` is less than `m`;
-- * type constructor _<_ is known to be injective, so we have better type inference;
-- * `suc n < suc m` and `n < m` are distinct types;
--
-- Let's see some examples:
--
--     0<1 : 0 < 1
--     0<1 = z<s 0
--
-- We have other ways to define _<_, and here is an example:
--
--     data _<_ : ℕ → ℕ → Set where
--       n<suc[n] : (n : ℕ) → n < suc n
--       n<m⇒n<suc[m] : {n m : ℕ} → n < m → n < suc m
--
-- It is also possible to define _<_ in terms of _≤_:
--
--     data _≤_ (n : ℕ) : ℕ → Set where
--       ≤-refl : n ≤ n
--       ≤-suc : {m : ℕ} → n ≤ m → n ≤ suc m
--
--     _<_ : (n m : ℕ) → Set
--     n < m = suc n ≤ m
--
-- Try the three definitions (and other ones if you wish):
--
--     matrix-elt′ : {n m : ℕ}
--       → n by m matrix
--       → (i j : ℕ)
--       → i < n
--       → j < m
--       → ℕ
--     matrix-elt′ {n} {m} mat i j = ?
--
-- Feel free to uncomment the definition above (or copy it below) and give your solution!
-- Pause and ponder: which definition of _<_ is easier to use in this case? Why?


-- Bonus: bounded natural numbers
-- ==============================
--
-- What? Pass an `i` and prove it is in bound separately? We have better options!
-- Let's define a type for bounded natural numbers [0, n):
--
--     data Fin : ℕ → Set where
--       zero : Fin (suc n)
--       suc : (i : Fin n) → Fin (suc n)
--
-- Values of type `Fin n` is statically known to be smaller than `n`.
-- And guess what? The standard library already have it defined for us, so ...
--
--     open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
--
-- Let's rewrite `matrix-elt` using `Fin`:
--
--     matrix-elt″ : {n m : ℕ}
--       → n by m matrix
--       → (i : Fin n)
--       → (j : Fin m)
--       → ℕ
--     matrix-elt″ {n} {m} mat i j = ?
--
-- Feel free to uncomment the definition above (or copy it below) and give your solution!

-- 20.2(c): diagonal matrix, with the same element along the main diagonal
-- helper functions

_==_ : (n m : ℕ) → Bool
zero == zero = true
zero == suc _ = false
suc _ == zero = false
suc x == suc y = x == y

gen-vec : (n : ℕ) → (d : ℕ) → (pos : ℕ) → Vec ℕ n
gen-vec 0 d pos = []
gen-vec (suc n) d pos with pos == n
... | true = d ∷ gen-vec n d pos
... | false = 0 ∷ gen-vec n d pos

diag-calculation : (n : ℕ) → (m : ℕ) → (d : ℕ) -> m by n matrix
diag-calculation n 0 d = []
diag-calculation n (suc m) d = gen-vec n d m ∷ diag-calculation n m d
-- 
diagonal-matrix : (n : ℕ) → (d : ℕ) → n by n matrix
diagonal-matrix n d = diag-calculation n n d


identity-matrix : (n : ℕ) → n by n matrix
identity-matrix n = diagonal-matrix n 1

-- 20.2(d): transpose
-- helper functions
module Problem-20-2-d where
  open import Data.Bool using (Bool; true; false)

  _<_ : (n m : ℕ) → Bool
  zero  < zero  = false
  zero  < suc _ = true
  suc _ < zero  = false
  suc x < suc y = x < y
-- helper functions
--  <-1same : (x y : ℕ) → (suc x) < (suc y) ≡ true → x < y ≡ true
--  <-1same x y p = p
  vector-elt : {n : ℕ} → Vec ℕ n → (i : ℕ) → i < n ≡ true → ℕ
  vector-elt {(suc n)} (x ∷ xs) 0 p = x
  vector-elt {(suc n)} (x ∷ xs) (suc i) p = vector-elt {n} xs i p
-- 
-- begin from 0,0 end in (n-1,m-1)
  matrix-elt : {n m : ℕ}
    → n by m matrix
    → (i j : ℕ)
    → i < n ≡ true
    → j < m ≡ true
    → ℕ
  matrix-elt {n} {m} (x ∷ xs) 0 j p q = vector-elt x j q
  matrix-elt {(suc n)} {m} (x ∷ xs) (suc i) j p q = matrix-elt {n} {m} xs i j p q

  zipWith : ∀ {♭ ♭' ♭''} {A : Set ♭} {B : Set ♭'} {C : Set ♭''}{n : ℕ} → (A → B → C) → Vec A n → Vec B n → Vec C n
  zipWith f [] [] = []
  zipWith f (x ∷ xs) (y ∷ ys) = (f x y) ∷ (zipWith f xs ys)

  repeat-vec : ∀ {♭} {A : Set ♭} → (x : A) → (n : ℕ) → Vec A n
  repeat-vec x 0 = []
  repeat-vec x (suc n) = x ∷ (repeat-vec x n) 

  transpose : {n m : ℕ} → n by m matrix → m by n matrix
  transpose {n} {m} [] = repeat-vec [] m
  transpose (x ∷ xs) = zipWith (λ x y → x ∷ y) x (transpose xs)

  test : 2 by 3 matrix
  test = (1 ∷ 2 ∷ 3 ∷ []) ∷ (4 ∷ 5 ∷ 6 ∷ []) ∷ []

  test2 : 3 by 2 matrix
  test2 = (1 ∷ 4 ∷ []) ∷ (2 ∷ 5 ∷ []) ∷ (3 ∷ 6 ∷ []) ∷ []

  testprop : transpose test ≡ test2
  testprop = refl

  testprop2 : matrix-elt test 1 2 refl refl ≡ matrix-elt (transpose test) 2 1 refl refl
  testprop2 = refl

-- 20.2(e): dot product
_∙_ : {n : ℕ} → (x y : Vec ℕ n) → ℕ
(x ∷ xs) ∙ (y ∷ ys) = x * y + (xs ∙ ys)
[] ∙ [] = 0
