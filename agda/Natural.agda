

module Natural where

infixl 10 _+_
infixl 20 _*_
infix 4 _≡_
infix 1 if_then_else_

data 𝔹 : Set where
    tt : 𝔹
    ff : 𝔹

data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ

data _≡_ {ℓ} {A : Set ℓ} (x : A) : A → Set ℓ where
    refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

if_then_else_ : ∀ {ℓ} {A : Set ℓ} → 𝔹 → A → A → A
if tt then a else b = a
if ff then a else b = b

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

_*_ : ℕ → ℕ → ℕ
zero * _ = zero
suc m * n = n + (m * n)

pred : ℕ → ℕ
pred zero = zero
pred (suc n) = n

0+ : ∀ (n : ℕ) → zero + n ≡ n
0+ x = refl

+0 : ∀ (n : ℕ) → n + zero ≡ n
+0 zero = refl
+0 (suc x) rewrite +0 x = refl

+assoc : ∀ (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
+assoc zero y z = refl
+assoc (suc x) y z rewrite +assoc x y z = refl