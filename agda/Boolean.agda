
module Boolean where

infix 80 ~_
infixl 40 _&&_
infixl 20 _||_
infixl 30 _xor_
infixl 30 _nor_
infix  4 _≡_
infixl 1 if_then_else_

data 𝔹 : Set where
    tt : 𝔹
    ff : 𝔹
-- not operation
~_ : 𝔹 → 𝔹
~ tt = ff
~ ff = tt

-- and operation
_&&_ : 𝔹 → 𝔹 → 𝔹
tt && b = b
ff && b = ff

-- or operation
_||_ : 𝔹 → 𝔹 → 𝔹
tt || b = tt
ff || b = b

-- xor operation
_xor_ : 𝔹 → 𝔹 → 𝔹
tt xor b = ~ b
ff xor b = b

-- nor operation
_nor_ : 𝔹 → 𝔹 → 𝔹
a nor b = ~ (a || b)

if_then_else_ : ∀ {ℓ} {A : Set ℓ} → 𝔹 → A → A → A
if tt then a else b = a
if ff then a else b = b

data _≡_ {ℓ} {A : Set ℓ} (x : A) : A → Set ℓ where
    refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

~~tt : ~ ~ tt ≡ tt
~~tt = refl

~~ff : ~ ~ ff ≡ ff
~~ff = refl

~~-elim : ∀ (b : 𝔹) → ~ ~ b ≡ b
~~-elim tt = ~~tt
~~-elim ff = ~~ff

&&-idem : ∀ {b} → b && b ≡ b
&&-idem{tt} = refl
&&-idem{ff} = refl

||≡ff₂ : ∀ {b1 b2} → b1 || b2 ≡ ff → b2 ≡ ff
||≡ff₂{tt} ()
||≡ff₂{ff}{tt} ()
||≡ff₂{ff}{ff} p = refl

||≡ff₁ : ∀ {b1 b2} → b1 || b2 ≡ ff → b1 ≡ ff
||≡ff₁{tt} ()
||≡ff₁{ff}{tt} ()
||≡ff₁{ff}{ff} p = refl

||-cong₁ : ∀ {b1 b2 b1′} → b1 ≡ b1′ → b1 || b2 ≡ b1′ || b2
||-cong₁ refl = refl

||-cong₂ : ∀ {b1 b2 b2′} → b2 ≡ b2′ → b1 || b2 ≡ b1 || b2′
||-cong₂ p rewrite p = refl

𝔹-contra : ff ≡ tt → ∀{ℓ} {P : Set ℓ} → P
𝔹-contra ()

