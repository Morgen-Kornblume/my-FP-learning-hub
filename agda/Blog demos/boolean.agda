module boolean where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

data 𝔹 : Set where
  true : 𝔹
  false : 𝔹

-- 优先级 30
infixl 30 ~_ -- not

-- 优先级 20
infixr 20 _⊗_ -- nor

-- 优先级 15
infixl 15 _⊕_ -- xor

-- 优先级 10
infixr 10 _||_ -- or

-- 优先级 5
infixr 5 _&&_ -- and

-- not
~_ : 𝔹 → 𝔹
~ true = false
~ false = true

-- and
_&&_ : 𝔹 → 𝔹 → 𝔹
true && true = true
_ && _ = false

-- or
_||_ : 𝔹 → 𝔹 → 𝔹
false || false = false
_ || _ = true

infixr 1 if_then_else_ -- if_then_else
if_then_else_ : ∀ {l}  {A : Set l} → 𝔹 → A → A → A
if true then x else y = x
if false then x else y = y

-- xor 
_⊕_ : 𝔹 → 𝔹 → 𝔹
x ⊕ y = if x then ~ y else y

-- nor
_⊗_ : 𝔹 → 𝔹 → 𝔹
x ⊗ y = ~ (x || y)

||≡ff₂ : ∀ {b1 b2} → b1 || b2 ≡ false → b2 ≡ false
||≡ff₂ {true} ()
||≡ff₂ {false}{true} ()
||≡ff₂ {false}{false} p = refl

||≡ff₁ : ∀ {b1 b2} → b1 || b2 ≡ false → b1 ≡ false
||≡ff₁ {true} ()
||≡ff₁ {false}{true} ()
||≡ff₁ {false}{false} p = refl

||-cong₁ : ∀ {b1 b1' b2} → b1 ≡ b1' → b1 || b2 ≡ b1' || b2
||-cong₁ refl = refl

||-cong₂ : ∀ {b1 b2 b2'} → b2 ≡ b2' → b1 || b2 ≡ b1 || b2'
||-cong₂ p rewrite p = refl

ite-same : ∀ {b} {A : Set} (x : A) → if b then x else x ≡ x
ite-same {true} x = refl
ite-same {false} x = refl

𝔹-contra : true ≡ false → ∀{l} {P : Set l} → P 
𝔹-contra ()

ite-arg : {A : Set} {B : Set} → (f : A → B) (b : 𝔹) (x y : A) → (f (if b then x else y)) ≡ (if b then f x else f y)
ite-arg f true x y = refl
ite-arg f false x y = refl