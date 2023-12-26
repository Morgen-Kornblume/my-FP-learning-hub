module natural where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym)
open import Data.Bool

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)
infixl 7 _*_
_*_ : ℕ → ℕ → ℕ
zero * n = zero
suc m * n = n + (m * n)

pred : ℕ → ℕ
pred zero = zero
pred (suc n) = n

0+ : ∀(x : ℕ) → zero + x ≡ x
0+ x = refl

+0 : ∀(x : ℕ) → x + zero ≡ x
+0 zero = refl
+0 (suc x) rewrite +0 x = refl

+assoc : ∀ (x y z : ℕ) → x + (y + z) ≡ (x + y) + z
+assoc zero y z = refl
+assoc (suc x) y z rewrite +assoc x y z = refl

+suc : ∀ (x y : ℕ) → x + suc y ≡ suc (x + y)
+suc zero y = refl
+suc (suc x) y rewrite +suc x y = refl

+comm : ∀ (x y : ℕ) → x + y ≡ y + x
+comm zero y rewrite +0 y = refl
+comm (suc x) y rewrite +comm x y | +suc y x = refl

*distrib : ∀ (x y z : ℕ) → (x + y) * z ≡ (x * z) + (y * z)
*distrib zero y z = refl
*distrib (suc x) y z rewrite *distrib x y z | +assoc z (x * z) (y * z) = refl


_<ℕ_ : ℕ → ℕ → Bool
zero <ℕ zero = false
zero <ℕ suc y = true
suc x <ℕ zero = false
suc x <ℕ suc y = x <ℕ y


_=ℕ_ : ℕ → ℕ → Bool
zero =ℕ zero = true
zero =ℕ suc y = false
suc x =ℕ zero = false
suc x =ℕ suc y = x =ℕ y


_≤ℕ_ : ℕ → ℕ → Bool
zero ≤ℕ zero = true
zero ≤ℕ suc y = true
suc x ≤ℕ zero = false
suc x ≤ℕ suc y = x ≤ℕ y


_≥ℕ_ : ℕ → ℕ → Bool
x ≥ℕ y = y ≤ℕ x

_>ℕ_ : ℕ → ℕ → Bool
x >ℕ y = y <ℕ x

<0 : ∀ (x : ℕ) → (x <ℕ zero) ≡ false
<0 zero = refl
<0 (suc x) = refl

𝔹-contra : false ≡ true → ∀{l} {P : Set l} → P 
𝔹-contra ()

<-trans : ∀ {x y z : ℕ} → (x <ℕ y) ≡ true → (y <ℕ z) ≡ true → (x <ℕ z) ≡ true
<-trans {x} {zero} p1 p2 rewrite <0 x = 𝔹-contra p1
<-trans {zero} {suc y} {zero} p1 () 
<-trans {zero} {suc y} {suc z} p1 p2 = refl
<-trans {suc x} {suc y} {zero} p1 () 
<-trans {suc x} {suc y} {suc z} p1 p2 = <-trans {x} {y} {z} p1 p2

=ℕ-to-≡ : ∀ {x y : ℕ} → x =ℕ y ≡ true → x ≡ y
=ℕ-to-≡ {zero} {zero} u = refl
=ℕ-to-≡ {suc x} {zero} ()
=ℕ-to-≡ {zero} {suc y} ()
=ℕ-to-≡ {suc x} {suc y} u rewrite =ℕ-to-≡ {x} {y} u = refl

=ℕ-refl : ∀ (x : ℕ) → (x =ℕ x) ≡ true
=ℕ-refl zero = refl
=ℕ-refl (suc x) = =ℕ-refl x


=ℕ-from-≡ : ∀ {x y : ℕ} → x ≡ y → x =ℕ y ≡ true
=ℕ-from-≡ {x} refl = =ℕ-refl x

isEven : ℕ → Bool
isOdd : ℕ → Bool
isEven zero = true
isEven (suc x) = isOdd x
isOdd zero = false
isOdd (suc x) = isEven x

~_ : Bool → Bool
~ true = false
~ false = true

even~odd : ∀ (x : ℕ) → isEven x ≡ ~ isOdd x
odd~even : ∀ (x : ℕ) → isOdd x ≡ ~ isEven x
even~odd zero = refl
even~odd (suc x) = odd~even x
odd~even zero = refl
odd~even (suc x) = even~odd x

+assoc2 : ∀ (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
+assoc2 zero y z = refl
+assoc2 (suc x) y z rewrite +assoc2 x y z = refl

+-swap : ∀ (x y z : ℕ) → x + (y + z) ≡ y + (x + z)
+-swap x y z rewrite sym(+assoc2 y x z) | sym(+assoc2 x y z) | +comm x y = refl

*0 : ∀ (x : ℕ) → x * zero ≡ zero
*0 zero = refl
*0 (suc x) rewrite *0 x = refl

*-suc : ∀ (x y : ℕ) → x * suc y ≡ x + x * y
*-suc zero y = refl
*-suc (suc x) y rewrite *-suc x y | +-swap y x (x * y) = refl

*-comm : (x y : ℕ) → x * y ≡ y * x
*-comm zero y rewrite *0 y = refl
*-comm (suc x) y rewrite *-suc y x | *-comm x y = refl

+-samex : ∀ (x y z : ℕ) → y ≡ z → x + y ≡ x + z
+-samex zero y z p = p 
+-samex (suc x) y z p rewrite +-samex x y z p = refl

*-distri2 : (x y z : ℕ) → x * (y + z) ≡ x * y + x * z
*-distri2 zero y z = refl
*-distri2 (suc x) y z rewrite *-distri2 x y z | +assoc2 y z (x * y + x * z) | +assoc2 y (x * y) (z + x * z) = +-samex y (z + (x * y + x * z)) (x * y + (z + x * z)) (+-swap z (x * y) (x * z))

-- problem 1.2: associativity of _*_
*-assoc : (x y z : ℕ) → (x * y) * z ≡ x * (y * z)
*-assoc zero y z = refl
*-assoc (suc x) y z rewrite *-assoc x y z | sym(+assoc2 y z (x * y + x * z)) | *-comm (y + x * y) z | *-distri2 z y (x * y) | *-comm z y | *-comm z (x * y) | sym(*-assoc x y z) = refl

n≮n : (n : ℕ) → (n <ℕ n) ≡ false
n≮n zero = refl 
n≮n (suc n) rewrite n≮n n = refl

-- 反对称性
<-antisym : (x y : ℕ) → (x <ℕ y) ≡ true → (y <ℕ x) ≡ false
<-antisym zero zero ()
<-antisym (suc x) zero ()
<-antisym zero (suc y) p = refl
<-antisym (suc x) (suc y) p rewrite <-antisym x y p = refl

-- 三岐性
infix 20 _or_
_or_ : Bool → Bool → Bool
true or _ = true
false or b = b

<-trichotomy : (x y : ℕ) → (((x <ℕ y) or (x =ℕ y)) or (y <ℕ x)) ≡ true
<-trichotomy zero zero = refl
<-trichotomy (suc x) zero = refl
<-trichotomy zero (suc y) = refl
<-trichotomy (suc x) (suc y) rewrite <-trichotomy x y = refl
