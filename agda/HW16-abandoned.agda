-- transpose-vec : {n m : ℕ} → n by m matrix → (x y : ℕ) → x < m ≡ true → y < n ≡ true → Vec ℕ (suc y)
-- transpose-vec mat x 0 p q = matrix-elt mat 0 x q p ∷ []
-- transpose-vec mat x (suc y) p q = matrix-elt mat (suc y) x q p ∷ transpose-vec mat x y p (<-1same q)

-- transpose-helper : {n m : ℕ} → n by m matrix → (x y : ℕ) → x < m ≡ true → y < n ≡ true → (suc x) by (suc y) matrix
-- transpose-helper mat 0 y p q = transpose-vec mat 0 y p q ∷ []
-- transpose-helper mat (suc x) y p q = transpose-vec mat (suc x) y p q ∷ transpose-helper mat x y (<-1same p) q 
--  

-- pred : ℕ → ℕ
-- pred zero = zero
-- pred (suc n) = n

-- <suc : (n : ℕ) → n < suc n ≡ true
-- <suc zero = refl
-- <suc (suc n) rewrite <suc n = refl

-- <pred : (n : ℕ) → pred n < n ≡ true
-- <pred zero = refl
-- <pred (suc n) = <suc n

-- transpose : {n m : ℕ} → n by m matrix → m by n matrix
-- transpose {n} {m} mat = transpose-helper mat (pred m) (pred n) (<pred m) (<pred n)

_-_ : ℕ → ℕ → ℕ
  x - 0 = x
  (suc x) - (suc y) = x - y
  0 - x = x

  vector-helper : {n m : ℕ} → n by m matrix → (x y : ℕ) → x < m ≡ true → (Vec ℕ (n - y))
  vector-helper {n} {m} mat x y p with (y < n)
  ... | true  = matrix-elt mat y x refl p ∷ vector-helper mat x (suc y) p
  ... | false = []

  transpose-helper : {n m : ℕ} → n by m matrix → (x : ℕ) → (m - x) by n matrix
  transpose-helper {n} {m} mat x with (x < m)
  ... | true = vector-helper mat x 0 refl ∷ transpose-helper mat (suc x) 
  ... | false = []