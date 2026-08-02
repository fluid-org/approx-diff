{-# OPTIONS --prop --postfix-projections --safe #-}

-- What the lifting looks like on the target side. A position order is realised as its fixed
-- vectors, and a vector is fixed by a lifted order exactly when its tail is fixed and its root entry
-- dominates the support of that tail, the support being the join of the coordinates. So the realised
-- lifting is the fixed vectors of the order with a new bottom adjoined, the extra element being the
-- root selected over an empty tail.
--
-- The support is linear and no morphism increases it, so the construction is functorial in an object
-- paired with its support. It is not a construction on a bare semimodule, since the constraint
-- mentions the support, which such an object does not carry.
open import Level using (0ℓ)
open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; zero; suc)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import basics using (IsPreorder; IsTop)
import matrix
import order-idempotent

module order-idempotent-support
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (let open CommutativeSemiring S hiding (_≈_; trans; sym; refl); open Setoid A)
  (∨-idem    : ∀ {x} → x + x ≈ x)
  (∧-idem    : ∀ {x} → x · x ≈ x)
  (⊤-add-top : ∀ {x} → ι + x ≈ ι)
  where

open matrix.Mat S using (Matrix; Vec; Σ; Σ-cong; Σ-+; Σ-·-distribₗ)
open order-idempotent S ∨-idem ∧-idem ⊤-add-top
open IsPreorder L.≤-isPreorder using () renaming (trans to ≤-trans)

-- A matrix acting on a vector, and the vectors an order fixes.
app : ∀ {m n} → Matrix m n → Vec n → Vec m
app {m} {n} M v i = Σ {n} (λ j → M i j · v j)

Fixed : ∀ (P : Pos) → Vec (P .dim) → Prop 0ℓ
Fixed P v = ∀ i → app (P .ord) v i ≈ v i

-- The join of the coordinates.
supp : ∀ {n} → Vec n → Setoid.Carrier A
supp {n} v = Σ {n} v

supp-+ : ∀ {n} (u v : Vec n) → supp {n} (λ i → u i + v i) ≈ (supp {n} u + supp {n} v)
supp-+ {n} u v = sym (Σ-+ u v)

supp-· : ∀ {n} (s : Setoid.Carrier A) (v : Vec n) → supp {n} (λ i → s · v i) ≈ (s · supp {n} v)
supp-· {n} s v = sym (Σ-·-distribₗ s v)

-- No matrix increases the support: each entry is below ι, so each summand is below a coordinate.
supp-mono : ∀ {m n} (M : Matrix m n) (v : Vec n) → supp {m} (app M v) L.≤ supp {n} v
supp-mono {m} {n} M v =
  L.Σ-lub {m} (λ i → app M v i)
    (λ i → L.Σ-lub {n} (λ j → M i j · v j)
             (λ j → ≤-trans (L.∧-monoˡ (IsTop.≤-top L.⊤-isTop))
                    (≤-trans (L.≈→≤ ·-lunit) (L.Σ-ub {n} v j))))

head : ∀ {n} → Vec (suc n) → Setoid.Carrier A
head v = v zero

tail : ∀ {n} → Vec (suc n) → Vec n
tail v i = v (suc i)

-- Acting by a lifted order: the root entry gains the tail's support, and the tail is acted on by
-- the order itself.
Lp-app-root : ∀ (P : Pos) (v : Vec (suc (P .dim))) →
              app (Lp P .ord) v zero ≈ (head v + supp {P .dim} (tail v))
Lp-app-root P v = +-cong ·-lunit (Σ-cong {P .dim} (λ i → ·-lunit))

Lp-app-tail : ∀ (P : Pos) (v : Vec (suc (P .dim))) (i : Fin (P .dim)) →
              app (Lp P .ord) v (suc i) ≈ app (P .ord) (tail v) i
Lp-app-tail P v i = trans (+-cong ε-annihilₗ refl) +-lunit

-- So the fixed vectors of a lifted order are exactly the pairs of a root entry and a fixed tail
-- whose support the root entry dominates.
Lp-fixed-tail : ∀ (P : Pos) (v : Vec (suc (P .dim))) → Fixed (Lp P) v → Fixed P (tail v)
Lp-fixed-tail P v h i = trans (sym (Lp-app-tail P v i)) (h (suc i))

Lp-fixed-root : ∀ (P : Pos) (v : Vec (suc (P .dim))) →
                Fixed (Lp P) v → supp {P .dim} (tail v) L.≤ head v
Lp-fixed-root P v h = trans +-comm (trans (sym (Lp-app-root P v)) (h zero))

Lp-fixed : ∀ (P : Pos) (v : Vec (suc (P .dim))) →
           Fixed P (tail v) → supp {P .dim} (tail v) L.≤ head v → Fixed (Lp P) v
Lp-fixed P v ht hr zero    = trans (Lp-app-root P v) (trans +-comm hr)
Lp-fixed P v ht hr (suc i) = trans (Lp-app-tail P v i) (ht i)

-- The support of a lifted vector is its root entry, since the root dominates the tail.
Lp-supp : ∀ (P : Pos) (v : Vec (suc (P .dim))) →
          Fixed (Lp P) v → supp {suc (P .dim)} v ≈ head v
Lp-supp P v h = trans +-comm (Lp-fixed-root P v h)

-- A morphism does not increase the support, so an object paired with its support is carried to one
-- again, and the lifting above is functorial on those pairs.
mor-supp : ∀ {P Q} (f : P ⇒ Q) (v : Vec (P .dim)) →
           supp {Q .dim} (app (f .mat) v) L.≤ supp {P .dim} v
mor-supp f v = supp-mono (f .mat) v
