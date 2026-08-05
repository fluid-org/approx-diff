{-# OPTIONS --prop --postfix-projections --safe #-}

-- The rooted lifting of position orders as a biproduct: the root is one fresh position, unordered
-- against the payload, so a down-closed selection of the lifted order is a free root scalar beside
-- a down-closed selection of the payload. This replaces the dominated lifting, whose prefix
-- closure between root and payload identified every eliminator that reads a root with the support
-- map; here reading the root is the projection, distinct from reading anything else. Prefix
-- closure of reported dependencies, when wanted, is a closure applied to answers, not a property
-- of the carriers.
open import Level using (0ℓ)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import lifting using (Lifting)
import lifting-biproduct
import order-idempotent

module order-idempotent-roots
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (let open CommutativeSemiring S hiding (_≈_; trans; sym; refl); open Setoid A)
  (∨-idem    : ∀ {x} → x + x ≈ x)
  (∧-idem    : ∀ {x} → x · x ≈ x)
  (⊤-add-top : ∀ {x} → ι + x ≈ ι)
  where

open order-idempotent S ∨-idem ∧-idem ⊤-add-top hiding (Lp)

-- One position, so a selection of it is a scalar; the roots live here.
𝟙p : Pos
𝟙p = disc 1

-- The lifted order is the biproduct with the unit order, root first, so the lifted dimension and
-- the column layout agree with the dominated lifting it replaces.
Lp : Pos → Pos
Lp P = 𝟙p ⊕ P

module LpB = lifting-biproduct cmon 𝟙p (λ P → biproduct 𝟙p P)

Lp-lifting : Lifting cmon 𝟙p
Lp-lifting = LpB.biproduct-lifting

-- Reading the root and dropping it are the projections.
tag : ∀ {P} → Lp P ⇒ 𝟙p
tag {P} = π₁ 𝟙p P

payload : ∀ {P} → Lp P ⇒ P
payload {P} = π₂ 𝟙p P
