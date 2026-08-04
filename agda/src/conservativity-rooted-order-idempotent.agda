{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- The rooted logical relations at the concrete model: families over the position orders as the
-- first-order side, families over the supported semimodules as the model, and the realisation as
-- the change of base.
------------------------------------------------------------------------------

open import Level using (0ℓ)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
import conservativity-rooted
import ho-model-rooted-order-idempotent

module conservativity-rooted-order-idempotent
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (let open CommutativeSemiring S hiding (_≈_; trans; sym; refl); open Setoid A)
  (∨-idem    : ∀ {x} → x + x ≈ x)
  (∧-idem    : ∀ {x} → x · x ≈ x)
  (⊤-add-top : ∀ {x} → ι + x ≈ ι)
  where

open ho-model-rooted-order-idempotent S ∨-idem ∧-idem ⊤-add-top

-- The rooted logical relations, with the decorated μ-carrier, its algebra map and its
-- catamorphism at every polynomial and environment.
module Rooted = conservativity-rooted
  Sup-terminal SS.Sup.cmon Sup-biproduct SS.supported-lifting 𝓥F
