{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- The rooted logical relations at the concrete model: families over the position orders as the
-- first-order side, families over plain semimodules as the model, and the realisation as the
-- change of base.
------------------------------------------------------------------------------

open import Level using (0ℓ)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
import conservativity-rooted
import order-idempotent-realise

module conservativity-rooted-order-idempotent
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (let open CommutativeSemiring S hiding (_≈_; trans; sym; refl); open Setoid A)
  (∨-idem    : ∀ {x} → x + x ≈ x)
  (∧-idem    : ∀ {x} → x · x ≈ x)
  (⊤-add-top : ∀ {x} → ι + x ≈ ι)
  where

private
  module R = order-idempotent-realise S ∨-idem ∧-idem ⊤-add-top

-- The rooted logical relations, with the decorated μ-carrier, its algebra map and its
-- catamorphism at every polynomial and environment.
module Rooted = conservativity-rooted
  R.SemiMod.terminal R.SemiMod.cmon-enriched R.SemiMod.biproduct R.Ls-lifting R.𝓥F
