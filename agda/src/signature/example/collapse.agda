{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (0ℓ)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import Data.Rational using (ℚ; 0ℚ) renaming (_≟_ to _≟ℚ_)
open import Relation.Nullary using (yes; no)

-- The weight of a rational derivative: ε at 0, ι elsewhere.
module signature.example.collapse where

nonzero : ∀ {A : Setoid 0ℓ 0ℓ} → CommutativeSemiring A → ℚ → Setoid.Carrier A
nonzero S q with q ≟ℚ 0ℚ
... | yes _ = CommutativeSemiring.ε S
... | no _  = CommutativeSemiring.ι S
