{-# OPTIONS --postfix-projections --prop --safe #-}

-- The higher-order model over the Data.Vec matrix representation (matrix-new):
-- Fam(Mat S) interpreted in Fam(SemiMod S) via the embedding F : Mat ↪ SemiMod.
open import Level using (0ℓ)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
import matrix-new
import semimodule
import ho-model

module ho-model-matrix-new {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A) where

module E  = matrix-new.Embedding S
module FD = matrix-new.Mat S
module SM = semimodule S

open ho-model.Interpretation
  FD.cat FD.terminal FD.products
  SM.cat SM.cmon-enriched SM.limits SM.terminal SM.biproduct
  E.F E.F-preserve-terminal
  (λ {X} {Y} → E.F-preserve-products {X} {Y})
  public
