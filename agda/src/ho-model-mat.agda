{-# OPTIONS --postfix-projections --prop --safe #-}

-- The higher-order model: Fam(Mat Two) interpreted in Fam(SemiMod Two),
-- via the embedding F : Mat ↪ SemiMod (in mat).
module ho-model-mat where

open import Level using (0ℓ)
import mat
import semimodule
import two
import ho-model

module E  = mat.Embedding two.semiring
module FD = mat.Mat two.semiring
module SM = semimodule two.semiring

open ho-model.Interpretation
  FD.cat FD.terminal FD.products
  SM.cat SM.cmon-enriched SM.limits SM.terminal SM.biproduct
  E.F E.F-preserve-terminal
  (λ {X} {Y} → E.F-preserve-products {X} {Y})
  public
