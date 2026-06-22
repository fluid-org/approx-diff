{-# OPTIONS --postfix-projections --prop --safe #-}

-- The higher-order model: Fam(Mat Two) interpreted in Fam(SemiMod Two),
-- via the embedding F : Mat ↪ SemiMod (in mat).
module ho-model-mat where

open import Level using (0ℓ)
import matrix-new
import semimodule
import semiring-bool
import ho-model

module E  = matrix-new.Embedding semiring-bool.semiring
module FD = matrix-new.Mat semiring-bool.semiring
module SM = semimodule semiring-bool.semiring

open ho-model.Interpretation
  FD.cat FD.terminal FD.products
  SM.cat SM.cmon-enriched SM.limits SM.terminal SM.biproduct
  E.F E.F-preserve-terminal
  (λ {X} {Y} → E.F-preserve-products {X} {Y})
  public
