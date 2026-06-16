{-# OPTIONS --postfix-projections --prop --safe #-}

-- The higher-order model: Fam(FDSemiMod₂ Two) interpreted in Fam(SemiMod Two),
-- via the embedding F : FDSemiMod₂ ↪ SemiMod (in fd-semimodule-2).
module ho-model-fd-semimod-2 where

open import Level using (0ℓ)
import fd-semimodule-2
import semimodule
import two
import ho-model

module E  = fd-semimodule-2.Embedding two.semiring
module FD = fd-semimodule-2.FDSemiMod₂ two.semiring
module SM = semimodule {0ℓ} {0ℓ} two.semiring

open ho-model.Interpretation
  FD.cat FD.terminal FD.products
  SM.cat SM.cmon-enriched SM.limits SM.terminal SM.biproduct
  E.F E.F-preserve-terminal
  (λ {X} {Y} → E.F-preserve-products {X} {Y})
  public
