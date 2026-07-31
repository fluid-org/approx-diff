{-# OPTIONS --prop --postfix-projections --safe #-}

-- order-idempotent-embedding instantiated at 𝒞 = SemiMod(S): matrices are realised as linear maps
-- between free semimodules via the matrix embedding, and each order idempotent splits at its
-- fixed-point sub-semimodule, the down-closed vectors.
open import Level using (0ℓ)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import categories using (Category; Splitting)
open import functor using (Functor; _∘F_)
import semimodule
import matrix-embedding-semimod
import order-idempotent-embedding

module order-idempotent-embedding-semimod
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (let open CommutativeSemiring S hiding (_≈_; trans; sym; refl); open Setoid A)
  (∨-idem    : ∀ {x} → x + x ≈ x)
  (∧-idem    : ∀ {x} → x · x ≈ x)
  (⊤-add-top : ∀ {x} → ι + x ≈ ι)
  where

module SemiMod = semimodule S
module ME = matrix-embedding-semimod S
module OIE = order-idempotent-embedding S ∨-idem ∧-idem ⊤-add-top

open Functor
open OIE.OI using (Pos; ord; ord-idem)
open Category SemiMod.cat using (≈-sym; ≈-trans)

-- Matrices over S as linear maps between the free semimodules on their dimensions.
𝓖 : Functor OIE.MatS.cat SemiMod.cat
𝓖 = ME.𝓕 ∘F ME.mat→mor

split : ∀ (P : Pos) → Splitting SemiMod.cat (𝓖 .fmor (P .ord))
split P = SemiMod.splitting (𝓖 .fmor (P .ord))
            (≈-trans (≈-sym (𝓖 .fmor-comp (P .ord) (P .ord))) (𝓖 .fmor-cong (ord-idem P)))

open OIE.Embed 𝓖 split public

-- SemiMod is CMon-enriched with biproducts, 𝓖 is additive, and the free object of width zero is
-- terminal, so 𝓚 preserves the chosen terminal and products.
open Preserve SemiMod.cmon-enriched SemiMod.biproduct
  (λ {m} {n} → ME.mat→mor-εₘ {m} {n}) ME.mat→mor-+ₘ SemiMod.terminal ME.𝟘-terminal public

-- 𝓚 is faithful and full: the matrix embedding recovers entries, and the scalar embedding is
-- injective and retracts.
open Faithful (ME.mat→mor-faithful ME.into-inj) public
open Full (ME.mat→mor-full ME.into-outof) public
