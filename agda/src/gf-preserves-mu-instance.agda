{-# OPTIONS --postfix-projections --prop --safe #-}

-- Apply gf-preserves-mu at the interpretation instance: build the higher-order
-- interpretation once, feed its glueing data to the proof, and discharge the
-- recursive-types definability theorem.

open import Level using (Level; 0ℓ; suc)
open import categories using (Category; HasProducts; HasTerminal)
open import cmon-enriched using (CMonEnriched; Biproduct; biproducts→products)
open import functor using (Functor; HasLimits)
open import prop using (∃; ∃ₛ; Prf)
open import finite-product-functor using (preserve-chosen-products; preserve-chosen-terminal)
open import signature using (Signature)
import gf-preserves-mu
import ho-model

open Functor

module gf-preserves-mu-instance
  {o : Level}
  (𝒞 : Category o 0ℓ 0ℓ)
  (𝒞-terminal : HasTerminal 𝒞)
  (𝒞-products : HasProducts 𝒞)
  (𝒟 : Category (suc 0ℓ) 0ℓ 0ℓ)
  (𝒟-cmon : CMonEnriched 𝒟)
  (𝒟-limits : ∀ (𝒮 : Category 0ℓ 0ℓ 0ℓ) → HasLimits 𝒮 𝒟)
  (𝒟-terminal : HasTerminal 𝒟)
  (𝒟-biproducts : ∀ x y → Biproduct 𝒟-cmon x y)
  (F : Functor 𝒞 𝒟)
  (F-preserve-terminal : preserve-chosen-terminal F 𝒞-terminal 𝒟-terminal)
  (F-preserve-products : preserve-chosen-products F 𝒞-products (biproducts→products _ 𝒟-biproducts))
  (F-faithful : ∀ {a b} {g₁ g₂ : Category._⇒_ 𝒞 a b} → Category._≈_ 𝒟 (F .fmor g₁) (F .fmor g₂) → Category._≈_ 𝒞 g₁ g₂)
  (F-def : ∀ {a b} (h : Category._⇒_ 𝒟 (F .fobj a) (F .fobj b)) →
           Prf (∃ (Category._⇒_ 𝒞 a b) λ g → Category._≈_ 𝒟 (F .fmor g) h) →
           ∃ₛ (Category._⇒_ 𝒞 a b) λ g → Category._≈_ 𝒟 (F .fmor g) h)
  where

  module I = ho-model.Interpretation 𝒞 𝒞-terminal 𝒞-products 𝒟 𝒟-cmon 𝒟-limits
               𝒟-terminal 𝒟-biproducts F F-preserve-terminal F-preserve-products F-faithful F-def
  open I.Conservativity

  module GFM = gf-preserves-mu 𝒞 𝒞-terminal 𝒞-products
                 Gl.cat GlPE.terminal GlPE.products Gl-exponentials GlSC GDC
                 GF GF-preserve-products GF-preserve-coproducts-indexed Gl-Mu Gl-Mu-obj

  open GFM public using (GFμ)

  -- Syntactic definability for the recursive-types language: higher-order terms
  -- at first-order types collapse to Fam(𝒞) morphisms, for any signature and
  -- model of it in Fam(𝒞).
  module syntactic-μ {ℓ} (Sig : Signature ℓ) =
    syntactic Sig Fam⟨𝒞⟩-strongCoproducts Fam⟨𝒞⟩-hasMu GF-preserve-strong-coproducts GFμ
