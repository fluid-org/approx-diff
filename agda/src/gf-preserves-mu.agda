{-# OPTIONS --postfix-projections --prop --safe #-}

-- The glueing embedding preserves μ-types. Discharges the GFμ hypothesis of
-- conservativity.syntactic-2 at the Fam instance: the source μ-object is the
-- Fam(𝒞) W-tree, compared under GF against the realised Fam(Gl) W-tree.

open import Level using (Level; 0ℓ; suc)
open import categories using (Category; HasProducts; HasTerminal)
open import cmon-enriched using (CMonEnriched; Biproduct; biproducts→products)
open import functor using (Functor; HasLimits)
open import prop using (∃; ∃ₛ; Prf)
open import finite-product-functor using (preserve-chosen-products; preserve-chosen-terminal)
import polynomial-functor-2
import ho-model

open Functor

module gf-preserves-mu
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
  open I
  open I.Conservativity

  GFμ : polynomial-functor-2.Preserves-μ
          Fam⟨𝒞⟩-terminal Fam⟨𝒞⟩-products Fam⟨𝒞⟩-strongCoproducts
          GlPE.terminal GlPE.products GlSC Fam⟨𝒞⟩-hasMu Gl-Mu GF
  GFμ P δ = {!!}
