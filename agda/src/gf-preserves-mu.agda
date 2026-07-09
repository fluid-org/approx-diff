{-# OPTIONS --postfix-projections --prop --safe #-}

-- The glueing embedding preserves μ-types. Discharges the GFμ hypothesis of
-- conservativity.syntactic-2 at the Fam instance: the source μ-object is the
-- Fam(𝒞) W-tree, compared under GF against the realised Fam(Gl) W-tree.

open import Level using (Level; 0ℓ; suc)
open import Data.Fin using (Fin)
open import categories using (Category; HasProducts; HasTerminal)
open import cmon-enriched using (CMonEnriched; Biproduct; biproducts→products)
open import functor using (Functor; HasLimits; functor-preserve-iso; _∘F_)
open import prop using (∃; ∃ₛ; Prf)
open import finite-product-functor using (preserve-chosen-products; preserve-chosen-terminal)
open import polynomial-functor-2 using (Preserves-μ; Poly; Poly-map)
import fam-mu-types-2
import fam-mu-types-2.skeleton
import fam-mu-realisation
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

  private
    module Sk  = fam-mu-types-2.skeleton 0ℓ 0ℓ 𝒞-terminal 𝒞-products
    module FMc = fam-mu-types-2 0ℓ 0ℓ 𝒞-terminal 𝒞-products
    module RGl = fam-mu-realisation 0ℓ 0ℓ GDC GlPE.terminal GlPE.products GlPE.exponentials GlSC
    module FMg = RGl.FM
  open RGl using (realise; η)

  -- Cross-category realisation comparison: GF of the Fam(𝒞) interpretation agrees
  -- with the realised Fam(Gl) interpretation, over any pointwise agreement of the
  -- environments up to realisation. The template is fam-mu-realisation's
  -- single-category fobj-realise-iso.
  carrier-comparison : ∀ {n} (Q : Poly Fam⟨𝒞⟩.cat n)
                       (env : Fin n → Fam⟨𝒞⟩.Obj) (env̌ : Fin n → FMg.Obj) →
                       (∀ i → Glued.Iso (GF .fobj (env i)) (realise .fobj (env̌ i))) →
                       Glued.Iso (GF .fobj (FMc.fobj FMc.μObj Q env))
                                 (realise .fobj (FMg.fobj FMg.μObj (Poly-map (η ∘F GF) Q) env̌))
  carrier-comparison (Poly.const A) env env̌ js = Glued.Iso-sym (RGl.realise-η-iso (GF .fobj A))
  carrier-comparison (Poly.var i)   env env̌ js = js i
  carrier-comparison (P Poly.+ Q)   env env̌ js = Glued.Iso-refl
  carrier-comparison (P Poly.× Q)   env env̌ js = {!!}
  carrier-comparison (Poly.μ Q)     env env̌ js = {!!}

  -- Step 1: strip constants in 𝒞. The remaining chain compares the constant-free
  -- skeleton W-tree under GF against the realised Fam(Gl) W-tree.
  GFμ : polynomial-functor-2.Preserves-μ
          Fam⟨𝒞⟩-terminal Fam⟨𝒞⟩-products Fam⟨𝒞⟩-strongCoproducts
          GlPE.terminal GlPE.products GlSC Fam⟨𝒞⟩-hasMu Gl-Mu GF
  GFμ P δ = Glued.Iso-trans (functor-preserve-iso GF (Sk.skeleton-μ-iso P δ)) {!!}
