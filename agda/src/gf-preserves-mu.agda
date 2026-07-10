{-# OPTIONS --postfix-projections --prop --safe #-}

-- The glueing embedding preserves μ-types. Discharges the GFμ hypothesis of
-- conservativity.syntactic-2 at the Fam instance: the source μ-object is the
-- Fam(𝒞) W-tree, compared under GF against the realised Fam(Gl) W-tree.

open import Level using (Level; 0ℓ; suc)
open import Data.Fin using (Fin)
open import categories using (Category; HasProducts; HasTerminal; HasCoproducts; strong-coproducts→coproducts)
open import cmon-enriched using (CMonEnriched; Biproduct; biproducts→products)
open import functor using (Functor; HasLimits; functor-preserve-iso; _∘F_; Colimit; NatIso)
open import prop using (∃; ∃ₛ; Prf)
open import indexed-family using (Fam; fam→functor; functor→fam)
import finite-coproducts-from-indexed
open import finite-product-functor using (preserve-chosen-products; preserve-chosen-terminal)
open import polynomial-functor-2 using (Preserves-μ; Poly; Poly-map)
import fam-mu-types-2
import fam-mu-types-2.skeleton
import fam-mu-realisation
import fam-realisation
import fam-presentation
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
    module FRg = fam-realisation 0ℓ 0ℓ GDC
    GlCoprodStruct = strong-coproducts→coproducts GlPE.terminal GlSC
    module GlCoprod = HasCoproducts GlCoprodStruct
    module GlProd = HasProducts GlPE.products
    module Pres = fam-presentation 0ℓ 0ℓ {𝒞}
    module Gld = finite-coproducts-from-indexed.derive GDC
  open RGl using (realise; η)

  -- Source side of the carrier comparison: GF of a Fam W-tree is the Gl
  -- set-indexed coproduct of the GF-images of its singleton fibres, via the
  -- canonical presentation and GF's preservation of set-indexed coproducts.
  source-iso : (M : Fam⟨𝒞⟩.Obj) →
    Glued.Iso (GF .fobj M)
              (GDC (M .Fam⟨𝒞⟩.Obj.idx) (GF ∘F Pres.singletons M) .Colimit.apex)
  source-iso M =
    Glued.Iso-trans
      (Glued.Iso-sym (functor-preserve-iso GF (Pres.present M)))
      (Glued.Iso-sym (GF-preserve-coproducts-indexed (M .Fam⟨𝒞⟩.Obj.idx) (Pres.singletons M)))

  -- The checked presentation of a Fam(𝒞)-object: the Fam(Gl)-family over the
  -- same index setoid whose fibres are the GF-images of the singleton fibres.
  check : Fam⟨𝒞⟩.Obj → FMg.Obj
  check X .FMg.Obj.idx = X .Fam⟨𝒞⟩.Obj.idx
  check X .FMg.Obj.fam = functor→fam (GF ∘F Pres.singletons X)

  -- Compare GF of a family against the realisation of a Gl-family over the same
  -- index setoid, given a pointwise isomorphism of the fibre diagrams.
  presented-iso : (M : Fam⟨𝒞⟩.Obj) (Nf : Fam (M .Fam⟨𝒞⟩.Obj.idx) Gl.cat) →
                  NatIso (GF ∘F Pres.singletons M) (fam→functor Nf) →
                  Glued.Iso (GF .fobj M)
                            (realise .fobj (record { idx = M .Fam⟨𝒞⟩.Obj.idx ; fam = Nf }))
  presented-iso M Nf α = Glued.Iso-trans (source-iso M) (Gld.∐-iso α)

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
  carrier-comparison (P Poly.+ Q)   env env̌ js =
    Glued.Iso-trans
      (Glued.Iso-sym (Glued.IsIso→Iso GF-preserve-strong-coproducts))
      (Glued.Iso-trans
        (GlCoprod.coproduct-preserve-iso
          (carrier-comparison P env env̌ js)
          (carrier-comparison Q env env̌ js))
        (Glued.Iso-sym (FRg.realise-coproducts-iso GlCoprodStruct _ _)))
  carrier-comparison (P Poly.× Q)   env env̌ js =
    Glued.Iso-trans
      (Glued.IsIso→Iso GF-preserve-products)
      (Glued.Iso-trans
        (GlProd.product-preserves-iso
          (carrier-comparison P env env̌ js)
          (carrier-comparison Q env env̌ js))
        (Glued.Iso-sym (FRg.realise-products-iso GlPE.products GlPE.exponentials _ _)))
  carrier-comparison (Poly.μ Q)     env env̌ js = {!!}

  -- Step 1: strip constants in 𝒞. The remaining chain compares the constant-free
  -- skeleton W-tree under GF against the realised Fam(Gl) W-tree.
  GFμ : polynomial-functor-2.Preserves-μ
          Fam⟨𝒞⟩-terminal Fam⟨𝒞⟩-products Fam⟨𝒞⟩-strongCoproducts
          GlPE.terminal GlPE.products GlSC Fam⟨𝒞⟩-hasMu Gl-Mu GF
  GFμ P δ = Glued.Iso-trans (functor-preserve-iso GF (Sk.skeleton-μ-iso P δ)) {!!}
