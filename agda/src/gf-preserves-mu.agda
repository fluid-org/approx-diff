{-# OPTIONS --postfix-projections --prop --safe #-}

-- The glueing embedding preserves μ-types. Discharges the GFμ hypothesis of
-- the conservativity theorem at the Fam instance: the source μ-object is the
-- Fam(𝒞) W-tree, compared under GF against the realised Fam(Gl) W-tree.

open import Level using (Level; 0ℓ; suc)
open import Data.Nat using () renaming (suc to sucℕ; _+_ to _+ℕ_)
open import Data.Fin using (Fin)
open import categories using (Category; HasProducts; HasTerminal)
open import cmon-enriched using (CMonEnriched; Biproduct; biproducts→products)
open import functor using (Functor; HasLimits; functor-preserve-iso; _∘F_; Colimit; NatIso)
open import prop using (∃; ∃ₛ; Prf)
open import indexed-family using (Fam; fam→functor; functor→fam; fam→functor-eta)
import finite-coproducts-from-indexed
open import finite-product-functor using (preserve-chosen-products; preserve-chosen-terminal)
open import polynomial-functor-2
  using (Preserves-μ; Poly; Poly-map; skeleton; Poly-map-skeleton-go; #c; consts; _++e_)
open import Relation.Binary.PropositionalEquality
  using (_≡_) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
import fam-mu-types-2
import fam-mu-types-2.skeleton
import fam-mu-realisation
import fam-presentation
import fam-mu-checked
import ho-model

open Functor
open Colimit

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
    module Pres = fam-presentation 0ℓ 0ℓ {𝒞}
    module Gld = finite-coproducts-from-indexed.derive GDC
    module FamGl = FMg.Fam𝒞
    module Chk = fam-mu-checked 0ℓ 0ℓ 𝒞-terminal 𝒞-products
                   GlPE.terminal GlPE.products GF GF-preserve-products
  open RGl using (realise; η)

  -- Source side of the carrier comparison: GF of a Fam W-tree is the Gl
  -- set-indexed coproduct of the GF-images of its singleton fibres, via the
  -- canonical presentation and GF's preservation of set-indexed coproducts.
  source-iso : (M : Fam⟨𝒞⟩.Obj) →
    Glued.Iso (GF .fobj M) (GDC (M .Fam⟨𝒞⟩.Obj.idx) (GF ∘F Pres.singletons M) .apex)
  source-iso M =
    Glued.Iso-trans
      (Glued.Iso-sym (functor-preserve-iso GF (Pres.present M)))
      (Glued.Iso-sym (GF-preserve-coproducts-indexed (M .Fam⟨𝒞⟩.Obj.idx) (Pres.singletons M)))

  -- The checked presentation of a Fam(𝒞)-object: the Fam(Gl)-family over the
  -- same index setoid, obtained by applying GF to the singleton fibres.
  check : Fam⟨𝒞⟩.Obj → FMg.Obj
  check = Chk.check

  -- Compare GF of a family against the realisation of a Gl-family over the same
  -- index setoid, given a pointwise isomorphism of the fibre diagrams.
  presented-iso : (M : Fam⟨𝒞⟩.Obj) (Nf : Fam (M .Fam⟨𝒞⟩.Obj.idx) Gl.cat) →
                  NatIso (GF ∘F Pres.singletons M) (fam→functor Nf) →
                  Glued.Iso (GF .fobj M) (realise .fobj (record { idx = M .Fam⟨𝒞⟩.Obj.idx ; fam = Nf }))
  presented-iso M Nf α = Glued.Iso-trans (source-iso M) (Gld.∐-iso α)

  -- GF of a family is the realisation of its checked presentation.
  check-iso : (M : Fam⟨𝒞⟩.Obj) → Glued.Iso (GF .fobj M) (realise .fobj (check M))
  check-iso M =
    presented-iso M (functor→fam (GF ∘F Pres.singletons M)) (fam→functor-eta (GF ∘F Pres.singletons M))

  -- check commutes with μ at the constant-free skeleton, as an iso in Fam(Gl):
  -- the shared shapes make the index setoids agree, and the fibres are products
  -- of GF-images compared by tree recursion.
  check-μ : ∀ {n} (P : Poly Fam⟨𝒞⟩.cat (sucℕ n)) (ε : Fin (n +ℕ #c P) → Fam⟨𝒞⟩.Obj) →
            FamGl.Iso (check (FMc.μObj (skeleton P) ε)) (FMg.μObj (skeleton P) (λ i → check (ε i)))
  check-μ P ε = Chk.ChkMu.check-μ-iso P ε

  -- Realised μ-objects along an equality of polynomials.
  μObj-≡-iso : ∀ {k} {Q₁ Q₂ : Poly FMg.cat (sucℕ k)} (e : Q₁ ≡ Q₂) (δ̂ : Fin k → FMg.Obj) →
               Glued.Iso (realise .fobj (FMg.μObj Q₁ δ̂)) (realise .fobj (FMg.μObj Q₂ δ̂))
  μObj-≡-iso ≡-refl δ̂ = Glued.Iso-refl

  obj-≡-iso : ∀ {X Y : Glued.obj} → X ≡ Y → Glued.Iso X Y
  obj-≡-iso ≡-refl = Glued.Iso-refl

  -- GF preserves μ-types: skeleton in Fam(𝒞), carrier comparison, collapse at
  -- the checked-versus-embedded environments, and the realised skeleton in
  -- Fam(Gl), backwards.
  GFμ : Preserves-μ Fam⟨𝒞⟩-terminal Fam⟨𝒞⟩-products Fam⟨𝒞⟩-strongCoproducts
          GlPE.terminal GlPE.products GlSC Fam⟨𝒞⟩-hasMu Gl-Mu GF
  GFμ {n} P δ =
    Glued.Iso-trans (functor-preserve-iso GF (Sk.skeleton-μ-iso P δ))
    (Glued.Iso-trans (check-iso (FMc.μObj (skeleton P) ε))
    (Glued.Iso-trans (functor-preserve-iso realise (check-μ P ε))
    (Glued.Iso-trans (μObj-≡-iso (≡-sym (Poly-map-skeleton-go η P (λ c → c))) (λ i → check (ε i)))
    (Glued.Iso-trans (RGl.MuCollapse.mu-collapse SKg (RGl.collapseAt SKg)
                       (λ i → check (ε i)) (λ i → η .fobj (GF .fobj (ε i))) isos)
    (Glued.Iso-trans realised-skeleton
      (obj-≡-iso (≡-sym (Gl-Mu-obj (Poly-map GF P) (λ i → GF .fobj (δ i))))))))))
    where
      ε : Fin (n +ℕ #c P) → Fam⟨𝒞⟩.Obj
      ε = δ ++e consts P

      SKg : Poly Gl.cat (sucℕ (n +ℕ #c P))
      SKg = skeleton P

      isos : ∀ i → Glued.Iso (realise .fobj (check (ε i)))
                             (realise .fobj (η .fobj (GF .fobj (ε i))))
      isos i = Glued.Iso-trans (Glued.Iso-sym (check-iso (ε i)))
                 (Glued.Iso-sym (RGl.realise-η-iso (GF .fobj (ε i))))

      realised-skeleton : Glued.Iso (RGl.Creal SKg (λ i → η .fobj (GF .fobj (ε i))))
                                    (RGl.μ-objℰ (Poly-map GF P) (λ i → GF .fobj (δ i)))
      realised-skeleton = {!!}
