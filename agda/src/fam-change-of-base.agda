{-# OPTIONS --prop --postfix-projections --safe #-}

-- The change of base between family categories: given two bases with biproducts and liftings and a
-- structured functor between them (products, terminal and the lifting preserved), the change of
-- base between the family categories preserves the structure. Coproducts and terminal are
-- native to the family categories; the lifting comparison acts fibrewise; the μ-carriers
-- are carried across by the fibrewise comparison.

open import Level using (Level; _⊔_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import prop using (_,_)
open import prop-setoid using (Setoid; IsEquivalence)
open import categories using (Category; HasTerminal; HasCoproducts)
open import cmon-enriched using (CMonEnriched; Biproduct; biproducts→products)
import lifting
open import functor using (Functor)
open import finite-product-functor using (preserve-chosen-products; preserve-chosen-terminal)
open import indexed-family using (Fam; _⇒f_; _≃f_)
import fam
import fam-functor
import fam-mu-lifting.in-map
import fam-mu-lifting.fibrewise

module fam-change-of-base {o m e o₂ m₂ e₂} (os es : Level)
    {𝒞 : Category o m e} (T : HasTerminal 𝒞)
    (CM : CMonEnriched 𝒞) (BP : ∀ x y → Biproduct CM x y)
    (𝟙c : Category.obj 𝒞)
    {𝒟 : Category o₂ m₂ e₂} (T' : HasTerminal 𝒟)
    (CM' : CMonEnriched 𝒟) (BP' : ∀ x y → Biproduct CM' x y)
    (𝟙d : Category.obj 𝒟)
    (F : Functor 𝒞 𝒟)
    (F-terminal : preserve-chosen-terminal F T T')
    (F-prod : preserve-chosen-products F (biproducts→products CM BP) (biproducts→products CM' BP'))
    (let module CL = lifting CM BP 𝟙c) (let module DL = lifting CM' BP' 𝟙d)
    (F-L : ∀ X → Category.Iso 𝒟 (Functor.fobj F (CL.L X)) (DL.L (Functor.fobj F X)))
    (F-L-natural : ∀ {X Y} (f : Category._⇒_ 𝒞 X Y) →
       Category._≈_ 𝒟
         (Category._∘_ 𝒟 (Category.Iso.fwd (F-L Y)) (Functor.fmor F (CL.Lmap f)))
         (Category._∘_ 𝒟 (DL.Lmap (Functor.fmor F f)) (Category.Iso.fwd (F-L X))))
    where

module Fam⟨𝒞⟩μ = fam-mu-lifting.in-map os es CM BP 𝟙c
module Fam⟨𝒟⟩μ = fam-mu-lifting.in-map os es CM' BP' 𝟙d

private
  module 𝒟C = Category 𝒟
  module Fam𝒟 = Category Fam⟨𝒟⟩μ.cat

open Category.Iso
open Category.IsIso
open Functor
open Fam
open _⇒f_
open fam.CategoryOfFamilies.Obj
open fam.CategoryOfFamilies.Mor
open fam.CategoryOfFamilies._≃_
open prop-setoid._⇒_
open prop-setoid._≃m_
open indexed-family._≃f_

-- The change of base and its preservation of the family-level structure.
Fam⟨F⟩ : Functor Fam⟨𝒞⟩μ.cat Fam⟨𝒟⟩μ.cat
Fam⟨F⟩ = fam-functor.FamF os (os ⊔ es) F

Fam⟨F⟩-preserves-coproducts = fam-functor.preserve-coproducts os (os ⊔ es) F

Fam⟨F⟩-preserves-terminal = fam-functor.preserve-terminal os (os ⊔ es) F T T' F-terminal

Fam⟨F⟩-preserves-products =
  fam-functor.preserve-products os (os ⊔ es) F
    (biproducts→products CM BP) (biproducts→products CM' BP')
    (λ {X} {Y} → F-prod {X} {Y})

-- The lifting comparison, fibrewise: the change of base commutes with the two liftings.
Fam⟨F⟩-L : ∀ (X : Fam⟨𝒞⟩μ.Obj) →
           Category.Iso Fam⟨𝒟⟩μ.cat (Fam⟨F⟩ .fobj (Fam⟨𝒞⟩μ.Lf X)) (Fam⟨𝒟⟩μ.Lf (Fam⟨F⟩ .fobj X))
Fam⟨F⟩-L X .fwd .idxf = prop-setoid.idS _
Fam⟨F⟩-L X .fwd .famf .transf x = F-L (X .fam .fm x) .fwd
Fam⟨F⟩-L X .fwd .famf .natural e = F-L-natural (X .fam .subst e)
Fam⟨F⟩-L X .bwd .idxf = prop-setoid.idS _
Fam⟨F⟩-L X .bwd .famf .transf x = F-L (X .fam .fm x) .bwd
Fam⟨F⟩-L X .bwd .famf .natural {x₁} {x₂} e =
  flip (F-L (X .fam .fm x₁)) (F-L (X .fam .fm x₂)) (F-L-natural (X .fam .subst e))
  where
    -- Conjugating the naturality square by the comparison isomorphisms.
    flip : ∀ {a a' b b'} (i : 𝒟C.Iso a b) (j : 𝒟C.Iso a' b')
           {f : a 𝒟C.⇒ a'} {g : b 𝒟C.⇒ b'} →
           𝒟C._≈_ (𝒟C._∘_ (j .fwd) f) (𝒟C._∘_ g (i .fwd)) →
           𝒟C._≈_ (𝒟C._∘_ (j .bwd) g) (𝒟C._∘_ f (i .bwd))
    flip i j {f} {g} sq =
      begin
        j .bwd ∘ g
      ≈˘⟨ ∘-cong ≈-refl (≈-trans (∘-cong ≈-refl (i .fwd∘bwd≈id)) id-right) ⟩
        j .bwd ∘ (g ∘ (i .fwd ∘ i .bwd))
      ≈˘⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
        j .bwd ∘ ((g ∘ i .fwd) ∘ i .bwd)
      ≈˘⟨ ∘-cong ≈-refl (∘-cong sq ≈-refl) ⟩
        j .bwd ∘ ((j .fwd ∘ f) ∘ i .bwd)
      ≈⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
        j .bwd ∘ (j .fwd ∘ (f ∘ i .bwd))
      ≈˘⟨ assoc _ _ _ ⟩
        (j .bwd ∘ j .fwd) ∘ (f ∘ i .bwd)
      ≈⟨ ∘-cong (j .bwd∘fwd≈id) ≈-refl ⟩
        𝒟C.id _ ∘ (f ∘ i .bwd)
      ≈⟨ id-left ⟩
        f ∘ i .bwd
      ∎
      where
        open 𝒟C
        open prop-setoid.≈-Reasoning 𝒟C.isEquiv
Fam⟨F⟩-L X .fwd∘bwd≈id .idxf-eq .func-eq e = e
Fam⟨F⟩-L X .fwd∘bwd≈id .famf-eq .transf-eq {x} =
  𝒟C.≈-trans
    (𝒟C.∘-cong (Fam⟨𝒟⟩μ.Lf (Fam⟨F⟩ .fobj X) .fam .refl*)
               (𝒟C.≈-trans 𝒟C.id-left (F-L (X .fam .fm x) .fwd∘bwd≈id)))
    𝒟C.id-left
Fam⟨F⟩-L X .bwd∘fwd≈id .idxf-eq .func-eq e = e
Fam⟨F⟩-L X .bwd∘fwd≈id .famf-eq .transf-eq {x} =
  𝒟C.≈-trans
    (𝒟C.∘-cong (Fam⟨F⟩ .fobj (Fam⟨𝒞⟩μ.Lf X) .fam .refl*)
               (𝒟C.≈-trans 𝒟C.id-left (F-L (X .fam .fm x) .bwd∘fwd≈id)))
    𝒟C.id-left

module bool (𝟙ty : Fam⟨𝒞⟩μ.Obj) where

  private
    module CPc = HasCoproducts Fam⟨𝒞⟩μ.coproducts
    module CPd = HasCoproducts Fam⟨𝒟⟩μ.coproducts

  Bool𝒞 = CPc.coprod (Fam⟨𝒞⟩μ.Lf 𝟙ty) (Fam⟨𝒞⟩μ.Lf 𝟙ty)
  Bool𝒟 = CPd.coprod (Fam⟨𝒟⟩μ.Lf (Fam⟨F⟩ .fobj 𝟙ty)) (Fam⟨𝒟⟩μ.Lf (Fam⟨F⟩ .fobj 𝟙ty))

  Fam⟨F⟩-preserves-bool : Fam⟨𝒟⟩μ.Mor (Fam⟨F⟩ .fobj Bool𝒞) Bool𝒟
  Fam⟨F⟩-preserves-bool =
    Fam𝒟._∘_ (CPd.coprod-m (Fam⟨F⟩-L 𝟙ty .fwd) (Fam⟨F⟩-L 𝟙ty .fwd))
             (Fam⟨F⟩-preserves-coproducts .inverse)

module FW =
  fam-mu-lifting.fibrewise os es CM BP 𝟙c CM' BP' 𝟙d
    F (λ {X} {Y} → F-prod {X} {Y}) F-L (λ {X} {Y} f → F-L-natural {X} {Y} f)
