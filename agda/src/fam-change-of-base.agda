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
    {𝒞 : Category o m e} (T𝒞 : HasTerminal 𝒞)
    (CM𝒞 : CMonEnriched 𝒞) (BP𝒞 : ∀ x y → Biproduct CM𝒞 x y)
    (𝟙𝒞 : Category.obj 𝒞)
    {𝒟 : Category o₂ m₂ e₂} (T𝒟 : HasTerminal 𝒟)
    (CM𝒟 : CMonEnriched 𝒟) (BP𝒟 : ∀ x y → Biproduct CM𝒟 x y)
    (𝟙𝒟 : Category.obj 𝒟)
    (F : Functor 𝒞 𝒟)
    (F-terminal : preserve-chosen-terminal F T𝒞 T𝒟)
    (F-prod : preserve-chosen-products F (biproducts→products CM𝒞 BP𝒞) (biproducts→products CM𝒟 BP𝒟))
    (let module L𝒞 = lifting CM𝒞 BP𝒞 𝟙𝒞) (let module L𝒟 = lifting CM𝒟 BP𝒟 𝟙𝒟)
    (let module 𝒞 = Category 𝒞) (let module 𝒟 = Category 𝒟)
    (F-L : ∀ X → 𝒟.Iso (Functor.fobj F (L𝒞.L X)) (L𝒟.L (Functor.fobj F X)))
    (F-L-natural : ∀ {X Y} (f : X 𝒞.⇒ Y) →
       (F-L Y .𝒟.Iso.fwd 𝒟.∘ Functor.fmor F (L𝒞.Lmap f))
         𝒟.≈ (L𝒟.Lmap (Functor.fmor F f) 𝒟.∘ F-L X .𝒟.Iso.fwd))
    where

module Fam⟨𝒞⟩μ = fam-mu-lifting.in-map os es CM𝒞 BP𝒞 𝟙𝒞
module Fam⟨𝒟⟩μ = fam-mu-lifting.in-map os es CM𝒟 BP𝒟 𝟙𝒟

private
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

Fam⟨F⟩-preserves-terminal = fam-functor.preserve-terminal os (os ⊔ es) F T𝒞 T𝒟 F-terminal

Fam⟨F⟩-preserves-products =
  fam-functor.preserve-products os (os ⊔ es) F
    (biproducts→products CM𝒞 BP𝒞) (biproducts→products CM𝒟 BP𝒟)
    (λ {X} {Y} → F-prod {X} {Y})

-- The lifting comparison, fibrewise: the change of base commutes with the two liftings.
Fam⟨F⟩-L : ∀ (X : Fam⟨𝒞⟩μ.Obj) →
           Fam𝒟.Iso (Fam⟨F⟩ .fobj (Fam⟨𝒞⟩μ.Lf X)) (Fam⟨𝒟⟩μ.Lf (Fam⟨F⟩ .fobj X))
Fam⟨F⟩-L X .fwd .idxf = prop-setoid.idS _
Fam⟨F⟩-L X .fwd .famf .transf x = F-L (X .fam .fm x) .fwd
Fam⟨F⟩-L X .fwd .famf .natural e = F-L-natural (X .fam .subst e)
Fam⟨F⟩-L X .bwd .idxf = prop-setoid.idS _
Fam⟨F⟩-L X .bwd .famf .transf x = F-L (X .fam .fm x) .bwd
Fam⟨F⟩-L X .bwd .famf .natural {x₁} {x₂} e =
  flip (F-L (X .fam .fm x₁)) (F-L (X .fam .fm x₂)) (F-L-natural (X .fam .subst e))
  where
    -- Conjugating the naturality square by the comparison isomorphisms.
    flip : ∀ {a a' b b'} (i : 𝒟.Iso a b) (j : 𝒟.Iso a' b')
           {f : a 𝒟.⇒ a'} {g : b 𝒟.⇒ b'} →
           𝒟._≈_ (𝒟._∘_ (j .fwd) f) (𝒟._∘_ g (i .fwd)) →
           𝒟._≈_ (𝒟._∘_ (j .bwd) g) (𝒟._∘_ f (i .bwd))
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
        𝒟.id _ ∘ (f ∘ i .bwd)
      ≈⟨ id-left ⟩
        f ∘ i .bwd
      ∎
      where
        open 𝒟
        open prop-setoid.≈-Reasoning 𝒟.isEquiv
Fam⟨F⟩-L X .fwd∘bwd≈id .idxf-eq .func-eq e = e
Fam⟨F⟩-L X .fwd∘bwd≈id .famf-eq .transf-eq {x} =
  𝒟.≈-trans
    (𝒟.∘-cong (Fam⟨𝒟⟩μ.Lf (Fam⟨F⟩ .fobj X) .fam .refl*)
               (𝒟.≈-trans 𝒟.id-left (F-L (X .fam .fm x) .fwd∘bwd≈id)))
    𝒟.id-left
Fam⟨F⟩-L X .bwd∘fwd≈id .idxf-eq .func-eq e = e
Fam⟨F⟩-L X .bwd∘fwd≈id .famf-eq .transf-eq {x} =
  𝒟.≈-trans
    (𝒟.∘-cong (Fam⟨F⟩ .fobj (Fam⟨𝒞⟩μ.Lf X) .fam .refl*)
               (𝒟.≈-trans 𝒟.id-left (F-L (X .fam .fm x) .bwd∘fwd≈id)))
    𝒟.id-left

-- Constants transport along the change of base: the image of a constant family is constant at
-- the image morphisms, entered through a chosen map from the target unit object.
Fam⟨F⟩-constant : (u : 𝟙𝒟 𝒟.⇒ F .fobj 𝟙𝒞) → ∀ {X : Fam⟨𝒞⟩μ.Obj} →
                  Fam⟨𝒞⟩μ.Constant X → Fam⟨𝒟⟩μ.Constant (Fam⟨F⟩ .fobj X)
Fam⟨F⟩-constant u c .Fam⟨𝒟⟩μ.at x = 𝒟._∘_ (F .fmor (c .Fam⟨𝒞⟩μ.at x)) u
Fam⟨F⟩-constant u {X} c .Fam⟨𝒟⟩μ.at-natural e =
  𝒟.≈-trans (𝒟.≈-sym (𝒟.assoc _ _ _))
    (𝒟.∘-cong
      (𝒟.≈-trans (𝒟.≈-sym (F .fmor-comp _ _)) (F .fmor-cong (c .Fam⟨𝒞⟩μ.at-natural e)))
      𝒟.≈-refl)

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
  fam-mu-lifting.fibrewise os es CM𝒞 BP𝒞 𝟙𝒞 CM𝒟 BP𝒟 𝟙𝒟
    F (λ {X} {Y} → F-prod {X} {Y}) F-L (λ {X} {Y} f → F-L-natural {X} {Y} f)
