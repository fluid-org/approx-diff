{-# OPTIONS --prop --postfix-projections --safe #-}

-- Canonical presentation of a family as the set-indexed coproduct of its
-- singleton fibres. Every object of a Fam category is the coproduct, over its
-- index set, of the one-point families on its fibres. This exhibits an
-- arbitrary family as a diagram that the set-indexed coproduct preservation
-- lemmas can consume.

open import Level using (Level; lift)
import Data.Product as Prod
open import categories using (Category; setoid→category; HasProducts)
open import functor using (Functor; Colimit)
open import prop using (_,_; ⟪_⟫)
open import Data.Unit using (tt)
open import prop-setoid using (Setoid; IsEquivalence; idS; 𝟙)
open import indexed-family using (Fam; _⇒f_; _≃f_)
import fam

module fam-presentation {o m e} (os es : Level) {𝒞 : Category o m e} where

open fam.CategoryOfFamilies os es 𝒞
open Obj
open Mor
open Fam
open _⇒f_
open _≃_
open _≃f_
open IsEquivalence
open Category cat using (Iso; ≈-refl)
open Functor
open Colimit

private
  module 𝒞 = Category 𝒞

-- The diagram of singleton fibres of a family, indexed by its index set.
singletons : (X : Obj) → Functor (setoid→category (X .idx)) cat
singletons X .fobj s = simple[ 𝟙 , X .fam .fm s ]
singletons X .fmor ⟪ p ⟫ = simplef[ idS 𝟙 , X .fam .subst p ]
singletons X .fmor-cong _ = ≈-refl
singletons X .fmor-id .idxf-eq = prop-setoid.≃m-isEquivalence .refl
singletons X .fmor-id .famf-eq .transf-eq = 𝒞.≈-trans 𝒞.id-left (X .fam .refl*)
singletons X .fmor-comp ⟪ p ⟫ ⟪ q ⟫ .idxf-eq =
  prop-setoid.≃m-isEquivalence .sym prop-setoid.id-left
singletons X .fmor-comp ⟪ p ⟫ ⟪ q ⟫ .famf-eq .transf-eq =
  𝒞.≈-trans 𝒞.id-left (𝒞.≈-trans (X .fam .trans* p q) (𝒞.≈-sym 𝒞.id-left))

-- A family is the set-indexed coproduct of its singleton fibres.
present : (X : Obj) → Iso (bigCoproducts (X .idx) (singletons X) .apex) X
present X .Iso.fwd .idxf .prop-setoid._⇒_.func (s Prod., _) = s
present X .Iso.fwd .idxf .prop-setoid._⇒_.func-resp-≈ (e , _) = e
present X .Iso.fwd .famf .transf _ = 𝒞.id _
present X .Iso.fwd .famf .natural _ =
  𝒞.≈-trans 𝒞.id-left (𝒞.≈-trans 𝒞.id-left (𝒞.≈-sym 𝒞.id-right))
present X .Iso.bwd .idxf .prop-setoid._⇒_.func s = s Prod., lift tt
present X .Iso.bwd .idxf .prop-setoid._⇒_.func-resp-≈ e = e , _
present X .Iso.bwd .famf .transf _ = 𝒞.id _
present X .Iso.bwd .famf .natural _ =
  𝒞.≈-trans 𝒞.id-left (𝒞.≈-sym (𝒞.≈-trans 𝒞.id-right 𝒞.id-left))
present X .Iso.fwd∘bwd≈id .idxf-eq .prop-setoid._≃m_.func-eq e = e
present X .Iso.fwd∘bwd≈id .famf-eq .transf-eq =
  𝒞.≈-trans (𝒞.∘-cong (X .fam .refl*) (𝒞.≈-trans 𝒞.id-left 𝒞.id-left)) 𝒞.id-left
present X .Iso.bwd∘fwd≈id .idxf-eq .prop-setoid._≃m_.func-eq (e , _) = e , _
present X .Iso.bwd∘fwd≈id .famf-eq .transf-eq =
  𝒞.≈-trans
    (𝒞.∘-cong (𝒞.≈-trans 𝒞.id-left (X .fam .refl*)) (𝒞.≈-trans 𝒞.id-left 𝒞.id-left))
    𝒞.id-left

-- simple preserves finite products: a singleton on a product is the product of
-- the singletons. Lets the fibrewise carrier comparison move a product past GF.
module _ (Prods : HasProducts 𝒞) where
  private
    module ⊗M = products Prods
    module PH = HasProducts Prods
  open ⊗M using (_⊗_)

  simple-⊗ : ∀ {a b} → Iso simple[ 𝟙 , PH.prod a b ] (simple[ 𝟙 , a ] ⊗ simple[ 𝟙 , b ])
  simple-⊗ .Iso.fwd .idxf .prop-setoid._⇒_.func _ = lift tt Prod., lift tt
  simple-⊗ .Iso.fwd .idxf .prop-setoid._⇒_.func-resp-≈ _ = _
  simple-⊗ .Iso.fwd .famf .transf _ = 𝒞.id _
  simple-⊗ .Iso.fwd .famf .natural _ =
    𝒞.≈-trans 𝒞.id-left (𝒞.≈-sym (𝒞.≈-trans 𝒞.id-right PH.prod-m-id))
  simple-⊗ .Iso.bwd .idxf .prop-setoid._⇒_.func _ = lift tt
  simple-⊗ .Iso.bwd .idxf .prop-setoid._⇒_.func-resp-≈ _ = _
  simple-⊗ .Iso.bwd .famf .transf _ = 𝒞.id _
  simple-⊗ .Iso.bwd .famf .natural _ =
    𝒞.≈-trans (𝒞.≈-trans 𝒞.id-left PH.prod-m-id) (𝒞.≈-sym 𝒞.id-left)
  simple-⊗ .Iso.fwd∘bwd≈id .idxf-eq .prop-setoid._≃m_.func-eq _ = _ , _
  simple-⊗ .Iso.fwd∘bwd≈id .famf-eq .transf-eq =
    𝒞.≈-trans (𝒞.∘-cong PH.prod-m-id (𝒞.≈-trans 𝒞.id-left 𝒞.id-left)) 𝒞.id-left
  simple-⊗ .Iso.bwd∘fwd≈id .idxf-eq .prop-setoid._≃m_.func-eq _ = _
  simple-⊗ .Iso.bwd∘fwd≈id .famf-eq .transf-eq =
    𝒞.≈-trans 𝒞.id-left (𝒞.≈-trans 𝒞.id-left 𝒞.id-left)

  private module FPH = HasProducts ⊗M.products

  -- The product comparison is natural in both fibres.
  simple-⊗-natural : ∀ {a a' b b'} (f : a 𝒞.⇒ a') (g : b 𝒞.⇒ b') →
    Category._≈_ cat
      (Category._∘_ cat (simple-⊗ .Iso.fwd) simplef[ idS 𝟙 , PH.prod-m f g ])
      (Category._∘_ cat (FPH.prod-m simplef[ idS 𝟙 , f ] simplef[ idS 𝟙 , g ]) (simple-⊗ .Iso.fwd))
  simple-⊗-natural f g .idxf-eq .prop-setoid._≃m_.func-eq _ = _
  simple-⊗-natural f g .famf-eq .transf-eq =
    𝒞.≈-trans (𝒞.∘-cong PH.prod-m-id 𝒞.≈-refl)
      (𝒞.≈-trans 𝒞.id-left
        (𝒞.≈-trans 𝒞.id-left
          (𝒞.≈-trans 𝒞.id-left
            (𝒞.≈-sym (𝒞.≈-trans 𝒞.id-left
              (𝒞.≈-trans 𝒞.id-right (PH.pair-cong 𝒞.id-left 𝒞.id-left)))))))
