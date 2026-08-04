{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- Collapse of a family to its total space: the set-indexed coproduct of its
-- fibres over its index setoid, functorially in the family. The glueing of
-- rooted families reindexes presheaf predicates along this functor, so the
-- stages of the existing logical relations are reused unchanged.
------------------------------------------------------------------------------

open import Level using (Level; _⊔_)
open import prop using (Prf; ⟪_⟫)
open import prop-setoid as PS using (Setoid; IsEquivalence)
open import categories using (Category; setoid→category)
open import functor using (Functor; HasColimits; Colimit; NatTrans; ≃-NatTrans; constF)
open import indexed-family using (Fam; _⇒f_)
import fam
import stable-coproducts-indexed

module fam-collapse {o m e} (os es : Level) {𝒟 : Category o m e}
  (LC : ∀ (S : Setoid os es) → HasColimits (setoid→category S) 𝒟)
  where

private
  module 𝒟C = Category 𝒟

open fam.CategoryOfFamilies os es 𝒟
open Obj
open Mor
open _≃_
open Fam
open _⇒f_
open Colimit
open NatTrans
open Functor

module SI = stable-coproducts-indexed LC

-- A family as a diagram over its index setoid.
famF : (X : Obj) → Functor (setoid→category (X .idx)) 𝒟
famF X .fobj i = X .fam .fm i
famF X .fmor ⟪ e ⟫ = X .fam .subst e
famF X .fmor-cong _ = 𝒟C.≈-refl
famF X .fmor-id = X .fam .refl*
famF X .fmor-comp ⟪ f ⟫ ⟪ g ⟫ = X .fam .trans* f g

-- The cocone a family morphism induces on the collapse of its target.
push : ∀ {X Y : Obj} (f : Mor X Y) →
       NatTrans (famF X) (constF (setoid→category (X .idx)) (SI.∐ (Y .idx) (famF Y)))
push {X} {Y} f .transf i =
  𝒟C._∘_ (SI.inj (famF Y) (f .idxf .PS._⇒_.func i)) (f .famf .transf i)
push {X} {Y} f .natural {i} {j} ⟪ e ⟫ =
  𝒟C.≈-trans 𝒟C.id-left
  (𝒟C.≈-sym
    (𝒟C.≈-trans (𝒟C.assoc _ _ _)
    (𝒟C.≈-trans (𝒟C.∘-cong 𝒟C.≈-refl (f .famf .natural e))
    (𝒟C.≈-trans (𝒟C.≈-sym (𝒟C.assoc _ _ _))
    (𝒟C.∘-cong
      (𝒟C.≈-trans (𝒟C.≈-sym (LC (Y .idx) (famF Y) .cocone .natural
                     ⟪ f .idxf .PS._⇒_.func-resp-≈ e ⟫))
                  𝒟C.id-left)
      𝒟C.≈-refl)))))

-- The collapse functor.
Σf : Functor cat 𝒟
Σf .fobj X = SI.∐ (X .idx) (famF X)
Σf .fmor {X} {Y} f = LC (X .idx) (famF X) .colambda (SI.∐ (Y .idx) (famF Y)) (push f)
Σf .fmor-cong {X} {Y} {f} {g} f≃g =
  LC (X .idx) (famF X) .colambda-cong (record { transf-eq = λ i →
    𝒟C.≈-trans
      (𝒟C.∘-cong
        (𝒟C.≈-trans (𝒟C.≈-sym 𝒟C.id-left)
          (LC (Y .idx) (famF Y) .cocone .natural
            ⟪ f≃g .idxf-eq .PS._≃m_.func-eq
                (X .idx .Setoid.isEquivalence .IsEquivalence.refl) ⟫))
        𝒟C.≈-refl)
      (𝒟C.≈-trans (𝒟C.assoc _ _ _)
        (𝒟C.∘-cong 𝒟C.≈-refl
          (f≃g .famf-eq .indexed-family._≃f_.transf-eq))) })
Σf .fmor-id {X} =
  𝒟C.≈-trans
    (LC (X .idx) (famF X) .colambda-cong
      (record { transf-eq = λ i → 𝒟C.≈-trans 𝒟C.id-right (𝒟C.≈-sym 𝒟C.id-left) }))
    (LC (X .idx) (famF X) .colambda-ext _ (𝒟C.id _))
Σf .fmor-comp {X} {Y} {Z} f g =
  𝒟C.≈-trans
    (LC (X .idx) (famF X) .colambda-cong (record { transf-eq = λ i →
      𝒟C.≈-trans (𝒟C.∘-cong 𝒟C.≈-refl 𝒟C.id-left)
      (𝒟C.≈-trans (𝒟C.≈-sym (𝒟C.assoc _ _ _))
      (𝒟C.≈-trans (𝒟C.∘-cong
                     (𝒟C.≈-sym (LC (Y .idx) (famF Y) .colambda-coeval _ (push f)
                                  .≃-NatTrans.transf-eq (g .idxf .PS._⇒_.func i)))
                     𝒟C.≈-refl)
      (𝒟C.≈-trans (𝒟C.assoc _ _ _)
      (𝒟C.≈-trans (𝒟C.∘-cong 𝒟C.≈-refl
                     (𝒟C.≈-sym (LC (X .idx) (famF X) .colambda-coeval _ (push g)
                                  .≃-NatTrans.transf-eq i)))
                  (𝒟C.≈-sym (𝒟C.assoc _ _ _)))))) }))
    (LC (X .idx) (famF X) .colambda-ext _
      (𝒟C._∘_ (Σf .fmor f) (Σf .fmor g)))
