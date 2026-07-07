{-# OPTIONS --prop --postfix-projections --safe #-}

-- Realisation of a family as the set-indexed coproduct of its fibres: the
-- counit of the free coproduct completion, for a category with setoid-indexed
-- colimits.

open import Level using (Level)
open import prop using (⟪_⟫)
open import prop-setoid using (Setoid; IsEquivalence; module ≈-Reasoning)
  renaming (_⇒_ to _⇒s_; _≃m_ to _≃s_)
open import categories using (Category; setoid→category)
open import functor
  using (Functor; HasColimits; Colimit; IsColimit; NatTrans; constF; constFmor; ≃-NatTrans)
  renaming (_∘_ to _∘N_)
open import indexed-family using (Fam; _⇒f_; fam→functor)
import fam

module fam-realisation {o m e} (os es : Level) {ℰ : Category o m e}
  (EC : ∀ (A : Setoid os es) → HasColimits (setoid→category A) ℰ)
  where

open Category ℰ
open fam.CategoryOfFamilies os es ℰ using (cat; Mor-∘)
open fam.CategoryOfFamilies.Obj
open fam.CategoryOfFamilies.Mor
open fam.CategoryOfFamilies._≃_
open Functor
open NatTrans
open ≃-NatTrans
open Colimit
open IsColimit
open Fam
open _⇒f_
open _⇒s_ renaming (func to _$s_)
open prop-setoid._≃m_ using (func-eq)

private
  colim : (X : Category.obj cat) → Colimit (fam→functor (X .fam))
  colim X = EC (X .idx) (fam→functor (X .fam))

  -- The cocone on the realisation of the target induced by a morphism of
  -- families.
  push : ∀ {X Y} → Category._⇒_ cat X Y →
         NatTrans (fam→functor (X .fam)) (constF (setoid→category (X .idx)) (colim Y .apex))
  push {X} {Y} f .transf x = colim Y .cocone .transf (f .idxf $s x) ∘ f .famf .transf x
  push {X} {Y} f .natural {x₁} {x₂} ⟪ e ⟫ =
    begin
      id _ ∘ (colim Y .cocone .transf (f .idxf $s x₁) ∘ f .famf .transf x₁)
    ≈⟨ id-left ⟩
      colim Y .cocone .transf (f .idxf $s x₁) ∘ f .famf .transf x₁
    ≈⟨ ∘-cong (≈-trans (≈-sym id-left) (colim Y .cocone .natural ⟪ f .idxf .func-resp-≈ e ⟫)) ≈-refl ⟩
      (colim Y .cocone .transf (f .idxf $s x₂) ∘ Y .fam .subst (f .idxf .func-resp-≈ e)) ∘ f .famf .transf x₁
    ≈⟨ assoc _ _ _ ⟩
      colim Y .cocone .transf (f .idxf $s x₂) ∘ (Y .fam .subst (f .idxf .func-resp-≈ e) ∘ f .famf .transf x₁)
    ≈˘⟨ ∘-cong ≈-refl (f .famf .natural e) ⟩
      colim Y .cocone .transf (f .idxf $s x₂) ∘ (f .famf .transf x₂ ∘ X .fam .subst e)
    ≈˘⟨ assoc _ _ _ ⟩
      (colim Y .cocone .transf (f .idxf $s x₂) ∘ f .famf .transf x₂) ∘ X .fam .subst e
    ∎ where open ≈-Reasoning isEquiv

realise : Functor cat ℰ
realise .fobj X = colim X .apex
realise .fmor {X} {Y} f = colim X .isColimit .colambda _ (push f)
realise .fmor-cong {X} {Y} {f} {g} f≃g =
  colim X .isColimit .colambda-cong eq
  where
    eq : ≃-NatTrans (push f) (push g)
    eq .transf-eq x =
      begin
        colim Y .cocone .transf (f .idxf $s x) ∘ f .famf .transf x
      ≈⟨ ∘-cong (≈-trans (≈-sym id-left) (colim Y .cocone .natural ⟪ f≃g .idxf-eq .func-eq (X .idx .Setoid.refl) ⟫)) ≈-refl ⟩
        (colim Y .cocone .transf (g .idxf $s x) ∘ Y .fam .subst (f≃g .idxf-eq .func-eq (X .idx .Setoid.refl))) ∘ f .famf .transf x
      ≈⟨ assoc _ _ _ ⟩
        colim Y .cocone .transf (g .idxf $s x) ∘ (Y .fam .subst (f≃g .idxf-eq .func-eq (X .idx .Setoid.refl)) ∘ f .famf .transf x)
      ≈⟨ ∘-cong ≈-refl (f≃g .famf-eq .indexed-family._≃f_.transf-eq {x}) ⟩
        colim Y .cocone .transf (g .idxf $s x) ∘ g .famf .transf x
      ∎ where open ≈-Reasoning isEquiv
realise .fmor-id {X} =
  ≈-trans (colim X .isColimit .colambda-cong eq) (colim X .isColimit .colambda-ext _ (id _))
  where
    eq : ≃-NatTrans (push (Category.id cat X)) (constFmor (id _) ∘N colim X .cocone)
    eq .transf-eq x = ≈-trans id-right (≈-sym id-left)
realise .fmor-comp {X} {Y} {Z} f g =
  ≈-trans (colim X .isColimit .colambda-cong eq)
    (colim X .isColimit .colambda-ext _
      (colim Y .isColimit .colambda _ (push f) ∘ colim X .isColimit .colambda _ (push g)))
  where
    eq : ≃-NatTrans (push (Mor-∘ f g))
           (constFmor (colim Y .isColimit .colambda _ (push f) ∘ colim X .isColimit .colambda _ (push g))
             ∘N colim X .cocone)
    eq .transf-eq x =
      begin
        colim Z .cocone .transf (f .idxf $s (g .idxf $s x)) ∘
          (id _ ∘ (f .famf .transf (g .idxf $s x) ∘ g .famf .transf x))
      ≈⟨ ∘-cong ≈-refl id-left ⟩
        colim Z .cocone .transf (f .idxf $s (g .idxf $s x)) ∘ (f .famf .transf (g .idxf $s x) ∘ g .famf .transf x)
      ≈˘⟨ assoc _ _ _ ⟩
        (colim Z .cocone .transf (f .idxf $s (g .idxf $s x)) ∘ f .famf .transf (g .idxf $s x)) ∘ g .famf .transf x
      ≈˘⟨ ∘-cong (colim Y .isColimit .colambda-coeval _ (push f) .transf-eq (g .idxf $s x)) ≈-refl ⟩
        (colim Y .isColimit .colambda _ (push f) ∘ colim Y .cocone .transf (g .idxf $s x)) ∘ g .famf .transf x
      ≈⟨ assoc _ _ _ ⟩
        colim Y .isColimit .colambda _ (push f) ∘ (colim Y .cocone .transf (g .idxf $s x) ∘ g .famf .transf x)
      ≈˘⟨ ∘-cong ≈-refl (colim X .isColimit .colambda-coeval _ (push g) .transf-eq x) ⟩
        colim Y .isColimit .colambda _ (push f) ∘ (colim X .isColimit .colambda _ (push g) ∘ colim X .cocone .transf x)
      ≈˘⟨ assoc _ _ _ ⟩
        (colim Y .isColimit .colambda _ (push f) ∘ colim X .isColimit .colambda _ (push g)) ∘ colim X .cocone .transf x
      ∎ where open ≈-Reasoning isEquiv
