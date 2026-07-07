{-# OPTIONS --prop --postfix-projections --safe #-}

-- Realisation of a family as the set-indexed coproduct of its fibres: the
-- counit of the free coproduct completion, for a category with setoid-indexed
-- colimits.

open import Level using (Level; lift)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import prop using (⟪_⟫) renaming (_,_ to _,ₚ_)
open import prop-setoid using (Setoid; IsEquivalence; module ≈-Reasoning)
  renaming (_⇒_ to _⇒s_; _≃m_ to _≃s_)
open import categories using (Category; setoid→category; HasTerminal; IsTerminal; HasProducts; HasExponentials)
open import functor
  using (Functor; HasColimits; Colimit; IsColimit; NatTrans; constF; constFmor; ≃-NatTrans)
  renaming (_∘_ to _∘N_; _∘F_ to _∘F_)
open import indexed-family using (Fam; _⇒f_; fam→functor)
import fam
import product-cocontinuity

module fam-realisation {o m e} (os es : Level) {ℰ : Category o m e}
  (EC : ∀ (A : Setoid os es) → HasColimits (setoid→category A) ℰ)
  where

open Category ℰ
open fam.CategoryOfFamilies os es ℰ using (cat; Mor-∘; bigCoproducts; terminal)
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

-- Realisation preserves setoid-indexed coproducts: the realise-image of the
-- coproduct cocone in the category of families is a colimit in ℰ.
module _ (S : Setoid os es) (D : Functor (setoid→category S) cat) where

  private
    module C = Category cat
    ⨿D = bigCoproducts S D

    inS : ∀ s → Category._⇒_ cat (D .fobj s) (⨿D .apex)
    inS s = ⨿D .cocone .transf s

  realiseCocone : NatTrans (realise ∘F D) (constF (setoid→category S) (realise .fobj (⨿D .apex)))
  realiseCocone .transf s = realise .fmor (inS s)
  realiseCocone .natural {s₁} {s₂} ⟪ e ⟫ =
    ≈-trans id-left
      (≈-trans (realise .fmor-cong (C.≈-trans (C.≈-sym C.id-left) (⨿D .cocone .natural ⟪ e ⟫)))
        (realise .fmor-comp _ _))

  private
    -- Flatten a cocone under realise ∘F D to a cocone on the total family.
    flat : ∀ x (α : NatTrans (realise ∘F D) (constF (setoid→category S) x)) →
           NatTrans (fam→functor (⨿D .apex .fam)) (constF (setoid→category (⨿D .apex .idx)) x)
    flat x α .transf (s , d) = α .transf s ∘ colim (D .fobj s) .cocone .transf d
    flat x α .natural {s₁ , d₁} {s₂ , d₂} ⟪ es ,ₚ ed ⟫ =
      begin
        id _ ∘ (α .transf s₁ ∘ colim (D .fobj s₁) .cocone .transf d₁)
      ≈⟨ id-left ⟩
        α .transf s₁ ∘ colim (D .fobj s₁) .cocone .transf d₁
      ≈⟨ ∘-cong (≈-trans (≈-sym id-left) (α .natural ⟪ es ⟫)) ≈-refl ⟩
        (α .transf s₂ ∘ realise .fmor (D .fmor ⟪ es ⟫)) ∘ colim (D .fobj s₁) .cocone .transf d₁
      ≈⟨ assoc _ _ _ ⟩
        α .transf s₂ ∘ (realise .fmor (D .fmor ⟪ es ⟫) ∘ colim (D .fobj s₁) .cocone .transf d₁)
      ≈⟨ ∘-cong ≈-refl (colim (D .fobj s₁) .isColimit .colambda-coeval _ (push (D .fmor ⟪ es ⟫)) .transf-eq d₁) ⟩
        α .transf s₂ ∘ (colim (D .fobj s₂) .cocone .transf (D .fmor ⟪ es ⟫ .idxf $s d₁) ∘ D .fmor ⟪ es ⟫ .famf .transf d₁)
      ≈⟨ ∘-cong ≈-refl (∘-cong (≈-trans (≈-sym id-left) (colim (D .fobj s₂) .cocone .natural ⟪ ed ⟫)) ≈-refl) ⟩
        α .transf s₂ ∘ ((colim (D .fobj s₂) .cocone .transf d₂ ∘ D .fobj s₂ .fam .subst ed) ∘ D .fmor ⟪ es ⟫ .famf .transf d₁)
      ≈⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
        α .transf s₂ ∘ (colim (D .fobj s₂) .cocone .transf d₂ ∘ (D .fobj s₂ .fam .subst ed ∘ D .fmor ⟪ es ⟫ .famf .transf d₁))
      ≈˘⟨ assoc _ _ _ ⟩
        (α .transf s₂ ∘ colim (D .fobj s₂) .cocone .transf d₂) ∘ (D .fobj s₂ .fam .subst ed ∘ D .fmor ⟪ es ⟫ .famf .transf d₁)
      ∎ where open ≈-Reasoning isEquiv

  realise-preserves-coproducts : IsColimit (realise ∘F D) (realise .fobj (⨿D .apex)) realiseCocone
  realise-preserves-coproducts .IsColimit.colambda x α =
    colim (⨿D .apex) .isColimit .colambda x (flat x α)
  realise-preserves-coproducts .IsColimit.colambda-cong {x} {α} {β} α≃β =
    colim (⨿D .apex) .isColimit .colambda-cong eq
    where
      eq : ≃-NatTrans (flat x α) (flat x β)
      eq .transf-eq (s , d) = ∘-cong (α≃β .transf-eq s) ≈-refl
  realise-preserves-coproducts .IsColimit.colambda-coeval x α .transf-eq s =
    ≈-trans (≈-sym (colim (D .fobj s) .isColimit .colambda-ext x h))
      (≈-trans (colim (D .fobj s) .isColimit .colambda-cong eq)
        (colim (D .fobj s) .isColimit .colambda-ext x (α .transf s)))
    where
      h : Category._⇒_ ℰ (realise .fobj (D .fobj s)) x
      h = colim (⨿D .apex) .isColimit .colambda x (flat x α) ∘ realise .fmor (inS s)

      eq : ≃-NatTrans (constFmor h ∘N colim (D .fobj s) .cocone)
                      (constFmor (α .transf s) ∘N colim (D .fobj s) .cocone)
      eq .transf-eq d =
        begin
          h ∘ colim (D .fobj s) .cocone .transf d
        ≈⟨ assoc _ _ _ ⟩
          colim (⨿D .apex) .isColimit .colambda x (flat x α) ∘ (realise .fmor (inS s) ∘ colim (D .fobj s) .cocone .transf d)
        ≈⟨ ∘-cong ≈-refl (colim (D .fobj s) .isColimit .colambda-coeval _ (push (inS s)) .transf-eq d) ⟩
          colim (⨿D .apex) .isColimit .colambda x (flat x α) ∘ (colim (⨿D .apex) .cocone .transf (s , d) ∘ id _)
        ≈⟨ ∘-cong ≈-refl id-right ⟩
          colim (⨿D .apex) .isColimit .colambda x (flat x α) ∘ colim (⨿D .apex) .cocone .transf (s , d)
        ≈⟨ colim (⨿D .apex) .isColimit .colambda-coeval _ (flat x α) .transf-eq (s , d) ⟩
          α .transf s ∘ colim (D .fobj s) .cocone .transf d
        ∎ where open ≈-Reasoning isEquiv
  realise-preserves-coproducts .IsColimit.colambda-ext x f =
    ≈-trans (colim (⨿D .apex) .isColimit .colambda-cong eq)
      (colim (⨿D .apex) .isColimit .colambda-ext x f)
    where
      eq : ≃-NatTrans _ _
      eq .transf-eq (s , d) =
        begin
          (f ∘ realise .fmor (inS s)) ∘ colim (D .fobj s) .cocone .transf d
        ≈⟨ assoc _ _ _ ⟩
          f ∘ (realise .fmor (inS s) ∘ colim (D .fobj s) .cocone .transf d)
        ≈⟨ ∘-cong ≈-refl (colim (D .fobj s) .isColimit .colambda-coeval _ (push (inS s)) .transf-eq d) ⟩
          f ∘ (colim (⨿D .apex) .cocone .transf (s , d) ∘ id _)
        ≈⟨ ∘-cong ≈-refl id-right ⟩
          f ∘ colim (⨿D .apex) .cocone .transf (s , d)
        ∎ where open ≈-Reasoning isEquiv

-- Realisation preserves the terminal object: the coproduct over the singleton
-- setoid of the terminal fibre is terminal.
module _ (ET : HasTerminal ℰ) where

  private
    module ET = HasTerminal ET

    𝟙F = terminal ET .HasTerminal.witness

    inT = colim 𝟙F .cocone .transf (lift tt)

    roundtrip : (inT ∘ ET.to-terminal) ≈ id (realise .fobj 𝟙F)
    roundtrip =
      ≈-trans (≈-sym (colim 𝟙F .isColimit .colambda-ext _ (inT ∘ ET.to-terminal)))
        (≈-trans (colim 𝟙F .isColimit .colambda-cong eq)
          (colim 𝟙F .isColimit .colambda-ext _ (id _)))
      where
        eq : ≃-NatTrans (constFmor (inT ∘ ET.to-terminal) ∘N colim 𝟙F .cocone)
                        (constFmor (id _) ∘N colim 𝟙F .cocone)
        eq .transf-eq u =
          begin
            (inT ∘ ET.to-terminal) ∘ colim 𝟙F .cocone .transf u
          ≈⟨ assoc _ _ _ ⟩
            inT ∘ (ET.to-terminal ∘ colim 𝟙F .cocone .transf u)
          ≈⟨ ∘-cong ≈-refl (ET.to-terminal-unique _ (id _)) ⟩
            inT ∘ id _
          ≈⟨ id-right ⟩
            inT
          ≈˘⟨ id-left ⟩
            id _ ∘ colim 𝟙F .cocone .transf u
          ∎ where open ≈-Reasoning isEquiv

  realise-terminal : IsTerminal ℰ (realise .fobj 𝟙F)
  realise-terminal .IsTerminal.to-terminal = inT ∘ ET.to-terminal
  realise-terminal .IsTerminal.to-terminal-ext f =
    begin
      inT ∘ ET.to-terminal
    ≈⟨ ∘-cong ≈-refl (ET.to-terminal-ext (ET.to-terminal ∘ f)) ⟩
      inT ∘ (ET.to-terminal ∘ f)
    ≈˘⟨ assoc _ _ _ ⟩
      (inT ∘ ET.to-terminal) ∘ f
    ≈⟨ ∘-cong roundtrip ≈-refl ⟩
      id _ ∘ f
    ≈⟨ id-left ⟩
      f
    ∎ where open ≈-Reasoning isEquiv

-- Realisation preserves binary products, given products and exponentials on ℰ
-- (the exponentials supplying distributivity of products over the colimits).
module _ (EP : HasProducts ℰ) (EE : HasExponentials ℰ EP) where

  private
    module EP = HasProducts EP
    module PC = product-cocontinuity EP EE

    open fam.CategoryOfFamilies.products os es ℰ EP using (_⊗_)

  module _ (X Y : Category.obj cat) where

    private
      DX = fam→functor (X .fam)
      DY = fam→functor (Y .fam)
      D⊗ = fam→functor ((X ⊗ Y) .fam)
      R×R = EP.prod (realise .fobj X) (realise .fobj Y)

    prodCocone : NatTrans D⊗ (constF (setoid→category ((X ⊗ Y) .idx)) R×R)
    prodCocone .transf (i , j) = EP.prod-m (colim X .cocone .transf i) (colim Y .cocone .transf j)
    prodCocone .natural {i₁ , j₁} {i₂ , j₂} ⟪ ei ,ₚ ej ⟫ =
      begin
        id _ ∘ EP.prod-m (colim X .cocone .transf i₁) (colim Y .cocone .transf j₁)
      ≈⟨ id-left ⟩
        EP.prod-m (colim X .cocone .transf i₁) (colim Y .cocone .transf j₁)
      ≈⟨ EP.prod-m-cong (≈-trans (≈-sym id-left) (colim X .cocone .natural ⟪ ei ⟫))
                        (≈-trans (≈-sym id-left) (colim Y .cocone .natural ⟪ ej ⟫)) ⟩
        EP.prod-m (colim X .cocone .transf i₂ ∘ X .fam .subst ei) (colim Y .cocone .transf j₂ ∘ Y .fam .subst ej)
      ≈⟨ EP.prod-m-comp _ _ _ _ ⟩
        EP.prod-m (colim X .cocone .transf i₂) (colim Y .cocone .transf j₂) ∘ EP.prod-m (X .fam .subst ei) (Y .fam .subst ej)
      ∎ where open ≈-Reasoning isEquiv

    private
      -- Restrict a cocone on the total diagram to the fibre at i.
      restr : ∀ x (α : NatTrans D⊗ (constF (setoid→category ((X ⊗ Y) .idx)) x)) i →
              NatTrans (PC.B×D' (X .fam .fm i) DY (colim Y)) (constF (setoid→category (Y .idx)) x)
      restr x α i .transf j = α .transf (i , j)
      restr x α i .natural {j₁} {j₂} ⟪ e ⟫ =
        begin
          id _ ∘ α .transf (i , j₁)
        ≈⟨ α .natural ⟪ X .idx .Setoid.refl ,ₚ e ⟫ ⟩
          α .transf (i , j₂) ∘ EP.prod-m (X .fam .subst (X .idx .Setoid.refl)) (Y .fam .subst e)
        ≈⟨ ∘-cong ≈-refl (EP.prod-m-cong (X .fam .refl*) ≈-refl) ⟩
          α .transf (i , j₂) ∘ EP.prod-m (id _) (Y .fam .subst e)
        ∎ where open ≈-Reasoning isEquiv

      -- Mediate each fibre through the left-handed cocontinuity of the product.
      inner : ∀ x α i → Category._⇒_ ℰ (EP.prod (X .fam .fm i) (realise .fobj Y)) x
      inner x α i = PC.B×-preserves-colimit (X .fam .fm i) DY (colim Y) .colambda x (restr x α i)

      eq₁ : ∀ x α i₁ i₂ (e : X .idx .Setoid._≈_ i₁ i₂) →
            ≃-NatTrans (constFmor (inner x α i₁) ∘N PC.B×-cocone (X .fam .fm i₁) DY (colim Y))
                       (constFmor (inner x α i₂ ∘ EP.prod-m (X .fam .subst e) (id _)) ∘N PC.B×-cocone (X .fam .fm i₁) DY (colim Y))
      eq₁ x α i₁ i₂ e .transf-eq j =
        begin
          inner x α i₁ ∘ EP.prod-m (id _) (colim Y .cocone .transf j)
        ≈⟨ PC.B×-preserves-colimit _ DY (colim Y) .colambda-coeval x (restr x α i₁) .transf-eq j ⟩
          α .transf (i₁ , j)
        ≈⟨ ≈-trans (≈-sym id-left) (α .natural ⟪ e ,ₚ Y .idx .Setoid.refl ⟫) ⟩
          α .transf (i₂ , j) ∘ EP.prod-m (X .fam .subst e) (Y .fam .subst (Y .idx .Setoid.refl))
        ≈⟨ ∘-cong ≈-refl (EP.prod-m-cong ≈-refl (Y .fam .refl*)) ⟩
          α .transf (i₂ , j) ∘ EP.prod-m (X .fam .subst e) (id _)
        ≈˘⟨ ∘-cong (PC.B×-preserves-colimit _ DY (colim Y) .colambda-coeval x (restr x α i₂) .transf-eq j) ≈-refl ⟩
          (inner x α i₂ ∘ EP.prod-m (id _) (colim Y .cocone .transf j)) ∘ EP.prod-m (X .fam .subst e) (id _)
        ≈⟨ assoc _ _ _ ⟩
          inner x α i₂ ∘ (EP.prod-m (id _) (colim Y .cocone .transf j) ∘ EP.prod-m (X .fam .subst e) (id _))
        ≈˘⟨ ∘-cong ≈-refl (EP.prod-m-comp _ _ _ _) ⟩
          inner x α i₂ ∘ EP.prod-m (id _ ∘ X .fam .subst e) (colim Y .cocone .transf j ∘ id _)
        ≈⟨ ∘-cong ≈-refl (EP.prod-m-cong (≈-trans id-left (≈-sym id-right)) (≈-trans id-right (≈-sym id-left))) ⟩
          inner x α i₂ ∘ EP.prod-m (X .fam .subst e ∘ id _) (id _ ∘ colim Y .cocone .transf j)
        ≈⟨ ∘-cong ≈-refl (EP.prod-m-comp _ _ _ _) ⟩
          inner x α i₂ ∘ (EP.prod-m (X .fam .subst e) (id _) ∘ EP.prod-m (id _) (colim Y .cocone .transf j))
        ≈˘⟨ assoc _ _ _ ⟩
          (inner x α i₂ ∘ EP.prod-m (X .fam .subst e) (id _)) ∘ EP.prod-m (id _) (colim Y .cocone .transf j)
        ∎ where open ≈-Reasoning isEquiv

      -- The fibrewise mediators form a cocone on the X-side diagram.
      outer : ∀ x α → NatTrans (PC.D×B DX (realise .fobj Y) (colim X)) (constF (setoid→category (X .idx)) x)
      outer x α .transf i = inner x α i
      outer x α .natural {i₁} {i₂} ⟪ e ⟫ =
        begin
          id _ ∘ inner x α i₁
        ≈⟨ id-left ⟩
          inner x α i₁
        ≈˘⟨ PC.B×-preserves-colimit _ DY (colim Y) .colambda-ext x (inner x α i₁) ⟩
          PC.B×-preserves-colimit _ DY (colim Y) .colambda x (constFmor (inner x α i₁) ∘N PC.B×-cocone _ DY (colim Y))
        ≈⟨ PC.B×-preserves-colimit _ DY (colim Y) .colambda-cong (eq₁ x α i₁ i₂ e) ⟩
          PC.B×-preserves-colimit _ DY (colim Y) .colambda x
            (constFmor (inner x α i₂ ∘ EP.prod-m (X .fam .subst e) (id _)) ∘N PC.B×-cocone _ DY (colim Y))
        ≈⟨ PC.B×-preserves-colimit _ DY (colim Y) .colambda-ext x _ ⟩
          inner x α i₂ ∘ EP.prod-m (X .fam .subst e) (id _)
        ∎ where open ≈-Reasoning isEquiv

    realise-preserves-products : IsColimit D⊗ R×R prodCocone
    realise-preserves-products .colambda x α =
      PC.×B-preserves-colimit DX (realise .fobj Y) (colim X) .colambda x (outer x α)
    realise-preserves-products .colambda-cong {x} {α} {β} α≃β =
      PC.×B-preserves-colimit DX (realise .fobj Y) (colim X) .colambda-cong eq
      where
        eq : ≃-NatTrans (outer x α) (outer x β)
        eq .transf-eq i =
          PC.B×-preserves-colimit _ DY (colim Y) .colambda-cong eq'
          where
            eq' : ≃-NatTrans (restr x α i) (restr x β i)
            eq' .transf-eq j = α≃β .transf-eq (i , j)
    realise-preserves-products .colambda-coeval x α .transf-eq (i , j) =
      begin
        realise-preserves-products .colambda x α ∘ EP.prod-m (colim X .cocone .transf i) (colim Y .cocone .transf j)
      ≈⟨ ∘-cong ≈-refl (≈-trans (EP.prod-m-cong (≈-sym id-right) (≈-sym id-left)) (EP.prod-m-comp _ _ _ _)) ⟩
        realise-preserves-products .colambda x α ∘ (EP.prod-m (colim X .cocone .transf i) (id _) ∘ EP.prod-m (id _) (colim Y .cocone .transf j))
      ≈˘⟨ assoc _ _ _ ⟩
        (realise-preserves-products .colambda x α ∘ EP.prod-m (colim X .cocone .transf i) (id _)) ∘ EP.prod-m (id _) (colim Y .cocone .transf j)
      ≈⟨ ∘-cong (PC.×B-preserves-colimit DX (realise .fobj Y) (colim X) .colambda-coeval x (outer x α) .transf-eq i) ≈-refl ⟩
        inner x α i ∘ EP.prod-m (id _) (colim Y .cocone .transf j)
      ≈⟨ PC.B×-preserves-colimit _ DY (colim Y) .colambda-coeval x (restr x α i) .transf-eq j ⟩
        α .transf (i , j)
      ∎ where open ≈-Reasoning isEquiv
    realise-preserves-products .colambda-ext x f =
      ≈-trans
        (PC.×B-preserves-colimit DX (realise .fobj Y) (colim X) .colambda-cong eq)
        (PC.×B-preserves-colimit DX (realise .fobj Y) (colim X) .colambda-ext x f)
      where
        eq : ≃-NatTrans (outer x (constFmor f ∘N prodCocone))
                        (constFmor f ∘N PC.×B-cocone DX (realise .fobj Y) (colim X))
        eq .transf-eq i =
          ≈-trans (PC.B×-preserves-colimit _ DY (colim Y) .colambda-cong eq')
            (PC.B×-preserves-colimit _ DY (colim Y) .colambda-ext x (f ∘ EP.prod-m (colim X .cocone .transf i) (id _)))
          where
            eq' : ≃-NatTrans (restr x (constFmor f ∘N prodCocone) i)
                             (constFmor (f ∘ EP.prod-m (colim X .cocone .transf i) (id _)) ∘N PC.B×-cocone (X .fam .fm i) DY (colim Y))
            eq' .transf-eq j =
              begin
                f ∘ EP.prod-m (colim X .cocone .transf i) (colim Y .cocone .transf j)
              ≈⟨ ∘-cong ≈-refl (≈-trans (EP.prod-m-cong (≈-sym id-right) (≈-sym id-left)) (EP.prod-m-comp _ _ _ _)) ⟩
                f ∘ (EP.prod-m (colim X .cocone .transf i) (id _) ∘ EP.prod-m (id _) (colim Y .cocone .transf j))
              ≈˘⟨ assoc _ _ _ ⟩
                (f ∘ EP.prod-m (colim X .cocone .transf i) (id _)) ∘ EP.prod-m (id _) (colim Y .cocone .transf j)
              ∎ where open ≈-Reasoning isEquiv

    -- The two colimits of the total diagram are canonically isomorphic.
    realise-products-iso : Category.Iso ℰ (realise .fobj (X ⊗ Y)) R×R
    realise-products-iso .Category.Iso.fwd =
      colim (X ⊗ Y) .isColimit .colambda _ prodCocone
    realise-products-iso .Category.Iso.bwd =
      realise-preserves-products .colambda _ (colim (X ⊗ Y) .cocone)
    realise-products-iso .Category.Iso.fwd∘bwd≈id =
      ≈-trans (≈-sym (realise-preserves-products .colambda-ext _ _))
        (≈-trans (realise-preserves-products .colambda-cong eq)
          (realise-preserves-products .colambda-ext _ (id _)))
      where
        eq : ≃-NatTrans
               (constFmor (colim (X ⊗ Y) .isColimit .colambda _ prodCocone ∘ realise-preserves-products .colambda _ (colim (X ⊗ Y) .cocone)) ∘N prodCocone)
               (constFmor (id _) ∘N prodCocone)
        eq .transf-eq (i , j) =
          begin
            (colim (X ⊗ Y) .isColimit .colambda _ prodCocone ∘ realise-preserves-products .colambda _ (colim (X ⊗ Y) .cocone)) ∘ prodCocone .transf (i , j)
          ≈⟨ assoc _ _ _ ⟩
            colim (X ⊗ Y) .isColimit .colambda _ prodCocone ∘ (realise-preserves-products .colambda _ (colim (X ⊗ Y) .cocone) ∘ prodCocone .transf (i , j))
          ≈⟨ ∘-cong ≈-refl (realise-preserves-products .colambda-coeval _ (colim (X ⊗ Y) .cocone) .transf-eq (i , j)) ⟩
            colim (X ⊗ Y) .isColimit .colambda _ prodCocone ∘ colim (X ⊗ Y) .cocone .transf (i , j)
          ≈⟨ colim (X ⊗ Y) .isColimit .colambda-coeval _ prodCocone .transf-eq (i , j) ⟩
            prodCocone .transf (i , j)
          ≈˘⟨ id-left ⟩
            id _ ∘ prodCocone .transf (i , j)
          ∎ where open ≈-Reasoning isEquiv
    realise-products-iso .Category.Iso.bwd∘fwd≈id =
      ≈-trans (≈-sym (colim (X ⊗ Y) .isColimit .colambda-ext _ _))
        (≈-trans (colim (X ⊗ Y) .isColimit .colambda-cong eq)
          (colim (X ⊗ Y) .isColimit .colambda-ext _ (id _)))
      where
        eq : ≃-NatTrans
               (constFmor (realise-preserves-products .colambda _ (colim (X ⊗ Y) .cocone) ∘ colim (X ⊗ Y) .isColimit .colambda _ prodCocone) ∘N colim (X ⊗ Y) .cocone)
               (constFmor (id _) ∘N colim (X ⊗ Y) .cocone)
        eq .transf-eq (i , j) =
          begin
            (realise-preserves-products .colambda _ (colim (X ⊗ Y) .cocone) ∘ colim (X ⊗ Y) .isColimit .colambda _ prodCocone) ∘ colim (X ⊗ Y) .cocone .transf (i , j)
          ≈⟨ assoc _ _ _ ⟩
            realise-preserves-products .colambda _ (colim (X ⊗ Y) .cocone) ∘ (colim (X ⊗ Y) .isColimit .colambda _ prodCocone ∘ colim (X ⊗ Y) .cocone .transf (i , j))
          ≈⟨ ∘-cong ≈-refl (colim (X ⊗ Y) .isColimit .colambda-coeval _ prodCocone .transf-eq (i , j)) ⟩
            realise-preserves-products .colambda _ (colim (X ⊗ Y) .cocone) ∘ prodCocone .transf (i , j)
          ≈⟨ realise-preserves-products .colambda-coeval _ (colim (X ⊗ Y) .cocone) .transf-eq (i , j) ⟩
            colim (X ⊗ Y) .cocone .transf (i , j)
          ≈˘⟨ id-left ⟩
            id _ ∘ colim (X ⊗ Y) .cocone .transf (i , j)
          ∎ where open ≈-Reasoning isEquiv
