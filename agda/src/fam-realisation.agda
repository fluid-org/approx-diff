{-# OPTIONS --prop --postfix-projections --safe #-}

-- Realisation of a family as the set-indexed coproduct of its fibres: the
-- counit of the free coproduct completion, for a category with setoid-indexed
-- colimits.

open import Level using (Level; lift)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import prop using (⟪_⟫) renaming (_,_ to _,ₚ_)
open import prop-setoid using (Setoid; IsEquivalence; 𝟙; to-𝟙; module ≈-Reasoning)
  renaming (_⇒_ to _⇒s_; _≃m_ to _≃s_)
open import categories using (Category; setoid→category; HasTerminal; IsTerminal; HasProducts; HasExponentials; HasCoproducts)
open import functor
  using (Functor; HasColimits; Colimit; IsColimit; NatTrans; constF; constFmor; ≃-NatTrans)
  renaming (_∘_ to _∘N_; _∘F_ to _∘F_)
open import indexed-family using (Fam; _⇒f_; fam→functor)
import fam
import product-cocontinuity

module fam-realisation {o m e} (os es : Level) {ℰ : Category o m e}
  (ℰC : ∀ (A : Setoid os es) → HasColimits (setoid→category A) ℰ)
  where

open Category ℰ
open fam.CategoryOfFamilies os es ℰ using (cat; Mor-∘; bigCoproducts; terminal; simple[_,_]; simplef[_,_]; coproducts)
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
  colim X = ℰC (X .idx) (fam→functor (X .fam))

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
module _ (ℰT : HasTerminal ℰ) where

  private
    module ℰT = HasTerminal ℰT

    𝟙F = terminal ℰT .HasTerminal.witness

    inT = colim 𝟙F .cocone .transf (lift tt)

    roundtrip : (inT ∘ ℰT.to-terminal) ≈ id (realise .fobj 𝟙F)
    roundtrip =
      ≈-trans (≈-sym (colim 𝟙F .isColimit .colambda-ext _ (inT ∘ ℰT.to-terminal)))
        (≈-trans (colim 𝟙F .isColimit .colambda-cong eq)
          (colim 𝟙F .isColimit .colambda-ext _ (id _)))
      where
        eq : ≃-NatTrans (constFmor (inT ∘ ℰT.to-terminal) ∘N colim 𝟙F .cocone)
                        (constFmor (id _) ∘N colim 𝟙F .cocone)
        eq .transf-eq u =
          begin
            (inT ∘ ℰT.to-terminal) ∘ colim 𝟙F .cocone .transf u
          ≈⟨ assoc _ _ _ ⟩
            inT ∘ (ℰT.to-terminal ∘ colim 𝟙F .cocone .transf u)
          ≈⟨ ∘-cong ≈-refl (ℰT.to-terminal-unique _ (id _)) ⟩
            inT ∘ id _
          ≈⟨ id-right ⟩
            inT
          ≈˘⟨ id-left ⟩
            id _ ∘ colim 𝟙F .cocone .transf u
          ∎ where open ≈-Reasoning isEquiv

  realise-terminal : IsTerminal ℰ (realise .fobj 𝟙F)
  realise-terminal .IsTerminal.to-terminal = inT ∘ ℰT.to-terminal
  realise-terminal .IsTerminal.to-terminal-ext f =
    begin
      inT ∘ ℰT.to-terminal
    ≈⟨ ∘-cong ≈-refl (ℰT.to-terminal-ext (ℰT.to-terminal ∘ f)) ⟩
      inT ∘ (ℰT.to-terminal ∘ f)
    ≈˘⟨ assoc _ _ _ ⟩
      (inT ∘ ℰT.to-terminal) ∘ f
    ≈⟨ ∘-cong roundtrip ≈-refl ⟩
      id _ ∘ f
    ≈⟨ id-left ⟩
      f
    ∎ where open ≈-Reasoning isEquiv

-- Realisation preserves binary products, given products and exponentials on ℰ
-- (the exponentials supplying distributivity of products over the colimits).
module _ (ℰP : HasProducts ℰ) (ℰE : HasExponentials ℰ ℰP) where

  private
    module ℰP = HasProducts ℰP
    module PC = product-cocontinuity ℰP ℰE

    open fam.CategoryOfFamilies.products os es ℰ ℰP using (_⊗_)

  module _ (X Y : Category.obj cat) where

    private
      DX = fam→functor (X .fam)
      DY = fam→functor (Y .fam)
      D⊗ = fam→functor ((X ⊗ Y) .fam)
      R×R = ℰP.prod (realise .fobj X) (realise .fobj Y)

    prodCocone : NatTrans D⊗ (constF (setoid→category ((X ⊗ Y) .idx)) R×R)
    prodCocone .transf (i , j) = ℰP.prod-m (colim X .cocone .transf i) (colim Y .cocone .transf j)
    prodCocone .natural {i₁ , j₁} {i₂ , j₂} ⟪ ei ,ₚ ej ⟫ =
      begin
        id _ ∘ ℰP.prod-m (colim X .cocone .transf i₁) (colim Y .cocone .transf j₁)
      ≈⟨ id-left ⟩
        ℰP.prod-m (colim X .cocone .transf i₁) (colim Y .cocone .transf j₁)
      ≈⟨ ℰP.prod-m-cong (≈-trans (≈-sym id-left) (colim X .cocone .natural ⟪ ei ⟫))
                        (≈-trans (≈-sym id-left) (colim Y .cocone .natural ⟪ ej ⟫)) ⟩
        ℰP.prod-m (colim X .cocone .transf i₂ ∘ X .fam .subst ei) (colim Y .cocone .transf j₂ ∘ Y .fam .subst ej)
      ≈⟨ ℰP.prod-m-comp _ _ _ _ ⟩
        ℰP.prod-m (colim X .cocone .transf i₂) (colim Y .cocone .transf j₂) ∘ ℰP.prod-m (X .fam .subst ei) (Y .fam .subst ej)
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
          α .transf (i , j₂) ∘ ℰP.prod-m (X .fam .subst (X .idx .Setoid.refl)) (Y .fam .subst e)
        ≈⟨ ∘-cong ≈-refl (ℰP.prod-m-cong (X .fam .refl*) ≈-refl) ⟩
          α .transf (i , j₂) ∘ ℰP.prod-m (id _) (Y .fam .subst e)
        ∎ where open ≈-Reasoning isEquiv

      -- Mediate each fibre through the left-handed cocontinuity of the product.
      inner : ∀ x α i → Category._⇒_ ℰ (ℰP.prod (X .fam .fm i) (realise .fobj Y)) x
      inner x α i = PC.B×-preserves-colimit (X .fam .fm i) DY (colim Y) .colambda x (restr x α i)

      eq₁ : ∀ x α i₁ i₂ (e : X .idx .Setoid._≈_ i₁ i₂) →
            ≃-NatTrans (constFmor (inner x α i₁) ∘N PC.B×-cocone (X .fam .fm i₁) DY (colim Y))
                       (constFmor (inner x α i₂ ∘ ℰP.prod-m (X .fam .subst e) (id _)) ∘N PC.B×-cocone (X .fam .fm i₁) DY (colim Y))
      eq₁ x α i₁ i₂ e .transf-eq j =
        begin
          inner x α i₁ ∘ ℰP.prod-m (id _) (colim Y .cocone .transf j)
        ≈⟨ PC.B×-preserves-colimit _ DY (colim Y) .colambda-coeval x (restr x α i₁) .transf-eq j ⟩
          α .transf (i₁ , j)
        ≈⟨ ≈-trans (≈-sym id-left) (α .natural ⟪ e ,ₚ Y .idx .Setoid.refl ⟫) ⟩
          α .transf (i₂ , j) ∘ ℰP.prod-m (X .fam .subst e) (Y .fam .subst (Y .idx .Setoid.refl))
        ≈⟨ ∘-cong ≈-refl (ℰP.prod-m-cong ≈-refl (Y .fam .refl*)) ⟩
          α .transf (i₂ , j) ∘ ℰP.prod-m (X .fam .subst e) (id _)
        ≈˘⟨ ∘-cong (PC.B×-preserves-colimit _ DY (colim Y) .colambda-coeval x (restr x α i₂) .transf-eq j) ≈-refl ⟩
          (inner x α i₂ ∘ ℰP.prod-m (id _) (colim Y .cocone .transf j)) ∘ ℰP.prod-m (X .fam .subst e) (id _)
        ≈⟨ assoc _ _ _ ⟩
          inner x α i₂ ∘ (ℰP.prod-m (id _) (colim Y .cocone .transf j) ∘ ℰP.prod-m (X .fam .subst e) (id _))
        ≈˘⟨ ∘-cong ≈-refl (ℰP.prod-m-comp _ _ _ _) ⟩
          inner x α i₂ ∘ ℰP.prod-m (id _ ∘ X .fam .subst e) (colim Y .cocone .transf j ∘ id _)
        ≈⟨ ∘-cong ≈-refl (ℰP.prod-m-cong (≈-trans id-left (≈-sym id-right)) (≈-trans id-right (≈-sym id-left))) ⟩
          inner x α i₂ ∘ ℰP.prod-m (X .fam .subst e ∘ id _) (id _ ∘ colim Y .cocone .transf j)
        ≈⟨ ∘-cong ≈-refl (ℰP.prod-m-comp _ _ _ _) ⟩
          inner x α i₂ ∘ (ℰP.prod-m (X .fam .subst e) (id _) ∘ ℰP.prod-m (id _) (colim Y .cocone .transf j))
        ≈˘⟨ assoc _ _ _ ⟩
          (inner x α i₂ ∘ ℰP.prod-m (X .fam .subst e) (id _)) ∘ ℰP.prod-m (id _) (colim Y .cocone .transf j)
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
            (constFmor (inner x α i₂ ∘ ℰP.prod-m (X .fam .subst e) (id _)) ∘N PC.B×-cocone _ DY (colim Y))
        ≈⟨ PC.B×-preserves-colimit _ DY (colim Y) .colambda-ext x _ ⟩
          inner x α i₂ ∘ ℰP.prod-m (X .fam .subst e) (id _)
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
        realise-preserves-products .colambda x α ∘ ℰP.prod-m (colim X .cocone .transf i) (colim Y .cocone .transf j)
      ≈⟨ ∘-cong ≈-refl (≈-trans (ℰP.prod-m-cong (≈-sym id-right) (≈-sym id-left)) (ℰP.prod-m-comp _ _ _ _)) ⟩
        realise-preserves-products .colambda x α ∘ (ℰP.prod-m (colim X .cocone .transf i) (id _) ∘ ℰP.prod-m (id _) (colim Y .cocone .transf j))
      ≈˘⟨ assoc _ _ _ ⟩
        (realise-preserves-products .colambda x α ∘ ℰP.prod-m (colim X .cocone .transf i) (id _)) ∘ ℰP.prod-m (id _) (colim Y .cocone .transf j)
      ≈⟨ ∘-cong (PC.×B-preserves-colimit DX (realise .fobj Y) (colim X) .colambda-coeval x (outer x α) .transf-eq i) ≈-refl ⟩
        inner x α i ∘ ℰP.prod-m (id _) (colim Y .cocone .transf j)
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
            (PC.B×-preserves-colimit _ DY (colim Y) .colambda-ext x (f ∘ ℰP.prod-m (colim X .cocone .transf i) (id _)))
          where
            eq' : ≃-NatTrans (restr x (constFmor f ∘N prodCocone) i)
                             (constFmor (f ∘ ℰP.prod-m (colim X .cocone .transf i) (id _)) ∘N PC.B×-cocone (X .fam .fm i) DY (colim Y))
            eq' .transf-eq j =
              begin
                f ∘ ℰP.prod-m (colim X .cocone .transf i) (colim Y .cocone .transf j)
              ≈⟨ ∘-cong ≈-refl (≈-trans (ℰP.prod-m-cong (≈-sym id-right) (≈-sym id-left)) (ℰP.prod-m-comp _ _ _ _)) ⟩
                f ∘ (ℰP.prod-m (colim X .cocone .transf i) (id _) ∘ ℰP.prod-m (id _) (colim Y .cocone .transf j))
              ≈˘⟨ assoc _ _ _ ⟩
                (f ∘ ℰP.prod-m (colim X .cocone .transf i) (id _)) ∘ ℰP.prod-m (id _) (colim Y .cocone .transf j)
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

-- The singleton embedding, right adjoint to realisation.
η : Functor ℰ cat
η .fobj A = simple[ 𝟙 , A ]
η .fmor f = simplef[ prop-setoid.idS _ , f ]
η .fmor-cong f₁≈f₂ .idxf-eq = prop-setoid.≃m-isEquivalence .IsEquivalence.refl
η .fmor-cong f₁≈f₂ .famf-eq .indexed-family._≃f_.transf-eq = ≈-trans id-left f₁≈f₂
η .fmor-id .idxf-eq = prop-setoid.≃m-isEquivalence .IsEquivalence.refl
η .fmor-id .famf-eq .indexed-family._≃f_.transf-eq = id-left
η .fmor-comp f g .idxf-eq = prop-setoid.to-𝟙-unique _ _
η .fmor-comp f g .famf-eq .indexed-family._≃f_.transf-eq = ≈-trans id-left (≈-sym id-left)

-- The counit: realising a singleton family collapses to the object itself.
module _ (A : Category.obj ℰ) where

  private
    ηA = η .fobj A

    flatten : NatTrans (fam→functor (ηA .fam)) (constF (setoid→category 𝟙) A)
    flatten .transf _ = id A
    flatten .natural _ = ≈-refl

  realise-η-iso : Category.Iso ℰ (realise .fobj ηA) A
  realise-η-iso .Category.Iso.fwd = colim ηA .isColimit .colambda A flatten
  realise-η-iso .Category.Iso.bwd = colim ηA .cocone .transf (lift tt)
  realise-η-iso .Category.Iso.fwd∘bwd≈id =
    ≈-trans (colim ηA .isColimit .colambda-coeval A flatten .transf-eq (lift tt)) ≈-refl
  realise-η-iso .Category.Iso.bwd∘fwd≈id =
    ≈-trans (≈-sym (colim ηA .isColimit .colambda-ext _ _))
      (≈-trans (colim ηA .isColimit .colambda-cong eq)
        (colim ηA .isColimit .colambda-ext _ (id _)))
    where
      eq : ≃-NatTrans
             (constFmor (colim ηA .cocone .transf (lift tt) ∘ colim ηA .isColimit .colambda A flatten) ∘N colim ηA .cocone)
             (constFmor (id _) ∘N colim ηA .cocone)
      eq .transf-eq u =
        begin
          (colim ηA .cocone .transf (lift tt) ∘ colim ηA .isColimit .colambda A flatten) ∘ colim ηA .cocone .transf u
        ≈⟨ assoc _ _ _ ⟩
          colim ηA .cocone .transf (lift tt) ∘ (colim ηA .isColimit .colambda A flatten ∘ colim ηA .cocone .transf u)
        ≈⟨ ∘-cong ≈-refl (colim ηA .isColimit .colambda-coeval A flatten .transf-eq u) ⟩
          colim ηA .cocone .transf (lift tt) ∘ id A
        ≈⟨ id-right ⟩
          colim ηA .cocone .transf (lift tt)
        ≈˘⟨ id-left ⟩
          id _ ∘ colim ηA .cocone .transf u
        ∎ where open ≈-Reasoning isEquiv

-- The adjunction realise ⊣ η, in transposition form.
module _ {W : Category.obj cat} {X : Category.obj ℰ} where

  transpose : Category._⇒_ cat W (η .fobj X) → Category._⇒_ ℰ (realise .fobj W) X
  transpose f = colim W .isColimit .colambda X cone
    where
      cone : NatTrans (fam→functor (W .fam)) (constF (setoid→category (W .idx)) X)
      cone .transf i = f .famf .transf i
      cone .natural {i₁} {i₂} ⟪ e ⟫ = ≈-sym (f .famf .natural e)

  untranspose : Category._⇒_ ℰ (realise .fobj W) X → Category._⇒_ cat W (η .fobj X)
  untranspose g .idxf = to-𝟙
  untranspose g .famf .transf i = g ∘ colim W .cocone .transf i
  untranspose g .famf .natural {i₁} {i₂} e =
    begin
      (g ∘ colim W .cocone .transf i₂) ∘ W .fam .subst e
    ≈⟨ assoc _ _ _ ⟩
      g ∘ (colim W .cocone .transf i₂ ∘ W .fam .subst e)
    ≈⟨ ∘-cong ≈-refl (≈-trans (≈-sym (colim W .cocone .natural ⟪ e ⟫)) id-left) ⟩
      g ∘ colim W .cocone .transf i₁
    ≈˘⟨ id-left ⟩
      id _ ∘ (g ∘ colim W .cocone .transf i₁)
    ∎ where open ≈-Reasoning isEquiv

  transpose-cong : ∀ {f₁ f₂ : Category._⇒_ cat W (η .fobj X)} →
                   Category._≈_ cat f₁ f₂ → transpose f₁ ≈ transpose f₂
  transpose-cong {f₁} {f₂} f₁≃f₂ = colim W .isColimit .colambda-cong eq
    where
      eq : ≃-NatTrans _ _
      eq .transf-eq i =
        ≈-trans (≈-sym id-left) (f₁≃f₂ .famf-eq .indexed-family._≃f_.transf-eq {i})

  untranspose-cong : ∀ {g₁ g₂ : Category._⇒_ ℰ (realise .fobj W) X} →
                     g₁ ≈ g₂ → Category._≈_ cat (untranspose g₁) (untranspose g₂)
  untranspose-cong g₁≈g₂ .idxf-eq = prop-setoid.to-𝟙-unique _ _
  untranspose-cong g₁≈g₂ .famf-eq .indexed-family._≃f_.transf-eq =
    ≈-trans id-left (∘-cong g₁≈g₂ ≈-refl)

  transpose-untranspose : ∀ (g : Category._⇒_ ℰ (realise .fobj W) X) →
                          transpose (untranspose g) ≈ g
  transpose-untranspose g =
    ≈-trans (colim W .isColimit .colambda-cong eq) (colim W .isColimit .colambda-ext _ g)
    where
      eq : ≃-NatTrans _ (constFmor g ∘N colim W .cocone)
      eq .transf-eq i = ≈-refl

  untranspose-transpose : ∀ (f : Category._⇒_ cat W (η .fobj X)) →
                          Category._≈_ cat (untranspose (transpose f)) f
  untranspose-transpose f .idxf-eq = prop-setoid.to-𝟙-unique _ _
  untranspose-transpose f .famf-eq .indexed-family._≃f_.transf-eq {i} =
    ≈-trans id-left (colim W .isColimit .colambda-coeval _ _ .transf-eq i)

-- Naturality of transposition in each argument.
transpose-natural₁ : ∀ {W' W : Category.obj cat} {X : Category.obj ℰ}
                     (f : Category._⇒_ cat W (η .fobj X)) (g : Category._⇒_ cat W' W) →
                     transpose (Mor-∘ f g) ≈ (transpose f ∘ realise .fmor g)
transpose-natural₁ {W'} {W} {X} f g =
  ≈-sym (≈-trans (≈-sym (colim W' .isColimit .colambda-ext _ _))
    (colim W' .isColimit .colambda-cong eq))
  where
    eq : ≃-NatTrans (constFmor (transpose f ∘ realise .fmor g) ∘N colim W' .cocone) _
    eq .transf-eq i =
      begin
        (transpose f ∘ realise .fmor g) ∘ colim W' .cocone .transf i
      ≈⟨ assoc _ _ _ ⟩
        transpose f ∘ (realise .fmor g ∘ colim W' .cocone .transf i)
      ≈⟨ ∘-cong ≈-refl (colim W' .isColimit .colambda-coeval _ (push g) .transf-eq i) ⟩
        transpose f ∘ (colim W .cocone .transf (g .idxf $s i) ∘ g .famf .transf i)
      ≈˘⟨ assoc _ _ _ ⟩
        (transpose f ∘ colim W .cocone .transf (g .idxf $s i)) ∘ g .famf .transf i
      ≈⟨ ∘-cong (colim W .isColimit .colambda-coeval _ _ .transf-eq (g .idxf $s i)) ≈-refl ⟩
        f .famf .transf (g .idxf $s i) ∘ g .famf .transf i
      ≈˘⟨ id-left ⟩
        id _ ∘ (f .famf .transf (g .idxf $s i) ∘ g .famf .transf i)
      ∎ where open ≈-Reasoning isEquiv

transpose-natural₂ : ∀ {W : Category.obj cat} {X Y : Category.obj ℰ}
                     (h : Category._⇒_ ℰ X Y) (f : Category._⇒_ cat W (η .fobj X)) →
                     transpose (Mor-∘ (η .fmor h) f) ≈ (h ∘ transpose f)
transpose-natural₂ {W} {X} {Y} h f =
  ≈-sym (≈-trans (≈-sym (colim W .isColimit .colambda-ext _ _))
    (colim W .isColimit .colambda-cong eq))
  where
    eq : ≃-NatTrans (constFmor (h ∘ transpose f) ∘N colim W .cocone) _
    eq .transf-eq i =
      begin
        (h ∘ transpose f) ∘ colim W .cocone .transf i
      ≈⟨ assoc _ _ _ ⟩
        h ∘ (transpose f ∘ colim W .cocone .transf i)
      ≈⟨ ∘-cong ≈-refl (colim W .isColimit .colambda-coeval _ _ .transf-eq i) ⟩
        h ∘ f .famf .transf i
      ≈˘⟨ id-left ⟩
        id _ ∘ (h ∘ f .famf .transf i)
      ∎ where open ≈-Reasoning isEquiv

-- Realisation preserves binary coproducts.
module _ (ℰCP : HasCoproducts ℰ) where

  private
    module ℰCP = HasCoproducts ℰCP
    module FC = HasCoproducts coproducts

  module _ (X Y : Category.obj cat) where

    private
      X⊕Y = FC.coprod X Y

      sumCone : NatTrans (fam→functor (X⊕Y .fam)) (constF (setoid→category (X⊕Y .idx)) (ℰCP.coprod (realise .fobj X) (realise .fobj Y)))
      sumCone .transf (inj₁ i) = ℰCP.in₁ ∘ colim X .cocone .transf i
      sumCone .transf (inj₂ j) = ℰCP.in₂ ∘ colim Y .cocone .transf j
      sumCone .natural {inj₁ i₁} {inj₁ i₂} ⟪ e ⟫ =
        begin
          id _ ∘ (ℰCP.in₁ ∘ colim X .cocone .transf i₁)
        ≈⟨ id-left ⟩
          ℰCP.in₁ ∘ colim X .cocone .transf i₁
        ≈⟨ ∘-cong ≈-refl (≈-trans (≈-sym id-left) (colim X .cocone .natural ⟪ e ⟫)) ⟩
          ℰCP.in₁ ∘ (colim X .cocone .transf i₂ ∘ X .fam .subst e)
        ≈˘⟨ assoc _ _ _ ⟩
          (ℰCP.in₁ ∘ colim X .cocone .transf i₂) ∘ X .fam .subst e
        ∎ where open ≈-Reasoning isEquiv
      sumCone .natural {inj₁ i₁} {inj₂ j₂} ⟪ () ⟫
      sumCone .natural {inj₂ j₁} {inj₁ i₂} ⟪ () ⟫
      sumCone .natural {inj₂ j₁} {inj₂ j₂} ⟪ e ⟫ =
        begin
          id _ ∘ (ℰCP.in₂ ∘ colim Y .cocone .transf j₁)
        ≈⟨ id-left ⟩
          ℰCP.in₂ ∘ colim Y .cocone .transf j₁
        ≈⟨ ∘-cong ≈-refl (≈-trans (≈-sym id-left) (colim Y .cocone .natural ⟪ e ⟫)) ⟩
          ℰCP.in₂ ∘ (colim Y .cocone .transf j₂ ∘ Y .fam .subst e)
        ≈˘⟨ assoc _ _ _ ⟩
          (ℰCP.in₂ ∘ colim Y .cocone .transf j₂) ∘ Y .fam .subst e
        ∎ where open ≈-Reasoning isEquiv

      fwd⊕ = colim X⊕Y .isColimit .colambda _ sumCone

      fwd-in₁ : (fwd⊕ ∘ realise .fmor FC.in₁) ≈ ℰCP.in₁
      fwd-in₁ =
        ≈-trans (≈-sym (colim X .isColimit .colambda-ext _ _))
          (≈-trans (colim X .isColimit .colambda-cong eq₁) (colim X .isColimit .colambda-ext _ ℰCP.in₁))
        where
          eq₁ : ≃-NatTrans _ _
          eq₁ .transf-eq i =
            begin
              (fwd⊕ ∘ realise .fmor FC.in₁) ∘ colim X .cocone .transf i
            ≈⟨ assoc _ _ _ ⟩
              fwd⊕ ∘ (realise .fmor FC.in₁ ∘ colim X .cocone .transf i)
            ≈⟨ ∘-cong ≈-refl (colim X .isColimit .colambda-coeval _ (push FC.in₁) .transf-eq i) ⟩
              fwd⊕ ∘ (colim X⊕Y .cocone .transf (inj₁ i) ∘ id _)
            ≈⟨ ∘-cong ≈-refl id-right ⟩
              fwd⊕ ∘ colim X⊕Y .cocone .transf (inj₁ i)
            ≈⟨ colim X⊕Y .isColimit .colambda-coeval _ sumCone .transf-eq (inj₁ i) ⟩
              ℰCP.in₁ ∘ colim X .cocone .transf i
            ∎ where open ≈-Reasoning isEquiv

      fwd-in₂ : (fwd⊕ ∘ realise .fmor FC.in₂) ≈ ℰCP.in₂
      fwd-in₂ =
        ≈-trans (≈-sym (colim Y .isColimit .colambda-ext _ _))
          (≈-trans (colim Y .isColimit .colambda-cong eq₂) (colim Y .isColimit .colambda-ext _ ℰCP.in₂))
        where
          eq₂ : ≃-NatTrans _ _
          eq₂ .transf-eq j =
            begin
              (fwd⊕ ∘ realise .fmor FC.in₂) ∘ colim Y .cocone .transf j
            ≈⟨ assoc _ _ _ ⟩
              fwd⊕ ∘ (realise .fmor FC.in₂ ∘ colim Y .cocone .transf j)
            ≈⟨ ∘-cong ≈-refl (colim Y .isColimit .colambda-coeval _ (push FC.in₂) .transf-eq j) ⟩
              fwd⊕ ∘ (colim X⊕Y .cocone .transf (inj₂ j) ∘ id _)
            ≈⟨ ∘-cong ≈-refl id-right ⟩
              fwd⊕ ∘ colim X⊕Y .cocone .transf (inj₂ j)
            ≈⟨ colim X⊕Y .isColimit .colambda-coeval _ sumCone .transf-eq (inj₂ j) ⟩
              ℰCP.in₂ ∘ colim Y .cocone .transf j
            ∎ where open ≈-Reasoning isEquiv

    realise-coproducts-iso : Category.Iso ℰ (realise .fobj X⊕Y) (ℰCP.coprod (realise .fobj X) (realise .fobj Y))
    realise-coproducts-iso .Category.Iso.fwd = fwd⊕
    realise-coproducts-iso .Category.Iso.bwd =
      ℰCP.copair (realise .fmor FC.in₁) (realise .fmor FC.in₂)
    realise-coproducts-iso .Category.Iso.fwd∘bwd≈id =
      begin
        fwd⊕ ∘ ℰCP.copair (realise .fmor FC.in₁) (realise .fmor FC.in₂)
      ≈⟨ ℰCP.copair-natural _ _ _ ⟩
        ℰCP.copair (fwd⊕ ∘ realise .fmor FC.in₁) (fwd⊕ ∘ realise .fmor FC.in₂)
      ≈⟨ ℰCP.copair-cong fwd-in₁ fwd-in₂ ⟩
        ℰCP.copair ℰCP.in₁ ℰCP.in₂
      ≈⟨ ≈-trans (ℰCP.copair-cong (≈-sym id-left) (≈-sym id-left)) (ℰCP.copair-ext (id _)) ⟩
        id _
      ∎ where open ≈-Reasoning isEquiv
    realise-coproducts-iso .Category.Iso.bwd∘fwd≈id =
      ≈-trans (≈-sym (colim X⊕Y .isColimit .colambda-ext _ _))
        (≈-trans (colim X⊕Y .isColimit .colambda-cong eq)
          (colim X⊕Y .isColimit .colambda-ext _ (id _)))
      where
        bwd⊕ = ℰCP.copair (realise .fmor FC.in₁) (realise .fmor FC.in₂)

        eq : ≃-NatTrans _ _
        eq .transf-eq (inj₁ i) =
          begin
            (bwd⊕ ∘ fwd⊕) ∘ colim X⊕Y .cocone .transf (inj₁ i)
          ≈⟨ assoc _ _ _ ⟩
            bwd⊕ ∘ (fwd⊕ ∘ colim X⊕Y .cocone .transf (inj₁ i))
          ≈⟨ ∘-cong ≈-refl (colim X⊕Y .isColimit .colambda-coeval _ sumCone .transf-eq (inj₁ i)) ⟩
            bwd⊕ ∘ (ℰCP.in₁ ∘ colim X .cocone .transf i)
          ≈˘⟨ assoc _ _ _ ⟩
            (bwd⊕ ∘ ℰCP.in₁) ∘ colim X .cocone .transf i
          ≈⟨ ∘-cong (ℰCP.copair-in₁ _ _) ≈-refl ⟩
            realise .fmor FC.in₁ ∘ colim X .cocone .transf i
          ≈⟨ colim X .isColimit .colambda-coeval _ (push FC.in₁) .transf-eq i ⟩
            colim X⊕Y .cocone .transf (inj₁ i) ∘ id _
          ≈⟨ id-right ⟩
            colim X⊕Y .cocone .transf (inj₁ i)
          ≈˘⟨ id-left ⟩
            id _ ∘ colim X⊕Y .cocone .transf (inj₁ i)
          ∎ where open ≈-Reasoning isEquiv
        eq .transf-eq (inj₂ j) =
          begin
            (bwd⊕ ∘ fwd⊕) ∘ colim X⊕Y .cocone .transf (inj₂ j)
          ≈⟨ assoc _ _ _ ⟩
            bwd⊕ ∘ (fwd⊕ ∘ colim X⊕Y .cocone .transf (inj₂ j))
          ≈⟨ ∘-cong ≈-refl (colim X⊕Y .isColimit .colambda-coeval _ sumCone .transf-eq (inj₂ j)) ⟩
            bwd⊕ ∘ (ℰCP.in₂ ∘ colim Y .cocone .transf j)
          ≈˘⟨ assoc _ _ _ ⟩
            (bwd⊕ ∘ ℰCP.in₂) ∘ colim Y .cocone .transf j
          ≈⟨ ∘-cong (ℰCP.copair-in₂ _ _) ≈-refl ⟩
            realise .fmor FC.in₂ ∘ colim Y .cocone .transf j
          ≈⟨ colim Y .isColimit .colambda-coeval _ (push FC.in₂) .transf-eq j ⟩
            colim X⊕Y .cocone .transf (inj₂ j) ∘ id _
          ≈⟨ id-right ⟩
            colim X⊕Y .cocone .transf (inj₂ j)
          ≈˘⟨ id-left ⟩
            id _ ∘ colim X⊕Y .cocone .transf (inj₂ j)
          ∎ where open ≈-Reasoning isEquiv
