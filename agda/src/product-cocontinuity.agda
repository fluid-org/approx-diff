{-# OPTIONS --prop --postfix-projections --safe #-}

-- Products preserve colimits in the presence of exponentials: (− × B) is left
-- adjoint to exp B −, so the product of a colimit with a fixed object is again
-- a colimit.

open import prop-setoid using (module ≈-Reasoning)
open import categories using (Category; HasProducts; HasExponentials)
open import functor
  using (Functor; Colimit; IsColimit; NatTrans; constF; constFmor; ≃-NatTrans)
  renaming (_∘_ to _∘N_)

module product-cocontinuity
  {o m e} {𝒞 : Category o m e} (P : HasProducts 𝒞) (E : HasExponentials 𝒞 P)
  where

open Category 𝒞
private
  module P = HasProducts P
  module E = HasExponentials E
open Functor
open NatTrans
open ≃-NatTrans
open Colimit
open IsColimit

module _ {o₁ m₁ e₁} {𝒮 : Category o₁ m₁ e₁} (D : Functor 𝒮 𝒞) (B : obj) (C : Colimit D) where

  D×B : Functor 𝒮 𝒞
  D×B .fobj s = P.prod (D .fobj s) B
  D×B .fmor f = P.prod-m (D .fmor f) (id _)
  D×B .fmor-cong e = P.prod-m-cong (D .fmor-cong e) ≈-refl
  D×B .fmor-id = ≈-trans (P.prod-m-cong (D .fmor-id) ≈-refl) P.prod-m-id
  D×B .fmor-comp f g =
    ≈-trans (P.prod-m-cong (D .fmor-comp f g) (≈-sym id-left)) (P.prod-m-comp _ _ _ _)

  ×B-cocone : NatTrans D×B (constF 𝒮 (P.prod (C .apex) B))
  ×B-cocone .transf s = P.prod-m (C .cocone .transf s) (id _)
  ×B-cocone .natural {s₁} {s₂} f =
    begin
      id _ ∘ P.prod-m (C .cocone .transf s₁) (id _)
    ≈⟨ id-left ⟩
      P.prod-m (C .cocone .transf s₁) (id _)
    ≈⟨ P.prod-m-cong (≈-trans (≈-sym id-left) (C .cocone .natural f)) (≈-sym id-left) ⟩
      P.prod-m (C .cocone .transf s₂ ∘ D .fmor f) (id _ ∘ id _)
    ≈⟨ P.prod-m-comp _ _ _ _ ⟩
      P.prod-m (C .cocone .transf s₂) (id _) ∘ P.prod-m (D .fmor f) (id _)
    ∎ where open ≈-Reasoning isEquiv

  private
    -- Transpose a cocone on D×B to a cocone on D.
    curry : ∀ x → NatTrans D×B (constF 𝒮 x) → NatTrans D (constF 𝒮 (E.exp B x))
    curry x α .transf s = E.lambda (α .transf s)
    curry x α .natural {s₁} {s₂} f =
      begin
        id _ ∘ E.lambda (α .transf s₁)
      ≈⟨ id-left ⟩
        E.lambda (α .transf s₁)
      ≈⟨ E.lambda-cong (≈-trans (≈-sym id-left) (α .natural f)) ⟩
        E.lambda (α .transf s₂ ∘ P.prod-m (D .fmor f) (id _))
      ≈˘⟨ E.lambda-natural _ _ ⟩
        E.lambda (α .transf s₂) ∘ D .fmor f
      ∎ where open ≈-Reasoning isEquiv

  ×B-preserves-colimit : IsColimit D×B (P.prod (C .apex) B) ×B-cocone
  ×B-preserves-colimit .colambda x α =
    E.eval ∘ P.prod-m (C .isColimit .colambda (E.exp B x) (curry x α)) (id _)
  ×B-preserves-colimit .colambda-cong {x} {α} {β} α≃β =
    ∘-cong ≈-refl (P.prod-m-cong (C .isColimit .colambda-cong eq) ≈-refl)
    where
      eq : ≃-NatTrans (curry x α) (curry x β)
      eq .transf-eq s = E.lambda-cong (α≃β .transf-eq s)
  ×B-preserves-colimit .colambda-coeval x α .transf-eq s =
    begin
      (E.eval ∘ P.prod-m (C .isColimit .colambda _ (curry x α)) (id _)) ∘ P.prod-m (C .cocone .transf s) (id _)
    ≈⟨ assoc _ _ _ ⟩
      E.eval ∘ (P.prod-m (C .isColimit .colambda _ (curry x α)) (id _) ∘ P.prod-m (C .cocone .transf s) (id _))
    ≈˘⟨ ∘-cong ≈-refl (P.prod-m-comp _ _ _ _) ⟩
      E.eval ∘ P.prod-m (C .isColimit .colambda _ (curry x α) ∘ C .cocone .transf s) (id _ ∘ id _)
    ≈⟨ ∘-cong ≈-refl (P.prod-m-cong (C .isColimit .colambda-coeval _ (curry x α) .transf-eq s) id-left) ⟩
      E.eval ∘ P.prod-m (E.lambda (α .transf s)) (id _)
    ≈⟨ E.eval-lambda _ ⟩
      α .transf s
    ∎ where open ≈-Reasoning isEquiv
  ×B-preserves-colimit .colambda-ext x f =
    begin
      E.eval ∘ P.prod-m (C .isColimit .colambda _ (curry x (constFmor f ∘N ×B-cocone))) (id _)
    ≈⟨ ∘-cong ≈-refl (P.prod-m-cong (C .isColimit .colambda-cong eq) ≈-refl) ⟩
      E.eval ∘ P.prod-m (C .isColimit .colambda _ (constFmor (E.lambda f) ∘N C .cocone)) (id _)
    ≈⟨ ∘-cong ≈-refl (P.prod-m-cong (C .isColimit .colambda-ext _ (E.lambda f)) ≈-refl) ⟩
      E.eval ∘ P.prod-m (E.lambda f) (id _)
    ≈⟨ E.eval-lambda _ ⟩
      f
    ∎
    where
      eq : ≃-NatTrans (curry x (constFmor f ∘N ×B-cocone)) (constFmor (E.lambda f) ∘N C .cocone)
      eq .transf-eq s = ≈-sym (E.lambda-natural (C .cocone .transf s) f)

      open ≈-Reasoning isEquiv

-- The left-handed variant: (B × −) preserves colimits, by transposing through
-- the symmetry of the product.
module _ {o₁ m₁ e₁} {𝒮 : Category o₁ m₁ e₁} (B : obj) (D : Functor 𝒮 𝒞) (C : Colimit D) where

  B×D' : Functor 𝒮 𝒞
  B×D' .fobj s = P.prod B (D .fobj s)
  B×D' .fmor f = P.prod-m (id _) (D .fmor f)
  B×D' .fmor-cong e = P.prod-m-cong ≈-refl (D .fmor-cong e)
  B×D' .fmor-id = ≈-trans (P.prod-m-cong ≈-refl (D .fmor-id)) P.prod-m-id
  B×D' .fmor-comp f g =
    ≈-trans (P.prod-m-cong (≈-sym id-left) (D .fmor-comp f g)) (P.prod-m-comp _ _ _ _)

  private
    swapN : ∀ x → NatTrans B×D' (constF 𝒮 x) → NatTrans (D×B D B C) (constF 𝒮 x)
    swapN x α .transf s = α .transf s ∘ P.swap
    swapN x α .natural {s₁} {s₂} f =
      begin
        id _ ∘ (α .transf s₁ ∘ P.swap)
      ≈˘⟨ assoc _ _ _ ⟩
        (id _ ∘ α .transf s₁) ∘ P.swap
      ≈⟨ ∘-cong (α .natural f) ≈-refl ⟩
        (α .transf s₂ ∘ P.prod-m (id _) (D .fmor f)) ∘ P.swap
      ≈⟨ assoc _ _ _ ⟩
        α .transf s₂ ∘ (P.prod-m (id _) (D .fmor f) ∘ P.swap)
      ≈˘⟨ ∘-cong ≈-refl (P.swap-natural _ _) ⟩
        α .transf s₂ ∘ (P.swap ∘ P.prod-m (D .fmor f) (id _))
      ≈˘⟨ assoc _ _ _ ⟩
        (α .transf s₂ ∘ P.swap) ∘ P.prod-m (D .fmor f) (id _)
      ∎ where open ≈-Reasoning isEquiv

  B×-cocone : NatTrans B×D' (constF 𝒮 (P.prod B (C .apex)))
  B×-cocone .transf s = P.prod-m (id _) (C .cocone .transf s)
  B×-cocone .natural {s₁} {s₂} f =
    begin
      id _ ∘ P.prod-m (id _) (C .cocone .transf s₁)
    ≈⟨ id-left ⟩
      P.prod-m (id _) (C .cocone .transf s₁)
    ≈⟨ P.prod-m-cong (≈-sym id-left) (≈-trans (≈-sym id-left) (C .cocone .natural f)) ⟩
      P.prod-m (id _ ∘ id _) (C .cocone .transf s₂ ∘ D .fmor f)
    ≈⟨ P.prod-m-comp _ _ _ _ ⟩
      P.prod-m (id _) (C .cocone .transf s₂) ∘ P.prod-m (id _) (D .fmor f)
    ∎ where open ≈-Reasoning isEquiv

  B×-preserves-colimit : IsColimit B×D' (P.prod B (C .apex)) B×-cocone
  B×-preserves-colimit .colambda x α =
    ×B-preserves-colimit D B C .colambda x (swapN x α) ∘ P.swap
  B×-preserves-colimit .colambda-cong {x} {α} {β} α≃β =
    ∘-cong (×B-preserves-colimit D B C .colambda-cong eq) ≈-refl
    where
      eq : ≃-NatTrans (swapN x α) (swapN x β)
      eq .transf-eq s = ∘-cong (α≃β .transf-eq s) ≈-refl
  B×-preserves-colimit .colambda-coeval x α .transf-eq s =
    begin
      (×B-preserves-colimit D B C .colambda x (swapN x α) ∘ P.swap) ∘ P.prod-m (id _) (C .cocone .transf s)
    ≈⟨ assoc _ _ _ ⟩
      ×B-preserves-colimit D B C .colambda x (swapN x α) ∘ (P.swap ∘ P.prod-m (id _) (C .cocone .transf s))
    ≈⟨ ∘-cong ≈-refl (P.swap-natural _ _) ⟩
      ×B-preserves-colimit D B C .colambda x (swapN x α) ∘ (P.prod-m (C .cocone .transf s) (id _) ∘ P.swap)
    ≈˘⟨ assoc _ _ _ ⟩
      (×B-preserves-colimit D B C .colambda x (swapN x α) ∘ P.prod-m (C .cocone .transf s) (id _)) ∘ P.swap
    ≈⟨ ∘-cong (×B-preserves-colimit D B C .colambda-coeval x (swapN x α) .transf-eq s) ≈-refl ⟩
      (α .transf s ∘ P.swap) ∘ P.swap
    ≈⟨ assoc _ _ _ ⟩
      α .transf s ∘ (P.swap ∘ P.swap)
    ≈⟨ ∘-cong ≈-refl P.swap-involutive ⟩
      α .transf s ∘ id _
    ≈⟨ id-right ⟩
      α .transf s
    ∎ where open ≈-Reasoning isEquiv
  B×-preserves-colimit .colambda-ext x f =
    begin
      ×B-preserves-colimit D B C .colambda x (swapN x (constFmor f ∘N B×-cocone)) ∘ P.swap
    ≈⟨ ∘-cong (×B-preserves-colimit D B C .colambda-cong eq) ≈-refl ⟩
      ×B-preserves-colimit D B C .colambda x (constFmor (f ∘ P.swap) ∘N ×B-cocone D B C) ∘ P.swap
    ≈⟨ ∘-cong (×B-preserves-colimit D B C .colambda-ext x (f ∘ P.swap)) ≈-refl ⟩
      (f ∘ P.swap) ∘ P.swap
    ≈⟨ assoc _ _ _ ⟩
      f ∘ (P.swap ∘ P.swap)
    ≈⟨ ∘-cong ≈-refl P.swap-involutive ⟩
      f ∘ id _
    ≈⟨ id-right ⟩
      f
    ∎
    where
      open ≈-Reasoning isEquiv

      eq : ≃-NatTrans (swapN x (constFmor f ∘N B×-cocone)) (constFmor (f ∘ P.swap) ∘N ×B-cocone D B C)
      eq .transf-eq s =
        ≈-trans (assoc _ _ _)
          (≈-trans (∘-cong ≈-refl (≈-sym (P.swap-natural (C .cocone .transf s) (id B))))
            (≈-sym (assoc _ _ _)))
