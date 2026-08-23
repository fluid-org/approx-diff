{-# OPTIONS --prop --postfix-projections --safe #-}

-- Transporting a biproduct along an isomorphism on its first leg, and the naturality of the
-- canonical comparison with a chosen biproduct against maps built by copairing. Stated over an
-- abstract category so that instances at concrete categories whose objects lack eta need no
-- equational reasoning of their own.
-- FIXME: Not clear why this is its own module or whether this overlaps with something we already have.
-- Also that last comment about abstract category seems like noise. And the other comments here seem to be
-- assuming some context: "first leg", "this is the naturality a change of base needs", etc.
open import categories using (Category)
open import cmon-enriched using (CMonEnriched; Biproduct)
open import commutative-monoid using (CommutativeMonoid)
open import prop-setoid using (module ≈-Reasoning)

module biproduct-transport {o m e} {𝒞 : Category o m e} (CM : CMonEnriched 𝒞) where

open Category 𝒞
open CMonEnriched CM
open CommutativeMonoid
open Biproduct

-- FIXME: These would be better alongside the other generic biproduct facts.
pair-id-ε : ∀ {x y} (B : Biproduct CM x y) → Biproduct.pair B (id x) εm ≈ B .in₁
pair-id-ε B =
  ≈-trans (Biproduct.pair-cong B (≈-sym (B .id-1)) (≈-sym (B .zero-2)))
          (Biproduct.pair-ext B (B .in₁))

pair-ε-id : ∀ {x y} (B : Biproduct CM x y) → Biproduct.pair B εm (id y) ≈ B .in₂
pair-ε-id B =
  ≈-trans (Biproduct.pair-cong B (≈-sym (B .zero-1)) (≈-sym (B .id-2)))
          (Biproduct.pair-ext B (B .in₂))

bp-ext : ∀ {x y z} (B : Biproduct CM x y) {h k : Biproduct.prod B ⇒ z} →
         (h ∘ B .in₁) ≈ (k ∘ B .in₁) → (h ∘ B .in₂) ≈ (k ∘ B .in₂) → h ≈ k
bp-ext B {h} {k} e₁ e₂ =
  ≈-trans (≈-sym (Biproduct.copair-ext B h))
  (≈-trans (Biproduct.copair-cong B e₁ e₂) (Biproduct.copair-ext B k))

module _ {x x' y : obj} (B : Biproduct CM x y)
  (fwd : x ⇒ x') (bwd : x' ⇒ x)
  (fb : (fwd ∘ bwd) ≈ id x') (bf : (bwd ∘ fwd) ≈ id x)
  where

  transport₁ : Biproduct CM x' y
  transport₁ .prod = B .prod
  transport₁ .p₁ = fwd ∘ B .p₁
  transport₁ .p₂ = B .p₂
  transport₁ .in₁ = B .in₁ ∘ bwd
  transport₁ .in₂ = B .in₂
  transport₁ .id-1 = begin
      (fwd ∘ B .p₁) ∘ (B .in₁ ∘ bwd)   ≈⟨ assoc _ _ _ ⟩
      fwd ∘ (B .p₁ ∘ (B .in₁ ∘ bwd))   ≈˘⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
      fwd ∘ ((B .p₁ ∘ B .in₁) ∘ bwd)   ≈⟨ ∘-cong ≈-refl (∘-cong (B .id-1) ≈-refl) ⟩
      fwd ∘ (id _ ∘ bwd)               ≈⟨ ∘-cong ≈-refl id-left ⟩
      fwd ∘ bwd                        ≈⟨ fb ⟩
      id x'                            ∎
    where open ≈-Reasoning isEquiv
  transport₁ .id-2 = B .id-2
  transport₁ .zero-1 = begin
      (fwd ∘ B .p₁) ∘ B .in₂   ≈⟨ assoc _ _ _ ⟩
      fwd ∘ (B .p₁ ∘ B .in₂)   ≈⟨ ∘-cong ≈-refl (B .zero-1) ⟩
      fwd ∘ εm                 ≈⟨ comp-bilinear-ε₂ fwd ⟩
      εm                       ∎
    where open ≈-Reasoning isEquiv
  transport₁ .zero-2 = begin
      B .p₂ ∘ (B .in₁ ∘ bwd)   ≈˘⟨ assoc _ _ _ ⟩
      (B .p₂ ∘ B .in₁) ∘ bwd   ≈⟨ ∘-cong (B .zero-2) ≈-refl ⟩
      εm ∘ bwd                 ≈⟨ comp-bilinear-ε₁ bwd ⟩
      εm                       ∎
    where open ≈-Reasoning isEquiv
  transport₁ .id-+ = begin
      ((B .in₁ ∘ bwd) ∘ (fwd ∘ B .p₁)) +m (B .in₂ ∘ B .p₂)
    ≈⟨ homCM _ _ .+-cong middle ≈-refl ⟩
      (B .in₁ ∘ B .p₁) +m (B .in₂ ∘ B .p₂)
    ≈⟨ B .id-+ ⟩
      id _
    ∎
    where
    open ≈-Reasoning isEquiv
    middle : ((B .in₁ ∘ bwd) ∘ (fwd ∘ B .p₁)) ≈ (B .in₁ ∘ B .p₁)
    middle = begin
        (B .in₁ ∘ bwd) ∘ (fwd ∘ B .p₁)   ≈⟨ assoc _ _ _ ⟩
        B .in₁ ∘ (bwd ∘ (fwd ∘ B .p₁))   ≈˘⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
        B .in₁ ∘ ((bwd ∘ fwd) ∘ B .p₁)   ≈⟨ ∘-cong ≈-refl (∘-cong bf ≈-refl) ⟩
        B .in₁ ∘ (id _ ∘ B .p₁)          ≈⟨ ∘-cong ≈-refl id-left ⟩
        B .in₁ ∘ B .p₁                   ∎

module _ {x x' y y' : obj}
  (B  : Biproduct CM x y)  (B' : Biproduct CM x y')
  (C  : Biproduct CM x' y) (C' : Biproduct CM x' y')
  (fwd : x ⇒ x') (bwd : x' ⇒ x)
  (fb : (fwd ∘ bwd) ≈ id x') (bf : (bwd ∘ fwd) ≈ id x)
  (f : y ⇒ y')
  where

  private
    Bt  = transport₁ B fwd bwd fb bf
    Bt' = transport₁ B' fwd bwd fb bf

    φ : B .prod ⇒ C .prod
    φ = Biproduct.pair C (Bt .p₁) (Bt .p₂)

    φ' : B' .prod ⇒ C' .prod
    φ' = Biproduct.pair C' (Bt' .p₁) (Bt' .p₂)

    φ-in₁ : ∀ {z} (D : Biproduct CM x z) (E : Biproduct CM x' z)
            {ψ : D .prod ⇒ E .prod} → ψ ≈ Biproduct.pair E (fwd ∘ D .p₁) (D .p₂) →
            (ψ ∘ D .in₁) ≈ (E .in₁ ∘ fwd)
    φ-in₁ D E {ψ} eψ = begin
        ψ ∘ D .in₁
      ≈⟨ ∘-cong eψ ≈-refl ⟩
        Biproduct.pair E (fwd ∘ D .p₁) (D .p₂) ∘ D .in₁
      ≈⟨ Biproduct.pair-natural E _ _ _ ⟩
        Biproduct.pair E ((fwd ∘ D .p₁) ∘ D .in₁) (D .p₂ ∘ D .in₁)
      ≈⟨ Biproduct.pair-cong E
           (≈-trans (assoc _ _ _) (≈-trans (∘-cong ≈-refl (D .id-1)) id-right))
           (D .zero-2) ⟩
        Biproduct.pair E fwd εm
      ≈⟨ Biproduct.pair-cong E (≈-sym id-left) (≈-sym (comp-bilinear-ε₁ fwd)) ⟩
        Biproduct.pair E (id x' ∘ fwd) (εm ∘ fwd)
      ≈˘⟨ Biproduct.pair-natural E _ _ _ ⟩
        Biproduct.pair E (id x') εm ∘ fwd
      ≈⟨ ∘-cong (pair-id-ε E) ≈-refl ⟩
        E .in₁ ∘ fwd
      ∎
      where open ≈-Reasoning isEquiv

    φ-in₂ : ∀ {z} (D : Biproduct CM x z) (E : Biproduct CM x' z)
            {ψ : D .prod ⇒ E .prod} → ψ ≈ Biproduct.pair E (fwd ∘ D .p₁) (D .p₂) →
            (ψ ∘ D .in₂) ≈ E .in₂
    φ-in₂ D E {ψ} eψ = begin
        ψ ∘ D .in₂
      ≈⟨ ∘-cong eψ ≈-refl ⟩
        Biproduct.pair E (fwd ∘ D .p₁) (D .p₂) ∘ D .in₂
      ≈⟨ Biproduct.pair-natural E _ _ _ ⟩
        Biproduct.pair E ((fwd ∘ D .p₁) ∘ D .in₂) (D .p₂ ∘ D .in₂)
      ≈⟨ Biproduct.pair-cong E
           (≈-trans (assoc _ _ _) (≈-trans (∘-cong ≈-refl (D .zero-1)) (comp-bilinear-ε₂ fwd)))
           (D .id-2) ⟩
        Biproduct.pair E εm (id _)
      ≈⟨ pair-ε-id E ⟩
        E .in₂
      ∎
      where open ≈-Reasoning isEquiv

  compare-natural :
    (φ' ∘ Biproduct.copair B (B' .in₁) (B' .in₂ ∘ f))
      ≈ (Biproduct.copair C (C' .in₁) (C' .in₂ ∘ f) ∘ φ)
  compare-natural = bp-ext B leg₁ leg₂
    where
    M = Biproduct.copair B (B' .in₁) (B' .in₂ ∘ f)
    N = Biproduct.copair C (C' .in₁) (C' .in₂ ∘ f)

    leg₁ : ((φ' ∘ M) ∘ B .in₁) ≈ ((N ∘ φ) ∘ B .in₁)
    leg₁ = begin
        (φ' ∘ M) ∘ B .in₁
      ≈⟨ assoc _ _ _ ⟩
        φ' ∘ (M ∘ B .in₁)
      ≈⟨ ∘-cong ≈-refl (Biproduct.copair-in₁ B _ _) ⟩
        φ' ∘ B' .in₁
      ≈⟨ φ-in₁ B' C' ≈-refl ⟩
        C' .in₁ ∘ fwd
      ≈˘⟨ ∘-cong (Biproduct.copair-in₁ C _ _) ≈-refl ⟩
        (N ∘ C .in₁) ∘ fwd
      ≈⟨ assoc _ _ _ ⟩
        N ∘ (C .in₁ ∘ fwd)
      ≈˘⟨ ∘-cong ≈-refl (φ-in₁ B C ≈-refl) ⟩
        N ∘ (φ ∘ B .in₁)
      ≈˘⟨ assoc _ _ _ ⟩
        (N ∘ φ) ∘ B .in₁
      ∎
      where open ≈-Reasoning isEquiv

    leg₂ : ((φ' ∘ M) ∘ B .in₂) ≈ ((N ∘ φ) ∘ B .in₂)
    leg₂ = begin
        (φ' ∘ M) ∘ B .in₂
      ≈⟨ assoc _ _ _ ⟩
        φ' ∘ (M ∘ B .in₂)
      ≈⟨ ∘-cong ≈-refl (Biproduct.copair-in₂ B _ _) ⟩
        φ' ∘ (B' .in₂ ∘ f)
      ≈˘⟨ assoc _ _ _ ⟩
        (φ' ∘ B' .in₂) ∘ f
      ≈⟨ ∘-cong (φ-in₂ B' C' ≈-refl) ≈-refl ⟩
        C' .in₂ ∘ f
      ≈˘⟨ Biproduct.copair-in₂ C _ _ ⟩
        N ∘ C .in₂
      ≈˘⟨ ∘-cong ≈-refl (φ-in₂ B C ≈-refl) ⟩
        N ∘ (φ ∘ B .in₂)
      ≈˘⟨ assoc _ _ _ ⟩
        (N ∘ φ) ∘ B .in₂
      ∎
      where open ≈-Reasoning isEquiv
