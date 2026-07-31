{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (0ℓ)
open import prop-setoid using (Setoid; module ≈-Reasoning)
open import commutative-semiring using (CommutativeSemiring)
open import categories using (Category; Splitting)
open import functor using (Functor)
import matrix
import order-idempotent

-- Realise the order-idempotent category over a realisation 𝓖 of Mat(S): each order matrix becomes
-- an idempotent endomorphism of the realised object, and a chosen splitting of that idempotent
-- interprets the position order. Morphisms route through the splittings, so the functor laws are
-- absorption. Mirrors matrix-embedding, which realises Mat(S) itself.
module order-idempotent-embedding
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (let open CommutativeSemiring S hiding (_≈_; trans; sym; refl); open Setoid A)
  (∨-idem    : ∀ {x} → x + x ≈ x)
  (∧-idem    : ∀ {x} → x · x ≈ x)
  (⊤-add-top : ∀ {x} → ι + x ≈ ι)
  where

module OI = order-idempotent S ∨-idem ∧-idem ⊤-add-top
module MatS = matrix.Mat S

open OI using (Pos; dim; ord; mat; absorbed; absorb-left)
open Functor
open Splitting

module Embed
  {o m e} {𝒞 : Category o m e}
  (𝓖 : Functor MatS.cat 𝒞)
  (split : ∀ (P : Pos) → Splitting 𝒞 (𝓖 .fmor (P .ord)))
  where

  open Category 𝒞

  𝓚 : Functor OI.cat 𝒞
  𝓚 .fobj P = split P .witness
  𝓚 .fmor {P} {Q} f = split Q .retr ∘ (𝓖 .fmor (f .mat) ∘ split P .sect)
  𝓚 .fmor-cong f₁≈f₂ = ∘-cong ≈-refl (∘-cong (𝓖 .fmor-cong f₁≈f₂) ≈-refl)
  𝓚 .fmor-id {P} =
    begin
      split P .retr ∘ (𝓖 .fmor (P .ord) ∘ split P .sect)
    ≈˘⟨ ∘-cong ≈-refl (∘-cong (split P .sect-retr) ≈-refl) ⟩
      split P .retr ∘ ((split P .sect ∘ split P .retr) ∘ split P .sect)
    ≈⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
      split P .retr ∘ (split P .sect ∘ (split P .retr ∘ split P .sect))
    ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl (split P .retr-sect)) ⟩
      split P .retr ∘ (split P .sect ∘ id _)
    ≈⟨ ∘-cong ≈-refl id-right ⟩
      split P .retr ∘ split P .sect
    ≈⟨ split P .retr-sect ⟩
      id _
    ∎ where open ≈-Reasoning isEquiv
  𝓚 .fmor-comp {P} {Q} {R} g f =
    begin
      split R .retr ∘ (𝓖 .fmor (g .mat MatS.∘ f .mat) ∘ split P .sect)
    ≈˘⟨ ∘-cong ≈-refl (∘-cong (𝓖 .fmor-cong (MatS.∘-cong (OI.≈ₘ-refl {M = g .mat}) (absorb-left f))) ≈-refl) ⟩
      split R .retr ∘ (𝓖 .fmor (g .mat MatS.∘ (Q .ord MatS.∘ f .mat)) ∘ split P .sect)
    ≈⟨ ∘-cong ≈-refl (∘-cong (𝓖 .fmor-comp (g .mat) (Q .ord MatS.∘ f .mat)) ≈-refl) ⟩
      split R .retr ∘ ((𝓖 .fmor (g .mat) ∘ 𝓖 .fmor (Q .ord MatS.∘ f .mat)) ∘ split P .sect)
    ≈⟨ ∘-cong ≈-refl (∘-cong (∘-cong ≈-refl (𝓖 .fmor-comp (Q .ord) (f .mat))) ≈-refl) ⟩
      split R .retr ∘ ((𝓖 .fmor (g .mat) ∘ (𝓖 .fmor (Q .ord) ∘ 𝓖 .fmor (f .mat))) ∘ split P .sect)
    ≈˘⟨ ∘-cong ≈-refl (∘-cong (∘-cong ≈-refl (∘-cong (split Q .sect-retr) ≈-refl)) ≈-refl) ⟩
      split R .retr ∘ ((𝓖 .fmor (g .mat) ∘ ((split Q .sect ∘ split Q .retr) ∘ 𝓖 .fmor (f .mat))) ∘ split P .sect)
    ≈⟨ ∘-cong ≈-refl (∘-cong (∘-cong ≈-refl (assoc _ _ _)) ≈-refl) ⟩
      split R .retr ∘ ((𝓖 .fmor (g .mat) ∘ (split Q .sect ∘ (split Q .retr ∘ 𝓖 .fmor (f .mat)))) ∘ split P .sect)
    ≈˘⟨ ∘-cong ≈-refl (∘-cong (assoc _ _ _) ≈-refl) ⟩
      split R .retr ∘ (((𝓖 .fmor (g .mat) ∘ split Q .sect) ∘ (split Q .retr ∘ 𝓖 .fmor (f .mat))) ∘ split P .sect)
    ≈⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
      split R .retr ∘ ((𝓖 .fmor (g .mat) ∘ split Q .sect) ∘ ((split Q .retr ∘ 𝓖 .fmor (f .mat)) ∘ split P .sect))
    ≈˘⟨ assoc _ _ _ ⟩
      (split R .retr ∘ (𝓖 .fmor (g .mat) ∘ split Q .sect)) ∘ ((split Q .retr ∘ 𝓖 .fmor (f .mat)) ∘ split P .sect)
    ≈⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
      (split R .retr ∘ (𝓖 .fmor (g .mat) ∘ split Q .sect)) ∘ (split Q .retr ∘ (𝓖 .fmor (f .mat) ∘ split P .sect))
    ∎ where open ≈-Reasoning isEquiv
