{-# OPTIONS --prop --postfix-projections --safe #-}

-- Every value fibre is a forest: the fibres are built from discrete orders by biproduct and
-- lifting alone, and forests are closed under all three.
open import Level using (0ℓ)
open import commutative-semiring using (CommutativeSemiring)
open import signature using (Signature)
open import primitives using (Primitives)
import two
import order-idempotent
import order-idempotent-forest

module language-operational.forest {ℓ} (Sig : Signature ℓ) (𝒫 : Primitives two.semiring Sig) where

open Signature Sig
open Primitives 𝒫
open import language-operational.evaluation Sig 𝒫 using (Val; Env)
open Val
open Env
open import language-operational.value-fibre Sig 𝒫 using (pos; pos-env)

private
  module T = CommutativeSemiring two.semiring

  ∨-idem : ∀ {x} → (x T.+ x) T.≈ x
  ∨-idem {two.O} = T.refl {two.O}
  ∨-idem {two.I} = T.refl {two.I}

  ∧-idem : ∀ {x} → (x T.· x) T.≈ x
  ∧-idem {two.O} = T.refl {two.O}
  ∧-idem {two.I} = T.refl {two.I}

  ⊤-add-top : ∀ {x} → (T.ι T.+ x) T.≈ T.ι
  ⊤-add-top {two.O} = T.refl {two.I}
  ⊤-add-top {two.I} = T.refl {two.I}

open order-idempotent two.semiring (λ {x} → ∨-idem {x}) (λ {x} → ∧-idem {x}) (λ {x} → ⊤-add-top {x})
open order-idempotent-forest two.semiring
  (λ {x} → ∨-idem {x}) (λ {x} → ∧-idem {x}) (λ {x} → ⊤-add-top {x})

mutual
  forest-pos : ∀ {τ} (v : Val τ) → Forest (pos v)
  forest-pos unit          = forest-Lp 𝟘p forest-𝟘p
  forest-pos (const {s} _) = forest-disc (sort-width s)
  forest-pos (inl v)       = forest-Lp (pos v) (forest-pos v)
  forest-pos (inr v)       = forest-Lp (pos v) (forest-pos v)
  forest-pos (pair v u)    =
    forest-Lp (pos v ⊕ pos u) (forest-⊕ (pos v) (pos u) (forest-pos v) (forest-pos u))
  forest-pos (clo γ _)     = forest-Lp (pos-env γ) (forest-pos-env γ)
  forest-pos (roll v)      = forest-pos v

  forest-pos-env : ∀ {Γ} (γ : Env Γ) → Forest (pos-env γ)
  forest-pos-env emp     = forest-𝟘p
  forest-pos-env (γ · v) = forest-⊕ (pos-env γ) (pos v) (forest-pos-env γ) (forest-pos v)
