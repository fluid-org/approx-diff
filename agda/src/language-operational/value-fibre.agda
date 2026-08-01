{-# OPTIONS --prop --postfix-projections --safe #-}

-- The ordered fibre of a value: the positions of a value together with the order that makes a
-- selection of them a prefix. Every value former contributes a root above its payload, so the
-- bottom of a former is distinct from the former applied to bottoms. Rolling contributes nothing of
-- its own, since the sum and product inside the body already carry roots, and a closure is left
-- with the fibre of its environment for now.
--
-- The dimension is the width the operational semantics would have to use, which differs from the
-- present one at the unit, the injections and the pair.
open import Level using (0ℓ)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_; tabulate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import commutative-semiring using (CommutativeSemiring)
open import signature using (Signature)
open import primitives using (Primitives)
import two
import matrix
import order-idempotent

module language-operational.value-fibre {ℓ} (Sig : Signature ℓ) (𝒫 : Primitives two.semiring Sig) where

open Signature Sig
open Primitives 𝒫
import language-syntax Sig as Syn
open import language-operational.evaluation Sig 𝒫 using (Val; Env; width; width-env)
open Val
open Env

private
  module T = CommutativeSemiring two.semiring
  module TM = matrix.Mat two.semiring

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

mutual
  pos : ∀ {τ} → Val τ → Pos
  pos unit            = Lp 𝟘p
  pos (const {s} _)   = disc (sort-width s)
  pos (inl v)         = Lp (pos v)
  pos (inr v)         = Lp (pos v)
  pos (pair v u)      = Lp (pos v ⊕ pos u)
  pos (clo γ _)       = pos-env γ
  pos (roll v)        = pos v

  pos-env : ∀ {Γ} → Env Γ → Pos
  pos-env emp     = 𝟘p
  pos-env (γ · v) = pos-env γ ⊕ pos v

-- The width the ordered fibre implies, against the present one: a former now costs a position.
mutual
  width′ : ∀ {τ} → Val τ → ℕ
  width′ unit          = 1
  width′ (const {s} _) = sort-width s
  width′ (inl v)       = suc (width′ v)
  width′ (inr v)       = suc (width′ v)
  width′ (pair v u)    = suc (width′ v + width′ u)
  width′ (clo γ _)     = width-env′ γ
  width′ (roll v)      = width′ v

  width-env′ : ∀ {Γ} → Env Γ → ℕ
  width-env′ emp     = 0
  width-env′ (γ · v) = width-env′ γ + width′ v

mutual
  pos-dim : ∀ {τ} (v : Val τ) → pos v .dim ≡ width′ v
  pos-dim unit        = refl
  pos-dim (const _)   = refl
  pos-dim (inl v)     = cong suc (pos-dim v)
  pos-dim (inr v)     = cong suc (pos-dim v)
  pos-dim (pair v u)  = cong suc (cong₂ _+_ (pos-dim v) (pos-dim u))
  pos-dim (clo γ _)   = pos-env-dim γ
  pos-dim (roll v)    = pos-dim v

  pos-env-dim : ∀ {Γ} (γ : Env Γ) → pos-env γ .dim ≡ width-env′ γ
  pos-env-dim emp     = refl
  pos-env-dim (γ · v) = cong₂ _+_ (pos-env-dim γ) (pos-dim v)

private
  table : ∀ {m n} → TM.Matrix m n → Vec (Vec two.Two n) m
  table M = tabulate (λ i → tabulate (λ j → M i j))

  -- An injected unit: the injection's root above the unit's root.
  inl-unit : Vec (Vec two.Two 2) 2
  inl-unit = (two.I ∷ two.I ∷ []) ∷ (two.O ∷ two.I ∷ []) ∷ []

  test-inl-unit : table (pos (inl {Syn.unit} {Syn.unit} unit) .ord) ≡ inl-unit
  test-inl-unit = refl

  -- A pair of units: the pair's root above both components' roots, which are unrelated.
  pair-units : Vec (Vec two.Two 3) 3
  pair-units = (two.I ∷ two.I ∷ two.I ∷ []) ∷ (two.O ∷ two.I ∷ two.O ∷ []) ∷
               (two.O ∷ two.O ∷ two.I ∷ []) ∷ []

  test-pair-units : table (pos (pair {Syn.unit} {Syn.unit} unit unit) .ord) ≡ pair-units
  test-pair-units = refl
