{-# OPTIONS --prop --postfix-projections --safe #-}

-- Partial values: the operational reading of a selection. A partial value keeps some of a value's
-- formers and cuts the rest to holes; keeping a position keeps the formers above it, so the
-- partial values of a value are the prefixes of its former tree, with an arbitrary subset of the
-- positions at each constant. The bridge to the model: the fixed vectors of a value's position
-- order are exactly its partial values, a hole where a former's root is unselected.
open import Level using (0ℓ)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import basics using (IsTop)
open import prop using (∃ₛ) renaming (_,_ to _,ₚ_)
open import commutative-semiring using (CommutativeSemiring)
open import signature using (Signature)
open import primitives using (Primitives)
import two
import matrix
import order-idempotent
import order-idempotent-blocks

module language-operational.partial-value {ℓ} (Sig : Signature ℓ)
  (𝒫 : Primitives two.semiring Sig) where

open Signature Sig
open Primitives 𝒫
import language-syntax Sig as Syn
open import language-operational.evaluation Sig 𝒫 using (Val; Env)
open Val
open Env
open import language-operational.value-fibre Sig 𝒫 using (pos; pos-env)

private
  module T = CommutativeSemiring two.semiring
  module M = matrix.Mat two.semiring

open order-idempotent two.semiring
  (λ {x} → two.∨-idem {x}) (λ {x} → two.∧-idem {x}) (λ {x} → two.⊤-add-top {x})
open order-idempotent-blocks two.semiring
  (λ {x} → two.∨-idem {x}) (λ {x} → two.∧-idem {x}) (λ {x} → two.⊤-add-top {x})
  using (appendV; leftV; rightV; ⊕-fixed-left; ⊕-fixed-right; ⊕-fixed-append)

-- The formers that carry a root, so that a partial value can stop above them. Constants carry
-- their positions directly and rolling is transparent, so neither admits a hole of its own.
Rooted : ∀ {τ} → Val τ → Set
Rooted unit       = ⊤
Rooted (const _)  = ⊥
Rooted (inl _)    = ⊤
Rooted (inr _)    = ⊤
Rooted (pair _ _) = ⊤
Rooted (clo _ _)  = ⊤
Rooted (roll _)   = ⊥

mutual
  data PVal : ∀ {τ} → Val τ → Set ℓ where
    hole   : ∀ {τ} {v : Val τ} → Rooted v → PVal v
    unit*  : PVal unit
    const* : ∀ {s} {c : sort-val s} → M.Vec (sort-width s) → PVal (const c)
    inl*   : ∀ {τ₁ τ₂} {v : Val τ₁} → PVal v → PVal (inl {τ₁} {τ₂} v)
    inr*   : ∀ {τ₁ τ₂} {v : Val τ₂} → PVal v → PVal (inr {τ₁} {τ₂} v)
    pair*  : ∀ {τ₁ τ₂} {v : Val τ₁} {u : Val τ₂} → PVal v → PVal u → PVal (pair v u)
    clo*   : ∀ {Γ σ τ} {γ : Env Γ} {t : (Γ Syn., σ) Syn.⊢ τ} → PEnv γ → PVal (clo γ t)
    roll*  : ∀ {τ} {v : Val (τ Syn.[ Syn.μ τ ])} → PVal v → PVal (roll {τ = τ} v)

  data PEnv : ∀ {Γ} → Env Γ → Set ℓ where
    emp*  : PEnv emp
    _·*_  : ∀ {Γ τ} {γ : Env Γ} {v : Val τ} → PEnv γ → PVal v → PEnv (γ · v)

infixl 30 _·*_

private
  cons : ∀ {n} → two.Two → M.Vec n → M.Vec (ℕ.suc n)
  cons a u zero    = a
  cons a u (suc i) = u i

  -- Case analysis on a root bit that does not abstract it from the context, since the fixedness
  -- hypotheses mention the whole vector.
  two-case : ∀ {a} {A : Set a} (b : two.Two) → (b ≡ two.O → A) → (b ≡ two.I → A) → A
  two-case two.O o i = o refl
  two-case two.I o i = i refl

  Sel : Pos → Set
  Sel P = ∃ₛ (M.Vec (P .dim)) (Fixed P)

  -- The empty selection, and fixedness of a discrete selection.
  zero-sel : ∀ P → Sel P
  zero-sel P = (λ _ → T.ε) ,ₚ (λ i → app-ε (P .ord) i)

  disc-fixed : ∀ {n} (w : M.Vec n) → Fixed (disc n) w
  disc-fixed w i = M.Σ-unit i w

  -- A selection under a selected root: the payload's support is dominated because the root is top.
  under-root : ∀ P → Sel P → Sel (Lp P)
  under-root P (w ,ₚ fx) =
    cons T.ι w ,ₚ Lp-fixed P (cons T.ι w) fx (IsTop.≤-top L.⊤-isTop)

-- The selection a partial value denotes: holes select nothing, a kept former selects its root
-- above its payload's selection, a constant selects its subset. Recursion is driven by the value
-- so that the μ index never has to be recovered from a substituted type.
mutual
  sel : ∀ {τ} (v : Val τ) → PVal v → Sel (pos v)
  sel v (hole r)       = zero-sel (pos v)
  sel unit unit*       = under-root 𝟘p (zero-sel 𝟘p)
  sel (const c) (const* w) = w ,ₚ disc-fixed w
  sel (inl v) (inl* p) = under-root (pos v) (sel v p)
  sel (inr v) (inr* p) = under-root (pos v) (sel v p)
  sel (pair v u) (pair* p q) =
    under-root (pos v ⊕ pos u)
      (appendV (vec (pos v) (sel v p)) (vec (pos u) (sel u q)) ,ₚ
       ⊕-fixed-append (pos v) (pos u) (fxd (pos v) (sel v p)) (fxd (pos u) (sel u q)))
  sel (clo γ t) (clo* ρ) = under-root (pos-env γ) (sel-env γ ρ)
  sel (roll {τ = τ'} v) (roll* p) = sel v p

  sel-env : ∀ {Γ} (γ : Env Γ) → PEnv γ → Sel (pos-env γ)
  sel-env emp emp* = (λ ()) ,ₚ (λ ())
  sel-env (γ · v) (ρ ·* p) =
    appendV (vec (pos-env γ) (sel-env γ ρ)) (vec (pos v) (sel v p)) ,ₚ
    ⊕-fixed-append (pos-env γ) (pos v) (fxd (pos-env γ) (sel-env γ ρ)) (fxd (pos v) (sel v p))

-- The partial value a selection denotes: read the root; unselected cuts to a hole, selected
-- descends into the payload.
mutual
  pval : ∀ {τ} (v : Val τ) → Sel (pos v) → PVal v
  pval unit (w ,ₚ fx) =
    two-case (w zero) (λ _ → hole tt) (λ _ → unit*)
  pval (const c) (w ,ₚ fx) = const* w
  pval (inl v) (w ,ₚ fx) =
    two-case (w zero) (λ _ → hole tt)
      (λ _ → inl* (pval v (tail w ,ₚ Lp-fixed-tail (pos v) w fx)))
  pval (inr v) (w ,ₚ fx) =
    two-case (w zero) (λ _ → hole tt)
      (λ _ → inr* (pval v (tail w ,ₚ Lp-fixed-tail (pos v) w fx)))
  pval (pair v u) (w ,ₚ fx) =
    two-case (w zero) (λ _ → hole tt)
      (λ _ →
        pair* (pval v (leftV (tail w) ,ₚ
                       ⊕-fixed-left (pos v) (pos u) (Lp-fixed-tail (pos v ⊕ pos u) w fx)))
              (pval u (rightV (tail w) ,ₚ
                       ⊕-fixed-right (pos v) (pos u) (Lp-fixed-tail (pos v ⊕ pos u) w fx))))
  pval (clo γ t) (w ,ₚ fx) =
    two-case (w zero) (λ _ → hole tt)
      (λ _ → clo* (pval-env γ (tail w ,ₚ Lp-fixed-tail (pos-env γ) w fx)))
  pval (roll {τ = τ'} v) x = roll* {τ = τ'} (pval v x)

  pval-env : ∀ {Γ} (γ : Env Γ) → Sel (pos-env γ) → PEnv γ
  pval-env emp _ = emp*
  pval-env (γ · v) (w ,ₚ fx) =
    pval-env γ (leftV w ,ₚ ⊕-fixed-left (pos-env γ) (pos v) fx) ·*
    pval v (rightV w ,ₚ ⊕-fixed-right (pos-env γ) (pos v) fx)
