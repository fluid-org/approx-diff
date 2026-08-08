{-# OPTIONS --prop --postfix-projections --safe #-}

-- Annotated values: the operational presentation of a selection over free positions. A value's
-- positions are its scalar leaves together with one position per former, no order relates them, and
-- a selection is any weighted vector over the positions, presented by marking the value's subterms:
-- each former carries the scalar at its position and a constant carries one scalar per position.
-- Nothing closes a selection, so a relation row attaches to a value directly, positionwise in the
-- order the fibre counts positions: a former's root before its payload, a pair's first component
-- before its second.
open import Level using (0ℓ)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (toℕ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import signature using (Signature)
open import primitives using (Primitives)
import two
import matrix

module language-operational.annotated-value {ℓ} (Sig : Signature ℓ)
  (𝒫 : Primitives two.semiring Sig) where

open Signature Sig
open Primitives 𝒫
import language-syntax Sig as Syn
open import language-operational.evaluation Sig 𝒫 using (Val; Env)
open Val
open Env
open import language-operational.value-fibre Sig 𝒫 using (pos; pos-env)

module annotate {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A) where

  private
    module M = matrix.Mat S

  Scalar : Set
  Scalar = Setoid.Carrier A

  mutual
    data AVal : ∀ {τ} → Val τ → Set ℓ where
      unit*  : Scalar → AVal unit
      const* : ∀ {s} {c : sort-val s} → M.Vec (sort-width s) → AVal (const c)
      inl*   : ∀ {τ₁ τ₂} {v : Val τ₁} → Scalar → AVal v → AVal (inl {τ₁} {τ₂} v)
      inr*   : ∀ {τ₁ τ₂} {v : Val τ₂} → Scalar → AVal v → AVal (inr {τ₁} {τ₂} v)
      pair*  : ∀ {τ₁ τ₂} {v : Val τ₁} {u : Val τ₂} → Scalar → AVal v → AVal u → AVal (pair v u)
      clo*   : ∀ {Γ σ τ} {γ : Env Γ} {t : (Γ Syn., σ) Syn.⊢ τ} → Scalar → AEnv γ → AVal (clo γ t)
      roll*  : ∀ {τ} {v : Val (τ Syn.[ Syn.μ τ ])} → AVal v → AVal (roll {τ = τ} v)

    data AEnv : ∀ {Γ} → Env Γ → Set ℓ where
      emp* : AEnv emp
      _·*_ : ∀ {Γ τ} {γ : Env Γ} {v : Val τ} → AEnv γ → AVal v → AEnv (γ · v)

  infixl 30 _·*_

  -- A row read at an offset. The row is total so the caller fixes the out-of-range convention; the
  -- layouts of the row and the value agree positionwise, and a misalignment would surface in the
  -- rendered baseline.
  mutual
    aval-at : ∀ {τ} (v : Val τ) → (ℕ → Scalar) → ℕ → AVal v
    aval-at unit          row off = unit* (row off)
    aval-at (const {s} c) row off = const* (λ i → row (off + toℕ i))
    aval-at (inl v)       row off = inl* (row off) (aval-at v row (suc off))
    aval-at (inr v)       row off = inr* (row off) (aval-at v row (suc off))
    aval-at (pair v u)    row off =
      pair* (row off) (aval-at v row (suc off)) (aval-at u row (suc off + pos v))
    aval-at (clo γ t)     row off = clo* (row off) (aenv-at γ row (suc off))
    aval-at (roll v)      row off = roll* (aval-at v row off)

    aenv-at : ∀ {Γ} (γ : Env Γ) → (ℕ → Scalar) → ℕ → AEnv γ
    aenv-at emp     row off = emp*
    aenv-at (γ · v) row off = aenv-at γ row off ·* aval-at v row (off + pos-env γ)

  aval : ∀ {τ} (v : Val τ) → (ℕ → Scalar) → AVal v
  aval v row = aval-at v row 0

  aenv : ∀ {Γ} (γ : Env Γ) → (ℕ → Scalar) → AEnv γ
  aenv γ row = aenv-at γ row 0

-- The walk: one node per position, in the same order and number as the positions, carrying a
-- label, the parent position and a merge class. The class rule is the over-approximating sugar
-- view the graph dump draws: a former directly beneath an injection joins the injection's class,
-- so cons and nil cells and boolean values become single nodes; scalars never merge.
record Node : Set where
  field
    label  : String
    parent : Maybe ℕ
    cls    : ℕ

open Node public

node : String → Maybe ℕ → ℕ → Node
node l p c .label  = l
node l p c .parent = p
node l p c .cls    = c

private
  pick : Maybe ℕ → ℕ → ℕ
  pick (just c) _ = c
  pick nothing  i = i

module _ (show-const : ∀ {s} → sort-val s → String) where

  private
    scalars : ∀ {s} → sort-val s → ℕ → ℕ → Maybe ℕ → List Node
    scalars c zero    off par = []
    scalars c (suc n) off par = node (show-const c) par off ∷ scalars c n (suc off) par

  mutual
    -- Nodes for a value at an absolute offset, given the parent of its root and the class the
    -- root joins when the value sits directly beneath an injection.
    walk-at : ∀ {τ} (v : Val τ) (off : ℕ) (par : Maybe ℕ) (root-cls : Maybe ℕ) → List Node
    walk-at unit off par rc = node "()" par (pick rc off) ∷ []
    walk-at (const {s} c) off par rc = scalars c (sort-width s) off par
    walk-at (inl v) off par rc =
      node "inl" par (pick rc off) ∷ walk-at v (suc off) (just off) (just (pick rc off))
    walk-at (inr v) off par rc =
      node "inr" par (pick rc off) ∷ walk-at v (suc off) (just off) (just (pick rc off))
    walk-at (pair v u) off par rc =
      node "pr" par (pick rc off)
        ∷ (walk-at v (suc off) (just off) nothing
           ++ walk-at u (suc off + pos v) (just off) nothing)
    walk-at (clo γ t) off par rc =
      node "clo" par (pick rc off) ∷ walk-env-at γ (suc off) (just off)
    walk-at (roll v) off par rc = walk-at v off par rc

    walk-env-at : ∀ {Γ} (γ : Env Γ) (off : ℕ) (par : Maybe ℕ) → List Node
    walk-env-at emp     off par = []
    walk-env-at (γ · v) off par = walk-env-at γ off par ++ walk-at v (off + pos-env γ) par nothing

  walk : ∀ {τ} (v : Val τ) → List Node
  walk v = walk-at v 0 nothing nothing

  walk-env : ∀ {Γ} (γ : Env Γ) → List Node
  walk-env γ = walk-env-at γ 0 nothing
