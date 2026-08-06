{-# OPTIONS --prop --postfix-projections --safe #-}

-- The display skeleton of a value: one entry per position, in the same order and number as pos,
-- carrying a label, the parent position and a merge class. The class rule is the over-approximating
-- sugar view already used by the partial-value renderer: a former directly beneath an injection
-- joins the injection's class, so cons and nil cells and boolean values become single nodes;
-- scalars never merge.
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String)
import two
open import signature using (Signature)
open import primitives using (Primitives)

module language-operational.value-skeleton {ℓ} (Sig : Signature ℓ)
  (𝒫 : Primitives two.semiring Sig) where

open Signature Sig
open Primitives 𝒫
open import language-operational.evaluation Sig 𝒫 using (Val; Env)
open Val
open Env
open import language-operational.value-fibre Sig 𝒫 using (width′; width-env′)

record Entry : Set where
  field
    label  : String
    parent : Maybe ℕ
    cls    : ℕ

open Entry public

entry : String → Maybe ℕ → ℕ → Entry
entry l p c .label  = l
entry l p c .parent = p
entry l p c .cls    = c

private
  pick : Maybe ℕ → ℕ → ℕ
  pick (just c) _ = c
  pick nothing  i = i

module _ (show-const : ∀ {s} → sort-val s → String) where

  private
    scalars : ∀ {s} → sort-val s → ℕ → ℕ → Maybe ℕ → List Entry
    scalars c zero    off par = []
    scalars c (suc n) off par = entry (show-const c) par off ∷ scalars c n (suc off) par

  mutual
    -- Entries for a value at an absolute offset, given the parent of its root and the class the
    -- root joins when the value sits directly beneath an injection.
    build : ∀ {τ} (v : Val τ) (off : ℕ) (par : Maybe ℕ) (root-cls : Maybe ℕ) → List Entry
    build unit off par rc = entry "()" par (pick rc off) ∷ []
    build (const {s} c) off par rc = scalars c (sort-width s) off par
    build (inl v) off par rc =
      entry "inl" par (pick rc off) ∷ build v (suc off) (just off) (just (pick rc off))
    build (inr v) off par rc =
      entry "inr" par (pick rc off) ∷ build v (suc off) (just off) (just (pick rc off))
    build (pair v u) off par rc =
      entry "pr" par (pick rc off)
        ∷ (build v (suc off) (just off) nothing
           ++ build u (suc off + width′ v) (just off) nothing)
    build (clo γ t) off par rc =
      entry "clo" par (pick rc off) ∷ build-env γ (suc off) (just off)
    build (roll v) off par rc = build v off par rc

    build-env : ∀ {Γ} (γ : Env Γ) (off : ℕ) (par : Maybe ℕ) → List Entry
    build-env emp     off par = []
    build-env (γ · v) off par = build-env γ off par ++ build v (off + width-env′ γ) par nothing

  skeleton : ∀ {τ} (v : Val τ) → List Entry
  skeleton v = build v 0 nothing nothing

  skeleton-env : ∀ {Γ} (γ : Env Γ) → List Entry
  skeleton-env γ = build-env γ 0 nothing
