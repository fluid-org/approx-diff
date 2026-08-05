{-# OPTIONS --prop --postfix-projections --safe #-}

-- Rendering of partial values: structural, with a hole wherever a former's root is unselected,
-- so distinct partial values of the same value render distinctly. A constant renders as its
-- value when fully selected and with a ~ prefix when only some of its positions are selected.
-- List notation is left to the paper's conventions; here inductive values render through their
-- sum and product structure, with roll invisible.
open import Data.Fin using (zero; suc)
open import Data.Nat using (ℕ)
open import Data.String using (String) renaming (_++_ to _++ˢ_)
import two
open import signature using (Signature)
open import primitives using (Primitives)
import matrix

module language-operational.render-partial
  {ℓ} (Sig : Signature ℓ) (𝒫 : Primitives two.semiring Sig)
  where

open Signature Sig
open Primitives 𝒫
open import language-operational.evaluation Sig 𝒫 using (Val; Env)
open import language-operational.partial-value Sig 𝒫

private
  module M = matrix.Mat two.semiring

  any-I : ∀ {n} → M.Vec n → two.Two
  any-I {ℕ.zero}  w = two.O
  any-I {ℕ.suc n} w = w zero two.⊔ any-I {n} (λ i → w (suc i))

  all-I : ∀ {n} → M.Vec n → two.Two
  all-I {ℕ.zero}  w = two.I
  all-I {ℕ.suc n} w = w zero two.⊓ all-I {n} (λ i → w (suc i))

module _ (show-const : ∀ {s} → sort-val s → String) where

  private
    show-partial : ∀ {s} → sort-val s → M.Vec (sort-width s) → String
    show-partial c w with any-I w | all-I w
    ... | two.O | _     = "_"
    ... | two.I | two.I = show-const c
    ... | two.I | two.O = "~" ++ˢ show-const c

  mutual
    show-pval : ∀ {τ} {v : Val τ} → PVal v → String
    show-pval (hole _)           = "_"
    show-pval unit*              = "()"
    show-pval (const* {c = c} w) = show-partial c w
    show-pval (inl* p)           = "inl " ++ˢ show-pval p
    show-pval (inr* p)           = "inr " ++ˢ show-pval p
    show-pval (pair* p q)        = "(" ++ˢ show-pval p ++ˢ ", " ++ˢ show-pflat q ++ˢ ")"
    show-pval (clo* ρ)           = "<closure>"
    show-pval (roll* p)          = show-pval p

    -- Right-nested pairs render as flat tuples, as for full values.
    show-pflat : ∀ {τ} {v : Val τ} → PVal v → String
    show-pflat (pair* p q) = show-pval p ++ˢ ", " ++ˢ show-pflat q
    show-pflat p           = show-pval p
