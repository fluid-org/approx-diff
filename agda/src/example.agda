{-# OPTIONS --prop --postfix-projections --safe #-}

module example where

open import Level using (0ℓ; lift)
open import Data.List using (List; []; _∷_)
open import every using (Every; []; _∷_)
open import signature
import language-syntax
import label

open import example-signature

module L = language-syntax Sig

-- example query. Given `List (label [×] nat)`, add up all the
-- elements labelled with a specific label:
--
--   sum [ snd e | e <- xs, equal-label 'a' (fst e) ]
--
--   sum (concatMap x (e. if equal-label 'a' (fst e) then return (snd e) else nil))
--
--   sum = fold zero (add (var zero) (var (succ zero)))

module ex where
  open L

  `_ : ∀ {Γ} → label.label → Γ ⊢ base label
  ` l = bop (lbl l) []

  _≟_ : ∀ {Γ} → Γ ⊢ base label → Γ ⊢ base label → Γ ⊢ bool
  M ≟ N = brel equal-label (M ∷ N ∷ [])

  -- Summation function, μ-types version (uses list).
  sum : ∀ {Γ} → Γ ⊢ list (base number) [→] base number
  sum = lam (fold (bop zero []) (bop add (var zero ∷ var (succ zero) ∷ [])) (var zero))

  query : label.label → emp , list (base label [×] base number) ⊢ base number
  query l = app sum
                 (from var zero collect
                  when fst (var zero) ≟ (` l) ；
                  return (snd (var zero)))

  open import cbn-translation Sig

  cbn-query : label.label →
              ⟪ emp , list (base label [×] base number) ⟫ctxt ⊢ approx ⟪ base number ⟫ty
  cbn-query l = ⟪ query l ⟫tm
