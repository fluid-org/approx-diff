{-# OPTIONS --prop --postfix-projections --safe #-}

-- The fibre of a value: with no order on positions a fibre is a dimension, so the positions of a
-- value are a count, its scalar leaves together with one position per former. Every value former
-- contributes a root above its payload, so the bottom of a former is distinct from the former
-- applied to bottoms. Rolling contributes nothing of its own, since the sum and product inside the
-- body already carry roots. A closure carries a root above its environment, so that a function
-- position can be sliced away on its own.
--
-- This is the width the operational semantics would have to use, which differs from the present
-- one at the unit, the injections and the pair.
open import Data.Nat using (ℕ; suc; _+_)
open import signature using (Signature)
open import primitives using (Primitives)
import two

module language-operational.value-fibre {ℓ} (Sig : Signature ℓ) (𝒫 : Primitives two.semiring Sig) where

open Signature Sig
open Primitives 𝒫
open import language-operational.evaluation Sig 𝒫 using (Val; Env)
open Val
open Env

mutual
  pos : ∀ {τ} → Val τ → ℕ
  pos unit          = 1
  pos (const {s} _) = sort-width s
  pos (inl v)       = suc (pos v)
  pos (inr v)       = suc (pos v)
  pos (pair v u)    = suc (pos v + pos u)
  pos (clo γ _)     = suc (pos-env γ)
  pos (roll v)      = pos v

  pos-env : ∀ {Γ} → Env Γ → ℕ
  pos-env emp     = 0
  pos-env (γ · v) = pos-env γ + pos v
