{-# OPTIONS --prop --postfix-projections --safe #-}

-- language-operational.evaluation still uses the width without former roots.
open import Data.Nat using (ℕ; suc; _+_)
open import signature using (Signature)
open import primitives using (Primitives)
import two

module language-operational.width {ℓ} (Sig : Signature ℓ) (𝒫 : Primitives two.semiring Sig) where

open Signature Sig
open Primitives 𝒫
open import language-operational.evaluation Sig 𝒫 using (Val; Env)
open Val
open Env

mutual
  width : ∀ {τ} → Val τ → ℕ
  width unit          = 1
  width (const {s} _) = sort-width s
  width (inl v)       = suc (width v)
  width (inr v)       = suc (width v)
  width (pair v u)    = suc (width v + width u)
  width (clo γ _)     = suc (width-env γ)
  width (roll v)      = width v

  width-env : ∀ {Γ} → Env Γ → ℕ
  width-env emp     = 0
  width-env (γ · v) = width-env γ + width v
