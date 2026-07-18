{-# OPTIONS --postfix-projections --prop --safe #-}

open import Level using (Level; Lift; lift; suc; _⊔_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤; tt)
open import signature using (Signature; Algebra)
import language-syntax

------------------------------------------------------------------------
-- Operational interpretation: types as value sets, contexts as tuples. Depends only on the
-- signature's value-level interpretation (Algebra), not on any categorical model.

module language-fo-evaluation {ℓ ℓ'} (Sig : Signature ℓ) (𝒜 : Algebra Sig ℓ') where

open Signature Sig
open Algebra 𝒜
open language-syntax Sig

Val : type → Set ℓ'
Val unit         = Lift ℓ' ⊤
Val (base s)     = sort-val s
Val (τ₁ [×] τ₂)  = Val τ₁ × Val τ₂
Val (τ₁ [+] τ₂)  = Val τ₁ ⊎ Val τ₂
Val (list τ)     = List (Val τ)

Env : ctxt → Set ℓ'
Env emp          = Lift ℓ' ⊤
Env (Γ · τ)      = Env Γ × Val τ

lookup : ∀ {Γ τ} → Γ ∋ τ → Env Γ → Val τ
lookup zero     (_ , v) = v
lookup (succ x) (γ , _) = lookup x γ
