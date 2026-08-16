{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (0ℓ)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)

-- The example programs' inputs, as environments of values.
module example.inputs {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A) (elim-weight : Setoid.Carrier A) where

open import Data.Rational using (ℚ; 0ℚ; 1ℚ) renaming (_+_ to _+ℚ_)
import label
open import example.primitives-over S using (Sig; primitives; number; label)
open import example.programs using (case-ctxt)
open import language-syntax Sig using (base; unit; list; _[×]_; _[+]_; emp; _,_)
open import language-operational.evaluation Sig S primitives elim-weight using (Val; Env)
open Val
open Env
open import example.mk-list Sig S primitives elim-weight using (_∷ᵥ_; nilᵥ)

private
  el : label.label → ℚ → Val (base label [×] base number)
  el l n = pair (const l) (const n)

-- Three entries, two under the queried label.
γ-query : Env (emp , list (base label [×] base number))
γ-query = emp · (el label.a 0ℚ ∷ᵥ el label.b 1ℚ ∷ᵥ el label.a 1ℚ ∷ᵥ nilᵥ)

γ-nums : Env (emp , list (base number))
γ-nums = emp · (const 0ℚ ∷ᵥ const 1ℚ ∷ᵥ const (1ℚ +ℚ 1ℚ) ∷ᵥ nilᵥ)

-- The target, then the list.
γ-filter : Env (emp , base number , list (base number))
γ-filter = emp · const (1ℚ +ℚ 1ℚ) · (const 1ℚ ∷ᵥ const (1ℚ +ℚ 1ℚ) ∷ᵥ const ((1ℚ +ℚ 1ℚ) +ℚ 1ℚ) ∷ᵥ nilᵥ)

γ-cond : Env (emp , base number , base number)
γ-cond = emp · const 0ℚ · const 1ℚ

γ-eq γ-test : Env (emp , base number)
γ-eq   = emp · const 0ℚ
γ-test = emp · const 1ℚ

γ-case-l γ-case-r : Env case-ctxt
γ-case-l = emp · const 1ℚ · inl unit
γ-case-r = emp · const 1ℚ · inr unit
