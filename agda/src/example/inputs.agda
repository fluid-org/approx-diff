{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (0ℓ)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)

-- The example programs' inputs, as environments of values.
module example.inputs {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A) (ctrl-weight : Setoid.Carrier A) where

open import Data.Rational using (ℚ; 0ℚ; 1ℚ) renaming (_+_ to _+ℚ_)
open import Relation.Binary.PropositionalEquality using (subst; sym)
import label
open import signature.example.interpretation S using (Sig; interpretation; number; label)
open import example.programs using (case-ctxt)
open import language-syntax Sig using (type; base; unit; list; _[×]_; _[+]_; emp; _,_; sub-ren-id)
open import language-operational.evaluation Sig S interpretation ctrl-weight using (Val; Env)
open Val
open Env

private
  infixr 20 _∷ᵥ_

  nilᵥ : ∀ {τ : type 0} → Val (list τ)
  nilᵥ = roll (inl unit)

  _∷ᵥ_ : ∀ {τ : type 0} → Val τ → Val (list τ) → Val (list τ)
  _∷ᵥ_ {τ} x xs = roll (inr (pair (subst Val (sym (sub-ren-id τ (λ ()))) x) xs))

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

γ-mavg : Env (emp , base number [×] (base number [×] (base number [×] base number)))
γ-mavg = emp · pair (const 1ℚ) (pair (const two) (pair (const four) (const eight)))
  where
  two   = 1ℚ +ℚ 1ℚ
  four  = two +ℚ two
  eight = four +ℚ four

-- The derivative of x * y is [y, x], so at (1, 0) the result depends on y alone.
γ-mult : Env (emp , base number [×] base number)
γ-mult = emp · pair (const 1ℚ) (const 0ℚ)

γ-case-l γ-case-r : Env case-ctxt
γ-case-l = emp · const 1ℚ · inl unit
γ-case-r = emp · const 1ℚ · inr unit
