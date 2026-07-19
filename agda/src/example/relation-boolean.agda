{-# OPTIONS --prop --postfix-projections --safe #-}

-- Instantiation of the logical relation at the example signature: Boolean dependency model over rational
-- data.
module example.relation-boolean where

open import Level using (0ℓ)
open import Data.Nat using (ℕ)
open import Data.Rational using (ℚ)
open import categories using (Category)
open import language-operational.algebra using (Algebra)
import ho-model-boolalg-sd-semimod
import two
import matrix
import language-operational.logical-relation
open import example.signature ℚ using (Sig; sort; number; label; approx; op)
import example.dependency

module Dep = example.dependency

private
  module H = ho-model-boolalg-sd-semimod two.semiring two.semiring-boolean

-- Value-level algebra, by projection from the model.
module Alg-inst where
  module PA = language-operational.algebra.IndexAlgebra
                H.BoolAlg.cat H.BoolAlg.terminal H.BoolAlg.products Sig

  Alg : Algebra Sig 0ℓ
  Alg = PA.index-algebra Dep.D.BaseInterp1

  sort-val : sort → Set
  sort-val = Algebra.sort-val Alg

sort-width : sort → ℕ
sort-width = Dep.sort-width

private
  module M𝟚 = matrix.Mat two.semiring

op-mat : ∀ {is o'} → op is o' → Category._⇒_ M𝟚.cat (Dep.bases-width is) (sort-width o')
op-mat = Dep.op-mat

module LR = language-operational.logical-relation Sig Dep.D.BaseInterp1

pres : LR.Presentation
pres = record { sort-width = sort-width ; sort-can = sort-can ; op-mat = op-mat }
  where
  sort-can : ∀ s (c : Alg-inst.sort-val s) → _
  sort-can number _ = Dep.sort-can number
  sort-can label  _ = Dep.sort-can label
  sort-can approx _ = Dep.sort-can approx

module Inst = LR.WithPresentation pres

-- The fundamental property, specialised to this instantiation.
FP : Set
FP = Inst.FundamentalProperty

-- Totality, the evaluator and the instrumentation, at the same model.
import language-operational.totality
module Tot = language-operational.totality Sig Alg-inst.Alg sort-width
module TotOp = Tot.WithOp op-mat

import language-operational.instrument
module Instr = language-operational.instrument Sig Alg-inst.Alg sort-width
module InstrOp = Instr.WithOp op-mat
