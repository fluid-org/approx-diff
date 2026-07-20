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
open import example.signature ℚ using (Sig; sort; number; label; op)
import example.dependency

module Dep = example.dependency

private
  module H = ho-model-boolalg-sd-semimod two.semiring two.semiring-boolean

-- Value-level algebra, by projection from the model.
module Alg-inst = Dep.Alg-inst

module LR = language-operational.logical-relation Sig Dep.D.BaseInterp1

pres : LR.Presentation
pres = record { sort-approx = Dep.sort-approx ; sort-can = sort-can ; op-rel = Dep.op-rel }
  where
  sort-can : ∀ s (c : Alg-inst.sort-val s) → _
  sort-can number _ = Dep.FO𝟚.canonical (Dep.sort-approx number)
  sort-can label  _ = Dep.FO𝟚.canonical (Dep.sort-approx label)

module Inst = LR.WithPresentation pres

-- The fundamental property, specialised to this instantiation.
FP : Set
FP = Inst.FundamentalProperty

-- Totality, the evaluator and the instrumentation, at the same model.
import language-operational.totality
module Tot = language-operational.totality Sig Alg-inst.Alg (λ s → H.FO.width (Dep.sort-approx s))
module TotOp = Tot.WithOp Dep.op-rel

import language-operational.instrument
module Instr = language-operational.instrument Sig Alg-inst.Alg (λ s → H.FO.width (Dep.sort-approx s))
module InstrOp = Instr.WithOp Dep.op-rel
