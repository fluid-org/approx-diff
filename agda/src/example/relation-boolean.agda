{-# OPTIONS --prop --postfix-projections --safe #-}

-- Instantiation of the logical relation at the example signature: Boolean dependency model over rational
-- data.
module example.relation-boolean where

open import Level using (0ℓ)
open import Data.Nat using (ℕ)
open import Data.Rational using (ℚ)
open import categories using (Category)
open import language-operational.algebra using (Algebra)
import two
import matrix
import matrix-embedding-semimod
import language-operational.logical-relation
open import example.signature ℚ using (Sig; sort; number; label; op)
import example.dependency

module Dep = example.dependency

private
  module MES = matrix-embedding-semimod two.semiring

-- Value-level algebra, by projection from the model.
module Alg-inst = Dep.Alg-inst

module LR = language-operational.logical-relation Sig Dep.D.BaseInterp1

pres : LR.Presentation
pres = record { sort-width = Dep.sort-width ; sort-can = sort-can ; op-rel = Dep.op-rel }
  where
  -- Uniform in the sort: each base fibre is the free object of its width.
  sort-can : ∀ s (c : Alg-inst.sort-val s) → _
  sort-can s _ = MES.X^≅S^ (Dep.sort-width s) .Category.Iso.fwd

module Inst = LR.WithPresentation pres

-- The fundamental property, specialised to this instantiation.
FP : Set
FP = Inst.FundamentalProperty

-- Totality, the evaluator and the instrumentation, at the same model.
import language-operational.totality
module Tot = language-operational.totality Sig Alg-inst.Alg Dep.sort-width
module TotOp = Tot.WithOp Dep.op-rel

import language-operational.instrument
module Instr = language-operational.instrument Sig Alg-inst.Alg Dep.sort-width
module InstrOp = Instr.WithOp Dep.op-rel
