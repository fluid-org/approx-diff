{-# OPTIONS --prop --postfix-projections --safe #-}

-- Instantiation of the logical relation at the example signature: Boolean dependency model over rational
-- data.
module example.relation-boolean where

open import Level using (0ℓ)
open import Data.Nat using (ℕ)
open import Data.Rational using (ℚ)
open import categories using (Category)
open import Relation.Binary.PropositionalEquality using (sym) renaming (subst to ≡-subst)
open import language-operational.algebra using (Algebra)
import ho-model-boolalg-sd-semimod
import two
import matrix
import matrix-embedding-semimod
import language-operational.logical-relation
open import example.signature ℚ using (Sig; sort; number; label; op)
import example.dependency

module Dep = example.dependency

private
  module H = ho-model-boolalg-sd-semimod two.semiring two.semiring-boolean
  module MES = matrix-embedding-semimod two.semiring

-- Value-level algebra, by projection from the model.
module Alg-inst = Dep.Alg-inst

module LR = language-operational.logical-relation Sig Dep.D.BaseInterp1

pres : LR.Presentation
pres = record { sort-width = Dep.sort-width ; sort-can = sort-can ; op-rel = Dep.op-rel }
  where
  -- Uniform in the sort: each base fibre is the free object of its width, transported along the
  -- agreement between the Boolean and semimodule free objects.
  sort-can : ∀ s (c : Alg-inst.sort-val s) → _
  sort-can s _ =
    ≡-subst (λ M → Category._⇒_ MES.SDSemiMod.SemiMod.cat (MES.X^ (Dep.sort-width s)) (MES.SDSemiMod.SelfDual.obj M))
            (sym (H.BoolAlg.selfDual-S^ (Dep.sort-width s)))
            (MES.X^≅S^ (Dep.sort-width s) .Category.Iso.fwd)

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
