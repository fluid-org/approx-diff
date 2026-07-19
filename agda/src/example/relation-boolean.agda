{-# OPTIONS --prop --postfix-projections --safe #-}

-- Instantiation of the logical relation at the example signature: Boolean dependency model over rational
-- data.
module example.relation-boolean where

open import Level using (lift)
open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)
open import Data.Rational using (ℚ)
open import categories using (Category)
open import commutative-semiring using (CommutativeSemiring)
import cmon-enriched
import semimodule
import semiring-Q
import two
import matrix
import matrix-semimod-action
import matrix-embedding-semimod
import language-operational.logical-relation
open import example.signature ℚ
  using (Sig; sort; number; label; approx; op; lit; add; mult; lbl;
         approx-unit; approx-mult)
import example.algebra
import example.dependency

module SemiMod-𝟚 = semimodule two.semiring
module Dep = example.dependency

private
  module Num = CommutativeSemiring semiring-Q.semiring

-- Value-level algebra: rational arithmetic, trivial approx carrier.
module Alg-inst = example.algebra ℚ Num._+_ Num._·_ ⊤ tt (λ _ _ → tt)

sort-width : sort → ℕ
sort-width number = 1
sort-width label  = 0
sort-width approx = 1

module MSA = matrix-semimod-action two.semiring
module LR = language-operational.logical-relation Sig Alg-inst.Alg Dep.D.BaseInterp1 sort-width

open import language-syntax Sig using (base)
open import language-operational.evaluation-mat Sig Alg-inst.Alg two.semiring sort-width using (bases-width)

private
  module M𝟚 = matrix.Mat two.semiring
  module MES𝟚 = matrix-embedding-semimod two.semiring
  open cmon-enriched using (Biproduct)

sort-embed : ∀ s → Alg-inst.sort-val s → LR.Point (base s)
sort-embed number q = q
sort-embed label  l = l
sort-embed approx _ = lift tt

sort-can : ∀ s (c : Alg-inst.sort-val s) →
           Category._⇒_ SemiMod-𝟚.cat (MES𝟚.X^ (sort-width s))
                        (LR.Fibre (base s) (sort-embed s c))
sort-can number _ = Biproduct.p₁ (SemiMod-𝟚.biproduct SemiMod-𝟚.𝕀 SemiMod-𝟚.𝟘)
sort-can label  _ = SemiMod-𝟚.ε-map _ _
sort-can approx _ = Biproduct.p₁ (SemiMod-𝟚.biproduct SemiMod-𝟚.𝕀 SemiMod-𝟚.𝟘)

op-mat : ∀ {is o'} → op is o' →
         Category._⇒_ M𝟚.cat (bases-width is) (sort-width o')
op-mat (lit n)     = λ i ()
op-mat add         = λ i j → two.I
op-mat mult        = λ i j → two.I
op-mat (lbl l)     = λ ()
op-mat approx-unit = λ i ()
op-mat approx-mult = λ i j → two.I

module Inst = LR.WithAgreement sort-embed sort-can op-mat MSA.mat-mor

-- The fundamental property, specialised to this instantiation.
FP : Set
FP = Inst.FundamentalProperty

-- Totality, the evaluator and the instrumentation, at the same model.
import language-operational.totality
module Tot = language-operational.totality Sig Alg-inst.Alg two.semiring sort-width
module TotOp = Tot.WithOp op-mat

import language-operational.instrument
module Instr = language-operational.instrument Sig Alg-inst.Alg two.semiring sort-width
module InstrOp = Instr.WithOp op-mat
