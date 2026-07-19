{-# OPTIONS --prop --postfix-projections --safe #-}

-- Instantiation of the logical relation at the example signature: Boolean
-- dependency model over rational data.
module example.relation-boolean where

open import Level using (0ℓ; lift)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_)
open import Data.Rational using (ℚ; 0ℚ)
open import categories using (Category; HasInitial; HasProducts; HasTerminal)
open import commutative-semiring using (CommutativeSemiring)
open import prop-setoid using (Setoid)
import cmon-enriched
import prop-setoid
import semimodule
import sd-semimodule
import semiring-Q
import two
import prop
import matrix
import matrix-semimod-action
import matrix-embedding-semimod
import logical-relation
open import signature using (Model)
open import example.signature ℚ
  using (Sig; sort; number; label; approx; op; lit; add; mult; lbl;
         approx-unit; approx-mult)
import example.algebra
import example.signature-interpretation
import ho-model-sd-semimod

module SDSemiMod-𝟚 = sd-semimodule two.semiring
module SemiMod-𝟚 = semimodule two.semiring
open cmon-enriched.CMonEnriched SemiMod-𝟚.cmon-enriched using (_+m_)

Approx : Category.obj SDSemiMod-𝟚.cat
Approx = SDSemiMod-𝟚.𝕀

approx-unitm : Category._⇒_ SDSemiMod-𝟚.cat (HasTerminal.witness SDSemiMod-𝟚.terminal) Approx
approx-unitm = HasInitial.from-initial SDSemiMod-𝟚.initial {Approx}

approx-conjunctm : Category._⇒_ SDSemiMod-𝟚.cat (HasProducts.prod SDSemiMod-𝟚.products Approx Approx) Approx
approx-conjunctm =
  HasProducts.p₁ SDSemiMod-𝟚.products {Approx} {Approx}
    +m HasProducts.p₂ SDSemiMod-𝟚.products {Approx} {Approx}

private
  module Num = CommutativeSemiring semiring-Q.semiring
  open prop-setoid._⇒_

  num-add : prop-setoid._⇒_ (prop-setoid.⊗-setoid semiring-Q.setoid semiring-Q.setoid) semiring-Q.setoid
  num-add .func (x , y) = x Num.+ y
  num-add .func-resp-≈ e = Num.+-cong (prop.proj₁ e) (prop.proj₂ e)

  num-mult : prop-setoid._⇒_ (prop-setoid.⊗-setoid semiring-Q.setoid semiring-Q.setoid) semiring-Q.setoid
  num-mult .func (x , y) = x Num.· y
  num-mult .func-resp-≈ e = Num.·-cong (prop.proj₁ e) (prop.proj₂ e)

open example.signature-interpretation SDSemiMod-𝟚.cat SDSemiMod-𝟚.products SDSemiMod-𝟚.terminal
  Approx approx-unitm approx-conjunctm semiring-Q.setoid num-add num-mult

private
  unit-c : ℚ → ℚ → Category._⇒_ SDSemiMod-𝟚.cat Approx Approx
  unit-c _ _ = Category.id SDSemiMod-𝟚.cat Approx

  unit-c-cong : ∀ {x x' y y'} → Setoid._≈_ semiring-Q.setoid x x' → Setoid._≈_ semiring-Q.setoid y y' →
                Category._≈_ SemiMod-𝟚.cat (unit-c x y) (unit-c x' y')
  unit-c-cong _ _ = Category.≈-refl SemiMod-𝟚.cat {f = unit-c 0ℚ 0ℚ}

module D = BinDeriv unit-c unit-c unit-c unit-c unit-c-cong unit-c-cong unit-c-cong unit-c-cong

-- Value-level algebra: rational arithmetic, trivial approx carrier.
module Alg-inst = example.algebra ℚ Num._+_ Num._·_ ⊤ tt (λ _ _ → tt)

sort-width : sort → ℕ
sort-width number = 1
sort-width label  = 0
sort-width approx = 1

module MSA = matrix-semimod-action two.semiring
module LR = logical-relation two.semiring Sig Alg-inst.Alg D.BaseInterp1 sort-width

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
