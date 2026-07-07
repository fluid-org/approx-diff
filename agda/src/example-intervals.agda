{-# OPTIONS --prop --postfix-projections --safe #-}

-- Forward and backward analysis of the example query in the perturbation-bound model, over the
-- self-dual semimodules; numbers approximated by ℚ∞² (left, right perturbation bound).
module example-intervals where

open import categories using (Category; HasInitial; HasProducts; HasTerminal)
import cmon-enriched
import prop
import semimodule
import sd-semimodule
import ho-model-sd-semimod
import semiring-Q-tropical-add
import semiring-Q

open import Level using (lift; 0ℓ) public
open import Data.Unit renaming (tt to ·) using () public
open import Data.Product using (_,_) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl) public
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _/_) public
open import Data.Nat.Base public using (nonZero)
open import Data.Integer.Base public using (nonNeg)
open import Data.Integer using (+_; -[1+_]) public
open import commutative-semiring using (CommutativeSemiring)
open import prop using (liftS)
open import Data.Integer using (+_)
open import prop-setoid using (Setoid)
open Setoid using (Carrier) public
open import example-signature ℚ using (Sig; number; label; approx) public
import example
open import language-syntax Sig hiding (_,_) public
module Ex = example ℚ 0ℚ
open Ex.ex public
open import label using (a; b) public
open semiring-Q-tropical-add public using (∞; fin)

-- Model instantiation.
module SDSemiMod-ℚ∞ = sd-semimodule semiring-Q-tropical-add.semiring
module SemiMod-ℚ∞ = semimodule semiring-Q-tropical-add.semiring
open cmon-enriched.CMonEnriched SemiMod-ℚ∞.cmon-enriched using (_+m_; εm)

Approx : Category.obj SDSemiMod-ℚ∞.cat
Approx = SDSemiMod-ℚ∞._⊕_ SDSemiMod-ℚ∞.𝕀 SDSemiMod-ℚ∞.𝕀

approx-unit : Category._⇒_ SDSemiMod-ℚ∞.cat (HasTerminal.witness SDSemiMod-ℚ∞.terminal) Approx
approx-unit = HasInitial.from-initial SDSemiMod-ℚ∞.initial {Approx}
approx-conjunct : Category._⇒_ SDSemiMod-ℚ∞.cat (HasProducts.prod SDSemiMod-ℚ∞.products Approx Approx) Approx
approx-conjunct = HasProducts.p₁ SDSemiMod-ℚ∞.products {Approx} {Approx}
        +m HasProducts.p₂ SDSemiMod-ℚ∞.products {Approx} {Approx}

private
  module Num = CommutativeSemiring semiring-Q.semiring
  open prop-setoid._⇒_

  num-add : prop-setoid._⇒_ (prop-setoid.⊗-setoid semiring-Q.setoid semiring-Q.setoid) semiring-Q.setoid
  num-add .func (x , y) = x Num.+ y
  num-add .func-resp-≈ e = Num.+-cong (prop.proj₁ e) (prop.proj₂ e)

  num-mult : prop-setoid._⇒_ (prop-setoid.⊗-setoid semiring-Q.setoid semiring-Q.setoid) semiring-Q.setoid
  num-mult .func (x , y) = x Num.· y
  num-mult .func-resp-≈ e = Num.·-cong (prop.proj₁ e) (prop.proj₂ e)

open import example-signature-interpretation SDSemiMod-ℚ∞.cat SDSemiMod-ℚ∞.products SDSemiMod-ℚ∞.terminal
  Approx approx-unit approx-conjunct semiring-Q.setoid num-add num-mult

-- Multiplication admits no min-plus-linear perturbation bound; the zero map (constantly ∞) records
-- the absence of a bound.
private
  coeff-t : ℚ → Category._⇒_ SDSemiMod-ℚ∞.cat Approx Approx
  coeff-t _ = εm
  coeff-cong-t : ∀ {x y} → Setoid._≈_ semiring-Q.setoid x y → Category._≈_ SemiMod-ℚ∞.cat (coeff-t x) (coeff-t y)
  coeff-cong-t {x} _ = Category.≈-refl SemiMod-ℚ∞.cat {f = coeff-t x}

module D = Deriv coeff-t coeff-cong-t
open ho-model-sd-semimod.interp-sd semiring-Q-tropical-add.semiring Sig D.BaseInterp1 public
open SDSemiMod-ℚ∞ public using (conjugate)
open SemiMod-ℚ∞._⇒_ public

