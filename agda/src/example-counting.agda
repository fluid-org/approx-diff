{-# OPTIONS --prop --postfix-projections --safe #-}

-- Test harness for the counting semiring: rational data, with unit coefficients, so a Jacobian
-- entry counts the paths from an input to an output.
module example-counting where

open import categories using (Category; HasInitial; HasProducts; HasTerminal)
import cmon-enriched
import prop
import semimodule
import sd-semimodule
import ho-model-sd-semimod
import semiring-N
import semiring-Q
import indexed-family
open import commutative-semiring using (CommutativeSemiring)

open import Level using (lift; 0ℓ) public
open import Data.Unit renaming (tt to ·) using () public
open import Data.Product using (_,_) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl) public
open import Data.Nat using (ℕ) public
open import Data.Nat.Base public using (nonZero)
open import Data.Integer using (+_; -[1+_]) public
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _/_) public
open import prop-setoid using (Setoid)
open Setoid using (Carrier) public
open import example-signature ℚ using (Sig; number; label; approx) public
import example
module Ex = example ℚ
open Ex.ex public
open import language-syntax Sig hiding (_,_) public
open import label using (a; b) public
open import prop using (liftS)

-- Model instantiation: counting approximations over rational data.
module SDSemiMod-ℕ = sd-semimodule semiring-N.semiring
module SemiMod-ℕ = semimodule semiring-N.semiring
open cmon-enriched.CMonEnriched SemiMod-ℕ.cmon-enriched using (_+m_)

Approx : Category.obj SDSemiMod-ℕ.cat
Approx = SDSemiMod-ℕ.𝕀

approx-unit : Category._⇒_ SDSemiMod-ℕ.cat (HasTerminal.witness SDSemiMod-ℕ.terminal) Approx
approx-unit = HasInitial.from-initial SDSemiMod-ℕ.initial {Approx}
approx-conjunct : Category._⇒_ SDSemiMod-ℕ.cat (HasProducts.prod SDSemiMod-ℕ.products Approx Approx) Approx
approx-conjunct = HasProducts.p₁ SDSemiMod-ℕ.products {Approx} {Approx}
        +m HasProducts.p₂ SDSemiMod-ℕ.products {Approx} {Approx}

private
  module Num = CommutativeSemiring semiring-Q.semiring

  num-zero : prop-setoid._⇒_ (prop-setoid.𝟙 {0ℓ} {0ℓ}) semiring-Q.setoid
  num-zero = record { func = λ _ → 0ℚ ; func-resp-≈ = λ _ → Num.refl }

  num-add : prop-setoid._⇒_ (prop-setoid.⊗-setoid semiring-Q.setoid semiring-Q.setoid) semiring-Q.setoid
  num-add = record { func = λ (x , y) → Num._+_ x y
                   ; func-resp-≈ = λ e → Num.+-cong (prop.proj₁ e) (prop.proj₂ e) }

  num-mult : prop-setoid._⇒_ (prop-setoid.⊗-setoid semiring-Q.setoid semiring-Q.setoid) semiring-Q.setoid
  num-mult = record { func = λ (x , y) → Num._·_ x y
                    ; func-resp-≈ = λ e → Num.·-cong (prop.proj₁ e) (prop.proj₂ e) }

open import example-signature-interpretation SDSemiMod-ℕ.cat SDSemiMod-ℕ.products SDSemiMod-ℕ.terminal
  Approx approx-unit approx-conjunct semiring-Q.setoid num-zero num-add num-mult

-- Use-counting coefficients: every argument of every operation counts as one use.
private
  unit-c : ℚ → ℚ → Category._⇒_ SDSemiMod-ℕ.cat Approx Approx
  unit-c _ _ = Category.id SDSemiMod-ℕ.cat Approx

  unit-c-cong : ∀ {x x' y y'} → Setoid._≈_ semiring-Q.setoid x x' → Setoid._≈_ semiring-Q.setoid y y' →
                Category._≈_ SemiMod-ℕ.cat (unit-c x y) (unit-c x' y')
  unit-c-cong _ _ = Category.≈-refl SemiMod-ℕ.cat {f = unit-c 0ℚ 0ℚ}

module D = BinDeriv unit-c unit-c unit-c unit-c unit-c-cong unit-c-cong unit-c-cong unit-c-cong
open ho-model-sd-semimod.interp-sd semiring-N.semiring Sig D.BaseInterp1 public
open SDSemiMod-ℕ public using (conjugate)

open indexed-family._⇒f_ public
open SemiMod-ℕ._⇒_ public

