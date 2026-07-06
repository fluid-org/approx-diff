{-# OPTIONS --prop --postfix-projections --safe #-}

-- Use-counting analysis of the weighted-sum query, at the counting semiring: every operation has
-- unit coefficients, so a Jacobian entry counts the paths from an input to an output. The price of
-- the queried label is used twice, and the count survives the cancellation that zeroes the
-- rational derivative, because nothing cancels in a positive semiring.
module example-counting-total where

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

open import Level using (lift; 0ℓ)
open import Data.Unit renaming (tt to ·) using ()
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ)
open import Data.Integer using (+_; -[1+_])
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _/_)
open import prop-setoid using (Setoid)
open Setoid using (Carrier)
open import example-signature ℚ using (Sig; number; label; approx)
import example
module Ex = example ℚ
open Ex.ex using (total)
open import language-syntax Sig hiding (_,_)
open import label using (a; b)
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
open ho-model-sd-semimod.interp-sd semiring-N.semiring Sig D.BaseInterp1
open SDSemiMod-ℕ using (conjugate)

open indexed-family._⇒f_
open SemiMod-ℕ._⇒_

input : ⟦ (list (base label [×] base number)) [×] (base number [×] base number) ⟧ty .idx .Carrier
input = (3 , (a , + 3 / 1) , (b , 1ℚ) , (a , -[1+ 2 ] / 1) , _) , (+ 2 / 1 , + 5 / 1)

input-ty : first-order-data ((list (base label [×] base number)) [×] (base number [×] base number))
input-ty = list (base label [×] base number) [×] (base number [×] base number)

-- One use of the first quantity reaches the output once.
test-fwd-q₁ : fwd (total a) (_ , input)
                (lift · , ((lift · , 1) , (lift · , 0) , (lift · , 0) , _) , (0 , 0))
              ≡ 1
test-fwd-q₁ = refl

-- The price of label a is used twice: its uses reach the output along both selected rows, and the
-- counts add where the rational contributions cancelled.
test-fwd-price-a : fwd (total a) (_ , input)
                     (lift · , ((lift · , 0) , (lift · , 0) , (lift · , 0) , _) , (1 , 0))
                   ≡ 2
test-fwd-price-a = refl

-- Backward derivative of the output: use-counts for every position.
test-bwd : conjugate (ty (unit [×] input-ty) (_ , input)) (ty (base number) 0ℚ)
             (mor (total a) (_ , input)) .func 1
           ≡ (lift · , ((lift · , 1) , (lift · , 0) , (lift · , 1) , lift ·) , (2 , 0))
test-bwd = refl
