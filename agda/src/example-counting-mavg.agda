{-# OPTIONS --prop --postfix-projections --safe #-}

-- Use-counting analysis of the moving-average example, at the counting semiring: every operation
-- has unit coefficients, so a Jacobian entry counts the paths from an input to an output. The
-- backward derivative of the full output returns the multiplicities (1, 2, 2, 1).
module example-counting-mavg where

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
open import Data.Integer using (+_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _/_)
open import prop-setoid using (Setoid)
open Setoid using (Carrier)
open import example-signature ℚ using (Sig; number; label; approx)
import example
module Ex = example ℚ
open Ex.ex using (mavg)
open import language-syntax Sig hiding (_,_)
open import prop using (liftS)

-- Model instantiation: counting approximations over rational data.
module SDSemiMod-ℕ = sd-semimodule semiring-N.semiring
module SemiMod-ℕ = semimodule semiring-N.semiring
open cmon-enriched.CMonEnriched SemiMod-ℕ.cmon-enriched using (_+m_)

Approxm : Category.obj SDSemiMod-ℕ.cat
Approxm = SDSemiMod-ℕ.𝕀

unitm : Category._⇒_ SDSemiMod-ℕ.cat (HasTerminal.witness SDSemiMod-ℕ.terminal) Approxm
unitm = HasInitial.from-initial SDSemiMod-ℕ.initial {Approxm}
conjunctm : Category._⇒_ SDSemiMod-ℕ.cat (HasProducts.prod SDSemiMod-ℕ.products Approxm Approxm) Approxm
conjunctm = HasProducts.p₁ SDSemiMod-ℕ.products {Approxm} {Approxm}
        +m HasProducts.p₂ SDSemiMod-ℕ.products {Approxm} {Approxm}

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
  Approxm unitm conjunctm semiring-Q.setoid num-zero num-add num-mult

-- Use-counting coefficients: every argument of every operation counts as one use.
private
  unit-c : ℚ → ℚ → Category._⇒_ SDSemiMod-ℕ.cat Approxm Approxm
  unit-c _ _ = Category.id SDSemiMod-ℕ.cat Approxm

  unit-c-cong : ∀ {x x' y y'} → Setoid._≈_ semiring-Q.setoid x x' → Setoid._≈_ semiring-Q.setoid y y' →
                Category._≈_ SemiMod-ℕ.cat (unit-c x y) (unit-c x' y')
  unit-c-cong _ _ = Category.≈-refl SemiMod-ℕ.cat {f = unit-c 0ℚ 0ℚ}

module D = BinDeriv unit-c unit-c unit-c unit-c unit-c-cong unit-c-cong unit-c-cong unit-c-cong
open ho-model-sd-semimod.interp-sd semiring-N.semiring Sig D.BaseInterp1
open SDSemiMod-ℕ using (conjugate)

open indexed-family._⇒f_
open SemiMod-ℕ._⇒_

half : ℚ
half = + 1 / 2

input : ⟦ ((base number [×] base number) [×] base number) [×] base number ⟧ty .idx .Carrier
input = ((1ℚ , + 2 / 1) , + 4 / 1) , + 8 / 1

input-ty : first-order-data (((base number [×] base number) [×] base number) [×] base number)
input-ty = ((base number [×] base number) [×] base number) [×] base number

output-ty : first-order-data ((base number [×] base number) [×] base number)
output-ty = (base number [×] base number) [×] base number

-- One use of the first input reaches only the first output.
test-fwd-first : fwd (mavg half) (_ , input) (lift · , (((1 , 0) , 0) , 0))
                 ≡ ((1 , 0) , 0)
test-fwd-first = refl

-- One use of a shared input reaches both adjacent outputs.
test-fwd-shared : fwd (mavg half) (_ , input) (lift · , (((0 , 1) , 0) , 0))
                  ≡ ((1 , 1) , 0)
test-fwd-shared = refl

-- Backward derivative of the full output: each input's total number of uses.
test-bwd : conjugate (ty (unit [×] input-ty) (_ , input))
             (ty output-ty ((+ 3 / 2 , + 3 / 1) , + 6 / 1))
             (mor (mavg half) (_ , input)) .func ((1 , 1) , 1)
           ≡ (lift · , (((1 , 2) , 2) , 1))
test-bwd = refl
