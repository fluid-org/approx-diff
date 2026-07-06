{-# OPTIONS --prop --postfix-projections --safe #-}

-- Test harness for the rationals (AD) model with the value-carrying base interpretation
-- (BaseInterp1), over the self-dual semimodules as first-order model.
module example-rationals where

open import categories using (Category; HasInitial; HasProducts; HasTerminal)
import cmon-enriched
import prop
import semimodule
import sd-semimodule
import ho-model-sd-semimod
import indexed-family
import semiring-Q

open import Level using (lift; 0ℓ) public
open import Data.Unit renaming (tt to ·) using () public
open import Data.Product using (_,_) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl) public
open import prop using (liftS) public
open import Data.Rational using (ℚ; 0ℚ; 1ℚ) public
open import prop-setoid using (Setoid)
open Setoid using (Carrier) public
open import commutative-monoid using (CommutativeMonoid)
open import commutative-semiring using (CommutativeSemiring)
open import example-signature ℚ using (Sig; number; label; approx) public
import example
open import language-syntax Sig hiding (_,_) public
module Ex = example ℚ
open Ex.ex public

-- Model instantiation.

module SDSemiMod-ℚ = sd-semimodule semiring-Q.semiring
module SemiMod-ℚ = semimodule semiring-Q.semiring
module Scalars = CommutativeSemiring semiring-Q.semiring
open cmon-enriched.CMonEnriched SemiMod-ℚ.cmon-enriched using (_+m_)

Approx : Category.obj SDSemiMod-ℚ.cat
Approx = SDSemiMod-ℚ.𝕀

approx-unit : Category._⇒_ SDSemiMod-ℚ.cat (HasTerminal.witness SDSemiMod-ℚ.terminal) Approx
approx-unit = HasInitial.from-initial SDSemiMod-ℚ.initial {Approx}
approx-conjunct : Category._⇒_ SDSemiMod-ℚ.cat (HasProducts.prod SDSemiMod-ℚ.products Approx Approx) Approx
approx-conjunct = HasProducts.p₁ SDSemiMod-ℚ.products {Approx} {Approx}
        +m HasProducts.p₂ SDSemiMod-ℚ.products {Approx} {Approx}

private
  module Add = CommutativeMonoid semiring-Q.additive
  module Mul = CommutativeMonoid semiring-Q.multiplicative

  num-zero : prop-setoid._⇒_ (prop-setoid.𝟙 {0ℓ} {0ℓ}) semiring-Q.setoid
  num-zero = record { func = λ _ → 0ℚ ; func-resp-≈ = λ _ → Scalars.refl }

  num-add : prop-setoid._⇒_ (prop-setoid.⊗-setoid semiring-Q.setoid semiring-Q.setoid) semiring-Q.setoid
  num-add = record { func = λ (x , y) → Add._+_ x y ; func-resp-≈ = λ e → Add.+-cong (prop.proj₁ e) (prop.proj₂ e) }

  num-mult : prop-setoid._⇒_ (prop-setoid.⊗-setoid semiring-Q.setoid semiring-Q.setoid) semiring-Q.setoid
  num-mult = record { func = λ (x , y) → Mul._+_ x y ; func-resp-≈ = λ e → Mul.+-cong (prop.proj₁ e) (prop.proj₂ e) }

  -- Multiplication by c as a linear endomorphism of the scalars.
  scalar : ℚ → Category._⇒_ SDSemiMod-ℚ.cat Approx Approx
  scalar c .SemiMod-ℚ._⇒_.*→* = record { func = λ x → c Scalars.· x ; func-resp-≈ = λ e → Scalars.·-cong (Scalars.refl {c}) e }
  scalar c .SemiMod-ℚ._⇒_.preserve-ze = Scalars.ε-annihilᵣ {c}
  scalar c .SemiMod-ℚ._⇒_.preserve-+ {x} {y} = Scalars.·-+-distribₗ {c} {x} {y}
  scalar c .SemiMod-ℚ._⇒_.preserve-· {s} {x} =
    Scalars.trans (Scalars.sym (Scalars.·-assoc {c} {s} {x}))
      (Scalars.trans (Scalars.·-cong (Scalars.·-comm {c} {s}) Scalars.refl) (Scalars.·-assoc {s} {c} {x}))

  scalar-cong : ∀ {x y} → Setoid._≈_ semiring-Q.setoid x y → Category._≈_ SemiMod-ℚ.cat (scalar x) (scalar y)
  scalar-cong e = record { *≈* = record { func-eq = λ u≈v → Scalars.·-cong e u≈v } }

open import example-signature-interpretation SDSemiMod-ℚ.cat SDSemiMod-ℚ.products SDSemiMod-ℚ.terminal
  Approx approx-unit approx-conjunct semiring-Q.setoid num-zero num-add num-mult public
module D = Deriv scalar scalar-cong
open ho-model-sd-semimod.interp-sd semiring-Q.semiring Sig D.BaseInterp1 public
open SDSemiMod-ℚ public using (conjugate)

open indexed-family._⇒f_ public
open SemiMod-ℚ._⇒_ public


