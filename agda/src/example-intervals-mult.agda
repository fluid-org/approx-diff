{-# OPTIONS --prop --postfix-projections --safe #-}

-- Test harness for relative perturbation bounds, at the min-times tropical semiring: a scalar
-- bounds the relative error of a value, so multiplication passes bounds through unchanged (unit
-- coefficients) while addition scales them by the condition factor |x| / |x + y|, infinite at
-- exact cancellation.
module example-intervals-mult where

open import categories using (Category; HasInitial; HasProducts; HasTerminal)
import cmon-enriched
import prop
import semimodule
import sd-semimodule
import ho-model-sd-semimod
import semiring-Q-tropical-mult
import indexed-family
open import commutative-semiring using (CommutativeSemiring)

open import Level using (lift; 0ℓ) public
open import Data.Unit renaming (tt to ·) using () public
open import Data.Product using (_,_) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl) public
open import Relation.Nullary using (yes; no)
open import Data.Integer using (+_; -[1+_]) public
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _/_) public
open import Data.Rational using (_÷_; ∣_∣; ≢-nonZero) renaming (_≟_ to _≟ℚ_)
open import Data.Nat.Base public using (nonZero)
open import Data.Integer.Base public using (nonNeg)
open import Data.Rational.Properties using (∣-∣-nonNeg)
open import prop-setoid using (Setoid)
open Setoid using (Carrier) public
open import example-signature ℚ using (Sig; number; label; approx) public
import example
open import language-syntax Sig hiding (_,_) public
module Ex = example ℚ
open Ex.ex public
open import label using (a; b) public
open import prop using (liftS)
import semiring-Q
open semiring-Q-tropical-mult public using (ℚ≥0∞; ∞; fin)

-- Model instantiation.
module SDSemiMod-Rel = sd-semimodule semiring-Q-tropical-mult.semiring
module SemiMod-Rel = semimodule semiring-Q-tropical-mult.semiring
module Scalars = CommutativeSemiring semiring-Q-tropical-mult.semiring
open cmon-enriched.CMonEnriched SemiMod-Rel.cmon-enriched using (_+m_)

Approx : Category.obj SDSemiMod-Rel.cat
Approx = SDSemiMod-Rel.𝕀

approx-unit : Category._⇒_ SDSemiMod-Rel.cat (HasTerminal.witness SDSemiMod-Rel.terminal) Approx
approx-unit = HasInitial.from-initial SDSemiMod-Rel.initial {Approx}
approx-conjunct : Category._⇒_ SDSemiMod-Rel.cat (HasProducts.prod SDSemiMod-Rel.products Approx Approx) Approx
approx-conjunct = HasProducts.p₁ SDSemiMod-Rel.products {Approx} {Approx}
        +m HasProducts.p₂ SDSemiMod-Rel.products {Approx} {Approx}

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

open import example-signature-interpretation SDSemiMod-Rel.cat SDSemiMod-Rel.products SDSemiMod-Rel.terminal
  Approx approx-unit approx-conjunct semiring-Q.setoid num-zero num-add num-mult

private
  -- Multiplication by a scalar as a linear endomorphism of the scalars.
  scalar : ℚ≥0∞ → Category._⇒_ SDSemiMod-Rel.cat Approx Approx
  scalar c .SemiMod-Rel._⇒_.*→* = record { func = λ x → c Scalars.· x ; func-resp-≈ = λ e → Scalars.·-cong (Scalars.refl {c}) e }
  scalar c .SemiMod-Rel._⇒_.preserve-ze = Scalars.ε-annihilᵣ {c}
  scalar c .SemiMod-Rel._⇒_.preserve-+ {x} {y} = Scalars.·-+-distribₗ {c} {x} {y}
  scalar c .SemiMod-Rel._⇒_.preserve-· {s} {x} =
    Scalars.trans (Scalars.sym (Scalars.·-assoc {c} {s} {x}))
      (Scalars.trans (Scalars.·-cong (Scalars.·-comm {c} {s}) (Scalars.refl {x})) (Scalars.·-assoc {s} {c} {x}))

  -- The condition factor |x| / |x + y|, infinite at exact cancellation.
  relfac : ℚ → ℚ → ℚ≥0∞
  relfac x y with Num._+_ x y ≟ℚ 0ℚ
  ... | yes _ = ∞
  ... | no ne = fin ∣ _÷_ x (Num._+_ x y) ⦃ ≢-nonZero ne ⦄ ∣ ⦃ ∣-∣-nonNeg (_÷_ x (Num._+_ x y) ⦃ ≢-nonZero ne ⦄) ⦄

  add-c₁ add-c₂ mult-c : ℚ → ℚ → Category._⇒_ SDSemiMod-Rel.cat Approx Approx
  add-c₁ x y = scalar (relfac x y)
  add-c₂ x y = scalar (relfac y x)
  mult-c _ _ = Category.id SDSemiMod-Rel.cat Approx

  add-c₁-cong : ∀ {x x' y y'} → Setoid._≈_ semiring-Q.setoid x x' → Setoid._≈_ semiring-Q.setoid y y' →
                Category._≈_ SemiMod-Rel.cat (add-c₁ x y) (add-c₁ x' y')
  add-c₁-cong {x} {_} {y} (liftS refl) (liftS refl) = Category.≈-refl SemiMod-Rel.cat {f = add-c₁ x y}

  add-c₂-cong : ∀ {x x' y y'} → Setoid._≈_ semiring-Q.setoid x x' → Setoid._≈_ semiring-Q.setoid y y' →
                Category._≈_ SemiMod-Rel.cat (add-c₂ x y) (add-c₂ x' y')
  add-c₂-cong {x} {_} {y} (liftS refl) (liftS refl) = Category.≈-refl SemiMod-Rel.cat {f = add-c₂ x y}

  mult-c-cong : ∀ {x x' y y'} → Setoid._≈_ semiring-Q.setoid x x' → Setoid._≈_ semiring-Q.setoid y y' →
                Category._≈_ SemiMod-Rel.cat (mult-c x y) (mult-c x' y')
  mult-c-cong _ _ = Category.≈-refl SemiMod-Rel.cat {f = mult-c 0ℚ 0ℚ}

module D = BinDeriv add-c₁ add-c₂ mult-c mult-c add-c₁-cong add-c₂-cong mult-c-cong mult-c-cong
open ho-model-sd-semimod.interp-sd semiring-Q-tropical-mult.semiring Sig D.BaseInterp1 public
open SDSemiMod-Rel public using (conjugate)

open indexed-family._⇒f_ public
open SemiMod-Rel._⇒_ public

