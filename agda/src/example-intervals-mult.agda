{-# OPTIONS --prop --postfix-projections --safe #-}

-- Relative perturbation bounds for the weighted-sum query, at the min-times tropical semiring: a
-- scalar bounds the relative error of a value, so multiplication passes bounds through unchanged
-- (unit coefficients) while addition scales them by the condition factor |x| / |x + y|, infinite
-- at the refund's exact cancellation.
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

open import Level using (lift; 0ℓ)
open import Data.Unit renaming (tt to ·) using ()
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)
open import Data.Integer using (+_; -[1+_])
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _/_; _÷_; ∣_∣; _≟_; ≢-nonZero)
open import Data.Rational.Properties using (∣-∣-nonNeg)
open import prop-setoid using (Setoid)
open Setoid using (Carrier)
open import example-signature ℚ using (Sig; number; label; approx)
import example
open import language-syntax Sig hiding (_,_)
module Ex = example ℚ
open Ex.ex using (total)
open import label using (a; b)
open import prop using (liftS)
import semiring-Q
open semiring-Q-tropical-mult using (ℚ≥0∞; ∞; fin)

-- Model instantiation.
module SDSemiMod-Rel = sd-semimodule semiring-Q-tropical-mult.semiring
module SemiMod-Rel = semimodule semiring-Q-tropical-mult.semiring
module Scalars = CommutativeSemiring semiring-Q-tropical-mult.semiring
open cmon-enriched.CMonEnriched SemiMod-Rel.cmon-enriched using (_+m_)

Approxm : Category.obj SDSemiMod-Rel.cat
Approxm = SDSemiMod-Rel.𝕀

unitm : Category._⇒_ SDSemiMod-Rel.cat (HasTerminal.witness SDSemiMod-Rel.terminal) Approxm
unitm = HasInitial.from-initial SDSemiMod-Rel.initial {Approxm}
conjunctm : Category._⇒_ SDSemiMod-Rel.cat (HasProducts.prod SDSemiMod-Rel.products Approxm Approxm) Approxm
conjunctm = HasProducts.p₁ SDSemiMod-Rel.products {Approxm} {Approxm}
        +m HasProducts.p₂ SDSemiMod-Rel.products {Approxm} {Approxm}

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
  Approxm unitm conjunctm semiring-Q.setoid num-zero num-add num-mult

private
  -- Multiplication by a scalar as a linear endomorphism of the scalars.
  scalar : ℚ≥0∞ → Category._⇒_ SDSemiMod-Rel.cat Approxm Approxm
  scalar c .SemiMod-Rel._⇒_.*→* = record { func = λ x → c Scalars.· x ; func-resp-≈ = λ e → Scalars.·-cong (Scalars.refl {c}) e }
  scalar c .SemiMod-Rel._⇒_.preserve-ze = Scalars.ε-annihilᵣ {c}
  scalar c .SemiMod-Rel._⇒_.preserve-+ {x} {y} = Scalars.·-+-distribₗ {c} {x} {y}
  scalar c .SemiMod-Rel._⇒_.preserve-· {s} {x} =
    Scalars.trans (Scalars.sym (Scalars.·-assoc {c} {s} {x}))
      (Scalars.trans (Scalars.·-cong (Scalars.·-comm {c} {s}) (Scalars.refl {x})) (Scalars.·-assoc {s} {c} {x}))

  -- The condition factor |x| / |x + y|, infinite at exact cancellation.
  relfac : ℚ → ℚ → ℚ≥0∞
  relfac x y with Num._+_ x y ≟ 0ℚ
  ... | yes _ = ∞
  ... | no ne = fin ∣ _÷_ x (Num._+_ x y) ⦃ ≢-nonZero ne ⦄ ∣ ⦃ ∣-∣-nonNeg (_÷_ x (Num._+_ x y) ⦃ ≢-nonZero ne ⦄) ⦄

  add-c₁ add-c₂ mult-c : ℚ → ℚ → Category._⇒_ SDSemiMod-Rel.cat Approxm Approxm
  add-c₁ x y = scalar (relfac x y)
  add-c₂ x y = scalar (relfac y x)
  mult-c _ _ = Category.id SDSemiMod-Rel.cat Approxm

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
open ho-model-sd-semimod.interp-sd semiring-Q-tropical-mult.semiring Sig D.BaseInterp1
open SDSemiMod-Rel using (conjugate)

open indexed-family._⇒f_
open SemiMod-Rel._⇒_

input : ⟦ (list (base label [×] base number)) [×] (base number [×] base number) ⟧ty .idx .Carrier
input = (3 , (a , + 3 / 1) , (b , 1ℚ) , (a , -[1+ 2 ] / 1) , _) , (+ 2 / 1 , + 5 / 1)

input-ty : first-order-data ((list (base label [×] base number)) [×] (base number [×] base number))
input-ty = list (base label [×] base number) [×] (base number [×] base number)

-- Multiplication passes relative bounds through unchanged: a bound on price b reaches the output
-- of total b intact.
test-price-b : fwd (total b) (_ , input)
                 (lift · , ((lift · , ∞) , (lift · , ∞) , (lift · , ∞) , _) , (∞ , fin (+ 1 / 10)))
               ≡ fin (+ 1 / 10)
test-price-b = refl

-- Likewise a bound on the selected quantity.
test-q₂ : fwd (total b) (_ , input)
            (lift · , ((lift · , ∞) , (lift · , fin (+ 1 / 10)) , (lift · , ∞) , _) , (∞ , ∞))
          ≡ fin (+ 1 / 10)
test-q₂ = refl

-- At total a the contributions cancel exactly, so the condition factor is infinite and no
-- relative bound survives.
test-cancel : fwd (total a) (_ , input)
                (lift · , ((lift · , fin (+ 1 / 10)) , (lift · , ∞) , (lift · , ∞) , _) , (∞ , ∞))
              ≡ ∞
test-cancel = refl

-- The backward derivative of total b: the bound propagates to the selected quantity and its
-- price, and nothing else is constrained.
test-bwd : conjugate (ty (unit [×] input-ty) (_ , input)) (ty (base number) (+ 5 / 1))
             (mor (total b) (_ , input)) .func (fin (+ 1 / 10))
           ≡ (lift · , ((lift · , ∞) , (lift · , fin (+ 1 / 10)) , (lift · , ∞) , lift ·) , (∞ , fin (+ 1 / 10)))
test-bwd = refl
