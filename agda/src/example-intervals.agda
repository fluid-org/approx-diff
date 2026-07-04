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

open import Level using (lift; 0ℓ)
open import Data.Unit renaming (tt to ·) using ()
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _/_)
open import Data.Integer using (+_; -[1+_])
open import commutative-semiring using (CommutativeSemiring)
open import prop using (liftS)
open import Data.Integer using (+_)
open import prop-setoid using (Setoid)
open Setoid using (Carrier)
open import example-signature using (Sig; number; label; approx)
import example
open import language-syntax Sig hiding (_,_)
open example.ex using (query)
open import label using (a; b)
open semiring-Q-tropical-add using (∞; fin)

-- Model instantiation.
module SDSemiMod-ℚ∞ = sd-semimodule semiring-Q-tropical-add.semiring
module SemiMod-ℚ∞ = semimodule semiring-Q-tropical-add.semiring
open cmon-enriched.CMonEnriched SemiMod-ℚ∞.cmon-enriched using (_+m_; εm)

Approxm : Category.obj SDSemiMod-ℚ∞.cat
Approxm = SDSemiMod-ℚ∞._⊕_ SDSemiMod-ℚ∞.𝕀 SDSemiMod-ℚ∞.𝕀

unitm : Category._⇒_ SDSemiMod-ℚ∞.cat (HasTerminal.witness SDSemiMod-ℚ∞.terminal) Approxm
unitm = HasInitial.from-initial SDSemiMod-ℚ∞.initial {Approxm}
conjunctm : Category._⇒_ SDSemiMod-ℚ∞.cat (HasProducts.prod SDSemiMod-ℚ∞.products Approxm Approxm) Approxm
conjunctm = HasProducts.p₁ SDSemiMod-ℚ∞.products {Approxm} {Approxm}
        +m HasProducts.p₂ SDSemiMod-ℚ∞.products {Approxm} {Approxm}

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

open import example-signature-interpretation SDSemiMod-ℚ∞.cat SDSemiMod-ℚ∞.products SDSemiMod-ℚ∞.terminal
  Approxm unitm conjunctm semiring-Q.setoid num-zero num-add num-mult

-- Multiplication admits no min-plus-linear perturbation bound; the zero map (constantly ∞) records
-- the absence of a bound.
private
  coeff-t : ℚ → Category._⇒_ SDSemiMod-ℚ∞.cat Approxm Approxm
  coeff-t _ = εm
  coeff-cong-t : ∀ {x y} → Setoid._≈_ semiring-Q.setoid x y → Category._≈_ SemiMod-ℚ∞.cat (coeff-t x) (coeff-t y)
  coeff-cong-t {x} _ = Category.≈-refl SemiMod-ℚ∞.cat {f = coeff-t x}

module D = Deriv coeff-t coeff-cong-t
open ho-model-sd-semimod.interp-sd semiring-Q-tropical-add.semiring Sig D.BaseInterp1
open SDSemiMod-ℚ∞ using (conjugate)
open SemiMod-ℚ∞._⇒_

input : ⟦ list (base label [×] base number) ⟧ty .idx .Carrier
input = 3 , (a , + 3 / 1) , (b , 1ℚ) , (a , -[1+ 2 ] / 1) , _

input-ty : first-order-data (list (base label [×] base number))
input-ty = list (base label [×] base number)

-- An interval [l, u] around q becomes the pair of perturbation bounds (q - l , u - q); ∞ is the
-- absent (bottom) approximation.
-- Query a sums #1 and #3 (values 3 and -3, output 0); the forward derivative combines their
-- perturbation bounds by min:
--   ( min(1/2, 1/5) , min(0, 1/2) ) = (1/5 , 0) = the interval [-1/5, 0] around 0.
test-addᵀ : fwd (query a) (_ , input)
              (lift · , (lift · , (fin (+ 1 / 2) , fin 0ℚ))
                      , (lift · , (∞ , ∞))
                      , (lift · , (fin (+ 1 / 5) , fin (+ 1 / 2))) , _)
            ≡ (fin (+ 1 / 5) , fin 0ℚ)
test-addᵀ = refl

bwd-slice : _ → _
bwd-slice r =
  conjugate (ty (unit [×] input-ty) (_ , input)) (ty (base number) 0ℚ)
            (mor (query a) (_ , input)) .func r

-- Feeding back output interval [-1/10, 1/10] around 0 = perturbation bounds (1/10, 1/10). The
-- conjugate copies it to the two label-a inputs (#1, #3) and leaves ∞ elsewhere:
--   #1 around 3:  (1/10, 1/10) = [29/10, 31/10]
--   #2 (label b): (∞, ∞)       = no constraint
--   #3 around -3: (1/10, 1/10) = [-31/10, -29/10]
test-bwd : bwd-slice (fin (+ 1 / 10) , fin (+ 1 / 10))
           ≡ (lift · , (lift · , (fin (+ 1 / 10) , fin (+ 1 / 10)))
                     , (lift · , (∞ , ∞))
                     , (lift · , (fin (+ 1 / 10) , fin (+ 1 / 10))) , lift ·)
test-bwd = refl
