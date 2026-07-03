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
import nat

open import Level using (lift; 0ℓ)
open import Data.Unit renaming (tt to ·) using ()
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Rational using (0ℚ; _/_)
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

open import example-signature-interpretation SDSemiMod-ℚ∞.cat SDSemiMod-ℚ∞.products SDSemiMod-ℚ∞.terminal
  Approxm unitm conjunctm nat.ℕₛ nat.zero-m nat.add nat.mult

-- Multiplication admits no min-plus-linear perturbation bound; the zero map (constantly ∞) records
-- the absence of a bound.
private
  coeff-t : nat.ℕ → Category._⇒_ SDSemiMod-ℚ∞.cat Approxm Approxm
  coeff-t _ = εm
  coeff-cong-t : ∀ {x y} → nat._≃_ x y → Category._≈_ SemiMod-ℚ∞.cat (coeff-t x) (coeff-t y)
  coeff-cong-t {x} _ = Category.≈-refl SemiMod-ℚ∞.cat {f = coeff-t x}

module D = Deriv coeff-t coeff-cong-t
open ho-model-sd-semimod.interp-sd semiring-Q-tropical-add.semiring Sig D.BaseInterp1
open SDSemiMod-ℚ∞ using (conjugate)
open SemiMod-ℚ∞._⇒_

input : ⟦ list (base label [×] base number) ⟧ty .idx .Carrier
input = 3 , (a , 0) , (b , 1) , (a , 1) , _

input-ty : first-order-data (list (base label [×] base number))
input-ty = list (base label [×] base number)

-- An interval [l, u] around q from the paper becomes the pair of perturbation bounds (q - l , u - q); ∞ is
-- the absent (bottom) approximation. So [4/5, 3/2] around 1 becomes (1/5, 1/2).
-- Query a sums #1 and #3; the forward slice combines their perturbation bounds by min:
--   ( min(1/2, 1/5) , min(0, 1/2) ) = (1/5 , 0) = the interval [4/5, 1] around 1.
test-addᵀ : fwd (query a) (_ , input)
              (lift · , (lift · , (fin (+ 1 / 2) , fin 0ℚ))
                      , (lift · , (∞ , ∞))
                      , (lift · , (fin (+ 1 / 5) , fin (+ 1 / 2))) , _)
            ≡ (fin (+ 1 / 5) , fin 0ℚ)
test-addᵀ = refl

bwd-slice : _ → _
bwd-slice r =
  conjugate (ty (unit [×] input-ty) (_ , input)) (ty (base number) 0)
            (mor (query a) (_ , input)) .func r

-- Feeding back output interval [9/10, 11/10] around 1 = perturbation bounds (1/10, 1/10). The
-- conjugate copies it to the two label-a inputs (#1, #3) and leaves ∞ elsewhere:
--   #1 around 0: (1/10, 1/10) = [-1/10, 1/10]
--   #2 (label b): (∞, ∞)      = no constraint
--   #3 around 1: (1/10, 1/10) = [9/10, 11/10]
test-bwd : bwd-slice (fin (+ 1 / 10) , fin (+ 1 / 10))
           ≡ (lift · , (lift · , (fin (+ 1 / 10) , fin (+ 1 / 10)))
                     , (lift · , (∞ , ∞))
                     , (lift · , (fin (+ 1 / 10) , fin (+ 1 / 10))) , lift ·)
test-bwd = refl
