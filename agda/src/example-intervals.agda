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
open import example-signature ℚ using (Sig; number; label; approx)
import example
open import language-syntax Sig hiding (_,_)
module Ex = example ℚ
open Ex.ex using (query)
open import label using (a; b)
open semiring-Q-tropical-add using (∞; fin)

-- Model instantiation: bounds for each direction of change, so the approximation object is
-- 𝕀 ⊕ 𝕀. Multiplication admits no min-plus-linear perturbation bound; the zero map (constantly ∞)
-- records the absence of a bound.
module SDSemiMod-ℚ∞ = sd-semimodule semiring-Q-tropical-add.semiring
module SemiMod-ℚ∞ = semimodule semiring-Q-tropical-add.semiring
open cmon-enriched.CMonEnriched SemiMod-ℚ∞.cmon-enriched using (εm)

private
  Approx : Category.obj SDSemiMod-ℚ∞.cat
  Approx = SDSemiMod-ℚ∞._⊕_ SDSemiMod-ℚ∞.𝕀 SDSemiMod-ℚ∞.𝕀

  unit-c ∞-c : ℚ → ℚ → Category._⇒_ SDSemiMod-ℚ∞.cat Approx Approx
  unit-c _ _ = Category.id SDSemiMod-ℚ∞.cat Approx
  ∞-c _ _ = εm

  unit-c-cong : ∀ {x x' y y'} → Setoid._≈_ semiring-Q.setoid x x' → Setoid._≈_ semiring-Q.setoid y y' →
                Category._≈_ SemiMod-ℚ∞.cat (unit-c x y) (unit-c x' y')
  unit-c-cong _ _ = Category.≈-refl SemiMod-ℚ∞.cat {f = unit-c 0ℚ 0ℚ}

  ∞-c-cong : ∀ {x x' y y'} → Setoid._≈_ semiring-Q.setoid x x' → Setoid._≈_ semiring-Q.setoid y y' →
             Category._≈_ SemiMod-ℚ∞.cat (∞-c x y) (∞-c x' y')
  ∞-c-cong _ _ = Category.≈-refl SemiMod-ℚ∞.cat {f = ∞-c 0ℚ 0ℚ}

open import example-harness using (module SDSemiMod-model; rationals)
open SDSemiMod-model semiring-Q-tropical-add.semiring Approx rationals unit-c unit-c ∞-c ∞-c
  unit-c-cong unit-c-cong ∞-c-cong ∞-c-cong

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
