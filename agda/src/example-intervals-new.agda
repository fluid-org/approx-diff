{-# OPTIONS --prop --postfix-projections --safe #-}

-- Forward analysis of the example query in the perturbation-bound model: interpret directly
-- into Fam(SemiMod ℚ∞), numbers approximated by ℚ∞² (left, right perturbation bound).
module example-intervals-new where

open import Level using (0ℓ; lift)
open import signature
open import example-signature
import language-syntax
import label
import nat
import indexed-family
import prop-setoid
open import Data.Unit renaming (tt to ·) using ()
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open prop-setoid.Setoid

module L = language-syntax Sig
open L hiding (_,_)

import example
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl)

open import categories using (Category; HasTerminal; HasInitial; HasProducts)
import cmon-enriched as CMon
import matrix-new
import semimodule
import semiring-Q-tropical
import ho-model-matrix-new
module HM = ho-model-matrix-new semiring-Q-tropical.semiring
module FD = matrix-new.Mat semiring-Q-tropical.semiring
module SM = semimodule semiring-Q-tropical.semiring

open semiring-Q-tropical using (∞; fin)
open import Data.Rational using (0ℚ; 1ℚ; _/_)
open import Data.Integer using (+_)
open CMon.CMonEnriched FD.cmon using (_+m_)
open SM using (_⇒_; 𝟘-sd; ⊕-sd; conjugate)

-- numbers approximated by ℚ∞² = S² (left and right perturbation bound), the embedding of the
-- 2-dimensional matrix base.
unitm : FD._⇒_ 0 2
unitm = HasInitial.from-initial FD.initial {2}

conjunctm : FD._⇒_ (HasProducts.prod FD.products 2 2) 2
conjunctm = HasProducts.p₁ FD.products {2} {2} +m HasProducts.p₂ FD.products {2} {2}

open import example-signature-interpretation FD.cat FD.products FD.terminal 2 unitm conjunctm
open HM.interp Sig BaseInterp1
module SD = HM.interp-sd Sig BaseInterp1

input : ⟦ list (base label [×] base number) ⟧ty .idx .Carrier
input = 3 , (label.a , 0) , (label.b , 1) , (label.a , 1) , _

open indexed-family._⇒f_
open SM._⇒_
open FD using (_∷_; [])

fwd-slice : _ → _
fwd-slice n = ⟦ example.ex.query label.a ⟧tm .famf .transf (_ , input) .func n

-- An interval [l, u] around q from the paper becomes the pair of perturbation bounds (q - l , u - q); ∞ is
-- the absent (bottom) approximation. So [4/5, 3/2] around 1 becomes (1/5, 1/2).
-- Query a sums #1 and #3; the forward slice combines their perturbation bounds by min:
--   ( min(1/2, 1/5) , min(0, 1/2) ) = (1/5 , 0) = the interval [4/5, 1] around 1.
test-addᵀ : fwd-slice (lift · , ([] , (fin (+ 1 / 2) ∷ fin 0ℚ ∷ []))
                              , ([] , (∞ ∷ ∞ ∷ []))
                              , ([] , (fin (+ 1 / 5) ∷ fin (+ 1 / 2) ∷ [])) , _)
            ≡ (fin (+ 1 / 5) ∷ fin 0ℚ ∷ [])
test-addᵀ = ≡-refl

query : _
query = ⟦ example.ex.query label.a ⟧tm .famf .transf (_ , input)

bwd-slice : _ → _
bwd-slice r =
  conjugate (⊕-sd 𝟘-sd (SD.ty-sd (list (base label [×] base number)) input))
            (SD.ty-sd (base number) nat.zero) query .func r

-- example-intervals.backward feeds output [9/10, 11/10] around 1 = perturbation bounds (1/10, 1/10).
-- The transpose copies it to the two label-a inputs (#1, #3) and leaves ∞ elsewhere:
--   #1 around 0: (1/10, 1/10) = [-1/10, 1/10]
--   #2 (label b): (∞, ∞)      = no constraint
--   #3 around 1: (1/10, 1/10) = [9/10, 11/10]
test-bwd : bwd-slice (fin (+ 1 / 10) ∷ fin (+ 1 / 10) ∷ [])
           ≡ (lift · , ([] , (fin (+ 1 / 10) ∷ fin (+ 1 / 10) ∷ []))
                     , ([] , (∞ ∷ ∞ ∷ []))
                     , ([] , (fin (+ 1 / 10) ∷ fin (+ 1 / 10) ∷ [])) , lift ·)
test-bwd = ≡-refl
