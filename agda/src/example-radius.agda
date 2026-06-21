{-# OPTIONS --prop --postfix-projections --safe #-}

-- Forward analysis of the example query in the radius model: interpret directly
-- into Fam(SemiMod D), numbers approximated by D² (left, right radius).
module example-radius where

open import Level using (0ℓ; lift)
open import signature
open import example-signature
import language-syntax
import label
import indexed-family
import prop-setoid
open import Data.Unit renaming (tt to ·) using ()
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open prop-setoid.Setoid

module L = language-syntax Sig
open L hiding (_,_)

import example
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl)

open import categories using (Category; HasTerminal; HasProducts)
import cmon-enriched as CMon
import semimodule
import radius-semiring
import ho-model-semimod-D as HM

open radius-semiring using (∞; fin)
open import Data.Rational using (0ℚ; 1ℚ; _/_)
open import Data.Integer using (+_)
module SM = semimodule radius-semiring.semiring
open CMon.CMonEnriched SM.cmon-enriched using (_+m_)
open SM using (𝟘; 𝕀; _⊕_; _⇒_; ε-map; 𝕀-sd; 𝟘-sd; ⊕-sd; conjugate)

-- numbers approximated by D² = 𝕀 ⊕ 𝕀 (left and right radius).
D² : SM.Semimodule
D² = 𝕀 ⊕ 𝕀

conjunctm : HasProducts.prod HM.products D² D² ⇒ D²
conjunctm = HasProducts.p₁ HM.products {D²} {D²} +m HasProducts.p₂ HM.products {D²} {D²}

open import example-signature-interpretation SM.cat HM.products SM.terminal D² (ε-map 𝟘 D²) conjunctm
open HM.interp Sig BaseInterp1

input : ⟦ list (base label [×] base number) ⟧ty .idx .Carrier
input = 3 , (label.a , 0) , (label.b , 1) , (label.a , 1) , _

open indexed-family._⇒f_
open SM._⇒_

fwd-slice : _ → _
fwd-slice n = ⟦ example.ex.query label.a ⟧tm .famf .transf (_ , input) .func n

-- An interval [l, u] around q from the paper becomes the pair of radii (q - l , u - q); ∞ is the absent
-- (bottom) approximation. So [4/5, 3/2] around 1 becomes (1/5, 1/2).
-- Query a sums #1 and #3; the forward slice combines their radii by min:
--   ( min(1/2, 1/5) , min(0, 1/2) ) = (1/5 , 0) = the interval [4/5, 1] around 1.
test-addᵀ : fwd-slice (lift · , (lift · , (fin (+ 1 / 2) , fin 0ℚ))
                              , (lift · , (∞ , ∞))
                              , (lift · , (fin (+ 1 / 5) , fin (+ 1 / 2))) , _)
            ≡ (fin (+ 1 / 5) , fin 0ℚ)
test-addᵀ = ≡-refl

queryMor : _
queryMor = ⟦ example.ex.query label.a ⟧tm .famf .transf (_ , input)

-- each element is  label ⊕ number  =  𝟘 ⊕ D²
eltSD : SM.SelfDual
eltSD = ⊕-sd 𝟘-sd (⊕-sd 𝕀-sd 𝕀-sd)

-- empty context ⊕ (e₁ ⊕ (e₂ ⊕ (e₃ ⊕ nil)))
inputSD : SM.SelfDual
inputSD = ⊕-sd 𝟘-sd (⊕-sd eltSD (⊕-sd eltSD (⊕-sd eltSD 𝟘-sd)))

bwd-slice : _ → _
bwd-slice r = conjugate inputSD (⊕-sd 𝕀-sd 𝕀-sd) queryMor .func r

-- example-intervals.backward feeds output [9/10, 11/10] around 1 = radii (1/10, 1/10).
-- The transpose copies it to the two label-a inputs (#1, #3) and leaves ∞ elsewhere:
--   #1 around 0: (1/10, 1/10) = [-1/10, 1/10]
--   #2 (label b): (∞, ∞)      = no constraint
--   #3 around 1: (1/10, 1/10) = [9/10, 11/10]
test-bwd : bwd-slice (fin (+ 1 / 10) , fin (+ 1 / 10))
           ≡ (lift · , (lift · , (fin (+ 1 / 10) , fin (+ 1 / 10)))
                     , (lift · , (∞ , ∞))
                     , (lift · , (fin (+ 1 / 10) , fin (+ 1 / 10))) , lift ·)
test-bwd = ≡-refl
