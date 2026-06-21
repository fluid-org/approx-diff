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

open radius-semiring using (D; ∞; fin)
open import Data.Rational using (0ℚ; 1ℚ)
module SM = semimodule radius-semiring.semiring
open CMon.CMonEnriched SM.cmon-enriched using (_+m_)
open SM using (𝟘; 𝕀; _⊕_; ε-map)

-- numbers approximated by D² = 𝕀 ⊕ 𝕀 (left and right radius).
D² : SM.Semimodule
D² = 𝕀 ⊕ 𝕀

unitm : SM._⇒_ 𝟘 D²
unitm = ε-map 𝟘 D²

conjunctm : SM._⇒_ (HasProducts.prod HM.products D² D²) D²
conjunctm = HasProducts.p₁ HM.products {D²} {D²} +m HasProducts.p₂ HM.products {D²} {D²}

open import example-signature-interpretation SM.cat HM.products SM.terminal D² unitm conjunctm
open HM.interp Sig BaseInterp1

input : ⟦ list (base label [×] base number) ⟧ty .idx .Carrier
input = 3 , (label.a , 0) , (label.b , 1) , (label.a , 1) , _

open indexed-family._⇒f_
open SM._⇒_

fwd-slice : _ → _
fwd-slice n = ⟦ example.ex.query label.a ⟧tm .famf .transf (_ , input) .func n

-- Query a sums the 1st and 3rd numbers (label a); radii combine by min, with ∞
-- the no-information identity.  A present input survives an ∞ (no-info) input:
-- linear, not annihilating.
test-1 : fwd-slice (lift · , (lift · , (fin 0ℚ , fin 0ℚ)) , (lift · , (∞ , ∞)) , (lift · , (∞ , ∞)) , _)
         ≡ (fin 0ℚ , fin 0ℚ)
test-1 = ≡-refl

-- Both a-numbers present: left radii combine by min (1 ⊓ 0 = 0), right stay ∞.
test-2 : fwd-slice (lift · , (lift · , (fin 1ℚ , ∞)) , (lift · , (∞ , ∞)) , (lift · , (fin 0ℚ , ∞)) , _)
         ≡ (fin 0ℚ , ∞)
test-2 = ≡-refl

-- The label-b number (2nd) is irrelevant to query a, so it never reaches the output.
test-3 : fwd-slice (lift · , (lift · , (∞ , ∞)) , (lift · , (fin 0ℚ , fin 0ℚ)) , (lift · , (∞ , ∞)) , _)
         ≡ (∞ , ∞)
test-3 = ≡-refl
