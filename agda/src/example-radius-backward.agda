{-# OPTIONS --prop --postfix-projections --safe #-}

-- Backward map over D via the self-dual transpose.  The forward add is the
-- codiagonal ∇ (min-fold); its transpose, mediated by the self-duality at each
-- end, is the copy — reproducing add-interval's backward leg in radii.
module example-radius-backward where

open import Data.Rational using (1ℚ)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl)
import cmon-enriched as CMon
import semimodule
import radius-semiring

open radius-semiring using (D; ∞; fin)
module SM = semimodule radius-semiring.semiring
open CMon.CMonEnriched SM.cmon-enriched using (_+m_)
open SM using (𝕀; _⊕_; p₁; p₂; _⇒_; 𝕀-sd; ⊕-sd; conjugate)
open SM._⇒_

-- forward add codiagonal over D: (u , v) ↦ min(u , v).
∇ : (𝕀 ⊕ 𝕀) ⇒ 𝕀
∇ = p₁ +m p₂

-- backward = the conjugate, with self-dualities read off the objects.
bwd : 𝕀 ⇒ (𝕀 ⊕ 𝕀)
bwd = conjugate (⊕-sd 𝕀-sd 𝕀-sd) 𝕀-sd ∇

-- the backward of add copies the output radius to both inputs.
test : bwd .func (fin 1ℚ) ≡ (fin 1ℚ , fin 1ℚ)
test = ≡-refl
