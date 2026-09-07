{-# OPTIONS --prop --postfix-projections --safe #-}

-- The example constants as strings.
open import Level using (0ℓ)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)

open import Data.Rational using (ℚ)
module example.render.constants {A : Setoid 0ℓ 0ℓ} (as-weight : ℚ → Setoid.Carrier A) (S : CommutativeSemiring A) where

open import Data.Nat using (zero; suc)
open import Data.String using (String; _++_)
open import Data.Rational using (ℚ; ↥_; ↧_)
import Data.Integer as ℤ
import Data.Integer.Show as ℤ-Show
open import signature.example ℚ using (number; string)
open import signature.example.interpretation as-weight S using (sort-val)

show-ℚ : ℚ → String
show-ℚ q with ↧ q
... | ℤ.+ (suc zero) = ℤ-Show.show (↥ q)
... | d              = ℤ-Show.show (↥ q) ++ "/" ++ ℤ-Show.show d

show-const : ∀ {s} → sort-val s → String
show-const {number} q = show-ℚ q
show-const {string} s = "\"" ++ s ++ "\""
