{-# OPTIONS --prop --postfix-projections --safe #-}

-- The example constants as strings.
module example.show where

open import Data.Nat using (zero; suc)
open import Data.String using (String; _++_)
open import Data.Rational using (ℚ; ↥_; ↧_)
import Data.Integer as ℤ
import Data.Integer.Show as ℤ-Show
open import prop-setoid using (Setoid)
import label
open import example.signature ℚ using (number; label)
open import example.values using (sort-index)

show-ℚ : ℚ → String
show-ℚ q with ↧ q
... | ℤ.+ (suc zero) = ℤ-Show.show (↥ q)
... | d              = ℤ-Show.show (↥ q) ++ "/" ++ ℤ-Show.show d

show-label : label.label → String
show-label label.a = "a"
show-label label.b = "b"
show-label label.c = "c"
show-label label.d = "d"

show-const : ∀ {s} → Setoid.Carrier (sort-index s) → String
show-const {number} q = show-ℚ q
show-const {label}  l = show-label l
