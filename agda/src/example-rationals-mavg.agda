{-# OPTIONS --prop --postfix-projections --safe #-}

-- Shared setup for the moving-average tests: the term, the constant 1/2 and the input run.
-- The forward and backward tests live in their own files, since each is slow to normalise.
module example-rationals-mavg where

open import example-rationals
open import Data.Integer using (+_)
open import Data.Rational using (_/_)

half : ℚ
half = + 1 / 2

input : ⟦ list (base number) ⟧ty .idx .Carrier
input = 3 , 1ℚ , + 2 / 1 , + 4 / 1 , _

input-ty : first-order-data (list (base number))
input-ty = list (base number)
