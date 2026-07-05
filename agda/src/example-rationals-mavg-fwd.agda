{-# OPTIONS --prop --postfix-projections --safe #-}

-- Rows of the moving-average Jacobian: perturbing the first input moves only the first output;
-- perturbing the shared middle input moves both.
module example-rationals-mavg-fwd where

open import example-rationals
open import example-rationals-mavg
open import Data.Rational using (_/_)

test-fwd-first : fwd (mavg half) (_ , input) (lift · , (1ℚ , 0ℚ , 0ℚ , lift ·))
                 ≡ (half , 0ℚ , lift ·)
test-fwd-first = refl

test-fwd-shared : fwd (mavg half) (_ , input) (lift · , (0ℚ , 1ℚ , 0ℚ , lift ·))
                  ≡ (half , half , lift ·)
test-fwd-shared = refl
