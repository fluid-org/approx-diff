{-# OPTIONS --prop --postfix-projections --safe #-}

-- Backward derivative of the moving average over the full output: adjacent outputs share the
-- middle input, which receives 1/2 from each, so its entry is 1.
module example-rationals-mavg-bwd where

open import example-rationals
open import example-rationals-mavg
open import Data.Integer using (+_)
open import Data.Rational using (_/_)

test-bwd : conjugate (ty (unit [×] input-ty) (_ , input))
             (ty (list (base number)) (2 , + 3 / 2 , + 3 / 1 , _))
             (mor (mavg half) (_ , input)) .func (1ℚ , 1ℚ , lift ·)
           ≡ (lift · , (half , 1ℚ , half , lift ·))
test-bwd = refl
