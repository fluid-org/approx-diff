{-# OPTIONS --prop --postfix-projections --safe #-}

-- Forward and backward derivatives of the moving-average example at the rationals. Adjacent
-- outputs share the middle input, so the backward derivative of the full output gives it a
-- coefficient of 1/2 + 1/2 = 1.
module example-rationals-mavg where

open import example-rationals
open import Data.Integer using (+_)
open import Data.Rational using (_/_)

half : ℚ
half = + 1 / 2

input : ⟦ (base number [×] base number) [×] base number ⟧ty .idx .Carrier
input = (1ℚ , + 2 / 1) , + 4 / 1

input-ty : first-order-data ((base number [×] base number) [×] base number)
input-ty = (base number [×] base number) [×] base number

-- Perturbing the first input moves only the first output, by 1/2 ...
test-fwd-first : fwd (mavg half) (_ , input) (lift · , ((1ℚ , 0ℚ) , 0ℚ))
                 ≡ (half , 0ℚ)
test-fwd-first = refl

-- ... and perturbing the shared middle input moves both outputs.
test-fwd-shared : fwd (mavg half) (_ , input) (lift · , ((0ℚ , 1ℚ) , 0ℚ))
                  ≡ (half , half)
test-fwd-shared = refl

-- Backward derivative of the full output: the shared input receives 1/2 from each output.
test-bwd : conjugate (ty (unit [×] input-ty) (_ , input))
             (ty (base number [×] base number) (+ 3 / 2 , + 3 / 1))
             (mor (mavg half) (_ , input)) .func (1ℚ , 1ℚ)
           ≡ (lift · , ((half , 1ℚ) , half))
test-bwd = refl
