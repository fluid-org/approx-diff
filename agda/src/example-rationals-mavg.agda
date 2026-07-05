{-# OPTIONS --prop --postfix-projections --safe #-}

-- Forward and backward derivatives of the moving-average example at the rationals. Adjacent
-- outputs share an input, so the backward derivative of the full output gives each shared input a
-- coefficient of 1/2 + 1/2 = 1; non-adjacent outputs share no input.
module example-rationals-mavg where

open import example-rationals
open import Data.Integer using (+_)
open import Data.Rational using (_/_)

half : ℚ
half = + 1 / 2

input : ⟦ ((base number [×] base number) [×] base number) [×] base number ⟧ty .idx .Carrier
input = ((1ℚ , + 2 / 1) , + 4 / 1) , + 8 / 1

input-ty : first-order-data (((base number [×] base number) [×] base number) [×] base number)
input-ty = ((base number [×] base number) [×] base number) [×] base number

output-ty : first-order-data ((base number [×] base number) [×] base number)
output-ty = (base number [×] base number) [×] base number

-- Perturbing the first input moves only the first output, by 1/2 ...
test-fwd-first : fwd (mavg half) (_ , input) (lift · , (((1ℚ , 0ℚ) , 0ℚ) , 0ℚ))
                 ≡ ((half , 0ℚ) , 0ℚ)
test-fwd-first = refl

-- ... and perturbing a shared input moves both adjacent outputs.
test-fwd-shared : fwd (mavg half) (_ , input) (lift · , (((0ℚ , 1ℚ) , 0ℚ) , 0ℚ))
                  ≡ ((half , half) , 0ℚ)
test-fwd-shared = refl

-- Backward derivative of the full output: each shared input receives 1/2 from both of its
-- outputs; the end inputs receive 1/2 from their single output.
test-bwd : conjugate (ty (unit [×] input-ty) (_ , input))
             (ty output-ty ((+ 3 / 2 , + 3 / 1) , + 6 / 1))
             (mor (mavg half) (_ , input)) .func ((1ℚ , 1ℚ) , 1ℚ)
           ≡ (lift · , (((half , 1ℚ) , 1ℚ) , half))
test-bwd = refl

-- Related outputs: backwards from the first output and forwards again. The second output is
-- related to the first (they share the second input); the third shares nothing and receives 0.
test-related : fwd (mavg half) (_ , input)
                 (conjugate (ty (unit [×] input-ty) (_ , input))
                    (ty output-ty ((+ 3 / 2 , + 3 / 1) , + 6 / 1))
                    (mor (mavg half) (_ , input)) .func ((1ℚ , 0ℚ) , 0ℚ))
               ≡ ((half , + 1 / 4) , 0ℚ)
test-related = refl
