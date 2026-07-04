{-# OPTIONS --prop --postfix-projections --safe #-}

-- Forward and backward derivatives of the weighted-sum query from the introduction, at the
-- rationals: the price column cancels (3 + (-3) = 0) even though the price is used.
module example-rationals-total where

open import example-rationals
open import Data.Integer using (+_; -[1+_])
open import Data.Rational using (_/_)
open import label using (a; b)

input : ⟦ (list (base label [×] base number)) [×] (base number [×] base number) ⟧ty .idx .Carrier
input = (3 , (a , + 3 / 1) , (b , 1ℚ) , (a , -[1+ 2 ] / 1) , _) , (+ 2 / 1 , + 5 / 1)

input-ty : first-order-data ((list (base label [×] base number)) [×] (base number [×] base number))
input-ty = list (base label [×] base number) [×] (base number [×] base number)

-- ∂/∂q₁ is the price, 2.
test-q₁ : fwd (total a) (_ , input)
            (lift · , ((lift · , 1ℚ) , (lift · , 0ℚ) , (lift · , 0ℚ) , _) , (0ℚ , 0ℚ))
          ≡ + 2 / 1
test-q₁ = refl

-- ∂/∂(price a) is 3 + (-3) = 0: the contributions cancel.
test-price-a : fwd (total a) (_ , input)
                 (lift · , ((lift · , 0ℚ) , (lift · , 0ℚ) , (lift · , 0ℚ) , _) , (1ℚ , 0ℚ))
               ≡ 0ℚ
test-price-a = refl

-- The full backward derivative: (2 0 2 0 0), the price entries zero.
test-bwd : conjugate (ty (unit [×] input-ty) (_ , input)) (ty (base number) 0ℚ)
             (mor (total a) (_ , input)) .func 1ℚ
           ≡ (lift · , ((lift · , + 2 / 1) , (lift · , 0ℚ) , (lift · , + 2 / 1) , lift ·) , (0ℚ , 0ℚ))
test-bwd = refl
