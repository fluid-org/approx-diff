{-# OPTIONS --prop --postfix-projections --safe #-}
module mavg-diag where

open import example-rationals
open import example-rationals-mavg using (half)
open import Data.Integer using (+_)
open import Data.Rational using (_/_)

input2 : ⟦ list (base number) ⟧ty .idx .Carrier
input2 = 2 , 1ℚ , + 2 / 1 , _

test : fwd (mavg half) (_ , input2) (lift · , (1ℚ , 0ℚ , lift ·))
       ≡ (half , 0ℚ , lift ·)
test = refl
