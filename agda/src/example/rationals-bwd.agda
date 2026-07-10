{-# OPTIONS --prop --postfix-projections --safe #-}

-- Reverse-mode AD over the self-dual semimodules, via the conjugate.
module example.rationals-bwd where

open import example.rationals
import Data.Rational as Q
open import Data.Integer using (+_)
open import Data.Rational using (_/_)

2ℚ = (+ 2) / 1
3ℚ = (+ 3) / 1

bwd-mult : ℚ → ℚ → ℚ → _
bwd-mult a b w =
  conjugate (ty₀ (unit [×] (base number [×] base number)) (_ , (a , b)))
            (ty₀ (base number) (Q._*_ a b))
            (mor mult-ex (_ , (a , b))) .func w

-- Reverse mode: the gradient of x × y at (2, 3) is (∂/∂x, ∂/∂y) = (y, x) = (3, 2).
test-rev : bwd-mult 2ℚ 3ℚ 1ℚ ≡ (lift · , (3ℚ , 2ℚ))
test-rev = refl
