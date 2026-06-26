{-# OPTIONS --prop --postfix-projections --safe #-}

module example-rationals-bwd where

open import example-rationals
import Data.Rational as Q

bwd-mult : ℚ → ℚ → FD.Vec 1 → _
bwd-mult a b w =
  SM.conjugate (ty-sd (unit [×] (base number [×] base number)) (_ , (a , b)))
               (ty-sd (base number) (Q._*_ a b))
               (mor mult-ex (_ , (a , b))) .func w

test-rev : bwd-mult 0ℚ 1ℚ (1ℚ ∷ []) ≡ (lift · , (1ℚ ∷ [] , 0ℚ ∷ []))
test-rev = refl

test-rev' : bwd-mult 1ℚ 0ℚ (1ℚ ∷ []) ≡ (lift · , (0ℚ ∷ [] , 1ℚ ∷ []))
test-rev' = refl
