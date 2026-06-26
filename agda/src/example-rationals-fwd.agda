{-# OPTIONS --prop --postfix-projections --safe #-}

module example-rationals-fwd where

open import example-rationals

test-∂x : fwd mult-ex (_ , (0ℚ , 1ℚ)) (lift · , (1ℚ ∷ [] , 0ℚ ∷ [])) ≡ (1ℚ ∷ [])
test-∂x = refl

test-∂y : fwd mult-ex (_ , (1ℚ , 0ℚ)) (lift · , (0ℚ ∷ [] , 1ℚ ∷ [])) ≡ (1ℚ ∷ [])
test-∂y = refl

test-cross : fwd mult-ex (_ , (1ℚ , 0ℚ)) (lift · , (1ℚ ∷ [] , 0ℚ ∷ [])) ≡ (0ℚ ∷ [])
test-cross = refl
