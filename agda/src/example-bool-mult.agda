{-# OPTIONS --prop --postfix-projections --safe #-}

-- Derivative interpretation of `mult`: the output's dependence on each factor is value-dependent.
-- ∂(x·y)/∂x = y, ∂(x·y)/∂y = x, pushed through · → Bool (non-zero ↦ ⊤).  So at (0,5) only the first factor
-- matters; at (3,0) only the second.
module example-bool-mult where

open import example-bool

-- At (0,5): first factor matters (∂/∂x = 5 ≠ 0), second does not (∂/∂y = 0).
test-x : fwd mult-ex (_ , (0 , 5)) (lift · , (⊤ ∷ [] , ⊥ ∷ [])) ≡ (⊤ ∷ [])
test-x = refl
test-y : fwd mult-ex (_ , (0 , 5)) (lift · , (⊥ ∷ [] , ⊤ ∷ [])) ≡ (⊥ ∷ [])
test-y = refl

-- At (3,0): reversed — second factor matters, first does not.
test-x' : fwd mult-ex (_ , (3 , 0)) (lift · , (⊤ ∷ [] , ⊥ ∷ [])) ≡ (⊥ ∷ [])
test-x' = refl
test-y' : fwd mult-ex (_ , (3 , 0)) (lift · , (⊥ ∷ [] , ⊤ ∷ [])) ≡ (⊤ ∷ [])
test-y' = refl
