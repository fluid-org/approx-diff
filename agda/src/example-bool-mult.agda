{-# OPTIONS --prop --postfix-projections --safe #-}

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
