{-# OPTIONS --prop --postfix-projections --safe #-}

-- Forward analysis (matrix-new, embedded into SemiMod).
module example-bools-matrix-fwd where

open import example-bools-matrix

input : ⟦ list (base label [×] base number) ⟧ty .idx .Carrier
input = 3 , (a , 0) , (b , 1) , (a , 1) , _

-- Output depends on the 1st and 3rd numbers (those with label a), not the 2nd.
test-1 : fwd (query a) (_ , input) (lift · , ([] , ⊤ ∷ []) , ([] , ⊥ ∷ []) , ([] , ⊥ ∷ []) , _) ≡ (⊤ ∷ [])
test-1 = refl
test-2 : fwd (query a) (_ , input) (lift · , ([] , ⊥ ∷ []) , ([] , ⊤ ∷ []) , ([] , ⊥ ∷ []) , _) ≡ (⊥ ∷ [])
test-2 = refl
test-3 : fwd (query a) (_ , input) (lift · , ([] , ⊥ ∷ []) , ([] , ⊥ ∷ []) , ([] , ⊤ ∷ []) , _) ≡ (⊤ ∷ [])
test-3 = refl
