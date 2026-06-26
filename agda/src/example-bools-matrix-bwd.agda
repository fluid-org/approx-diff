{-# OPTIONS --prop --postfix-projections --safe #-}

-- Backward analysis (matrix-new), via the to-gal Galois connection.
module example-bools-matrix-bwd where

open import example-bools-matrix

input : ⟦ list (base label [×] base number) ⟧ty .idx .Carrier
input = 3 , (a , 0) , (b , 1) , (a , 1) , _

input-ty : first-order-data (list (base label [×] base number))
input-ty = list (base label [×] base number)

bwd-slice : _ → _
bwd-slice l =
  to-gal (ty-bsddl (unit [×] input-ty) (_ , input)) (ty-bsddl (base number) 0)
         (mor (query l) (_ , input)) .right .fun (⊥ ∷ [])

-- Querying 'a' needs the 1st and 3rd numbers; querying 'b' needs the 2nd.
test1 : bwd-slice a ≡ (lift · , ([] , ⊥ ∷ []) , ([] , ⊤ ∷ []) , ([] , ⊥ ∷ []) , _)
test1 = refl
test2 : bwd-slice b ≡ (lift · , ([] , ⊤ ∷ []) , ([] , ⊥ ∷ []) , ([] , ⊤ ∷ []) , _)
test2 = refl
