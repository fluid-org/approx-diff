{-# OPTIONS --prop --postfix-projections --safe #-}

-- Forward analysis over the SDSemiMod first-order model.
module example.bool-fwd where

open import example.bool

input : ⟦ list (base label [×] base number) ⟧ty (λ ()) .idx .Carrier
input = T.sup (inj₂ ((a , 0) , T.sup (inj₂ ((b , 1) , T.sup (inj₂ ((a , 1) , T.sup (inj₁ (lift ·))))))))

-- Output depends on the 1st and 3rd numbers (those with label a), not the 2nd.
test-1 : fwd (query a) (_ , input) (lift · , (lift · , ⊤) , (lift · , ⊥) , (lift · , ⊥) , _) ≡ ⊤
test-1 = refl
test-2 : fwd (query a) (_ , input) (lift · , (lift · , ⊥) , (lift · , ⊤) , (lift · , ⊥) , _) ≡ ⊥
test-2 = refl
test-3 : fwd (query a) (_ , input) (lift · , (lift · , ⊥) , (lift · , ⊥) , (lift · , ⊤) , _) ≡ ⊤
test-3 = refl
