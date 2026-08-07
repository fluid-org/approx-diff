{-# OPTIONS --prop --postfix-projections --safe #-}

-- Backward analysis over the self-dual Boolean algebras, via the to-gal Galois connection.
module example.bool-bwd where

open import example.bool
import Data.Fin as Fin

input : ⟦ list (base label [×] base number) ⟧ty (λ ()) .idx .Carrier
input = T.sup (inj₂ ((a , 0) , T.sup (inj₂ ((b , 1) , T.sup (inj₂ ((a , 1) , T.sup (inj₁ (lift ·))))))))

input-ty : first-order (list (base label [×] base number))
input-ty = μ (unit [+] ((base label [×] base number) [×] var Fin.zero))

bwd-slice : _ → _
bwd-slice l =
  to-gal (𝟘 ⊕ ty₀ input-ty input) (ty₀ (base number) 0)
         (mor (query l) (_ , input)) .right .fun ⊥

-- Querying 'a' needs the 1st and 3rd numbers; querying 'b' needs the 2nd.
test1 : bwd-slice a ≡ (lift · , (lift · , ⊥) , (lift · , ⊤) , (lift · , ⊥) , _)
test1 = refl
test2 : bwd-slice b ≡ (lift · , (lift · , ⊤) , (lift · , ⊥) , (lift · , ⊤) , _)
test2 = refl
