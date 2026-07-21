{-# OPTIONS --prop --postfix-projections --safe #-}

-- Boolean dependency analysis of the weighted-sum query from the introduction. Where the rational
-- derivative of the price entry cancels to 0, the Boolean analysis reports ⊤, because disjunction
-- can't cancel.
module test.dependency where

open import example.dependency
import Data.Fin as Fin

input : ⟦ (list (base label [×] base number)) [×] (base number [×] base number) ⟧ty (λ ()) .idx .Carrier
input = T.sup (inj₂ ((a , + 3 / 1) , T.sup (inj₂ ((b , 1ℚ) , T.sup (inj₂ ((a , -[1+ 2 ] / 1) , T.sup (inj₁ (lift ·))))))))
        , (+ 2 / 1 , + 5 / 1)

input-ty : first-order ((list (base label [×] base number)) [×] (base number [×] base number))
input-ty = μ (unit [+] ((base label [×] base number) [×] var Fin.zero)) [×] (base number [×] base number)

-- ∂₂/∂q₁ = ⊤: the output may depend on the first quantity.
test-q₁ : fwd (total a) (_ , input)
            (lift · , ((lift · , ⊤) , (lift · , ⊥) , (lift · , ⊥) , _) , (⊥ , ⊥))
          ≡ ⊤
test-q₁ = refl

-- ∂₂/∂(price a) = ⊤, although the rational derivative is 0, because disjunction can't cancel.
test-price-a : fwd (total a) (_ , input)
                 (lift · , ((lift · , ⊥) , (lift · , ⊥) , (lift · , ⊥) , _) , (⊤ , ⊥))
               ≡ ⊤
test-price-a = refl

-- ∂₂/∂q₂ = ⊥: the b-labelled row is not consulted.
test-q₂ : fwd (total a) (_ , input)
            (lift · , ((lift · , ⊥) , (lift · , ⊤) , (lift · , ⊥) , _) , (⊥ , ⊥))
          ≡ ⊥
test-q₂ = refl

-- The backward derivative applied to the selected output: the inputs the output may depend on,
-- (1 0 1 1 0), still including the cancelled price a.
test-bwd : HM.SDSemiMod.conjugate (ty₀ (unit [×] input-ty) (_ , input))
             (ty₀ (base number) 0ℚ)
             (mor (total a) (_ , input)) .func ⊤
           ≡ (lift · , ((lift · , ⊤) , (lift · , ⊥) , (lift · , ⊤) , _) , (⊤ , ⊥))
test-bwd = refl
