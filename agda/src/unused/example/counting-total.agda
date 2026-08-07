{-# OPTIONS --prop --postfix-projections --safe #-}

-- Use-counting analysis of the weighted-sum query: the price of the queried label is used twice,
-- and the count survives the cancellation that zeroes the rational derivative, because nothing
-- cancels in a positive semiring.
module example.counting-total where

open import example.counting
import Data.Fin as Fin

input : ⟦ (list (base label [×] base number)) [×] (base number [×] base number) ⟧ty (λ ()) .idx .Carrier
input = T.sup (inj₂ ((a , + 3 / 1) , T.sup (inj₂ ((b , 1ℚ) , T.sup (inj₂ ((a , -[1+ 2 ] / 1) , T.sup (inj₁ (lift ·))))))))
        , (+ 2 / 1 , + 5 / 1)

input-ty : first-order ((list (base label [×] base number)) [×] (base number [×] base number))
input-ty = μ (unit [+] ((base label [×] base number) [×] var Fin.zero)) [×] (base number [×] base number)

-- One use of the first quantity reaches the output once.
test-fwd-q₁ : fwd (total a) (_ , input)
                (lift · , ((lift · , 1) , (lift · , 0) , (lift · , 0) , _) , (0 , 0))
              ≡ 1
test-fwd-q₁ = refl

-- The price of label a is used twice: its uses reach the output along both selected rows, and the
-- counts add where the rational contributions cancelled.
test-fwd-price-a : fwd (total a) (_ , input)
                     (lift · , ((lift · , 0) , (lift · , 0) , (lift · , 0) , _) , (1 , 0))
                   ≡ 2
test-fwd-price-a = refl

-- Backward derivative of the output: use-counts for every position.
test-bwd : conjugate (ty₀ (unit [×] input-ty) (_ , input)) (ty₀ (base number) 0ℚ)
             (mor (total a) (_ , input)) .func 1
           ≡ (lift · , ((lift · , 1) , (lift · , 0) , (lift · , 1) , _) , (2 , 0))
test-bwd = refl
