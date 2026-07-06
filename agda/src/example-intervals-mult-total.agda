{-# OPTIONS --prop --postfix-projections --safe #-}

-- Relative perturbation bounds for the weighted-sum query: multiplication passes bounds through
-- unchanged, and the refund's exact cancellation makes the condition factor infinite.
module example-intervals-mult-total where

open import example-intervals-mult

input : ⟦ (list (base label [×] base number)) [×] (base number [×] base number) ⟧ty .idx .Carrier
input = (3 , (a , + 3 / 1) , (b , 1ℚ) , (a , -[1+ 2 ] / 1) , _) , (+ 2 / 1 , + 5 / 1)

input-ty : first-order-data ((list (base label [×] base number)) [×] (base number [×] base number))
input-ty = list (base label [×] base number) [×] (base number [×] base number)

-- Multiplication passes relative bounds through unchanged: a bound on price b reaches the output
-- of total b intact.
test-price-b : fwd (total b) (_ , input)
                 (lift · , ((lift · , ∞) , (lift · , ∞) , (lift · , ∞) , _) , (∞ , fin (+ 1 / 10)))
               ≡ fin (+ 1 / 10)
test-price-b = refl

-- Likewise a bound on the selected quantity.
test-q₂ : fwd (total b) (_ , input)
            (lift · , ((lift · , ∞) , (lift · , fin (+ 1 / 10)) , (lift · , ∞) , _) , (∞ , ∞))
          ≡ fin (+ 1 / 10)
test-q₂ = refl

-- At total a the contributions cancel exactly, so the condition factor is infinite and no
-- relative bound survives.
test-cancel : fwd (total a) (_ , input)
                (lift · , ((lift · , fin (+ 1 / 10)) , (lift · , ∞) , (lift · , ∞) , _) , (∞ , ∞))
              ≡ ∞
test-cancel = refl

-- The backward derivative of total b: the bound propagates to the selected quantity and its
-- price, and nothing else is constrained.
test-bwd : conjugate (ty (unit [×] input-ty) (_ , input)) (ty (base number) (+ 5 / 1))
             (mor (total b) (_ , input)) .func (fin (+ 1 / 10))
           ≡ (lift · , ((lift · , ∞) , (lift · , fin (+ 1 / 10)) , (lift · , ∞) , lift ·) , (∞ , fin (+ 1 / 10)))
test-bwd = refl
