{-# OPTIONS --prop --postfix-projections --safe #-}

-- Absolute perturbation bounds for the selection-and-sum query, forwards and backwards.
module example.intervals-query where

open import example.intervals

input : ⟦ list (base label [×] base number) ⟧ty .idx .Carrier
input = 3 , (a , + 3 / 1) , (b , 1ℚ) , (a , -[1+ 2 ] / 1) , _

input-ty : first-order-data (list (base label [×] base number))
input-ty = list (base label [×] base number)

-- An interval [l, u] around q becomes the pair of perturbation bounds (q - l , u - q); ∞ is the
-- absent (bottom) approximation.
-- Query a sums #1 and #3 (values 3 and -3, output 0); the forward derivative combines their
-- perturbation bounds by min:
--   ( min(1/2, 1/5) , min(0, 1/2) ) = (1/5 , 0) = the interval [-1/5, 0] around 0.
test-addᵀ : fwd (query a) (_ , input)
              (lift · , (lift · , (fin (+ 1 / 2) , fin 0ℚ))
                      , (lift · , (∞ , ∞))
                      , (lift · , (fin (+ 1 / 5) , fin (+ 1 / 2))) , _)
            ≡ (fin (+ 1 / 5) , fin 0ℚ)
test-addᵀ = refl

bwd-slice : _ → _
bwd-slice r =
  conjugate (ty (unit [×] input-ty) (_ , input)) (ty (base number) 0ℚ)
            (mor (query a) (_ , input)) .func r

-- Feeding back output interval [-1/10, 1/10] around 0 = perturbation bounds (1/10, 1/10). The
-- conjugate copies it to the two label-a inputs (#1, #3) and leaves ∞ elsewhere:
--   #1 around 3:  (1/10, 1/10) = [29/10, 31/10]
--   #2 (label b): (∞, ∞)       = no constraint
--   #3 around -3: (1/10, 1/10) = [-31/10, -29/10]
test-bwd : bwd-slice (fin (+ 1 / 10) , fin (+ 1 / 10))
           ≡ (lift · , (lift · , (fin (+ 1 / 10) , fin (+ 1 / 10)))
                     , (lift · , (∞ , ∞))
                     , (lift · , (fin (+ 1 / 10) , fin (+ 1 / 10))) , lift ·)
test-bwd = refl
