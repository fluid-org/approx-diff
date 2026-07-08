{-# OPTIONS --prop --postfix-projections --safe #-}

-- Linear provenance polynomials for the weighted-sum query: positions 0-4 seeded with their
-- variables (5 selects the output), the forward derivative returns x0 + x2 + 2·x3, and evaluating
-- at the all-ones valuation recovers the counting analysis.
module example.free-total where

open import example.free
import semiring-N

-- The run of the introduction, with each perturbable position seeded by its variable.
input : ⟦ (list (base label [×] base number)) [×] (base number [×] base number) ⟧ty .idx .Carrier
input = (3 , (a , + 3 / 1) , (b , 1ℚ) , (a , -[1+ 2 ] / 1) , _) , (+ 2 / 1 , + 5 / 1)

input-ty : first-order-data ((list (base label [×] base number)) [×] (base number [×] base number))
input-ty = list (base label [×] base number) [×] (base number [×] base number)

fwd-poly : Poly
fwd-poly = fwd (total a) (_ , input)
             (lift · , ((lift · , var 0) , (lift · , var 1) , (lift · , var 2) , _) , (var 3 , var 4))

-- The output's linear provenance polynomial: each selected quantity once, the queried price twice.
test-fwd : pretty fwd-poly ≡ "x0 + x2 + 2·x3"
test-fwd = refl

-- Evaluating the polynomial at the all-ones valuation recovers the counting analysis.
test-eval-counting : Free.Eval.eval semiring-N.semiring (λ _ → 1) fwd-poly ≡ 4
test-eval-counting = refl

bwd-polys : List Poly
bwd-polys =
  let (_ , ((_ , p₁) , (_ , p₂) , (_ , p₃) , _) , (ppa , ppb)) =
        conjugate (ty (unit [×] input-ty) (_ , input)) (ty (base number) 0ℚ)
          (mor (total a) (_ , input)) .func (var 5)
  in p₁ ∷ p₂ ∷ p₃ ∷ ppa ∷ ppb ∷ []

-- Backwards, with the output selected symbolically: the transpose distributes the output variable
-- to the used positions, twice to the price.
test-bwd : map pretty bwd-polys ≡ "x5" ∷ "0" ∷ "x5" ∷ "2·x5" ∷ "0" ∷ []
test-bwd = refl
