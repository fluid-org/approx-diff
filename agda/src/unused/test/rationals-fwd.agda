{-# OPTIONS --prop --postfix-projections --safe #-}

-- Forward-mode AD over the self-dual semimodules.
module unused.test.rationals-fwd where

open import example.rationals
open import Data.Integer using (+_)
open import Data.Rational using (_/_; -_)

2ℚ = (+ 2) / 1
3ℚ = (+ 3) / 1
5ℚ = (+ 5) / 1

-- The Jacobian of x × y at (2, 3) is [ ∂/∂x , ∂/∂y ] = [ y , x ] = [ 3 , 2 ].
test-∂x : fwd mult-ex (_ , (2ℚ , 3ℚ)) (lift · , (1ℚ , 0ℚ)) ≡ 3ℚ
test-∂x = refl

test-∂y : fwd mult-ex (_ , (2ℚ , 3ℚ)) (lift · , (0ℚ , 1ℚ)) ≡ 2ℚ
test-∂y = refl

-- Tangent (1,1) combines both partials: y + x = 5.
test-sum : fwd mult-ex (_ , (2ℚ , 3ℚ)) (lift · , (1ℚ , 1ℚ)) ≡ 5ℚ
test-sum = refl

-- Cancellation: at (3, 2), tangent (3, −2) gives (2 × 3) + (3 × −2) = 0, though both inputs contribute.
test-cancel : fwd mult-ex (_ , (3ℚ , 2ℚ)) (lift · , (3ℚ , - 2ℚ)) ≡ 0ℚ
test-cancel = refl

8ℚ = (+ 8) / 1

xs-in : ⟦ list (base number) ⟧ty (λ ()) .idx .Carrier
xs-in = T.sup (inj₂ (3ℚ , T.sup (inj₂ (5ℚ , T.sup (inj₁ (lift ·))))))

-- (sum xs) × y at xs = [3, 5], y = 2: ∂/∂x = y = 2, ∂/∂y = sum xs = 8.
test-sum-v : fwd sum-mul (_ , (xs-in , 2ℚ)) (lift · , ((1ℚ , 0ℚ , _) , 0ℚ)) ≡ 2ℚ
test-sum-v = refl

test-sum-y : fwd sum-mul (_ , (xs-in , 2ℚ)) (lift · , ((0ℚ , 0ℚ , _) , 1ℚ)) ≡ 8ℚ
test-sum-y = refl
