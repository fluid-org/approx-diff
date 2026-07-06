{-# OPTIONS --prop --postfix-projections --safe #-}

-- Use-counting analysis of the weighted-sum query, at the counting semiring: every operation has
-- unit coefficients, so a Jacobian entry counts the paths from an input to an output. The price of
-- the queried label is used twice, and the count survives the cancellation that zeroes the
-- rational derivative, because nothing cancels in a positive semiring.
module example-counting-total where

import semiring-N
import semiring-Q

open import Level using (lift; 0ℓ)
open import Data.Unit renaming (tt to ·) using ()
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ)
open import Data.Integer using (+_; -[1+_])
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _/_)
open import prop-setoid using (Setoid)
open Setoid using (Carrier)
open import example-signature ℚ using (Sig; number; label; approx)
import example
module Ex = example ℚ
open Ex.ex using (total)
open import language-syntax Sig hiding (_,_)
open import label using (a; b)

-- Model instantiation: counting approximations over rational data, unit coefficients.
open import example-harness using (module SDSemiMod-model-unit; rationals)
open SDSemiMod-model-unit semiring-N.semiring rationals

input : ⟦ (list (base label [×] base number)) [×] (base number [×] base number) ⟧ty .idx .Carrier
input = (3 , (a , + 3 / 1) , (b , 1ℚ) , (a , -[1+ 2 ] / 1) , _) , (+ 2 / 1 , + 5 / 1)

input-ty : first-order-data ((list (base label [×] base number)) [×] (base number [×] base number))
input-ty = list (base label [×] base number) [×] (base number [×] base number)

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
test-bwd : conjugate (ty (unit [×] input-ty) (_ , input)) (ty (base number) 0ℚ)
             (mor (total a) (_ , input)) .func 1
           ≡ (lift · , ((lift · , 1) , (lift · , 0) , (lift · , 1) , lift ·) , (2 , 0))
test-bwd = refl
