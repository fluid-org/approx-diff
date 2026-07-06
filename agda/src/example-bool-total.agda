{-# OPTIONS --prop --postfix-projections --safe #-}

-- Boolean dependency analysis of the weighted-sum query from the introduction, with rational
-- numbers as the underlying data. Where the rational derivative of the price entry cancels to 0,
-- the Boolean analysis reports ⊤, because disjunction can't cancel.
module example-bool-total where

import sd-semimodule
import semiring-Q

open import Level using (lift; 0ℓ)
open import Data.Unit renaming (tt to ·) using ()
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import two renaming (I to ⊤; O to ⊥) using ()
open import Data.Integer using (+_; -[1+_])
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _/_; _≟_)
open import prop-setoid using (Setoid)
open Setoid using (Carrier)
open import example-signature ℚ using (Sig; number; label; approx)
import example
open import language-syntax Sig hiding (_,_)
module Ex = example ℚ
open Ex.ex using (total)
open import label using (a; b)

-- Model instantiation: Boolean approximations over rational data, zero-testing coefficients.
module SDSemiMod-𝟚 = sd-semimodule two.semiring
open import example-harness using (module BoolAlg-model-nonzero)
open BoolAlg-model-nonzero two.semiring two.semiring-boolean
open BoolAlg.SelfDualBooleanAlgebra using (selfDual)

input : ⟦ (list (base label [×] base number)) [×] (base number [×] base number) ⟧ty .idx .Carrier
input = (3 , (a , + 3 / 1) , (b , 1ℚ) , (a , -[1+ 2 ] / 1) , _) , (+ 2 / 1 , + 5 / 1)

input-ty : first-order-data ((list (base label [×] base number)) [×] (base number [×] base number))
input-ty = list (base label [×] base number) [×] (base number [×] base number)

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
test-bwd : SDSemiMod-𝟚.conjugate (selfDual (ty (unit [×] input-ty) (_ , input)))
             (selfDual (ty (base number) 0ℚ))
             (mor (total a) (_ , input)) .func ⊤
           ≡ (lift · , ((lift · , ⊤) , (lift · , ⊥) , (lift · , ⊤) , lift ·) , (⊤ , ⊥))
test-bwd = refl
