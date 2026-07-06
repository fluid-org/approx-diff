{-# OPTIONS --prop --postfix-projections --safe #-}

-- Boolean dependency analysis of the moving-average example: adjacent outputs share an input,
-- and composing the backward and forward derivatives sends a selection of outputs to the outputs
-- related to it by a shared dependency, as in the cognacy analyses of linked visualisations.
module example-bool-mavg where

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
open Ex.ex using (mavg)
open import label using (a; b)

-- Model instantiation: Boolean approximations over rational data, zero-testing coefficients.
module SDSemiMod-𝟚 = sd-semimodule two.semiring
open import example-harness using (module BoolAlg-model-nonzero)
open BoolAlg-model-nonzero two.semiring two.semiring-boolean
open BoolAlg.SelfDualBooleanAlgebra using (selfDual)

half : ℚ
half = + 1 / 2

input : ⟦ ((base number [×] base number) [×] base number) [×] base number ⟧ty .idx .Carrier
input = ((1ℚ , + 2 / 1) , + 4 / 1) , + 8 / 1

input-ty : first-order-data (((base number [×] base number) [×] base number) [×] base number)
input-ty = ((base number [×] base number) [×] base number) [×] base number

output-ty : first-order-data ((base number [×] base number) [×] base number)
output-ty = (base number [×] base number) [×] base number

-- The first input reaches only the first output ...
test-fwd-first : fwd (mavg half) (_ , input) (lift · , (((⊤ , ⊥) , ⊥) , ⊥))
                 ≡ ((⊤ , ⊥) , ⊥)
test-fwd-first = refl

-- ... and a shared input reaches both adjacent outputs.
test-fwd-shared : fwd (mavg half) (_ , input) (lift · , (((⊥ , ⊤) , ⊥) , ⊥))
                  ≡ ((⊤ , ⊤) , ⊥)
test-fwd-shared = refl

-- Backward derivative of the full output: every input is used.
test-bwd : SDSemiMod-𝟚.conjugate (selfDual (ty (unit [×] input-ty) (_ , input)))
             (selfDual (ty output-ty ((+ 3 / 2 , + 3 / 1) , + 6 / 1)))
             (mor (mavg half) (_ , input)) .func ((⊤ , ⊤) , ⊤)
           ≡ (lift · , (((⊤ , ⊤) , ⊤) , ⊤))
test-bwd = refl

-- Related outputs: backwards from the first output and forwards again. The second output shares
-- an input with the first; the third shares nothing and stays ⊥.
test-related : fwd (mavg half) (_ , input)
                 (SDSemiMod-𝟚.conjugate (selfDual (ty (unit [×] input-ty) (_ , input)))
                    (selfDual (ty output-ty ((+ 3 / 2 , + 3 / 1) , + 6 / 1)))
                    (mor (mavg half) (_ , input)) .func ((⊤ , ⊥) , ⊥))
               ≡ ((⊤ , ⊤) , ⊥)
test-related = refl
