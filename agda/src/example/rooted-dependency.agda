{-# OPTIONS --prop --postfix-projections --safe #-}

-- The rooted interpretation of the dependency example over the Booleans, instantiated once so
-- consumers pay for the module application through the interface file.
module example.rooted-dependency where

open import Data.Product using () renaming (_,_ to _,'_)
open import Data.Sum using (inj₁; inj₂)
open import Level using (lift)
open import Data.Unit using (tt)
open import prop-setoid using (Setoid)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ)
import two
import matrix
import example
import example.primitives as EP
import ho-model-roots-order-idempotent

module Ex = example ℚ 0ℚ
open Ex.ex using (case-ctxt-fo; case-term)

module model = ho-model-roots-order-idempotent two.semiring
  (λ {x} → two.∨-idem {x}) (λ {x} → two.∧-idem {x}) (λ {x} → two.⊤-add-top {x})
module interp = model.rooted-interp EP.Sig EP.primitives

open import language-syntax EP.Sig
  using (base; _⊢_; case; brel; bop; var; zero; first-order-ctxt; emp; _,_)
open import every using ([]; _∷_)

γ-l γ-r : Setoid.Carrier (interp.𝒞⟦ case-ctxt-fo ⟧ctxt .model.Fam⟨𝒞⟩μ.idx)
γ-l = ((lift tt ,' 1ℚ) ,' inj₁ (lift tt))
γ-r = ((lift tt ,' 1ℚ) ,' inj₂ (lift tt))

-- The readback of the term's dependency matrices at the two inputs: one output row (the number's
-- scalar) against three input columns (the number's scalar, the injection's tag, the unit
-- payload's root).
abstract
  dep-l dep-r : matrix.Mat.Matrix two.semiring 1 3
  dep-l = interp.readback.dep-mat case-ctxt-fo (base EP.number) case-term γ-l
  dep-r = interp.readback.dep-mat case-ctxt-fo (base EP.number) case-term γ-r

-- Control dependence through a test: matching on a numeric equality must charge the scalar the
-- test read, through the root of the test's boolean.
test-ctxt-fo : first-order-ctxt (emp , base EP.number)
test-ctxt-fo = emp , base EP.number

test-term : (emp , base EP.number) ⊢ base EP.number
test-term =
  case (brel EP.equal-number (var zero ∷ (bop (EP.lit 0ℚ) [] ∷ [])))
       (bop (EP.lit 1ℚ) []) (bop (EP.lit 0ℚ) [])

γ-test : Setoid.Carrier (interp.𝒞⟦ test-ctxt-fo ⟧ctxt .model.Fam⟨𝒞⟩μ.idx)
γ-test = (lift tt ,' 1ℚ)

abstract
  dep-test : matrix.Mat.Matrix two.semiring 1 1
  dep-test = interp.readback.dep-mat test-ctxt-fo (base EP.number) test-term γ-test
