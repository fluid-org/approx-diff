{-# OPTIONS --prop --postfix-projections --safe #-}

-- The dependency example over the Booleans, instantiated once so consumers pay for the module
-- application through the interface file.
module example.dependency where

open import Data.Product using () renaming (_,_ to _,'_)
open import Data.Sum using (inj₁; inj₂)
open import Level using (lift)
open import Data.Unit using (tt)
open import prop-setoid using (Setoid)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ)
import two
import matrix
import example.primitives as EP
import ho-model
open import example.programs using (case-ctxt-fo; case-term; test-ctxt-fo; test-term)

module model = ho-model two.semiring two.I
module interp = model.interp EP.Sig EP.primitives

open import language-syntax EP.Sig
  using (base; _⊢_; case; brel; bop; var; zero; first-order-ctxt; emp; _,_)
open import every using ([]; _∷_)

γ-l γ-r : Setoid.Carrier (interp.𝒞⟦ case-ctxt-fo ⟧ctxt .model.Fam⟨𝒞⟩μ.idx)
γ-l = ((lift tt ,' 1ℚ) ,' inj₁ (lift tt))
γ-r = ((lift tt ,' 1ℚ) ,' inj₂ (lift tt))

-- The term's dependency matrices at the two inputs: one output row (the number's
-- scalar) against three input columns (the number's scalar, the injection's tag, the unit
-- payload's root).
abstract
  dep-l dep-r : matrix.Mat.Matrix two.semiring 1 3
  dep-l = interp.dependency.mat-of case-ctxt-fo (base EP.number) case-term γ-l
  dep-r = interp.dependency.mat-of case-ctxt-fo (base EP.number) case-term γ-r

γ-test : Setoid.Carrier (interp.𝒞⟦ test-ctxt-fo ⟧ctxt .model.Fam⟨𝒞⟩μ.idx)
γ-test = (lift tt ,' 1ℚ)

abstract
  dep-test : matrix.Mat.Matrix two.semiring 1 1
  dep-test = interp.dependency.mat-of test-ctxt-fo (base EP.number) test-term γ-test
