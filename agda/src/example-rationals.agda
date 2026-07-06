{-# OPTIONS --prop --postfix-projections --safe #-}

-- Test harness for the rationals (AD) model with the value-carrying base interpretation
-- (BaseInterp1), over the self-dual semimodules as first-order model.
module example-rationals where

open import categories using (Category; HasInitial; HasProducts; HasTerminal)
import cmon-enriched
import prop
import semimodule
import sd-semimodule
import ho-model-sd-semimod
import indexed-family
import semiring-Q

open import Level using (lift; 0ℓ) public
open import Data.Unit renaming (tt to ·) using () public
open import Data.Product using (_,_) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl) public
open import prop using (liftS) public
open import Data.Rational using (ℚ; 0ℚ; 1ℚ) public
open import prop-setoid using (Setoid)
open Setoid using (Carrier) public
open import commutative-monoid using (CommutativeMonoid)
open import commutative-semiring using (CommutativeSemiring)
open import example-signature ℚ using (Sig; number; label; approx) public
import example
open import language-syntax Sig hiding (_,_) public
module Ex = example ℚ
open Ex.ex public

-- Model instantiation: the genuine derivative coefficients, multiplication-by-c.

module SDSemiMod-ℚ = sd-semimodule semiring-Q.semiring
module SemiMod-ℚ = semimodule semiring-Q.semiring
module Scalars = CommutativeSemiring semiring-Q.semiring

private
  scalar : ℚ → Category._⇒_ SDSemiMod-ℚ.cat SDSemiMod-ℚ.𝕀 SDSemiMod-ℚ.𝕀
  scalar c .SemiMod-ℚ._⇒_.*→* = record { func = λ x → c Scalars.· x ; func-resp-≈ = λ e → Scalars.·-cong (Scalars.refl {c}) e }
  scalar c .SemiMod-ℚ._⇒_.preserve-ze = Scalars.ε-annihilᵣ {c}
  scalar c .SemiMod-ℚ._⇒_.preserve-+ {x} {y} = Scalars.·-+-distribₗ {c} {x} {y}
  scalar c .SemiMod-ℚ._⇒_.preserve-· {s} {x} =
    Scalars.trans (Scalars.sym (Scalars.·-assoc {c} {s} {x}))
      (Scalars.trans (Scalars.·-cong (Scalars.·-comm {c} {s}) Scalars.refl) (Scalars.·-assoc {s} {c} {x}))

  scalar-cong : ∀ {x y} → Setoid._≈_ semiring-Q.setoid x y → Category._≈_ SemiMod-ℚ.cat (scalar x) (scalar y)
  scalar-cong e = record { *≈* = record { func-eq = λ u≈v → Scalars.·-cong e u≈v } }

open import example-harness using (module SDSemiMod-model-scalar; rationals)
open SDSemiMod-model-scalar semiring-Q.semiring rationals scalar scalar-cong public


