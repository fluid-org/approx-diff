{-# OPTIONS --prop --postfix-projections --safe #-}

-- The rooted interpretation of the dependency example's signature, over the Booleans, read back as
-- matrices between position orders. The term cases on a boolean alongside a number: the input
-- carries the number's scalar position, the injection's tag and the unit payload's root. Taking the
-- left branch reads the number, so every input position reaches the output; taking the right branch
-- returns a literal, so the number's position reaches nothing, while the tag still reaches the
-- output through the branch's constant, and the payload's root through absorption into it.
module test.rooted-dependency where

open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_; tabulate)
open import Data.Product using () renaming (_,_ to _,'_)
open import Data.Sum using (inj₁; inj₂)
open import Level using (lift)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import Data.Rational using (0ℚ; 1ℚ)
open import every using ([])
import two
import matrix
import example.dependency as ED
import ho-model-rooted-order-idempotent

private
  module T = CommutativeSemiring two.semiring
  module TM = matrix.Mat two.semiring

  ∨-idem : ∀ {x} → (x T.+ x) T.≈ x
  ∨-idem {two.O} = T.refl {two.O}
  ∨-idem {two.I} = T.refl {two.I}

  ∧-idem : ∀ {x} → (x T.· x) T.≈ x
  ∧-idem {two.O} = T.refl {two.O}
  ∧-idem {two.I} = T.refl {two.I}

  ⊤-add-top : ∀ {x} → (T.ι T.+ x) T.≈ T.ι
  ⊤-add-top {two.O} = T.refl {two.I}
  ⊤-add-top {two.I} = T.refl {two.I}

module RH = ho-model-rooted-order-idempotent two.semiring
  (λ {x} → ∨-idem {x}) (λ {x} → ∧-idem {x}) (λ {x} → ⊤-add-top {x})
module RI = RH.rooted-interp ED.Sig ED.primitives

open import language-syntax ED.Sig

-- A number and a boolean in context; case on the boolean, reading the number on the left and a
-- literal on the right.
Γ : ctxt
Γ = (emp , base ED.number) , (unit [+] unit)

Γ-fo : first-order-ctxt Γ
Γ-fo = (emp , base ED.number) , (unit [+] unit)

t : Γ ⊢ base ED.number
t = case (var zero) (var (succ (succ zero))) (bop (ED.lit 0ℚ) [])

-- Inputs taking each branch: the number is 1, the boolean either injection of the unit value.
γ-l γ-r : Setoid.Carrier (RI.𝒞⟦ Γ-fo ⟧ctxt .RH.Fam⟨𝒞⟩μ.idx)
γ-l = ((lift tt ,' 1ℚ) ,' inj₁ (lift tt))
γ-r = ((lift tt ,' 1ℚ) ,' inj₂ (lift tt))

table : ∀ {m n} → TM.Matrix m n → Vec (Vec two.Two n) m
table M = tabulate (λ i → tabulate (λ j → M i j))

-- Columns: the number's scalar, the injection's tag, the unit payload's root.
test-l : table (RI.readback.dep-mat Γ-fo (base ED.number) t γ-l)
         ≡ ((two.I ∷ two.I ∷ two.I ∷ []) ∷ [])
test-l = refl

test-r : table (RI.readback.dep-mat Γ-fo (base ED.number) t γ-r)
         ≡ ((two.O ∷ two.I ∷ two.I ∷ []) ∷ [])
test-r = refl
