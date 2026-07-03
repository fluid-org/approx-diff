{-# OPTIONS --prop --postfix-projections --safe #-}

-- Which entries of a rational matrix are nonzero, as a lax functor Mat(ℚ) → Mat(𝟚): identities
-- and transpose preserved on the nose, composition laxly (the chain-rule over-approximation).
-- The tests exercise the Jacobians of the introductory example: a composite can have fewer
-- nonzero entries than the composite of the nonzero entries suggests, when contributions cancel.
module matrix-nonzero where

open import Data.Integer using (+_; -[1+_])
open import Data.Rational using (0ℚ; 1ℚ; _/_)
open import Data.Fin using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import commutative-semiring using (CommutativeSemiring)
import two
import semiring-Q
import matrix

private
  module T = CommutativeSemiring two.semiring
  module QM = matrix.Mat semiring-Q.semiring
  module TM = matrix.Mat two.semiring

  ∨-idem : ∀ {x} → (x T.+ x) T.≈ x
  ∨-idem {two.O} = T.refl {two.O}
  ∨-idem {two.I} = T.refl {two.I}

open import matrix-lax-functor semiring-Q.nonzero ∨-idem

-- The quantities column of the refund example: a purchase and its refund.
N : QM.Matrix 2 1
N zero zero = + 3 / 1
N (suc zero) zero = -[1+ 2 ] / 1

-- Summation of the two contributions.
M : QM.Matrix 1 2
M zero zero = 1ℚ
M zero (suc zero) = 1ℚ

-- The contributions cancel: the composite has no nonzero entries...
cancels : E (M QM.∘ N) zero zero ≡ two.O
cancels = refl

-- ...but the composite of the patterns records a possible dependency.
over-approximates : (E M TM.∘ E N) zero zero ≡ two.I
over-approximates = refl
