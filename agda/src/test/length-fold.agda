{-# OPTIONS --prop --postfix-projections --safe #-}

-- Length of a one-element list, over the Booleans, computed by the generic fold rather than written
-- down. The list's fibre has a root for the injection, a root for the pair, and the nil root, the
-- element carrying no positions. The algebra gives the successor as the constant of the cons branch
-- and the zero as the constant of the nil branch, and reads the tail's result through its linear
-- part.
--
-- The table below is that the cons tag alone determines the successor but not the zero, and that the
-- nil tag determines the zero.
module test.length-fold where

open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import commutative-semiring using (CommutativeSemiring)
import two
import matrix
import order-idempotent
import order-idempotent-poly-fold

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

open order-idempotent two.semiring (λ {x} → ∨-idem {x}) (λ {x} → ∧-idem {x}) (λ {x} → ⊤-add-top {x})
open order-idempotent-poly-fold two.semiring (λ {x} → ∨-idem {x}) (λ {x} → ∧-idem {x})
  (λ {x} → ⊤-add-top {x})

-- Results carry a successor position and a zero position.
E : Pos
E = 𝟘p

R : Pos
R = disc 2

-- Lists: nil carries nothing, cons carries an element and the tail.
Lst : Poly
Lst = konst 𝟘p ⊞ (konst E ⊗ var)

nil : Val Lst
nil = sup (inl kon)

cons : Val Lst → Val Lst
cons v = sup (inr (prd kon (rec v)))

-- The algebra. The constants are the parts of the result each branch builds: the zero for nil, the
-- successor for cons. The cons branch reads the tail's result through the zero position.
alg : (s : Shape Lst Lst) → (𝟘p ⊕ ⟦_⟧ 𝟘p R s) ⇒ R
alg (inl kon) = close raw
  where
  raw : TM.Matrix 2 1
  raw zero    _ = two.O
  raw (suc _) _ = two.I
alg (inr (prd kon (rec v))) = close raw
  where
  -- Columns: the injection root, the pair root, the element, then the tail's result.
  raw : TM.Matrix 2 4
  raw zero    zero                      = two.I
  raw zero    _                         = two.O
  raw (suc _) (suc (suc (suc _))) = two.I
  raw (suc _) _                         = two.O

one : Val Lst
one = cons nil

len : (𝟘p ⊕ fibV one) ⇒ R
len = fold 𝟘p R alg one

pattern s = zero
pattern z = suc zero

pattern c = zero
pattern p = suc zero
pattern n = suc (suc zero)

-- The cons tag determines the successor and not the zero.
test-cons-suc : len .mat s c ≡ two.I
test-cons-suc = refl

test-cons-zero : len .mat z c ≡ two.O
test-cons-zero = refl

-- The nil tag determines the zero, and the successor too, since the cons root is above it.
test-nil-zero : len .mat z n ≡ two.I
test-nil-zero = refl

test-nil-suc : len .mat s n ≡ two.I
test-nil-suc = refl

-- The pair root behaves as the cons root does.
test-pair-suc : len .mat s p ≡ two.I
test-pair-suc = refl

test-pair-zero : len .mat z p ≡ two.O
test-pair-zero = refl
