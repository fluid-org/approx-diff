{-# OPTIONS --prop --postfix-projections --safe #-}

-- The spine order of a two-element list, over the Booleans. Positions are the outer cons c₁, the
-- first element a, the inner cons c₂, and the second element b, with c₁ an ancestor of every
-- position and c₂ an ancestor of b. Closing a selection under the order adds the constructors
-- above each selected position, so the fixed selections are the prefix-closed slices.
module test.order-idempotent where

open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import commutative-semiring using (CommutativeSemiring)
import two
import matrix
import order-idempotent

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

pattern c₁ = zero
pattern a  = suc zero
pattern c₂ = suc (suc zero)
pattern b  = suc (suc (suc zero))

ord4 : TM.Matrix 4 4
ord4 c₁ _  = two.I
ord4 a  a  = two.I
ord4 a  _  = two.O
ord4 c₂ c₂ = two.I
ord4 c₂ b  = two.I
ord4 c₂ _  = two.O
ord4 b  b  = two.I
ord4 b  _  = two.O

private
  O-≤ : ∀ x → two.O L.≤ x
  O-≤ two.O = T.refl {two.O}
  O-≤ two.I = T.refl {two.I}

  ≤-I : ∀ x → x L.≤ two.I
  ≤-I two.O = T.refl {two.I}
  ≤-I two.I = T.refl {two.I}

  L-refl : ∀ x → x L.≤ x
  L-refl two.O = T.refl {two.O}
  L-refl two.I = T.refl {two.I}

spine : Pos
spine .dim = 4
spine .ord = ord4
spine .ord-refl c₁ = T.refl {two.I}
spine .ord-refl a  = T.refl {two.I}
spine .ord-refl c₂ = T.refl {two.I}
spine .ord-refl b  = T.refl {two.I}
spine .ord-trans c₁ j  k  = ≤-I (ord4 j k)
spine .ord-trans a  c₁ k  = O-≤ (ord4 a k)
spine .ord-trans a  a  k  = L-refl (ord4 a k)
spine .ord-trans a  c₂ k  = O-≤ (ord4 a k)
spine .ord-trans a  b  k  = O-≤ (ord4 a k)
spine .ord-trans c₂ c₁ k  = O-≤ (ord4 c₂ k)
spine .ord-trans c₂ a  k  = O-≤ (ord4 c₂ k)
spine .ord-trans c₂ c₂ k  = L-refl (ord4 c₂ k)
spine .ord-trans c₂ b  c₁ = T.refl {two.O}
spine .ord-trans c₂ b  a  = T.refl {two.O}
spine .ord-trans c₂ b  c₂ = T.refl {two.I}
spine .ord-trans c₂ b  b  = T.refl {two.I}
spine .ord-trans b  c₁ k  = O-≤ (ord4 b k)
spine .ord-trans b  a  k  = O-≤ (ord4 b k)
spine .ord-trans b  c₂ k  = O-≤ (ord4 b k)
spine .ord-trans b  b  k  = L-refl (ord4 b k)

-- Ancestor closure of a selection of positions: the action of the order matrix.
close-sel : TM.Vec 4 → TM.Vec 4
close-sel v q = ord4 q TM.⋅ v

sel-b : TM.Vec 4
sel-b b = two.I
sel-b _ = two.O

-- Closing {b} adds both cons cells but not the first element.
closure-b : TM.Vec 4
closure-b c₁ = two.I
closure-b a  = two.O
closure-b c₂ = two.I
closure-b b  = two.I

test-close-b : ∀ q → close-sel sel-b q ≡ closure-b q
test-close-b c₁ = refl
test-close-b a  = refl
test-close-b c₂ = refl
test-close-b b  = refl

-- The prefix {c₁, a} is fixed by the closure.
prefix-ca : TM.Vec 4
prefix-ca c₁ = two.I
prefix-ca a  = two.I
prefix-ca c₂ = two.O
prefix-ca b  = two.O

test-fixed-prefix : ∀ q → close-sel prefix-ca q ≡ prefix-ca q
test-fixed-prefix c₁ = refl
test-fixed-prefix a  = refl
test-fixed-prefix c₂ = refl
test-fixed-prefix b  = refl

-- The selection {a} is not prefix-closed and not fixed: closure adds the cons above it.
sel-a : TM.Vec 4
sel-a a = two.I
sel-a _ = two.O

test-close-a : close-sel sel-a c₁ ≡ two.I
test-close-a = refl

-- The spine order is the iterated lifting: each cons cell lifts the biproduct of its element's
-- discrete order with the tail.
spine-lifted : Pos
spine-lifted = lift (disc 1 ⊕ lift (disc 1 ⊕ 𝟘p))

test-spine-lifted : ∀ q p → spine-lifted .ord q p ≡ ord4 q p
test-spine-lifted c₁ c₁ = refl
test-spine-lifted c₁ a  = refl
test-spine-lifted c₁ c₂ = refl
test-spine-lifted c₁ b  = refl
test-spine-lifted a  c₁ = refl
test-spine-lifted a  a  = refl
test-spine-lifted a  c₂ = refl
test-spine-lifted a  b  = refl
test-spine-lifted c₂ c₁ = refl
test-spine-lifted c₂ a  = refl
test-spine-lifted c₂ c₂ = refl
test-spine-lifted c₂ b  = refl
test-spine-lifted b  c₁ = refl
test-spine-lifted b  a  = refl
test-spine-lifted b  c₂ = refl
test-spine-lifted b  b  = refl
