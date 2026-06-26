{-# OPTIONS --prop --postfix-projections --safe #-}

-- The booleans as a commutative semiring: + is join (⊔), · is meet (⊓), 0 is O,
-- 1 is I.  (The opposite semiring, swapping ⊔ and ⊓, would also live here.)
module semiring-bool where

open import commutative-semiring using (CommutativeSemiring; BooleanAlgebra)
open import two using (O; I; Two-setoid; ⊔-cmon; ⊓-cmon; ⊓-⊔-distribₗ; O-⊓-annihilₗ)
open import prop using (tt) renaming (_,_ to _,p_)

semiring : CommutativeSemiring Two-setoid
semiring .CommutativeSemiring.additive = ⊔-cmon
semiring .CommutativeSemiring.multiplicative = ⊓-cmon
semiring .CommutativeSemiring.·-+-distribₗ {x} {y} {z} = ⊓-⊔-distribₗ {x} {y} {z}
semiring .CommutativeSemiring.ε-annihilₗ {x} = O-⊓-annihilₗ {x}

open BooleanAlgebra

-- The two-element semiring is a Boolean algebra.
boolean : BooleanAlgebra semiring
boolean .∧-idem {O}       = tt ,p tt
boolean .∧-idem {I}       = tt ,p tt
boolean .⊤-add-top        = tt ,p tt
boolean .¬                = two.¬
boolean .compl-∧ {O} = tt ,p tt
boolean .compl-∧ {I} = tt ,p tt
boolean .compl-∨ {O} = tt ,p tt
boolean .compl-∨ {I} = tt ,p tt
