{-# OPTIONS --prop --postfix-projections --safe #-}

-- The booleans as a commutative semiring: + is join (⊔), · is meet (⊓), 0 is O,
-- 1 is I.  (The opposite semiring, swapping ⊔ and ⊓, would also live here.)
module semiring-bool where

open import commutative-semiring using (CommutativeSemiring)
open import two using (Two-setoid; ⊔-cmon; ⊓-cmon; ⊓-⊔-distribₗ; O-⊓-annihilₗ)

semiring : CommutativeSemiring Two-setoid
semiring .CommutativeSemiring.additive = ⊔-cmon
semiring .CommutativeSemiring.multiplicative = ⊓-cmon
semiring .CommutativeSemiring.·-+-distribₗ {x} {y} {z} = ⊓-⊔-distribₗ {x} {y} {z}
semiring .CommutativeSemiring.ε-annihilₗ {x} = O-⊓-annihilₗ {x}
