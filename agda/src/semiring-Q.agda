{-# OPTIONS --prop --postfix-projections --safe #-}

-- The usual commutative semiring over the rationals (ℚ, +, 0, ·, 1), for automatic-differentiation examples:
-- a program's fibre map is its Jacobian as a matrix over ℚ.

module semiring-Q where

open import Level using (0ℓ)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_)
open import Data.Rational.Properties using
  (+-comm; +-assoc; +-identityˡ; *-comm; *-assoc; *-identityˡ; *-distribˡ-+; *-zeroˡ; *-zeroʳ; _≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (yes; no)
open import prop using (LiftS; liftS)
open import prop-setoid using (Setoid; IsEquivalence)
open import commutative-monoid using (CommutativeMonoid)
open import commutative-semiring using (CommutativeSemiring; _⇒ˡ_)
open import two using (Two; O; I)
import two

setoid : Setoid 0ℓ 0ℓ
setoid .Setoid.Carrier = ℚ
setoid .Setoid._≈_ a b = LiftS 0ℓ (a ≡ b)
setoid .Setoid.isEquivalence .IsEquivalence.refl = liftS refl
setoid .Setoid.isEquivalence .IsEquivalence.sym (liftS e) = liftS (sym e)
setoid .Setoid.isEquivalence .IsEquivalence.trans (liftS e₁) (liftS e₂) = liftS (trans e₁ e₂)

additive : CommutativeMonoid setoid
additive .CommutativeMonoid.ε = 0ℚ
additive .CommutativeMonoid._+_ = _+_
additive .CommutativeMonoid.+-cong (liftS e₁) (liftS e₂) = liftS (cong₂ _+_ e₁ e₂)
additive .CommutativeMonoid.+-lunit {x} = liftS (+-identityˡ x)
additive .CommutativeMonoid.+-assoc {x} {y} {z} = liftS (+-assoc x y z)
additive .CommutativeMonoid.+-comm {x} {y} = liftS (+-comm x y)

multiplicative : CommutativeMonoid setoid
multiplicative .CommutativeMonoid.ε = 1ℚ
multiplicative .CommutativeMonoid._+_ = _*_
multiplicative .CommutativeMonoid.+-cong (liftS e₁) (liftS e₂) = liftS (cong₂ _*_ e₁ e₂)
multiplicative .CommutativeMonoid.+-lunit {x} = liftS (*-identityˡ x)
multiplicative .CommutativeMonoid.+-assoc {x} {y} {z} = liftS (*-assoc x y z)
multiplicative .CommutativeMonoid.+-comm {x} {y} = liftS (*-comm x y)

semiring : CommutativeSemiring setoid
semiring .CommutativeSemiring.additive = additive
semiring .CommutativeSemiring.multiplicative = multiplicative
semiring .CommutativeSemiring.·-+-distribₗ {x} {y} {z} = liftS (*-distribˡ-+ x y z)
semiring .CommutativeSemiring.ε-annihilₗ {x} = liftS (*-zeroˡ x)

private
  module T = CommutativeSemiring two.semiring

  nz : ℚ → Two
  nz x with x ≟ 0ℚ
  ... | yes _ = O
  ... | no  _ = I

  ⊑I : ∀ {z} → (z T.+ I) T.≈ I
  ⊑I {z} = T.trans (T.+-comm {z} {I}) (T.refl {I})

nonzero : semiring ⇒ˡ two.semiring
nonzero ._⇒ˡ_.f = nz
nonzero ._⇒ˡ_.f-cong {a} (liftS refl) with a ≟ 0ℚ
... | yes _ = T.refl {O}
... | no  _ = T.refl {I}
nonzero ._⇒ˡ_.f-ε = T.refl {O}
nonzero ._⇒ˡ_.f-ι = T.refl {I}
nonzero ._⇒ˡ_.f-+ {a} {b} with a ≟ 0ℚ | b ≟ 0ℚ
... | yes a≡0 | yes b≡0 rewrite trans (cong₂ _+_ a≡0 b≡0) (+-identityˡ 0ℚ) = T.refl {O}
... | yes _   | no  _ = ⊑I
... | no  _   | yes _ = ⊑I
... | no  _   | no  _ = ⊑I
nonzero ._⇒ˡ_.f-· {a} {b} with a ≟ 0ℚ | b ≟ 0ℚ
... | yes a≡0 | _       rewrite trans (cong (_* b) a≡0) (*-zeroˡ b) = T.refl {O}
... | no  _   | yes b≡0 rewrite trans (cong (a *_) b≡0) (*-zeroʳ a) = T.refl {O}
... | no  _   | no  _ = ⊑I
