{-# OPTIONS --prop --postfix-projections --safe #-}

-- The counting semiring (ℕ, +, 0, ·, 1): scalars count uses, with addition combining counts
-- across paths and multiplication along them.
module semiring-N where

open import Level using (0ℓ)
open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Nat.Properties using
  (+-comm; +-assoc; *-comm; *-assoc; *-identityˡ; *-distribˡ-+; *-zeroˡ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong₂)
open import prop using (LiftS; liftS)
open import prop-setoid using (Setoid; IsEquivalence)
open import commutative-monoid using (CommutativeMonoid)
open import commutative-semiring using (CommutativeSemiring)

setoid : Setoid 0ℓ 0ℓ
setoid .Setoid.Carrier = ℕ
setoid .Setoid._≈_ a b = LiftS 0ℓ (a ≡ b)
setoid .Setoid.isEquivalence .IsEquivalence.refl = liftS refl
setoid .Setoid.isEquivalence .IsEquivalence.sym (liftS e) = liftS (sym e)
setoid .Setoid.isEquivalence .IsEquivalence.trans (liftS e₁) (liftS e₂) = liftS (trans e₁ e₂)

additive : CommutativeMonoid setoid
additive .CommutativeMonoid.ε = 0
additive .CommutativeMonoid._+_ = _+_
additive .CommutativeMonoid.+-cong (liftS e₁) (liftS e₂) = liftS (cong₂ _+_ e₁ e₂)
additive .CommutativeMonoid.+-lunit = liftS refl
additive .CommutativeMonoid.+-assoc {x} {y} {z} = liftS (+-assoc x y z)
additive .CommutativeMonoid.+-comm {x} {y} = liftS (+-comm x y)

multiplicative : CommutativeMonoid setoid
multiplicative .CommutativeMonoid.ε = 1
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
