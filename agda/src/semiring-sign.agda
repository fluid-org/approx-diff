{-# OPTIONS --prop --postfix-projections --safe #-}

-- The sign semiring {+, 0, −, ?}: the rule-of-signs abstract domain as a commutative semiring.
-- Multiplication is the rule of signs; addition is sign addition, with ? the unknown sign arising
-- from adding + to −. The canonical additive order is the abstraction order: 0 below + and −,
-- everything below ?.
module semiring-sign where

open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong₂)
open import prop using (LiftS; liftS)
open import prop-setoid using (Setoid; IsEquivalence)
open import commutative-monoid using (CommutativeMonoid)
open import commutative-semiring using (CommutativeSemiring)
open import Data.Nat using (zero; suc)
open import Data.Integer using (+_; -[1+_])
open import Data.Rational using (ℚ; ↥_)

data Sign : Set where
  pos zer neg unk : Sign

sign-of : ℚ → Sign
sign-of q with ↥ q
... | + zero    = zer
... | + (suc _) = pos
... | -[1+ _ ]  = neg

infixl 20 _+ˢ_
_+ˢ_ : Sign → Sign → Sign
zer +ˢ y   = y
unk +ˢ y   = unk
pos +ˢ zer = pos
pos +ˢ pos = pos
pos +ˢ neg = unk
pos +ˢ unk = unk
neg +ˢ zer = neg
neg +ˢ pos = unk
neg +ˢ neg = neg
neg +ˢ unk = unk

infixl 21 _·ˢ_
_·ˢ_ : Sign → Sign → Sign
zer ·ˢ y   = zer
pos ·ˢ y   = y
neg ·ˢ zer = zer
neg ·ˢ pos = neg
neg ·ˢ neg = pos
neg ·ˢ unk = unk
unk ·ˢ zer = zer
unk ·ˢ pos = unk
unk ·ˢ neg = unk
unk ·ˢ unk = unk

+ˢ-comm : ∀ x y → (x +ˢ y) ≡ (y +ˢ x)
+ˢ-comm pos pos = refl
+ˢ-comm pos zer = refl
+ˢ-comm pos neg = refl
+ˢ-comm pos unk = refl
+ˢ-comm zer pos = refl
+ˢ-comm zer zer = refl
+ˢ-comm zer neg = refl
+ˢ-comm zer unk = refl
+ˢ-comm neg pos = refl
+ˢ-comm neg zer = refl
+ˢ-comm neg neg = refl
+ˢ-comm neg unk = refl
+ˢ-comm unk pos = refl
+ˢ-comm unk zer = refl
+ˢ-comm unk neg = refl
+ˢ-comm unk unk = refl

+ˢ-assoc : ∀ x y z → ((x +ˢ y) +ˢ z) ≡ (x +ˢ (y +ˢ z))
+ˢ-assoc zer y z = refl
+ˢ-assoc unk y z = refl
+ˢ-assoc pos zer z = refl
+ˢ-assoc pos pos zer = refl
+ˢ-assoc pos pos pos = refl
+ˢ-assoc pos pos neg = refl
+ˢ-assoc pos pos unk = refl
+ˢ-assoc pos neg zer = refl
+ˢ-assoc pos neg pos = refl
+ˢ-assoc pos neg neg = refl
+ˢ-assoc pos neg unk = refl
+ˢ-assoc pos unk z = refl
+ˢ-assoc neg zer z = refl
+ˢ-assoc neg pos zer = refl
+ˢ-assoc neg pos pos = refl
+ˢ-assoc neg pos neg = refl
+ˢ-assoc neg pos unk = refl
+ˢ-assoc neg neg zer = refl
+ˢ-assoc neg neg pos = refl
+ˢ-assoc neg neg neg = refl
+ˢ-assoc neg neg unk = refl
+ˢ-assoc neg unk z = refl

·ˢ-comm : ∀ x y → (x ·ˢ y) ≡ (y ·ˢ x)
·ˢ-comm pos pos = refl
·ˢ-comm pos zer = refl
·ˢ-comm pos neg = refl
·ˢ-comm pos unk = refl
·ˢ-comm zer pos = refl
·ˢ-comm zer zer = refl
·ˢ-comm zer neg = refl
·ˢ-comm zer unk = refl
·ˢ-comm neg pos = refl
·ˢ-comm neg zer = refl
·ˢ-comm neg neg = refl
·ˢ-comm neg unk = refl
·ˢ-comm unk pos = refl
·ˢ-comm unk zer = refl
·ˢ-comm unk neg = refl
·ˢ-comm unk unk = refl

·ˢ-assoc : ∀ x y z → ((x ·ˢ y) ·ˢ z) ≡ (x ·ˢ (y ·ˢ z))
·ˢ-assoc zer y z = refl
·ˢ-assoc pos y z = refl
·ˢ-assoc neg zer z = refl
·ˢ-assoc neg pos z = refl
·ˢ-assoc neg neg zer = refl
·ˢ-assoc neg neg pos = refl
·ˢ-assoc neg neg neg = refl
·ˢ-assoc neg neg unk = refl
·ˢ-assoc neg unk zer = refl
·ˢ-assoc neg unk pos = refl
·ˢ-assoc neg unk neg = refl
·ˢ-assoc neg unk unk = refl
·ˢ-assoc unk zer z = refl
·ˢ-assoc unk pos z = refl
·ˢ-assoc unk neg zer = refl
·ˢ-assoc unk neg pos = refl
·ˢ-assoc unk neg neg = refl
·ˢ-assoc unk neg unk = refl
·ˢ-assoc unk unk zer = refl
·ˢ-assoc unk unk pos = refl
·ˢ-assoc unk unk neg = refl
·ˢ-assoc unk unk unk = refl

distribˢ : ∀ x y z → (x ·ˢ (y +ˢ z)) ≡ ((x ·ˢ y) +ˢ (x ·ˢ z))
distribˢ zer y z = refl
distribˢ pos y z = refl
distribˢ neg zer z = refl
distribˢ neg pos zer = refl
distribˢ neg pos pos = refl
distribˢ neg pos neg = refl
distribˢ neg pos unk = refl
distribˢ neg neg zer = refl
distribˢ neg neg pos = refl
distribˢ neg neg neg = refl
distribˢ neg neg unk = refl
distribˢ neg unk z = refl
distribˢ unk zer z = refl
distribˢ unk pos zer = refl
distribˢ unk pos pos = refl
distribˢ unk pos neg = refl
distribˢ unk pos unk = refl
distribˢ unk neg zer = refl
distribˢ unk neg pos = refl
distribˢ unk neg neg = refl
distribˢ unk neg unk = refl
distribˢ unk unk z = refl

------------------------------------------------------------------------------
-- Packaging.

setoid : Setoid 0ℓ 0ℓ
setoid .Setoid.Carrier = Sign
setoid .Setoid._≈_ a b = LiftS 0ℓ (a ≡ b)
setoid .Setoid.isEquivalence .IsEquivalence.refl = liftS refl
setoid .Setoid.isEquivalence .IsEquivalence.sym (liftS e) = liftS (sym e)
setoid .Setoid.isEquivalence .IsEquivalence.trans (liftS e₁) (liftS e₂) = liftS (trans e₁ e₂)

additive : CommutativeMonoid setoid
additive .CommutativeMonoid.ε = zer
additive .CommutativeMonoid._+_ = _+ˢ_
additive .CommutativeMonoid.+-cong (liftS e₁) (liftS e₂) = liftS (cong₂ _+ˢ_ e₁ e₂)
additive .CommutativeMonoid.+-lunit = liftS refl
additive .CommutativeMonoid.+-assoc {x} {y} {z} = liftS (+ˢ-assoc x y z)
additive .CommutativeMonoid.+-comm {x} {y} = liftS (+ˢ-comm x y)

multiplicative : CommutativeMonoid setoid
multiplicative .CommutativeMonoid.ε = pos
multiplicative .CommutativeMonoid._+_ = _·ˢ_
multiplicative .CommutativeMonoid.+-cong (liftS e₁) (liftS e₂) = liftS (cong₂ _·ˢ_ e₁ e₂)
multiplicative .CommutativeMonoid.+-lunit = liftS refl
multiplicative .CommutativeMonoid.+-assoc {x} {y} {z} = liftS (·ˢ-assoc x y z)
multiplicative .CommutativeMonoid.+-comm {x} {y} = liftS (·ˢ-comm x y)

semiring : CommutativeSemiring setoid
semiring .CommutativeSemiring.additive = additive
semiring .CommutativeSemiring.multiplicative = multiplicative
semiring .CommutativeSemiring.·-+-distribₗ {x} {y} {z} = liftS (distribˢ x y z)
semiring .CommutativeSemiring.ε-annihilₗ = liftS refl
