{-# OPTIONS --prop --postfix-projections --safe #-}

-- The perturbation-bound semiring ℚ∞ = (ℚ ∪ {∞}, min, ∞, +, 0): the min-plus tropical semiring used to model
-- interval approximations. A perturbation bound records how far an endpoint sits from the nominated point; ∞
-- is "no information".  Information-join is min (tighter bound wins) and the multiplicative structure is
-- ordinary addition.

module semiring-Q-tropical where

open import Level using (0ℓ)
open import Data.Rational using (ℚ; 0ℚ; _⊓_; _+_)
open import Data.Rational.Properties using
  (⊓-comm; ⊓-assoc; +-comm; +-assoc; +-identityˡ; +-monoʳ-≤; mono-≤-distrib-⊓)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import prop using (LiftS; liftS)
open import prop-setoid using (Setoid; IsEquivalence)
open import commutative-monoid using (CommutativeMonoid)
open import commutative-semiring using (CommutativeSemiring)

data ℚ∞ : Set where
  ∞   : ℚ∞
  fin : ℚ → ℚ∞

-- min, with ∞ the (largest) additive identity.
infixl 20 _⊓ᴰ_
_⊓ᴰ_ : ℚ∞ → ℚ∞ → ℚ∞
∞     ⊓ᴰ y     = y
fin p ⊓ᴰ ∞     = fin p
fin p ⊓ᴰ fin q = fin (p ⊓ q)

-- arithmetic +, with ∞ absorbing.
infixl 21 _+ᴰ_
_+ᴰ_ : ℚ∞ → ℚ∞ → ℚ∞
∞     +ᴰ y     = ∞
fin p +ᴰ ∞     = ∞
fin p +ᴰ fin q = fin (p + q)

------------------------------------------------------------------------------
-- Equational laws, on ≡, by cases on ∞/fin.

⊓ᴰ-comm : ∀ a b → a ⊓ᴰ b ≡ b ⊓ᴰ a
⊓ᴰ-comm ∞ ∞ = refl
⊓ᴰ-comm ∞ (fin q) = refl
⊓ᴰ-comm (fin p) ∞ = refl
⊓ᴰ-comm (fin p) (fin q) = cong fin (⊓-comm p q)

⊓ᴰ-assoc : ∀ a b c → (a ⊓ᴰ b) ⊓ᴰ c ≡ a ⊓ᴰ (b ⊓ᴰ c)
⊓ᴰ-assoc ∞ b c = refl
⊓ᴰ-assoc (fin p) ∞ c = refl
⊓ᴰ-assoc (fin p) (fin q) ∞ = refl
⊓ᴰ-assoc (fin p) (fin q) (fin r) = cong fin (⊓-assoc p q r)

+ᴰ-comm : ∀ a b → a +ᴰ b ≡ b +ᴰ a
+ᴰ-comm ∞ ∞ = refl
+ᴰ-comm ∞ (fin q) = refl
+ᴰ-comm (fin p) ∞ = refl
+ᴰ-comm (fin p) (fin q) = cong fin (+-comm p q)

+ᴰ-assoc : ∀ a b c → (a +ᴰ b) +ᴰ c ≡ a +ᴰ (b +ᴰ c)
+ᴰ-assoc ∞ b c = refl
+ᴰ-assoc (fin p) ∞ c = refl
+ᴰ-assoc (fin p) (fin q) ∞ = refl
+ᴰ-assoc (fin p) (fin q) (fin r) = cong fin (+-assoc p q r)

+ᴰ-lunit : ∀ a → fin 0ℚ +ᴰ a ≡ a
+ᴰ-lunit ∞ = refl
+ᴰ-lunit (fin q) = cong fin (+-identityˡ q)

-- · distributes over + (= ordinary + over min): the one nontrivial law.
distrib : ∀ a b c → a +ᴰ (b ⊓ᴰ c) ≡ (a +ᴰ b) ⊓ᴰ (a +ᴰ c)
distrib ∞ b c = refl
distrib (fin p) ∞ c = refl
distrib (fin p) (fin q) ∞ = refl
distrib (fin p) (fin q) (fin r) = cong fin (mono-≤-distrib-⊓ (+-monoʳ-≤ p) q r)

------------------------------------------------------------------------------
-- Packaging.

setoid : Setoid 0ℓ 0ℓ
setoid .Setoid.Carrier = ℚ∞
setoid .Setoid._≈_ a b = LiftS 0ℓ (a ≡ b)
setoid .Setoid.isEquivalence .IsEquivalence.refl = liftS refl
setoid .Setoid.isEquivalence .IsEquivalence.sym (liftS e) = liftS (sym e)
setoid .Setoid.isEquivalence .IsEquivalence.trans (liftS e₁) (liftS e₂) = liftS (trans e₁ e₂)

additive : CommutativeMonoid setoid
additive .CommutativeMonoid.ε = ∞
additive .CommutativeMonoid._+_ = _⊓ᴰ_
additive .CommutativeMonoid.+-cong (liftS e₁) (liftS e₂) = liftS (cong₂ _⊓ᴰ_ e₁ e₂)
  where open import Relation.Binary.PropositionalEquality using (cong₂)
additive .CommutativeMonoid.+-lunit = liftS refl
additive .CommutativeMonoid.+-assoc {x} {y} {z} = liftS (⊓ᴰ-assoc x y z)
additive .CommutativeMonoid.+-comm {x} {y} = liftS (⊓ᴰ-comm x y)

multiplicative : CommutativeMonoid setoid
multiplicative .CommutativeMonoid.ε = fin 0ℚ
multiplicative .CommutativeMonoid._+_ = _+ᴰ_
multiplicative .CommutativeMonoid.+-cong (liftS e₁) (liftS e₂) = liftS (cong₂ _+ᴰ_ e₁ e₂)
  where open import Relation.Binary.PropositionalEquality using (cong₂)
multiplicative .CommutativeMonoid.+-lunit {x} = liftS (+ᴰ-lunit x)
multiplicative .CommutativeMonoid.+-assoc {x} {y} {z} = liftS (+ᴰ-assoc x y z)
multiplicative .CommutativeMonoid.+-comm {x} {y} = liftS (+ᴰ-comm x y)

semiring : CommutativeSemiring setoid
semiring .CommutativeSemiring.additive = additive
semiring .CommutativeSemiring.multiplicative = multiplicative
semiring .CommutativeSemiring.·-+-distribₗ {x} {y} {z} = liftS (distrib x y z)
semiring .CommutativeSemiring.ε-annihilₗ = liftS refl
