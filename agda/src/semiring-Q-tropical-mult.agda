{-# OPTIONS --prop --postfix-projections --safe #-}

-- The relative perturbation-bound semiring ℚ≥0∞ = (ℚ≥0 ∪ {∞}, min, ∞, ×, 1): the min-times
-- (multiplicative tropical) semiring, log-isomorphic to min-plus. A scalar bounds the factor by
-- which a value may change from its value in the run; ∞ is "no information". Information-join is
-- min (tighter bound wins) and the multiplicative structure is ordinary multiplication.
module semiring-Q-tropical-mult where

open import Level using (0ℓ)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _⊓_; _*_; _≤_; NonNegative; nonNegative)
open import Data.Rational.Properties using
  (⊓-comm; ⊓-assoc; *-comm; *-assoc; *-identityˡ; *-zeroˡ; ⊓-glb; ≤-trans; ≤-reflexive;
   *-monoʳ-≤-nonNeg; *-distribˡ-⊓-nonNeg; nonNegative⁻¹)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import prop using (LiftS; liftS; ⊤; ⊥; tt)
open import prop-setoid using (Setoid; IsEquivalence)
open import commutative-monoid using (CommutativeMonoid)
open import commutative-semiring using (CommutativeSemiring)

data ℚ≥0∞ : Set where
  ∞   : ℚ≥0∞
  fin : (q : ℚ) → .{{NonNegative q}} → ℚ≥0∞

private
  ⊓-nonneg : ∀ (p q : ℚ) .{{_ : NonNegative p}} .{{_ : NonNegative q}} → NonNegative (p ⊓ q)
  ⊓-nonneg p q = nonNegative (⊓-glb (nonNegative⁻¹ p) (nonNegative⁻¹ q))

  *-nonneg : ∀ (p q : ℚ) .{{_ : NonNegative p}} .{{_ : NonNegative q}} → NonNegative (p * q)
  *-nonneg p q = nonNegative
    (≤-trans (≤-reflexive (sym (*-zeroˡ q))) (*-monoʳ-≤-nonNeg q (nonNegative⁻¹ p)))

-- min, with ∞ the (largest) additive identity.
infixl 20 _⊓ᴰ_
_⊓ᴰ_ : ℚ≥0∞ → ℚ≥0∞ → ℚ≥0∞
∞     ⊓ᴰ y     = y
fin p ⊓ᴰ ∞     = fin p
fin p ⊓ᴰ fin q = fin (p ⊓ q) ⦃ ⊓-nonneg p q ⦄

-- arithmetic ×, with ∞ absorbing.
infixl 21 _×ᴰ_
_×ᴰ_ : ℚ≥0∞ → ℚ≥0∞ → ℚ≥0∞
∞     ×ᴰ y     = ∞
fin p ×ᴰ ∞     = ∞
fin p ×ᴰ fin q = fin (p * q) ⦃ *-nonneg p q ⦄

------------------------------------------------------------------------------
-- Setoid equality compares the underlying rationals, so the (irrelevant) nonnegativity proofs
-- never obstruct the laws.

infix 4 _≈ᴰ_
_≈ᴰ_ : ℚ≥0∞ → ℚ≥0∞ → Prop 0ℓ
∞     ≈ᴰ ∞     = ⊤
∞     ≈ᴰ fin _ = ⊥
fin _ ≈ᴰ ∞     = ⊥
fin p ≈ᴰ fin q = LiftS 0ℓ (p ≡ q)

private
  ≈ᴰ-refl : ∀ a → a ≈ᴰ a
  ≈ᴰ-refl ∞ = tt
  ≈ᴰ-refl (fin p) = liftS refl

  ≈ᴰ-sym : ∀ a b → a ≈ᴰ b → b ≈ᴰ a
  ≈ᴰ-sym ∞ ∞ e = tt
  ≈ᴰ-sym (fin p) (fin q) (liftS e) = liftS (sym e)

  ≈ᴰ-trans : ∀ a b c → a ≈ᴰ b → b ≈ᴰ c → a ≈ᴰ c
  ≈ᴰ-trans ∞ ∞ ∞ e₁ e₂ = tt
  ≈ᴰ-trans (fin p) (fin q) (fin r) (liftS e₁) (liftS e₂) = liftS (trans e₁ e₂)

  ⊓ᴰ-cong : ∀ a a' b b' → a ≈ᴰ a' → b ≈ᴰ b' → (a ⊓ᴰ b) ≈ᴰ (a' ⊓ᴰ b')
  ⊓ᴰ-cong ∞ ∞ b b' _ e₂ = e₂
  ⊓ᴰ-cong (fin p) (fin p') ∞ ∞ e₁ _ = e₁
  ⊓ᴰ-cong (fin p) (fin p') (fin q) (fin q') (liftS e₁) (liftS e₂) = liftS (cong₂ _⊓_ e₁ e₂)

  ×ᴰ-cong : ∀ a a' b b' → a ≈ᴰ a' → b ≈ᴰ b' → (a ×ᴰ b) ≈ᴰ (a' ×ᴰ b')
  ×ᴰ-cong ∞ ∞ b b' _ _ = tt
  ×ᴰ-cong (fin p) (fin p') ∞ ∞ e₁ _ = tt
  ×ᴰ-cong (fin p) (fin p') (fin q) (fin q') (liftS e₁) (liftS e₂) = liftS (cong₂ _*_ e₁ e₂)

⊓ᴰ-comm : ∀ a b → (a ⊓ᴰ b) ≈ᴰ (b ⊓ᴰ a)
⊓ᴰ-comm ∞ ∞ = tt
⊓ᴰ-comm ∞ (fin q) = liftS refl
⊓ᴰ-comm (fin p) ∞ = liftS refl
⊓ᴰ-comm (fin p) (fin q) = liftS (⊓-comm p q)

⊓ᴰ-assoc : ∀ a b c → ((a ⊓ᴰ b) ⊓ᴰ c) ≈ᴰ (a ⊓ᴰ (b ⊓ᴰ c))
⊓ᴰ-assoc ∞ b c = ≈ᴰ-refl (b ⊓ᴰ c)
⊓ᴰ-assoc (fin p) ∞ c = ≈ᴰ-refl (fin p ⊓ᴰ c)
⊓ᴰ-assoc (fin p) (fin q) ∞ = liftS refl
⊓ᴰ-assoc (fin p) (fin q) (fin r) = liftS (⊓-assoc p q r)

×ᴰ-comm : ∀ a b → (a ×ᴰ b) ≈ᴰ (b ×ᴰ a)
×ᴰ-comm ∞ ∞ = tt
×ᴰ-comm ∞ (fin q) = tt
×ᴰ-comm (fin p) ∞ = tt
×ᴰ-comm (fin p) (fin q) = liftS (*-comm p q)

×ᴰ-assoc : ∀ a b c → ((a ×ᴰ b) ×ᴰ c) ≈ᴰ (a ×ᴰ (b ×ᴰ c))
×ᴰ-assoc ∞ b c = tt
×ᴰ-assoc (fin p) ∞ c = tt
×ᴰ-assoc (fin p) (fin q) ∞ = tt
×ᴰ-assoc (fin p) (fin q) (fin r) = liftS (*-assoc p q r)

1≥0 : NonNegative 1ℚ
1≥0 = _

×ᴰ-lunit : ∀ a → (fin 1ℚ ⦃ 1≥0 ⦄ ×ᴰ a) ≈ᴰ a
×ᴰ-lunit ∞ = tt
×ᴰ-lunit (fin q) = liftS (*-identityˡ q)

-- · distributes over + (= ordinary × over min); the one nontrivial law.
distrib : ∀ a b c → (a ×ᴰ (b ⊓ᴰ c)) ≈ᴰ ((a ×ᴰ b) ⊓ᴰ (a ×ᴰ c))
distrib ∞ b c = tt
distrib (fin p) ∞ c = ≈ᴰ-refl (fin p ×ᴰ c)
distrib (fin p) (fin q) ∞ = liftS refl
distrib (fin p) (fin q) (fin r) = liftS (*-distribˡ-⊓-nonNeg p q r)

------------------------------------------------------------------------------
-- Packaging.

setoid : Setoid 0ℓ 0ℓ
setoid .Setoid.Carrier = ℚ≥0∞
setoid .Setoid._≈_ = _≈ᴰ_
setoid .Setoid.isEquivalence .IsEquivalence.refl {a} = ≈ᴰ-refl a
setoid .Setoid.isEquivalence .IsEquivalence.sym {a} {b} = ≈ᴰ-sym a b
setoid .Setoid.isEquivalence .IsEquivalence.trans {a} {b} {c} = ≈ᴰ-trans a b c

additive : CommutativeMonoid setoid
additive .CommutativeMonoid.ε = ∞
additive .CommutativeMonoid._+_ = _⊓ᴰ_
additive .CommutativeMonoid.+-cong {x} {x'} {y} {y'} = ⊓ᴰ-cong x x' y y'
additive .CommutativeMonoid.+-lunit {x} = ≈ᴰ-refl x
additive .CommutativeMonoid.+-assoc {x} {y} {z} = ⊓ᴰ-assoc x y z
additive .CommutativeMonoid.+-comm {x} {y} = ⊓ᴰ-comm x y

multiplicative : CommutativeMonoid setoid
multiplicative .CommutativeMonoid.ε = fin 1ℚ ⦃ 1≥0 ⦄
multiplicative .CommutativeMonoid._+_ = _×ᴰ_
multiplicative .CommutativeMonoid.+-cong {x} {x'} {y} {y'} = ×ᴰ-cong x x' y y'
multiplicative .CommutativeMonoid.+-lunit {x} = ×ᴰ-lunit x
multiplicative .CommutativeMonoid.+-assoc {x} {y} {z} = ×ᴰ-assoc x y z
multiplicative .CommutativeMonoid.+-comm {x} {y} = ×ᴰ-comm x y

semiring : CommutativeSemiring setoid
semiring .CommutativeSemiring.additive = additive
semiring .CommutativeSemiring.multiplicative = multiplicative
semiring .CommutativeSemiring.·-+-distribₗ {x} {y} {z} = distrib x y z
semiring .CommutativeSemiring.ε-annihilₗ {x} = tt
