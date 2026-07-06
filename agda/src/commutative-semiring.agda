{-# OPTIONS --prop --postfix-projections --safe #-}

module commutative-semiring where

open import Level using (_⊔_)
open import prop-setoid using (Setoid)
open import commutative-monoid using (CommutativeMonoid)

record CommutativeSemiring {o e} (A : Setoid o e) : Set (o ⊔ e) where
  open Setoid A public

  field
    additive : CommutativeMonoid A
    multiplicative : CommutativeMonoid A

  open CommutativeMonoid additive public
  open CommutativeMonoid multiplicative public
    renaming (ε to ι; _+_ to _·_; +-cong to ·-cong; +-lunit to ·-lunit; +-assoc to ·-assoc; +-comm to ·-comm; +-interchange to ·-interchange)

  field
    ·-+-distribₗ : ∀ {x y z} → x · (y + z) ≈ (x · y) + (x · z)
    ε-annihilₗ : ∀ {x} → ε · x ≈ ε

  ·-+-distribᵣ : ∀ {x y z} → (y + z) · x ≈ (y · x) + (z · x)
  ·-+-distribᵣ = trans ·-comm (trans ·-+-distribₗ (+-cong ·-comm ·-comm))

  ε-annihilᵣ : ∀ {x} → x · ε ≈ ε
  ε-annihilᵣ = trans ·-comm ε-annihilₗ

-- The additional data making a commutative semiring a Boolean algebra.
record BooleanAlgebra {o e} {A : Setoid o e} (S : CommutativeSemiring A) : Set (o ⊔ e) where
  open CommutativeSemiring S
  field
    ∧-idem : ∀ {x} → (x · x) ≈ x
    ⊤-add-top : ∀ {x} → (ι + x) ≈ ι
    ¬ : Carrier → Carrier
    compl-∧ : ∀ {x} → ((x · ¬ x) + ε) ≈ ε
    compl-∨ : ∀ {x} → (ι + (x + ¬ x)) ≈ (x + ¬ x)

-- Lax homomorphisms: preserving + and · up to the target's additive preorder x ⊑ y = (x + y) ≈ y, and ε, ι
-- exactly.
-- Homomorphisms: preserving all the structure exactly.
record _⇒h_ {o₁ e₁ o₂ e₂} {A : Setoid o₁ e₁} {B : Setoid o₂ e₂}
            (S : CommutativeSemiring A) (T : CommutativeSemiring B) : Set (o₁ ⊔ e₁ ⊔ o₂ ⊔ e₂) where
  private
    module S = CommutativeSemiring S
    module T = CommutativeSemiring T

  field
    f      : S.Carrier → T.Carrier
    f-cong : ∀ {a b} → a S.≈ b → f a T.≈ f b
    f-+    : ∀ {a b} → f (a S.+ b) T.≈ (f a T.+ f b)
    f-·    : ∀ {a b} → f (a S.· b) T.≈ (f a T.· f b)
    f-ε    : f S.ε T.≈ T.ε
    f-ι    : f S.ι T.≈ T.ι

record _⇒ˡ_ {o₁ e₁ o₂ e₂} {A : Setoid o₁ e₁} {B : Setoid o₂ e₂}
            (S : CommutativeSemiring A) (T : CommutativeSemiring B) : Set (o₁ ⊔ e₁ ⊔ o₂ ⊔ e₂) where
  private
    module S = CommutativeSemiring S
    module T = CommutativeSemiring T

  _⊑_ : T.Carrier → T.Carrier → Prop e₂
  x ⊑ y = (x T.+ y) T.≈ y

  field
    f      : S.Carrier → T.Carrier
    f-cong : ∀ {a b} → a S.≈ b → f a T.≈ f b
    f-+    : ∀ {a b} → f (a S.+ b) ⊑ (f a T.+ f b)
    f-·    : ∀ {a b} → f (a S.· b) ⊑ (f a T.· f b)
    f-ε    : f S.ε T.≈ T.ε
    f-ι    : f S.ι T.≈ T.ι
