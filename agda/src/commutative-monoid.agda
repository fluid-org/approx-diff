{-# OPTIONS --prop --postfix-projections --safe #-}

module commutative-monoid where

open import Level
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import prop
open import prop-setoid
  using (Setoid; IsEquivalence; idS; _∘S_; ⊗-setoid; 𝟙; module ≈-Reasoning)
  renaming (_⇒_ to _⇒s_; _≃m_ to _≃s_; ≃m-isEquivalence to ≃s-isEquivalence)

------------------------------------------------------------------------------
-- Commutative Monoid structure on setoids
--
record CommutativeMonoid {o e} (A : Setoid o e) : Set (o ⊔ e) where
  open Setoid A
  field
    ε   : Carrier
    _+_ : Carrier → Carrier → Carrier

  infixl 21 _+_

  field
    +-cong  : ∀ {x₁ x₂ y₁ y₂} → x₁ ≈ x₂ → y₁ ≈ y₂ → (x₁ + y₁) ≈ (x₂ + y₂)
    +-lunit : ∀ {x} → (ε + x) ≈ x
    +-assoc : ∀ {x y z} → ((x + y) + z) ≈ (x + (y + z))
    +-comm  : ∀ {x y} → (x + y) ≈ (y + x)

  +-runit : ∀ {x} → (x + ε) ≈ x
  +-runit = trans +-comm +-lunit

  +-interchange : ∀ {w x y z} → (w + x) + (y + z) ≈ (w + y) + (x + z)
  +-interchange {w}{x}{y}{z} = begin
      (w + x) + (y + z)     ≈⟨ +-assoc ⟩
      w + (x + (y + z))     ≈⟨ +-cong refl (sym +-assoc) ⟩
      w + ((x + y) + z)     ≈⟨ +-cong refl (+-cong +-comm refl) ⟩
      w + ((y + x) + z)     ≈⟨ +-cong refl +-assoc ⟩
      w + (y + (x + z))     ≈⟨ sym +-assoc ⟩
      (w + y) + (x + z)     ∎
    where open ≈-Reasoning isEquivalence

------------------------------------------------------------------------------
-- The additive preorder x ⊑ y iff x + y ≈ y. When addition is idempotent this is a preorder with
-- monotone addition, joins given by + and bottom ε.
module AdditivePreorder {o e} {A : Setoid o e} (M : CommutativeMonoid A)
  (let open CommutativeMonoid M) (let open Setoid A)
  (+-idem : ∀ {x} → (x + x) ≈ x)
  where

  open import basics using (IsPreorder; IsJoin; IsBottom)

  infix 4 _⊑_

  _⊑_ : Carrier → Carrier → Prop e
  x ⊑ y = (x + y) ≈ y

  ⊑-refl : ∀ {x} → x ⊑ x
  ⊑-refl = +-idem

  ⊑-trans : ∀ {x y z} → x ⊑ y → y ⊑ z → x ⊑ z
  ⊑-trans x⊑y y⊑z = trans (+-cong refl (sym y⊑z)) (trans (sym +-assoc) (trans (+-cong x⊑y refl) y⊑z))

  ≈→⊑ : ∀ {x y} → x ≈ y → x ⊑ y
  ≈→⊑ x≈y = trans (+-cong x≈y refl) +-idem

  ⊑-antisym : ∀ {x y} → x ⊑ y → y ⊑ x → x ≈ y
  ⊑-antisym x⊑y y⊑x = trans (sym y⊑x) (trans +-comm x⊑y)

  +-mono-⊑ : ∀ {x₁ x₂ y₁ y₂} → x₁ ⊑ y₁ → x₂ ⊑ y₂ → (x₁ + x₂) ⊑ (y₁ + y₂)
  +-mono-⊑ p q = trans +-interchange (+-cong p q)

  ⊑-isPreorder : IsPreorder _⊑_
  ⊑-isPreorder .IsPreorder.refl = ⊑-refl
  ⊑-isPreorder .IsPreorder.trans = ⊑-trans

  ∨-isJoin : IsJoin ⊑-isPreorder _+_
  ∨-isJoin .IsJoin.inl = trans (sym +-assoc) (+-cong +-idem refl)
  ∨-isJoin .IsJoin.inr =
    trans (+-cong refl +-comm) (trans (sym +-assoc) (trans (+-cong +-idem refl) +-comm))
  ∨-isJoin .IsJoin.[_,_] x⊑z y⊑z = trans +-assoc (trans (+-cong refl y⊑z) x⊑z)

  ⊥-isBottom : IsBottom ⊑-isPreorder ε
  ⊥-isBottom .IsBottom.≤-bottom = +-lunit

------------------------------------------------------------------------------
record _=[_]>_ {o e}{A B : Setoid o e}(X : CommutativeMonoid A)(f : A ⇒s B)(Y : CommutativeMonoid B) : Prop (o ⊔ e) where
  private
    module X = CommutativeMonoid X
    module Y = CommutativeMonoid Y
  open _⇒s_ f
  open Setoid B
  field
    preserve-ε : func X.ε ≈ Y.ε
    preserve-+ : ∀ {x₁ x₂} → func (x₁ X.+ x₂) ≈ (func x₁ Y.+ func x₂)
open _=[_]>_

module _ where

  open CommutativeMonoid

  𝟙cm : ∀ {o e} → CommutativeMonoid (𝟙 {o} {e})
  𝟙cm .ε = lift tt
  𝟙cm ._+_ _ _ = lift tt
  𝟙cm .+-cong _ _ = tt
  𝟙cm .+-lunit = tt
  𝟙cm .+-assoc = tt
  𝟙cm .+-comm = tt

  _⊗_ : ∀ {o e}{A B : Setoid o e} →
        CommutativeMonoid A →
        CommutativeMonoid B →
        CommutativeMonoid (⊗-setoid A B)
  (X ⊗ Y) .ε = X .ε , Y .ε
  (X ⊗ Y) ._+_ (x₁ , y₁) (x₂ , y₂) = X ._+_ x₁ x₂ , Y ._+_ y₁ y₂
  (X ⊗ Y) .+-cong (x₁≈x₂ , y₁≈y₂) (x'₁≈x'₂ , y'₁≈y'₂) =
     X .+-cong x₁≈x₂ x'₁≈x'₂ , Y .+-cong y₁≈y₂ y'₁≈y'₂
  (X ⊗ Y) .+-lunit = X .+-lunit , Y .+-lunit
  (X ⊗ Y) .+-assoc = X .+-assoc , Y .+-assoc
  (X ⊗ Y) .+-comm = X .+-comm , Y .+-comm
