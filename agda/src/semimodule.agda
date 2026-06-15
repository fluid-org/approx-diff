{-# OPTIONS --postfix-projections --prop --safe #-}

module semimodule where

open import Level using (suc; _⊔_)
open import prop-setoid using (Setoid; IsEquivalence)
open import commutative-monoid using (CommutativeMonoid)
open import commutative-semiring using (CommutativeSemiring)
open import categories using (Category)

-- The category of all S-semimodules and their linear homomorphisms.  Unlike
-- FDSemiMod (the free finitely-generated ones) this is an algebraic category,
-- so it is complete: limits are computed pointwise, with no bound on the size
-- of carriers.  It is the limit-complete target into which FDSemiMod embeds,
-- playing the role JoinSLat plays for the join-semilattice development.
module SemiMod {o ℓ} {A : Setoid o ℓ} (S : CommutativeSemiring A) where

  open CommutativeSemiring S
    using ()
    renaming (Carrier to Scalar; _≈_ to _≈ₛ_; _+_ to _+ₛ_; _·_ to _·ₛ_; ε to εₛ; ι to ιₛ)

  ----------------------------------------------------------------------------
  -- Objects: a setoid carrying a commutative monoid and a scalar action.

  record SemiModule : Set (suc (o ⊔ ℓ)) where
    no-eta-equality
    field
      carrier : Setoid o ℓ
    open Setoid carrier public
    field
      +-monoid : CommutativeMonoid carrier
    open CommutativeMonoid +-monoid public
    field
      scale      : Scalar → Carrier → Carrier
      scale-cong : ∀ {a a′ x x′} → a ≈ₛ a′ → x ≈ x′ → scale a x ≈ scale a′ x′
      scale-+ᵣ   : ∀ {a x y} → scale a (x + y) ≈ (scale a x + scale a y)        -- a·(x+y)
      scale-+ₗ   : ∀ {a b x} → scale (a +ₛ b) x ≈ (scale a x + scale b x)       -- (a+b)·x
      scale-·    : ∀ {a b x} → scale (a ·ₛ b) x ≈ scale a (scale b x)           -- (ab)·x
      scale-ι    : ∀ {x} → scale ιₛ x ≈ x                                       -- 1·x
      scale-0ₗ   : ∀ {x} → scale εₛ x ≈ ε                                       -- 0·x
      scale-0ᵣ   : ∀ {a} → scale a ε ≈ ε                                        -- a·0
  open SemiModule

  ----------------------------------------------------------------------------
  -- Morphisms: linear maps preserving +, ε and the scalar action.

  record _⇒_ (M N : SemiModule) : Set (o ⊔ ℓ) where
    no-eta-equality
    open SemiModule M using () renaming (Carrier to ∣M∣; _≈_ to _≈ᴹ_; _+_ to _+ᴹ_; ε to εᴹ; scale to scaleᴹ)
    open SemiModule N using () renaming (Carrier to ∣N∣; _≈_ to _≈ᴺ_; _+_ to _+ᴺ_; ε to εᴺ; scale to scaleᴺ)
    field
      func             : ∣M∣ → ∣N∣
      func-resp-≈      : ∀ {x y} → x ≈ᴹ y → func x ≈ᴺ func y
      +-preserving     : ∀ {x y} → func (x +ᴹ y) ≈ᴺ (func x +ᴺ func y)
      ε-preserving     : func εᴹ ≈ᴺ εᴺ
      scale-preserving : ∀ {a x} → func (scaleᴹ a x) ≈ᴺ scaleᴺ a (func x)
  open _⇒_ public

  -- Extensional (pointwise) equality of morphisms.
  infix 4 _≃_
  _≃_ : ∀ {M N} → M ⇒ N → M ⇒ N → Prop (o ⊔ ℓ)
  _≃_ {M} {N} f g = ∀ x → N ._≈_ (f .func x) (g .func x)

  ≃-isEquiv : ∀ {M N} → IsEquivalence (_≃_ {M} {N})
  ≃-isEquiv {N = N} .IsEquivalence.refl x = N .refl
  ≃-isEquiv {N = N} .IsEquivalence.sym f≃g x = N .sym (f≃g x)
  ≃-isEquiv {N = N} .IsEquivalence.trans f≃g g≃h x = N .trans (f≃g x) (g≃h x)

  ----------------------------------------------------------------------------
  -- Identity and composition.

  id : ∀ {M} → M ⇒ M
  id .func x = x
  id .func-resp-≈ x≈y = x≈y
  id {M} .+-preserving = M .refl
  id {M} .ε-preserving = M .refl
  id {M} .scale-preserving = M .refl

  infixl 21 _∘_
  _∘_ : ∀ {M N P} → N ⇒ P → M ⇒ N → M ⇒ P
  (g ∘ f) .func x = g .func (f .func x)
  (g ∘ f) .func-resp-≈ x≈y = g .func-resp-≈ (f .func-resp-≈ x≈y)
  _∘_ {P = P} g f .+-preserving = P .trans (g .func-resp-≈ (f .+-preserving)) (g .+-preserving)
  _∘_ {P = P} g f .ε-preserving = P .trans (g .func-resp-≈ (f .ε-preserving)) (g .ε-preserving)
  _∘_ {P = P} g f .scale-preserving = P .trans (g .func-resp-≈ (f .scale-preserving)) (g .scale-preserving)

  ----------------------------------------------------------------------------
  -- The category of S-semimodules.  Laws inline by copattern (no eta).

  cat : Category (suc (o ⊔ ℓ)) (o ⊔ ℓ) (o ⊔ ℓ)
  cat .Category.obj = SemiModule
  cat .Category._⇒_ M N = M ⇒ N
  cat .Category._≈_ = _≃_
  cat .Category.isEquiv = ≃-isEquiv
  cat .Category.id M = id
  cat .Category._∘_ = _∘_
  cat .Category.∘-cong {z = P} {f₁ = F₁} {g₂ = G₂} F≃ G≃ x =
    P .trans (F₁ .func-resp-≈ (G≃ x)) (F≃ (G₂ .func x))
  cat .Category.id-left {y = N} x = N .refl
  cat .Category.id-right {y = N} x = N .refl
  cat .Category.assoc {z = P} f g h x = P .refl
