{-# OPTIONS --prop --postfix-projections --safe #-}

module nat where

open import Level using (0ℓ)
open import Data.Product using (_,_)
open import prop
open import basics
open import prop-setoid using (module ≈-Reasoning; Setoid; ⊗-setoid; 𝟙)
  renaming (_⇒_ to _⇒s_)

------------------------------------------------------------------------------
-- Reuse the builtin definitions so we get fast implementations

open import Agda.Builtin.Nat
  renaming (Nat to ℕ; suc to succ)
  using (_+_; _*_; zero)
  public

------------------------------------------------------------------------------
data _≤_ : ℕ → ℕ → Prop where
  0≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n → succ m ≤ succ n

infix 4 _≤_

succ-increasing : ∀ {x} → x ≤ succ x
succ-increasing {zero}   = 0≤n
succ-increasing {succ x} = s≤s succ-increasing

≤-refl : ∀ {x} → x ≤ x
≤-refl {zero}   = 0≤n
≤-refl {succ x} = s≤s ≤-refl

≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
≤-trans 0≤n       y≤z       = 0≤n
≤-trans (s≤s x≤y) (s≤s y≤z) = s≤s (≤-trans x≤y y≤z)

≤-isPreorder : IsPreorder _≤_
≤-isPreorder .IsPreorder.refl = ≤-refl
≤-isPreorder .IsPreorder.trans = ≤-trans

open IsPreorder ≤-isPreorder
  using (_≃_; ≃-refl; ≃-sym; ≃-trans)
  renaming (isEquivalence to ≃-isEquivalence)
  public

------------------------------------------------------------------------------
-- Equality and setoids

≃-zero : zero ≃ zero
≃-zero .proj₁ = 0≤n
≃-zero .proj₂ = 0≤n

succ-cong : ∀ {x y} → x ≃ y → succ x ≃ succ y
succ-cong p .proj₁ = s≤s (proj₁ p)
succ-cong p .proj₂ = s≤s (proj₂ p)

ℕₛ : Setoid 0ℓ 0ℓ
ℕₛ .Setoid.Carrier = ℕ
ℕₛ .Setoid._≈_ = _≃_
ℕₛ .Setoid.isEquivalence = ≃-isEquivalence

------------------------------------------------------------------------------
-- Addition

+-increasing : ∀ {x y} → y ≤ (x + y)
+-increasing {zero} = ≤-refl
+-increasing {succ x} = ≤-trans succ-increasing (s≤s (+-increasing {x}))

+-mono : ∀ {x₁ x₂ y₁ y₂} → x₁ ≤ x₂ → y₁ ≤ y₂ → (x₁ + y₁) ≤ (x₂ + y₂)
+-mono 0≤n     0≤n     = 0≤n
+-mono 0≤n     (s≤s q) = ≤-trans (s≤s q) +-increasing
+-mono (s≤s p) q       = s≤s (+-mono p q)

+-lunit : ∀ {x} → (zero + x) ≃ x
+-lunit = ≃-refl

+-runit : ∀ {x} → (x + zero) ≃ x
+-runit {zero}   = ≃-zero
+-runit {succ x} = succ-cong +-runit

+-assoc : ∀ {x y z} → ((x + y) + z) ≃ (x + (y + z))
+-assoc {zero}   = ≃-refl
+-assoc {succ x} = succ-cong (+-assoc {x})

+-isMonoid : IsMonoid ≤-isPreorder _+_ zero
+-isMonoid .IsMonoid.mono = +-mono
+-isMonoid .IsMonoid.assoc {x} {y} {z} = +-assoc {x} {y} {z}
+-isMonoid .IsMonoid.lunit = +-lunit
+-isMonoid .IsMonoid.runit = +-runit

open IsMonoid +-isMonoid
  using ()
  renaming (cong to +-cong; interchange to +-interchange)

+-succ : ∀ {x y} → (x + succ y) ≃ succ (x + y)
+-succ {zero}   = succ-cong ≃-refl
+-succ {succ x} = succ-cong +-succ

+-comm : ∀ {x y} → (x + y) ≃ (y + x)
+-comm {zero}   = ≃-sym +-runit
+-comm {succ x} = ≃-trans (succ-cong (+-comm {x})) (≃-sym +-succ)

module _ where

  open _⇒s_

  add : ⊗-setoid ℕₛ ℕₛ ⇒s ℕₛ
  add .func (x , y) = x + y
  add .func-resp-≈ (x₁≈x₂ , y₁≈y₂) = +-cong x₁≈x₂ y₁≈y₂

  zero-m : 𝟙 {0ℓ} {0ℓ} ⇒s ℕₛ
  zero-m .func x = zero
  zero-m .func-resp-≈ x = ≃-refl

------------------------------------------------------------------------------
-- Multiplication: _*_ is defined in Agda.Builtin.Nat

*-zero : ∀ {x} → (x * zero) ≃ zero
*-zero {zero}   = ≃-refl
*-zero {succ x} = *-zero {x}

*-succ : ∀ {x y} → (y * succ x) ≃ (y + (y * x))
*-succ {x} {zero} = ≃-refl
*-succ {x} {succ y} =
  begin succ (x + (y * succ x))  ≈⟨ succ-cong (+-cong ≃-refl (*-succ {x} {y})) ⟩
        succ (x + (y + (y * x))) ≈˘⟨ succ-cong (+-assoc {x} {y}) ⟩
        succ ((x + y) + (y * x)) ≈⟨ succ-cong (+-cong (+-comm {x} {y}) ≃-refl) ⟩
        succ ((y + x) + (y * x)) ≈⟨ succ-cong (+-assoc {y} {x}) ⟩
        succ (y + (x + (y * x))) ∎
  where open ≈-Reasoning ≃-isEquivalence

*-mono : ∀ {x₁ x₂ y₁ y₂} → x₁ ≤ x₂ → y₁ ≤ y₂ → (x₁ * y₁) ≤ (x₂ * y₂)
*-mono 0≤n         y₁≤y₂ = 0≤n
*-mono (s≤s x₁≤x₂) y₁≤y₂ = +-mono y₁≤y₂ (*-mono x₁≤x₂ y₁≤y₂)

*-lunit : ∀ {x} → (1 * x) ≃ x
*-lunit = +-runit

*-runit : ∀ {x} → (x * 1) ≃ x
*-runit {zero}   = ≃-zero
*-runit {succ x} = succ-cong *-runit

*-comm : ∀ {x y} → (x * y) ≃ (y * x)
*-comm {zero}   {y} = ≃-sym (*-zero {y})
*-comm {succ x} {y} = ≃-trans (+-cong ≃-refl (*-comm {x} {y})) (≃-sym (*-succ {x} {y}))

+-*-distribₗ : ∀ {x y z} → (x * (y + z)) ≃ ((x * y) + (x * z))
+-*-distribₗ {zero} = ≃-refl
+-*-distribₗ {succ x} {y} {z} =
  begin
    ((y + z) + (x * (y + z)))       ≈⟨ +-cong ≃-refl (+-*-distribₗ {x} {y} {z}) ⟩
    ((y + z) + ((x * y) + (x * z))) ≈⟨ +-interchange (λ {x} {y} → +-comm {x} {y} .proj₁) {y} {z} ⟩
    ((y + (x * y)) + (z + (x * z))) ∎
  where open ≈-Reasoning ≃-isEquivalence

+-*-distribᵣ : ∀ {x y z} → ((y + z) * x) ≃ ((y * x) + (z * x))
+-*-distribᵣ {x} {y} {z} =
  begin
    (y + z) * x       ≈⟨ *-comm {y + z} {x} ⟩
    x * (y + z)       ≈⟨ +-*-distribₗ {x} {y} {z} ⟩
    (x * y) + (x * z) ≈⟨ +-cong (*-comm {x} {y}) (*-comm {x} {z}) ⟩
    (y * x) + (z * x) ∎
  where open ≈-Reasoning ≃-isEquivalence

*-assoc : ∀ {x y z} → ((x * y) * z) ≃ (x * (y * z))
*-assoc {zero} = ≃-refl
*-assoc {succ x} {y} {z} =
  begin
    (y + (x * y)) * z       ≈⟨ +-*-distribᵣ {z} {y} {x * y} ⟩
    (y * z) + ((x * y) * z) ≈⟨ +-cong ≃-refl (*-assoc {x} {y} {z}) ⟩
    (y * z) + (x * (y * z)) ∎
  where open ≈-Reasoning ≃-isEquivalence

*-isMonoid : IsMonoid ≤-isPreorder _*_ 1
*-isMonoid .IsMonoid.mono = *-mono
*-isMonoid .IsMonoid.assoc {x} {y} {z} = *-assoc {x} {y} {z}
*-isMonoid .IsMonoid.lunit = *-lunit
*-isMonoid .IsMonoid.runit = *-runit

open IsMonoid *-isMonoid using () renaming (cong to *-cong)

module _ where

  open _⇒s_

  mult : ⊗-setoid ℕₛ ℕₛ ⇒s ℕₛ
  mult .func (x , y) = x * y
  mult .func-resp-≈ (x₁≈x₂ , y₁≈y₂) = *-cong x₁≈x₂ y₁≈y₂
