{-# OPTIONS --postfix-projections --prop --safe #-}

module fd-semimodule where

open import Level using (_⊔_)
open import prop-setoid using (Setoid; IsEquivalence)
open import commutative-semiring using (CommutativeSemiring)
open import categories using (Category)

-- Finite-dimensional free semimodules over a commutative semiring S, with linear maps as morphisms; the
-- analogue of FDVect(R) for a general semiring.
module FDSemiMod {o ℓ} {A : Setoid o ℓ} (S : CommutativeSemiring A) where

  open CommutativeSemiring S public
  open import Data.Nat using (ℕ; zero; suc)
  open import Data.Fin using (Fin; zero; suc)

  ----------------------------------------------------------------------------
  -- The carrier: vectors S^n, and their (pointwise) semimodule structure.

  Vec : ℕ → Set o
  Vec n = Fin n → Carrier

  -- Pointwise equality of vectors.
  infix 4 _≈v_
  _≈v_ : ∀ {n} → Vec n → Vec n → Prop ℓ
  u ≈v v = ∀ i → u i ≈ v i

  -- Zero vector.
  εv : ∀ {n} → Vec n
  εv _ = ε

  -- Pointwise addition.
  infixl 20 _+v_
  _+v_ : ∀ {n} → Vec n → Vec n → Vec n
  (u +v v) i = u i + v i

  -- Pointwise scalar multiplication.
  scale : ∀ {n} → Carrier → Vec n → Vec n
  scale a v i = a · v i

  ----------------------------------------------------------------------------
  -- Morphisms: linear maps S^n → S^m.

  record _⇒_ (n m : ℕ) : Set (o ⊔ ℓ) where
    no-eta-equality
    field
      func             : Vec n → Vec m
      func-resp-≈      : ∀ {u v} → u ≈v v → func u ≈v func v
      +-preserving     : ∀ {u v} → func (u +v v) ≈v (func u +v func v)
      ε-preserving     : func εv ≈v εv
      scale-preserving : ∀ {a v} → func (scale a v) ≈v scale a (func v)
  open _⇒_ public

  -- Extensional (pointwise) equality of morphisms.
  infix 4 _≃_
  _≃_ : ∀ {n m} → n ⇒ m → n ⇒ m → Prop (o ⊔ ℓ)
  f ≃ g = ∀ v → f .func v ≈v g .func v

  ≃-isEquiv : ∀ {n m} → IsEquivalence (_≃_ {n} {m})
  ≃-isEquiv .IsEquivalence.refl v i = refl
  ≃-isEquiv .IsEquivalence.sym f≃g v i = sym (f≃g v i)
  ≃-isEquiv .IsEquivalence.trans f≃g g≃h v i = trans (f≃g v i) (g≃h v i)

  ----------------------------------------------------------------------------
  -- Identity and composition.

  id : ∀ {n} → n ⇒ n
  id .func v = v
  id .func-resp-≈ u≈v = u≈v
  id .+-preserving _ = refl
  id .ε-preserving _ = refl
  id .scale-preserving _ = refl

  infixl 21 _∘_
  _∘_ : ∀ {n m k} → m ⇒ k → n ⇒ m → n ⇒ k
  (g ∘ f) .func v = g .func (f .func v)
  (g ∘ f) .func-resp-≈ u≈v = g .func-resp-≈ (f .func-resp-≈ u≈v)
  (g ∘ f) .+-preserving i = trans (g .func-resp-≈ (f .+-preserving) i) (g .+-preserving i)
  (g ∘ f) .ε-preserving i = trans (g .func-resp-≈ (f .ε-preserving) i) (g .ε-preserving i)
  (g ∘ f) .scale-preserving i = trans (g .func-resp-≈ (f .scale-preserving) i) (g .scale-preserving i)

  ----------------------------------------------------------------------------
  -- The category of free semimodules.  Laws are given inline by copattern, so
  -- the implicit morphisms stay rigid (the record has no eta).

  cat : Category _ _ _
  cat .Category.obj = ℕ
  cat .Category._⇒_ n m = n ⇒ m
  cat .Category._≈_ = _≃_
  cat .Category.isEquiv = ≃-isEquiv
  cat .Category.id n = id
  cat .Category._∘_ = _∘_
  cat .Category.∘-cong {f₁ = F₁} {g₂ = G₂} F≃ G≃ v i =
    trans (F₁ .func-resp-≈ (G≃ v) i) (F≃ (G₂ .func v) i)
  cat .Category.id-left _ _ = refl
  cat .Category.id-right _ _ = refl
  cat .Category.assoc _ _ _ _ _ = refl
