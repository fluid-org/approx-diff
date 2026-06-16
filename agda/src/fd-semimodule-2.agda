{-# OPTIONS --postfix-projections --prop --safe #-}

module fd-semimodule-2 where

open import Level using (_⊔_)
open import prop using (⊤; tt; _∧_; _,_; proj₁; proj₂)
open import prop-setoid using (Setoid; IsEquivalence)
open import commutative-semiring using (CommutativeSemiring)
open import categories using (Category)

-- Experiment: FDSemiMod with vectors as inductive Data.Vec data (value-like)
-- rather than functions Fin n → Carrier.  Compare awkwardness + performance to
-- fd-semimodule.agda.
module FDSemiMod₂ {o ℓ} {A : Setoid o ℓ} (S : CommutativeSemiring A) where

  open CommutativeSemiring S public
  open import Data.Nat using (ℕ; zero; suc)
  import Data.Vec as V
  open V using ([]; _∷_)

  ----------------------------------------------------------------------------
  -- The carrier: vectors S^n as inductive data.

  Vec : ℕ → Set o
  Vec n = V.Vec Carrier n

  -- Pointwise equality, defined structurally (no function extensionality).
  infix 4 _≈ᵥ_
  _≈ᵥ_ : ∀ {n} → Vec n → Vec n → Prop ℓ
  []      ≈ᵥ []      = ⊤
  (x ∷ u) ≈ᵥ (y ∷ v) = (x ≈ y) ∧ (u ≈ᵥ v)

  ≈ᵥ-refl : ∀ {n} {v : Vec n} → v ≈ᵥ v
  ≈ᵥ-refl {v = []}    = tt
  ≈ᵥ-refl {v = x ∷ v} = refl , ≈ᵥ-refl

  ≈ᵥ-sym : ∀ {n} {u v : Vec n} → u ≈ᵥ v → v ≈ᵥ u
  ≈ᵥ-sym {u = []} {[]} _              = tt
  ≈ᵥ-sym {u = _ ∷ _} {_ ∷ _} (p , q)  = sym p , ≈ᵥ-sym q

  ≈ᵥ-trans : ∀ {n} {u v w : Vec n} → u ≈ᵥ v → v ≈ᵥ w → u ≈ᵥ w
  ≈ᵥ-trans {u = []} {[]} {[]} _ _                         = tt
  ≈ᵥ-trans {u = _ ∷ _} {_ ∷ _} {_ ∷ _} (p , q) (p' , q')  = trans p p' , ≈ᵥ-trans q q'

  -- Zero vector.
  εᵥ : ∀ {n} → Vec n
  εᵥ {zero}  = []
  εᵥ {suc n} = ε ∷ εᵥ

  -- Pointwise addition and scalar multiplication.
  infixl 20 _+ᵥ_
  _+ᵥ_ : ∀ {n} → Vec n → Vec n → Vec n
  _+ᵥ_ = V.zipWith _+_

  scale : ∀ {n} → Carrier → Vec n → Vec n
  scale a = V.map (a ·_)

  ----------------------------------------------------------------------------
  -- Morphisms: linear maps S^n → S^m.

  record _⇒_ (n m : ℕ) : Set (o ⊔ ℓ) where
    no-eta-equality
    field
      func             : Vec n → Vec m
      func-resp-≈      : ∀ {u v} → u ≈ᵥ v → func u ≈ᵥ func v
      +-preserving     : ∀ {u v} → func (u +ᵥ v) ≈ᵥ (func u +ᵥ func v)
      ε-preserving     : func εᵥ ≈ᵥ εᵥ
      scale-preserving : ∀ {a v} → func (scale a v) ≈ᵥ scale a (func v)
  open _⇒_ public

  infix 4 _≃_
  _≃_ : ∀ {n m} → n ⇒ m → n ⇒ m → Prop (o ⊔ ℓ)
  f ≃ g = ∀ v → f .func v ≈ᵥ g .func v

  ≃-isEquiv : ∀ {n m} → IsEquivalence (_≃_ {n} {m})
  ≃-isEquiv .IsEquivalence.refl v = ≈ᵥ-refl
  ≃-isEquiv .IsEquivalence.sym f≃g v = ≈ᵥ-sym (f≃g v)
  ≃-isEquiv .IsEquivalence.trans f≃g g≃h v = ≈ᵥ-trans (f≃g v) (g≃h v)

  ----------------------------------------------------------------------------
  -- Category of free semimodules.

  id : ∀ {n} → n ⇒ n
  id .func v = v
  id .func-resp-≈ u≈ᵥ = u≈ᵥ
  id .+-preserving = ≈ᵥ-refl
  id .ε-preserving = ≈ᵥ-refl
  id .scale-preserving = ≈ᵥ-refl

  infixl 21 _∘_
  _∘_ : ∀ {n m k} → m ⇒ k → n ⇒ m → n ⇒ k
  (g ∘ f) .func v = g .func (f .func v)
  (g ∘ f) .func-resp-≈ u≈ᵥ = g .func-resp-≈ (f .func-resp-≈ u≈ᵥ)
  (g ∘ f) .+-preserving = ≈ᵥ-trans (g .func-resp-≈ (f .+-preserving)) (g .+-preserving)
  (g ∘ f) .ε-preserving = ≈ᵥ-trans (g .func-resp-≈ (f .ε-preserving)) (g .ε-preserving)
  (g ∘ f) .scale-preserving = ≈ᵥ-trans (g .func-resp-≈ (f .scale-preserving)) (g .scale-preserving)

  cat : Category _ _ _
  cat .Category.obj = ℕ
  cat .Category._⇒_ n m = n ⇒ m
  cat .Category._≈_ = _≃_
  cat .Category.isEquiv = ≃-isEquiv
  cat .Category.id n = id
  cat .Category._∘_ = _∘_
  cat .Category.∘-cong {f₁ = F₁} {g₂ = G₂} F≃ G≃ v = ≈ᵥ-trans (F₁ .func-resp-≈ (G≃ v)) (F≃ (G₂ .func v))
  cat .Category.id-left _ = ≈ᵥ-refl
  cat .Category.id-right _ = ≈ᵥ-refl
  cat .Category.assoc _ _ _ _ = ≈ᵥ-refl
