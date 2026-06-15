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

  ----------------------------------------------------------------------------
  -- 0 is a zero object (both terminal and initial); Vec 0 is a singleton.

  open import categories using (HasTerminal; IsTerminal; HasInitial; IsInitial)

  terminal : HasTerminal cat
  terminal .HasTerminal.witness = 0
  terminal .HasTerminal.is-terminal .IsTerminal.to-terminal .func _ ()
  terminal .HasTerminal.is-terminal .IsTerminal.to-terminal .func-resp-≈ _ ()
  terminal .HasTerminal.is-terminal .IsTerminal.to-terminal .+-preserving ()
  terminal .HasTerminal.is-terminal .IsTerminal.to-terminal .ε-preserving ()
  terminal .HasTerminal.is-terminal .IsTerminal.to-terminal .scale-preserving ()
  terminal .HasTerminal.is-terminal .IsTerminal.to-terminal-ext f v ()

  initial : HasInitial cat
  initial .HasInitial.witness = 0
  initial .HasInitial.is-initial .IsInitial.from-initial .func _ = εv
  initial .HasInitial.is-initial .IsInitial.from-initial .func-resp-≈ _ _ = refl
  initial .HasInitial.is-initial .IsInitial.from-initial .+-preserving _ = sym +-lunit
  initial .HasInitial.is-initial .IsInitial.from-initial .ε-preserving _ = refl
  initial .HasInitial.is-initial .IsInitial.from-initial .scale-preserving _ = sym ε-annihilᵣ
  initial .HasInitial.is-initial .IsInitial.from-initial-ext f v i =
    sym (trans (f .func-resp-≈ (λ ()) i) (f .ε-preserving i))

  ----------------------------------------------------------------------------
  -- CMon-enrichment: each hom is a commutative monoid under pointwise sum of
  -- linear maps, and composition is bilinear.

  open import cmon-enriched using (CMonEnriched)
  open import commutative-monoid using (CommutativeMonoid)

  -- The zero map.
  εₘ : ∀ {n m} → n ⇒ m
  εₘ .func _ = εv
  εₘ .func-resp-≈ _ _ = refl
  εₘ .+-preserving _ = sym +-lunit
  εₘ .ε-preserving _ = refl
  εₘ .scale-preserving _ = sym ε-annihilᵣ

  +-interchange : ∀ {a b c d} → (a + b) + (c + d) ≈ (a + c) + (b + d)
  +-interchange =
    trans +-assoc (trans (+-cong refl (trans (sym +-assoc) (trans (+-cong +-comm refl) +-assoc))) (sym +-assoc))

  -- Pointwise sum of linear maps.
  infixl 21 _+ₘ_
  _+ₘ_ : ∀ {n m} → n ⇒ m → n ⇒ m → n ⇒ m
  (f +ₘ g) .func v = f .func v +v g .func v
  (f +ₘ g) .func-resp-≈ p i = +-cong (f .func-resp-≈ p i) (g .func-resp-≈ p i)
  (f +ₘ g) .+-preserving i = trans (+-cong (f .+-preserving i) (g .+-preserving i)) +-interchange
  (f +ₘ g) .ε-preserving i = trans (+-cong (f .ε-preserving i) (g .ε-preserving i)) +-lunit
  (f +ₘ g) .scale-preserving i = trans (+-cong (f .scale-preserving i) (g .scale-preserving i)) (sym ·-+-distribₗ)

  cmon : CMonEnriched cat
  cmon .CMonEnriched.homCM n m .CommutativeMonoid.ε = εₘ
  cmon .CMonEnriched.homCM n m .CommutativeMonoid._+_ = _+ₘ_
  cmon .CMonEnriched.homCM n m .CommutativeMonoid.+-cong p q v i = +-cong (p v i) (q v i)
  cmon .CMonEnriched.homCM n m .CommutativeMonoid.+-lunit v i = +-lunit
  cmon .CMonEnriched.homCM n m .CommutativeMonoid.+-assoc v i = +-assoc
  cmon .CMonEnriched.homCM n m .CommutativeMonoid.+-comm v i = +-comm
  cmon .CMonEnriched.comp-bilinear₁ f₁ f₂ g v i = refl
  cmon .CMonEnriched.comp-bilinear₂ f g₁ g₂ v i = f .+-preserving i
  cmon .CMonEnriched.comp-bilinear-ε₁ f v i = refl
  cmon .CMonEnriched.comp-bilinear-ε₂ f v i = f .ε-preserving i
