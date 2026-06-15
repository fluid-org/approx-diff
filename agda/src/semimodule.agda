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
      scale-+ᵣ   : ∀ {a x y} → scale a (x + y) ≈ (scale a x + scale a y)
      scale-+ₗ   : ∀ {a b x} → scale (a +ₛ b) x ≈ (scale a x + scale b x)
      scale-·    : ∀ {a b x} → scale (a ·ₛ b) x ≈ scale a (scale b x)
      scale-ι    : ∀ {x} → scale ιₛ x ≈ x
      scale-0ₗ   : ∀ {x} → scale εₛ x ≈ ε
      scale-0ᵣ   : ∀ {a} → scale a ε ≈ ε
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
  -- The category of S-semimodules.

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

  ----------------------------------------------------------------------------
  -- The one-point semimodule is a zero object.

  open import categories using (HasTerminal; IsTerminal; HasInitial; IsInitial)
  open import prop-setoid using (𝟙)
  open import commutative-monoid using (𝟙cm)

  𝟘 : SemiModule
  𝟘 .carrier = 𝟙
  𝟘 .+-monoid = 𝟙cm
  𝟘 .scale _ c = c
  𝟘 .scale-cong _ _ = _
  𝟘 .scale-+ᵣ = _
  𝟘 .scale-+ₗ = _
  𝟘 .scale-· = _
  𝟘 .scale-ι = _
  𝟘 .scale-0ₗ = _
  𝟘 .scale-0ᵣ = _

  terminal : HasTerminal cat
  terminal .HasTerminal.witness = 𝟘
  terminal .HasTerminal.is-terminal .IsTerminal.to-terminal .func _ = 𝟘 .ε
  terminal .HasTerminal.is-terminal .IsTerminal.to-terminal .func-resp-≈ _ = _
  terminal .HasTerminal.is-terminal .IsTerminal.to-terminal .+-preserving = _
  terminal .HasTerminal.is-terminal .IsTerminal.to-terminal .ε-preserving = _
  terminal .HasTerminal.is-terminal .IsTerminal.to-terminal .scale-preserving = _
  terminal .HasTerminal.is-terminal .IsTerminal.to-terminal-ext f x = _

  initial : HasInitial cat
  initial .HasInitial.witness = 𝟘
  initial .HasInitial.is-initial .IsInitial.from-initial {x = M} .func _ = M .ε
  initial .HasInitial.is-initial .IsInitial.from-initial {x = M} .func-resp-≈ _ = M .refl
  initial .HasInitial.is-initial .IsInitial.from-initial {x = M} .+-preserving = M .sym (M .+-lunit)
  initial .HasInitial.is-initial .IsInitial.from-initial {x = M} .ε-preserving = M .refl
  initial .HasInitial.is-initial .IsInitial.from-initial {x = M} .scale-preserving = M .sym (M .scale-0ᵣ)
  initial .HasInitial.is-initial .IsInitial.from-initial-ext {x = M} f x = M .sym (f .ε-preserving)

  ----------------------------------------------------------------------------
  -- CMon-enrichment: pointwise sum of linear maps, composition bilinear.

  open import cmon-enriched using (CMonEnriched)

  -- The zero map.
  εₘ : ∀ {M N} → M ⇒ N
  εₘ {N = N} .func _ = N .ε
  εₘ {N = N} .func-resp-≈ _ = N .refl
  εₘ {N = N} .+-preserving = N .sym (N .+-lunit)
  εₘ {N = N} .ε-preserving = N .refl
  εₘ {N = N} .scale-preserving = N .sym (N .scale-0ᵣ)

  -- Pointwise sum of linear maps.
  infixl 21 _+ₘ_
  _+ₘ_ : ∀ {M N} → M ⇒ N → M ⇒ N → M ⇒ N
  _+ₘ_ {N = N} f g .func x = N ._+_ (f .func x) (g .func x)
  _+ₘ_ {N = N} f g .func-resp-≈ p = N .+-cong (f .func-resp-≈ p) (g .func-resp-≈ p)
  _+ₘ_ {N = N} f g .+-preserving = N .trans (N .+-cong (f .+-preserving) (g .+-preserving)) (CommutativeMonoid.+-interchange (N .+-monoid))
  _+ₘ_ {N = N} f g .ε-preserving = N .trans (N .+-cong (f .ε-preserving) (g .ε-preserving)) (N .+-lunit)
  _+ₘ_ {N = N} f g .scale-preserving = N .trans (N .+-cong (f .scale-preserving) (g .scale-preserving)) (N .sym (N .scale-+ᵣ))

  cmon : CMonEnriched cat
  cmon .CMonEnriched.homCM M N .CommutativeMonoid.ε = εₘ
  cmon .CMonEnriched.homCM M N .CommutativeMonoid._+_ = _+ₘ_
  cmon .CMonEnriched.homCM M N .CommutativeMonoid.+-cong p q x = N .+-cong (p x) (q x)
  cmon .CMonEnriched.homCM M N .CommutativeMonoid.+-lunit x = N .+-lunit
  cmon .CMonEnriched.homCM M N .CommutativeMonoid.+-assoc x = N .+-assoc
  cmon .CMonEnriched.homCM M N .CommutativeMonoid.+-comm x = N .+-comm
  cmon .CMonEnriched.comp-bilinear₁ {Z = P} f₁ f₂ g x = P .refl
  cmon .CMonEnriched.comp-bilinear₂ f g₁ g₂ x = f .+-preserving
  cmon .CMonEnriched.comp-bilinear-ε₁ {Z = P} f x = P .refl
  cmon .CMonEnriched.comp-bilinear-ε₂ f x = f .ε-preserving

  ----------------------------------------------------------------------------
  -- Biproducts: the direct sum M ⊕ N, with componentwise structure.

  open import prop using (_,_)
  open import Data.Product using (_,_)
  open import prop-setoid using (⊗-setoid)
  open import commutative-monoid using (_⊗_)
  open import cmon-enriched using (Biproduct)

  infixr 20 _⊕_
  _⊕_ : SemiModule → SemiModule → SemiModule
  (M ⊕ N) .carrier = ⊗-setoid (M .carrier) (N .carrier)
  (M ⊕ N) .+-monoid = M .+-monoid ⊗ N .+-monoid
  (M ⊕ N) .scale a (x , y) = M .scale a x , N .scale a y
  (M ⊕ N) .scale-cong a≈ (x≈ , y≈) = M .scale-cong a≈ x≈ , N .scale-cong a≈ y≈
  (M ⊕ N) .scale-+ᵣ = M .scale-+ᵣ , N .scale-+ᵣ
  (M ⊕ N) .scale-+ₗ = M .scale-+ₗ , N .scale-+ₗ
  (M ⊕ N) .scale-· = M .scale-· , N .scale-·
  (M ⊕ N) .scale-ι = M .scale-ι , N .scale-ι
  (M ⊕ N) .scale-0ₗ = M .scale-0ₗ , N .scale-0ₗ
  (M ⊕ N) .scale-0ᵣ = M .scale-0ᵣ , N .scale-0ᵣ

  -- Projections.
  p₁ : ∀ {M N} → (M ⊕ N) ⇒ M
  p₁ {M} .func (x , y) = x
  p₁ {M} .func-resp-≈ (x≈ , y≈) = x≈
  p₁ {M} .+-preserving = M .refl
  p₁ {M} .ε-preserving = M .refl
  p₁ {M} .scale-preserving = M .refl

  p₂ : ∀ {M N} → (M ⊕ N) ⇒ N
  p₂ {N = N} .func (x , y) = y
  p₂ {N = N} .func-resp-≈ (x≈ , y≈) = y≈
  p₂ {N = N} .+-preserving = N .refl
  p₂ {N = N} .ε-preserving = N .refl
  p₂ {N = N} .scale-preserving = N .refl

  -- Injections: pad with zero in the other component.
  in₁ : ∀ {M N} → M ⇒ (M ⊕ N)
  in₁ {M} {N} .func x = x , N .ε
  in₁ {M} {N} .func-resp-≈ x≈ = x≈ , N .refl
  in₁ {M} {N} .+-preserving = M .refl , N .sym (N .+-lunit)
  in₁ {M} {N} .ε-preserving = M .refl , N .refl
  in₁ {M} {N} .scale-preserving = M .refl , N .sym (N .scale-0ᵣ)

  in₂ : ∀ {M N} → N ⇒ (M ⊕ N)
  in₂ {M} {N} .func y = M .ε , y
  in₂ {M} {N} .func-resp-≈ y≈ = M .refl , y≈
  in₂ {M} {N} .+-preserving = M .sym (M .+-lunit) , N .refl
  in₂ {M} {N} .ε-preserving = M .refl , N .refl
  in₂ {M} {N} .scale-preserving = M .sym (M .scale-0ᵣ) , N .refl

  biproduct : ∀ M N → Biproduct cmon M N
  biproduct M N .Biproduct.prod = M ⊕ N
  biproduct M N .Biproduct.p₁ = p₁ {M} {N}
  biproduct M N .Biproduct.p₂ = p₂ {M} {N}
  biproduct M N .Biproduct.in₁ = in₁ {M} {N}
  biproduct M N .Biproduct.in₂ = in₂ {M} {N}
  biproduct M N .Biproduct.id-1 x = M .refl
  biproduct M N .Biproduct.id-2 x = N .refl
  biproduct M N .Biproduct.zero-1 x = M .refl
  biproduct M N .Biproduct.zero-2 x = N .refl
  biproduct M N .Biproduct.id-+ (x , y) = M .trans (M .+-comm) (M .+-lunit) , N .+-lunit

  -- Finite products, from the biproducts.
  open import categories using (HasProducts)
  open import cmon-enriched using (biproducts→products)

  products : HasProducts cat
  products = biproducts→products cmon biproduct
