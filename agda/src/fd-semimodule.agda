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
  infix 4 _≈ᵥ_
  _≈ᵥ_ : ∀ {n} → Vec n → Vec n → Prop ℓ
  u ≈ᵥ v = ∀ i → u i ≈ v i

  -- Zero vector.
  εᵥ : ∀ {n} → Vec n
  εᵥ _ = ε

  -- Pointwise addition.
  infixl 20 _+ᵥ_
  _+ᵥ_ : ∀ {n} → Vec n → Vec n → Vec n
  (u +ᵥ v) i = u i + v i

  -- Pointwise scalar multiplication.
  scale : ∀ {n} → Carrier → Vec n → Vec n
  scale a v i = a · v i

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

  -- Extensional (pointwise) equality of morphisms.
  infix 4 _≃_
  _≃_ : ∀ {n m} → n ⇒ m → n ⇒ m → Prop (o ⊔ ℓ)
  f ≃ g = ∀ v → f .func v ≈ᵥ g .func v

  ≃-isEquiv : ∀ {n m} → IsEquivalence (_≃_ {n} {m})
  ≃-isEquiv .IsEquivalence.refl v i = refl
  ≃-isEquiv .IsEquivalence.sym f≃g v i = sym (f≃g v i)
  ≃-isEquiv .IsEquivalence.trans f≃g g≃h v i = trans (f≃g v i) (g≃h v i)

  ----------------------------------------------------------------------------
  -- Identity and composition.

  id : ∀ {n} → n ⇒ n
  id .func v = v
  id .func-resp-≈ u≈ᵥ = u≈ᵥ
  id .+-preserving _ = refl
  id .ε-preserving _ = refl
  id .scale-preserving _ = refl

  infixl 21 _∘_
  _∘_ : ∀ {n m k} → m ⇒ k → n ⇒ m → n ⇒ k
  (g ∘ f) .func v = g .func (f .func v)
  (g ∘ f) .func-resp-≈ u≈ᵥ = g .func-resp-≈ (f .func-resp-≈ u≈ᵥ)
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
  initial .HasInitial.is-initial .IsInitial.from-initial .func _ = εᵥ
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
  εₘ .func _ = εᵥ
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
  (f +ₘ g) .func v = f .func v +ᵥ g .func v
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

  ----------------------------------------------------------------------------
  -- Biproducts: the direct sum m + n, splitting/joining vectors via Data.Fin.

  open import Data.Nat using () renaming (_+_ to _+ℕ_)
  open import Data.Fin using (_↑ˡ_; _↑ʳ_; splitAt; join)
  open import Data.Sum using (inj₁; inj₂; [_,_])
  open import Data.Fin.Properties using (splitAt-↑ˡ; splitAt-↑ʳ; join-splitAt)
  open import Relation.Binary.PropositionalEquality using (cong) renaming (sym to ≡-sym; trans to ≡-trans)
  open import cmon-enriched using (Biproduct; biproducts→products)
  open import categories using (HasProducts)

  -- Projections: take the first m / last n components.  Reindexing, so linear definitionally.
  p₁ : ∀ {m n} → (m +ℕ n) ⇒ m
  p₁ {m} {n} .func v i = v (i ↑ˡ n)
  p₁ {m} {n} .func-resp-≈ p i = p (i ↑ˡ n)
  p₁ .+-preserving _ = refl
  p₁ .ε-preserving _ = refl
  p₁ .scale-preserving _ = refl

  p₂ : ∀ {m n} → (m +ℕ n) ⇒ n
  p₂ {m} {n} .func v j = v (m ↑ʳ j)
  p₂ {m} {n} .func-resp-≈ p j = p (m ↑ʳ j)
  p₂ .+-preserving _ = refl
  p₂ .ε-preserving _ = refl
  p₂ .scale-preserving _ = refl

  -- Injections: pad with zeros in the other block.
  in₁ : ∀ {m n} → m ⇒ (m +ℕ n)
  in₁ {m} {n} .func v k = [ v , εᵥ ] (splitAt m k)
  in₁ {m} {n} .func-resp-≈ p k with splitAt m k
  ... | inj₁ i = p i
  ... | inj₂ j = refl
  in₁ {m} {n} .+-preserving k with splitAt m k
  ... | inj₁ i = refl
  ... | inj₂ j = sym +-lunit
  in₁ {m} {n} .ε-preserving k with splitAt m k
  ... | inj₁ i = refl
  ... | inj₂ j = refl
  in₁ {m} {n} .scale-preserving k with splitAt m k
  ... | inj₁ i = refl
  ... | inj₂ j = sym ε-annihilᵣ

  in₂ : ∀ {m n} → n ⇒ (m +ℕ n)
  in₂ {m} {n} .func v k = [ εᵥ , v ] (splitAt m k)
  in₂ {m} {n} .func-resp-≈ p k with splitAt m k
  ... | inj₁ i = refl
  ... | inj₂ j = p j
  in₂ {m} {n} .+-preserving k with splitAt m k
  ... | inj₁ i = sym +-lunit
  ... | inj₂ j = refl
  in₂ {m} {n} .ε-preserving k with splitAt m k
  ... | inj₁ i = refl
  ... | inj₂ j = refl
  in₂ {m} {n} .scale-preserving k with splitAt m k
  ... | inj₁ i = sym ε-annihilᵣ
  ... | inj₂ j = refl

  id-1 : ∀ m n → (p₁ {m} {n} ∘ in₁ {m} {n}) ≃ id
  id-1 m n v i rewrite splitAt-↑ˡ m i n = refl

  id-2 : ∀ m n → (p₂ {m} {n} ∘ in₂ {m} {n}) ≃ id
  id-2 m n v j rewrite splitAt-↑ʳ m n j = refl

  zero-1 : ∀ m n → (p₁ {m} {n} ∘ in₂ {m} {n}) ≃ εₘ
  zero-1 m n v i rewrite splitAt-↑ˡ m i n = refl

  zero-2 : ∀ m n → (p₂ {m} {n} ∘ in₁ {m} {n}) ≃ εₘ
  zero-2 m n v j rewrite splitAt-↑ʳ m n j = refl

  id-+ : ∀ m n → ((in₁ {m} {n} ∘ p₁ {m} {n}) +ₘ (in₂ {m} {n} ∘ p₂ {m} {n})) ≃ id
  id-+ m n v k with splitAt m k in eq
  ... | inj₁ i rewrite ≡-trans (≡-sym (join-splitAt m n k)) (cong (join m n) eq) = trans +-comm +-lunit
  ... | inj₂ j rewrite ≡-trans (≡-sym (join-splitAt m n k)) (cong (join m n) eq) = +-lunit

  biproduct : ∀ m n → Biproduct cmon m n
  biproduct m n .Biproduct.prod = m +ℕ n
  biproduct m n .Biproduct.p₁ = p₁
  biproduct m n .Biproduct.p₂ = p₂
  biproduct m n .Biproduct.in₁ = in₁
  biproduct m n .Biproduct.in₂ = in₂
  biproduct m n .Biproduct.id-1 = id-1 m n
  biproduct m n .Biproduct.id-2 = id-2 m n
  biproduct m n .Biproduct.zero-1 = zero-1 m n
  biproduct m n .Biproduct.zero-2 = zero-2 m n
  biproduct m n .Biproduct.id-+ = id-+ m n

  -- Finite products, from the biproducts.
  products : HasProducts cat
  products = biproducts→products cmon biproduct
