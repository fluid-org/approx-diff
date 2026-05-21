{-# OPTIONS --prop --postfix-projections --safe #-}

module categories where

open import Level using (Level; suc; _⊔_; 0ℓ; Lift; lift)
open import Data.Nat using (ℕ) renaming (zero to nzero; suc to nsuc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import prop using (LiftP; Prf; ⊤; ⟪_⟫; tt; lift)
open import prop-setoid
  using (IsEquivalence; Setoid; module ≈-Reasoning; ⊗-setoid)
  renaming (_⇒_ to _⇒s_)

open IsEquivalence

-- Definition of category, and some basic structure one might want to
-- have.

record Category o m e : Set (suc (o ⊔ m ⊔ e)) where
  no-eta-equality
  field
    obj  : Set o
    _⇒_ : obj → obj → Set m
    _≈_  : ∀ {x y} → x ⇒ y → x ⇒ y → Prop e

    isEquiv : ∀ {x y} → IsEquivalence (_≈_ {x} {y})

    id  : ∀ x → x ⇒ x
    _∘_ : ∀ {x y z} → y ⇒ z → x ⇒ y → x ⇒ z

  infixl 21 _∘_

  field
    ∘-cong : ∀ {x y z} {f₁ f₂ : y ⇒ z} {g₁ g₂ : x ⇒ y} →
      f₁ ≈ f₂ → g₁ ≈ g₂ → (f₁ ∘ g₁) ≈ (f₂ ∘ g₂)

    id-left  : ∀ {x y} {f : x ⇒ y} → (id y ∘ f) ≈ f
    id-right : ∀ {x y} {f : x ⇒ y} → (f ∘ id x) ≈ f
    assoc    : ∀ {w x y z} (f : y ⇒ z) (g : x ⇒ y) (h : w ⇒ x) →
      ((f ∘ g) ∘ h) ≈ (f ∘ (g ∘ h))

  ≈-refl : ∀ {x y} {f : x ⇒ y} → f ≈ f
  ≈-refl = isEquiv .refl

  ≈-sym : ∀ {x y} {f g : x ⇒ y} → f ≈ g → g ≈ f
  ≈-sym = isEquiv .sym

  ≈-trans : ∀ {x y} {f g h : x ⇒ y} → f ≈ g → g ≈ h → f ≈ h
  ≈-trans = isEquiv .trans

  ≡-to-≈ : ∀ {x y} {f g : x ⇒ y} → f ≡ g → f ≈ g
  ≡-to-≈ ≡.refl = ≈-refl

  id-swap : ∀ {x y}{f : x ⇒ y} → (id y ∘ f) ≈ (f ∘ id x)
  id-swap = isEquiv .trans id-left (≈-sym id-right)

  id-swap' : ∀ {x y}{f : x ⇒ y} → (f ∘ id x) ≈ (id y ∘ f)
  id-swap' = isEquiv .trans id-right (≈-sym id-left)

  open Setoid renaming (_≈_ to _≃_)

  hom-setoid : obj → obj → Setoid m e
  hom-setoid x y .Carrier = x ⇒ y
  hom-setoid x y ._≃_ = _≈_
  hom-setoid x y .isEquivalence = isEquiv

  hom-setoid-l : ∀ ℓ₁ ℓ₂ → obj → obj → Setoid (ℓ₁ ⊔ m) (ℓ₂ ⊔ e)
  hom-setoid-l ℓ₁ _ x y .Carrier = Lift ℓ₁ (x ⇒ y)
  hom-setoid-l _ ℓ₂ x y ._≃_ (lift f) (lift g) = LiftP ℓ₂ (f ≈ g)
  hom-setoid-l _ _ x y .isEquivalence .refl = lift (isEquiv .refl)
  hom-setoid-l _ _ x y .isEquivalence .sym (lift e) = lift (isEquiv .sym e)
  hom-setoid-l _ _ x y .isEquivalence .trans (lift p) (lift q) = lift (isEquiv .trans p q)

  record IsIso {x y} (f : x ⇒ y) : Set (m ⊔ e) where
    field
      inverse     : y ⇒ x
      f∘inverse≈id : (f ∘ inverse) ≈ id y
      inverse∘f≈id : (inverse ∘ f) ≈ id x

  record Iso (x y : obj) : Set (m ⊔ e) where
    field
      fwd : x ⇒ y
      bwd : y ⇒ x
      fwd∘bwd≈id : (fwd ∘ bwd) ≈ id y
      bwd∘fwd≈id : (bwd ∘ fwd) ≈ id x

  open IsIso
  open Iso

  IsIso→Iso : ∀ {x y} {f : x ⇒ y} → IsIso f → Iso x y
  IsIso→Iso {x} {y} {f} isIso = record
                                 { fwd = f
                                 ; bwd = inverse isIso
                                 ; fwd∘bwd≈id = f∘inverse≈id isIso
                                 ; bwd∘fwd≈id = inverse∘f≈id isIso
                                 }

  Iso-refl : ∀ {x} → Iso x x
  Iso-refl .Iso.fwd = id _
  Iso-refl .Iso.bwd = id _
  Iso-refl .Iso.fwd∘bwd≈id = id-left
  Iso-refl .Iso.bwd∘fwd≈id = id-left

  Iso-sym : ∀ {x y} → Iso x y → Iso y x
  Iso-sym iso .fwd = iso .bwd
  Iso-sym iso .bwd = iso .fwd
  Iso-sym iso .fwd∘bwd≈id = bwd∘fwd≈id iso
  Iso-sym iso .bwd∘fwd≈id = fwd∘bwd≈id iso

  Iso-trans : ∀ {x y z} → Iso x y → Iso y z → Iso x z
  Iso-trans iso₁ iso₂ .fwd = (iso₂ .fwd) ∘ (iso₁ .fwd)
  Iso-trans iso₁ iso₂ .bwd = (iso₁ .bwd) ∘ (iso₂ .bwd)
  Iso-trans iso₁ iso₂ .fwd∘bwd≈id = begin
      (iso₂ .fwd ∘ iso₁ .fwd) ∘ (iso₁ .bwd ∘ iso₂ .bwd)
    ≈⟨ assoc _ _ _ ⟩
      iso₂ .fwd ∘ (iso₁ .fwd ∘ (iso₁ .bwd ∘ iso₂ .bwd))
    ≈˘⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
      iso₂ .fwd ∘ ((iso₁ .fwd ∘ iso₁ .bwd) ∘ iso₂ .bwd)
    ≈⟨ ∘-cong ≈-refl (∘-cong (fwd∘bwd≈id iso₁) ≈-refl) ⟩
      iso₂ .fwd ∘ (id _ ∘ iso₂ .bwd)
    ≈⟨ ∘-cong ≈-refl id-left ⟩
      iso₂ .fwd ∘ iso₂ .bwd
    ≈⟨ fwd∘bwd≈id iso₂ ⟩
      id _
    ∎
    where open ≈-Reasoning isEquiv
  Iso-trans iso₁ iso₂ .bwd∘fwd≈id = begin
      (iso₁ .bwd ∘ iso₂ .bwd) ∘ (iso₂ .fwd ∘ iso₁ .fwd)
    ≈⟨ assoc _ _ _ ⟩
      iso₁ .bwd ∘ (iso₂ .bwd ∘ (iso₂ .fwd ∘ iso₁ .fwd))
    ≈˘⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
      iso₁ .bwd ∘ ((iso₂ .bwd ∘ iso₂ .fwd) ∘ iso₁ .fwd)
    ≈⟨ ∘-cong ≈-refl (∘-cong (bwd∘fwd≈id iso₂) ≈-refl) ⟩
      iso₁ .bwd ∘ (id _ ∘ iso₁ .fwd)
    ≈⟨ ∘-cong ≈-refl id-left ⟩
      iso₁ .bwd ∘ iso₁ .fwd
    ≈⟨ bwd∘fwd≈id iso₁ ⟩
      id _
    ∎
    where open ≈-Reasoning isEquiv

  opposite : Category o m e
  opposite .obj = obj
  opposite ._⇒_ x y = y ⇒ x
  opposite ._≈_ = _≈_
  opposite .isEquiv = isEquiv
  opposite .id = id
  opposite ._∘_ f g = g ∘ f
  opposite .∘-cong e₁ e₂ = ∘-cong e₂ e₁
  opposite .id-left = id-right
  opposite .id-right = id-left
  opposite .assoc f g h = ≈-sym (assoc h g f)

------------------------------------------------------------------------------
setoid→category : ∀ {o e} → Setoid o e → Category o e e
setoid→category A .Category.obj = A .Setoid.Carrier
setoid→category A .Category._⇒_ x y = Prf (A .Setoid._≈_ x y)
setoid→category A .Category._≈_ _ _ = ⊤
setoid→category A .Category.isEquiv = prop-setoid.⊤-isEquivalence
setoid→category A .Category.id x = ⟪ A .Setoid.refl ⟫
setoid→category A .Category._∘_ ⟪ f ⟫ ⟪ g ⟫ = ⟪ A .Setoid.trans g f ⟫
setoid→category A .Category.∘-cong _ _ = tt
setoid→category A .Category.id-left = tt
setoid→category A .Category.id-right = tt
setoid→category A .Category.assoc _ _ _ = tt


------------------------------------------------------------------------------
-- Terminal objects
record IsTerminal {o m e} (𝒞 : Category o m e) (t : Category.obj 𝒞) : Set (o ⊔ m ⊔ e) where
  open Category 𝒞
  field
    to-terminal     : ∀ {x} → x ⇒ t
    to-terminal-ext : ∀ {x} (f : x ⇒ t) → to-terminal ≈ f

  to-terminal-unique : ∀ {x} (f g : x ⇒ t) → f ≈ g
  to-terminal-unique f g = ≈-trans (≈-sym (to-terminal-ext f)) (to-terminal-ext g)

record HasTerminal {o m e} (𝒞 : Category o m e) : Set (o ⊔ m ⊔ e) where
  open Category 𝒞
  field
    witness         : obj
    is-terminal     : IsTerminal 𝒞 witness
  open IsTerminal is-terminal public

------------------------------------------------------------------------------
-- Initial objects
record IsInitial {o m e} (𝒞 : Category o m e) (t : Category.obj 𝒞) : Set (o ⊔ m ⊔ e) where
  open Category 𝒞
  field
    from-initial     : ∀ {x} → t ⇒ x
    from-initial-ext : ∀ {x} (f : t ⇒ x) → from-initial ≈ f

  from-initial-unique : ∀ {x} (f g : t ⇒ x) → f ≈ g
  from-initial-unique f g = ≈-trans (≈-sym (from-initial-ext f)) (from-initial-ext g)

record HasInitial {o m e} (𝒞 : Category o m e) : Set (o ⊔ m ⊔ e) where
  open Category 𝒞
  field
    witness         : obj
    is-initial      : IsInitial 𝒞 witness
  open IsInitial is-initial public

op-initial→terminal : ∀ {o m e} {𝒞 : Category o m e} → HasInitial 𝒞 → HasTerminal (Category.opposite 𝒞)
op-initial→terminal i .HasTerminal.witness = i .HasInitial.witness
op-initial→terminal i .HasTerminal.is-terminal .IsTerminal.to-terminal = i .HasInitial.from-initial
op-initial→terminal i .HasTerminal.is-terminal .IsTerminal.to-terminal-ext = i .HasInitial.from-initial-ext

------------------------------------------------------------------------------
-- Coproducts
record HasCoproducts {o m e} (𝒞 : Category o m e) : Set (o ⊔ m ⊔ e) where
  open Category 𝒞
  field
    coprod : obj → obj → obj
    in₁    : ∀ {x y} → x ⇒ coprod x y
    in₂    : ∀ {x y} → y ⇒ coprod x y
    copair : ∀ {x y z} → x ⇒ z → y ⇒ z → coprod x y ⇒ z

    copair-cong : ∀ {x y z} {f₁ f₂ : x ⇒ z} {g₁ g₂ : y ⇒ z} → f₁ ≈ f₂ → g₁ ≈ g₂ → copair f₁ g₁ ≈ copair f₂ g₂
    copair-in₁ : ∀ {x y z} (f : x ⇒ z) (g : y ⇒ z) → (copair f g ∘ in₁) ≈ f
    copair-in₂ : ∀ {x y z} (f : x ⇒ z) (g : y ⇒ z) → (copair f g ∘ in₂) ≈ g
    copair-ext : ∀ {x y z} (f : coprod x y ⇒ z) → copair (f ∘ in₁) (f ∘ in₂) ≈ f

  copair-natural : ∀ {w x y z} (h : z ⇒ w) (f : x ⇒ z) (g : y ⇒ z) → (h ∘ copair f g) ≈ copair (h ∘ f) (h ∘ g)
  copair-natural h f g =
    begin
      h ∘ copair f g
    ≈˘⟨ copair-ext _ ⟩
      copair ((h ∘ copair f g) ∘ in₁) ((h ∘ copair f g) ∘ in₂)
    ≈⟨ copair-cong (assoc _ _ _) (assoc _ _ _) ⟩
      copair (h ∘ (copair f g ∘ in₁)) (h ∘ (copair f g ∘ in₂))
    ≈⟨ copair-cong (∘-cong ≈-refl (copair-in₁ f g)) (∘-cong ≈-refl (copair-in₂ f g)) ⟩
      copair (h ∘ f) (h ∘ g)
    ∎
    where open ≈-Reasoning isEquiv

  coprod-m : ∀ {x₁ y₁ x₂ y₂} → x₁ ⇒ x₂ → y₁ ⇒ y₂ → coprod x₁ y₁ ⇒ coprod x₂ y₂
  coprod-m f g = copair (in₁ ∘ f) (in₂ ∘ g)

  coprod-m-cong : ∀ {x₁ y₁ x₂ y₂} {f₁ f₂ : x₁ ⇒ x₂} {g₁ g₂ : y₁ ⇒ y₂} →
                  f₁ ≈ f₂ → g₁ ≈ g₂ → coprod-m f₁ g₁ ≈ coprod-m f₂ g₂
  coprod-m-cong f₁≈f₂ g₁≈g₂ =
    copair-cong (∘-cong ≈-refl f₁≈f₂) (∘-cong ≈-refl g₁≈g₂)

  coprod-m-comp : ∀ {x₁ x₂ y₁ y₂ z₁ z₂} (f₁ : y₁ ⇒ z₁) (f₂ : y₂ ⇒ z₂) (g₁ : x₁ ⇒ y₁) (g₂ : x₂ ⇒ y₂) →
    coprod-m (f₁ ∘ g₁) (f₂ ∘ g₂) ≈ (coprod-m f₁ f₂ ∘ coprod-m g₁ g₂)
  coprod-m-comp f₁ f₂ g₁ g₂ = begin
      copair (in₁ ∘ (f₁ ∘ g₁)) (in₂ ∘ (f₂ ∘ g₂))
    ≈˘⟨ copair-cong (assoc _ _ _) (assoc _ _ _) ⟩
      copair ((in₁ ∘ f₁) ∘ g₁) ((in₂ ∘ f₂) ∘ g₂)
    ≈˘⟨ copair-cong (∘-cong (copair-in₁ _ _) ≈-refl) (∘-cong (copair-in₂ _ _) ≈-refl) ⟩
      copair ((copair (in₁ ∘ f₁) (in₂ ∘ f₂) ∘ in₁) ∘ g₁) ((copair (in₁ ∘ f₁) (in₂ ∘ f₂) ∘ in₂) ∘ g₂)
    ≈⟨ copair-cong (assoc _ _ _) (assoc _ _ _) ⟩
      copair (copair (in₁ ∘ f₁) (in₂ ∘ f₂) ∘ (in₁ ∘ g₁)) (copair (in₁ ∘ f₁) (in₂ ∘ f₂) ∘ (in₂ ∘ g₂))
    ≈˘⟨ copair-natural _ _ _ ⟩
      copair (in₁ ∘ f₁) (in₂ ∘ f₂) ∘ copair (in₁ ∘ g₁) (in₂ ∘ g₂)
    ∎
    where open ≈-Reasoning isEquiv

  coprod-m-id : ∀ {x y} → coprod-m (id x) (id y) ≈ id (coprod x y)
  coprod-m-id {x} {y} = begin
      coprod-m (id x) (id y)
    ≈⟨ copair-cong id-swap' id-swap' ⟩
      copair (id _ ∘ in₁) (id _ ∘ in₂)
    ≈⟨ copair-ext (id _) ⟩
      id (coprod x y)
    ∎
    where open ≈-Reasoning isEquiv

  copair-coprod : ∀ {x₁ x₂ y₁ y₂ z} (f₁ : y₁ ⇒ z) (f₂ : y₂ ⇒ z) (g₁ : x₁ ⇒ y₁) (g₂ : x₂ ⇒ y₂) →
    copair (f₁ ∘ g₁) (f₂ ∘ g₂) ≈ (copair f₁ f₂ ∘ coprod-m g₁ g₂)
  copair-coprod f₁ f₂ g₁ g₂ = begin
      copair (f₁ ∘ g₁) (f₂ ∘ g₂)
    ≈˘⟨ copair-cong (∘-cong (copair-in₁ _ _) ≈-refl) (∘-cong (copair-in₂ _ _) ≈-refl) ⟩
      copair ((copair f₁ f₂ ∘ in₁) ∘ g₁) ((copair f₁ f₂ ∘ in₂) ∘ g₂)
    ≈⟨ copair-cong (assoc _ _ _) (assoc _ _ _) ⟩
      copair (copair f₁ f₂ ∘ (in₁ ∘ g₁)) (copair f₁ f₂ ∘ (in₂ ∘ g₂))
    ≈˘⟨ copair-natural _ _ _ ⟩
      copair f₁ f₂ ∘ copair (in₁ ∘ g₁) (in₂ ∘ g₂)
    ∎
    where open ≈-Reasoning isEquiv

  copair-ext0 : ∀ {x y} → copair in₁ in₂ ≈ id (coprod x y)
  copair-ext0 = begin
      copair in₁ in₂
    ≈˘⟨ copair-cong id-left id-left ⟩
      copair (id _ ∘ in₁) (id _ ∘ in₂)
    ≈⟨ copair-ext (id _) ⟩
      id _
    ∎
    where open ≈-Reasoning isEquiv

  -- FIXME: do this using the general fact that functors preserve isomorphisms
  coproduct-preserve-iso : ∀ {x₁ x₂ y₁ y₂} → Iso x₁ x₂ → Iso y₁ y₂ → Iso (coprod x₁ y₁) (coprod x₂ y₂)
  coproduct-preserve-iso x₁≅x₂ y₁≅y₂ .Iso.fwd = coprod-m (x₁≅x₂ .Iso.fwd) (y₁≅y₂ .Iso.fwd)
  coproduct-preserve-iso x₁≅x₂ y₁≅y₂ .Iso.bwd = coprod-m (x₁≅x₂ .Iso.bwd) (y₁≅y₂ .Iso.bwd)
  coproduct-preserve-iso x₁≅x₂ y₁≅y₂ .Iso.fwd∘bwd≈id =
    begin
      coprod-m (x₁≅x₂ .Iso.fwd) (y₁≅y₂ .Iso.fwd) ∘ coprod-m (x₁≅x₂ .Iso.bwd) (y₁≅y₂ .Iso.bwd)
    ≈˘⟨ coprod-m-comp _ _ _ _ ⟩
      coprod-m (x₁≅x₂ .Iso.fwd ∘ x₁≅x₂ .Iso.bwd) (y₁≅y₂ .Iso.fwd ∘ y₁≅y₂ .Iso.bwd)
    ≈⟨ coprod-m-cong (x₁≅x₂ .Iso.fwd∘bwd≈id) (y₁≅y₂ .Iso.fwd∘bwd≈id) ⟩
      coprod-m (id _) (id _)
    ≈⟨ coprod-m-id ⟩
      id _
    ∎ where open ≈-Reasoning isEquiv
  coproduct-preserve-iso x₁≅x₂ y₁≅y₂ .Iso.bwd∘fwd≈id =
    begin
      coprod-m (x₁≅x₂ .Iso.bwd) (y₁≅y₂ .Iso.bwd) ∘ coprod-m (x₁≅x₂ .Iso.fwd) (y₁≅y₂ .Iso.fwd)
    ≈˘⟨ coprod-m-comp _ _ _ _ ⟩
      coprod-m (x₁≅x₂ .Iso.bwd ∘ x₁≅x₂ .Iso.fwd) (y₁≅y₂ .Iso.bwd ∘ y₁≅y₂ .Iso.fwd)
    ≈⟨ coprod-m-cong (x₁≅x₂ .Iso.bwd∘fwd≈id) (y₁≅y₂ .Iso.bwd∘fwd≈id) ⟩
      coprod-m (id _) (id _)
    ≈⟨ coprod-m-id ⟩
      id _
    ∎ where open ≈-Reasoning isEquiv


module _ {o m e} (𝒞 : Category o m e) where

  open Category 𝒞

  record IsProduct (x : obj) (y : obj) (p : obj) (p₁ : p ⇒ x) (p₂ : p ⇒ y) : Set (o ⊔ m ⊔ e) where
    field
      pair : ∀ {z} → z ⇒ x → z ⇒ y → z ⇒ p
      pair-cong : ∀ {z} {f₁ f₂ : z ⇒ x} {g₁ g₂ : z ⇒ y} → f₁ ≈ f₂ → g₁ ≈ g₂ → pair f₁ g₁ ≈ pair f₂ g₂
      pair-p₁ : ∀ {z} (f : z ⇒ x) (g : z ⇒ y) → (p₁ ∘ pair f g) ≈ f
      pair-p₂ : ∀ {z} (f : z ⇒ x) (g : z ⇒ y) → (p₂ ∘ pair f g) ≈ g
      pair-ext : ∀ {z} (f : z ⇒ p) → pair (p₁ ∘ f) (p₂ ∘ f) ≈ f

    pair-natural : ∀ {w z} (h : w ⇒ z) (f : z ⇒ x) (g : z ⇒ y) → (pair f g ∘ h) ≈ pair (f ∘ h) (g ∘ h)
    pair-natural h f g =
      begin
       pair f g ∘ h
      ≈⟨ ≈-sym (pair-ext _) ⟩
        pair (p₁ ∘ (pair f g ∘ h)) (p₂ ∘ (pair f g ∘ h))
      ≈⟨ ≈-sym (pair-cong (assoc _ _ _) (assoc _ _ _)) ⟩
        pair ((p₁ ∘ pair f g) ∘ h) ((p₂ ∘ pair f g) ∘ h)
      ≈⟨ pair-cong (∘-cong (pair-p₁ _ _) ≈-refl) (∘-cong (pair-p₂ _ _) ≈-refl) ⟩
        pair (f ∘ h) (g ∘ h)
      ∎
      where open ≈-Reasoning isEquiv

    pair-ext0 : pair p₁ p₂ ≈ id p
    pair-ext0 = begin pair p₁ p₂
                        ≈⟨ ≈-sym (pair-cong id-right id-right) ⟩
                      pair (p₁ ∘ id _) (p₂ ∘ id _)
                        ≈⟨ pair-ext (id _) ⟩
                      id _ ∎
      where open ≈-Reasoning isEquiv

  IsProduct-cong : ∀ {x y p} {p₁ p₁' : p ⇒ x} {p₂ p₂' : p ⇒ y} →
                   p₁ ≈ p₁' → p₂ ≈ p₂' →
                   IsProduct x y p p₁ p₂ → IsProduct x y p p₁' p₂'
  IsProduct-cong p₁≈p₁' p₂≈p₂' is-product .IsProduct.pair = is-product .IsProduct.pair
  IsProduct-cong p₁≈p₁' p₂≈p₂' is-product .IsProduct.pair-cong = is-product .IsProduct.pair-cong
  IsProduct-cong p₁≈p₁' p₂≈p₂' is-product .IsProduct.pair-p₁ f g = ≈-trans (∘-cong (≈-sym p₁≈p₁') ≈-refl) (is-product .IsProduct.pair-p₁ f g)
  IsProduct-cong p₁≈p₁' p₂≈p₂' is-product .IsProduct.pair-p₂ f g = ≈-trans (∘-cong (≈-sym p₂≈p₂') ≈-refl) (is-product .IsProduct.pair-p₂ f g)
  IsProduct-cong p₁≈p₁' p₂≈p₂' is-product .IsProduct.pair-ext f =
    ≈-trans (is-product .IsProduct.pair-cong (∘-cong (≈-sym p₁≈p₁') ≈-refl) (∘-cong (≈-sym p₂≈p₂') ≈-refl)) (is-product .IsProduct.pair-ext f)

  record Product (x : obj) (y : obj) : Set (o ⊔ m ⊔ e) where
    field
      prod : obj
      p₁   : prod ⇒ x
      p₂   : prod ⇒ y
      isProduct : IsProduct x y prod p₁ p₂
    open IsProduct isProduct public

  -- FIXME: extend this to all limits and colimits, and include the (co)cones.
  product-iso : ∀ {x y} (P₁ P₂ : Product x y) → Iso (Product.prod P₁) (Product.prod P₂)
  product-iso P₁ P₂ .Iso.fwd = Product.pair P₂ (Product.p₁ P₁) (Product.p₂ P₁)
  product-iso P₁ P₂ .Iso.bwd = Product.pair P₁ (Product.p₁ P₂) (Product.p₂ P₂)
  product-iso P₁ P₂ .Iso.fwd∘bwd≈id =
    begin
      Product.pair P₂ (Product.p₁ P₁) (Product.p₂ P₁) ∘ Product.pair P₁ (Product.p₁ P₂) (Product.p₂ P₂)
    ≈⟨ Product.pair-natural P₂ _ _ _ ⟩
      Product.pair P₂ (Product.p₁ P₁ ∘ Product.pair P₁ (Product.p₁ P₂) (Product.p₂ P₂)) (Product.p₂ P₁ ∘ Product.pair P₁ (Product.p₁ P₂) (Product.p₂ P₂))
    ≈⟨ Product.pair-cong P₂ (Product.pair-p₁ P₁ _ _) (Product.pair-p₂ P₁ _ _) ⟩
      Product.pair P₂ (Product.p₁ P₂) (Product.p₂ P₂)
    ≈⟨ Product.pair-ext0 P₂ ⟩
      id _
    ∎
    where open ≈-Reasoning isEquiv
  product-iso P₁ P₂ .Iso.bwd∘fwd≈id =
    begin
      Product.pair P₁ (Product.p₁ P₂) (Product.p₂ P₂) ∘ Product.pair P₂ (Product.p₁ P₁) (Product.p₂ P₁)
    ≈⟨ Product.pair-natural P₁ _ _ _ ⟩
      Product.pair P₁ (Product.p₁ P₂ ∘ Product.pair P₂ (Product.p₁ P₁) (Product.p₂ P₁)) (Product.p₂ P₂ ∘ Product.pair P₂ (Product.p₁ P₁) (Product.p₂ P₁))
    ≈⟨ Product.pair-cong P₁ (Product.pair-p₁ P₂ _ _) (Product.pair-p₂ P₂ _ _) ⟩
      Product.pair P₁ (Product.p₁ P₁) (Product.p₂ P₁)
    ≈⟨ Product.pair-ext0 P₁ ⟩
      id _
    ∎
    where open ≈-Reasoning isEquiv

record HasProducts {o m e} (𝒞 : Category o m e) : Set (o ⊔ m ⊔ e) where
  open Category 𝒞
  field
    prod : obj → obj → obj
    p₁   : ∀ {x y} → prod x y ⇒ x
    p₂   : ∀ {x y} → prod x y ⇒ y
    pair : ∀ {x y z} → x ⇒ y → x ⇒ z → x ⇒ prod y z

    pair-cong : ∀ {x y z} {f₁ f₂ : x ⇒ y} {g₁ g₂ : x ⇒ z} → f₁ ≈ f₂ → g₁ ≈ g₂ → pair f₁ g₁ ≈ pair f₂ g₂
    pair-p₁ : ∀ {x y z} (f : x ⇒ y) (g : x ⇒ z) → (p₁ ∘ pair f g) ≈ f
    pair-p₂ : ∀ {x y z} (f : x ⇒ y) (g : x ⇒ z) → (p₂ ∘ pair f g) ≈ g
    pair-ext : ∀ {x y z} (f : x ⇒ prod y z) → pair (p₁ ∘ f) (p₂ ∘ f) ≈ f

  pair-natural : ∀ {w x y z} (h : w ⇒ x) (f : x ⇒ y) (g : x ⇒ z) → (pair f g ∘ h) ≈ pair (f ∘ h) (g ∘ h)
  pair-natural h f g =
    begin
      pair f g ∘ h
    ≈⟨ ≈-sym (pair-ext _) ⟩
      pair (p₁ ∘ (pair f g ∘ h)) (p₂ ∘ (pair f g ∘ h))
    ≈⟨ ≈-sym (pair-cong (assoc _ _ _) (assoc _ _ _)) ⟩
      pair ((p₁ ∘ pair f g) ∘ h) ((p₂ ∘ pair f g) ∘ h)
    ≈⟨ pair-cong (∘-cong (pair-p₁ _ _) ≈-refl) (∘-cong (pair-p₂ _ _) ≈-refl) ⟩
      pair (f ∘ h) (g ∘ h)
    ∎
    where open ≈-Reasoning isEquiv

  prod-m : ∀ {x₁ x₂ y₁ y₂} → x₁ ⇒ y₁ → x₂ ⇒ y₂ → prod x₁ x₂ ⇒ prod y₁ y₂
  prod-m f₁ f₂ = pair (f₁ ∘ p₁) (f₂ ∘ p₂)

  swap : ∀ {x y} → prod x y ⇒ prod y x
  swap = pair p₂ p₁

  swap-involutive : ∀ {x y} → (swap {y} {x} ∘ swap {x} {y}) ≈ id _
  swap-involutive = begin
      pair p₂ p₁ ∘ pair p₂ p₁
    ≈⟨ pair-natural _ _ _ ⟩
      pair (p₂ ∘ pair p₂ p₁) (p₁ ∘ pair p₂ p₁)
    ≈⟨ pair-cong (pair-p₂ _ _) (pair-p₁ _ _) ⟩
      pair p₁ p₂
    ≈˘⟨ pair-cong id-right id-right ⟩
      pair (p₁ ∘ id _) (p₂ ∘ id _)
    ≈⟨ pair-ext (id _) ⟩
      id _
    ∎ where open ≈-Reasoning isEquiv

  pair-compose : ∀ {x y₁ y₂ z₁ z₂} (f₁ : y₁ ⇒ z₁) (f₂ : y₂ ⇒ z₂) (g₁ : x ⇒ y₁) (g₂ : x ⇒ y₂) →
    (prod-m f₁ f₂ ∘ pair g₁ g₂) ≈ pair (f₁ ∘ g₁) (f₂ ∘ g₂)
  pair-compose f₁ f₂ g₁ g₂ =
    begin
      prod-m f₁ f₂ ∘ pair g₁ g₂
    ≈⟨ pair-natural _ _ _ ⟩
      pair ((f₁ ∘ p₁) ∘ pair g₁ g₂) ((f₂ ∘ p₂) ∘ pair g₁ g₂)
    ≈⟨ pair-cong (assoc _ _ _) (assoc _ _ _) ⟩
      pair (f₁ ∘ (p₁ ∘ pair g₁ g₂)) (f₂ ∘ (p₂ ∘ pair g₁ g₂))
    ≈⟨ pair-cong (∘-cong ≈-refl (pair-p₁ _ _)) (∘-cong ≈-refl (pair-p₂ _ _)) ⟩
      pair (f₁ ∘ g₁) (f₂ ∘ g₂)
    ∎ where open ≈-Reasoning isEquiv

  pair-functorial : ∀ {x₁ x₂ y₁ y₂ z₁ z₂} (f₁ : y₁ ⇒ z₁) (f₂ : y₂ ⇒ z₂) (g₁ : x₁ ⇒ y₁) (g₂ : x₂ ⇒ y₂) →
    prod-m (f₁ ∘ g₁) (f₂ ∘ g₂) ≈ (prod-m f₁ f₂ ∘ prod-m g₁ g₂)
  pair-functorial f₁ f₂ g₁ g₂ =
    begin
      pair ((f₁ ∘ g₁) ∘ p₁) ((f₂ ∘ g₂) ∘ p₂)
    ≈⟨ pair-cong (assoc _ _ _) (assoc _ _ _) ⟩
      pair (f₁ ∘ (g₁ ∘ p₁)) (f₂ ∘ (g₂ ∘ p₂))
    ≈⟨ ≈-sym (pair-cong (∘-cong ≈-refl (pair-p₁ _ _)) (∘-cong ≈-refl (pair-p₂ _ _))) ⟩
      pair (f₁ ∘ (p₁ ∘ pair (g₁ ∘ p₁) (g₂ ∘ p₂))) (f₂ ∘ (p₂ ∘ pair (g₁ ∘ p₁) (g₂ ∘ p₂)))
    ≈⟨ ≈-sym (pair-cong (assoc _ _ _) (assoc _ _ _)) ⟩
      pair ((f₁ ∘ p₁) ∘ pair (g₁ ∘ p₁) (g₂ ∘ p₂)) ((f₂ ∘ p₂) ∘ pair (g₁ ∘ p₁) (g₂ ∘ p₂))
    ≈⟨ ≈-sym (pair-natural _ _ _) ⟩
      pair (f₁ ∘ p₁) (f₂ ∘ p₂) ∘ pair (g₁ ∘ p₁) (g₂ ∘ p₂)
    ∎
    where open ≈-Reasoning isEquiv

  prod-m-cong : ∀ {x₁ x₂ y₁ y₂} {f₁ f₂ : x₁ ⇒ y₁} {g₁ g₂ : x₂ ⇒ y₂} →
                f₁ ≈ f₂ → g₁ ≈ g₂ → prod-m f₁ g₁ ≈ prod-m f₂ g₂
  prod-m-cong f₁≈f₂ g₁≈g₂ =
    pair-cong (∘-cong f₁≈f₂ ≈-refl) (∘-cong g₁≈g₂ ≈-refl)

  pair-ext0 : ∀ {x y} → pair p₁ p₂ ≈ id (prod x y)
  pair-ext0 = begin pair p₁ p₂
                      ≈⟨ ≈-sym (pair-cong id-right id-right) ⟩
                    pair (p₁ ∘ id _) (p₂ ∘ id _)
                      ≈⟨ pair-ext (id _) ⟩
                    id _ ∎
    where open ≈-Reasoning isEquiv

  prod-m-id : ∀ {x y} → prod-m (id x) (id y) ≈ id (prod x y)
  prod-m-id =
    begin
      pair (id _ ∘ p₁) (id _ ∘ p₂)
    ≈⟨ pair-cong id-left id-left ⟩
      pair p₁ p₂
    ≈⟨ pair-ext0 ⟩
      id _
    ∎
    where open ≈-Reasoning isEquiv

  -- functors preserve isomorphisms
  product-preserves-iso : ∀ {x₁ x₂ y₁ y₂} → Iso x₁ x₂ → Iso y₁ y₂ → Iso (prod x₁ y₁) (prod x₂ y₂)
  product-preserves-iso x₁≅x₂ y₁≅y₂ .Iso.fwd = prod-m (x₁≅x₂ .Iso.fwd) (y₁≅y₂ .Iso.fwd)
  product-preserves-iso x₁≅x₂ y₁≅y₂ .Iso.bwd = prod-m (x₁≅x₂ .Iso.bwd) (y₁≅y₂ .Iso.bwd)
  product-preserves-iso x₁≅x₂ y₁≅y₂ .Iso.fwd∘bwd≈id =
    begin
      prod-m (x₁≅x₂ .Iso.fwd) (y₁≅y₂ .Iso.fwd) ∘ prod-m (x₁≅x₂ .Iso.bwd) (y₁≅y₂ .Iso.bwd)
    ≈⟨ pair-compose _ _ _ _ ⟩
      pair (x₁≅x₂ .Iso.fwd ∘ (x₁≅x₂ .Iso.bwd ∘ p₁)) (y₁≅y₂ .Iso.fwd ∘ (y₁≅y₂ .Iso.bwd ∘ p₂))
    ≈⟨ pair-cong (isEquiv .IsEquivalence.sym (assoc _ _ _)) (isEquiv .IsEquivalence.sym (assoc _ _ _)) ⟩
      prod-m (x₁≅x₂ .Iso.fwd ∘ x₁≅x₂ .Iso.bwd) (y₁≅y₂ .Iso.fwd ∘ y₁≅y₂ .Iso.bwd)
    ≈⟨ prod-m-cong (x₁≅x₂ .Iso.fwd∘bwd≈id) (y₁≅y₂ .Iso.fwd∘bwd≈id) ⟩
      prod-m (id _) (id _)
    ≈⟨ prod-m-id ⟩
      id _
    ∎ where open ≈-Reasoning isEquiv
  product-preserves-iso x₁≅x₂ y₁≅y₂ .Iso.bwd∘fwd≈id =
    begin
      prod-m (x₁≅x₂ .Iso.bwd) (y₁≅y₂ .Iso.bwd) ∘ prod-m (x₁≅x₂ .Iso.fwd) (y₁≅y₂ .Iso.fwd)
    ≈⟨ pair-compose _ _ _ _ ⟩
      pair (x₁≅x₂ .Iso.bwd ∘ (x₁≅x₂ .Iso.fwd ∘ p₁)) (y₁≅y₂ .Iso.bwd ∘ (y₁≅y₂ .Iso.fwd ∘ p₂))
    ≈⟨ pair-cong (isEquiv .IsEquivalence.sym (assoc _ _ _)) (isEquiv .IsEquivalence.sym (assoc _ _ _)) ⟩
      prod-m (x₁≅x₂ .Iso.bwd ∘ x₁≅x₂ .Iso.fwd) (y₁≅y₂ .Iso.bwd ∘ y₁≅y₂ .Iso.fwd)
    ≈⟨ prod-m-cong (x₁≅x₂ .Iso.bwd∘fwd≈id) (y₁≅y₂ .Iso.bwd∘fwd≈id) ⟩
      prod-m (id _) (id _)
    ≈⟨ prod-m-id ⟩
      id _
    ∎ where open ≈-Reasoning isEquiv

  getProduct : ∀ (x y : obj) → Product 𝒞 x y
  getProduct x y .Product.prod = prod x y
  getProduct x y .Product.p₁ = p₁
  getProduct x y .Product.p₂ = p₂
  getProduct x y .Product.isProduct .IsProduct.pair = pair
  getProduct x y .Product.isProduct .IsProduct.pair-cong = pair-cong
  getProduct x y .Product.isProduct .IsProduct.pair-p₁ = pair-p₁
  getProduct x y .Product.isProduct .IsProduct.pair-p₂ = pair-p₂
  getProduct x y .Product.isProduct .IsProduct.pair-ext = pair-ext

make-HasProducts : ∀ {o m e} (𝒞 : Category o m e) → (∀ x y → Product 𝒞 x y) → HasProducts 𝒞
make-HasProducts 𝒞 p .HasProducts.prod x y = p x y .Product.prod
make-HasProducts 𝒞 p .HasProducts.p₁ = p _ _ .Product.p₁
make-HasProducts 𝒞 p .HasProducts.p₂ = p _ _ .Product.p₂
make-HasProducts 𝒞 p .HasProducts.pair = p _ _ .Product.pair
make-HasProducts 𝒞 p .HasProducts.pair-cong = p _ _ .Product.pair-cong
make-HasProducts 𝒞 p .HasProducts.pair-p₁ = p _ _ .Product.pair-p₁
make-HasProducts 𝒞 p .HasProducts.pair-p₂ = p _ _ .Product.pair-p₂
make-HasProducts 𝒞 p .HasProducts.pair-ext = p _ _ .Product.pair-ext

op-coproducts→products : ∀ {o m e} {𝒞 : Category o m e} → HasCoproducts 𝒞 → HasProducts (Category.opposite 𝒞)
op-coproducts→products cp .HasProducts.prod = cp .HasCoproducts.coprod
op-coproducts→products cp .HasProducts.p₁ = cp .HasCoproducts.in₁
op-coproducts→products cp .HasProducts.p₂ = cp .HasCoproducts.in₂
op-coproducts→products cp .HasProducts.pair = cp .HasCoproducts.copair
op-coproducts→products cp .HasProducts.pair-cong = HasCoproducts.copair-cong cp
op-coproducts→products cp .HasProducts.pair-p₁ = HasCoproducts.copair-in₁ cp
op-coproducts→products cp .HasProducts.pair-p₂ = HasCoproducts.copair-in₂ cp
op-coproducts→products cp .HasProducts.pair-ext = HasCoproducts.copair-ext cp

record HasStrongCoproducts {o m e} (𝒞 : Category o m e) (P : HasProducts 𝒞) : Set (o ⊔ m ⊔ e) where
  open Category 𝒞
  open HasProducts P
  field
    coprod : obj → obj → obj
    in₁    : ∀ {x y} → x ⇒ coprod x y
    in₂    : ∀ {x y} → y ⇒ coprod x y
    copair : ∀ {w x y z} → prod w x ⇒ z → prod w y ⇒ z → prod w (coprod x y) ⇒ z

    copair-cong : ∀ {w x y z} {f₁ f₂ : prod w x ⇒ z} {g₁ g₂ : prod w y ⇒ z} →
                  f₁ ≈ f₂ → g₁ ≈ g₂ → copair f₁ g₁ ≈ copair f₂ g₂
    copair-in₁  : ∀ {w x y z} (f : prod w x ⇒ z) (g : prod w y ⇒ z) → (copair f g ∘ pair p₁ (in₁ ∘ p₂)) ≈ f
    copair-in₂  : ∀ {w x y z} (f : prod w x ⇒ z) (g : prod w y ⇒ z) → (copair f g ∘ pair p₁ (in₂ ∘ p₂)) ≈ g
    copair-ext  : ∀ {w x y z} (h : prod w (coprod x y) ⇒ z) →
                  copair (h ∘ pair p₁ (in₁ ∘ p₂)) (h ∘ pair p₁ (in₂ ∘ p₂)) ≈ h

-- Given a terminal, every HasStrongCoproducts gives a plain HasCoproducts:
-- copair f g := strong-copair (f ∘ p₂) (g ∘ p₂) ∘ pair to-terminal (id _).
strong-coproducts→coproducts : ∀ {o m e} {𝒞 : Category o m e} {P : HasProducts 𝒞}
                               → HasTerminal 𝒞 → HasStrongCoproducts 𝒞 P → HasCoproducts 𝒞
strong-coproducts→coproducts {𝒞 = 𝒞} {P = P} T SCP = result
  where
    open Category 𝒞
    open HasProducts P
    open HasTerminal T renaming (witness to 𝟙)
    open HasStrongCoproducts SCP
      using (in₁; in₂)
      renaming (coprod to scoprod; copair to scopair;
                copair-cong to scopair-cong; copair-in₁ to scopair-in₁;
                copair-in₂ to scopair-in₂; copair-ext to scopair-ext)

    -- Section a ⇒ 𝟙 × a for converting plain → strong-shaped.
    sect : ∀ {a} → a ⇒ prod 𝟙 a
    sect = pair to-terminal (id _)

    plain-copair : ∀ {x y z} → x ⇒ z → y ⇒ z → scoprod x y ⇒ z
    plain-copair f g = scopair (f ∘ p₂) (g ∘ p₂) ∘ sect

    -- For the copair-in₁/in₂ proofs: sect ∘ in_i ≈ pair p₁ (in_i ∘ p₂) ∘ sect.
    sect-LHS : ∀ {x y} → (sect ∘ in₁ {x} {y}) ≈ pair to-terminal in₁
    sect-LHS = begin
        pair to-terminal (id _) ∘ in₁
      ≈⟨ pair-natural _ _ _ ⟩
        pair (to-terminal ∘ in₁) (id _ ∘ in₁)
      ≈⟨ pair-cong (≈-sym (to-terminal-ext _)) id-left ⟩
        pair to-terminal in₁
      ∎ where open ≈-Reasoning isEquiv

    sect-LHS₂ : ∀ {x y} → (sect ∘ in₂ {x} {y}) ≈ pair to-terminal in₂
    sect-LHS₂ = begin
        pair to-terminal (id _) ∘ in₂
      ≈⟨ pair-natural _ _ _ ⟩
        pair (to-terminal ∘ in₂) (id _ ∘ in₂)
      ≈⟨ pair-cong (≈-sym (to-terminal-ext _)) id-left ⟩
        pair to-terminal in₂
      ∎ where open ≈-Reasoning isEquiv

    sect-RHS : ∀ {x y} → (pair p₁ (in₁ ∘ p₂) ∘ sect {x}) ≈ pair to-terminal (in₁ {x} {y})
    sect-RHS = begin
        pair p₁ (in₁ ∘ p₂) ∘ pair to-terminal (id _)
      ≈⟨ pair-natural _ _ _ ⟩
        pair (p₁ ∘ pair to-terminal (id _)) ((in₁ ∘ p₂) ∘ pair to-terminal (id _))
      ≈⟨ pair-cong (pair-p₁ _ _) (assoc _ _ _) ⟩
        pair to-terminal (in₁ ∘ (p₂ ∘ pair to-terminal (id _)))
      ≈⟨ pair-cong ≈-refl (∘-cong ≈-refl (pair-p₂ _ _)) ⟩
        pair to-terminal (in₁ ∘ id _)
      ≈⟨ pair-cong ≈-refl id-right ⟩
        pair to-terminal in₁
      ∎ where open ≈-Reasoning isEquiv

    sect-RHS₂ : ∀ {x y} → (pair p₁ (in₂ ∘ p₂) ∘ sect {y}) ≈ pair to-terminal (in₂ {x} {y})
    sect-RHS₂ = begin
        pair p₁ (in₂ ∘ p₂) ∘ pair to-terminal (id _)
      ≈⟨ pair-natural _ _ _ ⟩
        pair (p₁ ∘ pair to-terminal (id _)) ((in₂ ∘ p₂) ∘ pair to-terminal (id _))
      ≈⟨ pair-cong (pair-p₁ _ _) (assoc _ _ _) ⟩
        pair to-terminal (in₂ ∘ (p₂ ∘ pair to-terminal (id _)))
      ≈⟨ pair-cong ≈-refl (∘-cong ≈-refl (pair-p₂ _ _)) ⟩
        pair to-terminal (in₂ ∘ id _)
      ≈⟨ pair-cong ≈-refl id-right ⟩
        pair to-terminal in₂
      ∎ where open ≈-Reasoning isEquiv

    sect-in₁ : ∀ {x y} → (sect ∘ in₁ {x} {y}) ≈ (pair p₁ (in₁ ∘ p₂) ∘ sect)
    sect-in₁ = isEquiv .trans sect-LHS (isEquiv .sym sect-RHS)

    sect-in₂ : ∀ {x y} → (sect ∘ in₂ {x} {y}) ≈ (pair p₁ (in₂ ∘ p₂) ∘ sect)
    sect-in₂ = isEquiv .trans sect-LHS₂ (isEquiv .sym sect-RHS₂)

    p₂-sect : ∀ {a} → (p₂ ∘ sect {a}) ≈ id _
    p₂-sect = pair-p₂ _ _

    result : HasCoproducts 𝒞
    result .HasCoproducts.coprod = scoprod
    result .HasCoproducts.in₁ = in₁
    result .HasCoproducts.in₂ = in₂
    result .HasCoproducts.copair = plain-copair
    result .HasCoproducts.copair-cong f₁≈f₂ g₁≈g₂ =
      ∘-cong (scopair-cong (∘-cong f₁≈f₂ ≈-refl) (∘-cong g₁≈g₂ ≈-refl)) ≈-refl
    result .HasCoproducts.copair-in₁ f g = begin
        (scopair (f ∘ p₂) (g ∘ p₂) ∘ sect) ∘ in₁
      ≈⟨ assoc _ _ _ ⟩
        scopair (f ∘ p₂) (g ∘ p₂) ∘ (sect ∘ in₁)
      ≈⟨ ∘-cong ≈-refl sect-in₁ ⟩
        scopair (f ∘ p₂) (g ∘ p₂) ∘ (pair p₁ (in₁ ∘ p₂) ∘ sect)
      ≈˘⟨ assoc _ _ _ ⟩
        (scopair (f ∘ p₂) (g ∘ p₂) ∘ pair p₁ (in₁ ∘ p₂)) ∘ sect
      ≈⟨ ∘-cong (scopair-in₁ _ _) ≈-refl ⟩
        (f ∘ p₂) ∘ sect
      ≈⟨ assoc _ _ _ ⟩
        f ∘ (p₂ ∘ sect)
      ≈⟨ ∘-cong ≈-refl p₂-sect ⟩
        f ∘ id _
      ≈⟨ id-right ⟩
        f
      ∎ where open ≈-Reasoning isEquiv
    result .HasCoproducts.copair-in₂ f g = begin
        (scopair (f ∘ p₂) (g ∘ p₂) ∘ sect) ∘ in₂
      ≈⟨ assoc _ _ _ ⟩
        scopair (f ∘ p₂) (g ∘ p₂) ∘ (sect ∘ in₂)
      ≈⟨ ∘-cong ≈-refl sect-in₂ ⟩
        scopair (f ∘ p₂) (g ∘ p₂) ∘ (pair p₁ (in₂ ∘ p₂) ∘ sect)
      ≈˘⟨ assoc _ _ _ ⟩
        (scopair (f ∘ p₂) (g ∘ p₂) ∘ pair p₁ (in₂ ∘ p₂)) ∘ sect
      ≈⟨ ∘-cong (scopair-in₂ _ _) ≈-refl ⟩
        (g ∘ p₂) ∘ sect
      ≈⟨ assoc _ _ _ ⟩
        g ∘ (p₂ ∘ sect)
      ≈⟨ ∘-cong ≈-refl p₂-sect ⟩
        g ∘ id _
      ≈⟨ id-right ⟩
        g
      ∎ where open ≈-Reasoning isEquiv
    result .HasCoproducts.copair-ext {x} {y} {z} h = begin
        scopair ((h ∘ in₁) ∘ p₂) ((h ∘ in₂) ∘ p₂) ∘ sect
      ≈⟨ ∘-cong (scopair-cong (assoc _ _ _) (assoc _ _ _)) ≈-refl ⟩
        scopair (h ∘ (in₁ ∘ p₂)) (h ∘ (in₂ ∘ p₂)) ∘ sect
      ≈˘⟨ ∘-cong (scopair-cong (∘-cong ≈-refl (pair-p₂ _ _)) (∘-cong ≈-refl (pair-p₂ _ _))) ≈-refl ⟩
        scopair (h ∘ (p₂ ∘ pair p₁ (in₁ ∘ p₂))) (h ∘ (p₂ ∘ pair p₁ (in₂ ∘ p₂))) ∘ sect
      ≈˘⟨ ∘-cong (scopair-cong (assoc _ _ _) (assoc _ _ _)) ≈-refl ⟩
        scopair ((h ∘ p₂) ∘ pair p₁ (in₁ ∘ p₂)) ((h ∘ p₂) ∘ pair p₁ (in₂ ∘ p₂)) ∘ sect
      ≈⟨ ∘-cong (scopair-ext (h ∘ p₂)) ≈-refl ⟩
        (h ∘ p₂) ∘ sect
      ≈⟨ assoc _ _ _ ⟩
        h ∘ (p₂ ∘ sect)
      ≈⟨ ∘-cong ≈-refl p₂-sect ⟩
        h ∘ id _
      ≈⟨ id-right ⟩
        h
      ∎ where open ≈-Reasoning isEquiv

record HasExponentials {o m e} (𝒞 : Category o m e) (P : HasProducts 𝒞) : Set (o ⊔ m ⊔ e) where
  open Category 𝒞
  open HasProducts P
  field
    exp    : obj → obj → obj
    eval   : ∀ {x y} → prod (exp x y) x ⇒ y
    lambda : ∀ {x y z} → prod x y ⇒ z → x ⇒ exp y z

    lambda-cong : ∀ {x y z} {f₁ f₂ : prod x y ⇒ z} → f₁ ≈ f₂ → lambda f₁ ≈ lambda f₂
    eval-lambda : ∀ {x y z} (f : prod x y ⇒ z) →
                  (eval ∘ prod-m (lambda f) (id _)) ≈ f
    lambda-ext  : ∀ {x y z} (f : x ⇒ exp y z) →
                  lambda (eval ∘ prod-m f (id _)) ≈ f

  lambda-natural : ∀ {x₁ x₂ y z} (f : x₁ ⇒ x₂) (g : prod x₂ y ⇒ z) →
                   (lambda g ∘ f) ≈ lambda (g ∘ prod-m f (id _))
  lambda-natural f g = begin
      lambda g ∘ f
    ≈˘⟨ lambda-ext _ ⟩
      lambda (eval ∘ prod-m (lambda g ∘ f) (id _))
    ≈˘⟨ lambda-cong (∘-cong ≈-refl (prod-m-cong ≈-refl id-left)) ⟩
      lambda (eval ∘ prod-m (lambda g ∘ f) (id _ ∘ id _))
    ≈⟨ lambda-cong (∘-cong ≈-refl (pair-functorial (lambda g) (id _) f (id _))) ⟩
      lambda (eval ∘ (prod-m (lambda g) (id _) ∘ prod-m f (id _)))
    ≈˘⟨ lambda-cong (assoc _ _ _) ⟩
      lambda ((eval ∘ prod-m (lambda g) (id _)) ∘ prod-m f (id _))
    ≈⟨ lambda-cong (∘-cong (eval-lambda g) ≈-refl) ⟩
      lambda (g ∘ prod-m f (id _))
    ∎
    where open ≈-Reasoning isEquiv

  exp-fmor : ∀ {x₁ x₂ y₁ y₂} → x₂ ⇒ x₁ → y₁ ⇒ y₂ → exp x₁ y₁ ⇒ exp x₂ y₂
  exp-fmor f g = lambda (g ∘ (eval ∘ (prod-m (id _) f)))

  exp-cong : ∀ {x₁ x₂ y₁ y₂} {f₁ f₂ : x₂ ⇒ x₁} {g₁ g₂ : y₁ ⇒ y₂} →
             f₁ ≈ f₂ → g₁ ≈ g₂ → exp-fmor f₁ g₁ ≈ exp-fmor f₂ g₂
  exp-cong f₁≈f₂ g₁≈g₂ = lambda-cong (∘-cong g₁≈g₂ (∘-cong ≈-refl (prod-m-cong ≈-refl f₁≈f₂)))

  exp-id : ∀ {x y} → exp-fmor (id x) (id y) ≈ id (exp x y)
  exp-id = begin
      lambda (id _ ∘ (eval ∘ prod-m (id _) (id _)))
    ≈⟨ lambda-cong id-left ⟩
      lambda (eval ∘ prod-m (id _) (id _))
    ≈⟨ lambda-ext (id _) ⟩
      id _
    ∎
    where open ≈-Reasoning isEquiv

  exp-comp : ∀ {x₁ x₂ x₃ y₁ y₂ y₃}
             (f₁ : x₂ ⇒ x₁) (f₂ : x₃ ⇒ x₂)
             (g₁ : y₂ ⇒ y₃) (g₂ : y₁ ⇒ y₂) →
             exp-fmor (f₁ ∘ f₂) (g₁ ∘ g₂) ≈ (exp-fmor f₂ g₁ ∘ exp-fmor f₁ g₂)
  exp-comp f₁ f₂ g₁ g₂ = begin
      lambda ((g₁ ∘ g₂) ∘ (eval ∘ (prod-m (id _) (f₁ ∘ f₂))))
    ≈˘⟨ lambda-cong (∘-cong ≈-refl (∘-cong ≈-refl (prod-m-cong id-left ≈-refl))) ⟩
      lambda ((g₁ ∘ g₂) ∘ (eval ∘ (prod-m (id _ ∘ id _) (f₁ ∘ f₂))))
    ≈⟨ lambda-cong (∘-cong ≈-refl (∘-cong ≈-refl (pair-functorial _ _ _ _))) ⟩
      lambda ((g₁ ∘ g₂) ∘ (eval ∘ (prod-m (id _) f₁ ∘ prod-m (id _) f₂)))
    ≈⟨ lambda-cong (assoc _ _ _) ⟩
      lambda (g₁ ∘ (g₂ ∘ (eval ∘ (prod-m (id _) f₁ ∘ prod-m (id _) f₂))))
    ≈˘⟨ lambda-cong (∘-cong ≈-refl (∘-cong ≈-refl (assoc _ _ _))) ⟩
      lambda (g₁ ∘ (g₂ ∘ ((eval ∘ prod-m (id _) f₁) ∘ prod-m (id _) f₂)))
    ≈˘⟨ lambda-cong (∘-cong ≈-refl (assoc _ _ _)) ⟩
      lambda (g₁ ∘ ((g₂ ∘ (eval ∘ prod-m (id _) f₁)) ∘ prod-m (id _) f₂))
    ≈˘⟨ lambda-cong (∘-cong ≈-refl (∘-cong (eval-lambda _) ≈-refl)) ⟩
      lambda (g₁ ∘ ((eval ∘ prod-m (lambda (g₂ ∘ (eval ∘ prod-m (id _) f₁))) (id _)) ∘ prod-m (id _) f₂))
    ≈⟨ lambda-cong (∘-cong ≈-refl (assoc _ _ _)) ⟩
      lambda (g₁ ∘ (eval ∘ (prod-m (lambda (g₂ ∘ (eval ∘ prod-m (id _) f₁))) (id _) ∘ prod-m (id _) f₂)))
    ≈˘⟨ lambda-cong (∘-cong ≈-refl (∘-cong ≈-refl (pair-functorial _ _ _ _))) ⟩
      lambda (g₁ ∘ (eval ∘ (prod-m (lambda (g₂ ∘ (eval ∘ prod-m (id _) f₁)) ∘ id _) (id _ ∘ f₂))))
    ≈⟨ lambda-cong (∘-cong ≈-refl (∘-cong ≈-refl (prod-m-cong id-swap' id-swap))) ⟩
      lambda (g₁ ∘ (eval ∘ (prod-m (id _ ∘ lambda (g₂ ∘ (eval ∘ prod-m (id _) f₁))) (f₂ ∘ id _))))
    ≈⟨ lambda-cong (∘-cong ≈-refl (∘-cong ≈-refl (pair-functorial _ _ _ _))) ⟩
      lambda (g₁ ∘ (eval ∘ (prod-m (id _) f₂ ∘ prod-m (lambda (g₂ ∘ (eval ∘ prod-m (id _) f₁))) (id _))))
    ≈˘⟨ lambda-cong (∘-cong ≈-refl (assoc _ _ _)) ⟩
      lambda (g₁ ∘ ((eval ∘ prod-m (id _) f₂) ∘ prod-m (lambda (g₂ ∘ (eval ∘ prod-m (id _) f₁))) (id _)))
    ≈˘⟨ lambda-cong (assoc _ _ _) ⟩
      lambda ((g₁ ∘ (eval ∘ prod-m (id _) f₂)) ∘ prod-m (lambda (g₂ ∘ (eval ∘ prod-m (id _) f₁))) (id _))
    ≈˘⟨ lambda-natural _ _ ⟩
      lambda (g₁ ∘ (eval ∘ prod-m (id _) f₂)) ∘ lambda (g₂ ∘ (eval ∘ prod-m (id _) f₁))
    ∎
    where open ≈-Reasoning isEquiv

  -- functors preserve isomorphisms
  exp-preserves-iso : ∀ {x₁ x₂ y₁ y₂} → Iso x₁ x₂ → Iso y₁ y₂ → Iso (exp x₁ y₁) (exp x₂ y₂)
  exp-preserves-iso x₁≅x₂ y₁≅y₂ .Iso.fwd = exp-fmor (x₁≅x₂ .Iso.bwd) (y₁≅y₂ .Iso.fwd)
  exp-preserves-iso x₁≅x₂ y₁≅y₂ .Iso.bwd = exp-fmor (x₁≅x₂ .Iso.fwd) (y₁≅y₂ .Iso.bwd)
  exp-preserves-iso x₁≅x₂ y₁≅y₂ .Iso.fwd∘bwd≈id =
    begin
      exp-fmor (x₁≅x₂ .Iso.bwd) (y₁≅y₂ .Iso.fwd) ∘ exp-fmor (x₁≅x₂ .Iso.fwd) (y₁≅y₂ .Iso.bwd)
    ≈⟨ isEquiv .IsEquivalence.sym (exp-comp _ _ _ _) ⟩
      exp-fmor (x₁≅x₂ .Iso.fwd ∘ x₁≅x₂ .Iso.bwd) (y₁≅y₂ .Iso.fwd ∘ y₁≅y₂ .Iso.bwd)
    ≈⟨ exp-cong (x₁≅x₂ .Iso.fwd∘bwd≈id) (y₁≅y₂ .Iso.fwd∘bwd≈id) ⟩
      exp-fmor (id _) (id _)
    ≈⟨ exp-id ⟩
      id _
    ∎ where open ≈-Reasoning isEquiv
  exp-preserves-iso x₁≅x₂ y₁≅y₂ .Iso.bwd∘fwd≈id =
    begin
      (exp-fmor (x₁≅x₂ .Iso.fwd) (y₁≅y₂ .Iso.bwd) ∘ exp-fmor (x₁≅x₂ .Iso.bwd) (y₁≅y₂ .Iso.fwd))
    ≈⟨ isEquiv .IsEquivalence.sym (exp-comp _ _ _ _) ⟩
      exp-fmor (x₁≅x₂ .Iso.bwd ∘ x₁≅x₂ .Iso.fwd) (y₁≅y₂ .Iso.bwd ∘ y₁≅y₂ .Iso.fwd)
    ≈⟨ exp-cong (x₁≅x₂ .Iso.bwd∘fwd≈id) (y₁≅y₂ .Iso.bwd∘fwd≈id) ⟩
      exp-fmor (id _) (id _)
    ≈⟨ exp-id ⟩
      id _
    ∎ where open ≈-Reasoning isEquiv

-- FIXME: separate out 'endofunctor' and 'natural transformation'
record Monad {o m e} (𝒞 : Category o m e) : Set (o ⊔ m ⊔ e) where
  open Category 𝒞
  field
    M    : obj → obj
    map  : ∀ {x y} → x ⇒ y → M x ⇒ M y
    unit : ∀ {x} → x ⇒ M x
    join : ∀ {x} → M (M x) ⇒ M x
    map-cong : ∀ {x y}{f g : x ⇒ y} → f ≈ g → map f ≈ map g
    map-id   : ∀ {x} → map (id x) ≈ id (M x)
    map-comp : ∀ {x y z} (f : y ⇒ z) (g : x ⇒ y) → map (f ∘ g) ≈ (map f ∘ map g)
    unit-natural : ∀ {x y} (f : x ⇒ y) → (unit ∘ f) ≈ (map f ∘ unit)
    join-natural : ∀ {x y} (f : x ⇒ y) → (join ∘ map (map f)) ≈ (map f ∘ join)
    -- FIXME: actual monad equations

record HasBooleans {o m e} (𝒞 : Category o m e) (T : HasTerminal 𝒞) (P : HasProducts 𝒞) : Set (o ⊔ m ⊔ e) where
  open Category 𝒞
  open HasTerminal T renaming (witness to terminal)
  open HasProducts P
  field
    Bool : obj
    True False : terminal ⇒ Bool
    cond : ∀ {x y} → x ⇒ y → x ⇒ y → prod x Bool ⇒ y
  -- FIXME: equations

-- strong coproducts to booleans
module _ {o m e} {𝒞 : Category o m e} (T : HasTerminal 𝒞) {P : HasProducts 𝒞} (C : HasStrongCoproducts 𝒞 P) where

  open Category 𝒞
  open HasTerminal T renaming (witness to terminal)
  open HasProducts P
  open HasStrongCoproducts C
  open HasBooleans

  strong-coproducts→booleans : HasBooleans 𝒞 T P
  strong-coproducts→booleans .Bool = coprod terminal terminal
  strong-coproducts→booleans .True = in₁
  strong-coproducts→booleans .False = in₂
  strong-coproducts→booleans .cond f g = copair (f ∘ p₁) (g ∘ p₁)

-- coproducts and exponentials to booleans
module _ {o m e} {𝒞 : Category o m e} (T : HasTerminal 𝒞) {P : HasProducts 𝒞} (CP : HasCoproducts 𝒞) (E : HasExponentials 𝒞 P) where

  open Category 𝒞
  open HasProducts P
  open HasCoproducts CP
  open HasTerminal T renaming (witness to terminal)
  open HasExponentials E
  open HasBooleans

  coproducts+exp→booleans : HasBooleans 𝒞 T P
  coproducts+exp→booleans .Bool = coprod terminal terminal
  coproducts+exp→booleans .True = in₁
  coproducts+exp→booleans .False = in₂
  coproducts+exp→booleans .cond f g =
    eval ∘ (prod-m (copair (lambda (f ∘ p₂)) (lambda (g ∘ p₂))) (id _) ∘ pair p₂ p₁)

-- Any CCC has strong coproducts.
ccc→strong-coproducts : ∀ {o m e} {𝒞 : Category o m e} {P : HasProducts 𝒞}
                        → HasCoproducts 𝒞 → HasExponentials 𝒞 P → HasStrongCoproducts 𝒞 P
ccc→strong-coproducts {𝒞 = 𝒞} {P = P} CP E = strongCoproducts
  where
    open Category 𝒞
    open HasProducts P
    open HasCoproducts CP
    open HasExponentials E

    -- Lambda-abstract over the *second* factor of a product (via swap).
    lambda' : ∀ {w x y} → prod w x ⇒ y → x ⇒ exp w y
    lambda' f = lambda (f ∘ swap)

    pair-via-swap : ∀ {w x y} (h : x ⇒ y) → (prod-m h (id _) ∘ swap {w} {x}) ≈ pair (h ∘ p₂) p₁
    pair-via-swap h = begin
        pair (h ∘ p₁) (id _ ∘ p₂) ∘ pair p₂ p₁
      ≈⟨ pair-natural _ _ _ ⟩
        pair ((h ∘ p₁) ∘ pair p₂ p₁) ((id _ ∘ p₂) ∘ pair p₂ p₁)
      ≈⟨ pair-cong (assoc _ _ _) (assoc _ _ _) ⟩
        pair (h ∘ (p₁ ∘ pair p₂ p₁)) (id _ ∘ (p₂ ∘ pair p₂ p₁))
      ≈⟨ pair-cong (∘-cong ≈-refl (pair-p₁ _ _)) (∘-cong ≈-refl (pair-p₂ _ _)) ⟩
        pair (h ∘ p₂) (id _ ∘ p₁)
      ≈⟨ pair-cong ≈-refl id-left ⟩
        pair (h ∘ p₂) p₁
      ∎ where open ≈-Reasoning isEquiv

    eval-lambda' : ∀ {w x y} (f : prod w x ⇒ y) → eval ∘ pair (lambda' f ∘ p₂) p₁ ≈ f
    eval-lambda' f = begin
        eval ∘ pair (lambda (f ∘ swap) ∘ p₂) p₁
      ≈˘⟨ ∘-cong ≈-refl (pair-via-swap (lambda (f ∘ swap))) ⟩
        eval ∘ (prod-m (lambda (f ∘ swap)) (id _) ∘ swap)
      ≈˘⟨ assoc _ _ _ ⟩
        (eval ∘ prod-m (lambda (f ∘ swap)) (id _)) ∘ swap
      ≈⟨ ∘-cong (eval-lambda (f ∘ swap)) ≈-refl ⟩
        (f ∘ swap) ∘ swap
      ≈⟨ assoc _ _ _ ⟩
        f ∘ (swap ∘ swap)
      ≈⟨ ∘-cong ≈-refl swap-involutive ⟩
        f ∘ id _
      ≈⟨ id-right ⟩
        f
      ∎ where open ≈-Reasoning isEquiv

    lambda'-ext : ∀ {w x y} (f : x ⇒ exp w y) → lambda' (eval ∘ pair (f ∘ p₂) p₁) ≈ f
    lambda'-ext f = begin
        lambda ((eval ∘ pair (f ∘ p₂) p₁) ∘ swap)
      ≈⟨ lambda-cong (assoc _ _ _) ⟩
        lambda (eval ∘ (pair (f ∘ p₂) p₁ ∘ swap))
      ≈⟨ lambda-cong (∘-cong ≈-refl (pair-natural _ _ _)) ⟩
        lambda (eval ∘ pair ((f ∘ p₂) ∘ swap) (p₁ ∘ swap))
      ≈⟨ lambda-cong (∘-cong ≈-refl (pair-cong (assoc _ _ _) (pair-p₁ _ _))) ⟩
        lambda (eval ∘ pair (f ∘ (p₂ ∘ swap)) p₂)
      ≈⟨ lambda-cong (∘-cong ≈-refl (pair-cong (∘-cong ≈-refl (pair-p₂ _ _)) ≈-refl)) ⟩
        lambda (eval ∘ pair (f ∘ p₁) p₂)
      ≈˘⟨ lambda-cong (∘-cong ≈-refl (pair-cong ≈-refl id-left)) ⟩
        lambda (eval ∘ pair (f ∘ p₁) (id _ ∘ p₂))
      ≈⟨ lambda-ext f ⟩
        f
      ∎ where open ≈-Reasoning isEquiv

    swap-shape : ∀ {w x x'} (j : x' ⇒ x) →
                 pair (p₁ {w} {x'}) (j ∘ p₂) ∘ swap {x'} {w} ≈ swap {x} {w} ∘ prod-m j (id w)
    swap-shape j = begin
        pair p₁ (j ∘ p₂) ∘ pair p₂ p₁
      ≈⟨ pair-natural _ _ _ ⟩
        pair (p₁ ∘ pair p₂ p₁) ((j ∘ p₂) ∘ pair p₂ p₁)
      ≈⟨ pair-cong (pair-p₁ _ _) (assoc _ _ _) ⟩
        pair p₂ (j ∘ (p₂ ∘ pair p₂ p₁))
      ≈⟨ pair-cong ≈-refl (∘-cong ≈-refl (pair-p₂ _ _)) ⟩
        pair p₂ (j ∘ p₁)
      ≈˘⟨ pair-cong id-left ≈-refl ⟩
        pair (id _ ∘ p₂) (j ∘ p₁)
      ≈˘⟨ pair-cong (pair-p₂ _ _) (pair-p₁ _ _) ⟩
        pair (p₂ ∘ pair (j ∘ p₁) (id _ ∘ p₂)) (p₁ ∘ pair (j ∘ p₁) (id _ ∘ p₂))
      ≈˘⟨ pair-natural _ _ _ ⟩
        pair p₂ p₁ ∘ pair (j ∘ p₁) (id _ ∘ p₂)
      ∎ where open ≈-Reasoning isEquiv

    lambda'-natural : ∀ {w x x' y} (j : x' ⇒ x) (h : prod w x ⇒ y) →
                      lambda' (h ∘ pair p₁ (j ∘ p₂)) ≈ (lambda' h ∘ j)
    lambda'-natural j h = begin
        lambda ((h ∘ pair p₁ (j ∘ p₂)) ∘ swap)
      ≈⟨ lambda-cong (assoc _ _ _) ⟩
        lambda (h ∘ (pair p₁ (j ∘ p₂) ∘ swap))
      ≈⟨ lambda-cong (∘-cong ≈-refl (swap-shape j)) ⟩
        lambda (h ∘ (swap ∘ prod-m j (id _)))
      ≈˘⟨ lambda-cong (assoc _ _ _) ⟩
        lambda ((h ∘ swap) ∘ prod-m j (id _))
      ≈˘⟨ lambda-natural _ _ ⟩
        lambda (h ∘ swap) ∘ j
      ∎ where open ≈-Reasoning isEquiv

    strong-copair : ∀ {w x y z} → prod w x ⇒ z → prod w y ⇒ z → prod w (coprod x y) ⇒ z
    strong-copair f g = eval ∘ pair (copair (lambda' f) (lambda' g) ∘ p₂) p₁

    strong-copair-cong : ∀ {w x y z} {f₁ f₂ : prod w x ⇒ z} {g₁ g₂ : prod w y ⇒ z} →
                         f₁ ≈ f₂ → g₁ ≈ g₂ → strong-copair f₁ g₁ ≈ strong-copair f₂ g₂
    strong-copair-cong f₁≈f₂ g₁≈g₂ =
      ∘-cong ≈-refl (pair-cong (∘-cong (copair-cong (lambda-cong (∘-cong f₁≈f₂ ≈-refl))
                                                    (lambda-cong (∘-cong g₁≈g₂ ≈-refl))) ≈-refl) ≈-refl)

    strong-copair-in₁ : ∀ {w x y z} (f : prod w x ⇒ z) (g : prod w y ⇒ z) →
                        (strong-copair f g ∘ pair p₁ (in₁ ∘ p₂)) ≈ f
    strong-copair-in₁ f g = begin
        (eval ∘ pair (copair (lambda' f) (lambda' g) ∘ p₂) p₁) ∘ pair p₁ (in₁ ∘ p₂)
      ≈⟨ assoc _ _ _ ⟩
        eval ∘ (pair (copair (lambda' f) (lambda' g) ∘ p₂) p₁ ∘ pair p₁ (in₁ ∘ p₂))
      ≈⟨ ∘-cong ≈-refl (pair-natural _ _ _) ⟩
        eval ∘ pair ((copair (lambda' f) (lambda' g) ∘ p₂) ∘ pair p₁ (in₁ ∘ p₂)) (p₁ ∘ pair p₁ (in₁ ∘ p₂))
      ≈⟨ ∘-cong ≈-refl (pair-cong (assoc _ _ _) (pair-p₁ _ _)) ⟩
        eval ∘ pair (copair (lambda' f) (lambda' g) ∘ (p₂ ∘ pair p₁ (in₁ ∘ p₂))) p₁
      ≈⟨ ∘-cong ≈-refl (pair-cong (∘-cong ≈-refl (pair-p₂ _ _)) ≈-refl) ⟩
        eval ∘ pair (copair (lambda' f) (lambda' g) ∘ (in₁ ∘ p₂)) p₁
      ≈˘⟨ ∘-cong ≈-refl (pair-cong (assoc _ _ _) ≈-refl) ⟩
        eval ∘ pair ((copair (lambda' f) (lambda' g) ∘ in₁) ∘ p₂) p₁
      ≈⟨ ∘-cong ≈-refl (pair-cong (∘-cong (copair-in₁ _ _) ≈-refl) ≈-refl) ⟩
        eval ∘ pair (lambda' f ∘ p₂) p₁
      ≈⟨ eval-lambda' f ⟩
        f
      ∎ where open ≈-Reasoning isEquiv

    strong-copair-in₂ : ∀ {w x y z} (f : prod w x ⇒ z) (g : prod w y ⇒ z) →
                        (strong-copair f g ∘ pair p₁ (in₂ ∘ p₂)) ≈ g
    strong-copair-in₂ f g = begin
        (eval ∘ pair (copair (lambda' f) (lambda' g) ∘ p₂) p₁) ∘ pair p₁ (in₂ ∘ p₂)
      ≈⟨ assoc _ _ _ ⟩
        eval ∘ (pair (copair (lambda' f) (lambda' g) ∘ p₂) p₁ ∘ pair p₁ (in₂ ∘ p₂))
      ≈⟨ ∘-cong ≈-refl (pair-natural _ _ _) ⟩
        eval ∘ pair ((copair (lambda' f) (lambda' g) ∘ p₂) ∘ pair p₁ (in₂ ∘ p₂)) (p₁ ∘ pair p₁ (in₂ ∘ p₂))
      ≈⟨ ∘-cong ≈-refl (pair-cong (assoc _ _ _) (pair-p₁ _ _)) ⟩
        eval ∘ pair (copair (lambda' f) (lambda' g) ∘ (p₂ ∘ pair p₁ (in₂ ∘ p₂))) p₁
      ≈⟨ ∘-cong ≈-refl (pair-cong (∘-cong ≈-refl (pair-p₂ _ _)) ≈-refl) ⟩
        eval ∘ pair (copair (lambda' f) (lambda' g) ∘ (in₂ ∘ p₂)) p₁
      ≈˘⟨ ∘-cong ≈-refl (pair-cong (assoc _ _ _) ≈-refl) ⟩
        eval ∘ pair ((copair (lambda' f) (lambda' g) ∘ in₂) ∘ p₂) p₁
      ≈⟨ ∘-cong ≈-refl (pair-cong (∘-cong (copair-in₂ _ _) ≈-refl) ≈-refl) ⟩
        eval ∘ pair (lambda' g ∘ p₂) p₁
      ≈⟨ eval-lambda' g ⟩
        g
      ∎ where open ≈-Reasoning isEquiv

    strong-copair-ext : ∀ {w x y z} (h : prod w (coprod x y) ⇒ z) →
                        strong-copair (h ∘ pair p₁ (in₁ ∘ p₂)) (h ∘ pair p₁ (in₂ ∘ p₂)) ≈ h
    strong-copair-ext h = begin
        eval ∘ pair (copair (lambda' (h ∘ pair p₁ (in₁ ∘ p₂))) (lambda' (h ∘ pair p₁ (in₂ ∘ p₂))) ∘ p₂) p₁
      ≈⟨ ∘-cong ≈-refl (pair-cong (∘-cong (copair-cong (lambda'-natural in₁ h) (lambda'-natural in₂ h)) ≈-refl) ≈-refl) ⟩
        eval ∘ pair (copair (lambda' h ∘ in₁) (lambda' h ∘ in₂) ∘ p₂) p₁
      ≈⟨ ∘-cong ≈-refl (pair-cong (∘-cong (copair-ext _) ≈-refl) ≈-refl) ⟩
        eval ∘ pair (lambda' h ∘ p₂) p₁
      ≈⟨ eval-lambda' h ⟩
        h
      ∎ where open ≈-Reasoning isEquiv

    strongCoproducts : HasStrongCoproducts 𝒞 P
    strongCoproducts .HasStrongCoproducts.coprod = coprod
    strongCoproducts .HasStrongCoproducts.in₁ = in₁
    strongCoproducts .HasStrongCoproducts.in₂ = in₂
    strongCoproducts .HasStrongCoproducts.copair = strong-copair
    strongCoproducts .HasStrongCoproducts.copair-cong = strong-copair-cong
    strongCoproducts .HasStrongCoproducts.copair-in₁ = strong-copair-in₁
    strongCoproducts .HasStrongCoproducts.copair-in₂ = strong-copair-in₂
    strongCoproducts .HasStrongCoproducts.copair-ext = strong-copair-ext
