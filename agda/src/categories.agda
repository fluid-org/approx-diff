{-# OPTIONS --prop --postfix-projections --safe #-}

module categories where

open import Level using (suc; _⊔_; Lift; lift)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import prop using (LiftP; Prf; ⊤; ⟪_⟫; tt; lift)
open import prop-setoid
  using (IsEquivalence; Setoid; module ≈-Reasoning)

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

------------------------------------------------------------------------------
-- Products
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

record HasLists {o m e} (𝒞 : Category o m e) (T : HasTerminal 𝒞) (P : HasProducts 𝒞) : Set (o ⊔ m ⊔ e) where
  open Category 𝒞
  open HasTerminal T renaming (witness to terminal)
  open HasProducts P
  field
    list : obj → obj
    nil  : ∀ {x} → terminal ⇒ list x
    cons : ∀ {x} → prod x (list x) ⇒ list x
    fold : ∀ {x y z} →
           x ⇒ z →
           prod (prod x y) z ⇒ z →
           prod x (list y) ⇒ z
  -- FIXME: equations

record HasStrongCoproducts {o m e} (𝒞 : Category o m e) (P : HasProducts 𝒞) : Set (o ⊔ m ⊔ e) where
  open Category 𝒞
  open HasProducts P
  field
    coprod : obj → obj → obj
    in₁    : ∀ {x y} → x ⇒ coprod x y
    in₂    : ∀ {x y} → y ⇒ coprod x y
    copair : ∀ {w x y z} → prod w x ⇒ z → prod w y ⇒ z → prod w (coprod x y) ⇒ z

------------------------------------------------------------------------------
-- A Setoid as a (groupoid) category: objects are Carrier elements, morphisms
-- are setoid equivalences (proof-irrelevant via Prf).

open import prop-setoid using (⊤-isEquivalence)

setoid→category : ∀ {o e} → Setoid o e → Category o e e
setoid→category A .Category.obj = A .Setoid.Carrier
setoid→category A .Category._⇒_ x y = Prf (A .Setoid._≈_ x y)
setoid→category A .Category._≈_ _ _ = ⊤
setoid→category A .Category.isEquiv = ⊤-isEquivalence
setoid→category A .Category.id x = ⟪ A .Setoid.isEquivalence .refl ⟫
setoid→category A .Category._∘_ ⟪ f ⟫ ⟪ g ⟫ = ⟪ A .Setoid.isEquivalence .trans g f ⟫
setoid→category A .Category.∘-cong _ _ = tt
setoid→category A .Category.id-left = tt
setoid→category A .Category.id-right = tt
setoid→category A .Category.assoc _ _ _ = tt
