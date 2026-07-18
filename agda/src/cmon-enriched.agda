{-# OPTIONS --prop --postfix-projections --safe #-}

module cmon-enriched where

open import Level
open import categories using (Category; HasProducts; HasCoproducts; HasTerminal; HasInitial; IsTerminal; IsInitial)
open import prop-setoid using (module ≈-Reasoning; IsEquivalence)
open import commutative-monoid using (CommutativeMonoid)

-- Additional biproduct bits:
--   https://arxiv.org/pdf/1801.06488

record CMonEnriched {o m e} (𝒞 : Category o m e) : Set (o ⊔ m ⊔ e) where
  open Category 𝒞
  open CommutativeMonoid
  open IsEquivalence
  field
    homCM : ∀ x y → CommutativeMonoid (hom-setoid x y)

  _+m_ : ∀ {x y} → x ⇒ y → x ⇒ y → x ⇒ y
  f +m g = homCM _ _ ._+_ f g

  infixl 21 _+m_

  εm : ∀ {x y} → x ⇒ y
  εm {x} {y} = homCM x y .ε

  +m-runit : ∀ {x y} {f : x ⇒ y} → (f +m εm) ≈ f
  +m-runit = isEquiv .trans (homCM _ _ .+-comm) (homCM _ _ .+-lunit)

  field
    comp-bilinear₁ : ∀ {X Y Z} (f₁ f₂ : Y ⇒ Z) (g : X ⇒ Y) →
                     ((f₁ +m f₂) ∘ g) ≈ ((f₁ ∘ g) +m (f₂ ∘ g))
    comp-bilinear₂ : ∀ {X Y Z} (f : Y ⇒ Z) (g₁ g₂ : X ⇒ Y) →
                     (f ∘ (g₁ +m g₂)) ≈ ((f ∘ g₁) +m (f ∘ g₂))
    comp-bilinear-ε₁ : ∀ {X Y Z} (f : X ⇒ Y) → (εm ∘ f) ≈ εm {X} {Z}
    comp-bilinear-ε₂ : ∀ {X Y Z} (f : Y ⇒ Z) → (f ∘ εm) ≈ εm {X} {Z}

module _ {o m e} {𝒞 : Category o m e} (CM : CMonEnriched 𝒞) where
  open Category 𝒞
  open CMonEnriched CM
  open CommutativeMonoid

  record Biproduct (A B : Category.obj 𝒞) : Set (o ⊔ m ⊔ e) where
    field
      prod : obj
      p₁ : prod ⇒ A
      p₂ : prod ⇒ B
      in₁ : A ⇒ prod
      in₂ : B ⇒ prod

      id-1 : (p₁ ∘ in₁) ≈ id A
      id-2 : (p₂ ∘ in₂) ≈ id B
      zero-1 : (p₁ ∘ in₂) ≈ εm
      zero-2 : (p₂ ∘ in₁) ≈ εm
      id-+   : ((in₁ ∘ p₁) +m (in₂ ∘ p₂)) ≈ id prod

    -- Derived: products via biproduct.
    pair : ∀ {x} → x ⇒ A → x ⇒ B → x ⇒ prod
    pair f g = (in₁ ∘ f) +m (in₂ ∘ g)

    pair-cong : ∀ {x} {f₁ f₂ : x ⇒ A} {g₁ g₂ : x ⇒ B} →
                f₁ ≈ f₂ → g₁ ≈ g₂ → pair f₁ g₁ ≈ pair f₂ g₂
    pair-cong f₁≈f₂ g₁≈g₂ = homCM _ _ .+-cong (∘-cong ≈-refl f₁≈f₂) (∘-cong ≈-refl g₁≈g₂)

    pair-p₁ : ∀ {x} (f : x ⇒ A) (g : x ⇒ B) → (p₁ ∘ pair f g) ≈ f
    pair-p₁ f g =
      begin
        p₁ ∘ pair f g                       ≡⟨⟩
        p₁ ∘ ((in₁ ∘ f) +m (in₂ ∘ g))        ≈⟨ comp-bilinear₂ _ _ _ ⟩
        (p₁ ∘ (in₁ ∘ f)) +m (p₁ ∘ (in₂ ∘ g))  ≈˘⟨ homCM _ _ .+-cong (assoc _ _ _) (assoc _ _ _) ⟩
        ((p₁ ∘ in₁) ∘ f) +m ((p₁ ∘ in₂) ∘ g)  ≈⟨ homCM _ _ .+-cong (∘-cong id-1 ≈-refl) (∘-cong zero-1 ≈-refl) ⟩
        (id _ ∘ f) +m (εm ∘ g)               ≈⟨ homCM _ _ .+-cong id-left (comp-bilinear-ε₁ _) ⟩
        f +m εm                             ≈⟨ homCM _ _ .+-comm ⟩
        εm +m f                             ≈⟨ homCM _ _ .+-lunit ⟩
        f                                   ∎
      where open ≈-Reasoning isEquiv

    pair-p₂ : ∀ {x} (f : x ⇒ A) (g : x ⇒ B) → (p₂ ∘ pair f g) ≈ g
    pair-p₂ f g =
      begin
        p₂ ∘ pair f g                       ≡⟨⟩
        p₂ ∘ ((in₁ ∘ f) +m (in₂ ∘ g))        ≈⟨ comp-bilinear₂ _ _ _ ⟩
        (p₂ ∘ (in₁ ∘ f)) +m (p₂ ∘ (in₂ ∘ g))  ≈˘⟨ homCM _ _ .+-cong (assoc _ _ _) (assoc _ _ _) ⟩
        ((p₂ ∘ in₁) ∘ f) +m ((p₂ ∘ in₂) ∘ g)  ≈⟨ homCM _ _ .+-cong (∘-cong zero-2 ≈-refl) (∘-cong id-2 ≈-refl) ⟩
        (εm ∘ f) +m (id _ ∘ g)               ≈⟨ homCM _ _ .+-cong (comp-bilinear-ε₁ _) id-left ⟩
        εm +m g                             ≈⟨ homCM _ _ .+-lunit ⟩
        g                                   ∎
      where open ≈-Reasoning isEquiv

    pair-ext : ∀ {x} (f : x ⇒ prod) → pair (p₁ ∘ f) (p₂ ∘ f) ≈ f
    pair-ext f =
      begin
        pair (p₁ ∘ f) (p₂ ∘ f)              ≡⟨⟩
        (in₁ ∘ (p₁ ∘ f)) +m (in₂ ∘ (p₂ ∘ f)) ≈˘⟨ homCM _ _ .+-cong (assoc _ _ _) (assoc _ _ _) ⟩
        ((in₁ ∘ p₁) ∘ f) +m ((in₂ ∘ p₂) ∘ f) ≈˘⟨ comp-bilinear₁ _ _ _ ⟩
        ((in₁ ∘ p₁) +m (in₂ ∘ p₂)) ∘ f       ≈⟨ ∘-cong id-+ ≈-refl ⟩
        id _ ∘ f                            ≈⟨ id-left ⟩
        f                                   ∎
      where open ≈-Reasoning isEquiv

    pair-natural : ∀ {w x} (f : w ⇒ A) (g : w ⇒ B) (h : x ⇒ w) → (pair f g ∘ h) ≈ pair (f ∘ h) (g ∘ h)
    pair-natural f g h =
      begin
        ((in₁ ∘ f) +m (in₂ ∘ g)) ∘ h
      ≈⟨ comp-bilinear₁ _ _ h ⟩
        ((in₁ ∘ f) ∘ h) +m ((in₂ ∘ g) ∘ h)
      ≈⟨ homCM _ _ .+-cong (assoc _ _ _) (assoc _ _ _) ⟩
        (in₁ ∘ (f ∘ h)) +m (in₂ ∘ (g ∘ h))
      ∎ where open ≈-Reasoning isEquiv

    pair-ext0 : pair p₁ p₂ ≈ id prod
    pair-ext0 = ≈-trans (≈-sym (pair-cong id-right id-right)) (pair-ext (id _))

    -- Derived: coproducts via biproduct.
    copair : ∀ {x} → A ⇒ x → B ⇒ x → prod ⇒ x
    copair f g = (f ∘ p₁) +m (g ∘ p₂)

    copair-cong : ∀ {x} {f₁ f₂ : A ⇒ x} {g₁ g₂ : B ⇒ x} →
                    f₁ ≈ f₂ → g₁ ≈ g₂ → copair f₁ g₁ ≈ copair f₂ g₂
    copair-cong f₁≈f₂ g₁≈g₂ = homCM _ _ .+-cong (∘-cong f₁≈f₂ ≈-refl) (∘-cong g₁≈g₂ ≈-refl)

    copair-in₁ : ∀ {x} (f : A ⇒ x) (g : B ⇒ x) → (copair f g ∘ in₁) ≈ f
    copair-in₁ f g =
      begin copair f g ∘ in₁                     ≡⟨⟩
             ((f ∘ p₁) +m (g ∘ p₂)) ∘ in₁         ≈⟨ comp-bilinear₁ _ _ _ ⟩
             ((f ∘ p₁) ∘ in₁) +m ((g ∘ p₂) ∘ in₁)  ≈⟨ homCM _ _ .+-cong (assoc _ _ _) (assoc _ _ _) ⟩
             (f ∘ (p₁ ∘ in₁)) +m (g ∘ (p₂ ∘ in₁))  ≈⟨ homCM _ _ .+-cong (∘-cong ≈-refl id-1) (∘-cong ≈-refl zero-2) ⟩
             (f ∘ id _) +m (g ∘ εm)               ≈⟨ homCM _ _ .+-cong id-right (comp-bilinear-ε₂ _) ⟩
             f +m εm                             ≈⟨ homCM _ _ .+-comm ⟩
             εm +m f                             ≈⟨ homCM _ _ .+-lunit ⟩
             f                                  ∎
      where open ≈-Reasoning isEquiv

    copair-in₂ : ∀ {x} (f : A ⇒ x) (g : B ⇒ x) → (copair f g ∘ in₂) ≈ g
    copair-in₂ f g =
      begin copair f g ∘ in₂                     ≡⟨⟩
             ((f ∘ p₁) +m (g ∘ p₂)) ∘ in₂         ≈⟨ comp-bilinear₁ _ _ _ ⟩
             ((f ∘ p₁) ∘ in₂) +m ((g ∘ p₂) ∘ in₂)  ≈⟨ homCM _ _ .+-cong (assoc _ _ _) (assoc _ _ _) ⟩
             (f ∘ (p₁ ∘ in₂)) +m (g ∘ (p₂ ∘ in₂))  ≈⟨ homCM _ _ .+-cong (∘-cong ≈-refl zero-1) (∘-cong ≈-refl id-2) ⟩
             (f ∘ εm) +m (g ∘ id _)               ≈⟨ homCM _ _ .+-cong (comp-bilinear-ε₂ _) id-right ⟩
             εm +m g                             ≈⟨ homCM _ _ .+-lunit ⟩
             g                                  ∎
      where open ≈-Reasoning isEquiv

    copair-ext : ∀ {x} (f : prod ⇒ x) → copair (f ∘ in₁) (f ∘ in₂) ≈ f
    copair-ext f =
      begin copair (f ∘ in₁) (f ∘ in₂)           ≡⟨⟩
             ((f ∘ in₁) ∘ p₁) +m ((f ∘ in₂) ∘ p₂) ≈⟨ homCM _ _ .+-cong (assoc _ _ _) (assoc _ _ _) ⟩
             (f ∘ (in₁ ∘ p₁)) +m (f ∘ (in₂ ∘ p₂)) ≈˘⟨ comp-bilinear₂ _ _ _ ⟩
             f ∘ ((in₁ ∘ p₁) +m (in₂ ∘ p₂))       ≈⟨ ∘-cong ≈-refl id-+ ⟩
             f ∘ id _                            ≈⟨ id-right ⟩
             f ∎
      where open ≈-Reasoning isEquiv

  -- Zero objects: an object Z with id Z ≈ εm is both initial and terminal.
  -- Uniqueness comes from f = id Z ∘ f = εm ∘ f = εm (and dually for g ∘ id Z).
  record HasZero : Set (o ⊔ m ⊔ e) where
    field
      witness        : obj
      id-witness≈εm : id witness ≈ εm

    is-terminal : IsTerminal 𝒞 witness
    is-terminal .IsTerminal.to-terminal       = εm
    is-terminal .IsTerminal.to-terminal-ext f =
      ≈-trans (≈-sym (comp-bilinear-ε₁ f))
              (≈-trans (∘-cong (≈-sym id-witness≈εm) ≈-refl) id-left)

    is-initial : IsInitial 𝒞 witness
    is-initial .IsInitial.from-initial       = εm
    is-initial .IsInitial.from-initial-ext g =
      ≈-trans (≈-sym (comp-bilinear-ε₂ g))
              (≈-trans (∘-cong ≈-refl (≈-sym id-witness≈εm)) id-right)

    hasTerminal : HasTerminal 𝒞
    hasTerminal .HasTerminal.witness     = witness
    hasTerminal .HasTerminal.is-terminal = is-terminal

    hasInitial : HasInitial 𝒞
    hasInitial .HasInitial.witness    = witness
    hasInitial .HasInitial.is-initial = is-initial

  -- Biproducts give both products and coproducts.
  module _ where
    open Biproduct

    biproducts→products : (∀ x y → Biproduct x y) → HasProducts 𝒞
    biproducts→products bp .HasProducts.prod x y = prod (bp x y)
    biproducts→products bp .HasProducts.p₁ {x} {y} = p₁ (bp x y)
    biproducts→products bp .HasProducts.p₂ {x} {y} = p₂ (bp x y)
    biproducts→products bp .HasProducts.pair {x} {y} {z} = pair (bp y z)
    biproducts→products bp .HasProducts.pair-cong {x} {y} {z} = pair-cong (bp y z)
    biproducts→products bp .HasProducts.pair-p₁ {x} {y} {z} = pair-p₁ (bp y z)
    biproducts→products bp .HasProducts.pair-p₂ {x} {y} {z} = pair-p₂ (bp y z)
    biproducts→products bp .HasProducts.pair-ext {x} {y} {z} = pair-ext (bp y z)

    -- Any two biproducts on the same pair are canonically isomorphic.
    biproduct-iso : ∀ {A B} (bp₁ bp₂ : Biproduct A B) → Category.IsIso 𝒞 (pair bp₂ (p₁ bp₁) (p₂ bp₁))
    biproduct-iso bp₁ bp₂ .Category.IsIso.inverse = pair bp₁ (p₁ bp₂) (p₂ bp₂)
    biproduct-iso bp₁ bp₂ .Category.IsIso.f∘inverse≈id =
      begin
        pair bp₂ (p₁ bp₁) (p₂ bp₁) ∘ pair bp₁ (p₁ bp₂) (p₂ bp₂)
      ≈⟨ pair-natural bp₂ _ _ _ ⟩
        pair bp₂ (p₁ bp₁ ∘ pair bp₁ (p₁ bp₂) (p₂ bp₂)) (p₂ bp₁ ∘ pair bp₁ (p₁ bp₂) (p₂ bp₂))
      ≈⟨ pair-cong bp₂ (pair-p₁ bp₁ _ _) (pair-p₂ bp₁ _ _) ⟩
        pair bp₂ (p₁ bp₂) (p₂ bp₂)
      ≈⟨ pair-ext0 bp₂ ⟩
        id (prod bp₂)
      ∎ where open ≈-Reasoning isEquiv
    biproduct-iso bp₁ bp₂ .Category.IsIso.inverse∘f≈id =
      begin
        pair bp₁ (p₁ bp₂) (p₂ bp₂) ∘ pair bp₂ (p₁ bp₁) (p₂ bp₁)
      ≈⟨ pair-natural bp₁ _ _ _ ⟩
        pair bp₁ (p₁ bp₂ ∘ pair bp₂ (p₁ bp₁) (p₂ bp₁)) (p₂ bp₂ ∘ pair bp₂ (p₁ bp₁) (p₂ bp₁))
      ≈⟨ pair-cong bp₁ (pair-p₁ bp₂ _ _) (pair-p₂ bp₂ _ _) ⟩
        pair bp₁ (p₁ bp₁) (p₂ bp₁)
      ≈⟨ pair-ext0 bp₁ ⟩
        id (prod bp₁)
      ∎ where open ≈-Reasoning isEquiv

    biproducts→coproducts : (∀ x y → Biproduct x y) → HasCoproducts 𝒞
    biproducts→coproducts bp .HasCoproducts.coprod x y = prod (bp x y)
    biproducts→coproducts bp .HasCoproducts.in₁ {x} {y} = in₁ (bp x y)
    biproducts→coproducts bp .HasCoproducts.in₂ {x} {y} = in₂ (bp x y)
    biproducts→coproducts bp .HasCoproducts.copair {x} {y} = copair (bp x y)
    biproducts→coproducts bp .HasCoproducts.copair-cong {x} {y} = copair-cong (bp x y)
    biproducts→coproducts bp .HasCoproducts.copair-in₁ {x} {y} = copair-in₁ (bp x y)
    biproducts→coproducts bp .HasCoproducts.copair-in₂ {x} {y} = copair-in₂ (bp x y)
    biproducts→coproducts bp .HasCoproducts.copair-ext {x} {y} = copair-ext (bp x y)

    module _ (bp : ∀ x y → Biproduct x y) where
      private
        module BProds = HasProducts (biproducts→products bp)
        module BCoprods = HasCoproducts (biproducts→coproducts bp)

      coprod-m-pair-id : ∀ {x y z} (F : x ⇒ y) (G : x ⇒ z) →
                         (BCoprods.coprod-m F G ∘ BProds.pair (id _) (id _)) ≈ BProds.pair F G
      coprod-m-pair-id F G =
        begin
          BCoprods.coprod-m F G ∘ BProds.pair (id _) (id _)
        ≈⟨ comp-bilinear₂ _ _ _ ⟩
          (BCoprods.coprod-m F G ∘ (BCoprods.in₁ ∘ id _)) +m (BCoprods.coprod-m F G ∘ (BCoprods.in₂ ∘ id _))
        ≈⟨ homCM _ _ .CommutativeMonoid.+-cong
             (∘-cong ≈-refl id-right) (∘-cong ≈-refl id-right) ⟩
          (BCoprods.coprod-m F G ∘ BCoprods.in₁) +m (BCoprods.coprod-m F G ∘ BCoprods.in₂)
        ≈⟨ homCM _ _ .CommutativeMonoid.+-cong (BCoprods.copair-in₁ _ _) (BCoprods.copair-in₂ _ _) ⟩
          BProds.pair F G
        ∎ where open ≈-Reasoning isEquiv

      open BProds   using () renaming (p₁ to bp₁; p₂ to bp₂; prod-m to bprod-m)
      open BCoprods using () renaming (in₁ to bin₁; in₂ to bin₂; copair to bcopair)
      open CommutativeMonoid

      codiag-pair-+m : ∀ {x y} (a b : x ⇒ y) → bcopair (id _) (id _) ∘ BProds.pair a b ≈ a +m b
      codiag-pair-+m a b =
        begin
          bcopair (id _) (id _) ∘ BProds.pair a b
        ≡⟨⟩
          ((id _ ∘ bp₁) +m (id _ ∘ bp₂)) ∘ BProds.pair a b
        ≈⟨ comp-bilinear₁ _ _ _ ⟩
          ((id _ ∘ bp₁) ∘ BProds.pair a b) +m ((id _ ∘ bp₂) ∘ BProds.pair a b)
        ≈⟨ homCM _ _ .+-cong (assoc _ _ _) (assoc _ _ _) ⟩
          (id _ ∘ (bp₁ ∘ BProds.pair a b)) +m (id _ ∘ (bp₂ ∘ BProds.pair a b))
        ≈⟨ homCM _ _ .+-cong id-left id-left ⟩
          (bp₁ ∘ BProds.pair a b) +m (bp₂ ∘ BProds.pair a b)
        ≈⟨ homCM _ _ .+-cong (BProds.pair-p₁ _ _) (BProds.pair-p₂ _ _) ⟩
          a +m b
        ∎ where open ≈-Reasoning isEquiv

      in₁-natural : ∀ {x₁ y₁ x₂ y₂} {f : x₁ ⇒ y₁} {g : x₂ ⇒ y₂} →
                    (bprod-m f g ∘ bin₁) ≈ (bin₁ ∘ f)
      in₁-natural {f = f} {g = g} =
        begin
          ((bin₁ ∘ (f ∘ bp₁)) +m (bin₂ ∘ (g ∘ bp₂))) ∘ bin₁
        ≈⟨ comp-bilinear₁ _ _ _ ⟩
          ((bin₁ ∘ (f ∘ bp₁)) ∘ bin₁) +m ((bin₂ ∘ (g ∘ bp₂)) ∘ bin₁)
        ≈⟨ homCM _ _ .+-cong (assoc _ _ _) (assoc _ _ _) ⟩
          (bin₁ ∘ ((f ∘ bp₁) ∘ bin₁)) +m (bin₂ ∘ ((g ∘ bp₂) ∘ bin₁))
        ≈⟨ homCM _ _ .+-cong (∘-cong ≈-refl (assoc _ _ _)) (∘-cong ≈-refl (assoc _ _ _)) ⟩
          (bin₁ ∘ (f ∘ (bp₁ ∘ bin₁))) +m (bin₂ ∘ (g ∘ (bp₂ ∘ bin₁)))
        ≈⟨ homCM _ _ .+-cong (∘-cong ≈-refl (∘-cong ≈-refl (bp _ _ .Biproduct.id-1))) (∘-cong ≈-refl (∘-cong ≈-refl (bp _ _ .Biproduct.zero-2))) ⟩
          (bin₁ ∘ (f ∘ id _)) +m (bin₂ ∘ (g ∘ εm))
        ≈⟨ homCM _ _ .+-cong (∘-cong ≈-refl id-right) (∘-cong ≈-refl (comp-bilinear-ε₂ _)) ⟩
          (bin₁ ∘ f) +m (bin₂ ∘ εm)
        ≈⟨ homCM _ _ .+-cong ≈-refl (comp-bilinear-ε₂ _) ⟩
          (bin₁ ∘ f) +m εm
        ≈⟨ +m-runit ⟩
          bin₁ ∘ f
        ∎ where open ≈-Reasoning isEquiv

      in₂-natural : ∀ {x₁ y₁ x₂ y₂} {f : x₁ ⇒ y₁} {g : x₂ ⇒ y₂} →
                    (bprod-m f g ∘ bin₂) ≈ (bin₂ ∘ g)
      in₂-natural {f = f} {g = g} =
        begin
          ((bin₁ ∘ (f ∘ bp₁)) +m (bin₂ ∘ (g ∘ bp₂))) ∘ bin₂
        ≈⟨ comp-bilinear₁ _ _ _ ⟩
          ((bin₁ ∘ (f ∘ bp₁)) ∘ bin₂) +m ((bin₂ ∘ (g ∘ bp₂)) ∘ bin₂)
        ≈⟨ homCM _ _ .+-cong (assoc _ _ _) (assoc _ _ _) ⟩
          (bin₁ ∘ ((f ∘ bp₁) ∘ bin₂)) +m (bin₂ ∘ ((g ∘ bp₂) ∘ bin₂))
        ≈⟨ homCM _ _ .+-cong (∘-cong ≈-refl (assoc _ _ _)) (∘-cong ≈-refl (assoc _ _ _)) ⟩
          (bin₁ ∘ (f ∘ (bp₁ ∘ bin₂))) +m (bin₂ ∘ (g ∘ (bp₂ ∘ bin₂)))
        ≈⟨ homCM _ _ .+-cong (∘-cong ≈-refl (∘-cong ≈-refl (bp _ _ .Biproduct.zero-1))) (∘-cong ≈-refl (∘-cong ≈-refl (bp _ _ .Biproduct.id-2))) ⟩
          (bin₁ ∘ (f ∘ εm)) +m (bin₂ ∘ (g ∘ id _))
        ≈⟨ homCM _ _ .+-cong (∘-cong ≈-refl (comp-bilinear-ε₂ _)) (∘-cong ≈-refl id-right) ⟩
          (bin₁ ∘ εm) +m (bin₂ ∘ g)
        ≈⟨ homCM _ _ .+-cong (comp-bilinear-ε₂ _) ≈-refl ⟩
          εm +m (bin₂ ∘ g)
        ≈⟨ homCM _ _ .+-lunit ⟩
          bin₂ ∘ g
        ∎ where open ≈-Reasoning isEquiv

      copair-prod : ∀ {x₁ x₂ y₁ y₂ z}
                      {f₁ : x₂ ⇒ z} {g₁ : y₂ ⇒ z}
                      {f₂ : x₁ ⇒ x₂} {g₂ : y₁ ⇒ y₂} →
                    (bcopair f₁ g₁ ∘ bprod-m f₂ g₂) ≈ bcopair (f₁ ∘ f₂) (g₁ ∘ g₂)
      copair-prod {f₁ = f₁} {g₁ = g₁} {f₂ = f₂} {g₂ = g₂} =
        begin
          bcopair f₁ g₁ ∘ bprod-m f₂ g₂
        ≡⟨⟩
          ((f₁ ∘ bp₁) +m (g₁ ∘ bp₂)) ∘ ((bin₁ ∘ (f₂ ∘ bp₁)) +m (bin₂ ∘ (g₂ ∘ bp₂)))
        ≈⟨ comp-bilinear₁ _ _ _ ⟩
          ((f₁ ∘ bp₁) ∘ ((bin₁ ∘ (f₂ ∘ bp₁)) +m (bin₂ ∘ (g₂ ∘ bp₂)))) +m ((g₁ ∘ bp₂) ∘ ((bin₁ ∘ (f₂ ∘ bp₁)) +m (bin₂ ∘ (g₂ ∘ bp₂))))
        ≈⟨ homCM _ _ .+-cong (comp-bilinear₂ _ _ _) (comp-bilinear₂ _ _ _) ⟩
          (((f₁ ∘ bp₁) ∘ (bin₁ ∘ (f₂ ∘ bp₁))) +m ((f₁ ∘ bp₁) ∘ (bin₂ ∘ (g₂ ∘ bp₂)))) +m (((g₁ ∘ bp₂) ∘ (bin₁ ∘ (f₂ ∘ bp₁))) +m ((g₁ ∘ bp₂) ∘ (bin₂ ∘ (g₂ ∘ bp₂))))
        ≈⟨ homCM _ _ .+-cong (homCM _ _ .+-cong (assoc _ _ _) (assoc _ _ _)) (homCM _ _ .+-cong (assoc _ _ _) (assoc _ _ _)) ⟩
          ((f₁ ∘ (bp₁ ∘ (bin₁ ∘ (f₂ ∘ bp₁)))) +m (f₁ ∘ (bp₁ ∘ (bin₂ ∘ (g₂ ∘ bp₂))))) +m ((g₁ ∘ (bp₂ ∘ (bin₁ ∘ (f₂ ∘ bp₁)))) +m (g₁ ∘ (bp₂ ∘ (bin₂ ∘ (g₂ ∘ bp₂)))))
        ≈˘⟨ homCM _ _ .+-cong (homCM _ _ .+-cong (∘-cong ≈-refl (assoc _ _ _)) (∘-cong ≈-refl (assoc _ _ _))) (homCM _ _ .+-cong (∘-cong ≈-refl (assoc _ _ _)) (∘-cong ≈-refl (assoc _ _ _))) ⟩
          ((f₁ ∘ ((bp₁ ∘ bin₁) ∘ (f₂ ∘ bp₁))) +m (f₁ ∘ ((bp₁ ∘ bin₂) ∘ (g₂ ∘ bp₂)))) +m ((g₁ ∘ ((bp₂ ∘ bin₁) ∘ (f₂ ∘ bp₁))) +m (g₁ ∘ ((bp₂ ∘ bin₂) ∘ (g₂ ∘ bp₂))))
        ≈⟨ homCM _ _ .+-cong (homCM _ _ .+-cong (∘-cong ≈-refl (∘-cong (bp _ _ .Biproduct.id-1) ≈-refl))
                                                (∘-cong ≈-refl (∘-cong (bp _ _ .Biproduct.zero-1) ≈-refl)))
                             (homCM _ _ .+-cong (∘-cong ≈-refl (∘-cong (bp _ _ .Biproduct.zero-2) ≈-refl))
                                                (∘-cong ≈-refl (∘-cong (bp _ _ .Biproduct.id-2) ≈-refl))) ⟩
          ((f₁ ∘ (id _ ∘ (f₂ ∘ bp₁))) +m (f₁ ∘ (εm ∘ (g₂ ∘ bp₂)))) +m ((g₁ ∘ (εm ∘ (f₂ ∘ bp₁))) +m (g₁ ∘ (id _ ∘ (g₂ ∘ bp₂))))
        ≈⟨ homCM _ _ .+-cong (homCM _ _ .+-cong (∘-cong ≈-refl id-left) (∘-cong ≈-refl (comp-bilinear-ε₁ _)))
                             (homCM _ _ .+-cong (∘-cong ≈-refl (comp-bilinear-ε₁ _)) (∘-cong ≈-refl id-left)) ⟩
          ((f₁ ∘ (f₂ ∘ bp₁)) +m (f₁ ∘ εm)) +m ((g₁ ∘ εm) +m (g₁ ∘ (g₂ ∘ bp₂)))
        ≈⟨ homCM _ _ .+-cong (homCM _ _ .+-cong (≈-sym (assoc _ _ _)) (comp-bilinear-ε₂ _))
                             (homCM _ _ .+-cong (comp-bilinear-ε₂ _) (≈-sym (assoc _ _ _))) ⟩
          (((f₁ ∘ f₂) ∘ bp₁) +m εm) +m (εm +m ((g₁ ∘ g₂) ∘ bp₂))
        ≈⟨ homCM _ _ .+-cong +m-runit (homCM _ _ .+-lunit) ⟩
          ((f₁ ∘ f₂) ∘ bp₁) +m ((g₁ ∘ g₂) ∘ bp₂)
        ≡⟨⟩
          bcopair (f₁ ∘ f₂) (g₁ ∘ g₂)
        ∎ where open ≈-Reasoning isEquiv

------------------------------------------------------------------------------
-- Construct biproducts from products on a CMon-enriched category.

module cmon+products→biproducts-impl {o m e} {𝒞 : Category o m e}
         (CM𝒞 : CMonEnriched 𝒞) (P : HasProducts 𝒞)
         (x y : Category.obj 𝒞) where

  open Category 𝒞
  open CMonEnriched CM𝒞
  open CommutativeMonoid
  open IsEquivalence
  open HasProducts P

  pair-ε : ∀ {z} → pair εm εm ≈ εm {z} {prod x y}
  pair-ε =
    begin
      pair εm εm                ≈˘⟨ pair-cong (comp-bilinear-ε₂ p₁) (comp-bilinear-ε₂ p₂) ⟩
      pair (p₁ ∘ εm) (p₂ ∘ εm)  ≈⟨ pair-ext εm ⟩
      εm
    ∎ where open ≈-Reasoning isEquiv

  pair-+ : ∀ {z} (f₁ f₂ : z ⇒ x) (g₁ g₂ : z ⇒ y) →
           (pair f₁ g₁ +m pair f₂ g₂) ≈ pair (f₁ +m f₂) (g₁ +m g₂)
  pair-+ f₁ f₂ g₁ g₂ =
    begin
      pair f₁ g₁ +m pair f₂ g₂
    ≈⟨ ≈-sym (pair-ext _) ⟩
      pair (p₁ ∘ (pair f₁ g₁ +m pair f₂ g₂)) (p₂ ∘ (pair f₁ g₁ +m pair f₂ g₂))
    ≈⟨ pair-cong (comp-bilinear₂ _ _ _) (comp-bilinear₂ _ _ _) ⟩
      pair ((p₁ ∘ pair f₁ g₁) +m (p₁ ∘ pair f₂ g₂)) ((p₂ ∘ pair f₁ g₁) +m (p₂ ∘ pair f₂ g₂))
    ≈⟨ pair-cong (homCM _ _ .+-cong (pair-p₁ _ _) (pair-p₁ _ _))
                  (homCM _ _ .+-cong (pair-p₂ _ _) (pair-p₂ _ _)) ⟩
      pair (f₁ +m f₂) (g₁ +m g₂)
    ∎ where open ≈-Reasoning isEquiv

  in₁ : x ⇒ prod x y
  in₁ = pair (id _) εm

  in₂ : y ⇒ prod x y
  in₂ = pair εm (id _)

  biproduct : Biproduct CM𝒞 x y
  biproduct .Biproduct.prod = prod x y
  biproduct .Biproduct.p₁ = p₁
  biproduct .Biproduct.p₂ = p₂
  biproduct .Biproduct.in₁ = in₁
  biproduct .Biproduct.in₂ = in₂
  biproduct .Biproduct.id-1 = pair-p₁ _ _
  biproduct .Biproduct.id-2 = pair-p₂ _ _
  biproduct .Biproduct.zero-1 = pair-p₁ _ _
  biproduct .Biproduct.zero-2 = pair-p₂ _ _
  biproduct .Biproduct.id-+ =
    begin
      (in₁ ∘ p₁) +m (in₂ ∘ p₂)
    ≈⟨ homCM _ _ .+-cong (pair-natural _ _ _) (pair-natural _ _ _) ⟩
      pair (id _ ∘ p₁) (εm ∘ p₁) +m pair (εm ∘ p₂) (id _ ∘ p₂)
    ≈⟨ homCM _ _ .+-cong (pair-cong id-left (comp-bilinear-ε₁ _))
                          (pair-cong (comp-bilinear-ε₁ _) id-left) ⟩
      pair p₁ εm +m pair εm p₂
    ≈⟨ pair-+ _ _ _ _ ⟩
      pair (p₁ +m εm) (εm +m p₂)
    ≈⟨ pair-cong (isEquiv .trans (homCM _ _ .+-comm) (homCM _ _ .+-lunit))
                  (homCM _ _ .+-lunit) ⟩
      pair p₁ p₂
    ≈⟨ pair-ext0 ⟩
      id _
    ∎ where open ≈-Reasoning isEquiv

cmon+products→biproducts : ∀ {o m e} {𝒞 : Category o m e}
  (CM𝒞 : CMonEnriched 𝒞) (P : HasProducts 𝒞) →
  ∀ x y → Biproduct CM𝒞 x y
cmon+products→biproducts CM𝒞 P x y = cmon+products→biproducts-impl.biproduct CM𝒞 P x y
