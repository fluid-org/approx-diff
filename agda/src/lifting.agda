{-# OPTIONS --prop --postfix-projections --safe #-}

-- What the interpretation needs of a lifting: an object with a root, an injection of the payload
-- under it, and the assembly of a map out of it from a constant and a linear part, with the constant
-- recovered by the root and every map its own assembly. Functoriality is not among the requirements,
-- since the recursion only ever splits a map out of a lifted object and rebuilds it.
open import Level using (_⊔_)
open import categories using (Category)
open import cmon-enriched using (CMonEnriched)

module lifting where

record Lifting {o m e} {𝒞 : Category o m e} (CM : CMonEnriched 𝒞) (𝟙 : Category.obj 𝒞) :
    Set (o ⊔ m ⊔ e) where
  open Category 𝒞
  open CMonEnriched CM
  field
    L      : obj → obj
    root   : ∀ {P} → 𝟙 ⇒ L P
    inj    : ∀ {P} → P ⇒ L P
    affine : ∀ {P C} → 𝟙 ⇒ C → P ⇒ C → L P ⇒ C

    affine-cong : ∀ {P C} {c c' : 𝟙 ⇒ C} {M M' : P ⇒ C} →
                  c ≈ c' → M ≈ M' → affine c M ≈ affine c' M'
    -- The root recovers the constant.
    affine-root : ∀ {P C} (c : 𝟙 ⇒ C) (M : P ⇒ C) → (affine c M ∘ root) ≈ c
    -- Every map out of a lifted object is assembled from its own two restrictions.
    affine-η    : ∀ {P C} (h : L P ⇒ C) → affine (h ∘ root) (h ∘ inj) ≈ h

    -- The action on morphisms, which transport along bisimilarity of trees needs. The root is
    -- natural for it; the injection is not, which is why there is no unit and no strength.
    Lmap      : ∀ {P Q} → P ⇒ Q → L P ⇒ L Q
    Lmap-cong : ∀ {P Q} {f g : P ⇒ Q} → f ≈ g → Lmap f ≈ Lmap g
    Lmap-id   : ∀ {P} → Lmap (id P) ≈ id (L P)
    Lmap-comp : ∀ {P Q R} (g : Q ⇒ R) (f : P ⇒ Q) → Lmap (g ∘ f) ≈ (Lmap g ∘ Lmap f)
    Lmap-root : ∀ {P Q} (f : P ⇒ Q) → (Lmap f ∘ root) ≈ root

    -- The support: what an object contributes to a constant. Restricting an assembly along the
    -- injection joins the constant in over the support; the injection and the support are natural
    -- only at isomorphisms, which is all the transports along bisimilarity need.
    spt         : ∀ {P} → P ⇒ 𝟙
    affine-inj  : ∀ {P C} (c : 𝟙 ⇒ C) (M : P ⇒ C) →
                  (affine c M ∘ inj) ≈ ((c ∘ spt) +m M)
    Lmap-inj    : ∀ {P Q} {f : P ⇒ Q} {g : Q ⇒ P} →
                  (f ∘ g) ≈ id Q → (g ∘ f) ≈ id P → (Lmap f ∘ inj) ≈ (inj ∘ f)
    spt-natural : ∀ {P Q} {f : P ⇒ Q} {g : Q ⇒ P} →
                  (f ∘ g) ≈ id Q → (g ∘ f) ≈ id P → (spt ∘ f) ≈ spt

  -- Two maps out of a lifted object agreeing on the root and on the payload are equal, which is the
  -- uniqueness principle the initial-algebra laws use.
  lifting-ext : ∀ {P C} (h k : L P ⇒ C) →
                (h ∘ root) ≈ (k ∘ root) → (h ∘ inj) ≈ (k ∘ inj) → h ≈ k
  lifting-ext h k er ei =
    ≈-trans (≈-sym (affine-η h)) (≈-trans (affine-cong er ei) (affine-η k))

