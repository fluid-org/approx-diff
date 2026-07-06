{-# OPTIONS --prop --postfix-projections --safe #-}

module monoidal-product where

open import Level using (_⊔_)
open import prop using (_,_)
open import Data.Product using (_,_; _×_)
open import prop-setoid using (module ≈-Reasoning)
open import categories using (Category)
open import product-category using (product)
open import functor using (Functor)

-- FIXME: derive naturality of the inverses:
--
-- Assume G f ∘ α ≈ α ∘ F f
--
--   α⁻¹ ∘ G f
-- = α⁻¹ ∘ G f ∘ α ∘ α⁻¹
-- = α⁻¹ ∘ α ∘ F f ∘ α⁻¹
-- = F f ∘ α⁻¹

record MonoidalProduct {o m e} (𝒞 : Category o m e) : Set (o ⊔ m ⊔ e) where
  open Category 𝒞
  field
    I⊗  : obj

    -- Functor (𝒞 ×C 𝒞) 𝒞
    _⊗_ : obj → obj → obj
    _⊗m_ : ∀ {x₁ x₂ y₁ y₂} → x₁ ⇒ x₂ → y₁ ⇒ y₂ → (x₁ ⊗ y₁) ⇒ (x₂ ⊗ y₂)
    ⊗m-cong : ∀ {x₁ x₂ y₁ y₂} {f₁ f₂ : x₁ ⇒ x₂} {g₁ g₂ : y₁ ⇒ y₂} → f₁ ≈ f₂ → g₁ ≈ g₂ → (f₁ ⊗m g₁) ≈ (f₂ ⊗m g₂)
    ⊗m-id : ∀ {x y} → (id x ⊗m id y) ≈ id (x ⊗ y)
    ⊗m-comp : ∀ {x₁ x₂ y₁ y₂ z₁ z₂}
              (f₁ : y₁ ⇒ z₁) (f₂ : y₂ ⇒ z₂) (g₁ : x₁ ⇒ y₁) (g₂ : x₂ ⇒ y₂) →
              ((f₁ ∘ g₁) ⊗m (f₂ ∘ g₂)) ≈ ((f₁ ⊗m f₂) ∘ (g₁ ⊗m g₂))

    -- associativity
    ⊗-assoc : ∀ {x y z} → ((x ⊗ y) ⊗ z) ⇒ (x ⊗ (y ⊗ z))
    ⊗-assoc-natural : ∀ {x₁ x₂ y₁ y₂ z₁ z₂} (f : x₁ ⇒ x₂) (g : y₁ ⇒ y₂) (h : z₁ ⇒ z₂) →
      ((f ⊗m (g ⊗m h)) ∘ ⊗-assoc) ≈ (⊗-assoc ∘ ((f ⊗m g) ⊗m h))
    ⊗-assoc⁻¹ : ∀ {x y z} → (x ⊗ (y ⊗ z)) ⇒ ((x ⊗ y) ⊗ z)
    ⊗-assoc-iso1 : ∀ {x y z} → (⊗-assoc ∘ ⊗-assoc⁻¹) ≈ id (x ⊗ (y ⊗ z))
    ⊗-assoc-iso2 : ∀ {x y z} → (⊗-assoc⁻¹ ∘ ⊗-assoc) ≈ id ((x ⊗ y) ⊗ z)

    -- left unit
    ⊗-lunit : ∀ {x} → (I⊗ ⊗ x) ⇒ x
    ⊗-lunit⁻¹ : ∀ {x} → x ⇒ (I⊗ ⊗ x)
    ⊗-lunit-natural : ∀ {x₁ x₂} (f : x₁ ⇒ x₂) → (f ∘ ⊗-lunit) ≈ (⊗-lunit ∘ (id _ ⊗m f))
    ⊗-lunit-iso1 : ∀ {x} → (⊗-lunit ∘ ⊗-lunit⁻¹) ≈ id x
    ⊗-lunit-iso2 : ∀ {x} → (⊗-lunit⁻¹ ∘ ⊗-lunit) ≈ id (I⊗ ⊗ x)

    -- right unit
    ⊗-runit : ∀ {x} → (x ⊗ I⊗) ⇒ x
    ⊗-runit⁻¹ : ∀ {x} → x ⇒ (x ⊗ I⊗)
    ⊗-runit-natural : ∀ {x₁ x₂} (f : x₁ ⇒ x₂) → (f ∘ ⊗-runit) ≈ (⊗-runit ∘ (f ⊗m id _))
    ⊗-runit-iso1 : ∀ {x} → (⊗-runit ∘ ⊗-runit⁻¹) ≈ id x
    ⊗-runit-iso2 : ∀ {x} → (⊗-runit⁻¹ ∘ ⊗-runit) ≈ id (x ⊗ I⊗)

    pentagon : ∀ {w x y z} →
               (⊗-assoc ∘ ⊗-assoc {w ⊗ x} {y} {z})
               ≈ (((id w ⊗m ⊗-assoc) ∘ ⊗-assoc) ∘ (⊗-assoc ⊗m id z))

    triangle : ∀ {x y} → ((id x ⊗m ⊗-lunit) ∘ ⊗-assoc) ≈ (⊗-runit ⊗m id y)

  open Functor

  ⊗-functor : Functor (product 𝒞 𝒞) 𝒞
  ⊗-functor .fobj (x , y) = x ⊗ y
  ⊗-functor .fmor (f , g) = f ⊗m g
  ⊗-functor .fmor-cong (f₁≈f₂ , g₁≈g₂) = ⊗m-cong f₁≈f₂ g₁≈g₂
  ⊗-functor .fmor-id = ⊗m-id
  ⊗-functor .fmor-comp (f₁ , g₁) (f₂ , g₂) = ⊗m-comp f₁ g₁ f₂ g₂


  ⊗-runit⁻¹-natural : ∀ {x₁ x₂} (f : x₁ ⇒ x₂) → (⊗-runit⁻¹ ∘ f) ≈ ((f ⊗m id _) ∘ ⊗-runit⁻¹)
  ⊗-runit⁻¹-natural f = begin
      ⊗-runit⁻¹ ∘ f
    ≈˘⟨ ∘-cong ≈-refl id-right ⟩
      ⊗-runit⁻¹ ∘ (f ∘ id _)
    ≈˘⟨ ∘-cong ≈-refl (∘-cong ≈-refl ⊗-runit-iso1) ⟩
      ⊗-runit⁻¹ ∘ (f ∘ (⊗-runit ∘ ⊗-runit⁻¹))
    ≈˘⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
      ⊗-runit⁻¹ ∘ ((f ∘ ⊗-runit) ∘ ⊗-runit⁻¹)
    ≈⟨ ∘-cong ≈-refl (∘-cong (⊗-runit-natural f) ≈-refl) ⟩
      ⊗-runit⁻¹ ∘ ((⊗-runit ∘ (f ⊗m id _)) ∘ ⊗-runit⁻¹)
    ≈⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
      ⊗-runit⁻¹ ∘ (⊗-runit ∘ ((f ⊗m id _) ∘ ⊗-runit⁻¹))
    ≈˘⟨ assoc _ _ _ ⟩
      (⊗-runit⁻¹ ∘ ⊗-runit) ∘ ((f ⊗m id _) ∘ ⊗-runit⁻¹)
    ≈⟨ ∘-cong ⊗-runit-iso2 ≈-refl ⟩
      id _ ∘ ((f ⊗m id _) ∘ ⊗-runit⁻¹)
    ≈⟨ id-left ⟩
      (f ⊗m id _) ∘ ⊗-runit⁻¹
    ∎
    where open ≈-Reasoning isEquiv

  assoc-runit⁻¹ : ∀ {x y} → (⊗-assoc ∘ (⊗-runit⁻¹ ⊗m id y)) ≈ (id x ⊗m ⊗-lunit⁻¹)
  assoc-runit⁻¹ = begin
      ⊗-assoc ∘ (⊗-runit⁻¹ ⊗m id _)
    ≈˘⟨ ∘-cong id-left ≈-refl ⟩
      (id _ ∘ ⊗-assoc) ∘ (⊗-runit⁻¹ ⊗m id _)
    ≈˘⟨ ∘-cong (∘-cong ⊗m-id ≈-refl) ≈-refl ⟩
      ((id _ ⊗m id _) ∘ ⊗-assoc) ∘ (⊗-runit⁻¹ ⊗m id _)
    ≈˘⟨ ∘-cong (∘-cong (⊗m-cong id-left ⊗-lunit-iso2) ≈-refl) ≈-refl ⟩
      (((id _ ∘ id _) ⊗m (⊗-lunit⁻¹ ∘ ⊗-lunit)) ∘ ⊗-assoc) ∘ (⊗-runit⁻¹ ⊗m id _)
    ≈⟨ ∘-cong (∘-cong (⊗m-comp _ _ _ _) ≈-refl) ≈-refl ⟩
      (((id _ ⊗m ⊗-lunit⁻¹) ∘ (id _ ⊗m ⊗-lunit)) ∘ ⊗-assoc) ∘ (⊗-runit⁻¹ ⊗m id _)
    ≈⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
      ((id _ ⊗m ⊗-lunit⁻¹) ∘ ((id _ ⊗m ⊗-lunit) ∘ ⊗-assoc)) ∘ (⊗-runit⁻¹ ⊗m id _)
    ≈⟨ assoc _ _ _ ⟩
      (id _ ⊗m ⊗-lunit⁻¹) ∘ (((id _ ⊗m ⊗-lunit) ∘ ⊗-assoc) ∘ (⊗-runit⁻¹ ⊗m id _))
    ≈⟨ ∘-cong ≈-refl (∘-cong triangle ≈-refl) ⟩
      (id _ ⊗m ⊗-lunit⁻¹) ∘ ((⊗-runit ⊗m id _) ∘ (⊗-runit⁻¹ ⊗m id _))
    ≈˘⟨ ∘-cong ≈-refl (⊗m-comp _ _ _ _) ⟩
      (id _ ⊗m ⊗-lunit⁻¹) ∘ ((⊗-runit ∘ ⊗-runit⁻¹) ⊗m (id _ ∘ id _))
    ≈⟨ ∘-cong ≈-refl (⊗m-cong ⊗-runit-iso1 id-left) ⟩
      (id _ ⊗m ⊗-lunit⁻¹) ∘ (id _ ⊗m id _)
    ≈⟨ ∘-cong ≈-refl ⊗m-id ⟩
      (id _ ⊗m ⊗-lunit⁻¹) ∘ id _
    ≈⟨ id-right ⟩
      id _ ⊗m ⊗-lunit⁻¹
    ∎
    where open ≈-Reasoning isEquiv

  -- (x ⊗ y) -> (x ⊗ y) ⊗ I -> x ⊗ (y ⊗ I)
  -- assoc-runit⁻¹-2 : ∀ {x y} → (id x ⊗m ⊗-runit⁻¹ {y}) ≈ (⊗-assoc ∘ ⊗-runit⁻¹ {x ⊗ y})
  -- assoc-runit⁻¹-2 = begin
  --     id _ ⊗m ⊗-runit⁻¹
  --   ≈⟨ {!!} ⟩
  --     ⊗-assoc ∘ ⊗-runit⁻¹
  --   ∎
  --   where open ≈-Reasoning isEquiv

record SymmetricMonoidal {o m e} (𝒞 : Category o m e) : Set (o ⊔ m ⊔ e) where
  open Category 𝒞

  field
    monoidal : MonoidalProduct 𝒞

  open MonoidalProduct monoidal public
  field
    ⊗-symmetry : ∀ {x y} → (x ⊗ y) ⇒ (y ⊗ x)
    ⊗-symmetry-natural : ∀ {x₁ x₂ y₁ y₂} (f : x₁ ⇒ x₂) (g : y₁ ⇒ y₂) →
            ((g ⊗m f) ∘ ⊗-symmetry) ≈ (⊗-symmetry ∘ (f ⊗m g))
    ⊗-symmetry-iso : ∀ {x y} → (⊗-symmetry ∘ ⊗-symmetry) ≈ id (x ⊗ y)
    ⊗-symmetry-triangle : ∀ {x} → (⊗-runit ∘ ⊗-symmetry {I⊗} {x}) ≈ ⊗-lunit
    ⊗-symmetry-hexagon : ∀ {x y z} →
      (((id y ⊗m ⊗-symmetry) ∘ ⊗-assoc {y} {x} {z}) ∘ (⊗-symmetry ⊗m id z))
      ≈ ((⊗-assoc {y} {z} {x} ∘ ⊗-symmetry) ∘ ⊗-assoc {x} {y} {z})

-- TODO:
--  0. Lots of derived equations for monoidal categories.
--  1. Monoidal product on 𝒞 gives a monoidal product on 𝒞.opposite.
--  2. Monoidal Functors.

open import functor using (Functor)

module _ {o₁ m₁ e₁ o₂ m₂ e₂}
         {𝒞 : Category o₁ m₁ e₁} (𝒞M : MonoidalProduct 𝒞)
         {𝒟 : Category o₂ m₂ e₂} (𝒟M : MonoidalProduct 𝒟)
         (F : Functor 𝒞 𝒟)
  where

  private
    module 𝒞 = Category 𝒞
    module 𝒞M = MonoidalProduct 𝒞M
    module 𝒟 = Category 𝒟
    module 𝒟M = MonoidalProduct 𝒟M
    module F = Functor F

  record LaxMonoidalFunctor : Set (o₁ ⊔ m₁ ⊔ m₂ ⊔ e₂) where
    field
      mult : ∀ {X Y} → (F.fobj X 𝒟M.⊗ F.fobj Y) 𝒟.⇒ F.fobj (X 𝒞M.⊗ Y)
      unit : 𝒟M.I⊗ 𝒟.⇒ F.fobj 𝒞M.I⊗

      -- naturality of mult
      mult-natural : ∀ {x₁ x₂ y₁ y₂} (f : x₁ 𝒞.⇒ x₂) (g : y₁ 𝒞.⇒ y₂) →
                     (mult 𝒟.∘ (F.fmor f 𝒟M.⊗m F.fmor g)) 𝒟.≈ (F.fmor (f 𝒞M.⊗m g) 𝒟.∘ mult)
      -- assoc, left-unit, right-unit
      mult-assoc : ∀ {x y z} →
        (mult 𝒟.∘ ((𝒟.id _ 𝒟M.⊗m mult) 𝒟.∘ 𝒟M.⊗-assoc {F.fobj x} {F.fobj y} {F.fobj z}))
        𝒟.≈ (F.fmor 𝒞M.⊗-assoc 𝒟.∘ (mult 𝒟.∘ (mult 𝒟M.⊗m 𝒟.id _)))

      mult-lunit : ∀ {x} →
              (mult {𝒞M.I⊗}{x} 𝒟.∘ (unit 𝒟M.⊗m 𝒟.id _))
         𝒟.≈ (F.fmor 𝒞M.⊗-lunit⁻¹ 𝒟.∘ 𝒟M.⊗-lunit)

      mult-runit : ∀ {x} →
              (mult {x}{𝒞M.I⊗} 𝒟.∘ (𝒟.id _ 𝒟M.⊗m unit))
         𝒟.≈ (F.fmor 𝒞M.⊗-runit⁻¹ 𝒟.∘ 𝒟M.⊗-runit)

  -- a.k.a. strong monoidal
  record MonoidalFunctor : Set (o₁ ⊔ m₁ ⊔ m₂ ⊔ e₂) where
    field
      lax-monoidal : LaxMonoidalFunctor
    open LaxMonoidalFunctor lax-monoidal public
    field
      mult-is-iso : ∀ {X Y} → 𝒟.IsIso (mult {X} {Y})
      unit-is-iso : 𝒟.IsIso unit

-- FIXME: and symmetric versions
