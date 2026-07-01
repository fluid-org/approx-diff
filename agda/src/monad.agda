{-# OPTIONS --postfix-projections --prop --safe #-}

open import Level using (suc; _⊔_)
open import categories using (Category)
open import product-category using (pairF; project₁; project₂)
open import functor using (Functor; NatTrans; Id; _∘F_; NatIso; ≃-NatTrans)
open import monoidal-product using (MonoidalProduct)

module monad where

record Monad {o m e} (𝒞 : Category o m e) : Set (o ⊔ m ⊔ e) where
  field
    funct : Functor 𝒞 𝒞
    unit  : NatTrans Id funct
    join  : NatTrans (funct ∘F funct) funct

    -- FIXME: laws

record MonadFunctor {o₁ m₁ e₁ o₂ m₂ e₂}
            {𝒞 : Category o₁ m₁ e₁}
            {𝒟 : Category o₂ m₂ e₂}
            (F : Functor 𝒞 𝒟)
            (𝒞M : Monad 𝒞) (𝒟M : Monad 𝒟)
       : Set (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂) where
  private
    module 𝒟 = Category 𝒟
    module 𝒞M = Monad 𝒞M
    module 𝒟M = Monad 𝒟M
  field
    transform : NatTrans (𝒟M.funct ∘F F) (F ∘F 𝒞M.funct)

  open Functor
  open NatTrans

  field
    preserve-unit : ∀ {x} → transform .transf x 𝒟.∘ 𝒟M.unit .transf _ 𝒟.≈ F .fmor (𝒞M.unit .transf _)
    preserve-join : ∀ {x} → transform .transf _ 𝒟.∘ 𝒟M.join .transf _ 𝒟.≈ F .fmor (𝒞M.join .transf _) 𝒟.∘ (transform .transf _ 𝒟.∘ 𝒟M.funct .fmor (transform .transf x))

-- FIXME: this is a "Strong Monad Functor", but that terminology
-- conflicts with the other kind of strength.
record preserve-monad {o₁ m₁ e₁ o₂ m₂ e₂}
            {𝒞 : Category o₁ m₁ e₁}
            {𝒟 : Category o₂ m₂ e₂}
            (F : Functor 𝒞 𝒟)
            (𝒞M : Monad 𝒞) (𝒟M : Monad 𝒟)
       : Set (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂) where
  private
    module 𝒟 = Category 𝒟
    module 𝒞M = Monad 𝒞M
    module 𝒟M = Monad 𝒟M
  field
    iso     : NatIso (F ∘F 𝒞M.funct) (𝒟M.funct ∘F F)

  open NatIso iso public
  open Functor
  open NatTrans

  field
    preserve-unit : ∀ {x} → transform .transf x 𝒟.∘ F .fmor (𝒞M.unit .transf x)
                       𝒟.≈ 𝒟M.unit .transf _
    preserve-join : ∀ {x} → transform .transf x 𝒟.∘ F .fmor (𝒞M.join .transf x)
                       𝒟.≈ 𝒟M.join .transf _ 𝒟.∘ (𝒟M.funct .fmor (transform .transf _) 𝒟.∘ transform .transf _)

record StrongMonad {o m e} (𝒞 : Category o m e) (𝒞⊗ : MonoidalProduct 𝒞) : Set (o ⊔ m ⊔ e) where
  field
    monad : Monad 𝒞
  open Monad monad public
  open MonoidalProduct 𝒞⊗
  field
    strength : NatTrans (⊗-functor ∘F pairF (funct ∘F project₁) project₂)
                        (funct ∘F ⊗-functor)

    -- FIXME: laws
