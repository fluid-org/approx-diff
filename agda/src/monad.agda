{-# OPTIONS --postfix-projections --prop --safe #-}

open import Level using (suc; _⊔_)
open import categories using (Category)
open import product-category using (pairF; project₁; project₂)
open import functor using (Functor; NatTrans; Id; _∘F_)
open import monoidal-product using (MonoidalProduct)

module monad {o m e} (𝒞 : Category o m e) where

record Monad : Set (o ⊔ m ⊔ e) where
  field
    funct : Functor 𝒞 𝒞
    unit  : NatTrans Id funct
    join  : NatTrans (funct ∘F funct) funct

    -- FIXME: laws

record StrongMonad (𝒞⊗ : MonoidalProduct 𝒞) : Set (o ⊔ m ⊔ e) where
  field
    monad : Monad
  open Monad monad public
  open MonoidalProduct 𝒞⊗
  field
    strength : NatTrans (⊗-functor ∘F pairF (funct ∘F project₁) project₂)
                        (funct ∘F ⊗-functor)

    -- FIXME: laws
