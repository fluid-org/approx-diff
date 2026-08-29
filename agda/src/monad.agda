{-# OPTIONS --postfix-projections --prop --safe #-}

open import Level using (suc; _⊔_)
open import categories using (Category)
open import product-category using (pairF; project₁; project₂)
open import functor using (Functor; NatTrans; Id; _∘F_; NatIso; ≃-NatTrans; id; right-unit)
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

------------------------------------------------------------------------------

IdentityMonad : ∀ {o m e} (𝒞 : Category o m e) → Monad 𝒞
IdentityMonad 𝒞 .Monad.funct = Id
IdentityMonad 𝒞 .Monad.unit = id _
IdentityMonad 𝒞 .Monad.join = right-unit _

module _ {o₁ m₁ e₁ o₂ m₂ e₂} {𝒞 : Category o₁ m₁ e₁} {𝒟 : Category o₂ m₂ e₂} where

  private
    module 𝒟 = Category 𝒟

  preserve-identity-monad : (F : Functor 𝒞 𝒟) → preserve-monad F (IdentityMonad 𝒞) (IdentityMonad 𝒟)
  preserve-identity-monad F .preserve-monad.iso .NatIso.transform .NatTrans.transf x = 𝒟.id _
  preserve-identity-monad F .preserve-monad.iso .NatIso.transform .NatTrans.natural f = 𝒟.id-swap-sym
  preserve-identity-monad F .preserve-monad.iso .NatIso.transf-iso x .Category.IsIso.inverse = 𝒟.id _
  preserve-identity-monad F .preserve-monad.iso .NatIso.transf-iso x .Category.IsIso.f∘inverse≈id = 𝒟.id-left
  preserve-identity-monad F .preserve-monad.iso .NatIso.transf-iso x .Category.IsIso.inverse∘f≈id = 𝒟.id-left
  preserve-identity-monad F .preserve-monad.preserve-unit = 𝒟.≈-trans 𝒟.id-left (F .Functor.fmor-id)
  preserve-identity-monad F .preserve-monad.preserve-join = 𝒟.≈-trans (𝒟.∘-cong 𝒟.≈-refl (F .Functor.fmor-id)) (𝒟.≈-sym 𝒟.id-left)

open categories using (HasCoproducts)
open import finite-coproduct-functor using (preserve-chosen-coproducts)

module _ {o₁ m₁ e₁} {𝒞 : Category o₁ m₁ e₁} (𝒞CP : HasCoproducts 𝒞) where

  private
    module 𝒞CP = HasCoproducts 𝒞CP
    module 𝒞 = Category 𝒞

  Identity-monad-preserve-coproducts : preserve-chosen-coproducts (IdentityMonad 𝒞 .Monad.funct) 𝒞CP 𝒞CP
  Identity-monad-preserve-coproducts .Category.IsIso.inverse = 𝒞.id _
  Identity-monad-preserve-coproducts .Category.IsIso.f∘inverse≈id =
    𝒞.≈-trans 𝒞.id-right 𝒞CP.copair-ext0
  Identity-monad-preserve-coproducts .Category.IsIso.inverse∘f≈id =
    𝒞.≈-trans 𝒞.id-left 𝒞CP.copair-ext0
