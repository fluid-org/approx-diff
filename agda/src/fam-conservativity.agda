{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- The parameters the Grothendieck logical relations need, at the level of
-- families: the change of base between family categories is faithful and
-- preserves the set-indexed coproducts when it does so on fibres, because
-- families keep their index setoids, and the identity monad preserves them
-- outright. With these the logical relations construction applies to the
-- categories of families themselves, so that a stage's coproduct
-- decomposition can split a family into its fibres.
------------------------------------------------------------------------------

open import Level using (Level; _⊔_)
open import Data.Product using (Σ; _,_)
open import prop using (Prf; ⟪_⟫; ∃; ∃ₛ; _,_)
open import prop-setoid as PS using (Setoid; IsEquivalence)
open import categories using (Category; setoid→category)
open import functor using (Functor; HasColimits; Colimit; NatTrans; ≃-NatTrans; Id; _∘F_)
import functor
open import indexed-family using (Fam; _⇒f_; _≃f_)
open import monad using (Monad; IdentityMonad)
import fam
import fam-functor

module fam-conservativity {o₁ m₁ e₁ o₂ m₂ e₂} (os es : Level)
  {𝒞 : Category o₁ m₁ e₁} {𝒟 : Category o₂ m₂ e₂} (F : Functor 𝒞 𝒟) where

private
  module 𝒞C = Category 𝒞
  module 𝒟C = Category 𝒟
  module Fam𝒞 = fam.CategoryOfFamilies os es 𝒞
  module Fam𝒟 = fam.CategoryOfFamilies os es 𝒟

open Functor
open Fam
open _⇒f_
open Colimit
open NatTrans
open fam.CategoryOfFamilies.Obj
open fam.CategoryOfFamilies.Mor
open fam.CategoryOfFamilies._≃_

FamF : Functor Fam𝒞.cat Fam𝒟.cat
FamF = fam-functor.FamF os es F

-- Faithfulness passes to families: the index maps are carried unchanged, so
-- only the fibre maps have to be reflected.
FamF-faithful : (∀ {a b} {g₁ g₂ : a 𝒞C.⇒ b} → F .fmor g₁ 𝒟C.≈ F .fmor g₂ → g₁ 𝒞C.≈ g₂) →
                ∀ {a b} {g₁ g₂ : Fam𝒞.Mor a b} →
                Fam𝒟.cat .Category._≈_ (FamF .fmor g₁) (FamF .fmor g₂) →
                Fam𝒞.cat .Category._≈_ g₁ g₂
FamF-faithful faithful e .idxf-eq = e .idxf-eq
FamF-faithful faithful {a} {b} {g₁} {g₂} e .famf-eq ._≃f_.transf-eq {x} =
  faithful
    (𝒟C.≈-trans (F .fmor-comp _ _) (e .famf-eq ._≃f_.transf-eq {x}))

-- The identity monad's functor leaves a diagram alone, so it preserves the
-- colimits on the nose.
Id-preserves-colimits :
  ∀ {o m e} {𝒦 : Category o m e}
    (DC : ∀ (S : Setoid os es) → HasColimits (setoid→category S) 𝒦)
    (S : Setoid os es) (D : Functor (setoid→category S) 𝒦) →
  ∃ₛ (Category.Iso 𝒦 (DC S (Monad.funct (IdentityMonad 𝒦) ∘F D) .apex)
                     (Monad.funct (IdentityMonad 𝒦) .fobj (DC S D .apex)))
     (λ i → ∀ s → Category._≈_ 𝒦
                    (Category._∘_ 𝒦 (Category.Iso.fwd i)
                      (DC S (Monad.funct (IdentityMonad 𝒦) ∘F D) .cocone .transf s))
                    (Monad.funct (IdentityMonad 𝒦) .fmor (DC S D .cocone .transf s)))
Id-preserves-colimits {𝒦 = 𝒦} DC S D = iso , coh
  where
    module K = Category 𝒦
    CI = DC S (Monad.funct (IdentityMonad 𝒦) ∘F D)
    CD = DC S D

    -- The two diagrams agree on objects and morphisms, so each cocone is a
    -- cocone for the other.
    coI : NatTrans (Monad.funct (IdentityMonad 𝒦) ∘F D)
                   (functor.constF (setoid→category S) (CD .apex))
    coI .transf s = CD .cocone .transf s
    coI .natural f = CD .cocone .natural f

    coD : NatTrans D (functor.constF (setoid→category S) (CI .apex))
    coD .transf s = CI .cocone .transf s
    coD .natural f = CI .cocone .natural f

    fwd = CI .colambda (CD .apex) coI
    bwd = CD .colambda (CI .apex) coD

    fwd-leg : ∀ s → (fwd K.∘ CI .cocone .transf s) K.≈ CD .cocone .transf s
    fwd-leg s = CI .colambda-coeval (CD .apex) coI .≃-NatTrans.transf-eq s

    bwd-leg : ∀ s → (bwd K.∘ CD .cocone .transf s) K.≈ CI .cocone .transf s
    bwd-leg s = CD .colambda-coeval (CI .apex) coD .≃-NatTrans.transf-eq s

    iso : K.Iso (CI .apex) (CD .apex)
    iso .K.Iso.fwd = fwd
    iso .K.Iso.bwd = bwd
    iso .K.Iso.fwd∘bwd≈id =
      functor.colambda-unique (CD .isColimit)
        (λ s → K.≈-trans (K.assoc _ _ _)
               (K.≈-trans (K.∘-cong K.≈-refl (bwd-leg s))
               (K.≈-trans (fwd-leg s) (K.≈-sym K.id-left))))
    iso .K.Iso.bwd∘fwd≈id =
      functor.colambda-unique (CI .isColimit)
        (λ s → K.≈-trans (K.assoc _ _ _)
               (K.≈-trans (K.∘-cong K.≈-refl (fwd-leg s))
               (K.≈-trans (bwd-leg s) (K.≈-sym K.id-left))))

    coh : ∀ s → (fwd K.∘ CI .cocone .transf s) K.≈ CD .cocone .transf s
    coh = fwd-leg
