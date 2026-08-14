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

open import Level using (Level)
open import Data.Product using (_,_)
open import prop using (Prf; ⟪_⟫; ∃; ∃ₛ; _,_)
open import prop-setoid as PS using (Setoid)
open import categories using (Category; setoid→category)
open import functor using (Functor; HasColimits; Colimit; NatTrans; ≃-NatTrans; _∘F_)
import functor
open import indexed-family using (Fam; _⇒f_; _≃f_)
open import monad using (Monad; IdentityMonad)
import fam
import fam-functor

module fam-conservativity {o₁ m₁ e₁ o₂ m₂ e₂} (os es : Level)
  {𝒞 : Category o₁ m₁ e₁} {𝒟 : Category o₂ m₂ e₂} (F : Functor 𝒞 𝒟) where

private
  module 𝒞 = Category 𝒞
  module 𝒟 = Category 𝒟
  module Fam𝒞 = fam.CategoryOfFamilies os es 𝒞
  module Fam𝒟 = fam.CategoryOfFamilies os es 𝒟
  module Fam𝒞C = Category Fam𝒞.cat
  module Fam𝒟C = Category Fam𝒟.cat

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
FamF-faithful : (∀ {a b} {g₁ g₂ : a 𝒞.⇒ b} → F .fmor g₁ 𝒟.≈ F .fmor g₂ → g₁ 𝒞.≈ g₂) →
                ∀ {a b} {g₁ g₂ : Fam𝒞.Mor a b} →
                Fam𝒟C._≈_ (FamF .fmor g₁) (FamF .fmor g₂) →
                Fam𝒞C._≈_ g₁ g₂
FamF-faithful faithful e .idxf-eq = e .idxf-eq
FamF-faithful faithful {a} {b} {g₁} {g₂} e .famf-eq ._≃f_.transf-eq {x} =
  faithful
    (𝒟.≈-trans (F .fmor-comp _ _) (e .famf-eq ._≃f_.transf-eq {x}))

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

-- The change of base preserves the set-indexed coproducts of families: both
-- sides have the same indexes and the same fibres, and differ only in how a
-- transport is split, which the functor's composition law reconciles.
module _ (S : Setoid os es) (D : Functor (setoid→category S) Fam𝒞.cat) where

  private
    CI = Fam𝒟.bigCoproducts S (FamF ∘F D)
    CD = Fam𝒞.bigCoproducts S D

  FamF-∐-fwd : Fam𝒟.Mor (CI .apex) (FamF .fobj (CD .apex))
  FamF-∐-fwd .idxf .PS._⇒_.func i = i
  FamF-∐-fwd .idxf .PS._⇒_.func-resp-≈ e = e
  FamF-∐-fwd .famf ._⇒f_.transf _ = 𝒟.id _
  FamF-∐-fwd .famf ._⇒f_.natural _ =
    𝒟.≈-trans 𝒟.id-left
      (𝒟.≈-trans (𝒟.≈-sym (F .fmor-comp _ _)) (𝒟.≈-sym 𝒟.id-right))

  FamF-∐-bwd : Fam𝒟.Mor (FamF .fobj (CD .apex)) (CI .apex)
  FamF-∐-bwd .idxf .PS._⇒_.func i = i
  FamF-∐-bwd .idxf .PS._⇒_.func-resp-≈ e = e
  FamF-∐-bwd .famf ._⇒f_.transf _ = 𝒟.id _
  FamF-∐-bwd .famf ._⇒f_.natural _ =
    𝒟.≈-trans 𝒟.id-left
      (𝒟.≈-trans (F .fmor-comp _ _) (𝒟.≈-sym 𝒟.id-right))

  FamF-∐-iso : Fam𝒟C.Iso (CI .apex) (FamF .fobj (CD .apex))
  FamF-∐-iso .Fam𝒟C.Iso.fwd = FamF-∐-fwd
  FamF-∐-iso .Fam𝒟C.Iso.bwd = FamF-∐-bwd
  FamF-∐-iso .Fam𝒟C.Iso.fwd∘bwd≈id .idxf-eq .PS._≃m_.func-eq e = e
  FamF-∐-iso .Fam𝒟C.Iso.fwd∘bwd≈id .famf-eq ._≃f_.transf-eq =
    𝒟.≈-trans (𝒟.∘-cong (𝒟.≈-trans (F .fmor-cong (CD .apex .fam .refl*)) (F .fmor-id))
                          (𝒟.≈-trans 𝒟.id-left 𝒟.id-left))
               𝒟.id-left
  FamF-∐-iso .Fam𝒟C.Iso.bwd∘fwd≈id .idxf-eq .PS._≃m_.func-eq e = e
  FamF-∐-iso .Fam𝒟C.Iso.bwd∘fwd≈id .famf-eq ._≃f_.transf-eq =
    𝒟.≈-trans (𝒟.∘-cong (CI .apex .fam .refl*)
                          (𝒟.≈-trans 𝒟.id-left 𝒟.id-left))
               𝒟.id-left

  FamF-∐-leg : ∀ s → Fam𝒟C._≈_
                       (Fam𝒟C._∘_ FamF-∐-fwd (CI .cocone .transf s))
                       (FamF .fmor (CD .cocone .transf s))
  FamF-∐-leg s .idxf-eq .PS._≃m_.func-eq e =
    S .Setoid.refl , D .fmor-id .idxf-eq .PS._≃m_.func-eq e
  FamF-∐-leg s .famf-eq ._≃f_.transf-eq =
    𝒟.≈-trans (𝒟.∘-cong (𝒟.≈-trans (F .fmor-cong (CD .apex .fam .refl*)) (F .fmor-id))
                          (𝒟.≈-trans 𝒟.id-left 𝒟.id-left))
               (𝒟.≈-trans 𝒟.id-left (𝒟.≈-sym (F .fmor-id)))

-- The definability witness picker passes to families: a family morphism is an
-- index map together with a fibre map at each index, and the change of base
-- leaves the index map alone, so the fibres can be chosen one at a time. The
-- chosen fibres are natural because the base functor is faithful.
module _ (faithful : ∀ {a b} {g₁ g₂ : a 𝒞.⇒ b} → F .fmor g₁ 𝒟.≈ F .fmor g₂ → g₁ 𝒞.≈ g₂)
         (Fdef : ∀ {a b} (k : F .fobj a 𝒟.⇒ F .fobj b) →
                 Prf (∃ (a 𝒞.⇒ b) λ g → F .fmor g 𝒟.≈ k) →
                 ∃ₛ (a 𝒞.⇒ b) λ g → F .fmor g 𝒟.≈ k)
         where

  FamF-def : ∀ {a b : Fam𝒞.Obj} (h : Fam𝒟.Mor (FamF .fobj a) (FamF .fobj b)) →
             Prf (∃ (Fam𝒞.Mor a b) λ g → Fam𝒟C._≈_ (FamF .fmor g) h) →
             ∃ₛ (Fam𝒞.Mor a b) λ g → Fam𝒟C._≈_ (FamF .fmor g) h
  FamF-def {a} {b} h ⟪ def ⟫ = g , g-eq
    where
      -- Each fibre of h is definable, by restricting the given witness.
      fibre-def : ∀ i → Prf (∃ (a .fam .fm i 𝒞.⇒ b .fam .fm (h .idxf .PS._⇒_.func i))
                               λ k → F .fmor k 𝒟.≈ h .famf ._⇒f_.transf i)
      fibre-def i = ⟪ go def ⟫
        where
          go : (∃ (Fam𝒞.Mor a b) λ g₀ → Fam𝒟C._≈_ (FamF .fmor g₀) h) →
               ∃ (a .fam .fm i 𝒞.⇒ b .fam .fm (h .idxf .PS._⇒_.func i))
                 λ k → F .fmor k 𝒟.≈ h .famf ._⇒f_.transf i
          go (g₀ , eq) =
            (b .fam .subst (eq .idxf-eq .PS._≃m_.func-eq (a .idx .Setoid.refl))
               𝒞.∘ g₀ .famf ._⇒f_.transf i) ,
            𝒟.≈-trans (F .fmor-comp _ _) (eq .famf-eq ._≃f_.transf-eq {i})

      pick : ∀ i → a .fam .fm i 𝒞.⇒ b .fam .fm (h .idxf .PS._⇒_.func i)
      pick i = ∃ₛ.fst (Fdef (h .famf ._⇒f_.transf i) (fibre-def i))

      pick-eq : ∀ i → F .fmor (pick i) 𝒟.≈ h .famf ._⇒f_.transf i
      pick-eq i = ∃ₛ.snd (Fdef (h .famf ._⇒f_.transf i) (fibre-def i))

      g : Fam𝒞.Mor a b
      g .idxf = h .idxf
      g .famf ._⇒f_.transf = pick
      g .famf ._⇒f_.natural {i₁} {i₂} e =
        faithful
          (𝒟.≈-trans (F .fmor-comp _ _)
          (𝒟.≈-trans (𝒟.∘-cong (pick-eq i₂) 𝒟.≈-refl)
          (𝒟.≈-trans (h .famf ._⇒f_.natural e)
          (𝒟.≈-trans (𝒟.∘-cong 𝒟.≈-refl (𝒟.≈-sym (pick-eq i₁)))
                      (𝒟.≈-sym (F .fmor-comp _ _))))))

      g-eq : Fam𝒟C._≈_ (FamF .fmor g) h
      g-eq .idxf-eq .PS._≃m_.func-eq e = h .idxf .PS._⇒_.func-resp-≈ e
      g-eq .famf-eq ._≃f_.transf-eq {i} =
        𝒟.≈-trans (𝒟.∘-cong (𝒟.≈-trans (F .fmor-cong (b .fam .refl*)) (F .fmor-id))
                              𝒟.≈-refl)
                   (𝒟.≈-trans 𝒟.id-left (pick-eq i))

-- Fullness passes to families outright, with no mere-definability hypothesis: the index map is
-- carried unchanged, each fibre's preimage is chosen directly, and the chosen fibres are natural
-- because the base functor is faithful.
module _ (faithful : ∀ {a b} {g₁ g₂ : a 𝒞.⇒ b} → F .fmor g₁ 𝒟.≈ F .fmor g₂ → g₁ 𝒞.≈ g₂)
         (full : ∀ {a b} (k : F .fobj a 𝒟.⇒ F .fobj b) →
                 ∃ₛ (a 𝒞.⇒ b) λ g → F .fmor g 𝒟.≈ k)
         where

  FamF-full : ∀ {a b : Fam𝒞.Obj} (h : Fam𝒟.Mor (FamF .fobj a) (FamF .fobj b)) →
              ∃ₛ (Fam𝒞.Mor a b) λ g → Fam𝒟C._≈_ (FamF .fmor g) h
  FamF-full {a} {b} h = g , g-eq
    where
      pick : ∀ i → a .fam .fm i 𝒞.⇒ b .fam .fm (h .idxf .PS._⇒_.func i)
      pick i = ∃ₛ.fst (full (h .famf ._⇒f_.transf i))

      pick-eq : ∀ i → F .fmor (pick i) 𝒟.≈ h .famf ._⇒f_.transf i
      pick-eq i = ∃ₛ.snd (full (h .famf ._⇒f_.transf i))

      g : Fam𝒞.Mor a b
      g .idxf = h .idxf
      g .famf ._⇒f_.transf = pick
      g .famf ._⇒f_.natural {i₁} {i₂} e =
        faithful
          (𝒟.≈-trans (F .fmor-comp _ _)
          (𝒟.≈-trans (𝒟.∘-cong (pick-eq i₂) 𝒟.≈-refl)
          (𝒟.≈-trans (h .famf ._⇒f_.natural e)
          (𝒟.≈-trans (𝒟.∘-cong 𝒟.≈-refl (𝒟.≈-sym (pick-eq i₁)))
                      (𝒟.≈-sym (F .fmor-comp _ _))))))

      g-eq : Fam𝒟C._≈_ (FamF .fmor g) h
      g-eq .idxf-eq .PS._≃m_.func-eq e = h .idxf .PS._⇒_.func-resp-≈ e
      g-eq .famf-eq ._≃f_.transf-eq {i} =
        𝒟.≈-trans (𝒟.∘-cong (𝒟.≈-trans (F .fmor-cong (b .fam .refl*)) (F .fmor-id))
                              𝒟.≈-refl)
                   (𝒟.≈-trans 𝒟.id-left (pick-eq i))
