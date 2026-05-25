{-# OPTIONS --postfix-projections --prop --safe #-}

open import categories using (Category; HasTerminal; HasProducts; HasCoproducts; HasStrongCoproducts;
                              strong-coproducts→coproducts; HasExponentials; HasBooleans; coproducts+exp→booleans)
open import polynomial-functor using (Poly; module Interp; Poly-map; Poly-iso; Preserves-μ)
open import functor using (Functor)
open import finite-product-functor
  using (preserve-chosen-products; module preserve-chosen-products-consequences)
open import finite-coproduct-functor
  using (preserve-chosen-coproducts; module preserve-chosen-coproducts-consequences)

import language-syntax
open import signature

open Functor

module language-fo-interpretation {ℓ} (Sig : Signature ℓ)
  {o₁ m₁ e₁ o₂ m₂ e₂}
  (𝒞 : Category o₁ m₁ e₁) (𝒞T : HasTerminal 𝒞) (𝒞P : HasProducts 𝒞) (𝒞SC : HasStrongCoproducts 𝒞 𝒞P)
  (let 𝒞CP = strong-coproducts→coproducts 𝒞T 𝒞SC)
  (let open Interp 𝒞T 𝒞P 𝒞SC hiding (fobj; fmor; functor; fmor-id; fmor-cong; fmor-comp)
         renaming (HasMu to 𝒞HasMu)) (𝒞Mu : 𝒞HasMu)
  (𝒟 : Category o₂ m₂ e₂) (𝒟T : HasTerminal 𝒟) (𝒟P : HasProducts 𝒟) (𝒟SC : HasStrongCoproducts 𝒟 𝒟P) (𝒟E : HasExponentials 𝒟 𝒟P)
  (let 𝒟CP = strong-coproducts→coproducts 𝒟T 𝒟SC)
  (let open Interp 𝒟T 𝒟P 𝒟SC hiding (fobj; fmor; functor; fmor-id; fmor-cong; fmor-comp)) (𝒟Mu : HasMu)
  (F : Functor 𝒞 𝒟)
  (FT : Category.IsIso 𝒟 (HasTerminal.to-terminal 𝒟T {F .fobj (𝒞T .HasTerminal.witness)}))
  (FP : preserve-chosen-products F 𝒞P 𝒟P)
  (FC : preserve-chosen-coproducts F 𝒞CP 𝒟CP)
  (Fμ : Preserves-μ 𝒞T 𝒞P 𝒞SC 𝒟T 𝒟P 𝒟SC 𝒞Mu 𝒟Mu F)
  (𝒞-Sig-model : Model PFPC[ 𝒞 , 𝒞T , 𝒞P , 𝒞CP .HasCoproducts.coprod (𝒞T .HasTerminal.witness) (𝒞T .HasTerminal.witness) ] Sig)
  where

open language-syntax Sig

module _ where
  open Category 𝒞
  open HasTerminal 𝒞T renaming (witness to 𝟙)
  open HasProducts 𝒞P renaming (prod to _×_)
  open HasCoproducts 𝒞CP renaming (coprod to _+_)
  open Interp 𝒞T 𝒞P 𝒞SC renaming (fobj to poly-obj) using ()
  open 𝒞HasMu 𝒞Mu using () renaming (μ to μ-obj)

  mutual
    𝒞⟦_⟧ty : ∀ {τ} → first-order τ → obj
    𝒞⟦ unit ⟧ty = 𝟙
    𝒞⟦ bool ⟧ty = 𝟙 + 𝟙
    𝒞⟦ base s ⟧ty = 𝒞-Sig-model .Model.⟦sort⟧ s
    𝒞⟦ τ₁ [×] τ₂ ⟧ty = 𝒞⟦ τ₁ ⟧ty × 𝒞⟦ τ₂ ⟧ty
    𝒞⟦ τ₁ [+] τ₂ ⟧ty = 𝒞⟦ τ₁ ⟧ty + 𝒞⟦ τ₂ ⟧ty
    𝒞⟦ μ P-fo ⟧ty = μ-obj 𝒞⟦ P-fo ⟧poly

    𝒞⟦_⟧poly : ∀ {P} → first-order-poly P → Poly 𝒞
    𝒞⟦ const τ-fo ⟧poly = Poly.const 𝒞⟦ τ-fo ⟧ty
    𝒞⟦ var ⟧poly        = Poly.var
    𝒞⟦ P [+] Q ⟧poly    = 𝒞⟦ P ⟧poly Poly.+ 𝒞⟦ Q ⟧poly
    𝒞⟦ P [×] Q ⟧poly    = 𝒞⟦ P ⟧poly Poly.× 𝒞⟦ Q ⟧poly

  𝒞⟦_⟧ctxt : ∀ {Γ} → first-order-ctxt Γ → obj
  𝒞⟦ emp ⟧ctxt = 𝟙
  𝒞⟦ Γ , τ ⟧ctxt = 𝒞⟦ Γ ⟧ctxt × 𝒞⟦ τ ⟧ty

private
  module 𝒞CP = HasCoproducts 𝒞CP
  module 𝒟 = Category 𝒟
  module 𝒟CP = HasCoproducts 𝒟CP
  module 𝒟P = HasProducts 𝒟P

𝒞Bool = 𝒞CP.coprod (𝒞T .HasTerminal.witness) (𝒞T .HasTerminal.witness)
𝒟Bool = 𝒟CP.coprod (𝒟T .HasTerminal.witness) (𝒟T .HasTerminal.witness)

Bool-iso : 𝒟.Iso (F .fobj 𝒞Bool) 𝒟Bool
Bool-iso =
  𝒟.Iso-trans (𝒟.Iso-sym (𝒟.IsIso→Iso FC))
              (𝒟CP.coproduct-preserve-iso (𝒟.IsIso→Iso FT) (𝒟.IsIso→Iso FT))

𝒟-Sig-model : Model PFPC[ 𝒟 , 𝒟T , 𝒟P , 𝒟Bool ] Sig
𝒟-Sig-model = transport-model Sig F FT FP (Bool-iso .𝒟.Iso.fwd) 𝒞-Sig-model

open import language-interpretation Sig 𝒟 𝒟T 𝒟P 𝒟SC 𝒟E 𝒟Mu 𝒟-Sig-model
  renaming (⟦_⟧ty to 𝒟⟦_⟧ty; ⟦_⟧ctxt to 𝒟⟦_⟧ctxt; ⟦_⟧tm to 𝒟⟦_⟧tm; ⟦_⟧poly to 𝒟⟦_⟧poly) using ()
  public

mutual
  ⟦_⟧-iso : ∀ {τ} (τ-fo : first-order τ) → 𝒟.Iso (F .fobj 𝒞⟦ τ-fo ⟧ty) 𝒟⟦ τ ⟧ty
  ⟦ unit ⟧-iso      = 𝒟.IsIso→Iso FT
  ⟦ bool ⟧-iso      = Bool-iso
  ⟦ base s ⟧-iso    = 𝒟.Iso-refl
  ⟦ τ₁ [×] τ₂ ⟧-iso = 𝒟.Iso-trans (𝒟.IsIso→Iso FP) (𝒟P.product-preserves-iso ⟦ τ₁ ⟧-iso ⟦ τ₂ ⟧-iso)
  ⟦ τ₁ [+] τ₂ ⟧-iso = 𝒟.Iso-trans (𝒟.Iso-sym (𝒟.IsIso→Iso FC)) (𝒟CP.coproduct-preserve-iso ⟦ τ₁ ⟧-iso ⟦ τ₂ ⟧-iso)
  ⟦ μ P-fo ⟧-iso    = 𝒟.Iso-trans (Fμ 𝒞⟦ P-fo ⟧poly) (HasMu.iso 𝒟Mu ⟦ P-fo ⟧poly-iso)

  ⟦_⟧poly-iso : ∀ {P} (P-fo : first-order-poly P) → Poly-iso (Poly-map F 𝒞⟦ P-fo ⟧poly) 𝒟⟦ P ⟧poly
  ⟦ const τ-fo ⟧poly-iso = Poly-iso.const ⟦ τ-fo ⟧-iso
  ⟦ var ⟧poly-iso        = Poly-iso.var
  ⟦ P [+] Q ⟧poly-iso    = ⟦ P ⟧poly-iso Poly-iso.+ ⟦ Q ⟧poly-iso
  ⟦ P [×] Q ⟧poly-iso    = ⟦ P ⟧poly-iso Poly-iso.× ⟦ Q ⟧poly-iso

⟦_⟧ctxt-iso : ∀ {Γ} (Γ-fo : first-order-ctxt Γ) → 𝒟.Iso (F .fobj 𝒞⟦ Γ-fo ⟧ctxt) 𝒟⟦ Γ ⟧ctxt
⟦ emp ⟧ctxt-iso   = 𝒟.IsIso→Iso FT
⟦ Γ , τ ⟧ctxt-iso = 𝒟.Iso-trans (𝒟.IsIso→Iso FP) (𝒟P.product-preserves-iso ⟦ Γ ⟧ctxt-iso ⟦ τ ⟧-iso)
