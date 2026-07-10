{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (lift)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import prop using (_,_; ∃ₛ)
open import prop-setoid
  using (IsEquivalence; module ≈-Reasoning; idS)
  renaming (≃m-isEquivalence to ≈s-isEquivalence; _⇒_ to _⇒s_)
open import categories using (Category; HasTerminal; HasCoproducts; HasProducts)
open import setoid-cat using (SetoidCat; Setoid-coproducts; Setoid-products; Setoid-terminal)
open import functor using (Functor; NatTrans; Full; Faithful)
open import fam using (module CategoryOfFamilies)
open import finite-product-functor
  using (preserve-chosen-products; preserve-chosen-terminal; module preserve-chosen-products-consequences)
open import indexed-family using (Fam; _⇒f_; _≃f_; changeCat)

module fam-functor where

module _ {o₁ m₁ e₁ o₂ m₂ e₂}
         {𝒞 : Category o₁ m₁ e₁}
         {𝒟 : Category o₂ m₂ e₂}
         os es
         (F : Functor 𝒞 𝒟) where

  private
    module 𝒞 = Category 𝒞
    module 𝒟 = Category 𝒟
    module Fam𝒞 = CategoryOfFamilies os es 𝒞
    module Fam𝒟 = CategoryOfFamilies os es 𝒟

  open Fam
  open _⇒f_
  open _≃f_
  open IsEquivalence
  open CategoryOfFamilies.Obj
  open CategoryOfFamilies.Mor
  open CategoryOfFamilies._≃_
  open Functor

  FamF : Functor Fam𝒞.cat Fam𝒟.cat
  FamF .fobj X .idx = X .idx
  FamF .fobj X .fam = changeCat F (X .fam)
  FamF .fmor f .idxf = f .idxf
  FamF .fmor f .famf .transf x = F .fmor (f .famf .transf x)
  FamF .fmor {X} {Y} f .famf .natural x₁≈x₂ =
    begin
      F .fmor (f .famf .transf _) 𝒟.∘ F .fmor (X .fam .subst _)
    ≈⟨ 𝒟.≈-sym (F .fmor-comp _ _) ⟩
      F .fmor (f .famf .transf _ 𝒞.∘ X .fam .subst _)
    ≈⟨ F .fmor-cong (f .famf .natural _) ⟩
      F .fmor (Y .fam .subst _ 𝒞.∘ f .famf .transf _)
    ≈⟨ F .fmor-comp _ _ ⟩
      F .fmor (Y .fam .subst _) 𝒟.∘ F .fmor (f .famf .transf _)
    ∎ where open ≈-Reasoning 𝒟.isEquiv
  FamF .fmor-cong f₁≈f₂ .idxf-eq = f₁≈f₂ .idxf-eq
  FamF .fmor-cong {X} {Y} {f₁} {f₂} f₁≈f₂ .famf-eq .transf-eq {x} =
    begin
      F .fmor (Y .fam .subst _) 𝒟.∘ F .fmor (f₁ .famf .transf x)
    ≈˘⟨ F .fmor-comp _ _ ⟩
      F .fmor (Y .fam .subst _ 𝒞.∘ f₁ .famf .transf x)
    ≈⟨ F .fmor-cong (f₁≈f₂ .famf-eq .transf-eq) ⟩
      F .fmor (f₂ .famf .transf x)
    ∎
    where open ≈-Reasoning 𝒟.isEquiv
  FamF .fmor-id .idxf-eq = ≈s-isEquivalence .refl
  FamF .fmor-id {X} .famf-eq .transf-eq {x} =
    begin
      F .fmor (X .fam .subst _) 𝒟.∘ F .fmor (𝒞.id _)
    ≈⟨ 𝒟.∘-cong (F .fmor-cong (X .fam .refl*)) 𝒟.≈-refl ⟩
      F .fmor (𝒞.id _) 𝒟.∘ F .fmor (𝒞.id _)
    ≈⟨ 𝒟.∘-cong (F .fmor-id) (F .fmor-id) ⟩
      𝒟.id _ 𝒟.∘ 𝒟.id _
    ≈⟨ 𝒟.id-left ⟩
      𝒟.id _
    ∎
    where open ≈-Reasoning 𝒟.isEquiv
  FamF .fmor-comp f g .idxf-eq = ≈s-isEquivalence .refl
  FamF .fmor-comp {X} {Y} {Z} f g .famf-eq .transf-eq {x} =
    begin
      F .fmor (Z .fam .subst _) 𝒟.∘ F .fmor (𝒞.id _ 𝒞.∘ (f .famf .transf _ 𝒞.∘ g .famf .transf x))
    ≈⟨ 𝒟.∘-cong (F .fmor-cong (Z .fam .refl*)) (F .fmor-cong 𝒞.id-left) ⟩
      F .fmor (𝒞.id _) 𝒟.∘ F .fmor (f .famf .transf _ 𝒞.∘ g .famf .transf x)
    ≈⟨ 𝒟.∘-cong (F .fmor-id) (F .fmor-comp _ _) ⟩
      𝒟.id _ 𝒟.∘ (F .fmor (f .famf .transf _) 𝒟.∘ F .fmor (g .famf .transf x))
    ∎
    where open ≈-Reasoning 𝒟.isEquiv

  ------------------------------------------------------------------------------
  -- Fam preserves faithfulness, and fullness in the presence of faithfulness (naturality of the
  -- assembled family of preimages is reflected along F).

  FamF-faithful : Faithful F → Faithful FamF
  FamF-faithful F-faithful eq .idxf-eq = eq .idxf-eq
  FamF-faithful F-faithful {X} {Y} {f} {g} eq .famf-eq .transf-eq {x} =
    F-faithful
      (begin
        F .fmor (Y .fam .subst _ 𝒞.∘ f .famf .transf x)
      ≈⟨ F .fmor-comp _ _ ⟩
        F .fmor (Y .fam .subst _) 𝒟.∘ F .fmor (f .famf .transf x)
      ≈⟨ eq .famf-eq .transf-eq ⟩
        F .fmor (g .famf .transf x)
      ∎)
    where open ≈-Reasoning 𝒟.isEquiv

  module _ (F-full : Full F) (F-faithful : Faithful F) where
    open ∃ₛ

    private
      ψ : ∀ {X Y} (h : Fam𝒟.Mor (FamF .fobj X) (FamF .fobj Y)) →
          ∀ x → X .fam .fm x 𝒞.⇒ Y .fam .fm (h .idxf ._⇒s_.func x)
      ψ h x = F-full (h .famf .transf x) .fst

      ψ-eq : ∀ {X Y} (h : Fam𝒟.Mor (FamF .fobj X) (FamF .fobj Y)) →
             ∀ x → F .fmor (ψ h x) 𝒟.≈ h .famf .transf x
      ψ-eq h x = F-full (h .famf .transf x) .snd

      preimage : ∀ {X Y} → Fam𝒟.Mor (FamF .fobj X) (FamF .fobj Y) → Fam𝒞.Mor X Y
      preimage h .idxf = h .idxf
      preimage {X} {Y} h .famf .transf x = ψ h x
      preimage {X} {Y} h .famf .natural {x₁} {x₂} e =
        F-faithful
          (begin
            F .fmor (ψ h x₂ 𝒞.∘ X .fam .subst e)
          ≈⟨ F .fmor-comp _ _ ⟩
            F .fmor (ψ h x₂) 𝒟.∘ F .fmor (X .fam .subst e)
          ≈⟨ 𝒟.∘-cong (ψ-eq h x₂) 𝒟.≈-refl ⟩
            h .famf .transf x₂ 𝒟.∘ F .fmor (X .fam .subst e)
          ≈⟨ h .famf .natural e ⟩
            F .fmor (Y .fam .subst _) 𝒟.∘ h .famf .transf x₁
          ≈˘⟨ 𝒟.∘-cong 𝒟.≈-refl (ψ-eq h x₁) ⟩
            F .fmor (Y .fam .subst _) 𝒟.∘ F .fmor (ψ h x₁)
          ≈˘⟨ F .fmor-comp _ _ ⟩
            F .fmor (Y .fam .subst _ 𝒞.∘ ψ h x₁)
          ∎)
        where open ≈-Reasoning 𝒟.isEquiv

    FamF-full : Full FamF
    FamF-full h .fst = preimage h
    FamF-full h .snd .idxf-eq = ≈s-isEquivalence .refl
    FamF-full {X} {Y} h .snd .famf-eq .transf-eq {x} =
      begin
        F .fmor (Y .fam .subst _) 𝒟.∘ F .fmor (ψ h x)
      ≈⟨ 𝒟.∘-cong (F .fmor-cong (Y .fam .refl*)) (ψ-eq h x) ⟩
        F .fmor (𝒞.id _) 𝒟.∘ h .famf .transf x
      ≈⟨ 𝒟.∘-cong (F .fmor-id) 𝒟.≈-refl ⟩
        𝒟.id _ 𝒟.∘ h .famf .transf x
      ≈⟨ 𝒟.id-left ⟩
        h .famf .transf x
      ∎
      where open ≈-Reasoning 𝒟.isEquiv

  ------------------------------------------------------------------------------
  -- Preservation of coproducts.
  --
  -- This should be trivial, because everything is the identity, but
  -- Agda makes us show every case separately.

  open import finite-coproduct-functor
  open import Data.Sum using (inj₁; inj₂)
  module SCP = HasCoproducts (Setoid-coproducts os es)
  module SP = HasProducts (Setoid-products os es)
  module ST = HasTerminal (Setoid-terminal os es)

  open Category.IsIso

  preserve-coproducts : preserve-chosen-coproducts FamF Fam𝒞.coproducts Fam𝒟.coproducts
  preserve-coproducts .inverse .idxf = idS _
  preserve-coproducts .inverse .famf .transf (inj₁ x) = 𝒟.id _
  preserve-coproducts .inverse .famf .transf (inj₂ y) = 𝒟.id _
  preserve-coproducts .inverse .famf .natural {inj₁ x} {inj₁ x₁} e = 𝒟.id-swap
  preserve-coproducts .inverse .famf .natural {inj₂ y} {inj₂ y₁} e = 𝒟.id-swap
  preserve-coproducts .f∘inverse≈id .idxf-eq = ≈s-isEquivalence .trans prop-setoid.id-right SCP.copair-ext0
  preserve-coproducts {X} {Y} .f∘inverse≈id .famf-eq .transf-eq {inj₁ x} = begin
      F .fmor (X .fam .subst _) 𝒟.∘ (𝒟.id _ 𝒟.∘ (F .fmor (𝒞.id _) 𝒟.∘ 𝒟.id _))
    ≈⟨ 𝒟.∘-cong (F .fmor-cong (X .fam .refl*)) 𝒟.id-left ⟩
      F .fmor (𝒞.id _) 𝒟.∘ (F .fmor (𝒞.id _) 𝒟.∘ 𝒟.id _)
    ≈⟨ 𝒟.∘-cong (F .fmor-id) (𝒟.∘-cong (F .fmor-id) 𝒟.≈-refl) ⟩
      𝒟.id _ 𝒟.∘ (𝒟.id _ 𝒟.∘ 𝒟.id _)
    ≈⟨ 𝒟.id-left ⟩
      𝒟.id _ 𝒟.∘ 𝒟.id _
    ≈⟨ 𝒟.id-left ⟩
      𝒟.id _
    ∎
    where open ≈-Reasoning 𝒟.isEquiv
  preserve-coproducts {X} {Y} .f∘inverse≈id .famf-eq .transf-eq {inj₂ y} = begin
      F .fmor (Y .fam .subst _) 𝒟.∘ (𝒟.id _ 𝒟.∘ (F .fmor (𝒞.id _) 𝒟.∘ 𝒟.id _))
    ≈⟨ 𝒟.∘-cong (F .fmor-cong (Y .fam .refl*)) 𝒟.id-left ⟩
      F .fmor (𝒞.id _) 𝒟.∘ (F .fmor (𝒞.id _) 𝒟.∘ 𝒟.id _)
    ≈⟨ 𝒟.∘-cong (F .fmor-id) (𝒟.∘-cong (F .fmor-id) 𝒟.≈-refl) ⟩
      𝒟.id _ 𝒟.∘ (𝒟.id _ 𝒟.∘ 𝒟.id _)
    ≈⟨ 𝒟.id-left ⟩
      𝒟.id _ 𝒟.∘ 𝒟.id _
    ≈⟨ 𝒟.id-left ⟩
      𝒟.id _
    ∎
    where open ≈-Reasoning 𝒟.isEquiv
  preserve-coproducts {X} {Y} .inverse∘f≈id .idxf-eq = ≈s-isEquivalence .trans prop-setoid.id-left SCP.copair-ext0
  preserve-coproducts {X} {Y} .inverse∘f≈id .famf-eq .transf-eq {inj₁ x} = begin
      F .fmor (X .fam .subst _) 𝒟.∘ (𝒟.id _ 𝒟.∘ (𝒟.id _ 𝒟.∘ F .fmor (𝒞.id _)))
    ≈⟨ 𝒟.∘-cong (F .fmor-cong (X .fam .refl*)) 𝒟.id-left ⟩
      F .fmor (𝒞.id _) 𝒟.∘ (𝒟.id _ 𝒟.∘ F .fmor (𝒞.id _))
    ≈⟨ 𝒟.∘-cong (F .fmor-id) (𝒟.∘-cong 𝒟.≈-refl (F .fmor-id)) ⟩
      𝒟.id _ 𝒟.∘ (𝒟.id _ 𝒟.∘ 𝒟.id _)
    ≈⟨ 𝒟.id-left ⟩
      𝒟.id _ 𝒟.∘ 𝒟.id _
    ≈⟨ 𝒟.id-left ⟩
      𝒟.id _
    ∎
    where open ≈-Reasoning 𝒟.isEquiv
  preserve-coproducts {X} {Y} .inverse∘f≈id .famf-eq .transf-eq {inj₂ y} = begin
      F .fmor (Y .fam .subst _) 𝒟.∘ (𝒟.id _ 𝒟.∘ (𝒟.id _ 𝒟.∘ F .fmor (𝒞.id _)))
    ≈⟨ 𝒟.∘-cong (F .fmor-cong (Y .fam .refl*)) 𝒟.id-left ⟩
      F .fmor (𝒞.id _) 𝒟.∘ (𝒟.id _ 𝒟.∘ F .fmor (𝒞.id _))
    ≈⟨ 𝒟.∘-cong (F .fmor-id) (𝒟.∘-cong 𝒟.≈-refl (F .fmor-id)) ⟩
      𝒟.id _ 𝒟.∘ (𝒟.id _ 𝒟.∘ 𝒟.id _)
    ≈⟨ 𝒟.id-left ⟩
      𝒟.id _ 𝒟.∘ 𝒟.id _
    ≈⟨ 𝒟.id-left ⟩
      𝒟.id _
    ∎
    where open ≈-Reasoning 𝒟.isEquiv

  module _ (𝒞T : HasTerminal 𝒞) (𝒟T : HasTerminal 𝒟) (FT : preserve-chosen-terminal F 𝒞T 𝒟T) where

    private
      module 𝒟T = HasTerminal 𝒟T
      module 𝒞T = HasTerminal 𝒞T

    Fam𝒞-terminal : HasTerminal Fam𝒞.cat
    Fam𝒞-terminal = Fam𝒞.terminal 𝒞T

    Fam𝒟-terminal : HasTerminal Fam𝒟.cat
    Fam𝒟-terminal = Fam𝒟.terminal 𝒟T

    preserve-terminal : preserve-chosen-terminal FamF Fam𝒞-terminal Fam𝒟-terminal
    preserve-terminal .inverse .idxf = idS _
    preserve-terminal .inverse .famf .transf x = inverse FT
    preserve-terminal .inverse .famf .natural {lift tt} {lift tt} _ = begin
        inverse FT 𝒟.∘ 𝒟.id _
      ≈⟨ 𝒟.id-swap' ⟩
        𝒟.id _ 𝒟.∘ inverse FT
      ≈˘⟨ 𝒟.∘-cong (F .fmor-id) 𝒟.≈-refl ⟩
        F .fmor (𝒞.id _) 𝒟.∘ inverse FT
      ∎
      where open ≈-Reasoning 𝒟.isEquiv
    preserve-terminal .f∘inverse≈id .idxf-eq = ST.to-terminal-unique _ _
    preserve-terminal .f∘inverse≈id .famf-eq .transf-eq = 𝒟T.to-terminal-unique _ _
    preserve-terminal .inverse∘f≈id .idxf-eq = ST.to-terminal-unique _ _
    preserve-terminal .inverse∘f≈id .famf-eq .transf-eq = begin
        F .fmor (𝒞.id _) 𝒟.∘ (𝒟.id _ 𝒟.∘ (inverse FT 𝒟.∘ 𝒟T.to-terminal))
      ≈⟨ 𝒟.∘-cong (F .fmor-id) (𝒟.∘-cong 𝒟.≈-refl (inverse∘f≈id FT)) ⟩
        𝒟.id _ 𝒟.∘ (𝒟.id _ 𝒟.∘ 𝒟.id _)
      ≈⟨ trans 𝒟.isEquiv 𝒟.id-left 𝒟.id-right ⟩
        𝒟.id _
      ∎
      where open ≈-Reasoning 𝒟.isEquiv

  module _ (𝒞P : HasProducts 𝒞) (𝒟P : HasProducts 𝒟) (FP : preserve-chosen-products F 𝒞P 𝒟P) where

    private
      module 𝒟P = HasProducts 𝒟P
      module 𝒞P = HasProducts 𝒞P

    Fam𝒞-products : HasProducts Fam𝒞.cat
    Fam𝒞-products = Fam𝒞.products.products 𝒞P

    Fam𝒟-products : HasProducts Fam𝒟.cat
    Fam𝒟-products = Fam𝒟.products.products 𝒟P

    open preserve-chosen-products-consequences F 𝒞P 𝒟P FP

    preserve-products : preserve-chosen-products FamF Fam𝒞-products Fam𝒟-products
    preserve-products .inverse .idxf = idS _
    preserve-products .inverse .famf .transf (x , y) = mul
    preserve-products .inverse .famf .natural {x₁ , y₁} {x₂ , y₂} (eq₁ , eq₂) = 𝒟.≈-sym mul-natural
    preserve-products {X} {Y} .f∘inverse≈id .idxf-eq =
      ≈s-isEquivalence .trans prop-setoid.id-right SP.pair-ext0
    preserve-products {X} {Y} .f∘inverse≈id .famf-eq .transf-eq = begin
        𝒟P.prod-m (F .fmor (X .fam .subst _)) (F .fmor (Y .fam .subst _)) 𝒟.∘ (𝒟.id _ 𝒟.∘ (mul⁻¹ 𝒟.∘ mul))
      ≈⟨ 𝒟.∘-cong (𝒟P.prod-m-cong (F .fmor-cong (X .fam .refl*)) (F .fmor-cong (Y .fam .refl*))) (𝒟.∘-cong 𝒟.≈-refl (f∘inverse≈id FP)) ⟩
        𝒟P.prod-m (F .fmor (𝒞.id _)) (F .fmor (𝒞.id _)) 𝒟.∘ (𝒟.id _ 𝒟.∘ 𝒟.id _)
      ≈⟨ 𝒟.∘-cong (𝒟P.prod-m-cong (F .fmor-id) (F .fmor-id)) 𝒟.id-left ⟩
        𝒟P.prod-m (𝒟.id _) (𝒟.id _) 𝒟.∘ 𝒟.id _
      ≈⟨ 𝒟.∘-cong 𝒟P.prod-m-id 𝒟.≈-refl ⟩
        𝒟.id _ 𝒟.∘ 𝒟.id _
      ≈⟨ 𝒟.id-left ⟩
        𝒟.id _
      ∎
      where open ≈-Reasoning 𝒟.isEquiv
    preserve-products {X} {Y} .inverse∘f≈id .idxf-eq =
      ≈s-isEquivalence .trans prop-setoid.id-left SP.pair-ext0
    preserve-products {X} {Y} .inverse∘f≈id .famf-eq .transf-eq = begin
        F .fmor (𝒞P.prod-m (X .fam .subst _) (Y .fam .subst _)) 𝒟.∘ (𝒟.id _ 𝒟.∘ (mul 𝒟.∘ mul⁻¹))
      ≈⟨ 𝒟.∘-cong (F .fmor-cong (𝒞P.prod-m-cong (X .fam .refl*) (Y .fam .refl*))) (𝒟.∘-cong 𝒟.≈-refl (inverse∘f≈id FP)) ⟩
        F .fmor (𝒞P.prod-m (𝒞.id _) (𝒞.id _)) 𝒟.∘ (𝒟.id _ 𝒟.∘ 𝒟.id _)
      ≈⟨ 𝒟.∘-cong (F .fmor-cong 𝒞P.prod-m-id) 𝒟.id-left ⟩
        F .fmor (𝒞.id _) 𝒟.∘ 𝒟.id _
      ≈⟨ 𝒟.∘-cong (F .fmor-id) 𝒟.≈-refl ⟩
        𝒟.id _ 𝒟.∘ 𝒟.id _
      ≈⟨ 𝒟.id-left ⟩
        𝒟.id _
      ∎
      where open ≈-Reasoning 𝒟.isEquiv



module _ {o₁ m₁ e₁ o₂ m₂ e₂} {𝒞 : Category o₁ m₁ e₁} {𝒟 : Category o₂ m₂ e₂}
         os es (F G : Functor 𝒞 𝒟)
       where

  private
    module 𝒞 = Category 𝒞
    module 𝒟 = Category 𝒟

  open Functor
  open NatTrans
  open Fam
  open CategoryOfFamilies.Obj
  open CategoryOfFamilies.Mor
  open CategoryOfFamilies._≃_
  open _⇒f_
  open _≃f_

  FamNat : (α : NatTrans F G) → NatTrans (FamF os es F) (FamF os es G)
  FamNat α .transf X .idxf = prop-setoid.idS _
  FamNat α .transf X .famf .transf x = α .transf (X .fam .fm x)
  FamNat α .transf X .famf .natural h = 𝒟.≈-sym (α .natural (X .fam .subst h))
  FamNat α .natural f .idxf-eq = Category.id-swap' (SetoidCat _ _)
  FamNat α .natural {X} {Y} f .famf-eq .transf-eq {x} =
    begin
      G .fmor (Y .fam .subst _ ) 𝒟.∘ (𝒟.id _ 𝒟.∘ (G .fmor (f .famf .transf x) 𝒟.∘ α .transf (X .fam .fm x)))
    ≈⟨ 𝒟.∘-cong (G .fmor-cong (Y .fam .refl*)) 𝒟.id-left ⟩
      G .fmor (𝒞.id _) 𝒟.∘ (G .fmor (f .famf .transf x) 𝒟.∘ α .transf (X .fam .fm x))
    ≈⟨ 𝒟.∘-cong (G .fmor-id) (α .natural (f .famf .transf x)) ⟩
      𝒟.id _ 𝒟.∘ (α .transf (Y .fam .fm (f .idxf ._⇒s_.func x)) 𝒟.∘ F .fmor (f .famf .transf x))
    ∎
    where open ≈-Reasoning 𝒟.isEquiv
