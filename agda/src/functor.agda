{-# OPTIONS --prop --postfix-projections --safe #-}

module functor where

open import Level using (_⊔_)
open import categories using (Category)
open import prop-setoid using (IsEquivalence; module ≈-Reasoning)

open IsEquivalence

record Functor {o₁ m₁ e₁ o₂ m₂ e₂}
         (𝒞 : Category o₁ m₁ e₁)
         (𝒟 : Category o₂ m₂ e₂) : Set (o₁ ⊔ o₂ ⊔ m₁ ⊔ m₂ ⊔ e₁ ⊔ e₂) where
  no-eta-equality
  private
    module 𝒞 = Category 𝒞
    module 𝒟 = Category 𝒟
  field
    fobj : 𝒞.obj → 𝒟.obj
    fmor : ∀ {x y} → x 𝒞.⇒ y → fobj x 𝒟.⇒ fobj y
    fmor-cong : ∀ {x y} {f₁ f₂ : x 𝒞.⇒ y} → f₁ 𝒞.≈ f₂ → fmor f₁ 𝒟.≈ fmor f₂
    fmor-id : ∀ {x} → fmor (𝒞.id x) 𝒟.≈ 𝒟.id _
    fmor-comp : ∀ {x y z} (f : y 𝒞.⇒ z) (g : x 𝒞.⇒ y) →
                fmor (f 𝒞.∘ g) 𝒟.≈ (fmor f 𝒟.∘ fmor g)

------------------------------------------------------------------------------
-- Functors preserve isomorphisms.
module _ {o₁ m₁ e₁ o₂ m₂ e₂} {𝒞 : Category o₁ m₁ e₁} {𝒟 : Category o₂ m₂ e₂} where

  private
    module 𝒞 = Category 𝒞
    module 𝒟 = Category 𝒟
  open Functor
  open 𝒞.Iso

  functor-preserve-iso : (F : Functor 𝒞 𝒟) → ∀ {x y} → 𝒞.Iso x y → 𝒟.Iso (F .fobj x) (F .fobj y)
  functor-preserve-iso F iso .Category.Iso.fwd = F .fmor (iso .fwd)
  functor-preserve-iso F iso .Category.Iso.bwd = F .fmor (iso .bwd)
  functor-preserve-iso F iso .Category.Iso.fwd∘bwd≈id = begin
      F .fmor (iso .fwd) 𝒟.∘ F .fmor (iso .bwd)
    ≈˘⟨ F .fmor-comp _ _ ⟩
      F .fmor (iso .fwd 𝒞.∘ iso .bwd)
    ≈⟨ F .fmor-cong (iso .fwd∘bwd≈id) ⟩
      F .fmor (𝒞.id _)
    ≈⟨ F .fmor-id ⟩
      𝒟.id _
    ∎
    where open ≈-Reasoning 𝒟.isEquiv
  functor-preserve-iso F iso .Category.Iso.bwd∘fwd≈id = begin
      F .fmor (iso .bwd) 𝒟.∘ F .fmor (iso .fwd)
    ≈˘⟨ F .fmor-comp _ _ ⟩
      F .fmor (iso .bwd 𝒞.∘ iso .fwd)
    ≈⟨ F .fmor-cong (iso .bwd∘fwd≈id) ⟩
      F .fmor (𝒞.id _)
    ≈⟨ F .fmor-id ⟩
      𝒟.id _
    ∎
    where open ≈-Reasoning 𝒟.isEquiv

------------------------------------------------------------------------------
-- Constant functor and natural transformations.

module _ {o₁ m₁ e₁ o₂ m₂ e₂} where

  constF : ∀ (𝒞 : Category o₁ m₁ e₁) {𝒟 : Category o₂ m₂ e₂} (x : 𝒟 .Category.obj) →
           Functor 𝒞 𝒟
  constF 𝒞 {𝒟} x .Functor.fobj _ = x
  constF 𝒞 {𝒟} x .Functor.fmor _ = 𝒟 .Category.id x
  constF 𝒞 {𝒟} x .Functor.fmor-cong _ = 𝒟 .Category.isEquiv .refl
  constF 𝒞 {𝒟} x .Functor.fmor-id = 𝒟 .Category.isEquiv .refl
  constF 𝒞 {𝒟} x .Functor.fmor-comp _ _ = 𝒟 .Category.isEquiv .sym (𝒟 .Category.id-left)

module _ {o₁ m₁ e₁ o₂ m₂ e₂} {𝒞 : Category o₁ m₁ e₁} {𝒟 : Category o₂ m₂ e₂} where

  private
    module 𝒞 = Category 𝒞
    module 𝒟 = Category 𝒟
  open Functor

  record NatTrans (F G : Functor 𝒞 𝒟) : Set (o₁ ⊔ m₁ ⊔ m₂ ⊔ e₂) where
    no-eta-equality
    field
      transf : ∀ x → F .fobj x 𝒟.⇒ G .fobj x
      natural : ∀ {x y} (f : x 𝒞.⇒ y) → (G .fmor f 𝒟.∘ transf x) 𝒟.≈ (transf y 𝒟.∘ F .fmor f)
  open NatTrans

  record ≃-NatTrans {F G : Functor 𝒞 𝒟} (α β : NatTrans F G) : Prop (o₁ ⊔ e₂) where
    no-eta-equality
    field
      transf-eq : ∀ x → α .transf x 𝒟.≈ β .transf x
  open ≃-NatTrans

  ≃-isEquivalence : ∀ {F G} → IsEquivalence (≃-NatTrans {F} {G})
  ≃-isEquivalence .refl .transf-eq x = 𝒟.≈-refl
  ≃-isEquivalence .sym e .transf-eq x = 𝒟.≈-sym (e .transf-eq x)
  ≃-isEquivalence .trans e₁ e₂ .transf-eq x = 𝒟.isEquiv .trans (e₁ .transf-eq x) (e₂ .transf-eq x)

  id : ∀ F → NatTrans F F
  id F .transf x = 𝒟.id _
  id F .natural f = 𝒟.≈-sym 𝒟.id-swap

  _∘_ : ∀ {F G H} → NatTrans G H → NatTrans F G → NatTrans F H
  (α ∘ β) .transf x = α .transf x 𝒟.∘ β .transf x
  _∘_ {F} {G} {H} α β .natural {x} {y} f =
    begin
      H .fmor f 𝒟.∘ (α .transf x 𝒟.∘ β .transf x)
    ≈⟨ 𝒟.≈-sym (𝒟.assoc _ _ _) ⟩
      (H .fmor f 𝒟.∘ α .transf x) 𝒟.∘ β .transf x
    ≈⟨ 𝒟.∘-cong (α .natural f) 𝒟.≈-refl ⟩
      (α .transf y 𝒟.∘ G .fmor f) 𝒟.∘ β .transf x
    ≈⟨ 𝒟.assoc _ _ _ ⟩
      α .transf y 𝒟.∘ (G .fmor f 𝒟.∘ β .transf x)
    ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (β .natural f) ⟩
      α .transf y 𝒟.∘ (β .transf y 𝒟.∘ F .fmor f)
    ≈⟨ 𝒟.≈-sym (𝒟.assoc _ _ _) ⟩
      (α .transf y 𝒟.∘ β .transf y) 𝒟.∘ F .fmor f
    ∎ where open ≈-Reasoning 𝒟.isEquiv

  ∘NT-cong : ∀ {F G H} {α₁ α₂ : NatTrans G H} {β₁ β₂ : NatTrans F G} →
             ≃-NatTrans α₁ α₂ → ≃-NatTrans β₁ β₂ → ≃-NatTrans (α₁ ∘ β₁) (α₂ ∘ β₂)
  ∘NT-cong α₁≃α₂ β₁≃β₂ .transf-eq x = 𝒟.∘-cong (α₁≃α₂ .transf-eq x) (β₁≃β₂ .transf-eq x)

  NT-assoc : ∀ {F G H I} (α : NatTrans H I) (β : NatTrans G H) (γ : NatTrans F G) →
             ≃-NatTrans ((α ∘ β) ∘ γ) (α ∘ (β ∘ γ))
  NT-assoc α β γ .transf-eq x = 𝒟.assoc _ _ _

  NT-id-left : ∀ {F G} {α : NatTrans F G} → ≃-NatTrans (id _ ∘ α) α
  NT-id-left .transf-eq x = 𝒟.id-left

  NT-id-right : ∀ {F G} {α : NatTrans F G} → ≃-NatTrans (α ∘ id _) α
  NT-id-right .transf-eq x = 𝒟.id-right

  constFmor : ∀ {x y} → (x 𝒟.⇒ y) → NatTrans (constF 𝒞 x) (constF 𝒞 y)
  constFmor f .transf _ = f
  constFmor f .natural _ = 𝒟.id-swap

-- Category of functors.
[_⇒_] : ∀ {o₁ m₁ e₁ o₂ m₂ e₂} → Category o₁ m₁ e₁ → Category o₂ m₂ e₂ →
        Category (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂) (o₁ ⊔ m₁ ⊔ m₂ ⊔ e₂) (o₁ ⊔ e₂)
[ 𝒞 ⇒ 𝒟 ] .Category.obj = Functor 𝒞 𝒟
[ 𝒞 ⇒ 𝒟 ] .Category._⇒_ = NatTrans
[ 𝒞 ⇒ 𝒟 ] .Category._≈_ = ≃-NatTrans
[ 𝒞 ⇒ 𝒟 ] .Category.isEquiv = ≃-isEquivalence
[ 𝒞 ⇒ 𝒟 ] .Category.id = id
[ 𝒞 ⇒ 𝒟 ] .Category._∘_ = _∘_
[ 𝒞 ⇒ 𝒟 ] .Category.∘-cong = ∘NT-cong
[ 𝒞 ⇒ 𝒟 ] .Category.id-left = NT-id-left
[ 𝒞 ⇒ 𝒟 ] .Category.id-right = NT-id-right
[ 𝒞 ⇒ 𝒟 ] .Category.assoc = NT-assoc

------------------------------------------------------------------------------
-- Limits.

module _ {o₁ m₁ e₁ o₂ m₂ e₂} {𝒮 : Category o₁ m₁ e₁} {𝒞 : Category o₂ m₂ e₂} where

  private
    module 𝒞 = Category 𝒞

  record IsLimit (D : Functor 𝒮 𝒞) (apex : 𝒞.obj) (cone : NatTrans (constF 𝒮 apex) D)
         : Set (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂) where
    no-eta-equality
    field
      lambda      : ∀ (x : 𝒞.obj) → NatTrans (constF _ x) D → x 𝒞.⇒ apex
      lambda-cong : ∀ {x α β} → ≃-NatTrans α β → lambda x α 𝒞.≈ lambda x β
      lambda-eval : ∀ {x} α → ≃-NatTrans (cone ∘ constFmor (lambda x α)) α
      lambda-ext  : ∀ {x} f → lambda x (cone ∘ constFmor f) 𝒞.≈ f

  record Limit (D : Functor 𝒮 𝒞) : Set (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂) where
    no-eta-equality
    field
      apex    : 𝒞.obj
      cone    : NatTrans (constF 𝒮 apex) D
      isLimit : IsLimit D apex cone
    open IsLimit isLimit public

HasLimits : ∀ {o₁ m₁ e₁ o₂ m₂ e₂} (𝒮 : Category o₁ m₁ e₁) (𝒞 : Category o₂ m₂ e₂) →
            Set (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂)
HasLimits 𝒮 𝒞 = (D : Functor 𝒮 𝒞) → Limit D

-- Streamlined version, sufficient for SP derivation.
record HasLimits' {o₁ m₁ e₁ o₂ m₂ e₂} (𝒮 : Category o₁ m₁ e₁) (𝒞 : Category o₂ m₂ e₂)
       : Set (o₁ ⊔ e₁ ⊔ e₂ ⊔ m₁ ⊔ m₂ ⊔ o₂) where
  private
    module 𝒞 = Category 𝒞
  field
    Π       : Functor 𝒮 𝒞 → 𝒞.obj
    lambdaΠ : ∀ (x : 𝒞.obj) F → NatTrans (constF _ x) F → (x 𝒞.⇒ Π F)
    evalΠ   : ∀ F → NatTrans (constF 𝒮 (Π F)) F

    lambda-cong : ∀ {x} {F : Functor 𝒮 𝒞} {α β : NatTrans (constF 𝒮 x) F} →
                  ≃-NatTrans α β → lambdaΠ x F α 𝒞.≈ lambdaΠ x F β
    lambda-eval : ∀ {x} {F} α → ≃-NatTrans (evalΠ F ∘ constFmor (lambdaΠ x F α)) α
    lambda-ext  : ∀ {x} {F} f → lambdaΠ x F (evalΠ F ∘ constFmor f) 𝒞.≈ f

limits→limits' : ∀ {o₁ m₁ e₁ o₂ m₂ e₂} {𝒮 : Category o₁ m₁ e₁} {𝒞 : Category o₂ m₂ e₂} →
                 HasLimits 𝒮 𝒞 → HasLimits' 𝒮 𝒞
limits→limits' hL .HasLimits'.Π D = hL D .Limit.apex
limits→limits' hL .HasLimits'.lambdaΠ x D α = hL D .Limit.isLimit .IsLimit.lambda x α
limits→limits' hL .HasLimits'.evalΠ D = hL D .Limit.cone
limits→limits' hL .HasLimits'.lambda-cong {x} {D} = hL D .Limit.isLimit .IsLimit.lambda-cong
limits→limits' hL .HasLimits'.lambda-eval {x} {D} = hL D .Limit.isLimit .IsLimit.lambda-eval
limits→limits' hL .HasLimits'.lambda-ext {x} {D} = hL D .Limit.isLimit .IsLimit.lambda-ext
