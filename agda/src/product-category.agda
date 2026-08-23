{-# OPTIONS --postfix-projections --prop --safe #-}

module product-category where

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Level using (_⊔_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import prop using (_∧_; _,_; proj₁; proj₂)
open import prop-setoid using (IsEquivalence)
open import categories using (Category; HasProducts; HasTerminal)
open import functor using (Functor; Limit; IsLimit; Colimit; IsColimit; _∘F_; NatTrans; ≃-NatTrans)

open IsEquivalence

_^_ : ∀ {o m e} → Category o m e → ℕ → Category o m e
(𝒞 ^ n) .Category.obj           = Fin n → Category.obj 𝒞
(𝒞 ^ n) .Category._⇒_ δ δ'      = ∀ i → Category._⇒_ 𝒞 (δ i) (δ' i)
(𝒞 ^ n) .Category._≈_ fs gs     = ∀ i → Category._≈_ 𝒞 (fs i) (gs i)
(𝒞 ^ n) .Category.isEquiv .refl                 i = Category.isEquiv 𝒞 .refl
(𝒞 ^ n) .Category.isEquiv .sym fs≈gs            i = Category.isEquiv 𝒞 .sym (fs≈gs i)
(𝒞 ^ n) .Category.isEquiv .trans fs≈gs gs≈hs    i = Category.isEquiv 𝒞 .trans (fs≈gs i) (gs≈hs i)
(𝒞 ^ n) .Category.id δ                          i = Category.id 𝒞 (δ i)
(𝒞 ^ n) .Category._∘_ fs gs                     i = Category._∘_ 𝒞 (fs i) (gs i)
(𝒞 ^ n) .Category.∘-cong fs≈fs' gs≈gs'          i = Category.∘-cong 𝒞 (fs≈fs' i) (gs≈gs' i)
(𝒞 ^ n) .Category.id-left                       i = Category.id-left 𝒞
(𝒞 ^ n) .Category.id-right                      i = Category.id-right 𝒞
(𝒞 ^ n) .Category.assoc fs gs hs                i = Category.assoc 𝒞 (fs i) (gs i) (hs i)

module _ {o₁ m₁ e₁ o₂ m₂ e₂} (𝒞 : Category o₁ m₁ e₁) (𝒟 : Category o₂ m₂ e₂) where

  private
    module 𝒞 = Category 𝒞
    module 𝒟 = Category 𝒟

  open IsEquivalence

  product : Category (o₁ ⊔ o₂) (m₁ ⊔ m₂) (e₁ ⊔ e₂)
  product .Category.obj = 𝒞.obj × 𝒟.obj
  product .Category._⇒_ (x₁ , y₁) (x₂ , y₂) = (x₁ 𝒞.⇒ x₂) × (y₁ 𝒟.⇒ y₂)
  product .Category._≈_ (f₁ , g₁) (f₂ , g₂) = (f₁ 𝒞.≈ f₂) ∧ (g₁ 𝒟.≈ g₂)
  product .Category.isEquiv .refl = 𝒞.isEquiv . refl , 𝒟.isEquiv .refl
  product .Category.isEquiv .sym (f₁≃f₂ , g₁≃g₂) = 𝒞.isEquiv .sym f₁≃f₂ , 𝒟.isEquiv .sym g₁≃g₂
  product .Category.isEquiv .trans (f₁≃f₂ , g₁≃g₂) (f₂≃f₃ , g₂≃g₃) =
    𝒞.isEquiv .trans f₁≃f₂ f₂≃f₃ , 𝒟.isEquiv .trans g₁≃g₂ g₂≃g₃
  product .Category.id (x , y) = 𝒞.id x , 𝒟.id y
  product .Category._∘_ (f₁ , f₂) (g₁ , g₂) = (f₁ 𝒞.∘ g₁) , (f₂ 𝒟.∘ g₂)
  product .Category.∘-cong (f₁≃f₁' , f₂≃f₂') (g₁≃g₁' , g₂≃g₂') = 𝒞.∘-cong f₁≃f₁' g₁≃g₁' , 𝒟.∘-cong f₂≃f₂' g₂≃g₂'
  product .Category.id-left = 𝒞.id-left , 𝒟.id-left
  product .Category.id-right = 𝒞.id-right , 𝒟.id-right
  product .Category.assoc (f₁ , f₂) (g₁ , g₂) (h₁ , h₂) = 𝒞.assoc f₁ g₁ h₁ , 𝒟.assoc f₂ g₂ h₂

module _ {o₁ m₁ e₁ o₂ m₂ e₂} {𝒞 : Category o₁ m₁ e₁} {𝒟 : Category o₂ m₂ e₂} where

  open Functor

  private
    module 𝒞 = Category 𝒞
    module 𝒟 = Category 𝒟

  pairF : ∀ {o₃ m₃ e₃} {ℰ : Category o₃ m₃ e₃} →
          Functor ℰ 𝒞 → Functor ℰ 𝒟 → Functor ℰ (product 𝒞 𝒟)
  pairF F G .fobj e = (F .fobj e) , (G .fobj e)
  pairF F G .fmor f = (F .fmor f) , (G .fmor f)
  pairF F G .fmor-cong f₁≈f₂ = (F .fmor-cong f₁≈f₂) , (G .fmor-cong f₁≈f₂)
  pairF F G .fmor-id = F .fmor-id , G .fmor-id
  pairF F G .fmor-comp f g = F .fmor-comp f g , G .fmor-comp f g

  project₁ : Functor (product 𝒞 𝒟) 𝒞
  project₁ .fobj = proj₁
  project₁ .fmor = proj₁
  project₁ .fmor-cong = proj₁
  project₁ .fmor-id = 𝒞.≈-refl
  project₁ .fmor-comp f g = 𝒞.≈-refl

  project₂ : Functor (product 𝒞 𝒟) 𝒟
  project₂ .fobj = proj₂
  project₂ .fmor = proj₂
  project₂ .fmor-cong = proj₂
  project₂ .fmor-id = 𝒟.≈-refl
  project₂ .fmor-comp f g = 𝒟.≈-refl

  -- FIXME: natural isomorphisms to show that this is a product

  module _ {o₃ m₃ e₃} (𝒮 : Category o₃ m₃ e₃) where

    open Limit
    open IsLimit
    open Colimit
    open IsColimit
    open NatTrans
    open ≃-NatTrans

    product-limit : (D : Functor 𝒮 (product 𝒞 𝒟)) →
                    Limit (project₁ ∘F D) → Limit (project₂ ∘F D) → Limit D
    product-limit D limit𝒞 limit𝒟 .apex = limit𝒞 .apex , limit𝒟 .apex
    product-limit D limit𝒞 limit𝒟 .cone .transf s = limit𝒞 .cone .transf s , limit𝒟 .cone .transf s
    product-limit D limit𝒞 limit𝒟 .cone .natural f = limit𝒞 .cone .natural f , limit𝒟 .cone .natural f
    product-limit D limit𝒞 limit𝒟 .isLimit .lambda (x , y) α =
      limit𝒞 .lambda x (record { transf = λ s → α .transf s .proj₁ ; natural = λ f → α .natural f .proj₁ }) ,
      limit𝒟 .lambda y (record { transf = λ s → α .transf s .proj₂ ; natural = λ f → α .natural f .proj₂ })
    product-limit D limit𝒞 limit𝒟 .isLimit .lambda-cong α≃β =
      limit𝒞 .lambda-cong (record { transf-eq = λ s → α≃β .transf-eq s .proj₁ }) ,
      limit𝒟 .lambda-cong (record { transf-eq = λ s → α≃β .transf-eq s .proj₂ })
    product-limit D limit𝒞 limit𝒟 .isLimit .lambda-eval α .transf-eq s =
      limit𝒞 .lambda-eval (record { transf = λ s → α .transf s .proj₁ ; natural = _ }) .transf-eq s ,
      limit𝒟 .lambda-eval (record { transf = λ s → α .transf s .proj₂ ; natural = _ }) .transf-eq s
    product-limit D limit𝒞 limit𝒟 .isLimit .lambda-ext f =
      𝒞.≈-trans
       (limit𝒞 .lambda-cong (record { transf-eq = λ _ → 𝒞.≈-refl }))
       (limit𝒞 .lambda-ext (f .proj₁)) ,
      𝒟.≈-trans
       (limit𝒟 .lambda-cong (record { transf-eq = λ _ → 𝒟.≈-refl }))
       (limit𝒟 .lambda-ext (f .proj₂))

    product-colimit : (D : Functor 𝒮 (product 𝒞 𝒟)) →
                      Colimit (project₁ ∘F D) → Colimit (project₂ ∘F D) → Colimit D
    product-colimit D colimit𝒞 colimit𝒟 .apex = colimit𝒞 .apex , colimit𝒟 .apex
    product-colimit D colimit𝒞 colimit𝒟 .cocone .transf s = colimit𝒞 .cocone .transf s , colimit𝒟 .cocone .transf s
    product-colimit D colimit𝒞 colimit𝒟 .cocone .natural f = colimit𝒞 .cocone .natural f , colimit𝒟 .cocone .natural f
    product-colimit D colimit𝒞 colimit𝒟 .isColimit .colambda (x , y) α =
      colimit𝒞 .colambda x (record { transf = λ s → α .transf s .proj₁ ; natural = λ f → α .natural f .proj₁ }) ,
      colimit𝒟 .colambda y (record { transf = λ s → α .transf s .proj₂ ; natural = λ f → α .natural f .proj₂ })
    product-colimit D colimit𝒞 colimit𝒟 .isColimit .colambda-cong α≃β =
      colimit𝒞 .colambda-cong (record { transf-eq = λ s → α≃β .transf-eq s .proj₁ }) ,
      colimit𝒟 .colambda-cong (record { transf-eq = λ s → α≃β .transf-eq s .proj₂ })
    product-colimit D colimit𝒞 colimit𝒟 .isColimit .colambda-coeval (x , y) α .transf-eq s =
      colimit𝒞 .colambda-coeval x (record { transf = λ s → α .transf s .proj₁ ; natural = _ }) .transf-eq s ,
      colimit𝒟 .colambda-coeval y (record { transf = λ s → α .transf s .proj₂ ; natural = _ }) .transf-eq s
    product-colimit D colimit𝒞 colimit𝒟 .isColimit .colambda-ext (x , y) f =
      𝒞.≈-trans
       (colimit𝒞 .colambda-cong (record { transf-eq = λ _ → 𝒞.≈-refl }))
       (colimit𝒞 .colambda-ext x (f .proj₁)) ,
      𝒟.≈-trans
       (colimit𝒟 .colambda-cong (record { transf-eq = λ _ → 𝒟.≈-refl }))
       (colimit𝒟 .colambda-ext y (f .proj₂))

  module _ (𝒞P : HasProducts 𝒞) (𝒟P : HasProducts 𝒟) where

    private
      module 𝒞P = HasProducts 𝒞P
      module 𝒟P = HasProducts 𝒟P

    product-products : HasProducts (product 𝒞 𝒟)
    product-products .HasProducts.prod (x₁ , y₁) (x₂ , y₂) = 𝒞P.prod x₁ x₂ , 𝒟P.prod y₁ y₂
    product-products .HasProducts.p₁ = 𝒞P.p₁ , 𝒟P.p₁
    product-products .HasProducts.p₂ = 𝒞P.p₂ , 𝒟P.p₂
    product-products .HasProducts.pair (f₁ , f₂) (g₁ , g₂) = 𝒞P.pair f₁ g₁ , 𝒟P.pair f₂ g₂
    product-products .HasProducts.pair-cong (eq₁ , eq₂) (eq₃ , eq₄) = 𝒞P.pair-cong eq₁ eq₃ , 𝒟P.pair-cong eq₂ eq₄
    product-products .HasProducts.pair-p₁ (f₁ , f₂) (g₁ , g₂) = 𝒞P.pair-p₁ f₁ g₁ , 𝒟P.pair-p₁ f₂ g₂
    product-products .HasProducts.pair-p₂ (f₁ , f₂) (g₁ , g₂) = 𝒞P.pair-p₂ f₁ g₁ , 𝒟P.pair-p₂ f₂ g₂
    product-products .HasProducts.pair-ext (f₁ , f₂) = 𝒞P.pair-ext f₁ , 𝒟P.pair-ext f₂

  module _ (𝒞T : HasTerminal 𝒞) (𝒟T : HasTerminal 𝒟) where

    private
      module 𝒞T = HasTerminal 𝒞T
      module 𝒟T = HasTerminal 𝒟T

    product-terminal : HasTerminal (product 𝒞 𝒟)
    product-terminal .HasTerminal.witness = 𝒞T.witness , 𝒟T.witness
    product-terminal .HasTerminal.is-terminal .categories.IsTerminal.to-terminal = 𝒞T.to-terminal , 𝒟T.to-terminal
    product-terminal .HasTerminal.is-terminal .categories.IsTerminal.to-terminal-ext (f , g) = (𝒞T.to-terminal-ext f) , (𝒟T.to-terminal-ext g)
