{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (suc; _⊔_)
open import Data.List using (List; []; _∷_; _++_)
open import categories using (Category; HasTerminal; HasProducts; IsProduct; IsTerminal; Product)

module signature where

record Signature ℓ : Set (suc ℓ) where
  field
    sort : Set ℓ
    op   : List sort → sort → Set ℓ
    rel  : List sort → Set ℓ

-- The product of a list of objects. Parameterised by the terminal object and products alone, so
-- that interpretations differing only elsewhere share their argument products.
finite-product : ∀ {o m e} {𝒞 : Category o m e} → HasTerminal 𝒞 → HasProducts 𝒞 →
                 ∀ {ℓ} {A : Set ℓ} → (A → Category.obj 𝒞) → List A → Category.obj 𝒞
finite-product T P i []       = HasTerminal.witness T
finite-product T P i (x ∷ xs) = HasProducts.prod P (i x) (finite-product T P i xs)


-- Models of signatures live in finite product (FIXME: monoidal?)
-- categories with a specified object of truth values.
record PointedFPCat o m e : Set (suc (o ⊔ m ⊔ e)) where
  field
    cat      : Category o m e
    terminal : HasTerminal cat
    products : HasProducts cat
    Ω        : Category.obj cat

  open Category cat public
  open HasTerminal terminal renaming (witness to 𝟙) public
  open HasProducts products renaming (pair to ⟨_,_⟩; prod to _×_) public

  field
    -- The object interpreting the unit type, with its point. It is the terminal object when the
    -- unit type has no positions of its own, and a larger object when it has.
    𝟙ty     : obj
    unit-pt : 𝟙 ⇒ 𝟙ty

  list→product : ∀ {ℓ} {A : Set ℓ} → (A → obj) → List A → obj
  list→product = finite-product terminal products

-- A category whose unit type has no positions of its own.
PFPC[_,_,_,_] : ∀ {o m e} (𝒞 : Category o m e) (T : HasTerminal 𝒞) (P : HasProducts 𝒞)
                (Ω : Category.obj 𝒞) → PointedFPCat o m e
PFPC[ 𝒞 , T , P , Ω ] .PointedFPCat.cat = 𝒞
PFPC[ 𝒞 , T , P , Ω ] .PointedFPCat.terminal = T
PFPC[ 𝒞 , T , P , Ω ] .PointedFPCat.products = P
PFPC[ 𝒞 , T , P , Ω ] .PointedFPCat.Ω = Ω
PFPC[ 𝒞 , T , P , Ω ] .PointedFPCat.𝟙ty = HasTerminal.witness T
PFPC[ 𝒞 , T , P , Ω ] .PointedFPCat.unit-pt = Category.id 𝒞 _

record Model {ℓ o m e} (𝒞 : PointedFPCat o m e) (Sig : Signature ℓ) : Set (ℓ ⊔ o ⊔ m) where
  open PointedFPCat 𝒞
  open Signature Sig
  field
    ⟦sort⟧ : sort → obj
    ⟦op⟧   : ∀ {i o} → op i o → list→product ⟦sort⟧ i ⇒ ⟦sort⟧ o
    ⟦rel⟧  : ∀ {i} → rel i → list→product ⟦sort⟧ i ⇒ Ω

  -- FIXME: morphisms of models: for each sort, a morphism between
  --   interpretations, such that all the operations and relations are
  --   preserved.
  --
  --   Get a category of models in the given category.

-- If F : 𝒞 ⇒ 𝒟 is a finite product preserving, point preserving
-- functor, then there is a map of Models : Model 𝒞 Sig → Model 𝒟 Sig
--
-- (and this is functorial.)

open import functor using (Functor)
open import finite-product-functor using (preserve-chosen-products)

module _ {ℓ o₁ m₁ e₁ o₂ m₂ e₂}
         {𝒞 : PointedFPCat o₁ m₁ e₁}
         {𝒟 : PointedFPCat o₂ m₂ e₂}
         (Sig : Signature ℓ)
  where

  private
    module Sig = Signature Sig
    module 𝒞 = PointedFPCat 𝒞
    module 𝒟 = PointedFPCat 𝒟
    module 𝒟P = HasProducts 𝒟.products

  open Model
  open Functor

  module _ (F : Functor 𝒞.cat 𝒟.cat)
           (FT : Category.IsIso 𝒟.cat (HasTerminal.to-terminal 𝒟.terminal {F .fobj (𝒞.terminal .HasTerminal.witness)}))
           (FP : preserve-chosen-products F 𝒞.products 𝒟.products)
           (Ω-mor : F .fobj 𝒞.Ω 𝒟.⇒ 𝒟.Ω)
    where

    open Category.IsIso

    transport-product : (f : Sig.sort → 𝒞.obj) →
        ∀ σs → 𝒟.list→product (λ σ → F .fobj (f σ)) σs 𝒟.⇒ F .fobj (𝒞.list→product f σs)
    transport-product f [] = FT .inverse
    transport-product f (x ∷ σs) = FP .inverse 𝒟.∘ 𝒟P.prod-m (𝒟.id _) (transport-product f σs)

    transport-model : Model 𝒞 Sig → Model 𝒟 Sig
    transport-model M .⟦sort⟧ σ = F .fobj (M .⟦sort⟧ σ)
    transport-model M .⟦op⟧ {σs} {σ} ω =
      F .fmor (M .⟦op⟧ ω) 𝒟.∘ transport-product (M .⟦sort⟧) σs
    transport-model M .⟦rel⟧ {σs} ρ =
      (Ω-mor 𝒟.∘ (F .fmor (M .⟦rel⟧ ρ))) 𝒟.∘ transport-product (M .⟦sort⟧) σs
