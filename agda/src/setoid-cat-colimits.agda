{-# OPTIONS --prop --postfix-projections --safe #-}

-- The cocompleteness structure of SetoidCat: initial object, strong coproducts, ω-colimits, and
-- cocontinuous products. This is the standalone half of the factorisation — instantiating colimit-mu-types
-- against it builds μ-types of polynomial functors on setoids (the index μ-types of the Fam construction).

open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import prop using (_,_)
open import categories
  using (Category; HasInitial; IsInitial; HasProducts; HasStrongCoproducts)
open import prop-setoid
  using (Setoid; 𝟘; from-𝟘; from-𝟘-unique; +-setoid; ⊗-setoid; case; inject₁; inject₂)
  renaming (_⇒_ to _⇒s_; _≃m_ to _≈s_)
open import setoid-cat using (SetoidCat; Setoid-products)

open Setoid
open _⇒s_
open _≈s_

module setoid-cat-colimits where

module _ o e where
  private
    𝒮 = SetoidCat o e
  open Category 𝒮
  open HasInitial
  open IsInitial
  open HasStrongCoproducts

  Setoid-initial : HasInitial 𝒮
  Setoid-initial .witness = 𝟘
  Setoid-initial .is-initial .from-initial = from-𝟘
  Setoid-initial .is-initial .from-initial-ext f = from-𝟘-unique from-𝟘 f

  Setoid-strongCoproducts : HasStrongCoproducts 𝒮 (Setoid-products o e)
  Setoid-strongCoproducts .coprod = +-setoid
  Setoid-strongCoproducts .in₁ = inject₁
  Setoid-strongCoproducts .in₂ = inject₂
  Setoid-strongCoproducts .copair = case
  Setoid-strongCoproducts .copair-cong f₁≈f₂ g₁≈g₂ .func-eq {_ , inj₁ _} {_ , inj₁ _} (w≈ , x≈) = f₁≈f₂ .func-eq (w≈ , x≈)
  Setoid-strongCoproducts .copair-cong f₁≈f₂ g₁≈g₂ .func-eq {_ , inj₂ _} {_ , inj₂ _} (w≈ , y≈) = g₁≈g₂ .func-eq (w≈ , y≈)
  Setoid-strongCoproducts .copair-in₁ f g .func-eq (w≈ , x≈) = f .func-resp-≈ (w≈ , x≈)
  Setoid-strongCoproducts .copair-in₂ f g .func-eq (w≈ , y≈) = g .func-resp-≈ (w≈ , y≈)
  Setoid-strongCoproducts .copair-ext h .func-eq {_ , inj₁ _} {_ , inj₁ _} (w≈ , x≈) = h .func-resp-≈ (w≈ , x≈)
  Setoid-strongCoproducts .copair-ext h .func-eq {_ , inj₂ _} {_ , inj₂ _} (w≈ , y≈) = h .func-resp-≈ (w≈ , y≈)
