{-# OPTIONS --prop --postfix-projections --safe #-}

module strings where

open import Level using (0ℓ)
open import Data.Product using (_,_)
open import Data.String using (String; _≟_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import prop using (LiftS; liftS; _,_)
open import prop-setoid using (Setoid; IsEquivalence; ⊗-setoid; 𝟙; +-setoid) renaming (_⇒_ to _⇒s_)

Str : Setoid 0ℓ 0ℓ
Str .Setoid.Carrier = String
Str .Setoid._≈_ x y = LiftS 0ℓ (x ≡ y)
Str .Setoid.isEquivalence .IsEquivalence.refl = liftS refl
Str .Setoid.isEquivalence .IsEquivalence.sym (liftS e) = liftS (sym e)
Str .Setoid.isEquivalence .IsEquivalence.trans (liftS e₁) (liftS e₂) = liftS (trans e₁ e₂)

private
  eq : String → String → Setoid.Carrier (+-setoid (𝟙 {0ℓ} {0ℓ}) 𝟙)
  eq x y with x ≟ y
  ... | yes _ = inj₁ _
  ... | no  _ = inj₂ _

equal-string : ⊗-setoid Str Str ⇒s +-setoid (𝟙 {0ℓ} {0ℓ}) (𝟙 {0ℓ} {0ℓ})
equal-string ._⇒s_.func (x , y) = eq x y
equal-string ._⇒s_.func-resp-≈ {x , y} (liftS refl , liftS refl) =
  Setoid.isEquivalence (+-setoid (𝟙 {0ℓ} {0ℓ}) 𝟙) .IsEquivalence.refl {eq x y}
