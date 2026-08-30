{-# OPTIONS --prop --postfix-projections --safe #-}

module label where

open import Level using (0ℓ)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import prop using (LiftS; liftS; _,_)
open import prop-setoid using (Setoid; IsEquivalence; ⊗-setoid; 𝟙; +-setoid) renaming (_⇒_ to _⇒s_)

data label : Set where
  a b c d : label

Label : Setoid 0ℓ 0ℓ
Label .Setoid.Carrier = label
Label .Setoid._≈_ x y = LiftS 0ℓ (x ≡ y)
Label .Setoid.isEquivalence .IsEquivalence.refl = liftS refl
Label .Setoid.isEquivalence .IsEquivalence.sym (liftS e) = liftS (sym e)
Label .Setoid.isEquivalence .IsEquivalence.trans (liftS e₁) (liftS e₂) = liftS (trans e₁ e₂)

equal-label : ⊗-setoid Label Label ⇒s +-setoid (𝟙 {0ℓ} {0ℓ}) (𝟙 {0ℓ} {0ℓ})
equal-label ._⇒s_.func (a , a) = inj₁ _
equal-label ._⇒s_.func (b , b) = inj₁ _
equal-label ._⇒s_.func (c , c) = inj₁ _
equal-label ._⇒s_.func (d , d) = inj₁ _
equal-label ._⇒s_.func (_ , _) = inj₂ _
equal-label ._⇒s_.func-resp-≈ {x , y} (liftS refl , liftS refl) =
  Setoid.isEquivalence (+-setoid (𝟙 {0ℓ} {0ℓ}) 𝟙) .IsEquivalence.refl {equal-label ._⇒s_.func (x , y)}
