{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (_⊔_; suc)
open import categories using (Category; setoid→category)
open import prop-setoid using (Setoid)
open import functor using (Functor; HasColimits; Colimit; NatTrans)

-- Stability of set-indexed coproducts: pulling a coproduct decomposition back
-- along a morphism yields a decomposition over the same index, one summand
-- pulled back per index. This is the set-indexed form of the binary stability
-- of `stable-coproducts`, the finite case being the two-element index.
module stable-coproducts-indexed
  {o m e os es} {𝒞 : Category o m e}
  (LC : ∀ (S : Setoid os es) → HasColimits (setoid→category S) 𝒞)
  where

private
  module 𝒞 = Category 𝒞

open 𝒞.Iso
open Colimit
open NatTrans
open Functor

∐ : ∀ (S : Setoid os es) (D : Functor (setoid→category S) 𝒞) → 𝒞.obj
∐ S D = LC S D .apex

inj : ∀ {S} (D : Functor (setoid→category S) 𝒞) (s : S .Setoid.Carrier) →
      D .fobj s 𝒞.⇒ ∐ S D
inj {S} D s = LC S D .cocone .transf s

record IdxStableBits
    {S : Setoid os es} {D : Functor (setoid→category S) 𝒞} {x y}
    (f : 𝒞.Iso (∐ S D) x) (g : y 𝒞.⇒ x) : Set (o ⊔ m ⊔ e ⊔ os ⊔ es) where
  field
    E   : Functor (setoid→category S) 𝒞
    leg : ∀ (s : S .Setoid.Carrier) → E .fobj s 𝒞.⇒ D .fobj s
    h   : 𝒞.Iso (∐ S E) y
    eq  : ∀ (s : S .Setoid.Carrier) →
          (f .fwd 𝒞.∘ (inj D s 𝒞.∘ leg s)) 𝒞.≈ (g 𝒞.∘ (h .fwd 𝒞.∘ inj E s))

IdxStable : Set (o ⊔ m ⊔ e ⊔ suc os ⊔ suc es)
IdxStable = ∀ {S D x y} f g → IdxStableBits {S} {D} {x} {y} f g
