{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.Nat using (suc)
open import Data.Fin using (Fin)
open import categories using (Category; HasTerminal; HasProducts; HasStrongCoproducts)
open import functor using (Functor)
import polynomial-functor-2

module polynomial-functor-2.map
  {o₁ m₁ e₁ o₂ m₂ e₂} {𝒞 : Category o₁ m₁ e₁} {𝒟 : Category o₂ m₂ e₂}
  (𝒞T : HasTerminal 𝒞) (𝒞P : HasProducts 𝒞) (𝒞SCP : HasStrongCoproducts 𝒞 𝒞P)
  (𝒟T : HasTerminal 𝒟) (𝒟P : HasProducts 𝒟) (𝒟SCP : HasStrongCoproducts 𝒟 𝒟P)
  (F : Functor 𝒞 𝒟)
  where

open Functor

private
  module P𝒞 = polynomial-functor-2 𝒞T 𝒞P 𝒞SCP
  module P𝒟 = polynomial-functor-2 𝒟T 𝒟P 𝒟SCP

-- Action of the functor on polynomials: apply F at the const leaves.
Poly-map : ∀ {n} → P𝒞.Poly n → P𝒟.Poly n
Poly-map (P𝒞.const A) = P𝒟.const (F .fobj A)
Poly-map (P𝒞.var i)   = P𝒟.var i
Poly-map (P P𝒞.+ Q)   = Poly-map P P𝒟.+ Poly-map Q
Poly-map (P P𝒞.× Q)   = Poly-map P P𝒟.× Poly-map Q
Poly-map (P𝒞.μ P)     = P𝒟.μ (Poly-map P)

-- F preserves μ-types: each μ-object maps, up to isomorphism, to the μ-object of
-- the image polynomial in the image environment.
Preserves-μ : P𝒞.HasMu → P𝒟.HasMu → Set _
Preserves-μ 𝒞Mu 𝒟Mu =
  ∀ {n} (P : P𝒞.Poly (suc n)) (δ : Fin n → Category.obj 𝒞) →
  Category.Iso 𝒟 (F .fobj (P𝒞.HasMu.μ-obj 𝒞Mu P δ))
                 (P𝒟.HasMu.μ-obj 𝒟Mu (Poly-map P) (λ i → F .fobj (δ i)))
