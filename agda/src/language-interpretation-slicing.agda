{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (_⊔_)
open import categories
  using (Category; HasTerminal; HasProducts; HasCoproducts; HasStrongCoproducts;
         strong-coproducts→coproducts; HasExponentials)
open import functor using (StrongMonad)
open import signature using (Signature)
open import polynomial-functor-2 using (module Interp)

module language-interpretation-slicing
  {ℓ} (Sig : Signature ℓ)
  {o m e}
  (𝒞 : Category o m e)
  (𝒞T : HasTerminal 𝒞) (𝒞P : HasProducts 𝒞) (𝒞SC : HasStrongCoproducts 𝒞 𝒞P)
  (𝒞E : HasExponentials 𝒞 𝒞P)
  (T  : StrongMonad 𝒞P)
  (let open Interp {T = StrongMonad.F T} 𝒞T 𝒞P 𝒞SC)
  (Mu : HasMu)
  (⟦sort⟧ : Signature.sort Sig → Category.obj 𝒞)
  where
