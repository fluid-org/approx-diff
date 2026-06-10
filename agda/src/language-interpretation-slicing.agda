{-# OPTIONS --prop --postfix-projections --safe #-}

import Data.Fin as Fin
open Fin using (Fin; splitAt)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Sum using ([_,_])
open import Level using (_⊔_)
open import categories
  using (Category; HasTerminal; HasProducts; HasCoproducts; HasStrongCoproducts;
         strong-coproducts→coproducts; HasExponentials)
open import functor using (Functor; StrongMonad)
open import signature using (Signature)
open import polynomial-functor-2 using (Poly; module Interp)
import language-syntax-2

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

open Category 𝒞
open HasTerminal 𝒞T renaming (witness to 𝟙)
open HasProducts 𝒞P
open HasCoproducts (strong-coproducts→coproducts 𝒞T 𝒞SC)
open HasExponentials 𝒞E renaming (exp to _⟹_)
open language-syntax-2 Sig
open HasMu Mu

T-obj : obj → obj
T-obj = Functor.fobj (StrongMonad.F T)

mutual
  ⟦_⟧ty : ∀ {Δ} → type Δ → (Fin Δ → obj) → obj
  ⟦ var i ⟧ty     δ = δ i
  ⟦ unit ⟧ty      δ = T-obj 𝟙
  ⟦ base s ⟧ty    δ = T-obj (⟦sort⟧ s)
  ⟦ τ₁ [+] τ₂ ⟧ty δ = T-obj (coprod (⟦ τ₁ ⟧ty δ) (⟦ τ₂ ⟧ty δ))
  ⟦ τ₁ [×] τ₂ ⟧ty δ = T-obj (prod   (⟦ τ₁ ⟧ty δ) (⟦ τ₂ ⟧ty δ))
  ⟦ τ₁ [→] τ₂ ⟧ty δ = T-obj (⟦ τ₁ ⟧ty (λ ()) ⟹ ⟦ τ₂ ⟧ty (λ ()))
  ⟦ μ τ ⟧ty       δ = μ-obj (build-poly τ δ) (λ ())

  build-poly : ∀ {Δ n} → type (n + Δ) → (Fin Δ → obj) → Poly 𝒞 (StrongMonad.F T) n
  build-poly {Δ} {n} (var i) δ = [ Poly.var , (λ j → Poly.const (δ j)) ] (splitAt n i)
  build-poly unit         δ = Poly.T∘ Poly.const 𝟙
  build-poly (base s)     δ = Poly.T∘ Poly.const (⟦sort⟧ s)
  build-poly (τ₁ [+] τ₂)  δ = Poly.T∘ (build-poly τ₁ δ Poly.+ build-poly τ₂ δ)
  build-poly (τ₁ [×] τ₂)  δ = Poly.T∘ (build-poly τ₁ δ Poly.× build-poly τ₂ δ)
  build-poly (τ₁ [→] τ₂)  δ = Poly.T∘ Poly.const (⟦ τ₁ ⟧ty (λ ()) ⟹ ⟦ τ₂ ⟧ty (λ ()))
  build-poly (μ τ)        δ = Poly.μ (build-poly τ δ)
