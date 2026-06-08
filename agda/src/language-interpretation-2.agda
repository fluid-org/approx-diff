{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.Fin using (Fin; splitAt) renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Sum using ([_,_])
open import Level using (_⊔_)
open import categories
  using (Category; HasTerminal; HasProducts; HasCoproducts; HasStrongCoproducts;
         strong-coproducts→coproducts; HasExponentials)
open import signature using (Signature)
open import polynomial-functor-2 using (Poly; module Interp)
import language-syntax-2

module language-interpretation-2
  {ℓ} (Sig : Signature ℓ)
  {o m e}
  (𝒞 : Category o m e)
  (𝒞T : HasTerminal 𝒞) (𝒞P : HasProducts 𝒞) (𝒞SC : HasStrongCoproducts 𝒞 𝒞P)
  (𝒞E : HasExponentials 𝒞 𝒞P)
  (let open Interp 𝒞T 𝒞P 𝒞SC)
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

mutual
  ⟦_⟧ty : ∀ {Δ} → type Δ → (Fin Δ → obj) → obj
  ⟦ var i ⟧ty     val = val i
  ⟦ unit ⟧ty      val = 𝟙
  ⟦ base s ⟧ty    val = ⟦sort⟧ s
  ⟦ τ₁ [+] τ₂ ⟧ty val = coprod (⟦ τ₁ ⟧ty val) (⟦ τ₂ ⟧ty val)
  ⟦ τ₁ [×] τ₂ ⟧ty val = prod   (⟦ τ₁ ⟧ty val) (⟦ τ₂ ⟧ty val)
  ⟦ τ₁ [→] τ₂ ⟧ty val = ⟦ τ₁ ⟧ty (λ ()) ⟹ ⟦ τ₂ ⟧ty (λ ())
  ⟦ μ τ ⟧ty       val = μ-poly (build-poly τ val) (λ ())

  build-poly : ∀ {Δ n} → type (n + Δ) → (Fin Δ → obj) → Poly 𝒞 n
  build-poly {Δ} {n} (var i) val = [ Poly.var , (λ j → Poly.const (val j)) ] (splitAt n i)
  build-poly unit         val = Poly.const 𝟙
  build-poly (base s)     val = Poly.const (⟦sort⟧ s)
  build-poly (τ₁ [+] τ₂)  val = build-poly τ₁ val Poly.+ build-poly τ₂ val
  build-poly (τ₁ [×] τ₂)  val = build-poly τ₁ val Poly.× build-poly τ₂ val
  build-poly (τ₁ [→] τ₂)  val = Poly.const (⟦ τ₁ ⟧ty (λ ()) ⟹ ⟦ τ₂ ⟧ty (λ ()))
  build-poly (μ τ)        val = Poly.μ (build-poly τ val)
