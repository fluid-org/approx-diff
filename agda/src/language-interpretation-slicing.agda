{-# OPTIONS --prop --postfix-projections --safe #-}

import Data.Fin as Fin
open Fin using (Fin; splitAt)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Sum using ([_,_])
open import Level using (_⊔_)
open import categories
  using (Category; HasTerminal; HasProducts; HasCoproducts; HasStrongCoproducts;
         strong-coproducts→coproducts; HasExponentials)
open import functor using (Functor; StrongFunctor)
open import signature using (Signature)
import polynomial-functor-2 as PF2
import language-syntax-2

module language-interpretation-slicing
  {ℓ} (Sig : Signature ℓ)
  {o m e}
  (𝒞 : Category o m e)
  (𝒞T : HasTerminal 𝒞) (𝒞P : HasProducts 𝒞) (𝒞SC : HasStrongCoproducts 𝒞 𝒞P)
  (𝒞E : HasExponentials 𝒞 𝒞P)
  (T  : StrongFunctor 𝒞P)
  (let open PF2 𝒞T 𝒞P 𝒞SC T hiding (_+_; _×_))
  (Mu : HasMu)
  (⟦sort⟧ : Signature.sort Sig → Category.obj 𝒞)
  where

open Category 𝒞
open HasTerminal 𝒞T renaming (witness to 𝟙)
open HasProducts 𝒞P
open HasCoproducts (strong-coproducts→coproducts 𝒞T 𝒞SC)
open HasExponentials 𝒞E renaming (exp to _⟦→⟧_)
open language-syntax-2 Sig
open HasMu Mu

T-obj : obj → obj
T-obj = Functor.fobj (StrongFunctor.F T)

mutual
  ⟦_⟧ty : ∀ {Δ} → type Δ → (Fin Δ → obj) → obj
  ⟦ var i ⟧ty     δ = δ i
  ⟦ unit ⟧ty      δ = T-obj 𝟙
  ⟦ base s ⟧ty    δ = T-obj (⟦sort⟧ s)
  ⟦ σ [+] τ ⟧ty δ = T-obj (coprod (⟦ σ ⟧ty δ) (⟦ τ ⟧ty δ))
  ⟦ σ [×] τ ⟧ty δ = T-obj (prod   (⟦ σ ⟧ty δ) (⟦ τ ⟧ty δ))
  ⟦ σ [→] τ ⟧ty δ = T-obj (⟦ σ ⟧ty (λ ()) ⟦→⟧ ⟦ τ ⟧ty (λ ()))
  ⟦ μ τ ⟧ty     δ = μ-obj (as-poly τ δ) (λ ())

  as-poly : ∀ {Δ n} → type (n + Δ) → (Fin Δ → obj) → Poly n
  as-poly {Δ} {n} (var i) δ = [ Poly.var , (λ j → Poly.const (δ j)) ] (splitAt n i)
  as-poly unit       δ = Poly.T∘ Poly.const 𝟙
  as-poly (base s)   δ = Poly.T∘ Poly.const (⟦sort⟧ s)
  as-poly (σ [+] τ)  δ = Poly.T∘ (as-poly σ δ Poly.+ as-poly τ δ)
  as-poly (σ [×] τ)  δ = Poly.T∘ (as-poly σ δ Poly.× as-poly τ δ)
  as-poly (σ [→] τ)  δ = Poly.T∘ Poly.const (⟦ σ ⟧ty (λ ()) ⟦→⟧ ⟦ τ ⟧ty (λ ()))
  as-poly (μ τ)      δ = Poly.μ (as-poly τ δ)
