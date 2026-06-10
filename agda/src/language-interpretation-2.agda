{-# OPTIONS --prop --postfix-projections --safe #-}

import Data.Fin as Fin
open Fin using (Fin; splitAt)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Sum using ([_,_])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst)
open import Level using (_⊔_)
open import categories
  using (Category; HasTerminal; HasProducts; HasCoproducts; HasStrongCoproducts;
         strong-coproducts→coproducts; HasExponentials)
open import functor using (Id)
open import signature using (Signature; Model; PointedFPCat; PFPC[_,_,_,_])
open import polynomial-functor-2 using (Poly; module Interp)
import language-syntax-2

module language-interpretation-2
  {ℓ} (Sig : Signature ℓ)
  {o m e}
  (𝒞 : Category o m e)
  (𝒞T : HasTerminal 𝒞) (𝒞P : HasProducts 𝒞) (𝒞SC : HasStrongCoproducts 𝒞 𝒞P)
  (𝒞E : HasExponentials 𝒞 𝒞P)
  (let open Interp {T = Id} 𝒞T 𝒞P 𝒞SC)
  (Mu : HasMu)
  (let Bool = HasCoproducts.coprod (strong-coproducts→coproducts 𝒞T 𝒞SC)
              (HasTerminal.witness 𝒞T) (HasTerminal.witness 𝒞T))
  (Int : Model PFPC[ 𝒞 , 𝒞T , 𝒞P , Bool ] Sig)
  where

open Category 𝒞
open HasTerminal 𝒞T renaming (witness to 𝟙)
open HasProducts 𝒞P renaming (pair to ⟨_,_⟩)
open HasCoproducts (strong-coproducts→coproducts 𝒞T 𝒞SC)
open HasExponentials 𝒞E renaming (exp to _⟹_)
open language-syntax-2 Sig
open HasMu Mu
open Model Int

mutual
  ⟦_⟧ty : ∀ {Δ} → type Δ → (Fin Δ → obj) → obj
  ⟦ var i ⟧ty     δ = δ i
  ⟦ unit ⟧ty      δ = 𝟙
  ⟦ base s ⟧ty    δ = ⟦sort⟧ s
  ⟦ τ₁ [+] τ₂ ⟧ty δ = coprod (⟦ τ₁ ⟧ty δ) (⟦ τ₂ ⟧ty δ)
  ⟦ τ₁ [×] τ₂ ⟧ty δ = prod (⟦ τ₁ ⟧ty δ) (⟦ τ₂ ⟧ty δ)
  ⟦ τ₁ [→] τ₂ ⟧ty δ = ⟦ τ₁ ⟧ty (λ ()) ⟹ ⟦ τ₂ ⟧ty (λ ())
  ⟦ μ τ ⟧ty       δ = μ-obj (build-poly τ δ) (λ ())

  build-poly : ∀ {Δ n} → type (n + Δ) → (Fin Δ → obj) → Poly 𝒞 Id n
  build-poly {Δ} {n} (var i) δ = [ Poly.var , (λ j → Poly.const (δ j)) ] (splitAt n i)
  build-poly unit         δ = Poly.const 𝟙
  build-poly (base s)     δ = Poly.const (⟦sort⟧ s)
  build-poly (τ₁ [+] τ₂)  δ = build-poly τ₁ δ Poly.+ build-poly τ₂ δ
  build-poly (τ₁ [×] τ₂)  δ = build-poly τ₁ δ Poly.× build-poly τ₂ δ
  build-poly (τ₁ [→] τ₂)  δ = Poly.const (⟦ τ₁ ⟧ty (λ ()) ⟹ ⟦ τ₂ ⟧ty (λ ()))
  build-poly (μ τ)        δ = Poly.μ (build-poly τ δ)

-- Syntactic subsitution is the same as
build-eq : (τ : type 1) (σ : type 0) →
           ⟦ τ [ σ ] ⟧ty (λ ()) ≡ fobj μ-obj (build-poly {0} {1} τ (λ ())) (extend (λ ()) (⟦ σ ⟧ty (λ ())))
build-eq (var Fin.zero)  σ = refl
build-eq unit            σ = refl
build-eq (base s)        σ = refl
build-eq (τ₁ [+] τ₂)     σ = cong₂ coprod (build-eq τ₁ σ) (build-eq τ₂ σ)
build-eq (τ₁ [×] τ₂)     σ = cong₂ prod   (build-eq τ₁ σ) (build-eq τ₂ σ)
build-eq (τ₁ [→] τ₂)     σ = refl
build-eq (μ τ')          σ = {!!}  -- nested μ: build-poly vs substitution-under-binder

⟦_⟧ctxt : ctxt → obj
⟦ emp ⟧ctxt   = 𝟙
⟦ Γ , τ ⟧ctxt = prod ⟦ Γ ⟧ctxt (⟦ τ ⟧ty (λ ()))

⟦_⟧var : ∀ {Γ τ} → Γ ∋ τ → ⟦ Γ ⟧ctxt ⇒ ⟦ τ ⟧ty (λ ())
⟦ zero ⟧var   = p₂
⟦ succ x ⟧var = ⟦ x ⟧var ∘ p₁

open import every using (Every; []; _∷_)
open PointedFPCat PFPC[ 𝒞 , 𝒞T , 𝒞P , Bool ] using (list→product)

mutual
  ⟦_⟧tm : ∀ {Γ τ} → Γ ⊢ τ → ⟦ Γ ⟧ctxt ⇒ ⟦ τ ⟧ty (λ ())
  ⟦ var x ⟧tm        = ⟦ x ⟧var
  ⟦ unit ⟧tm         = to-terminal
  ⟦ inl M ⟧tm        = in₁ ∘ ⟦ M ⟧tm
  ⟦ inr M ⟧tm        = in₂ ∘ ⟦ M ⟧tm
  ⟦ case M M₁ M₂ ⟧tm = HasStrongCoproducts.copair 𝒞SC ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm ∘ ⟨ id _ , ⟦ M ⟧tm ⟩
  ⟦ pair M N ⟧tm     = ⟨ ⟦ M ⟧tm , ⟦ N ⟧tm ⟩
  ⟦ fst M ⟧tm        = p₁ ∘ ⟦ M ⟧tm
  ⟦ snd M ⟧tm        = p₂ ∘ ⟦ M ⟧tm
  ⟦ lam M ⟧tm        = HasExponentials.lambda 𝒞E ⟦ M ⟧tm
  ⟦ app M N ⟧tm      = HasExponentials.eval 𝒞E ∘ ⟨ ⟦ M ⟧tm , ⟦ N ⟧tm ⟩
  ⟦ bop ω Ms ⟧tm     = ⟦op⟧ ω ∘ ⟦ Ms ⟧tms
  ⟦ brel r Ms ⟧tm    = ⟦rel⟧ r ∘ ⟦ Ms ⟧tms
  ⟦ roll {Γ = Γ} {τ = τ} M ⟧tm =
    inF (build-poly τ (λ ())) (λ ()) ∘ subst (⟦ Γ ⟧ctxt ⇒_) (build-eq τ (μ τ)) ⟦ M ⟧tm
  ⟦ fold-μ {Γ = Γ} {τ = τ} {σ = σ} alg M ⟧tm =
    ⦅ subst (λ A → prod ⟦ Γ ⟧ctxt A ⇒ ⟦ σ ⟧ty (λ ())) (build-eq τ σ) ⟦ alg ⟧tm ⦆ ∘ ⟨ id _ , ⟦ M ⟧tm ⟩

  ⟦_⟧tms : ∀ {Γ σs} → Every (λ σ → Γ ⊢ base σ) σs → ⟦ Γ ⟧ctxt ⇒ list→product ⟦sort⟧ σs
  ⟦ [] ⟧tms     = to-terminal
  ⟦ M ∷ Ms ⟧tms = ⟨ ⟦ M ⟧tm , ⟦ Ms ⟧tms ⟩
