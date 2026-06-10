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
  ⟦ σ [+] τ ⟧ty δ = coprod (⟦ σ ⟧ty δ) (⟦ τ ⟧ty δ)
  ⟦ σ [×] τ ⟧ty δ = prod (⟦ σ ⟧ty δ) (⟦ τ ⟧ty δ)
  ⟦ σ [→] τ ⟧ty δ = ⟦ σ ⟧ty (λ ()) ⟹ ⟦ τ ⟧ty (λ ())
  ⟦ μ τ ⟧ty       δ = μ-obj (as-poly τ δ) (λ ())

  as-poly : ∀ {Δ n} → type (n + Δ) → (Fin Δ → obj) → Poly 𝒞 Id n
  as-poly {Δ} {n} (var i) δ = [ Poly.var , (λ j → Poly.const (δ j)) ] (splitAt n i)
  as-poly unit            δ = Poly.const 𝟙
  as-poly (base s)        δ = Poly.const (⟦sort⟧ s)
  as-poly (σ [+] τ)       δ = as-poly σ δ Poly.+ as-poly τ δ
  as-poly (σ [×] τ)       δ = as-poly σ δ Poly.× as-poly τ δ
  as-poly (σ [→] τ)       δ = Poly.const (⟦ σ ⟧ty (λ ()) ⟹ ⟦ τ ⟧ty (λ ()))
  as-poly (μ τ)           δ = Poly.μ (as-poly τ δ)

-- Syntactic substitution is functor application.
sub-as-apply : (τ : type 1) (τ' : type 0) →
               ⟦ τ [ τ' ] ⟧ty (λ ()) ≡ fobj μ-obj (as-poly {0} {1} τ (λ ())) (extend (λ ()) (⟦ τ' ⟧ty (λ ())))
sub-as-apply (var Fin.zero) _  = refl
sub-as-apply unit           _  = refl
sub-as-apply (base s)       _  = refl
sub-as-apply (σ [+] τ)      τ' = cong₂ coprod (sub-as-apply σ τ') (sub-as-apply τ τ')
sub-as-apply (σ [×] τ)      τ' = cong₂ prod   (sub-as-apply σ τ') (sub-as-apply τ τ')
sub-as-apply (σ [→] τ)      _  = refl
sub-as-apply (μ τ)          τ' = {!!}  -- nested μ: as-poly vs substitution-under-binder

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
    inF (as-poly τ (λ ())) (λ ()) ∘ subst (⟦ Γ ⟧ctxt ⇒_) (sub-as-apply τ (μ τ)) ⟦ M ⟧tm
  ⟦ fold-μ {Γ = Γ} {τ = τ} {σ = σ} alg M ⟧tm =
    ⦅ subst (λ A → prod ⟦ Γ ⟧ctxt A ⇒ ⟦ σ ⟧ty (λ ())) (sub-as-apply τ σ) ⟦ alg ⟧tm ⦆ ∘ ⟨ id _ , ⟦ M ⟧tm ⟩

  ⟦_⟧tms : ∀ {Γ σs} → Every (λ σ → Γ ⊢ base σ) σs → ⟦ Γ ⟧ctxt ⇒ list→product ⟦sort⟧ σs
  ⟦ [] ⟧tms     = to-terminal
  ⟦ M ∷ Ms ⟧tms = ⟨ ⟦ M ⟧tm , ⟦ Ms ⟧tms ⟩
