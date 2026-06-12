{-# OPTIONS --prop --postfix-projections #-}

import Data.Fin as Fin
open Fin using (Fin; splitAt)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Sum using (_⊎_; [_,_]; inj₁; inj₂; map₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Level using (_⊔_)
open import categories
  using (Category; HasTerminal; HasProducts; HasCoproducts; HasStrongCoproducts;
         strong-coproducts→coproducts; HasExponentials)
open import functor using (StrongFunctor; StrongFunctor-Id)
open import signature using (Signature; Model; PointedFPCat; PFPC[_,_,_,_])
open import prop-setoid using (module ≈-Reasoning)
import polynomial-functor-2
import language-syntax-2

module language-interpretation-2
  {ℓ} (Sig : Signature ℓ)
  {o m e}
  (𝒞 : Category o m e)
  (𝒞T : HasTerminal 𝒞) (𝒞P : HasProducts 𝒞) (𝒞SC : HasStrongCoproducts 𝒞 𝒞P)
  (𝒞E : HasExponentials 𝒞 𝒞P)
  (let open polynomial-functor-2 𝒞T 𝒞P 𝒞SC (StrongFunctor-Id 𝒞P) hiding (_+_; _×_))
  (Mu : HasMu)
  (let Bool = HasCoproducts.coprod (strong-coproducts→coproducts 𝒞T 𝒞SC)
              (HasTerminal.witness 𝒞T) (HasTerminal.witness 𝒞T))
  (Int : Model PFPC[ 𝒞 , 𝒞T , 𝒞P , Bool ] Sig)
  where

open Category 𝒞
open HasTerminal 𝒞T renaming (witness to 𝟙)
open HasProducts 𝒞P renaming (pair to ⟨_,_⟩)
open HasCoproducts (strong-coproducts→coproducts 𝒞T 𝒞SC) using (coprod; coprod-m; in₁; in₂)
open HasStrongCoproducts 𝒞SC using () renaming (copair to scopair)
open HasExponentials 𝒞E using (lambda; eval) renaming (exp to _⟦→⟧_)
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
  ⟦ σ [→] τ ⟧ty δ = ⟦ σ ⟧ty (λ ()) ⟦→⟧ ⟦ τ ⟧ty (λ ())
  ⟦ μ τ ⟧ty       δ = μ-obj (as-poly τ δ) (λ ())

  as-poly : ∀ {Δ n} → type (n + Δ) → (Fin Δ → obj) → Poly n
  as-poly {Δ} {n} (var i) δ = [ Poly.var , (λ j → Poly.const (δ j)) ] (splitAt n i)
  as-poly unit            δ = Poly.const 𝟙
  as-poly (base s)        δ = Poly.const (⟦sort⟧ s)
  as-poly (σ [+] τ)       δ = as-poly σ δ Poly.+ as-poly τ δ
  as-poly (σ [×] τ)       δ = as-poly σ δ Poly.× as-poly τ δ
  as-poly (σ [→] τ)       δ = Poly.const (⟦ σ ⟧ty (λ ()) ⟦→⟧ ⟦ τ ⟧ty (λ ()))
  as-poly (μ τ)           δ = Poly.μ (as-poly τ δ)

-- Combined context: the first n variables from δ₀ (the Poly variables), the rest from δ.
concat : ∀ {n Δ} → (Fin n → obj) → (Fin Δ → obj) → Fin (n + Δ) → obj
concat {n} δ₀ δ i = [ δ₀ , δ ] (splitAt n i)

coe : ∀ {x y} → x ≡ y → x ⇒ y
coe refl = id _

-- Both as-poly and ⟦_⟧ty respect pointwise-equal environments.
as-poly-cong : ∀ {Δ n} (τ : type (n + Δ)) {δ δ' : Fin Δ → obj} → (∀ i → δ i ≡ δ' i) → as-poly τ δ ≡ as-poly τ δ'
as-poly-cong {Δ} {n} (var i) {δ} {δ'} h = go (splitAt n i)
  where
    go : (s : Fin n ⊎ Fin Δ) → [ Poly.var , (λ j → Poly.const (δ j)) ] s ≡ [ Poly.var , (λ j → Poly.const (δ' j)) ] s
    go (inj₁ k) = refl
    go (inj₂ j) = cong Poly.const (h j)
as-poly-cong unit      h = refl
as-poly-cong (base s)  h = refl
as-poly-cong (σ [+] τ) h = cong₂ Poly._+_ (as-poly-cong σ h) (as-poly-cong τ h)
as-poly-cong (σ [×] τ) h = cong₂ Poly._×_ (as-poly-cong σ h) (as-poly-cong τ h)
as-poly-cong (σ [→] τ) h = refl
as-poly-cong (μ τ)     h = cong Poly.μ (as-poly-cong τ h)

ty-cong : ∀ {Δ} (τ : type Δ) {δ δ' : Fin Δ → obj} → (∀ i → δ i ≡ δ' i) → ⟦ τ ⟧ty δ ≡ ⟦ τ ⟧ty δ'
ty-cong (var i)   h = h i
ty-cong unit      h = refl
ty-cong (base s)  h = refl
ty-cong (σ [+] τ) h = cong₂ coprod (ty-cong σ h) (ty-cong τ h)
ty-cong (σ [×] τ) h = cong₂ prod  (ty-cong σ h) (ty-cong τ h)
ty-cong (σ [→] τ) h = refl
ty-cong (μ τ)     h = cong (λ (P : Poly 1) → μ-obj P (λ ())) (as-poly-cong τ h)

-- Renaming a type is reindexing its environment. extᵗⁿ leaves the first n (poly) variables alone,
-- so splitAt commutes with it.
splitAt-extᵗⁿ : ∀ {Δ₁ Δ₂} n (ρ : TyRen Δ₁ Δ₂) (i : Fin (n + Δ₁)) →
                splitAt n (extᵗⁿ n ρ i) ≡ [ inj₁ , (λ k → inj₂ (ρ k)) ] (splitAt n i)
splitAt-extᵗⁿ zero    ρ i           = refl
splitAt-extᵗⁿ (suc n) ρ Fin.zero    = refl
splitAt-extᵗⁿ {Δ₁} (suc n) ρ (Fin.suc i) =
  trans (cong (map₁ Fin.suc) (splitAt-extᵗⁿ n ρ i)) (go (splitAt n i))
  where
    go : (s : Fin n ⊎ Fin Δ₁) →
         map₁ Fin.suc ([ inj₁ , (λ k → inj₂ (ρ k)) ] s) ≡ [ inj₁ , (λ k → inj₂ (ρ k)) ] (map₁ Fin.suc s)
    go (inj₁ j) = refl
    go (inj₂ k) = refl

as-poly-ren : ∀ {Δ₁ Δ₂ n} (ρ : TyRen Δ₁ Δ₂) (τ : type (n + Δ₁)) (δ : Fin Δ₂ → obj) →
              as-poly {Δ₂} {n} (extᵗⁿ n ρ *ᵗ τ) δ ≡ as-poly {Δ₁} {n} τ (λ i → δ (ρ i))
as-poly-ren {Δ₁} {Δ₂} {n} ρ (var i) δ = go (splitAt n i) (splitAt n (extᵗⁿ n ρ i)) (splitAt-extᵗⁿ n ρ i)
  where
    go : (s : Fin n ⊎ Fin Δ₁) (s' : Fin n ⊎ Fin Δ₂) → s' ≡ [ inj₁ , (λ k → inj₂ (ρ k)) ] s →
         [ Poly.var , (λ j → Poly.const (δ j)) ] s' ≡ [ Poly.var , (λ j → Poly.const (δ (ρ j))) ] s
    go (inj₁ j) _ refl = refl
    go (inj₂ k) _ refl = refl
as-poly-ren ρ unit      δ = refl
as-poly-ren ρ (base s)  δ = refl
as-poly-ren ρ (σ [+] τ) δ = cong₂ Poly._+_ (as-poly-ren ρ σ δ) (as-poly-ren ρ τ δ)
as-poly-ren ρ (σ [×] τ) δ = cong₂ Poly._×_ (as-poly-ren ρ σ δ) (as-poly-ren ρ τ δ)
as-poly-ren ρ (σ [→] τ) δ = refl
as-poly-ren ρ (μ τ)     δ = cong Poly.μ (as-poly-ren ρ τ δ)

ty-ren : ∀ {Δ₁ Δ₂} (ρ : TyRen Δ₁ Δ₂) (τ : type Δ₁) (δ : Fin Δ₂ → obj) →
         ⟦ ρ *ᵗ τ ⟧ty δ ≡ ⟦ τ ⟧ty (λ i → δ (ρ i))
ty-ren ρ (var i)   δ = refl
ty-ren ρ unit      δ = refl
ty-ren ρ (base s)  δ = refl
ty-ren ρ (σ [+] τ) δ = cong₂ coprod (ty-ren ρ σ δ) (ty-ren ρ τ δ)
ty-ren ρ (σ [×] τ) δ = cong₂ prod  (ty-ren ρ σ δ) (ty-ren ρ τ δ)
ty-ren ρ (σ [→] τ) δ = refl
ty-ren ρ (μ τ)     δ = cong (λ (P : Poly 1) → μ-obj P (λ ())) (as-poly-ren ρ τ δ)

-- Freezing the poly-variables δ₀ into the environment (with X at position 0) reshuffles the
-- combined context only up to pointwise equality.
env-pw : ∀ {Δ n} (δ : Fin Δ → obj) (δ₀ : Fin n → obj) (X : obj) (i : Fin (suc (n + Δ))) →
         concat (extend {0} (λ ()) X) (concat δ₀ δ) i ≡ concat (extend δ₀ X) δ i
env-pw δ δ₀ X Fin.zero    = refl
env-pw {n = n} δ δ₀ X (Fin.suc j) with splitAt n j
... | inj₁ k = refl
... | inj₂ l = refl

-- Applying the polynomial (as-poly τ δ) is the interpretation of τ, in each direction. Morphisms
-- suffice for the term semantics; the inverse laws are deferred.
mutual
  apply-fwd : ∀ {Δ n} (τ : type (n + Δ)) (δ : Fin Δ → obj) (δ₀ : Fin n → obj) →
              ⟦ τ ⟧ty (concat δ₀ δ) ⇒ fobj μ-obj (as-poly {Δ} {n} τ δ) δ₀
  apply-fwd {n = n} (var i) δ δ₀ with splitAt n i
  ... | inj₁ j = id _
  ... | inj₂ k = id _
  apply-fwd unit      δ δ₀ = id _
  apply-fwd (base s)  δ δ₀ = id _
  apply-fwd (σ [+] τ) δ δ₀ = coprod-m (apply-fwd σ δ δ₀) (apply-fwd τ δ δ₀)
  apply-fwd (σ [×] τ) δ δ₀ = prod-m (apply-fwd σ δ δ₀) (apply-fwd τ δ δ₀)
  apply-fwd (σ [→] τ) δ δ₀ = id _
  apply-fwd {Δ} {n} (μ τ) δ δ₀ =
    μ-map (as-poly {n + Δ} {1} τ (concat δ₀ δ)) (λ ()) (as-poly {Δ} {suc n} τ δ) δ₀
      (λ X → apply-fwd τ δ (extend δ₀ X) ∘ coe (ty-cong τ (env-pw δ δ₀ X)) ∘ apply-bwd {n = 1} τ (concat δ₀ δ) (extend (λ ()) X))

  apply-bwd : ∀ {Δ n} (τ : type (n + Δ)) (δ : Fin Δ → obj) (δ₀ : Fin n → obj) →
              fobj μ-obj (as-poly {Δ} {n} τ δ) δ₀ ⇒ ⟦ τ ⟧ty (concat δ₀ δ)
  apply-bwd {n = n} (var i) δ δ₀ with splitAt n i
  ... | inj₁ j = id _
  ... | inj₂ k = id _
  apply-bwd unit      δ δ₀ = id _
  apply-bwd (base s)  δ δ₀ = id _
  apply-bwd (σ [+] τ) δ δ₀ = coprod-m (apply-bwd σ δ δ₀) (apply-bwd τ δ δ₀)
  apply-bwd (σ [×] τ) δ δ₀ = prod-m (apply-bwd σ δ δ₀) (apply-bwd τ δ δ₀)
  apply-bwd (σ [→] τ) δ δ₀ = id _
  apply-bwd {Δ} {n} (μ τ) δ δ₀ =
    μ-map (as-poly {Δ} {suc n} τ δ) δ₀ (as-poly {n + Δ} {1} τ (concat δ₀ δ)) (λ ())
      (λ X → apply-fwd {n = 1} τ (concat δ₀ δ) (extend (λ ()) X) ∘ coe (sym (ty-cong τ (env-pw δ δ₀ X))) ∘ apply-bwd τ δ (extend δ₀ X))

-- Syntactic substitution is functor application, in each direction. The μ case crosses the two
-- presentations (as-poly expands the substituted type, whereas the environment freezes it as a
-- Poly.const), so it needs the substitution coherence.
sub-as-apply-fwd : (τ : type 1) (τ' : type 0) →
                   ⟦ τ [ τ' ] ⟧ty (λ ()) ⇒ fobj μ-obj (as-poly {0} {1} τ (λ ())) (extend (λ ()) (⟦ τ' ⟧ty (λ ())))
sub-as-apply-fwd (var Fin.zero) _  = id _
sub-as-apply-fwd unit           _  = id _
sub-as-apply-fwd (base s)       _  = id _
sub-as-apply-fwd (σ [+] τ)      τ' = coprod-m (sub-as-apply-fwd σ τ') (sub-as-apply-fwd τ τ')
sub-as-apply-fwd (σ [×] τ)      τ' = prod-m (sub-as-apply-fwd σ τ') (sub-as-apply-fwd τ τ')
sub-as-apply-fwd (σ [→] τ)      _  = id _
sub-as-apply-fwd (μ τ)          τ' = {!!}

sub-as-apply-bwd : (τ : type 1) (τ' : type 0) →
                   fobj μ-obj (as-poly {0} {1} τ (λ ())) (extend (λ ()) (⟦ τ' ⟧ty (λ ()))) ⇒ ⟦ τ [ τ' ] ⟧ty (λ ())
sub-as-apply-bwd (var Fin.zero) _  = id _
sub-as-apply-bwd unit           _  = id _
sub-as-apply-bwd (base s)       _  = id _
sub-as-apply-bwd (σ [+] τ)      τ' = coprod-m (sub-as-apply-bwd σ τ') (sub-as-apply-bwd τ τ')
sub-as-apply-bwd (σ [×] τ)      τ' = prod-m (sub-as-apply-bwd σ τ') (sub-as-apply-bwd τ τ')
sub-as-apply-bwd (σ [→] τ)      _  = id _
sub-as-apply-bwd (μ τ)          τ' = {!!}

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
  ⟦ var x ⟧tm                       = ⟦ x ⟧var
  ⟦ unit ⟧tm                        = to-terminal
  ⟦ inl M ⟧tm                       = in₁ ∘ ⟦ M ⟧tm
  ⟦ inr M ⟧tm                       = in₂ ∘ ⟦ M ⟧tm
  ⟦ case M M₁ M₂ ⟧tm                = scopair ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm ∘ ⟨ id _ , ⟦ M ⟧tm ⟩
  ⟦ pair M N ⟧tm                    = ⟨ ⟦ M ⟧tm , ⟦ N ⟧tm ⟩
  ⟦ fst M ⟧tm                       = p₁ ∘ ⟦ M ⟧tm
  ⟦ snd M ⟧tm                       = p₂ ∘ ⟦ M ⟧tm
  ⟦ lam M ⟧tm                       = lambda ⟦ M ⟧tm
  ⟦ app M N ⟧tm                     = eval ∘ ⟨ ⟦ M ⟧tm , ⟦ N ⟧tm ⟩
  ⟦ bop ω Ms ⟧tm                    = ⟦op⟧ ω ∘ ⟦ Ms ⟧tms
  ⟦ brel r Ms ⟧tm                   = ⟦rel⟧ r ∘ ⟦ Ms ⟧tms
  ⟦ roll {τ = τ} M ⟧tm              = α (as-poly τ (λ ())) (λ ()) ∘ sub-as-apply-fwd τ (μ τ) ∘ ⟦ M ⟧tm
  ⟦ fold {τ = τ} {σ = σ} alg M ⟧tm  = ⦅ ⟦ alg ⟧tm ∘ prod-m (id _) (sub-as-apply-bwd τ σ) ⦆ ∘ ⟨ id _ , ⟦ M ⟧tm ⟩

  ⟦_⟧tms : ∀ {Γ σs} → Every (λ σ → Γ ⊢ base σ) σs → ⟦ Γ ⟧ctxt ⇒ list→product ⟦sort⟧ σs
  ⟦ [] ⟧tms     = to-terminal
  ⟦ M ∷ Ms ⟧tms = ⟨ ⟦ M ⟧tm , ⟦ Ms ⟧tms ⟩
