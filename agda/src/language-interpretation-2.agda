{-# OPTIONS --prop --postfix-projections #-}

import Data.Fin as Fin
open Fin using (Fin; splitAt)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Sum using (_⊎_; [_,_]; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
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
open HasCoproducts (strong-coproducts→coproducts 𝒞T 𝒞SC) using (coprod; in₁; in₂; coproduct-preserve-iso)
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

≡→Iso : ∀ {x y} → x ≡ y → Iso x y
≡→Iso refl = Iso-refl

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

-- Applying the polynomial (as-poly τ δ) is the interpretation of τ.
apply-lemma : ∀ {Δ n} (τ : type (n + Δ)) (δ : Fin Δ → obj) (δ₀ : Fin n → obj) →
              Iso (⟦ τ ⟧ty (concat δ₀ δ)) (fobj μ-obj (as-poly {Δ} {n} τ δ) δ₀)

-- ⟦ τ ⟧ty is functorial in its poly-variables, with the action transported from fmor across apply-lemma.
ty-fmor : ∀ {Δ n} (τ : type (n + Δ)) (δ : Fin Δ → obj) {δ₀ δ₀' : Fin n → obj} →
          (∀ i → δ₀ i ⇒ δ₀' i) → ⟦ τ ⟧ty (concat δ₀ δ) ⇒ ⟦ τ ⟧ty (concat δ₀' δ)

apply-nat-fwd : ∀ {Δ n} (τ : type (n + Δ)) (δ : Fin Δ → obj) {δ₀ δ₀' : Fin n → obj} (fs : ∀ i → δ₀ i ⇒ δ₀' i) →
                Iso.fwd (apply-lemma τ δ δ₀') ∘ ty-fmor τ δ fs ≈ fmor (as-poly τ δ) fs ∘ Iso.fwd (apply-lemma τ δ δ₀)

apply-nat-bwd : ∀ {Δ n} (τ : type (n + Δ)) (δ : Fin Δ → obj) {δ₀ δ₀' : Fin n → obj} (fs : ∀ i → δ₀ i ⇒ δ₀' i) →
                ty-fmor τ δ fs ∘ Iso.bwd (apply-lemma τ δ δ₀) ≈ Iso.bwd (apply-lemma τ δ δ₀') ∘ fmor (as-poly τ δ) fs

apply-lemma {n = n} (var i) δ δ₀ with splitAt n i
... | inj₁ j = Iso-refl
... | inj₂ k = Iso-refl
apply-lemma unit      δ δ₀ = Iso-refl
apply-lemma (base s)  δ δ₀ = Iso-refl
apply-lemma (σ [+] τ) δ δ₀ = coproduct-preserve-iso (apply-lemma σ δ δ₀) (apply-lemma τ δ δ₀)
apply-lemma (σ [×] τ) δ δ₀ = product-preserves-iso  (apply-lemma σ δ δ₀) (apply-lemma τ δ δ₀)
apply-lemma (σ [→] τ) δ δ₀ = Iso-refl
apply-lemma {Δ} {n} (μ τ) δ δ₀ =
  μ-obj-resp unfold
    (λ {X} {Y} f →
      let open ≈-Reasoning isEquiv in
      begin
        fmor (as-poly τ δ) (extend-fam f) ∘ Iso.fwd (unfold X)
      ≈⟨ ≈-trans (≈-sym (assoc _ _ _)) (∘-cong₁ (≈-sym (assoc _ _ _))) ⟩
        fmor (as-poly τ δ) (extend-fam f) ∘ Iso.fwd (apply-lemma τ δ (extend δ₀ X))
          ∘ Iso.fwd (≡→Iso (ty-cong τ (env-pw X)))
          ∘ Iso.bwd (apply-lemma {n = 1} τ (concat δ₀ δ) (extend (λ ()) X))
      ≈⟨ ∘-cong₁ (∘-cong₁ (≈-sym (apply-nat-fwd τ δ (extend-fam f)))) ⟩
        Iso.fwd (apply-lemma τ δ (extend δ₀ Y)) ∘ ty-fmor τ δ (extend-fam f)
          ∘ Iso.fwd (≡→Iso (ty-cong τ (env-pw X)))
          ∘ Iso.bwd (apply-lemma {n = 1} τ (concat δ₀ δ) (extend (λ ()) X))
      ≈⟨ {!!} ⟩
        Iso.fwd (unfold Y) ∘ fmor (as-poly τ (concat δ₀ δ)) (extend-fam {n = 0} {δ = λ ()} f)
      ∎)
  where
    env-pw : ∀ X (i : Fin (suc (n + Δ))) → concat (extend {0} (λ ()) X) (concat δ₀ δ) i ≡ concat (extend δ₀ X) δ i
    env-pw X Fin.zero    = refl
    env-pw X (Fin.suc j) with splitAt n j
    ... | inj₁ k = refl
    ... | inj₂ l = refl

    unfold : ∀ X → Iso (fobj μ-obj (as-poly {n + Δ} {1} τ (concat δ₀ δ)) (extend {0} (λ ()) X))
                       (fobj μ-obj (as-poly {Δ} {suc n} τ δ) (extend δ₀ X))
    unfold X = Iso-trans (Iso-sym (apply-lemma {n = 1} τ (concat δ₀ δ) (extend (λ ()) X)))
                         (Iso-trans (≡→Iso (ty-cong τ (env-pw X))) (apply-lemma τ δ (extend δ₀ X)))

ty-fmor τ δ {δ₀} {δ₀'} fs =
  Iso.bwd (apply-lemma τ δ δ₀') ∘ fmor (as-poly τ δ) fs ∘ Iso.fwd (apply-lemma τ δ δ₀)

apply-nat-fwd τ δ {δ₀} {δ₀'} fs =
  begin
    Iso.fwd (apply-lemma τ δ δ₀') ∘ ((Iso.bwd (apply-lemma τ δ δ₀') ∘ fmor (as-poly τ δ) fs ∘ Iso.fwd (apply-lemma τ δ δ₀)))
  ≈⟨ ≈-trans (∘-cong₂ (assoc _ _ _)) (≈-sym (assoc _ _ _)) ⟩
    (Iso.fwd (apply-lemma τ δ δ₀') ∘ (Iso.bwd (apply-lemma τ δ δ₀')) ∘ (fmor (as-poly τ δ) fs ∘ Iso.fwd (apply-lemma τ δ δ₀)))
  ≈⟨ ≈-trans (∘-cong₁ (Iso.fwd∘bwd≈id (apply-lemma τ δ δ₀'))) id-left ⟩
    fmor (as-poly τ δ) fs ∘ Iso.fwd (apply-lemma τ δ δ₀)
  ∎
  where open ≈-Reasoning isEquiv

apply-nat-bwd τ δ {δ₀} {δ₀'} fs =
  begin
    ty-fmor τ δ fs ∘ Iso.bwd (apply-lemma τ δ δ₀)
  ≈˘⟨ id-left ⟩
    id _ ∘ (ty-fmor τ δ fs ∘ Iso.bwd (apply-lemma τ δ δ₀))
  ≈˘⟨ ∘-cong₁ (Iso.bwd∘fwd≈id (apply-lemma τ δ δ₀')) ⟩
    (Iso.bwd (apply-lemma τ δ δ₀') ∘ Iso.fwd (apply-lemma τ δ δ₀')) ∘ (ty-fmor τ δ fs ∘ Iso.bwd (apply-lemma τ δ δ₀))
  ≈⟨ assoc _ _ _ ⟩
    Iso.bwd (apply-lemma τ δ δ₀') ∘ (Iso.fwd (apply-lemma τ δ δ₀') ∘ (ty-fmor τ δ fs ∘ Iso.bwd (apply-lemma τ δ δ₀)))
  ≈˘⟨ ∘-cong₂ (assoc _ _ _) ⟩
    Iso.bwd (apply-lemma τ δ δ₀') ∘ ((Iso.fwd (apply-lemma τ δ δ₀') ∘ ty-fmor τ δ fs) ∘ Iso.bwd (apply-lemma τ δ δ₀))
  ≈⟨ ∘-cong₂ (∘-cong₁ (apply-nat-fwd τ δ fs)) ⟩
    Iso.bwd (apply-lemma τ δ δ₀') ∘ ((fmor (as-poly τ δ) fs ∘ Iso.fwd (apply-lemma τ δ δ₀)) ∘ Iso.bwd (apply-lemma τ δ δ₀))
  ≈⟨ ∘-cong₂ (assoc _ _ _) ⟩
    Iso.bwd (apply-lemma τ δ δ₀') ∘ (fmor (as-poly τ δ) fs ∘ (Iso.fwd (apply-lemma τ δ δ₀) ∘ Iso.bwd (apply-lemma τ δ δ₀)))
  ≈⟨ ∘-cong₂ (∘-cong₂ (Iso.fwd∘bwd≈id (apply-lemma τ δ δ₀))) ⟩
    Iso.bwd (apply-lemma τ δ δ₀') ∘ (fmor (as-poly τ δ) fs ∘ id _)
  ≈⟨ ∘-cong₂ id-right ⟩
    Iso.bwd (apply-lemma τ δ δ₀') ∘ fmor (as-poly τ δ) fs
  ∎
  where open ≈-Reasoning isEquiv

-- Syntactic substitution is functor application (up to isomorphism). The μ case is iso-level
-- (as-poly expands the substituted type, whereas the environment freezes it as a Poly.const).
sub-as-apply : (τ : type 1) (τ' : type 0) →
               Iso (⟦ τ [ τ' ] ⟧ty (λ ())) (fobj μ-obj (as-poly {0} {1} τ (λ ())) (extend (λ ()) (⟦ τ' ⟧ty (λ ()))))
sub-as-apply (var Fin.zero) _  = Iso-refl
sub-as-apply unit           _  = Iso-refl
sub-as-apply (base s)       _  = Iso-refl
sub-as-apply (σ [+] τ)      τ' = coproduct-preserve-iso (sub-as-apply σ τ') (sub-as-apply τ τ')
sub-as-apply (σ [×] τ)      τ' = product-preserves-iso  (sub-as-apply σ τ') (sub-as-apply τ τ')
sub-as-apply (σ [→] τ)      _  = Iso-refl
sub-as-apply (μ τ)          τ' =
  μ-obj-resp
    (λ X → Iso-trans (Iso-sym (apply-lemma (sub (sub-lift (push τ')) τ) (λ ()) (extend (λ ()) X)))
                     (Iso-trans {!!}
                                (apply-lemma {Δ = 0} {n = 2} τ (λ ()) (extend (extend (λ ()) (⟦ τ' ⟧ty (λ ()))) X))))
    {!!}

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
  ⟦ case M M₁ M₂ ⟧tm = scopair ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm ∘ ⟨ id _ , ⟦ M ⟧tm ⟩
  ⟦ pair M N ⟧tm     = ⟨ ⟦ M ⟧tm , ⟦ N ⟧tm ⟩
  ⟦ fst M ⟧tm        = p₁ ∘ ⟦ M ⟧tm
  ⟦ snd M ⟧tm        = p₂ ∘ ⟦ M ⟧tm
  ⟦ lam M ⟧tm        = lambda ⟦ M ⟧tm
  ⟦ app M N ⟧tm      = eval ∘ ⟨ ⟦ M ⟧tm , ⟦ N ⟧tm ⟩
  ⟦ bop ω Ms ⟧tm     = ⟦op⟧ ω ∘ ⟦ Ms ⟧tms
  ⟦ brel r Ms ⟧tm    = ⟦rel⟧ r ∘ ⟦ Ms ⟧tms
  ⟦ roll {τ = τ} M ⟧tm =
    α (as-poly τ (λ ())) (λ ()) ∘ Iso.fwd (sub-as-apply τ (μ τ)) ∘ ⟦ M ⟧tm
  ⟦ fold {τ = τ} {σ = σ} alg M ⟧tm =
    ⦅ ⟦ alg ⟧tm ∘ prod-m (id _) (Iso.bwd (sub-as-apply τ σ)) ⦆ ∘ ⟨ id _ , ⟦ M ⟧tm ⟩

  ⟦_⟧tms : ∀ {Γ σs} → Every (λ σ → Γ ⊢ base σ) σs → ⟦ Γ ⟧ctxt ⇒ list→product ⟦sort⟧ σs
  ⟦ [] ⟧tms     = to-terminal
  ⟦ M ∷ Ms ⟧tms = ⟨ ⟦ M ⟧tm , ⟦ Ms ⟧tms ⟩
