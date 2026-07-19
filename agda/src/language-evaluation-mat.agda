{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (0ℓ) renaming (_⊔_ to _⊔ℓ_)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import every using (Every; []; _∷_)
open import signature using (Signature)
open import signature-algebra using (Algebra; sort-vals)
import matrix
import cmon-enriched
open import categories using (Category; HasProducts; HasTerminal)

-- Big-step evaluation decorated with dependency matrices over a commutative
-- semiring.
module language-evaluation-mat
  {ℓ ℓ'} (Sig : Signature ℓ) (𝒜 : Algebra Sig ℓ')
  {o e} {A : Setoid o e} (S : CommutativeSemiring A)
  (sort-width : Signature.sort Sig → ℕ)
  where

open Signature Sig
open Algebra 𝒜
open import language-syntax Sig renaming (_,_ to _▸_)
open import type-substitution Sig using (unfold₁; unfold₁-inst)
open import language-evaluation Sig 𝒜 using (Val; Env; unit; const; inl; inr; pair; clo; roll; emp; _·_; lookup; bool→val)

private
  module M = matrix.Mat S

open Category M.cat using (_⇒_; _∘_) renaming (id to idm)
open HasTerminal M.terminal using (to-terminal)

products : HasProducts M.cat
products = cmon-enriched.biproducts→products M.cmon M.biproduct

open HasProducts products using (p₁; p₂) renaming (pair to ⟨_,_⟩)

mutual
  width : ∀ {τ} → Val τ → ℕ
  width unit        = 0
  width (const {s} _) = sort-width s
  width (inl v)     = width v
  width (inr v)     = width v
  width (pair v u)  = width v + width u
  width (clo γ _)   = width-env γ
  width (roll v)    = width v

  width-env : ∀ {Γ} → Env Γ → ℕ
  width-env emp     = 0
  width-env (γ · v) = width-env γ + width v

bases-width : List sort → ℕ
bases-width []       = 0
bases-width (s ∷ ss) = sort-width s + bases-width ss

width-subst : ∀ {τ τ'} (e : τ ≡ τ') (v : Val τ) → width (subst Val e v) ≡ width v
width-subst refl v = refl

proj-var : ∀ {Γ τ} (x : Γ ∋ τ) (γ : Env Γ) → width-env γ ⇒ width (lookup x γ)
proj-var zero     (γ · v) = p₂ {width-env γ} {width v}
proj-var (succ x) (γ · v) = proj-var x γ ∘ p₁ {width-env γ} {width v}

-- Case on the branch so that the width computes.
brel-mat : ∀ {Γ} (γ : Env Γ) (b : ⊤ {ℓ'} ⊎ ⊤ {ℓ'}) → width-env γ ⇒ width (bool→val b)
brel-mat γ (inj₁ _) = to-terminal {width-env γ}
brel-mat γ (inj₂ _) = to-terminal {width-env γ}

module WithOpMats
  (op-mat : ∀ {is o'} → op is o' → bases-width is ⇒ sort-width o')
  where

  mutual
    data _⊢_⇓_[_] : ∀ {Γ τ} (γ : Env Γ) (t : Γ ⊢ τ) (v : Val τ) →
                     width-env γ ⇒ width v → Set (ℓ ⊔ℓ ℓ' ⊔ℓ o ⊔ℓ e) where
      ⇓-var    : ∀ {Γ τ} {γ : Env Γ} (x : Γ ∋ τ) → γ ⊢ var x ⇓ lookup x γ [ proj-var x γ ]
      ⇓-unit   : ∀ {Γ} {γ : Env Γ} → γ ⊢ unit ⇓ unit [ to-terminal ]
      ⇓-inl    : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₁} {v R} →
                 γ ⊢ t ⇓ v [ R ] → γ ⊢ inl {τ₂ = τ₂} t ⇓ inl v [ R ]
      ⇓-inr    : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₂} {v R} →
                 γ ⊢ t ⇓ v [ R ] → γ ⊢ inr {τ₁ = τ₁} t ⇓ inr v [ R ]
      ⇓-case-l : ∀ {Γ τ₁ τ₂ τ} {γ : Env Γ} {s : Γ ⊢ τ₁ [+] τ₂} {t₁ : Γ ▸ τ₁ ⊢ τ} {t₂ : Γ ▸ τ₂ ⊢ τ}
                 {v u R S} →
                 γ ⊢ s ⇓ inl v [ R ] → γ · v ⊢ t₁ ⇓ u [ S ] →
                 γ ⊢ case s t₁ t₂ ⇓ u [ S ∘ ⟨ idm _ , R ⟩ ]
      ⇓-case-r : ∀ {Γ τ₁ τ₂ τ} {γ : Env Γ} {s : Γ ⊢ τ₁ [+] τ₂} {t₁ : Γ ▸ τ₁ ⊢ τ} {t₂ : Γ ▸ τ₂ ⊢ τ}
                 {v u R S} →
                 γ ⊢ s ⇓ inr v [ R ] → γ · v ⊢ t₂ ⇓ u [ S ] →
                 γ ⊢ case s t₁ t₂ ⇓ u [ S ∘ ⟨ idm _ , R ⟩ ]
      ⇓-pair   : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {s : Γ ⊢ τ₁} {t : Γ ⊢ τ₂} {v u R S} →
                 γ ⊢ s ⇓ v [ R ] → γ ⊢ t ⇓ u [ S ] → γ ⊢ pair s t ⇓ pair v u [ ⟨ R , S ⟩ ]
      ⇓-fst    : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₁ [×] τ₂} {v u R} →
                 γ ⊢ t ⇓ pair v u [ R ] → γ ⊢ fst t ⇓ v [ p₁ ∘ R ]
      ⇓-snd    : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₁ [×] τ₂} {v u R} →
                 γ ⊢ t ⇓ pair v u [ R ] → γ ⊢ snd t ⇓ u [ p₂ ∘ R ]
      ⇓-lam    : ∀ {Γ σ τ} {γ : Env Γ} {t : Γ ▸ σ ⊢ τ} → γ ⊢ lam t ⇓ clo γ t [ idm _ ]
      ⇓-app    : ∀ {Γ Γ' σ τ} {γ : Env Γ} {γ' : Env Γ'} {s : Γ ⊢ σ [→] τ} {t t' v u R S T} →
                 γ ⊢ s ⇓ clo {Γ'} γ' t' [ R ] → γ ⊢ t ⇓ v [ S ] → γ' · v ⊢ t' ⇓ u [ T ] →
                 γ ⊢ app s t ⇓ u [ T ∘ ⟨ R , S ⟩ ]
      ⇓-bop    : ∀ {Γ is o'} {γ : Env Γ} {ω : op is o'} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R} →
                 γ ⊢ Ms ⇓s vs [ R ] → γ ⊢ bop ω Ms ⇓ const (op-fun ω vs) [ op-mat ω ∘ R ]
      ⇓-brel   : ∀ {Γ is} {γ : Env Γ} {ω : rel is} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R} →
                 γ ⊢ Ms ⇓s vs [ R ] → γ ⊢ brel ω Ms ⇓ bool→val (rel-pred ω vs) [ brel-mat γ (rel-pred ω vs) ]
      ⇓-roll   : ∀ {Γ} {τ : type 1} {γ : Env Γ} {t : Γ ⊢ τ [ μ τ ]} {v R} →
                 γ ⊢ t ⇓ v [ R ] → γ ⊢ roll {τ = τ} t ⇓ roll {τ} v [ R ]
      ⇓-fold   : ∀ {Γ} {τ : type 1} {σ : type 0} {γ : Env Γ} {s : Γ ▸ τ [ σ ] ⊢ σ} {t : Γ ⊢ μ τ}
                 {v u R R'} →
                 γ ⊢ t ⇓ v [ R ] → Map γ {τ} {σ} s (var zero) v R u R' → γ ⊢ fold s t ⇓ u [ R' ]

    data _⊢_⇓s_[_] {Γ} (γ : Env Γ) : ∀ {is} → Every (λ s → Γ ⊢ base s) is →
                    sort-vals sort-val is → width-env γ ⇒ bases-width is →
                    Set (ℓ ⊔ℓ ℓ' ⊔ℓ o ⊔ℓ e) where
      []  : γ ⊢ [] ⇓s tt [ to-terminal ]
      _∷_ : ∀ {i is v vs R Rs} {M : Γ ⊢ base i} {Ms : Every (λ s → Γ ⊢ base s) is} →
            γ ⊢ M ⇓ const v [ R ] → γ ⊢ Ms ⇓s vs [ Rs ] → γ ⊢ (M ∷ Ms) ⇓s (v , vs) [ ⟨ R , Rs ⟩ ]

    -- Functorial action of σ' on the fold s, threading dependency matrices.
    data Map {Γ} (γ : Env Γ) {τ₀ : type 1} {σr : type 0} (s : Γ ▸ τ₀ [ σr ] ⊢ σr) :
             (σ' : type 1) (v : Val (σ' [ μ τ₀ ])) → width-env γ ⇒ width v →
             (v' : Val (σ' [ σr ])) → width-env γ ⇒ width v' →
             Set (ℓ ⊔ℓ ℓ' ⊔ℓ o ⊔ℓ e) where
      m-rec   : ∀ {w w' u R R' S} →
                Map γ s τ₀ w R w' R' → γ · w' ⊢ s ⇓ u [ S ] →
                Map γ s (var zero) (roll w) R u (S ∘ ⟨ idm _ , R' ⟩)
      m-unit  : ∀ {v R} → Map γ s unit v R v R
      m-base  : ∀ {b v R} → Map γ s (base b) v R v R
      m-arrow : ∀ {σ₁ σ₂ v R} → Map γ s (σ₁ [→] σ₂) v R v R
      m-inl   : ∀ {σ₁ σ₂ v v' R R'} →
                Map γ s σ₁ v R v' R' → Map γ s (σ₁ [+] σ₂) (inl v) R (inl v') R'
      m-inr   : ∀ {σ₁ σ₂ v v' R R'} →
                Map γ s σ₂ v R v' R' → Map γ s (σ₁ [+] σ₂) (inr v) R (inr v') R'
      m-pair  : ∀ {σ₁ σ₂ v v' u u' R S T} →
                Map γ s σ₁ v (p₁ ∘ R) v' S → Map γ s σ₂ u (p₂ ∘ R) u' T →
                Map γ s (σ₁ [×] σ₂) (pair v u) R (pair v' u') ⟨ S , T ⟩
      m-mu    : ∀ {τ' : type 2} {w w' R R'} →
                Map γ s (unfold₁ τ') w R w' R' →
                Map γ s (μ τ')
                    (roll (subst Val (unfold₁-inst τ' (μ τ₀)) w))
                    (subst (width-env γ ⇒_) (sym (width-subst (unfold₁-inst τ' (μ τ₀)) w)) R)
                    (roll (subst Val (unfold₁-inst τ' σr) w'))
                    (subst (width-env γ ⇒_) (sym (width-subst (unfold₁-inst τ' σr) w')) R')

  infix 25 _⊢_⇓_[_] _⊢_⇓s_[_]
