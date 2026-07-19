{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (_⊔_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import every using (Every; []; _∷_)
open import signature using (Signature)
open import signature-algebra using (Algebra; sort-vals)

-- Big-step operational semantics, relative to a value-level interpretation of
-- the signature.
module language-evaluation {ℓ ℓ'} (Sig : Signature ℓ) (𝒜 : Algebra Sig ℓ') where

open Signature Sig
open Algebra 𝒜
open import language-syntax Sig renaming (_,_ to _▸_)
open import type-substitution Sig using (unfold₁; unfold₁-inst)

mutual
  data Val : type 0 → Set (ℓ ⊔ ℓ') where
    unit  : Val unit
    const : ∀ {s} → sort-val s → Val (base s)
    inl   : ∀ {τ₁ τ₂} → Val τ₁ → Val (τ₁ [+] τ₂)
    inr   : ∀ {τ₁ τ₂} → Val τ₂ → Val (τ₁ [+] τ₂)
    pair  : ∀ {τ₁ τ₂} → Val τ₁ → Val τ₂ → Val (τ₁ [×] τ₂)
    clo   : ∀ {Γ σ τ} → Env Γ → (Γ ▸ σ) ⊢ τ → Val (σ [→] τ)
    roll  : ∀ {τ : type 1} → Val (τ [ μ τ ]) → Val (μ τ)

  data Env : ctxt → Set (ℓ ⊔ ℓ') where
    emp : Env emp
    _·_ : ∀ {Γ τ} → Env Γ → Val τ → Env (Γ ▸ τ)

infixl 30 _·_

lookup : ∀ {Γ τ} → Γ ∋ τ → Env Γ → Val τ
lookup zero     (γ · v) = v
lookup (succ x) (γ · _) = lookup x γ

bool→val : ⊤ {ℓ'} ⊎ ⊤ {ℓ'} → Val (unit [+] unit)
bool→val (inj₁ _) = inl unit
bool→val (inj₂ _) = inr unit

mutual
  data _⊢_⇓_ : ∀ {Γ τ} → Env Γ → Γ ⊢ τ → Val τ → Set (ℓ ⊔ ℓ') where
    ⇓-var    : ∀ {Γ τ} {γ : Env Γ} (x : Γ ∋ τ) → γ ⊢ var x ⇓ lookup x γ
    ⇓-unit   : ∀ {Γ} {γ : Env Γ} → γ ⊢ unit ⇓ unit
    ⇓-inl    : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₁} {v} →
               γ ⊢ t ⇓ v → γ ⊢ inl {τ₂ = τ₂} t ⇓ inl v
    ⇓-inr    : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₂} {v} →
               γ ⊢ t ⇓ v → γ ⊢ inr {τ₁ = τ₁} t ⇓ inr v
    ⇓-case-l : ∀ {Γ τ₁ τ₂ τ} {γ : Env Γ} {s : Γ ⊢ τ₁ [+] τ₂} {t₁ : Γ ▸ τ₁ ⊢ τ} {t₂ : Γ ▸ τ₂ ⊢ τ} {v u} →
               γ ⊢ s ⇓ inl v → γ · v ⊢ t₁ ⇓ u → γ ⊢ case s t₁ t₂ ⇓ u
    ⇓-case-r : ∀ {Γ τ₁ τ₂ τ} {γ : Env Γ} {s : Γ ⊢ τ₁ [+] τ₂} {t₁ : Γ ▸ τ₁ ⊢ τ} {t₂ : Γ ▸ τ₂ ⊢ τ} {v u} →
               γ ⊢ s ⇓ inr v → γ · v ⊢ t₂ ⇓ u → γ ⊢ case s t₁ t₂ ⇓ u
    ⇓-pair   : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {s : Γ ⊢ τ₁} {t : Γ ⊢ τ₂} {v u} →
               γ ⊢ s ⇓ v → γ ⊢ t ⇓ u → γ ⊢ pair s t ⇓ pair v u
    ⇓-fst    : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₁ [×] τ₂} {v u} →
               γ ⊢ t ⇓ pair v u → γ ⊢ fst t ⇓ v
    ⇓-snd    : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₁ [×] τ₂} {v u} →
               γ ⊢ t ⇓ pair v u → γ ⊢ snd t ⇓ u
    ⇓-lam    : ∀ {Γ σ τ} {γ : Env Γ} {t : Γ ▸ σ ⊢ τ} → γ ⊢ lam t ⇓ clo γ t
    ⇓-app    : ∀ {Γ Γ' σ τ} {γ : Env Γ} {γ' : Env Γ'} {s : Γ ⊢ σ [→] τ} {t t' v u} →
               γ ⊢ s ⇓ clo {Γ'} γ' t' → γ ⊢ t ⇓ v → γ' · v ⊢ t' ⇓ u → γ ⊢ app s t ⇓ u
    ⇓-bop    : ∀ {Γ is o} {γ : Env Γ} {ω : op is o} {Ms : Every (λ s → Γ ⊢ base s) is} {vs} →
               γ ⊢ Ms ⇓s vs → γ ⊢ bop ω Ms ⇓ const (op-fun ω vs)
    ⇓-brel   : ∀ {Γ is} {γ : Env Γ} {ω : rel is} {Ms : Every (λ s → Γ ⊢ base s) is} {vs} →
               γ ⊢ Ms ⇓s vs → γ ⊢ brel ω Ms ⇓ bool→val (rel-pred ω vs)
    ⇓-roll   : ∀ {Γ} {τ : type 1} {γ : Env Γ} {t : Γ ⊢ τ [ μ τ ]} {v} →
               γ ⊢ t ⇓ v → γ ⊢ roll {τ = τ} t ⇓ roll {τ} v
    ⇓-fold   : ∀ {Γ} {τ : type 1} {σ : type 0} {γ : Env Γ} {s : Γ ▸ τ [ σ ] ⊢ σ} {t : Γ ⊢ μ τ} {v u} →
               γ ⊢ t ⇓ v → Map γ {τ} {σ} s (var zero) v u → γ ⊢ fold s t ⇓ u

  data _⊢_⇓s_ {Γ} (γ : Env Γ) : ∀ {is} → Every (λ s → Γ ⊢ base s) is → sort-vals sort-val is →
               Set (ℓ ⊔ ℓ') where
    []  : γ ⊢ [] ⇓s tt
    _∷_ : ∀ {i is v vs} {M : Γ ⊢ base i} {Ms : Every (λ s → Γ ⊢ base s) is} →
          γ ⊢ M ⇓ const v → γ ⊢ Ms ⇓s vs → γ ⊢ (M ∷ Ms) ⇓s (v , vs)

  -- Functorial action of σ' on the fold s.
  data Map {Γ} (γ : Env Γ) {τ₀ : type 1} {σr : type 0} (s : Γ ▸ τ₀ [ σr ] ⊢ σr) :
           (σ' : type 1) → Val (σ' [ μ τ₀ ]) → Val (σ' [ σr ]) → Set (ℓ ⊔ ℓ') where
    m-rec   : ∀ {w w' u} →
              Map γ s τ₀ w w' → γ · w' ⊢ s ⇓ u → Map γ s (var zero) (roll w) u
    m-unit  : ∀ {v} → Map γ s unit v v
    m-base  : ∀ {b v} → Map γ s (base b) v v
    m-arrow : ∀ {σ₁ σ₂ v} → Map γ s (σ₁ [→] σ₂) v v
    m-inl   : ∀ {σ₁ σ₂ v v'} →
              Map γ s σ₁ v v' → Map γ s (σ₁ [+] σ₂) (inl v) (inl v')
    m-inr   : ∀ {σ₁ σ₂ v v'} →
              Map γ s σ₂ v v' → Map γ s (σ₁ [+] σ₂) (inr v) (inr v')
    m-pair  : ∀ {σ₁ σ₂ v v' u u'} →
              Map γ s σ₁ v v' → Map γ s σ₂ u u' →
              Map γ s (σ₁ [×] σ₂) (pair v u) (pair v' u')
    m-mu    : ∀ {τ' : type 2} {w w'} →
              Map γ s (unfold₁ τ') w w' →
              Map γ s (μ τ')
                  (roll (subst Val (unfold₁-inst τ' (μ τ₀)) w))
                  (roll (subst Val (unfold₁-inst τ' σr) w'))

infix 25 _⊢_⇓_ _⊢_⇓s_
