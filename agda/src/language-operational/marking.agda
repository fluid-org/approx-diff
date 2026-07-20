{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import every using (Every; []; _∷_)
open import signature using (Signature)

-- Decorations marking the subterms whose runtime values become intermediates. Indexed by terms, so a marking
-- has exactly the shape of its term; the doc constructor leaves the index unchanged.
module language-operational.marking {ℓ} (Sig : Signature ℓ) where

open Signature Sig
open import language-syntax Sig renaming (_,_ to _▸_)

mutual
  data Marked : ∀ {Γ τ} → Γ ⊢ τ → Set ℓ where
    var  : ∀ {Γ τ} (x : Γ ∋ τ) → Marked (var x)
    unit : ∀ {Γ} → Marked {Γ} unit
    inl  : ∀ {Γ τ₁ τ₂} {t : Γ ⊢ τ₁} → Marked t → Marked (inl {τ₂ = τ₂} t)
    inr  : ∀ {Γ τ₁ τ₂} {t : Γ ⊢ τ₂} → Marked t → Marked (inr {τ₁ = τ₁} t)
    case : ∀ {Γ τ₁ τ₂ τ} {s : Γ ⊢ τ₁ [+] τ₂} {t₁ : Γ ▸ τ₁ ⊢ τ} {t₂ : Γ ▸ τ₂ ⊢ τ} →
           Marked s → Marked t₁ → Marked t₂ → Marked (case s t₁ t₂)
    pair : ∀ {Γ τ₁ τ₂} {s : Γ ⊢ τ₁} {t : Γ ⊢ τ₂} →
           Marked s → Marked t → Marked (pair s t)
    fst  : ∀ {Γ τ₁ τ₂} {t : Γ ⊢ τ₁ [×] τ₂} → Marked t → Marked (fst t)
    snd  : ∀ {Γ τ₁ τ₂} {t : Γ ⊢ τ₁ [×] τ₂} → Marked t → Marked (snd t)
    lam  : ∀ {Γ σ τ} {t : Γ ▸ σ ⊢ τ} → Marked t → Marked (lam t)
    app  : ∀ {Γ σ τ} {s : Γ ⊢ σ [→] τ} {t : Γ ⊢ σ} →
           Marked s → Marked t → Marked (app s t)
    bop  : ∀ {Γ is o} {ω : op is o} {Ms : Every (λ s → Γ ⊢ base s) is} →
           MarkedS Ms → Marked (bop ω Ms)
    brel : ∀ {Γ is} {ω : rel is} {Ms : Every (λ s → Γ ⊢ base s) is} →
           MarkedS Ms → Marked (brel ω Ms)
    roll : ∀ {Γ} {τ : type 1} {t : Γ ⊢ τ [ μ τ ]} → Marked t → Marked (roll {τ = τ} t)
    fold : ∀ {Γ} {τ : type 1} {σ : type 0} {s : Γ ▸ τ [ σ ] ⊢ σ} {t : Γ ⊢ μ τ} →
           Marked s → Marked t → Marked (fold s t)
    doc  : ∀ {Γ τ} {t : Γ ⊢ τ} → first-order τ → Marked t → Marked t

  data MarkedS {Γ} : ∀ {is} → Every (λ s → Γ ⊢ base s) is → Set ℓ where
    []  : MarkedS []
    _∷_ : ∀ {i is} {M : Γ ⊢ base i} {Ms : Every (λ s → Γ ⊢ base s) is} →
          Marked M → MarkedS Ms → MarkedS (M ∷ Ms)

-- The decoration with no marks.
mutual
  unmarked : ∀ {Γ τ} (t : Γ ⊢ τ) → Marked t
  unmarked (var x)        = var x
  unmarked unit           = unit
  unmarked (inl t)        = inl (unmarked t)
  unmarked (inr t)        = inr (unmarked t)
  unmarked (case s t₁ t₂) = case (unmarked s) (unmarked t₁) (unmarked t₂)
  unmarked (pair s t)     = pair (unmarked s) (unmarked t)
  unmarked (fst t)        = fst (unmarked t)
  unmarked (snd t)        = snd (unmarked t)
  unmarked (lam t)        = lam (unmarked t)
  unmarked (app s t)      = app (unmarked s) (unmarked t)
  unmarked (bop ω Ms)     = bop (unmarked-s Ms)
  unmarked (brel ω Ms)    = brel (unmarked-s Ms)
  unmarked (roll t)       = roll (unmarked t)
  unmarked (fold s t)     = fold (unmarked s) (unmarked t)

  unmarked-s : ∀ {Γ is} (Ms : Every (λ s → Γ ⊢ base s) is) → MarkedS Ms
  unmarked-s []       = []
  unmarked-s (M ∷ Ms) = unmarked M ∷ unmarked-s Ms

-- Whether a type is first-order, with the witness.
private
  first-order? : ∀ {Δ} (τ : type Δ) → Maybe (first-order τ)
  first-order? (var i)   = just (var i)
  first-order? unit      = just unit
  first-order? (base s)  = just (base s)
  first-order? (σ [+] τ) with first-order? σ | first-order? τ
  ... | just a  | just b  = just (a [+] b)
  ... | _       | _       = nothing
  first-order? (σ [×] τ) with first-order? σ | first-order? τ
  ... | just a  | just b  = just (a [×] b)
  ... | _       | _       = nothing
  first-order? (σ [→] τ) = nothing
  first-order? (μ τ) with first-order? τ
  ... | just a  = just (μ a)
  ... | nothing = nothing

-- The decoration marking every first-order subterm; the full evaluation graph is the dependence
-- graph of a run so marked.
mutual
  marked-all : ∀ {Γ τ} (t : Γ ⊢ τ) → Marked t
  marked-all {τ = τ} t with first-order? τ
  ... | just fo = doc fo (marked-all′ t)
  ... | nothing = marked-all′ t

  private
    marked-all′ : ∀ {Γ τ} (t : Γ ⊢ τ) → Marked t
    marked-all′ (var x)        = var x
    marked-all′ unit           = unit
    marked-all′ (inl t)        = inl (marked-all t)
    marked-all′ (inr t)        = inr (marked-all t)
    marked-all′ (case s t₁ t₂) = case (marked-all s) (marked-all t₁) (marked-all t₂)
    marked-all′ (pair s t)     = pair (marked-all s) (marked-all t)
    marked-all′ (fst t)        = fst (marked-all t)
    marked-all′ (snd t)        = snd (marked-all t)
    marked-all′ (lam t)        = lam (marked-all t)
    marked-all′ (app s t)      = app (marked-all s) (marked-all t)
    marked-all′ (bop ω Ms)     = bop (marked-all-s Ms)
    marked-all′ (brel ω Ms)    = brel (marked-all-s Ms)
    marked-all′ (roll t)       = roll (marked-all t)
    marked-all′ (fold s t)     = fold (marked-all s) (marked-all t)

    marked-all-s : ∀ {Γ is} (Ms : Every (λ s → Γ ⊢ base s) is) → MarkedS Ms
    marked-all-s []       = []
    marked-all-s (M ∷ Ms) = marked-all M ∷ marked-all-s Ms
