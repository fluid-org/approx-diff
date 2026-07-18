{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.Nat using (ℕ; zero; suc)
open import signature using (Signature)
open import every using (Every; []; _∷_)

-- FO language only for now.
module language-syntax {ℓ} (Sig : Signature ℓ) where

open Signature Sig

data type : Set ℓ where
  unit : type
  base : sort → type
  _[×]_ _[+]_ : type → type → type
  list : type → type

infixl 40 _[×]_ _[+]_

data ctxt : Set ℓ where
  emp : ctxt
  _·_ : ctxt → type → ctxt

infixl 30 _·_

data _∋_ : ctxt → type → Set ℓ where
  zero : ∀ {Γ τ} → (Γ · τ) ∋ τ
  succ : ∀ {Γ τ τ'} → Γ ∋ τ → Γ · τ' ∋ τ

-- A renaming is a context morphism
Ren : ctxt → ctxt → Set ℓ
Ren Γ Γ' = ∀ {τ} → Γ ∋ τ → Γ' ∋ τ

id-ren : ∀ Γ → Ren Γ Γ
id-ren Γ x = x

_∘ren_ : ∀ {Γ₁ Γ₂ Γ₃} → Ren Γ₂ Γ₃ → Ren Γ₁ Γ₂ → Ren Γ₁ Γ₃
ρ₁ ∘ren ρ₂ = λ z → ρ₁ (ρ₂ z)

-- Push a renaming under a context extension.
ext : ∀ {Γ Γ' τ} → Ren Γ Γ' → Ren (Γ · τ) (Γ' · τ)
ext ρ zero = zero
ext ρ (succ x) = succ (ρ x)

weaken : ∀ {Γ τ} → Ren Γ (Γ · τ)
weaken zero = succ zero
weaken (succ x) = succ (weaken x)

data _⊢_ : ctxt → type → Set ℓ where
  var : ∀ {Γ τ} → Γ ∋ τ → Γ ⊢ τ

  unit : ∀ {Γ} → Γ ⊢ unit

  -- sums
  inl  : ∀ {Γ τ₁ τ₂} → Γ ⊢ τ₁ → Γ ⊢ τ₁ [+] τ₂
  inr  : ∀ {Γ τ₁ τ₂} → Γ ⊢ τ₂ → Γ ⊢ τ₁ [+] τ₂
  case : ∀ {Γ τ₁ τ₂ τ} → Γ ⊢ τ₁ [+] τ₂ → Γ · τ₁ ⊢ τ → Γ · τ₂ ⊢ τ → Γ ⊢ τ

  -- products
  pair : ∀ {Γ τ₁ τ₂} → Γ ⊢ τ₁ → Γ ⊢ τ₂ → Γ ⊢ τ₁ [×] τ₂
  fst  : ∀ {Γ τ₁ τ₂} → Γ ⊢ τ₁ [×] τ₂ → Γ ⊢ τ₁
  snd  : ∀ {Γ τ₁ τ₂} → Γ ⊢ τ₁ [×] τ₂ → Γ ⊢ τ₂

  -- base operations
  bop : ∀ {Γ in-sorts out-sort} →
        op in-sorts out-sort →
        Every (λ σ → Γ ⊢ base σ) in-sorts →
        Γ ⊢ base out-sort
  brel : ∀ {Γ in-sorts} →
         rel in-sorts →
         Every (λ σ → Γ ⊢ base σ) in-sorts →
         Γ ⊢ unit [+] unit

  -- lists
  nil  : ∀ {Γ τ} → Γ ⊢ list τ
  cons : ∀ {Γ τ} → Γ ⊢ τ → Γ ⊢ list τ → Γ ⊢ list τ
  fold : ∀ {Γ τ₁ τ₂} →
         Γ ⊢ τ₂ →
         Γ · τ₁ · τ₂ ⊢ τ₂ →
         Γ ⊢ list τ₁ →
         Γ ⊢ τ₂

-- Applying renamings to terms
mutual
  _*_ : ∀ {Γ Γ' τ} → Ren Γ Γ' → Γ ⊢ τ → Γ' ⊢ τ
  ρ * var x = var (ρ x)
  ρ * unit = unit
  ρ * inl M = inl (ρ * M)
  ρ * inr M = inr (ρ * M)
  ρ * case M N₁ N₂ = case (ρ * M) (ext ρ * N₁) (ext ρ * N₂)
  ρ * pair M N = pair (ρ * M) (ρ * N)
  ρ * fst M = fst (ρ * M)
  ρ * snd M = snd (ρ * M)
  ρ * bop ω Ms = bop ω (ρ ** Ms)
  ρ * brel ω Ms = brel ω (ρ ** Ms)
  ρ * nil = nil
  ρ * cons M N = cons (ρ * M) (ρ * N)
  ρ * fold M₁ M₂ M = fold (ρ * M₁) (ext (ext ρ) * M₂) (ρ * M)

  _**_ : ∀ {Γ Γ' σs} → Ren Γ Γ' → Every (λ σ → Γ ⊢ base σ) σs → Every (λ σ → Γ' ⊢ base σ) σs
  ρ ** [] = []
  ρ ** (M ∷ Ms) = (ρ * M) ∷ (ρ ** Ms)


var-to-ℕ : ∀ {Γ τ} → Γ ∋ τ → ℕ
var-to-ℕ zero     = zero
var-to-ℕ (succ x) = suc (var-to-ℕ x)

------------------------------------------------------------------------
-- Agda-side syntactic helpers for `bool` / `if`, expressed as the unit-sum.

bool : type
bool = unit [+] unit

true : ∀ {Γ} → Γ ⊢ bool
true = inl unit

false : ∀ {Γ} → Γ ⊢ bool
false = inr unit

if_then_else_ : ∀ {Γ τ} → Γ ⊢ bool → Γ ⊢ τ → Γ ⊢ τ → Γ ⊢ τ
if M then N₁ else N₂ = case M (weaken * N₁) (weaken * N₂)

