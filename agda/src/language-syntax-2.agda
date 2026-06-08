{-# OPTIONS --prop --postfix-projections --safe #-}

-- Syntax of types in the style of Lucatelli Nunes & Vákár: types are kinded over a context Δ of type
-- variables. Strict positivity of μα.τ is enforced by requiring function types to be closed (kinded in
-- the empty context), so type variables cannot occur in function positions.

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc)

open import signature using (Signature)

module language-syntax-2 {ℓ} (Sig : Signature ℓ) where

open Signature Sig

KCtx : Set
KCtx = ℕ

data type : KCtx → Set ℓ where
  var   : ∀ {Δ} → Fin Δ → type Δ
  unit  : ∀ {Δ} → type Δ
  base  : ∀ {Δ} → sort → type Δ
  _[+]_ : ∀ {Δ} → type Δ → type Δ → type Δ
  _[×]_ : ∀ {Δ} → type Δ → type Δ → type Δ
  _[→]_ : ∀ {Δ} → type zero → type zero → type Δ
  μ     : ∀ {Δ} → type (suc Δ) → type Δ

infixl 40 _[×]_ _[+]_
infixr 35 _[→]_

ren : ∀ {Δ₁ Δ₂} → (Fin Δ₁ → Fin Δ₂) → type Δ₁ → type Δ₂
ren ρ (var i)     = var (ρ i)
ren ρ unit        = unit
ren ρ (base s)    = base s
ren ρ (τ₁ [+] τ₂) = ren ρ τ₁ [+] ren ρ τ₂
ren ρ (τ₁ [×] τ₂) = ren ρ τ₁ [×] ren ρ τ₂
ren ρ (τ₁ [→] τ₂) = τ₁ [→] τ₂
ren {Δ₁} {Δ₂} ρ (μ τ) = μ (ren ext-ρ τ)
  where
    ext-ρ : Fin (suc Δ₁) → Fin (suc Δ₂)
    ext-ρ zero    = zero
    ext-ρ (suc i) = suc (ρ i)

sub : ∀ {Δ₁ Δ₂} → (Fin Δ₁ → type Δ₂) → type Δ₁ → type Δ₂
sub σ (var i)     = σ i
sub σ unit        = unit
sub σ (base s)    = base s
sub σ (τ₁ [+] τ₂) = sub σ τ₁ [+] sub σ τ₂
sub σ (τ₁ [×] τ₂) = sub σ τ₁ [×] sub σ τ₂
sub σ (τ₁ [→] τ₂) = τ₁ [→] τ₂
sub {Δ₁} {Δ₂} σ (μ τ) = μ (sub lift-σ τ)
  where
    lift-σ : Fin (suc Δ₁) → type (suc Δ₂)
    lift-σ zero    = var zero
    lift-σ (suc i) = ren suc (σ i)

_[_] : ∀ {Δ} → type (suc Δ) → type Δ → type Δ
_[_] {Δ} τ σ = sub σ-head τ
  where
    σ-head : Fin (suc Δ) → type Δ
    σ-head zero    = σ
    σ-head (suc i) = var i

infix 50 _[_]
