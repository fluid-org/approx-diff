{-# OPTIONS --prop --postfix-projections --safe #-}

-- Syntax of types in the style of Lucatelli Nunes & Vákár: types are kinded over a context Δ of type
-- variables. Strict positivity of μα.τ is enforced by requiring function types to be closed (kinded in
-- the empty context), so type variables cannot occur in function positions.

open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; subst)

open import every using (Every; []; _∷_)
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

ren-ext : ∀ {Δ₁ Δ₂} → (Fin Δ₁ → Fin Δ₂) → Fin (suc Δ₁) → Fin (suc Δ₂)
ren-ext ρ zero    = zero
ren-ext ρ (suc i) = suc (ρ i)

ren : ∀ {Δ₁ Δ₂} → (Fin Δ₁ → Fin Δ₂) → type Δ₁ → type Δ₂
ren ρ (var i)     = var (ρ i)
ren ρ unit        = unit
ren ρ (base s)    = base s
ren ρ (τ₁ [+] τ₂) = ren ρ τ₁ [+] ren ρ τ₂
ren ρ (τ₁ [×] τ₂) = ren ρ τ₁ [×] ren ρ τ₂
ren ρ (τ₁ [→] τ₂) = τ₁ [→] τ₂
ren ρ (μ τ)       = μ (ren (ren-ext ρ) τ)

sub-lift : ∀ {Δ₁ Δ₂} → (Fin Δ₁ → type Δ₂) → Fin (suc Δ₁) → type (suc Δ₂)
sub-lift σ zero    = var zero
sub-lift σ (suc i) = ren suc (σ i)

sub : ∀ {Δ₁ Δ₂} → (Fin Δ₁ → type Δ₂) → type Δ₁ → type Δ₂
sub σ (var i)     = σ i
sub σ unit        = unit
sub σ (base s)    = base s
sub σ (τ₁ [+] τ₂) = sub σ τ₁ [+] sub σ τ₂
sub σ (τ₁ [×] τ₂) = sub σ τ₁ [×] sub σ τ₂
sub σ (τ₁ [→] τ₂) = τ₁ [→] τ₂
sub σ (μ τ)       = μ (sub (sub-lift σ) τ)

sub-head : ∀ {Δ} → type Δ → Fin (suc Δ) → type Δ
sub-head σ zero    = σ
sub-head σ (suc i) = var i

_[_] : ∀ {Δ} → type (suc Δ) → type Δ → type Δ
τ [ σ ] = sub (sub-head σ) τ

infix 50 _[_]

sub-cong : ∀ {Δ Δ'} {σ σ' : Fin Δ → type Δ'} (τ : type Δ)
         → (∀ i → σ i ≡ σ' i) → sub σ τ ≡ sub σ' τ
sub-cong (var i)     p = p i
sub-cong unit        p = refl
sub-cong (base s)    p = refl
sub-cong (τ₁ [+] τ₂) p = cong₂ _[+]_ (sub-cong τ₁ p) (sub-cong τ₂ p)
sub-cong (τ₁ [×] τ₂) p = cong₂ _[×]_ (sub-cong τ₁ p) (sub-cong τ₂ p)
sub-cong (τ₁ [→] τ₂) p = refl
sub-cong (μ τ)       p = cong μ (sub-cong τ lifted)
  where
    lifted : ∀ i → sub-lift _ i ≡ sub-lift _ i
    lifted zero    = refl
    lifted (suc i) = cong (ren suc) (p i)

sub-ren-id : ∀ {Δ Δ'} (τ : type Δ) {f : Fin Δ → Fin Δ'} {σ : Fin Δ' → type Δ}
             → (∀ i → σ (f i) ≡ var i)
             → sub σ (ren f τ) ≡ τ
sub-ren-id (var i)     p = p i
sub-ren-id unit        p = refl
sub-ren-id (base s)    p = refl
sub-ren-id (τ₁ [+] τ₂) p = cong₂ _[+]_ (sub-ren-id τ₁ p) (sub-ren-id τ₂ p)
sub-ren-id (τ₁ [×] τ₂) p = cong₂ _[×]_ (sub-ren-id τ₁ p) (sub-ren-id τ₂ p)
sub-ren-id (τ₁ [→] τ₂) p = refl
sub-ren-id (μ τ)       p = cong μ (sub-ren-id τ lifted)
  where
    lifted : ∀ i → sub-lift _ (ren-ext _ i) ≡ var i
    lifted zero    = refl
    lifted (suc i) rewrite p i = refl

data ctxt : Set ℓ where
  emp : ctxt
  _,_ : ctxt → type 0 → ctxt

infixl 30 _,_

data _∋_ : ctxt → type 0 → Set ℓ where
  zero : ∀ {Γ τ}    → (Γ , τ) ∋ τ
  succ : ∀ {Γ τ τ'} → Γ ∋ τ → (Γ , τ') ∋ τ

Ren : ctxt → ctxt → Set ℓ
Ren Γ Γ' = ∀ {τ} → Γ ∋ τ → Γ' ∋ τ

id-ren : ∀ Γ → Ren Γ Γ
id-ren Γ x = x

_∘ren_ : ∀ {Γ₁ Γ₂ Γ₃} → Ren Γ₂ Γ₃ → Ren Γ₁ Γ₂ → Ren Γ₁ Γ₃
ρ₁ ∘ren ρ₂ = λ z → ρ₁ (ρ₂ z)

ext : ∀ {Γ Γ' τ} → Ren Γ Γ' → Ren (Γ , τ) (Γ' , τ)
ext ρ zero     = zero
ext ρ (succ x) = succ (ρ x)

weaken : ∀ {Γ τ} → Ren Γ (Γ , τ)
weaken zero     = succ zero
weaken (succ x) = succ (weaken x)

data _⊢_ : ctxt → type 0 → Set ℓ where
  var  : ∀ {Γ τ}        → Γ ∋ τ → Γ ⊢ τ
  unit : ∀ {Γ}          → Γ ⊢ unit
  inl  : ∀ {Γ τ₁ τ₂}    → Γ ⊢ τ₁ → Γ ⊢ τ₁ [+] τ₂
  inr  : ∀ {Γ τ₁ τ₂}    → Γ ⊢ τ₂ → Γ ⊢ τ₁ [+] τ₂
  case : ∀ {Γ τ₁ τ₂ τ}  → Γ ⊢ τ₁ [+] τ₂ → Γ , τ₁ ⊢ τ → Γ , τ₂ ⊢ τ → Γ ⊢ τ
  pair : ∀ {Γ τ₁ τ₂}    → Γ ⊢ τ₁ → Γ ⊢ τ₂ → Γ ⊢ τ₁ [×] τ₂
  fst  : ∀ {Γ τ₁ τ₂}    → Γ ⊢ τ₁ [×] τ₂ → Γ ⊢ τ₁
  snd  : ∀ {Γ τ₁ τ₂}    → Γ ⊢ τ₁ [×] τ₂ → Γ ⊢ τ₂
  lam  : ∀ {Γ σ τ}      → Γ , σ ⊢ τ → Γ ⊢ σ [→] τ
  app  : ∀ {Γ σ τ}      → Γ ⊢ σ [→] τ → Γ ⊢ σ → Γ ⊢ τ
  bop  : ∀ {Γ in-sorts out-sort} →
         op in-sorts out-sort →
         Every (λ σ → Γ ⊢ base σ) in-sorts →
         Γ ⊢ base out-sort
  brel : ∀ {Γ in-sorts} →
         rel in-sorts →
         Every (λ σ → Γ ⊢ base σ) in-sorts →
         Γ ⊢ unit [+] unit
  roll   : ∀ {Γ} {τ : type 1} → Γ ⊢ τ [ μ τ ] → Γ ⊢ μ τ
  fold-μ : ∀ {Γ} {τ : type 1} {σ : type 0} → Γ , τ [ σ ] ⊢ σ → Γ ⊢ μ τ → Γ ⊢ σ

mutual
  _*_ : ∀ {Γ Γ' τ} → Ren Γ Γ' → Γ ⊢ τ → Γ' ⊢ τ
  ρ * var x        = var (ρ x)
  ρ * unit         = unit
  ρ * inl t        = inl (ρ * t)
  ρ * inr t        = inr (ρ * t)
  ρ * case s t₁ t₂ = case (ρ * s) (ext ρ * t₁) (ext ρ * t₂)
  ρ * pair s t     = pair (ρ * s) (ρ * t)
  ρ * fst t        = fst (ρ * t)
  ρ * snd t        = snd (ρ * t)
  ρ * lam t        = lam (ext ρ * t)
  ρ * app s t      = app (ρ * s) (ρ * t)
  ρ * bop ω ts     = bop ω (ρ ** ts)
  ρ * brel ω ts    = brel ω (ρ ** ts)
  ρ * roll t       = roll (ρ * t)
  ρ * fold-μ s t   = fold-μ (ext ρ * s) (ρ * t)

  _**_ : ∀ {Γ Γ' σs} → Ren Γ Γ' → Every (λ σ → Γ ⊢ base σ) σs → Every (λ σ → Γ' ⊢ base σ) σs
  ρ ** []       = []
  ρ ** (t ∷ ts) = (ρ * t) ∷ (ρ ** ts)

list : type 0 → type 0
list τ = μ (unit [+] (ren (λ ()) τ [×] var zero))

nil : ∀ {Γ τ} → Γ ⊢ list τ
nil = roll (inl unit)

cons : ∀ {Γ τ} → Γ ⊢ τ → Γ ⊢ list τ → Γ ⊢ list τ
cons {_} {τ} h t = roll (inr (pair (subst (λ t → _ ⊢ t) (sym (sub-ren-id τ (λ ()))) h) t))

fold : ∀ {Γ σ τ} → Γ ⊢ τ → Γ , σ , τ ⊢ τ → Γ ⊢ list σ → Γ ⊢ τ
fold {Γ} {σ} {τ} nilCase consCase M =
  fold-μ {τ = unit [+] (ren (λ ()) σ [×] var zero)}
    (case (var zero)
          (weaken * (weaken * nilCase))
          (app (app (weaken * (weaken * (lam (lam consCase))))
                    (subst (Γ-inr ⊢_) (sub-ren-id σ (λ ())) (fst (var zero))))
               (snd (var zero))))
    M
  where
    Γ-inr : ctxt
    Γ-inr = Γ , (unit [+] (ren (λ ()) σ [×] var zero)) [ τ ] , sub (sub-head τ) (ren (λ ()) σ) [×] τ

append : ∀ {Γ τ} → Γ ⊢ list τ → Γ ⊢ list τ → Γ ⊢ list τ
append xs ys = fold ys (cons (var (succ zero)) (var zero)) xs

return : ∀ {Γ τ} → Γ ⊢ τ → Γ ⊢ list τ
return x = cons x nil

from_collect_ : ∀ {Γ τ₁ τ₂} → Γ ⊢ list τ₁ → Γ , τ₁ ⊢ list τ₂ → Γ ⊢ list τ₂
from M collect N = fold nil (append (weaken * N) (var zero)) M

append-f : ∀ {Γ τ} → Γ ⊢ list τ [→] list τ [→] list τ
append-f = lam (lam (fold (var zero) (cons (var (succ zero)) (var zero)) (var (succ zero))))

bool : type 0
bool = unit [+] unit

true false : ∀ {Γ} → Γ ⊢ bool
true  = inl unit
false = inr unit

if_then_else_ : ∀ {Γ τ} → Γ ⊢ bool → Γ ⊢ τ → Γ ⊢ τ → Γ ⊢ τ
if M then N₁ else N₂ = case M (weaken * N₁) (weaken * N₂)

when_；_ : ∀ {Γ τ} → Γ ⊢ bool → Γ ⊢ list τ → Γ ⊢ list τ
when M ； N = if M then N else nil

record SynMonad : Set ℓ where
  field
    Mon     : ∀ {Δ} → type Δ → type Δ
    Mon-ren : ∀ {Δ Δ'} (ρ : Fin Δ → Fin Δ') (τ : type Δ) → ren ρ (Mon τ) ≡ Mon (ren ρ τ)
    Mon-sub : ∀ {Δ Δ'} (σ : Fin Δ → type Δ') (τ : type Δ) → sub σ (Mon τ) ≡ Mon (sub σ τ)
    pure    : ∀ {Γ τ} → Γ ⊢ τ [→] Mon τ
    bind    : ∀ {Γ σ τ} → Γ ⊢ Mon σ [→] (σ [→] Mon τ) [→] Mon τ
