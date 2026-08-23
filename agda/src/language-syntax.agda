{-# OPTIONS --prop --postfix-projections --safe #-}

-- Syntax of types in the style of Lucatelli Nunes & Vákár: types are kinded over a context Δ of type
-- variables. Strict positivity of μα.τ is enforced by requiring function types to be closed (kinded in
-- the empty context), so type variables cannot occur in function positions.

open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _≤_; z≤n)
open import Data.Nat.Properties using (≤-refl; ⊔-lub; m⊔n≤o⇒m≤o; m⊔n≤o⇒n≤o)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; subst)
open import Relation.Nullary using (Dec; yes; no)

open import every using (Every; []; _∷_)
open import signature using (Signature)

module language-syntax {ℓ} (Sig : Signature ℓ) where

open Signature Sig

TyCtxt : Set
TyCtxt = ℕ

data type : TyCtxt → Set ℓ where
  var   : ∀ {Δ} → Fin Δ → type Δ
  unit  : ∀ {Δ} → type Δ
  base  : ∀ {Δ} → sort → type Δ
  _[+]_ : ∀ {Δ} → type Δ → type Δ → type Δ
  _[×]_ : ∀ {Δ} → type Δ → type Δ → type Δ
  _[→]_ : ∀ {Δ} → type zero → type zero → type Δ
  μ     : ∀ {Δ} → type (suc Δ) → type Δ

infixl 40 _[×]_ _[+]_
infixr 35 _[→]_

-- First-order types: no function spaces. Used to equip the fibres of a type's
-- interpretation with approximation structure.
data first-order : ∀ {Δ} → type Δ → Set ℓ where
  var   : ∀ {Δ} (i : Fin Δ) → first-order (var i)
  unit  : ∀ {Δ} → first-order {Δ} unit
  base  : ∀ {Δ} (s : sort) → first-order {Δ} (base s)
  _[+]_ : ∀ {Δ} {σ τ : type Δ} → first-order σ → first-order τ → first-order (σ [+] τ)
  _[×]_ : ∀ {Δ} {σ τ : type Δ} → first-order σ → first-order τ → first-order (σ [×] τ)
  μ     : ∀ {Δ} {τ : type (suc Δ)} → first-order τ → first-order (μ τ)

first-order? : ∀ {Δ} (τ : type Δ) → Dec (first-order τ)
first-order? (var i)    = yes (var i)
first-order? unit       = yes unit
first-order? (base s)   = yes (base s)
first-order? (σ [+] τ) with first-order? σ | first-order? τ
... | yes fσ | yes fτ = yes (fσ [+] fτ)
... | no ¬fσ | _      = no λ { (fσ [+] _) → ¬fσ fσ }
... | yes _  | no ¬fτ = no λ { (_ [+] fτ) → ¬fτ fτ }
first-order? (σ [×] τ) with first-order? σ | first-order? τ
... | yes fσ | yes fτ = yes (fσ [×] fτ)
... | no ¬fσ | _      = no λ { (fσ [×] _) → ¬fσ fσ }
... | yes _  | no ¬fτ = no λ { (_ [×] fτ) → ¬fτ fτ }
first-order? (σ [→] τ) = no λ ()
first-order? (μ τ) with first-order? τ
... | yes fτ = yes (μ fτ)
... | no ¬fτ = no λ { (μ fτ) → ¬fτ fτ }

TyRen : TyCtxt → TyCtxt → Set
TyRen Δ Δ' = Fin Δ → Fin Δ'

TySub : TyCtxt → TyCtxt → Set ℓ
TySub Δ Δ' = Fin Δ → type Δ'

extᵗ : ∀ {Δ₁ Δ₂} → TyRen Δ₁ Δ₂ → TyRen (suc Δ₁) (suc Δ₂)
extᵗ ρ zero    = zero
extᵗ ρ (suc i) = suc (ρ i)

extᵗⁿ : ∀ {Δ₁ Δ₂} n → TyRen Δ₁ Δ₂ → TyRen (n + Δ₁) (n + Δ₂)
extᵗⁿ zero    ρ = ρ
extᵗⁿ (suc n) ρ = extᵗ (extᵗⁿ n ρ)

_*ᵗ_ : ∀ {Δ₁ Δ₂} → TyRen Δ₁ Δ₂ → type Δ₁ → type Δ₂
ρ *ᵗ var i       = var (ρ i)
ρ *ᵗ unit        = unit
ρ *ᵗ base s      = base s
ρ *ᵗ (τ₁ [+] τ₂) = (ρ *ᵗ τ₁) [+] (ρ *ᵗ τ₂)
ρ *ᵗ (τ₁ [×] τ₂) = (ρ *ᵗ τ₁) [×] (ρ *ᵗ τ₂)
ρ *ᵗ (τ₁ [→] τ₂) = τ₁ [→] τ₂
ρ *ᵗ μ τ         = μ (extᵗ ρ *ᵗ τ)

infixr 50 _*ᵗ_

sub-lift : ∀ {Δ₁ Δ₂} → TySub Δ₁ Δ₂ → TySub (suc Δ₁) (suc Δ₂)
sub-lift σ zero    = var zero
sub-lift σ (suc i) = suc *ᵗ σ i

sub : ∀ {Δ₁ Δ₂} → TySub Δ₁ Δ₂ → type Δ₁ → type Δ₂
sub σ (var i)     = σ i
sub σ unit        = unit
sub σ (base s)    = base s
sub σ (τ₁ [+] τ₂) = sub σ τ₁ [+] sub σ τ₂
sub σ (τ₁ [×] τ₂) = sub σ τ₁ [×] sub σ τ₂
sub σ (τ₁ [→] τ₂) = τ₁ [→] τ₂
sub σ (μ τ)       = μ (sub (sub-lift σ) τ)

push : ∀ {Δ} → type Δ → TySub (suc Δ) Δ
push τ zero    = τ
push τ (suc i) = var i

_[_] : ∀ {Δ} → type (suc Δ) → type Δ → type Δ
τ [ τ' ] = sub (push τ') τ

infix 50 _[_]

sub-cong : ∀ {Δ Δ'} {σ σ' : TySub Δ Δ'} (τ : type Δ) → (∀ i → σ i ≡ σ' i) → sub σ τ ≡ sub σ' τ
sub-cong (var i)     σ≡σ' = σ≡σ' i
sub-cong unit        _    = refl
sub-cong (base s)    _    = refl
sub-cong (τ₁ [+] τ₂) σ≡σ' = cong₂ _[+]_ (sub-cong τ₁ σ≡σ') (sub-cong τ₂ σ≡σ')
sub-cong (τ₁ [×] τ₂) σ≡σ' = cong₂ _[×]_ (sub-cong τ₁ σ≡σ') (sub-cong τ₂ σ≡σ')
sub-cong (τ₁ [→] τ₂) _ = refl
sub-cong (μ τ)       σ≡σ' = cong μ (sub-cong τ lifted)
  where
    lifted : ∀ i → sub-lift _ i ≡ sub-lift _ i
    lifted zero    = refl
    lifted (suc i) = cong (suc *ᵗ_) (σ≡σ' i)

sub-ren-id : ∀ {Δ Δ'} (τ : type Δ) {ρ : TyRen Δ Δ'} {σ : TySub Δ' Δ} →
             (∀ i → σ (ρ i) ≡ var i) → sub σ (ρ *ᵗ τ) ≡ τ
sub-ren-id (var i)     σ∘ρ≡id = σ∘ρ≡id i
sub-ren-id unit        _       = refl
sub-ren-id (base s)    _       = refl
sub-ren-id (τ₁ [+] τ₂) σ∘ρ≡id = cong₂ _[+]_ (sub-ren-id τ₁ σ∘ρ≡id) (sub-ren-id τ₂ σ∘ρ≡id)
sub-ren-id (τ₁ [×] τ₂) σ∘ρ≡id = cong₂ _[×]_ (sub-ren-id τ₁ σ∘ρ≡id) (sub-ren-id τ₂ σ∘ρ≡id)
sub-ren-id (τ₁ [→] τ₂) _       = refl
sub-ren-id (μ τ)       σ∘ρ≡id = cong μ (sub-ren-id τ lifted)
  where
    lifted : ∀ i → sub-lift _ (extᵗ _ i) ≡ var i
    lifted zero    = refl
    lifted (suc i) rewrite σ∘ρ≡id i = refl

arr-depth : ∀ {Δ} → type Δ → ℕ
arr-depth (var i)     = 0
arr-depth unit        = 0
arr-depth (base s)    = 0
arr-depth (τ₁ [+] τ₂) = arr-depth τ₁ ⊔ arr-depth τ₂
arr-depth (τ₁ [×] τ₂) = arr-depth τ₁ ⊔ arr-depth τ₂
arr-depth (τ₁ [→] τ₂) = suc (arr-depth τ₁ ⊔ arr-depth τ₂)
arr-depth (μ τ)       = arr-depth τ

arr-depth-ren : ∀ {Δ₁ Δ₂} (ρ : TyRen Δ₁ Δ₂) (τ : type Δ₁) → arr-depth (ρ *ᵗ τ) ≡ arr-depth τ
arr-depth-ren ρ (var i)     = refl
arr-depth-ren ρ unit        = refl
arr-depth-ren ρ (base s)    = refl
arr-depth-ren ρ (τ₁ [+] τ₂) = cong₂ _⊔_ (arr-depth-ren ρ τ₁) (arr-depth-ren ρ τ₂)
arr-depth-ren ρ (τ₁ [×] τ₂) = cong₂ _⊔_ (arr-depth-ren ρ τ₁) (arr-depth-ren ρ τ₂)
arr-depth-ren ρ (τ₁ [→] τ₂) = refl
arr-depth-ren ρ (μ τ)       = arr-depth-ren (extᵗ ρ) τ

arr-depth-sub : ∀ {Δ Δ' n} (σ : TySub Δ Δ') (τ : type Δ) → (∀ i → arr-depth (σ i) ≤ n) → arr-depth τ ≤ n →
                arr-depth (sub σ τ) ≤ n
arr-depth-sub σ (var i)     hσ hτ = hσ i
arr-depth-sub σ unit        hσ hτ = hτ
arr-depth-sub σ (base s)    hσ hτ = hτ
arr-depth-sub σ (τ₁ [+] τ₂) hσ hτ =
  ⊔-lub (arr-depth-sub σ τ₁ hσ (m⊔n≤o⇒m≤o _ _ hτ)) (arr-depth-sub σ τ₂ hσ (m⊔n≤o⇒n≤o _ _ hτ))
arr-depth-sub σ (τ₁ [×] τ₂) hσ hτ =
  ⊔-lub (arr-depth-sub σ τ₁ hσ (m⊔n≤o⇒m≤o _ _ hτ)) (arr-depth-sub σ τ₂ hσ (m⊔n≤o⇒n≤o _ _ hτ))
arr-depth-sub σ (τ₁ [→] τ₂) hσ hτ = hτ
arr-depth-sub σ (μ τ)       hσ hτ = arr-depth-sub (sub-lift σ) τ lifted hτ
  where
    lifted : ∀ i → arr-depth (sub-lift σ i) ≤ _
    lifted zero    = z≤n
    lifted (suc i) rewrite arr-depth-ren suc (σ i) = hσ i

arr-depth-unfold : ∀ {Δ} (τ : type (suc Δ)) → arr-depth (τ [ μ τ ]) ≤ arr-depth (μ τ)
arr-depth-unfold τ = arr-depth-sub (push (μ τ)) τ pushed ≤-refl
  where
    pushed : ∀ i → arr-depth (push (μ τ) i) ≤ arr-depth τ
    pushed zero    = ≤-refl
    pushed (suc i) = z≤n

data ctxt : Set ℓ where
  emp : ctxt
  _,_ : ctxt → type 0 → ctxt

infixl 30 _,_

data first-order-ctxt : ctxt → Set ℓ where
  emp : first-order-ctxt emp
  _,_ : ∀ {Γ τ} → first-order-ctxt Γ → first-order τ → first-order-ctxt (Γ , τ)

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
  fold : ∀ {Γ} {τ : type 1} {σ : type 0} → Γ , τ [ σ ] ⊢ σ → Γ ⊢ μ τ → Γ ⊢ σ

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
  ρ * fold s t     = fold (ext ρ * s) (ρ * t)

  _**_ : ∀ {Γ Γ' σs} → Ren Γ Γ' → Every (λ σ → Γ ⊢ base σ) σs → Every (λ σ → Γ' ⊢ base σ) σs
  ρ ** []       = []
  ρ ** (t ∷ ts) = (ρ * t) ∷ (ρ ** ts)

list : type 0 → type 0
list τ = μ (unit [+] (((λ ()) *ᵗ τ) [×] var zero))

nil : ∀ {Γ τ} → Γ ⊢ list τ
nil = roll (inl unit)

cons : ∀ {Γ τ} → Γ ⊢ τ → Γ ⊢ list τ → Γ ⊢ list τ
cons {_} {τ} h t = roll (inr (pair (subst (λ t → _ ⊢ t) (sym (sub-ren-id τ (λ ()))) h) t))

foldr : ∀ {Γ σ τ} → Γ ⊢ τ → Γ , σ , τ ⊢ τ → Γ ⊢ list σ → Γ ⊢ τ
foldr {Γ} {σ} {τ} nilCase consCase M =
  fold {τ = unit [+] (((λ ()) *ᵗ σ) [×] var zero)}
    (case (var zero)
          (weaken * (weaken * nilCase))
          (app (app (weaken * (weaken * (lam (lam consCase))))
                    (subst (Γ-inr ⊢_) (sub-ren-id σ (λ ())) (fst (var zero))))
               (snd (var zero))))
    M
  where
    Γ-inr : ctxt
    Γ-inr = Γ , (unit [+] (((λ ()) *ᵗ σ) [×] var zero)) [ τ ] , ((λ ()) *ᵗ σ) [ τ ] [×] τ

append : ∀ {Γ τ} → Γ ⊢ list τ → Γ ⊢ list τ → Γ ⊢ list τ
append xs ys = foldr ys (cons (var (succ zero)) (var zero)) xs

return : ∀ {Γ τ} → Γ ⊢ τ → Γ ⊢ list τ
return x = cons x nil

from_collect_ : ∀ {Γ τ₁ τ₂} → Γ ⊢ list τ₁ → Γ , τ₁ ⊢ list τ₂ → Γ ⊢ list τ₂
from M collect N = foldr nil (append (weaken * N) (var zero)) M

append-f : ∀ {Γ τ} → Γ ⊢ list τ [→] list τ [→] list τ
append-f = lam (lam (foldr (var zero) (cons (var (succ zero)) (var zero)) (var (succ zero))))

bool : type 0
bool = unit [+] unit

true false : ∀ {Γ} → Γ ⊢ bool
true  = inl unit
false = inr unit

if_then_else_ : ∀ {Γ τ} → Γ ⊢ bool → Γ ⊢ τ → Γ ⊢ τ → Γ ⊢ τ
if M then N₁ else N₂ = case M (weaken * N₁) (weaken * N₂)

when_；_ : ∀ {Γ τ} → Γ ⊢ bool → Γ ⊢ list τ → Γ ⊢ list τ
when M ； N = if M then N else nil
