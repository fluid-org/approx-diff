{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (0ℓ; suc; _⊔_)
open import Data.List using (List; []; _∷_)
open import signature using (Signature)
open import every using (Every; []; _∷_)

module language-syntax {ℓ} (Sig : Signature ℓ) where

open Signature Sig

mutual
  data type : Set ℓ where
    unit bool : type
    base : sort → type
    _[×]_ _[→]_ _[+]_ : type → type → type
    μ : polynomial → type
    approx : type → type

  -- Polynomial functors syntactically (cf. Chad §3.6).
  data polynomial : Set ℓ where
    one : polynomial
    const : type → polynomial
    var : polynomial
    _+_ : polynomial → polynomial → polynomial
    _×_ : polynomial → polynomial → polynomial
    approx : polynomial → polynomial

apply : polynomial → type → type
apply one        _ = unit
apply (const σ)  _ = σ
apply var        τ = τ
apply (P₁ + P₂)     τ = apply P₁ τ [+] apply P₂ τ
apply (P₁ × P₂)     τ = apply P₁ τ [×] apply P₂ τ
apply (approx P) τ = approx (apply P τ)

infixr 35 _[→]_
infixl 40 _+_ _×_

data first-order : type → Set ℓ where
  unit  : first-order unit
  bool  : first-order bool
  base  : ∀ s → first-order (base s)
  _[×]_ : ∀ {τ₁ τ₂} → first-order τ₁ → first-order τ₂ → first-order (τ₁ [×] τ₂)
  _[+]_ : ∀ {τ₁ τ₂} → first-order τ₁ → first-order τ₂ → first-order (τ₁ [+] τ₂)

infixl 40 _[×]_ _[+]_

data ctxt : Set ℓ where
  emp : ctxt
  _,_ : ctxt → type → ctxt

data first-order-ctxt : ctxt → Set ℓ where
  emp : first-order-ctxt emp
  _,_ : ∀ {Γ τ} → first-order-ctxt Γ → first-order τ → first-order-ctxt (Γ , τ)

infixl 30 _,_

data _∋_ : ctxt → type → Set ℓ where
  zero : ∀ {Γ τ} → (Γ , τ) ∋ τ
  succ : ∀ {Γ τ τ'} → Γ ∋ τ → Γ , τ' ∋ τ

-- A renaming is a context morphism
Ren : ctxt → ctxt → Set ℓ
Ren Γ Γ' = ∀ {τ} → Γ ∋ τ → Γ' ∋ τ

id-ren : ∀ Γ → Ren Γ Γ
id-ren Γ x = x

_∘ren_ : ∀ {Γ₁ Γ₂ Γ₃} → Ren Γ₂ Γ₃ → Ren Γ₁ Γ₂ → Ren Γ₁ Γ₃
ρ₁ ∘ren ρ₂ = λ z → ρ₁ (ρ₂ z)

-- Push a renaming under a context extension.
ext : ∀ {Γ Γ' τ} → Ren Γ Γ' → Ren (Γ , τ) (Γ' , τ)
ext ρ zero = zero
ext ρ (succ x) = succ (ρ x)

weaken : ∀ {Γ τ} → Ren Γ (Γ , τ)
weaken zero = succ zero
weaken (succ x) = succ (weaken x)

data _⊢_ : ctxt → type → Set ℓ where
  var : ∀ {Γ τ} → Γ ∋ τ → Γ ⊢ τ

  unit : ∀ {Γ} → Γ ⊢ unit

  -- booleans
  true false : ∀ {Γ} → Γ ⊢ bool
  if_then_else_ : ∀ {Γ τ} → Γ ⊢ bool → Γ ⊢ τ → Γ ⊢ τ → Γ ⊢ τ

  -- sums
  inl  : ∀ {Γ τ₁ τ₂} → Γ ⊢ τ₁ → Γ ⊢ τ₁ [+] τ₂
  inr  : ∀ {Γ τ₁ τ₂} → Γ ⊢ τ₂ → Γ ⊢ τ₁ [+] τ₂
  case : ∀ {Γ τ₁ τ₂ τ} → Γ ⊢ τ₁ [+] τ₂ → Γ , τ₁ ⊢ τ → Γ , τ₂ ⊢ τ → Γ ⊢ τ

  -- products
  pair : ∀ {Γ τ₁ τ₂} → Γ ⊢ τ₁ → Γ ⊢ τ₂ → Γ ⊢ τ₁ [×] τ₂
  fst  : ∀ {Γ τ₁ τ₂} → Γ ⊢ τ₁ [×] τ₂ → Γ ⊢ τ₁
  snd  : ∀ {Γ τ₁ τ₂} → Γ ⊢ τ₁ [×] τ₂ → Γ ⊢ τ₂

  -- functions
  lam  : ∀ {Γ τ₁ τ₂} → Γ , τ₁ ⊢ τ₂ → Γ ⊢ τ₁ [→] τ₂
  app  : ∀ {Γ τ₁ τ₂} → Γ ⊢ τ₁ [→] τ₂ → Γ ⊢ τ₁ → Γ ⊢ τ₂

  -- base operations
  bop : ∀ {Γ in-sorts out-sort} →
        op in-sorts out-sort →
        Every (λ σ → Γ ⊢ base σ) in-sorts →
        Γ ⊢ base out-sort
  brel : ∀ {Γ in-sorts} →
         rel in-sorts →
         Every (λ σ → Γ ⊢ base σ) in-sorts →
         Γ ⊢ bool

  -- μ-type constructor (initial-algebra introduction). Takes an unrolled
  -- value of polynomial-applied type and packs it into a μ value.
  roll : ∀ {Γ P} → Γ ⊢ apply P (μ P) → Γ ⊢ μ P

  -- μ-type eliminator (closed-form initial-algebra fold). Takes a (possibly
  -- context-dependent) algebra value and a μ value, produces the folded
  -- result. The algebra is a function value; context-dependent algebras are
  -- expressed by building the function via lam (closure captures Γ).
  fold-μ : ∀ {Γ P τ} → Γ ⊢ apply P τ [→] τ → Γ ⊢ μ P → Γ ⊢ τ

  -- bind is Kleisli composition packaged as a term.
  pure : ∀ {Γ τ} → Γ ⊢ τ → Γ ⊢ approx τ
  bind : ∀ {Γ σ τ} → Γ ⊢ approx σ → Γ , σ ⊢ approx τ → Γ ⊢ approx τ

-- Applying renamings to terms
mutual
  _*_ : ∀ {Γ Γ' τ} → Ren Γ Γ' → Γ ⊢ τ → Γ' ⊢ τ
  ρ * var x = var (ρ x)
  ρ * unit = unit
  ρ * true = true
  ρ * false = false
  ρ * (if M then M₁ else M₂) = if (ρ * M) then (ρ * M₁) else (ρ * M₂)
  ρ * inl M = inl (ρ * M)
  ρ * inr M = inr (ρ * M)
  ρ * case M N₁ N₂ = case (ρ * M) (ext ρ * N₁) (ext ρ * N₂)
  ρ * pair M N = pair (ρ * M) (ρ * N)
  ρ * fst M = fst (ρ * M)
  ρ * snd M = snd (ρ * M)
  ρ * bop ω Ms = bop ω (ρ ** Ms)
  ρ * brel ω Ms = brel ω (ρ ** Ms)
  ρ * lam M = lam (ext ρ * M)
  ρ * app M N = app (ρ * M) (ρ * N)
  ρ * roll M = roll (ρ * M)
  ρ * fold-μ alg M = fold-μ (ρ * alg) (ρ * M)
  ρ * pure M = pure (ρ * M)
  ρ * bind M N = bind (ρ * M) (ext ρ * N)

  _**_ : ∀ {Γ Γ' σs} → Ren Γ Γ' → Every (λ σ → Γ ⊢ base σ) σs → Every (λ σ → Γ' ⊢ base σ) σs
  ρ ** [] = []
  ρ ** (M ∷ Ms) = (ρ * M) ∷ (ρ ** Ms)

-- “macros” for lists
list : type → type
list τ = μ (one + (const τ × var))

nil : ∀ {Γ τ} → Γ ⊢ list τ
nil = roll (inl unit)

cons : ∀ {Γ τ} → Γ ⊢ τ → Γ ⊢ list τ → Γ ⊢ list τ
cons h t = roll (inr (pair h t))

fold : ∀ {Γ σ τ} → Γ ⊢ τ → Γ , σ , τ ⊢ τ → Γ ⊢ list σ → Γ ⊢ τ
fold {σ = σ} {τ = τ} nilCase consCase M =
  fold-μ {P = one + (const σ × var)} (lam alg-body) M
  where
    alg-body : _
    alg-body =
      case (var zero)
        (weaken * (weaken * nilCase))
        (app (app (weaken * (weaken * (lam (lam consCase)))) (fst (var zero))) (snd (var zero)))

append : ∀ {Γ τ} → Γ ⊢ list τ → Γ ⊢ list τ → Γ ⊢ list τ
append xs ys = fold ys (cons (var (succ zero)) (var zero)) xs

return : ∀ {Γ τ} → Γ ⊢ τ → Γ ⊢ list τ
return x = cons x nil

from_collect_ : ∀ {Γ τ₁ τ₂} → Γ ⊢ list τ₁ → Γ , τ₁ ⊢ list τ₂ → Γ ⊢ list τ₂
from M collect N = fold nil (append (weaken * N) (var zero)) M

when_；_ : ∀ {Γ τ} → Γ ⊢ bool → Γ ⊢ list τ → Γ ⊢ list τ
when M ； N = if M then N else nil

append-f : ∀ {Γ τ} → Γ ⊢ list τ [→] list τ [→] list τ
append-f = lam (lam (fold (var zero) (cons (var (succ zero)) (var zero)) (var (succ zero))))
