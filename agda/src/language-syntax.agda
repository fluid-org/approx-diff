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
    μ : polytype → type

  -- Polynomial-functor bodies. Closed under (constant) unit, (constant) types,
  -- a recursive position, sums, and products. No function arrows here — that
  -- matches the standard "no function types under μ" restriction for inductive
  -- type bodies (Chad §3.6).
  data polytype : Set ℓ where
    poly-one : polytype
    poly-param : type → polytype
    poly-var : polytype
    _[⊞]_ : polytype → polytype → polytype
    _[⊠]_ : polytype → polytype → polytype

-- polyApply P τ "applies" the polynomial body P at the recursive variable τ,
-- producing an ordinary type.
polyApply : polytype → type → type
polyApply poly-one        _ = unit
polyApply (poly-param σ)  _ = σ
polyApply poly-var        τ = τ
polyApply (P₁ [⊞] P₂)     τ = polyApply P₁ τ [+] polyApply P₂ τ
polyApply (P₁ [⊠] P₂)     τ = polyApply P₁ τ [×] polyApply P₂ τ

infixr 35 _[→]_
infixl 40 _[⊞]_ _[⊠]_

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
  roll : ∀ {Γ P} → Γ ⊢ polyApply P (μ P) → Γ ⊢ μ P

  -- μ-type eliminator (closed-form initial-algebra fold). Takes a (possibly
  -- context-dependent) algebra value and a μ value, produces the folded
  -- result. The algebra is a function value; context-dependent algebras are
  -- expressed by building the function via lam (closure captures Γ).
  fold-μ : ∀ {Γ P τ} → Γ ⊢ polyApply P τ [→] τ → Γ ⊢ μ P → Γ ⊢ τ

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

  _**_ : ∀ {Γ Γ' σs} → Ren Γ Γ' → Every (λ σ → Γ ⊢ base σ) σs → Every (λ σ → Γ' ⊢ base σ) σs
  ρ ** [] = []
  ρ ** (M ∷ Ms) = (ρ * M) ∷ (ρ ** Ms)

-- “macros”

-- Lists as a μ-type: List τ = μα. 1 + (τ × α). The macros wrap roll/fold-μ
-- to mimic the primitive list interface.
ListM : type → type
ListM τ = μ (poly-one [⊞] (poly-param τ [⊠] poly-var))

nilM : ∀ {Γ τ} → Γ ⊢ ListM τ
nilM = roll (inl unit)

consM : ∀ {Γ τ} → Γ ⊢ τ → Γ ⊢ ListM τ → Γ ⊢ ListM τ
consM h t = roll (inr (pair h t))

-- foldM mirrors the existing list `fold` macro: the nil case is Γ-open,
-- the cons case is Γ , head , acc-open. The body uses the closed-form
-- fold-μ together with a lambda that captures Γ.
foldM : ∀ {Γ σ τ} →
        Γ ⊢ τ →
        Γ , σ , τ ⊢ τ →
        Γ ⊢ ListM σ →
        Γ ⊢ τ
foldM {σ = σ} {τ = τ} nilCase consCase M =
  fold-μ {P = poly-one [⊞] (poly-param σ [⊠] poly-var)} (lam alg-body) M
  where
    alg-body : _
    alg-body =
      case (var zero)
        (weaken * (weaken * nilCase))
        (app (app (weaken * (weaken * (lam (lam consCase)))) (fst (var zero))) (snd (var zero)))

-- Derived list-monad sugar, mirroring append/return/from-collect/when on the
-- ListM type.
appendM : ∀ {Γ τ} → Γ ⊢ ListM τ → Γ ⊢ ListM τ → Γ ⊢ ListM τ
appendM xs ys = foldM ys (consM (var (succ zero)) (var zero)) xs

returnM : ∀ {Γ τ} → Γ ⊢ τ → Γ ⊢ ListM τ
returnM x = consM x nilM

fromM_collectM_ : ∀ {Γ τ₁ τ₂} → Γ ⊢ ListM τ₁ → Γ , τ₁ ⊢ ListM τ₂ → Γ ⊢ ListM τ₂
fromM M collectM N = foldM nilM (appendM (weaken * N) (var zero)) M

whenM_；M_ : ∀ {Γ τ} → Γ ⊢ bool → Γ ⊢ ListM τ → Γ ⊢ ListM τ
whenM M ；M N = if M then N else nilM

appendM-f : ∀ {Γ τ} → Γ ⊢ ListM τ [→] ListM τ [→] ListM τ
appendM-f = lam (lam (foldM (var zero) (consM (var (succ zero)) (var zero)) (var (succ zero))))


-- The list monad
{-
ret : ∀ {Γ τ} → Γ ⊢ τ [→] list τ
ret = lam (return (var zero))

bind : ∀ {Γ τ₁ τ₂} → Γ ⊢ list τ₁ [→] (τ₁ [→] list τ₂) [→] list τ₂
bind = lam (lam (from (var (succ zero)) collect (app (var (succ zero)) (var zero))))

guard : ∀ {Γ} → Γ ⊢ bool [→] list unit
guard = lam (if (var zero) then (cons unit nil) else nil)
-}

-- Definition of a syntactically defined monad
record SynMonad : Set ℓ where
  field
    Mon  : type → type
    pure : ∀ {Γ τ} → Γ ⊢ τ [→] Mon τ
    bind : ∀ {Γ σ τ} → Γ ⊢ Mon σ [→] (σ [→] Mon τ) [→] Mon τ
