{-# OPTIONS --prop --postfix-projections --safe #-}

module unused.algebraic-theory where

open import Level using (suc; _⊔_)
open import Data.List using (List; []; _∷_; _++_)
open import prop using (LiftS; liftS)
open import prop-setoid using (IsEquivalence)
open import categories using (Category; HasProducts; IsTerminal; HasTerminal)

-- Multisorted algebraic theories with finitary operations.
--
-- Terms over a theory form a category with finite products.
--
-- FIXME: if every sort has a commutative monoid structure, and all
-- other operations distribute over them, then the category of terms
-- is cmon-enriched.

record Signature o m : Set (suc o ⊔ suc m) where
  field
    sort : Set o
    op   : List sort → sort → Set m

module Terms {o m} (𝕊 : Signature o m) where

  open Signature 𝕊

  data Var : List sort → sort → Set o where
    zero : ∀ {Γ σ} → Var (σ ∷ Γ) σ
    succ : ∀ {Γ σ τ} → Var Γ σ → Var (τ ∷ Γ) σ

  mutual
    data Term (Γ : List sort) : sort → Set (o ⊔ m) where
      var : ∀ {σ} → Var Γ σ → Term Γ σ
      app : ∀ {σ Δ} (ω : op Δ σ) → Terms Γ Δ → Term Γ σ

    data Terms (Γ : List sort) : List sort → Set (o ⊔ m) where
      []  : Terms Γ []
      _∷_ : ∀ {Δ σ} → Term Γ σ → Terms Γ Δ → Terms Γ (σ ∷ Δ)

  mutual
    wk : ∀ {Γ τ} σ → Term Γ τ → Term (σ ∷ Γ) τ
    wk σ (var x) = var (succ x)
    wk σ (app ω Ms) = app ω (wk* σ Ms)

    wk* : ∀ {Γ Δ} σ → Terms Γ Δ → Terms (σ ∷ Γ) Δ
    wk* σ []       = []
    wk* σ (M ∷ Ms) = wk σ M ∷ wk* σ Ms

  id : ∀ Γ → Terms Γ Γ
  id []      = []
  id (σ ∷ Γ) = var zero ∷ wk* σ (id Γ)

  lookup : ∀ {Γ Δ σ} → Var Δ σ → Terms Γ Δ → Term Γ σ
  lookup zero     (M ∷ Ms) = M
  lookup (succ x) (_ ∷ Ms) = lookup x Ms

  mutual
    subst : ∀ {Γ Δ σ} → Term Δ σ → Terms Γ Δ → Term Γ σ
    subst (var x)    Ns = lookup x Ns
    subst (app ω Ms) Ns = app ω (subst* Ms Ns)

    subst* : ∀ {Γ Δ Ξ} → Terms Δ Ξ → Terms Γ Δ → Terms Γ Ξ
    subst* []       Ns = []
    subst* (M ∷ Ms) Ns = subst M Ns ∷ subst* Ms Ns

  terminal : ∀ {Γ} → Terms Γ []
  terminal = []

  p₁ : ∀ {Γ Δ} → Terms (Γ ++ Δ) Γ
  p₁ {[]}    {Δ} = []
  p₁ {σ ∷ Γ} {Δ} = var zero ∷ wk* σ p₁

  p₂ : ∀ {Γ Δ} → Terms (Γ ++ Δ) Δ
  p₂ {[]}    {Δ} = id Δ
  p₂ {σ ∷ Γ} {Δ} = wk* σ p₂

  pair : ∀ {Γ Δ₁ Δ₂} → Terms Γ Δ₁ → Terms Γ Δ₂ → Terms Γ (Δ₁ ++ Δ₂)
  pair []       Ns = Ns
  pair (M ∷ Ms) Ns = M ∷ pair Ms Ns

  -- A solver:
  --  1. Language is categories + p₁, p₂, pair
  --  2. Above language is a normaliser for this language:
  --     - There is a (unique) functor from this category to any other FP category
  --     - If we have two expressions M, N such that M is syntactically equal to N, then ⟦M⟧ = ⟦N⟧ in the target category

record Equations {o m} (𝕊 : Signature o m) e : Set (suc e ⊔ o ⊔ m) where
  open Signature 𝕊
  open Terms 𝕊
  field
    eqn         : Set e
    eqn-context : eqn → List sort
    eqn-sort    : eqn → sort
    eqn-lhs     : (e : eqn) → Term (eqn-context e) (eqn-sort e)
    eqn-rhs     : (e : eqn) → Term (eqn-context e) (eqn-sort e)

module term-category {o m e} (𝕊 : Signature o m) (𝔼 : Equations 𝕊 e) where
  open Signature 𝕊
  open Terms 𝕊
  open Equations 𝔼

  data ≃-var : ∀ {Γ σ} → Var Γ σ → Var Γ σ → Set o where
    zero : ∀ {Γ σ} → ≃-var {σ ∷ Γ} {σ} zero zero
    succ : ∀ {Γ σ τ} {x y : Var Γ σ} → ≃-var x y → ≃-var {τ ∷ Γ} (succ x) (succ y)

  mutual
    data _≃_ {Γ} : {σ : sort} → Term Γ σ → Term Γ σ → Set (e ⊔ o ⊔ m) where
      var : ∀ {σ} {x y : Var Γ σ} → ≃-var x y → var x ≃ var y
      app : ∀ {σ Δ} {ω : op Δ σ} {Ms Ns} →
            Ms ≃* Ns →     -- FIXME: allow for intensionally different operation names
            app ω Ms ≃ app ω Ns
      eqn-inst : ∀ (η : eqn) (Ms : Terms Γ (eqn-context η)) →
                 subst (eqn-lhs η) Ms ≃ subst (eqn-rhs η) Ms
      ≃-trans : ∀ {σ} {M N O : Term Γ σ} → M ≃ N → N ≃ O → M ≃ O
      ≃-sym   : ∀ {σ} {M N : Term Γ σ} → M ≃ N → N ≃ M

    data _≃*_ {Γ} : {Δ : List sort} → Terms Γ Δ → Terms Γ Δ → Set (e ⊔ o ⊔ m) where
      []  : [] ≃* []
      _∷_ : ∀ {Δ σ} {M N : Term Γ σ} {Ms Ns : Terms Γ Δ} →
            M ≃ N →
            Ms ≃* Ns →
            (M ∷ Ms) ≃* (N ∷ Ns)

  ≃-var-refl : ∀ {Γ σ} (x : Var Γ σ) → ≃-var x x
  ≃-var-refl zero = zero
  ≃-var-refl (succ x) = succ (≃-var-refl x)

  mutual
    ≃-refl : ∀ {Γ σ} (M : Term Γ σ) → M ≃ M
    ≃-refl (var x)    = var (≃-var-refl x)
    ≃-refl (app ω Ms) = app (≃*-refl Ms)

    ≃*-refl : ∀ {Γ Δ} (Ms : Terms Γ Δ) → Ms ≃* Ms
    ≃*-refl [] = []
    ≃*-refl (M ∷ Ms) = ≃-refl M ∷ ≃*-refl Ms

  ≃*-sym : ∀ {Γ Δ} {Ms Ns : Terms Γ Δ} → Ms ≃* Ns → Ns ≃* Ms
  ≃*-sym []             = []
  ≃*-sym (M≃N ∷ Ms≃Ns) = ≃-sym M≃N ∷ ≃*-sym Ms≃Ns

  ≃*-trans : ∀ {Γ Δ} {Ms Ns Os : Terms Γ Δ} →
             Ms ≃* Ns → Ns ≃* Os → Ms ≃* Os
  ≃*-trans [] [] = []
  ≃*-trans (M≃N ∷ Ms≃Ns) (N≃O ∷ Ns≃Os) = ≃-trans M≃N N≃O ∷ ≃*-trans Ms≃Ns Ns≃Os

  lookup-cong : ∀ {Γ Δ σ} {x y : Var Δ σ} {Ms Ns : Terms Γ Δ} →
                ≃-var x y → Ms ≃* Ns →
                lookup x Ms ≃ lookup y Ns
  lookup-cong zero       (M≃N ∷ _)      = M≃N
  lookup-cong (succ x≃y) (M≃N ∷ Ms≃Ns) = lookup-cong x≃y Ms≃Ns

  mutual
    subst-wk : ∀ {Γ Δ σ τ} (M : Term Δ τ) (N : Term Γ σ) (Ns : Terms Γ Δ) →
               subst (wk σ M) (N ∷ Ns) ≃ subst M Ns
    subst-wk (var x)    N Ns = ≃-refl _
    subst-wk (app ω Ms) N Ns = app (subst*-wk* Ms Ns N)

    subst*-wk* : ∀ {Γ Δ Ξ σ} (Ms : Terms Δ Ξ) (Ns : Terms Γ Δ) (N : Term Γ σ) →
                 subst* (wk* σ Ms) (N ∷ Ns) ≃* subst* Ms Ns
    subst*-wk* []       Ns N = []
    subst*-wk* (M ∷ Ms) Ns N = subst-wk M N Ns ∷ subst*-wk* Ms Ns N

  lookup-wk : ∀ {Γ Δ σ τ} (x : Var Δ σ) (Ms : Terms Γ Δ) →
              lookup x (wk* τ Ms) ≃ wk τ (lookup x Ms)
  lookup-wk zero     (M ∷ Ms) = ≃-refl (wk _ M)
  lookup-wk (succ x) (M ∷ Ms) = lookup-wk x Ms

  mutual
    wk-subst : ∀ {Γ Δ σ} τ (M : Term Δ σ) (Ns : Terms Γ Δ) →
               wk τ (subst M Ns) ≃ subst M (wk* τ Ns)
    wk-subst τ (var x)    Ns = ≃-sym (lookup-wk x Ns)
    wk-subst τ (app ω Ms) Ns = app (wk*-subst* τ Ms Ns)

    wk*-subst* : ∀ {Γ Δ Ξ} τ (Ms : Terms Δ Ξ) (Ns : Terms Γ Δ) →
                 wk* τ (subst* Ms Ns) ≃* subst* Ms (wk* τ Ns)
    wk*-subst* τ []       Ns = []
    wk*-subst* τ (M ∷ Ms) Ns = wk-subst τ M Ns ∷ wk*-subst* τ Ms Ns

  mutual
    wk-cong : ∀ {Γ σ} {M N : Term Γ σ} τ → M ≃ N → wk τ M ≃ wk τ N
    wk-cong τ (var x≃y) = var (succ x≃y)
    wk-cong τ (app Ms≃Ns) = app (wk*-cong τ Ms≃Ns)
    wk-cong τ (eqn-inst η Ms) =
      ≃-trans (wk-subst τ (eqn-lhs η) Ms)
     (≃-trans (eqn-inst η (wk* τ Ms))
              (≃-sym (wk-subst τ (eqn-rhs η) Ms)))
    wk-cong τ (≃-trans M≃N N≃O) = ≃-trans (wk-cong τ M≃N) (wk-cong τ N≃O)
    wk-cong τ (≃-sym M≃N) = ≃-sym (wk-cong τ M≃N)

    wk*-cong : ∀ {Γ Δ} {Ms Ns : Terms Γ Δ} τ → Ms ≃* Ns → wk* τ Ms ≃* wk* τ Ns
    wk*-cong τ [] = []
    wk*-cong τ (M≃N ∷ Ms≃Ns) = wk-cong τ M≃N ∷ wk*-cong τ Ms≃Ns

  id-subst : ∀ {Γ Δ} {Ms : Terms Γ Δ} → subst* (id Δ) Ms ≃* Ms
  id-subst {Γ} {[]}    {[]} = []
  id-subst {Γ} {_ ∷ _} {M ∷ Ms} =
    ≃-refl M ∷ ≃*-trans (subst*-wk* (id _) Ms M) id-subst

  lookup-id : ∀ {Γ σ} (x : Var Γ σ) → lookup x (id Γ) ≃ var x
  lookup-id zero     = var zero
  lookup-id (succ x) = ≃-trans (lookup-wk x (id _)) (wk-cong _ (lookup-id x))

  mutual
    subst-id : ∀ {Γ σ} (M : Term Γ σ) → subst M (id Γ) ≃ M
    subst-id (var x)    = lookup-id x
    subst-id (app ω Ms) = app (subst-id* Ms)

    subst-id* : ∀ {Γ Δ} (Ms : Terms Γ Δ) → subst* Ms (id Γ) ≃* Ms
    subst-id* []       = []
    subst-id* (M ∷ Ms) = subst-id M ∷ subst-id* Ms

  subst-lookup : ∀ {Γ Δ Ξ σ}
                 (x : Var Ξ σ) (Ns : Terms Δ Ξ) (Os : Terms Γ Δ) →
                 lookup x (subst* Ns Os) ≃ subst (lookup x Ns) Os
  subst-lookup zero     (N ∷ Ns) Os = ≃-refl _
  subst-lookup (succ x) (N ∷ Ns) Os = subst-lookup x Ns Os

  mutual
    subst-assoc : ∀ {Γ Δ Ξ σ}
                   (M : Term Ξ σ) (Ns : Terms Δ Ξ) (Os : Terms Γ Δ) →
                   subst M (subst* Ns Os) ≃ subst (subst M Ns) Os
    subst-assoc (var x)    Ns Os = subst-lookup x Ns Os
    subst-assoc (app ω Ms) Ns Os = app (subst*-assoc Ms Ns Os)

    subst*-assoc : ∀ {Γ Δ Ξ Ζ}
                   (Ms : Terms Ξ Ζ) (Ns : Terms Δ Ξ) (Os : Terms Γ Δ) →
                   subst* Ms (subst* Ns Os) ≃* subst* (subst* Ms Ns) Os
    subst*-assoc [] Ns Os = []
    subst*-assoc (M ∷ Ms) Ns Os = subst-assoc M Ns Os ∷ subst*-assoc Ms Ns Os

  mutual
    subst-cong₂ : ∀ {Γ Δ σ} (M : Term Δ σ) {Os Ps : Terms Γ Δ} →
                  Os ≃* Ps → subst M Os ≃ subst M Ps
    subst-cong₂ (var x)    Os≃Ps = lookup-cong (≃-var-refl x) Os≃Ps
    subst-cong₂ (app ω Ms) Os≃Ps = app (subst*-cong₂ Ms Os≃Ps)

    subst*-cong₂ : ∀ {Γ Δ Ξ} (Ms : Terms Δ Ξ) {Os Ps : Terms Γ Δ} →
                   Os ≃* Ps → subst* Ms Os ≃* subst* Ms Ps
    subst*-cong₂ [] Os≃Ps = []
    subst*-cong₂ (M ∷ Ms) Os≃Ps = subst-cong₂ M Os≃Ps ∷ subst*-cong₂ Ms Os≃Ps

  mutual
    subst-cong₁ : ∀ {Γ Δ σ} {M N : Term Δ σ} {Os : Terms Γ Δ} →
                  M ≃ N → subst M Os ≃ subst N Os
    subst-cong₁ (var x≃y) = lookup-cong x≃y (≃*-refl _)
    subst-cong₁ (app Ms≃Ns) = app (subst*-cong₁ Ms≃Ns)
    subst-cong₁ {Os = Os} (eqn-inst η Ms) =
      ≃-trans (≃-sym (subst-assoc (eqn-lhs η) Ms Os))
     (≃-trans (eqn-inst η (subst* Ms Os))
              (subst-assoc (eqn-rhs η) Ms Os))
    subst-cong₁ (≃-trans M≃N N≃O) =
      ≃-trans (subst-cong₁ M≃N) (subst-cong₁ N≃O)
    subst-cong₁ (≃-sym M≃N) = ≃-sym (subst-cong₁ M≃N)

    subst*-cong₁ : ∀ {Γ Δ Ξ} {Ms Ns : Terms Δ Ξ} {Os : Terms Γ Δ} →
                   Ms ≃* Ns → subst* Ms Os ≃* subst* Ns Os
    subst*-cong₁ []             = []
    subst*-cong₁ (M≃N ∷ Ms≃Ns) = subst-cong₁ M≃N ∷ subst*-cong₁ Ms≃Ns

  ------------------------------------------------------------------------------
  -- Is a category

  cat : Category o (o ⊔ m) (e ⊔ o ⊔ m)
  cat .Category.obj = List sort
  cat .Category._⇒_ = Terms
  cat .Category._≈_ Ms Ns = LiftS (o ⊔ m) (Ms ≃* Ns)
  cat .Category.isEquiv .IsEquivalence.refl = liftS (≃*-refl _)
  cat .Category.isEquiv .IsEquivalence.sym (liftS eq) = liftS (≃*-sym eq)
  cat .Category.isEquiv .IsEquivalence.trans (liftS p) (liftS q) = liftS (≃*-trans p q)
  cat .Category.id = id
  cat .Category._∘_ = subst*
  cat .Category.∘-cong (liftS Ms≃Ns) (liftS Os≃Ps) =
    liftS (≃*-trans (subst*-cong₁ Ms≃Ns) (subst*-cong₂ _ Os≃Ps))
  cat .Category.id-left = liftS id-subst
  cat .Category.id-right = liftS (subst-id* _)
  cat .Category.assoc Ms Ns Os = liftS (≃*-sym (subst*-assoc Ms Ns Os))

  ------------------------------------------------------------------------------
  -- Finite products

  isTerminal : IsTerminal cat []
  isTerminal .IsTerminal.to-terminal = terminal
  isTerminal .IsTerminal.to-terminal-ext [] = liftS []

  pair-cong : ∀ {Γ Δ₁ Δ₂} {Ms₁ Ms₂ : Terms Γ Δ₁} {Ns₁ Ns₂ : Terms Γ Δ₂} →
              Ms₁ ≃* Ms₂ → Ns₁ ≃* Ns₂ → pair Ms₁ Ns₁ ≃* pair Ms₂ Ns₂
  pair-cong []                 Ns₁≃Ns₂ = Ns₁≃Ns₂
  pair-cong (M₁≃M₂ ∷ Ms₁≃Ms₂) Ns₁≃Ns₂ = M₁≃M₂ ∷ pair-cong Ms₁≃Ms₂ Ns₁≃Ns₂

  pair-p₁ : ∀ {Γ Δ₁ Δ₂} (Ms : Terms Γ Δ₁) (Ns : Terms Γ Δ₂) → subst* p₁ (pair Ms Ns) ≃* Ms
  pair-p₁ []       Ns = []
  pair-p₁ (M ∷ Ms) Ns = ≃-refl M ∷ ≃*-trans (subst*-wk* p₁ (pair Ms Ns) M) (pair-p₁ Ms Ns)

  pair-p₂ : ∀ {Γ Δ₁ Δ₂} (Ms : Terms Γ Δ₁) (Ns : Terms Γ Δ₂) → subst* p₂ (pair Ms Ns) ≃* Ns
  pair-p₂ []       Ns = id-subst
  pair-p₂ (M ∷ Ms) Ns = ≃*-trans (subst*-wk* p₂ (pair Ms Ns) M) (pair-p₂ Ms Ns)

  pair-ext : ∀ {Γ Δ₁ Δ₂} (Ms : Terms Γ (Δ₁ ++ Δ₂)) →
             pair {Γ} {Δ₁} {Δ₂} (subst* p₁ Ms) (subst* p₂ Ms) ≃* Ms
  pair-ext {Γ} {[]}     {Δ₂} Ms       = id-subst
  pair-ext {Γ} {σ ∷ Δ₁} {Δ₂} (M ∷ Ms) =
    ≃-refl M ∷ ≃*-trans (pair-cong {Γ} {Δ₁} {Δ₂}
                           (subst*-wk* p₁ Ms M) (subst*-wk* p₂ Ms M))
                         (pair-ext {Γ} {Δ₁} {Δ₂} Ms)

  products : HasProducts cat
  products .HasProducts.prod = _++_
  products .HasProducts.p₁ = p₁
  products .HasProducts.p₂ = p₂
  products .HasProducts.pair = pair
  products .HasProducts.pair-cong (liftS p) (liftS q) = liftS (pair-cong p q)
  products .HasProducts.pair-p₁ f g = liftS (pair-p₁ f g)
  products .HasProducts.pair-p₂ f g = liftS (pair-p₂ f g)
  products .HasProducts.pair-ext {Γ} {Δ₁} {Δ₂} f = liftS (pair-ext {Γ} {Δ₁} {Δ₂} f)

module model {o m o' m' e'} (𝕊 : Signature o m) (𝒞 : Category o' m' e') (𝒞P : HasProducts 𝒞) (𝒞T : HasTerminal 𝒞) where

  -- An interpretation is a map of sorts to objects, and operations to
  -- morphisms, such that the equations hold.

  -- Alternatively: a product preserving functor from the term
  -- category.

  open Signature 𝕊
  open Category 𝒞
  open HasTerminal 𝒞T renaming (witness to 𝟙)
  open HasProducts 𝒞P renaming (prod to _×_)

  ⟦_⟧* : List sort → (sort → obj) → obj
  ⟦ [] ⟧* ⟦_⟧ = 𝟙
  ⟦ σ ∷ σs ⟧* ⟦_⟧ = ⟦ σ ⟧ × ⟦ σs ⟧* ⟦_⟧

  record SignatureModel : Set (o ⊔ o' ⊔ m ⊔ m') where
    field
      interpSort : sort → obj
      interpOp   : ∀ {σs σ} (ω : op σs σ) → ⟦ σs ⟧* interpSort ⇒ interpSort σ

  module TermInterp (𝕊M : SignatureModel) where

    open Terms 𝕊 hiding (p₁; p₂; pair)
    open SignatureModel 𝕊M

    ⟦_⟧var : ∀ {Γ σ} → Var Γ σ → ⟦ Γ ⟧* interpSort ⇒ interpSort σ
    ⟦ Terms.zero ⟧var = p₁
    ⟦ Terms.succ x ⟧var = ⟦ x ⟧var ∘ p₂

    mutual
      ⟦_⟧tm : ∀ {Γ σ} → Term Γ σ → ⟦ Γ ⟧* interpSort ⇒ interpSort σ
      ⟦ Terms.var x ⟧tm = ⟦ x ⟧var
      ⟦ Terms.app ω ts ⟧tm = interpOp ω ∘ ⟦ ts ⟧tms

      ⟦_⟧tms : ∀ {Γ Γ'} → Terms Γ Γ' → ⟦ Γ ⟧* interpSort ⇒ ⟦ Γ' ⟧* interpSort
      ⟦ [] ⟧tms = to-terminal
      ⟦ t ∷ ts ⟧tms = pair ⟦ t ⟧tm ⟦ ts ⟧tms

  -- Given some equations, we can now ask whether these are supported
  -- by the interpretation.

  record Model {e} (𝔼 : Equations 𝕊 e) : Set (o ⊔ m ⊔ e ⊔ o' ⊔ m' ⊔ e') where
    field
      sigInterp : SignatureModel
    open SignatureModel sigInterp public
    open TermInterp sigInterp public
    open Equations 𝔼
    field
      eqns-satisfied : ∀ e → ⟦ eqn-lhs e ⟧tm ≈ ⟦ eqn-rhs e ⟧tm
