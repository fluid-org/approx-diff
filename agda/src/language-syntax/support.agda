{-# OPTIONS --prop --postfix-projections --safe #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Data.List.Relation.Unary.All using ([]; _∷_) renaming (All to Every)
open import signature using (Signature)

-- Support: the subcontext of entries a term mentions, as a mask over its context. Strengthening
-- retypes a term in any subcontext whose mask covers its support, and renaming along the mask's
-- embedding recovers the term: embed-strengthen.
module language-syntax.support {ℓ} (Sig : Signature ℓ) where

open Signature Sig using (sort)
open import language-syntax Sig

data mask : ctxt → Set ℓ where
  emp  : mask emp
  keep : ∀ {Γ τ} → mask Γ → mask (Γ , τ)
  drop : ∀ {Γ τ} → mask Γ → mask (Γ , τ)

restrict : ∀ {Γ} → mask Γ → ctxt
restrict emp              = emp
restrict (keep {τ = τ} m) = restrict m , τ
restrict (drop m)         = restrict m

embed : ∀ {Γ} (m : mask Γ) → Ren (restrict m) Γ
embed emp      ()
embed (keep m) = ext (embed m)
embed (drop m) x = succ (embed m x)

none : ∀ {Γ} → mask Γ
none {emp}   = emp
none {Γ , τ} = drop none

var-mask : ∀ {Γ τ} → Γ ∋ τ → mask Γ
var-mask zero     = keep none
var-mask (succ x) = drop (var-mask x)

tail : ∀ {Γ τ} → mask (Γ , τ) → mask Γ
tail (keep m) = m
tail (drop m) = m

_∪_ : ∀ {Γ} → mask Γ → mask Γ → mask Γ
emp    ∪ emp     = emp
keep m ∪ keep m' = keep (m ∪ m')
keep m ∪ drop m' = keep (m ∪ m')
drop m ∪ keep m' = keep (m ∪ m')
drop m ∪ drop m' = drop (m ∪ m')

infixl 40 _∪_

mutual
  support : ∀ {Γ τ} → Γ ⊢ τ → mask Γ
  support (var x)        = var-mask x
  support unit           = none
  support (inl t)        = support t
  support (inr t)        = support t
  support (case s t₁ t₂) = support s ∪ tail (support t₁) ∪ tail (support t₂)
  support (pair s t)     = support s ∪ support t
  support (fst t)        = support t
  support (snd t)        = support t
  support (lam t)        = tail (support t)
  support (app s t)      = support s ∪ support t
  support (bop ω ts)     = supports ts
  support (brel ω ts)    = supports ts
  support (roll t)       = support t
  support (fold s t)     = tail (support s) ∪ support t

  supports : ∀ {Γ σs} → Every (λ σ → Γ ⊢ base σ) σs → mask Γ
  supports []       = none
  supports (t ∷ ts) = support t ∪ supports ts

data _⊆_ : ∀ {Γ} → mask Γ → mask Γ → Set ℓ where
  emp  : emp ⊆ emp
  keep : ∀ {Γ τ} {m m' : mask Γ} → m ⊆ m' → keep {τ = τ} m ⊆ keep m'
  drop : ∀ {Γ τ} {m m' : mask Γ} → m ⊆ m' → drop {τ = τ} m ⊆ drop m'
  add  : ∀ {Γ τ} {m m' : mask Γ} → m ⊆ m' → drop {τ = τ} m ⊆ keep m'

infix 4 _⊆_

⊆-refl : ∀ {Γ} {m : mask Γ} → m ⊆ m
⊆-refl {m = emp}    = emp
⊆-refl {m = keep m} = keep ⊆-refl
⊆-refl {m = drop m} = drop ⊆-refl

⊆-trans : ∀ {Γ} {m m' m'' : mask Γ} → m ⊆ m' → m' ⊆ m'' → m ⊆ m''
⊆-trans emp      emp       = emp
⊆-trans (keep h) (keep h') = keep (⊆-trans h h')
⊆-trans (drop h) (drop h') = drop (⊆-trans h h')
⊆-trans (drop h) (add h')  = add (⊆-trans h h')
⊆-trans (add h)  (keep h') = add (⊆-trans h h')

∪-⊆₁ : ∀ {Γ} (m m' : mask Γ) → m ⊆ m ∪ m'
∪-⊆₁ emp      emp       = emp
∪-⊆₁ (keep m) (keep m') = keep (∪-⊆₁ m m')
∪-⊆₁ (keep m) (drop m') = keep (∪-⊆₁ m m')
∪-⊆₁ (drop m) (keep m') = add (∪-⊆₁ m m')
∪-⊆₁ (drop m) (drop m') = drop (∪-⊆₁ m m')

∪-⊆₂ : ∀ {Γ} (m m' : mask Γ) → m' ⊆ m ∪ m'
∪-⊆₂ emp      emp       = emp
∪-⊆₂ (keep m) (keep m') = keep (∪-⊆₂ m m')
∪-⊆₂ (keep m) (drop m') = add (∪-⊆₂ m m')
∪-⊆₂ (drop m) (keep m') = keep (∪-⊆₂ m m')
∪-⊆₂ (drop m) (drop m') = drop (∪-⊆₂ m m')

∪-bound₁ : ∀ {Γ} {m₁ m₂ m : mask Γ} → m₁ ∪ m₂ ⊆ m → m₁ ⊆ m
∪-bound₁ = ⊆-trans (∪-⊆₁ _ _)

∪-bound₂ : ∀ {Γ} {m₁ m₂ m : mask Γ} → m₁ ∪ m₂ ⊆ m → m₂ ⊆ m
∪-bound₂ = ⊆-trans (∪-⊆₂ _ _)

-- A binder body's mask is included in any mask that keeps the bound entry and covers its tail.
keep-tail : ∀ {Γ τ} {m₀ : mask (Γ , τ)} {m : mask Γ} → tail m₀ ⊆ m → m₀ ⊆ keep m
keep-tail {m₀ = keep m₀} h = keep h
keep-tail {m₀ = drop m₀} h = add h

strengthen-var : ∀ {Γ τ} (x : Γ ∋ τ) {m : mask Γ} → var-mask x ⊆ m → restrict m ∋ τ
strengthen-var zero     (keep _) = zero
strengthen-var (succ x) (add h)  = succ (strengthen-var x h)
strengthen-var (succ x) (drop h) = strengthen-var x h

mutual
  strengthen : ∀ {Γ τ} (t : Γ ⊢ τ) {m : mask Γ} → support t ⊆ m → restrict m ⊢ τ
  strengthen (var x)        h = var (strengthen-var x h)
  strengthen unit           h = unit
  strengthen (inl t)        h = inl (strengthen t h)
  strengthen (inr t)        h = inr (strengthen t h)
  strengthen (case s t₁ t₂) h = case (strengthen s (∪-bound₁ (∪-bound₁ h)))
                                     (strengthen t₁ (keep-tail (∪-bound₂ (∪-bound₁ h))))
                                     (strengthen t₂ (keep-tail (∪-bound₂ h)))
  strengthen (pair s t)     h = pair (strengthen s (∪-bound₁ h)) (strengthen t (∪-bound₂ h))
  strengthen (fst t)        h = fst (strengthen t h)
  strengthen (snd t)        h = snd (strengthen t h)
  strengthen (lam t)        h = lam (strengthen t (keep-tail h))
  strengthen (app s t)      h = app (strengthen s (∪-bound₁ h)) (strengthen t (∪-bound₂ h))
  strengthen (bop ω ts)     h = bop ω (strengthens ts h)
  strengthen (brel ω ts)    h = brel ω (strengthens ts h)
  strengthen (roll t)       h = roll (strengthen t h)
  strengthen (fold s t)     h = fold (strengthen s (keep-tail (∪-bound₁ h))) (strengthen t (∪-bound₂ h))

  strengthens : ∀ {Γ σs} (ts : Every (λ σ → Γ ⊢ base σ) σs) {m : mask Γ} → supports ts ⊆ m →
                Every (λ σ → restrict m ⊢ base σ) σs
  strengthens []       h = []
  strengthens (t ∷ ts) h = strengthen t (∪-bound₁ h) ∷ strengthens ts (∪-bound₂ h)

private
  cong₃ : ∀ {A B C D : Set ℓ} (f : A → B → C → D) {a a' b b' c c'} →
          a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
  cong₃ f refl refl refl = refl

embed-var : ∀ {Γ τ} (x : Γ ∋ τ) {m : mask Γ} (h : var-mask x ⊆ m) → embed m (strengthen-var x h) ≡ x
embed-var zero     (keep _) = refl
embed-var (succ x) (add h)  = cong succ (embed-var x h)
embed-var (succ x) (drop h) = cong succ (embed-var x h)

mutual
  embed-strengthen : ∀ {Γ τ} (t : Γ ⊢ τ) {m : mask Γ} (h : support t ⊆ m) →
                     embed m * strengthen t h ≡ t
  embed-strengthen (var x)        h = cong var (embed-var x h)
  embed-strengthen unit           h = refl
  embed-strengthen (inl t)        h = cong inl (embed-strengthen t h)
  embed-strengthen (inr t)        h = cong inr (embed-strengthen t h)
  embed-strengthen (case s t₁ t₂) h = cong₃ case (embed-strengthen s (∪-bound₁ (∪-bound₁ h)))
                                                 (embed-strengthen t₁ (keep-tail (∪-bound₂ (∪-bound₁ h))))
                                                 (embed-strengthen t₂ (keep-tail (∪-bound₂ h)))
  embed-strengthen (pair s t)     h = cong₂ pair (embed-strengthen s (∪-bound₁ h))
                                                 (embed-strengthen t (∪-bound₂ h))
  embed-strengthen (fst t)        h = cong fst (embed-strengthen t h)
  embed-strengthen (snd t)        h = cong snd (embed-strengthen t h)
  embed-strengthen (lam t)        h = cong lam (embed-strengthen t (keep-tail h))
  embed-strengthen (app s t)      h = cong₂ app (embed-strengthen s (∪-bound₁ h))
                                                (embed-strengthen t (∪-bound₂ h))
  embed-strengthen (bop ω ts)     h = cong (bop ω) (embed-strengthens ts h)
  embed-strengthen (brel ω ts)    h = cong (brel ω) (embed-strengthens ts h)
  embed-strengthen (roll t)       h = cong roll (embed-strengthen t h)
  embed-strengthen (fold s t)     h = cong₂ fold (embed-strengthen s (keep-tail (∪-bound₁ h)))
                                                 (embed-strengthen t (∪-bound₂ h))

  embed-strengthens : ∀ {Γ σs} (ts : Every (λ σ → Γ ⊢ base σ) σs) {m : mask Γ} (h : supports ts ⊆ m) →
                      embed m ** strengthens ts h ≡ ts
  embed-strengthens []       h = refl
  embed-strengthens (t ∷ ts) h = cong₂ _∷_ (embed-strengthen t (∪-bound₁ h)) (embed-strengthens ts (∪-bound₂ h))
