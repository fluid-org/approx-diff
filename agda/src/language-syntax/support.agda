{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.Nat using (ℕ; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
import nat
open import Data.List.Relation.Unary.All using ([]; _∷_) renaming (All to Every)
open import signature using (Signature)

-- Support: the subcontext of entries a term mentions, presented as a thinning of its context.
-- Strengthening retypes a term in any subcontext whose thinning covers its support, and renaming
-- along the thinning's embedding recovers the term: embed-strengthen.
module language-syntax.support {ℓ} (Sig : Signature ℓ) where

open Signature Sig using (sort)
open import language-syntax Sig

data thinning : ctxt → Set ℓ where
  emp  : thinning emp
  keep : ∀ {Γ τ} → thinning Γ → thinning (Γ , τ)
  drop : ∀ {Γ τ} → thinning Γ → thinning (Γ , τ)

restrict : ∀ {Γ} → thinning Γ → ctxt
restrict emp              = emp
restrict (keep {τ = τ} θ) = restrict θ , τ
restrict (drop θ)         = restrict θ

embed : ∀ {Γ} (θ : thinning Γ) → Ren (restrict θ) Γ
embed emp      ()
embed (keep θ) = ext (embed θ)
embed (drop θ) x = succ (embed θ x)

none : ∀ {Γ} → thinning Γ
none {emp}   = emp
none {Γ , τ} = drop none

var-thinning : ∀ {Γ τ} → Γ ∋ τ → thinning Γ
var-thinning zero     = keep none
var-thinning (succ x) = drop (var-thinning x)

tail : ∀ {Γ τ} → thinning (Γ , τ) → thinning Γ
tail (keep θ) = θ
tail (drop θ) = θ

_∪_ : ∀ {Γ} → thinning Γ → thinning Γ → thinning Γ
emp    ∪ emp     = emp
keep θ ∪ keep θ' = keep (θ ∪ θ')
keep θ ∪ drop θ' = keep (θ ∪ θ')
drop θ ∪ keep θ' = keep (θ ∪ θ')
drop θ ∪ drop θ' = drop (θ ∪ θ')

infixl 40 _∪_

mutual
  support : ∀ {Γ τ} → Γ ⊢ τ → thinning Γ
  support (var x)        = var-thinning x
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

  supports : ∀ {Γ σs} → Every (λ σ → Γ ⊢ base σ) σs → thinning Γ
  supports []       = none
  supports (t ∷ ts) = support t ∪ supports ts

mutual
  size : ∀ {Γ τ} → Γ ⊢ τ → ℕ
  size (var x)        = 1
  size unit           = 1
  size (inl t)        = suc (size t)
  size (inr t)        = suc (size t)
  size (case s t₁ t₂) = suc (size s + size t₁ + size t₂)
  size (pair s t)     = suc (size s + size t)
  size (fst t)        = suc (size t)
  size (snd t)        = suc (size t)
  size (lam t)        = suc (size t)
  size (app s t)      = suc (size s + size t)
  size (bop ω ts)     = suc (sizes ts)
  size (brel ω ts)    = suc (sizes ts)
  size (roll t)       = suc (size t)
  size (fold s t)     = suc (size s + size t)

  sizes : ∀ {Γ σs} → Every (λ σ → Γ ⊢ base σ) σs → ℕ
  sizes []       = 0
  sizes (t ∷ ts) = suc (size t + sizes ts)

size-positive : ∀ {Γ τ} (t : Γ ⊢ τ) → 1 nat.≤ size t
size-positive (var x)        = nat.≤-refl
size-positive unit           = nat.≤-refl
size-positive (inl t)        = nat.s≤s nat.0≤n
size-positive (inr t)        = nat.s≤s nat.0≤n
size-positive (case s t₁ t₂) = nat.s≤s nat.0≤n
size-positive (pair s t)     = nat.s≤s nat.0≤n
size-positive (fst t)        = nat.s≤s nat.0≤n
size-positive (snd t)        = nat.s≤s nat.0≤n
size-positive (lam t)        = nat.s≤s nat.0≤n
size-positive (app s t)      = nat.s≤s nat.0≤n
size-positive (bop ω ts)     = nat.s≤s nat.0≤n
size-positive (brel ω ts)    = nat.s≤s nat.0≤n
size-positive (roll t)       = nat.s≤s nat.0≤n
size-positive (fold s t)     = nat.s≤s nat.0≤n

data _⊆_ : ∀ {Γ} → thinning Γ → thinning Γ → Set ℓ where
  emp  : emp ⊆ emp
  keep : ∀ {Γ τ} {θ θ' : thinning Γ} → θ ⊆ θ' → keep {τ = τ} θ ⊆ keep θ'
  drop : ∀ {Γ τ} {θ θ' : thinning Γ} → θ ⊆ θ' → drop {τ = τ} θ ⊆ drop θ'
  add  : ∀ {Γ τ} {θ θ' : thinning Γ} → θ ⊆ θ' → drop {τ = τ} θ ⊆ keep θ'

infix 4 _⊆_

⊆-refl : ∀ {Γ} {θ : thinning Γ} → θ ⊆ θ
⊆-refl {θ = emp}    = emp
⊆-refl {θ = keep θ} = keep ⊆-refl
⊆-refl {θ = drop θ} = drop ⊆-refl

⊆-trans : ∀ {Γ} {θ θ' θ'' : thinning Γ} → θ ⊆ θ' → θ' ⊆ θ'' → θ ⊆ θ''
⊆-trans emp      emp       = emp
⊆-trans (keep h) (keep h') = keep (⊆-trans h h')
⊆-trans (drop h) (drop h') = drop (⊆-trans h h')
⊆-trans (drop h) (add h')  = add (⊆-trans h h')
⊆-trans (add h)  (keep h') = add (⊆-trans h h')

∪-⊆₁ : ∀ {Γ} (θ θ' : thinning Γ) → θ ⊆ θ ∪ θ'
∪-⊆₁ emp      emp       = emp
∪-⊆₁ (keep θ) (keep θ') = keep (∪-⊆₁ θ θ')
∪-⊆₁ (keep θ) (drop θ') = keep (∪-⊆₁ θ θ')
∪-⊆₁ (drop θ) (keep θ') = add (∪-⊆₁ θ θ')
∪-⊆₁ (drop θ) (drop θ') = drop (∪-⊆₁ θ θ')

∪-⊆₂ : ∀ {Γ} (θ θ' : thinning Γ) → θ' ⊆ θ ∪ θ'
∪-⊆₂ emp      emp       = emp
∪-⊆₂ (keep θ) (keep θ') = keep (∪-⊆₂ θ θ')
∪-⊆₂ (keep θ) (drop θ') = add (∪-⊆₂ θ θ')
∪-⊆₂ (drop θ) (keep θ') = keep (∪-⊆₂ θ θ')
∪-⊆₂ (drop θ) (drop θ') = drop (∪-⊆₂ θ θ')

∪-bound₁ : ∀ {Γ} {θ₁ θ₂ θ : thinning Γ} → θ₁ ∪ θ₂ ⊆ θ → θ₁ ⊆ θ
∪-bound₁ = ⊆-trans (∪-⊆₁ _ _)

∪-bound₂ : ∀ {Γ} {θ₁ θ₂ θ : thinning Γ} → θ₁ ∪ θ₂ ⊆ θ → θ₂ ⊆ θ
∪-bound₂ = ⊆-trans (∪-⊆₂ _ _)

keep-tail : ∀ {Γ τ} {θ₀ : thinning (Γ , τ)} {θ : thinning Γ} → tail θ₀ ⊆ θ → θ₀ ⊆ keep θ
keep-tail {θ₀ = keep θ₀} h = keep h
keep-tail {θ₀ = drop θ₀} h = add h

strengthen-var : ∀ {Γ τ} (x : Γ ∋ τ) {θ : thinning Γ} → var-thinning x ⊆ θ → restrict θ ∋ τ
strengthen-var zero     (keep _) = zero
strengthen-var (succ x) (add h)  = succ (strengthen-var x h)
strengthen-var (succ x) (drop h) = strengthen-var x h

mutual
  strengthen : ∀ {Γ τ} (t : Γ ⊢ τ) {θ : thinning Γ} → support t ⊆ θ → restrict θ ⊢ τ
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

  strengthens : ∀ {Γ σs} (ts : Every (λ σ → Γ ⊢ base σ) σs) {θ : thinning Γ} → supports ts ⊆ θ →
                Every (λ σ → restrict θ ⊢ base σ) σs
  strengthens []       h = []
  strengthens (t ∷ ts) h = strengthen t (∪-bound₁ h) ∷ strengthens ts (∪-bound₂ h)

body-thinning : ∀ {Γ σ τ} → Γ , σ ⊢ τ → thinning Γ
body-thinning t = tail (support t)

strengthen-body : ∀ {Γ σ τ} (t : Γ , σ ⊢ τ) → restrict (body-thinning t) , σ ⊢ τ
strengthen-body t = strengthen t (keep-tail ⊆-refl)

private
  cong₃ : ∀ {A B C D : Set ℓ} (f : A → B → C → D) {a a' b b' c c'} →
          a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
  cong₃ f refl refl refl = refl

embed-var : ∀ {Γ τ} (x : Γ ∋ τ) {θ : thinning Γ} (h : var-thinning x ⊆ θ) →
            embed θ (strengthen-var x h) ≡ x
embed-var zero     (keep _) = refl
embed-var (succ x) (add h)  = cong succ (embed-var x h)
embed-var (succ x) (drop h) = cong succ (embed-var x h)

mutual
  embed-strengthen : ∀ {Γ τ} (t : Γ ⊢ τ) {θ : thinning Γ} (h : support t ⊆ θ) →
                     embed θ * strengthen t h ≡ t
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

  embed-strengthens : ∀ {Γ σs} (ts : Every (λ σ → Γ ⊢ base σ) σs) {θ : thinning Γ}
                      (h : supports ts ⊆ θ) → embed θ ** strengthens ts h ≡ ts
  embed-strengthens []       h = refl
  embed-strengthens (t ∷ ts) h = cong₂ _∷_ (embed-strengthen t (∪-bound₁ h)) (embed-strengthens ts (∪-bound₂ h))

mutual
  size-strengthen : ∀ {Γ τ} (t : Γ ⊢ τ) {θ : thinning Γ} (h : support t ⊆ θ) →
                    size (strengthen t h) ≡ size t
  size-strengthen (var x)        h = refl
  size-strengthen unit           h = refl
  size-strengthen (inl t)        h = cong suc (size-strengthen t h)
  size-strengthen (inr t)        h = cong suc (size-strengthen t h)
  size-strengthen (case s t₁ t₂) h =
    cong suc (cong₂ _+_ (cong₂ _+_ (size-strengthen s (∪-bound₁ (∪-bound₁ h)))
                                   (size-strengthen t₁ (keep-tail (∪-bound₂ (∪-bound₁ h)))))
                        (size-strengthen t₂ (keep-tail (∪-bound₂ h))))
  size-strengthen (pair s t)     h =
    cong suc (cong₂ _+_ (size-strengthen s (∪-bound₁ h)) (size-strengthen t (∪-bound₂ h)))
  size-strengthen (fst t)        h = cong suc (size-strengthen t h)
  size-strengthen (snd t)        h = cong suc (size-strengthen t h)
  size-strengthen (lam t)        h = cong suc (size-strengthen t (keep-tail h))
  size-strengthen (app s t)      h =
    cong suc (cong₂ _+_ (size-strengthen s (∪-bound₁ h)) (size-strengthen t (∪-bound₂ h)))
  size-strengthen (bop ω ts)     h = cong suc (sizes-strengthens ts h)
  size-strengthen (brel ω ts)    h = cong suc (sizes-strengthens ts h)
  size-strengthen (roll t)       h = cong suc (size-strengthen t h)
  size-strengthen (fold s t)     h =
    cong suc (cong₂ _+_ (size-strengthen s (keep-tail (∪-bound₁ h))) (size-strengthen t (∪-bound₂ h)))

  sizes-strengthens : ∀ {Γ σs} (ts : Every (λ σ → Γ ⊢ base σ) σs) {θ : thinning Γ}
                      (h : supports ts ⊆ θ) → sizes (strengthens ts h) ≡ sizes ts
  sizes-strengthens []       h = refl
  sizes-strengthens (t ∷ ts) h =
    cong suc (cong₂ _+_ (size-strengthen t (∪-bound₁ h)) (sizes-strengthens ts (∪-bound₂ h)))
