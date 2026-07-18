{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (_⊔_) renaming (suc to lsuc)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc; _+_; _<_; s≤s)
open import Data.Nat.Properties using (m≤m+n; m≤n+m)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤ₛ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl) renaming (subst to ≡-subst)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import categories using (Category)
open import signature using (Signature)
open import signature-algebra using (Algebra)
import matrix

-- Computability (totality) predicate on values: the existence content of the
-- logical relation, without the denotational component. Its fundamental lemma
-- is normalisation, yielding a total evaluator.
module language-totality
  {ℓ ℓ'} (Sig : Signature ℓ) (𝒜 : Algebra Sig ℓ')
  {o e} {A : Setoid o e} (S : CommutativeSemiring A)
  (sort-width : Signature.sort Sig → ℕ)
  where

open Signature Sig
open Algebra 𝒜
open import language-syntax Sig renaming (_,_ to _▸_)
open import type-substitution Sig using (unfold₁; unfold₁-inst; size)
open import language-evaluation Sig 𝒜
  using (Val; Env; unit; const; inl; inr; pair; clo; roll; emp; _·_)
open import language-evaluation-mat Sig 𝒜 S sort-width
  using (width; width-env; bases-width; module WithOpMats)

private
  module M = matrix.Mat S

module WithOp
  (op-mat : ∀ {is o'} → op is o' → Category._⇒_ M.cat (bases-width is) (sort-width o'))
  where

  open WithOpMats op-mat

  private
    ℓT = ℓ ⊔ ℓ' ⊔ o ⊔ e

  TSpec : type 0 → Set (lsuc ℓT)
  TSpec τ = Val τ → Set ℓT

  data MuTotal (τ₀ : type 1)
               (T< : (σ : type 0) → size σ < size (μ τ₀) → TSpec σ) :
               (σ' : type 1) → Val (σ' [ μ τ₀ ]) → Set ℓT where
    mt-roll  : ∀ {w} → MuTotal τ₀ T< τ₀ w → MuTotal τ₀ T< (var Fin.zero) (roll w)
    mt-unit  : MuTotal τ₀ T< unit unit
    mt-base  : ∀ {s c} → MuTotal τ₀ T< (base s) (const c)
    mt-arrow : ∀ {σ₁ σ₂ : type 0} {v} →
               (p : size {1} (σ₁ [→] σ₂) < size (μ τ₀)) →
               T< (σ₁ [→] σ₂) p v →
               MuTotal τ₀ T< (σ₁ [→] σ₂) v
    mt-inl   : ∀ {σ₁ σ₂ : type 1} {v} →
               MuTotal τ₀ T< σ₁ v → MuTotal τ₀ T< (σ₁ [+] σ₂) (inl v)
    mt-inr   : ∀ {σ₁ σ₂ : type 1} {v} →
               MuTotal τ₀ T< σ₂ v → MuTotal τ₀ T< (σ₁ [+] σ₂) (inr v)
    mt-pair  : ∀ {σ₁ σ₂ : type 1} {v₁ v₂} →
               MuTotal τ₀ T< σ₁ v₁ → MuTotal τ₀ T< σ₂ v₂ →
               MuTotal τ₀ T< (σ₁ [×] σ₂) (pair v₁ v₂)
    mt-mu    : ∀ {τ' : type 2} {w} →
               MuTotal τ₀ T< (unfold₁ τ') w →
               MuTotal τ₀ T< (μ τ') (roll (≡-subst Val (unfold₁-inst τ' (μ τ₀)) w))

  Total-acc : (τ : type 0) → Acc _<_ (size τ) → TSpec τ
  Total-acc (var ())
  Total-acc unit _ v = ⊤ₛ {ℓT}
  Total-acc (base s) _ v = ⊤ₛ {ℓT}
  Total-acc (σ [+] τ) (acc rs) (inl v) =
    Total-acc σ (rs (s≤s (m≤m+n (size σ) (size τ)))) v
  Total-acc (σ [+] τ) (acc rs) (inr v) =
    Total-acc τ (rs (s≤s (m≤n+m (size τ) (size σ)))) v
  Total-acc (σ [×] τ) (acc rs) (pair v u) =
    Total-acc σ (rs (s≤s (m≤m+n (size σ) (size τ)))) v ×
    Total-acc τ (rs (s≤s (m≤n+m (size τ) (size σ)))) u
  Total-acc (σ [→] τ) (acc rs) (clo {Γ'} γ' t) =
    ∀ (v : Val σ) → Total-acc σ (rs (s≤s (m≤m+n (size σ) (size τ)))) v →
    Σ (Val τ) λ u →
    Σ (Category._⇒_ M.cat (width-env γ' + width v) (width u)) λ R →
    (γ' · v ,, t ⇓ u [ R ]) ×
    Total-acc τ (rs (s≤s (m≤n+m (size τ) (size σ)))) u
  Total-acc (μ τ₀) (acc rs) v =
    MuTotal τ₀ (λ σ p → Total-acc σ (rs p)) (var Fin.zero) v

  Total : (τ : type 0) → TSpec τ
  Total τ = Total-acc τ (<-wellFounded (size τ))

  TotalEnv : (Γ : ctxt) → Env Γ → Set ℓT
  TotalEnv emp emp = ⊤ₛ {ℓT}
  TotalEnv (Γ ▸ τ) (γ · v) = TotalEnv Γ γ × Total τ v

  mu-total-map : ∀ {τ₀} {T< T<' : (σ : type 0) → size σ < size (μ τ₀) → TSpec σ} →
                 (∀ σ p {v} → T< σ p v → T<' σ p v) →
                 ∀ {σ' v} → MuTotal τ₀ T< σ' v → MuTotal τ₀ T<' σ' v
  mu-total-map f (mt-roll m)     = mt-roll (mu-total-map f m)
  mu-total-map f mt-unit         = mt-unit
  mu-total-map f mt-base         = mt-base
  mu-total-map f (mt-arrow p t)  = mt-arrow p (f _ p t)
  mu-total-map f (mt-inl m)      = mt-inl (mu-total-map f m)
  mu-total-map f (mt-inr m)      = mt-inr (mu-total-map f m)
  mu-total-map f (mt-pair m m')  = mt-pair (mu-total-map f m) (mu-total-map f m')
  mu-total-map f (mt-mu m)       = mt-mu (mu-total-map f m)

  -- Total-acc does not depend on the accessibility proof.
  total-irr-acc : ∀ τ → Acc _<_ (size τ) →
                  ∀ {ac ac' : Acc _<_ (size τ)} {v} →
                  Total-acc τ ac v → Total-acc τ ac' v
  total-irr-acc unit _ t = t
  total-irr-acc (base s) _ t = t
  total-irr-acc (σ [+] τ) (acc as) {acc rs} {acc rs'} {inl v} t =
    total-irr-acc σ (as (s≤s (m≤m+n (size σ) (size τ)))) t
  total-irr-acc (σ [+] τ) (acc as) {acc rs} {acc rs'} {inr v} t =
    total-irr-acc τ (as (s≤s (m≤n+m (size τ) (size σ)))) t
  total-irr-acc (σ [×] τ) (acc as) {acc rs} {acc rs'} {pair v u} (t , t') =
    total-irr-acc σ (as (s≤s (m≤m+n (size σ) (size τ)))) t ,
    total-irr-acc τ (as (s≤s (m≤n+m (size τ) (size σ)))) t'
  total-irr-acc (σ [→] τ) (acc as) {acc rs} {acc rs'} {clo γ' t₀} f = λ v tv →
    let (u , R , D , tu) = f v (total-irr-acc σ (as (s≤s (m≤m+n (size σ) (size τ)))) tv)
    in u , R , D , total-irr-acc τ (as (s≤s (m≤n+m (size τ) (size σ)))) tu
  total-irr-acc (μ τ₀) (acc as) {acc rs} {acc rs'} m =
    mu-total-map (λ σ p t → total-irr-acc σ (as p) t) m

  total-irr : ∀ τ {ac ac' : Acc _<_ (size τ)} {v} →
              Total-acc τ ac v → Total-acc τ ac' v
  total-irr τ = total-irr-acc τ (<-wellFounded (size τ))
