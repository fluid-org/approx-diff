{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; suc; _+_; _<_; _≤_; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; m≤n+m; n≤1+n)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import signature using (Signature)

-- Fusion laws for type-level renaming and substitution, and the unfolding law used to traverse values of
-- nested inductive types.
module type-substitution {ℓ} (Sig : Signature ℓ) where

open import language-syntax Sig hiding (_,_)

ren-cong : ∀ {Δ Δ'} {ρ ρ' : TyRen Δ Δ'} (τ : type Δ) → (∀ i → ρ i ≡ ρ' i) → ρ *ᵗ τ ≡ ρ' *ᵗ τ
ren-cong (var i)     e = cong var (e i)
ren-cong unit        e = refl
ren-cong (base s)    e = refl
ren-cong (τ₁ [+] τ₂) e = cong₂ _[+]_ (ren-cong τ₁ e) (ren-cong τ₂ e)
ren-cong (τ₁ [×] τ₂) e = cong₂ _[×]_ (ren-cong τ₁ e) (ren-cong τ₂ e)
ren-cong (τ₁ [→] τ₂) e = refl
ren-cong (μ τ)       e = cong μ (ren-cong τ λ { zero → refl ; (suc i) → cong suc (e i) })

ren-ren : ∀ {Δ₁ Δ₂ Δ₃} (ρ₁ : TyRen Δ₂ Δ₃) (ρ₂ : TyRen Δ₁ Δ₂) (τ : type Δ₁) →
          ρ₁ *ᵗ (ρ₂ *ᵗ τ) ≡ (λ i → ρ₁ (ρ₂ i)) *ᵗ τ
ren-ren ρ₁ ρ₂ (var i)     = refl
ren-ren ρ₁ ρ₂ unit        = refl
ren-ren ρ₁ ρ₂ (base s)    = refl
ren-ren ρ₁ ρ₂ (τ₁ [+] τ₂) = cong₂ _[+]_ (ren-ren ρ₁ ρ₂ τ₁) (ren-ren ρ₁ ρ₂ τ₂)
ren-ren ρ₁ ρ₂ (τ₁ [×] τ₂) = cong₂ _[×]_ (ren-ren ρ₁ ρ₂ τ₁) (ren-ren ρ₁ ρ₂ τ₂)
ren-ren ρ₁ ρ₂ (τ₁ [→] τ₂) = refl
ren-ren ρ₁ ρ₂ (μ τ)       =
  cong μ (trans (ren-ren (extᵗ ρ₁) (extᵗ ρ₂) τ)
                (ren-cong τ λ { zero → refl ; (suc i) → refl }))

sub-ren : ∀ {Δ₁ Δ₂ Δ₃} (σ : TySub Δ₂ Δ₃) (ρ : TyRen Δ₁ Δ₂) (τ : type Δ₁) →
          sub σ (ρ *ᵗ τ) ≡ sub (λ i → σ (ρ i)) τ
sub-ren σ ρ (var i)     = refl
sub-ren σ ρ unit        = refl
sub-ren σ ρ (base s)    = refl
sub-ren σ ρ (τ₁ [+] τ₂) = cong₂ _[+]_ (sub-ren σ ρ τ₁) (sub-ren σ ρ τ₂)
sub-ren σ ρ (τ₁ [×] τ₂) = cong₂ _[×]_ (sub-ren σ ρ τ₁) (sub-ren σ ρ τ₂)
sub-ren σ ρ (τ₁ [→] τ₂) = refl
sub-ren σ ρ (μ τ)       =
  cong μ (trans (sub-ren (sub-lift σ) (extᵗ ρ) τ)
                (sub-cong τ λ { zero → refl ; (suc i) → refl }))

ren-sub : ∀ {Δ₁ Δ₂ Δ₃} (ρ : TyRen Δ₂ Δ₃) (σ : TySub Δ₁ Δ₂) (τ : type Δ₁) →
          ρ *ᵗ sub σ τ ≡ sub (λ i → ρ *ᵗ σ i) τ
ren-sub ρ σ (var i)     = refl
ren-sub ρ σ unit        = refl
ren-sub ρ σ (base s)    = refl
ren-sub ρ σ (τ₁ [+] τ₂) = cong₂ _[+]_ (ren-sub ρ σ τ₁) (ren-sub ρ σ τ₂)
ren-sub ρ σ (τ₁ [×] τ₂) = cong₂ _[×]_ (ren-sub ρ σ τ₁) (ren-sub ρ σ τ₂)
ren-sub ρ σ (τ₁ [→] τ₂) = refl
ren-sub ρ σ (μ τ)       =
  cong μ (trans (ren-sub (extᵗ ρ) (sub-lift σ) τ)
                (sub-cong τ λ { zero → refl
                              ; (suc i) → trans (ren-ren (extᵗ ρ) suc (σ i))
                                                (sym (ren-ren suc ρ (σ i))) }))

sub-sub : ∀ {Δ₁ Δ₂ Δ₃} (σ₁ : TySub Δ₂ Δ₃) (σ₂ : TySub Δ₁ Δ₂) (τ : type Δ₁) →
          sub σ₁ (sub σ₂ τ) ≡ sub (λ i → sub σ₁ (σ₂ i)) τ
sub-sub σ₁ σ₂ (var i)     = refl
sub-sub σ₁ σ₂ unit        = refl
sub-sub σ₁ σ₂ (base s)    = refl
sub-sub σ₁ σ₂ (τ₁ [+] τ₂) = cong₂ _[+]_ (sub-sub σ₁ σ₂ τ₁) (sub-sub σ₁ σ₂ τ₂)
sub-sub σ₁ σ₂ (τ₁ [×] τ₂) = cong₂ _[×]_ (sub-sub σ₁ σ₂ τ₁) (sub-sub σ₁ σ₂ τ₂)
sub-sub σ₁ σ₂ (τ₁ [→] τ₂) = refl
sub-sub σ₁ σ₂ (μ τ)       =
  cong μ (trans (sub-sub (sub-lift σ₁) (sub-lift σ₂) τ)
                (sub-cong τ λ { zero → refl
                              ; (suc i) → trans (sub-ren (sub-lift σ₁) suc (σ₂ i))
                                                (sym (ren-sub suc σ₁ (σ₂ i))) }))

sub-id : ∀ {Δ} (τ : type Δ) → sub var τ ≡ τ
sub-id (var i)     = refl
sub-id unit        = refl
sub-id (base s)    = refl
sub-id (τ₁ [+] τ₂) = cong₂ _[+]_ (sub-id τ₁) (sub-id τ₂)
sub-id (τ₁ [×] τ₂) = cong₂ _[×]_ (sub-id τ₁) (sub-id τ₂)
sub-id (τ₁ [→] τ₂) = refl
sub-id (μ τ)       = cong μ (trans (sub-cong τ λ { zero → refl ; (suc i) → refl }) (sub-id τ))

unfold₁-sub : type 2 → TySub 2 1
unfold₁-sub τ zero    = μ τ
unfold₁-sub τ (suc i) = var i

unfold₁ : type 2 → type 1
unfold₁ τ = sub (unfold₁-sub τ) τ

unfold₁-inst : ∀ (τ : type 2) (ρ : type 0) →
               sub (push ρ) (unfold₁ τ) ≡
               sub (sub-lift (push ρ)) τ [ μ (sub (sub-lift (push ρ)) τ) ]
unfold₁-inst τ ρ =
  trans (sub-sub (push ρ) (unfold₁-sub τ) τ)
        (trans (sub-cong τ pw)
               (sym (sub-sub (push (μ A)) (sub-lift (push ρ)) τ)))
  where
    A : type 1
    A = sub (sub-lift (push ρ)) τ

    pw : ∀ i → sub (push ρ) (unfold₁-sub τ i) ≡
               sub (push (μ A)) (sub-lift (push ρ) i)
    pw zero          = refl
    pw (suc zero)    =
      sym (trans (sub-ren (push (μ A)) suc ρ)
                 (trans (sub-cong ρ λ ()) (sub-id ρ)))
    pw (suc (suc ()))

size : ∀ {Δ} → type Δ → ℕ
size (var i)   = 1
size unit      = 1
size (base s)  = 1
size (σ [+] τ) = suc (size σ + size τ)
size (σ [×] τ) = suc (size σ + size τ)
size (σ [→] τ) = suc (size σ + size τ)
size (μ τ)     = suc (size τ)

-- All arrow leaves have size below the bound. Substitution preserves arrow leaves verbatim, so the bound
-- survives renaming, substitution and unfolding.
arr-bound : ∀ {Δ} → ℕ → type Δ → Set
arr-bound n (var i)     = ⊤
arr-bound n unit        = ⊤
arr-bound n (base s)    = ⊤
arr-bound n (τ₁ [+] τ₂) = arr-bound n τ₁ × arr-bound n τ₂
arr-bound n (τ₁ [×] τ₂) = arr-bound n τ₁ × arr-bound n τ₂
arr-bound n (τ₁ [→] τ₂) = suc (size τ₁ + size τ₂) < n
arr-bound n (μ τ)       = arr-bound n τ

arr-mono : ∀ {Δ m n} (τ : type Δ) → m ≤ n → arr-bound m τ → arr-bound n τ
arr-mono (var i)     e b        = tt
arr-mono unit        e b        = tt
arr-mono (base s)    e b        = tt
arr-mono (τ₁ [+] τ₂) e (b , b') = arr-mono τ₁ e b , arr-mono τ₂ e b'
arr-mono (τ₁ [×] τ₂) e (b , b') = arr-mono τ₁ e b , arr-mono τ₂ e b'
arr-mono (τ₁ [→] τ₂) e b        = ≤-trans b e
arr-mono (μ τ)       e b        = arr-mono τ e b

arr-self : ∀ {Δ} (τ : type Δ) → arr-bound (suc (size τ)) τ
arr-self (var i)     = tt
arr-self unit        = tt
arr-self (base s)    = tt
arr-self (τ₁ [+] τ₂) = arr-mono τ₁ (s≤s (≤-trans (m≤m+n (size τ₁) (size τ₂)) (n≤1+n _))) (arr-self τ₁) ,
                       arr-mono τ₂ (s≤s (≤-trans (m≤n+m (size τ₂) (size τ₁)) (n≤1+n _))) (arr-self τ₂)
arr-self (τ₁ [×] τ₂) = arr-mono τ₁ (s≤s (≤-trans (m≤m+n (size τ₁) (size τ₂)) (n≤1+n _))) (arr-self τ₁) ,
                       arr-mono τ₂ (s≤s (≤-trans (m≤n+m (size τ₂) (size τ₁)) (n≤1+n _))) (arr-self τ₂)
arr-self (τ₁ [→] τ₂) = ≤-refl
arr-self (μ τ)       = arr-mono τ (s≤s (n≤1+n _)) (arr-self τ)

ren-arr : ∀ {Δ Δ' n} (ρ : TyRen Δ Δ') (τ : type Δ) → arr-bound n τ → arr-bound n (ρ *ᵗ τ)
ren-arr ρ (var i)     b        = tt
ren-arr ρ unit        b        = tt
ren-arr ρ (base s)    b        = tt
ren-arr ρ (τ₁ [+] τ₂) (b , b') = ren-arr ρ τ₁ b , ren-arr ρ τ₂ b'
ren-arr ρ (τ₁ [×] τ₂) (b , b') = ren-arr ρ τ₁ b , ren-arr ρ τ₂ b'
ren-arr ρ (τ₁ [→] τ₂) b        = b
ren-arr ρ (μ τ)       b        = ren-arr (extᵗ ρ) τ b

sub-arr : ∀ {Δ Δ' n} (σ : TySub Δ Δ') (τ : type Δ) →
          (∀ i → arr-bound n (σ i)) → arr-bound n τ → arr-bound n (sub σ τ)
sub-arr σ (var i)     bσ b        = bσ i
sub-arr σ unit        bσ b        = tt
sub-arr σ (base s)    bσ b        = tt
sub-arr σ (τ₁ [+] τ₂) bσ (b , b') = sub-arr σ τ₁ bσ b , sub-arr σ τ₂ bσ b'
sub-arr σ (τ₁ [×] τ₂) bσ (b , b') = sub-arr σ τ₁ bσ b , sub-arr σ τ₂ bσ b'
sub-arr σ (τ₁ [→] τ₂) bσ b        = b
sub-arr σ (μ τ)       bσ b        =
  sub-arr (sub-lift σ) τ (λ { zero → tt ; (suc i) → ren-arr suc (σ i) (bσ i) }) b

unfold₁-arr : ∀ {n} (τ : type 2) → arr-bound n τ → arr-bound n (unfold₁ τ)
unfold₁-arr τ b = sub-arr (unfold₁-sub τ) τ (λ { zero → b ; (suc i) → tt }) b
