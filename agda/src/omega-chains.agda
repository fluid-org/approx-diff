{-# OPTIONS --prop --postfix-projections --safe #-}

-- The shape category ω = (ℕ, ≤): diagrams over it are ω-chains, whose colimits underlie the
-- initial-algebra construction for polynomial functors. A chain is most conveniently given by its
-- step maps; `chain` packages these as a functor out of ω.

open import Level using (0ℓ)
open import Data.Nat using (ℕ; suc; _≤′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (≤′-trans; ≤′⇒≤; 1+n≰n)
open import prop using (⊤; tt)
open import prop-setoid using (⊤-isEquivalence)
open import categories using (Category)
open import functor using (Functor)

module omega-chains where

ω : Category 0ℓ 0ℓ 0ℓ
ω .Category.obj = ℕ
ω .Category._⇒_ m n = m ≤′ n
ω .Category._≈_ _ _ = ⊤
ω .Category.isEquiv = ⊤-isEquivalence
ω .Category.id n = ≤′-refl
ω .Category._∘_ f g = ≤′-trans g f
ω .Category.∘-cong _ _ = tt
ω .Category.id-left = tt
ω .Category.id-right = tt
ω .Category.assoc _ _ _ = tt

module _ {o m e} {𝒞 : Category o m e} where
  open Category 𝒞

  chain : (X : ℕ → obj) → (∀ n → X n ⇒ X (suc n)) → Functor ω 𝒞
  chain X f = record
    { fobj = X ; fmor = walk ; fmor-cong = λ {_} {_} {p} {q} _ → walk-cong p q
    ; fmor-id = ≈-refl ; fmor-comp = λ p q → walk-comp p q }
    where
      walk : ∀ {m n} → m ≤′ n → X m ⇒ X n
      walk ≤′-refl     = id _
      walk (≤′-step p) = f _ ∘ walk p

      -- Any two parallel walks agree: ≤′ is propositional, up to the absurd mixed cases.
      walk-cong : ∀ {m n} (p q : m ≤′ n) → walk p ≈ walk q
      walk-cong ≤′-refl     ≤′-refl     = ≈-refl
      walk-cong ≤′-refl     (≤′-step q) with () ← 1+n≰n (≤′⇒≤ q)
      walk-cong (≤′-step p) ≤′-refl     with () ← 1+n≰n (≤′⇒≤ p)
      walk-cong (≤′-step p) (≤′-step q) = ∘-cong₂ (walk-cong p q)

      walk-comp : ∀ {x y z} (p : y ≤′ z) (q : x ≤′ y) → walk (≤′-trans q p) ≈ (walk p ∘ walk q)
      walk-comp ≤′-refl     q = ≈-sym id-left
      walk-comp (≤′-step p) q = ≈-trans (∘-cong₂ (walk-comp p q)) (≈-sym (assoc _ _ _))
