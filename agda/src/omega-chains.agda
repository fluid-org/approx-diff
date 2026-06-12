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
open import functor using (Functor; NatTrans; Colimit) renaming (_∘_ to _∘NT_)

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

  module _ (X : ℕ → obj) (f : ∀ n → X n ⇒ X (suc n)) where
    private
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

    chain : Functor ω 𝒞
    chain .Functor.fobj = X
    chain .Functor.fmor = walk
    chain .Functor.fmor-cong {_} {_} {p} {q} _ = walk-cong p q
    chain .Functor.fmor-id = ≈-refl
    chain .Functor.fmor-comp = walk-comp

  -- Stage maps commuting with the steps induce a natural transformation between chains, and a
  -- mediating morphism between their colimits.
  module _ {X Y : ℕ → obj} (f : ∀ n → X n ⇒ X (suc n)) (g : ∀ n → Y n ⇒ Y (suc n))
           (h : ∀ n → X n ⇒ Y n)
           (h-step : ∀ n → (h (suc n) ∘ f n) ≈ (g n ∘ h n)) where

    open NatTrans

    chain-map : NatTrans (chain X f) (chain Y g)
    chain-map .transf = h
    chain-map .natural p = square p
      where
        square : ∀ {k n} (p : k ≤′ n) → (chain Y g .Functor.fmor p ∘ h k) ≈ (h n ∘ chain X f .Functor.fmor p)
        square ≤′-refl     = id-swap
        square (≤′-step p) =
          ≈-trans (assoc _ _ _)
          (≈-trans (∘-cong₂ (square p))
          (≈-trans (≈-sym (assoc _ _ _))
          (≈-trans (∘-cong₁ (≈-sym (h-step _))) (assoc _ _ _))))

    colim-map : (CX : Colimit (chain X f)) (CY : Colimit (chain Y g)) → CX .Colimit.apex ⇒ CY .Colimit.apex
    colim-map CX CY = CX .Colimit.colambda _ (CY .Colimit.cocone ∘NT chain-map)
