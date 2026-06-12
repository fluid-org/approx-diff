{-# OPTIONS --prop --postfix-projections --safe #-}

-- The shape category ω = (ℕ, ≤): diagrams over it are ω-chains, whose colimits underlie the
-- initial-algebra construction for polynomial functors. A chain is most conveniently given by its
-- step maps; `chain` packages these as a functor out of ω.

open import Level using (0ℓ)
open import Data.Nat using (ℕ; suc; _≤′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (≤′-trans; ≤′⇒≤; 1+n≰n)
open import prop using (⊤; tt)
open import prop-setoid using (⊤-isEquivalence; module ≈-Reasoning)
open import categories using (Category)
open import functor using (Functor; NatTrans; ≃-NatTrans; Colimit; constFmor) renaming (_∘_ to _∘NT_)

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

  -- The mediating morphism respects pointwise-equal stage maps (and so is independent of the squares).
  colim-map-cong : ∀ {X Y : ℕ → obj} {f : ∀ n → X n ⇒ X (suc n)} {g : ∀ n → Y n ⇒ Y (suc n)}
                   {h h' : ∀ n → X n ⇒ Y n}
                   {h-step : ∀ n → (h (suc n) ∘ f n) ≈ (g n ∘ h n)}
                   {h'-step : ∀ n → (h' (suc n) ∘ f n) ≈ (g n ∘ h' n)} →
                   (∀ n → h n ≈ h' n) → ∀ CX CY →
                   colim-map f g h h-step CX CY ≈ colim-map f g h' h'-step CX CY
  colim-map-cong h≈h' CX CY =
    CX .Colimit.colambda-cong (record { transf-eq = λ n → ∘-cong₂ (h≈h' n) })

  -- Composite stage maps satisfy the composite square.
  square-comp : ∀ {X Y Z : ℕ → obj}
                {f : ∀ n → X n ⇒ X (suc n)} {g : ∀ n → Y n ⇒ Y (suc n)} {e : ∀ n → Z n ⇒ Z (suc n)}
                {h : ∀ n → X n ⇒ Y n} {k : ∀ n → Y n ⇒ Z n} →
                (∀ n → (h (suc n) ∘ f n) ≈ (g n ∘ h n)) →
                (∀ n → (k (suc n) ∘ g n) ≈ (e n ∘ k n)) →
                ∀ n → ((k (suc n) ∘ h (suc n)) ∘ f n) ≈ (e n ∘ (k n ∘ h n))
  square-comp h-step k-step n =
    ≈-trans (assoc _ _ _)
    (≈-trans (∘-cong₂ (h-step n))
    (≈-trans (≈-sym (assoc _ _ _))
    (≈-trans (∘-cong₁ (k-step n)) (assoc _ _ _))))

  -- Mediating morphisms compose.
  colim-map-comp : ∀ {X Y Z : ℕ → obj}
                   {f : ∀ n → X n ⇒ X (suc n)} {g : ∀ n → Y n ⇒ Y (suc n)} {e : ∀ n → Z n ⇒ Z (suc n)}
                   {h : ∀ n → X n ⇒ Y n} {k : ∀ n → Y n ⇒ Z n}
                   {h-step : ∀ n → (h (suc n) ∘ f n) ≈ (g n ∘ h n)}
                   {k-step : ∀ n → (k (suc n) ∘ g n) ≈ (e n ∘ k n)}
                   {kh-step : ∀ n → ((k (suc n) ∘ h (suc n)) ∘ f n) ≈ (e n ∘ (k n ∘ h n))} →
                   ∀ CX CY CZ →
                   colim-map f e (λ n → k n ∘ h n) kh-step CX CZ
                     ≈ (colim-map g e k k-step CY CZ ∘ colim-map f g h h-step CX CY)
  colim-map-comp {f = f} {g} {e} {h} {k} {h-step} {k-step} {kh-step} CX CY CZ =
    ≈-trans (CX .Colimit.colambda-cong E) (CX .Colimit.colambda-ext _ _)
    where
      open NatTrans

      E : ≃-NatTrans (CZ .Colimit.cocone ∘NT chain-map f e (λ n → k n ∘ h n) kh-step)
                     (constFmor (colim-map g e k k-step CY CZ ∘ colim-map f g h h-step CX CY)
                        ∘NT CX .Colimit.cocone)
      E .≃-NatTrans.transf-eq n = begin
          CZ .Colimit.cocone .transf n ∘ (k n ∘ h n)
        ≈˘⟨ assoc _ _ _ ⟩
          (CZ .Colimit.cocone .transf n ∘ k n) ∘ h n
        ≈˘⟨ ∘-cong₁ (CY .Colimit.colambda-coeval _ _ .≃-NatTrans.transf-eq n) ⟩
          (colim-map g e k k-step CY CZ ∘ CY .Colimit.cocone .transf n) ∘ h n
        ≈⟨ assoc _ _ _ ⟩
          colim-map g e k k-step CY CZ ∘ (CY .Colimit.cocone .transf n ∘ h n)
        ≈˘⟨ ∘-cong₂ (CX .Colimit.colambda-coeval _ _ .≃-NatTrans.transf-eq n) ⟩
          colim-map g e k k-step CY CZ ∘ (colim-map f g h h-step CX CY ∘ CX .Colimit.cocone .transf n)
        ≈˘⟨ assoc _ _ _ ⟩
          (colim-map g e k k-step CY CZ ∘ colim-map f g h h-step CX CY) ∘ CX .Colimit.cocone .transf n
        ∎
        where open ≈-Reasoning isEquiv
