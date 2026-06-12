{-# OPTIONS --prop --postfix-projections --safe #-}

-- The shape category ω = (ℕ, ≤): diagrams over it are ω-chains, whose colimits underlie the
-- initial-algebra construction for polynomial functors. A chain is most conveniently given by its
-- step maps; `chain` packages these as a functor out of ω.

open import Level using (0ℓ; _⊔_)
open import Data.Nat using (ℕ; suc; _≤′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (≤′-trans; ≤′⇒≤; 1+n≰n; z≤′n)
open import prop using (⊤; tt)
open import prop-setoid using (⊤-isEquivalence; module ≈-Reasoning)
open import categories using (Category)
import functor
open functor using (Functor; NatTrans; ≃-NatTrans; Colimit; IsColimit; constF; constFmor; colambda-unique) renaming (_∘_ to _∘NT_)

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

  -- A cocone over a chain, from legs commuting with single steps.
  module _ {X : ℕ → obj} {f : ∀ n → X n ⇒ X (suc n)} {a : obj}
           (legs : ∀ n → X n ⇒ a) (legs-step : ∀ n → legs n ≈ (legs (suc n) ∘ f n)) where

    open NatTrans

    step-cocone : NatTrans (chain X f) (constF ω a)
    step-cocone .transf = legs
    step-cocone .natural p = nat p
      where
        nat : ∀ {k n} (p : k ≤′ n) → (id a ∘ legs k) ≈ (legs n ∘ chain X f .Functor.fmor p)
        nat ≤′-refl     = id-swap
        nat (≤′-step p) = ≈-trans (nat p) (≈-trans (∘-cong₁ (legs-step _)) (assoc _ _ _))

  -- Conversely, any cocone commutes with single steps.
  cocone-step : ∀ {X : ℕ → obj} {f : ∀ n → X n ⇒ X (suc n)} {a : obj}
                (c : NatTrans (chain X f) (constF ω a)) →
                ∀ n → c .NatTrans.transf n ≈ (c .NatTrans.transf (suc n) ∘ f n)
  cocone-step c n =
    ≈-trans (≈-sym id-left)
    (≈-trans (c .NatTrans.natural (≤′-step ≤′-refl)) (∘-cong₂ id-right))

  -- A constant chain has its value as a colimit.
  module _ (A : obj) where
    private
      walk-id : ∀ {m n} (p : m ≤′ n) → chain (λ _ → A) (λ _ → id A) .Functor.fmor p ≈ id A
      walk-id ≤′-refl     = ≈-refl
      walk-id (≤′-step p) = ≈-trans id-left (walk-id p)

    open NatTrans
    open Colimit
    open functor.IsColimit

    const-chain-colimit : Colimit (chain (λ _ → A) (λ _ → id A))
    const-chain-colimit .apex = A
    const-chain-colimit .cocone .transf n = id A
    const-chain-colimit .cocone .natural p =
      ≈-trans id-left (≈-trans (≈-sym (walk-id p)) (≈-sym id-left))
    const-chain-colimit .isColimit .colambda x β = β .transf 0
    const-chain-colimit .isColimit .colambda-cong β≃γ = β≃γ .≃-NatTrans.transf-eq 0
    const-chain-colimit .isColimit .colambda-coeval x β .≃-NatTrans.transf-eq n =
      ≈-trans id-right
      (≈-trans (≈-sym id-left)
      (≈-trans (β .natural (z≤′n {n}))
      (≈-trans (∘-cong₂ (walk-id (z≤′n {n}))) id-right)))
    const-chain-colimit .isColimit .colambda-ext x f = id-right

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

  -- Identity stage maps mediate to the identity.
  colim-map-id : ∀ {X : ℕ → obj} {f : ∀ n → X n ⇒ X (suc n)}
                 {id-step : ∀ n → ((id (X (suc n))) ∘ f n) ≈ (f n ∘ id (X n))} →
                 ∀ CX → colim-map f f (λ n → id (X n)) id-step CX CX ≈ id (CX .Colimit.apex)
  colim-map-id CX =
    ≈-trans (CX .Colimit.colambda-cong (record { transf-eq = λ n → id-swap' }))
            (CX .Colimit.colambda-ext _ (id _))

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

-- Interchange of colimits for a commuting ω×ω grid: given colimits of the rows, colimits of the
-- columns onto a chain of column apexes, and a colimit of that chain, the latter is also a colimit
-- of the chain of row apexes.
module interchange {o m e} {𝒞 : Category o m e}
  (let open Category 𝒞)
  (G : ℕ → ℕ → obj)
  (v : ∀ k j → G k j ⇒ G k (suc j))            -- steps within row k
  (h : ∀ k j → G k j ⇒ G (suc k) j)            -- steps between rows
  (sq : ∀ k j → (h k (suc j) ∘ v k j) ≈ (v (suc k) j ∘ h k j))
  (R : ∀ k → Colimit (chain {𝒞 = 𝒞} (G k) (v k)))
  (γ : ℕ → obj) (w : ∀ j → γ j ⇒ γ (suc j))    -- the chain of column apexes
  (ℓ : ∀ k j → G k j ⇒ γ j)                    -- column cocone legs
  (ℓ-step : ∀ k j → ℓ k j ≈ (ℓ (suc k) j ∘ h k j))
  (ℓ-v : ∀ k j → (w j ∘ ℓ k j) ≈ (ℓ k (suc j) ∘ v k j))
  (CL : ∀ j → IsColimit (chain {𝒞 = 𝒞} (λ k → G k j) (λ k → h k j)) (γ j)
                        (step-cocone (λ k → ℓ k j) (λ k → ℓ-step k j)))
  (CΓ : Colimit (chain {𝒞 = 𝒞} γ w))
  where

  open NatTrans

  -- The chain of row apexes, with the mediated steps.
  ρ : ℕ → obj
  ρ k = R k .Colimit.apex

  ρ-step : ∀ k → ρ k ⇒ ρ (suc k)
  ρ-step k = colim-map (v k) (v (suc k)) (h k) (sq k) (R k) (R (suc k))

  -- Each row maps into the apex of the column chain, mediated row by row.
  row-legs : ∀ k j → G k j ⇒ CΓ .Colimit.apex
  row-legs k j = CΓ .Colimit.cocone .transf j ∘ ℓ k j

  row-legs-step : ∀ k j → row-legs k j ≈ (row-legs k (suc j) ∘ v k j)
  row-legs-step k j =
    ≈-trans (∘-cong₁ (cocone-step (CΓ .Colimit.cocone) j))
    (≈-trans (assoc _ _ _)
    (≈-trans (∘-cong₂ (ℓ-v k j)) (≈-sym (assoc _ _ _))))

  ρ-inj : ∀ k → ρ k ⇒ CΓ .Colimit.apex
  ρ-inj k = R k .Colimit.colambda _ (step-cocone (row-legs k) (row-legs-step k))

  ρ-inj-step : ∀ k → ρ-inj k ≈ (ρ-inj (suc k) ∘ ρ-step k)
  ρ-inj-step k = ≈-sym (colambda-unique (R k .Colimit.isColimit) pointwise)
    where
      pointwise : ∀ j → ((ρ-inj (suc k) ∘ ρ-step k) ∘ R k .Colimit.cocone .transf j)
                      ≈ (ρ-inj k ∘ R k .Colimit.cocone .transf j)
      pointwise j =
        ≈-trans (assoc _ _ _)
        (≈-trans (∘-cong₂ (R k .Colimit.colambda-coeval _ _ .≃-NatTrans.transf-eq j))
        (≈-trans (≈-sym (assoc _ _ _))
        (≈-trans (∘-cong₁ (R (suc k) .Colimit.colambda-coeval _ _ .≃-NatTrans.transf-eq j))
        (≈-trans (assoc _ _ _)
        (≈-trans (∘-cong₂ (≈-sym (ℓ-step k j)))
                 (≈-sym (R k .Colimit.colambda-coeval _ _ .≃-NatTrans.transf-eq j)))))))

  -- Mediation: a cocone over the row-apex chain mediates column-wise, then along the column-apex
  -- chain.
  private
    module _ {x : obj} (β : NatTrans (chain {𝒞 = 𝒞} ρ ρ-step) (constF ω x)) where

      col-legs : ∀ j k → G k j ⇒ x
      col-legs j k = β .transf k ∘ R k .Colimit.cocone .transf j

      col-legs-step : ∀ j k → col-legs j k ≈ (col-legs j (suc k) ∘ h k j)
      col-legs-step j k =
        ≈-trans (∘-cong₁ (cocone-step β k))
        (≈-trans (assoc _ _ _)
        (≈-trans (∘-cong₂ (R k .Colimit.colambda-coeval _ _ .≃-NatTrans.transf-eq j))
                 (≈-sym (assoc _ _ _))))

      col-mediate : ∀ j → γ j ⇒ x
      col-mediate j = CL j .IsColimit.colambda x (step-cocone (col-legs j) (col-legs-step j))

      col-mediate-step : ∀ j → col-mediate j ≈ (col-mediate (suc j) ∘ w j)
      col-mediate-step j = colambda-unique (CL j) pointwise
        where
          pointwise : ∀ k → (col-mediate j ∘ ℓ k j) ≈ ((col-mediate (suc j) ∘ w j) ∘ ℓ k j)
          pointwise k =
            ≈-trans (CL j .IsColimit.colambda-coeval _ _ .≃-NatTrans.transf-eq k)
            (≈-sym
              (≈-trans (assoc _ _ _)
              (≈-trans (∘-cong₂ (ℓ-v k j))
              (≈-trans (≈-sym (assoc _ _ _))
              (≈-trans (∘-cong₁ (CL (suc j) .IsColimit.colambda-coeval _ _ .≃-NatTrans.transf-eq k))
              (≈-trans (assoc _ _ _)
                       (∘-cong₂ (≈-sym (cocone-step (R k .Colimit.cocone) j)))))))))

      mediate : CΓ .Colimit.apex ⇒ x
      mediate = CΓ .Colimit.colambda x (step-cocone col-mediate col-mediate-step)

  is-colimit : IsColimit (chain {𝒞 = 𝒞} ρ ρ-step) (CΓ .Colimit.apex) (step-cocone ρ-inj ρ-inj-step)
  is-colimit .IsColimit.colambda x β = mediate β
  is-colimit .IsColimit.colambda-cong β≃β' =
    CΓ .Colimit.colambda-cong (record { transf-eq = λ j →
      CL j .IsColimit.colambda-cong (record { transf-eq = λ k →
        ∘-cong₁ (β≃β' .≃-NatTrans.transf-eq k) }) })
  is-colimit .IsColimit.colambda-coeval x β .≃-NatTrans.transf-eq k =
    colambda-unique (R k .Colimit.isColimit) pointwise
    where
      pointwise : ∀ j → ((mediate β ∘ ρ-inj k) ∘ R k .Colimit.cocone .transf j)
                      ≈ (β .transf k ∘ R k .Colimit.cocone .transf j)
      pointwise j =
        ≈-trans (assoc _ _ _)
        (≈-trans (∘-cong₂ (R k .Colimit.colambda-coeval _ _ .≃-NatTrans.transf-eq j))
        (≈-trans (≈-sym (assoc _ _ _))
        (≈-trans (∘-cong₁ (CΓ .Colimit.colambda-coeval _ _ .≃-NatTrans.transf-eq j))
                 (CL j .IsColimit.colambda-coeval _ _ .≃-NatTrans.transf-eq k))))
  is-colimit .IsColimit.colambda-ext x f =
    colambda-unique (CΓ .Colimit.isColimit) pointwise
    where
      βf = constFmor f ∘NT step-cocone ρ-inj ρ-inj-step

      pointwise : ∀ j → (mediate βf ∘ CΓ .Colimit.cocone .transf j) ≈ (f ∘ CΓ .Colimit.cocone .transf j)
      pointwise j =
        ≈-trans (CΓ .Colimit.colambda-coeval _ _ .≃-NatTrans.transf-eq j)
                (colambda-unique (CL j) inner)
        where
          inner : ∀ k → (col-mediate βf j ∘ ℓ k j) ≈ ((f ∘ CΓ .Colimit.cocone .transf j) ∘ ℓ k j)
          inner k =
            ≈-trans (CL j .IsColimit.colambda-coeval _ _ .≃-NatTrans.transf-eq k)
            (≈-trans (assoc _ _ _)
            (≈-trans (∘-cong₂ (R k .Colimit.colambda-coeval _ _ .≃-NatTrans.transf-eq j))
                     (≈-sym (assoc _ _ _))))
