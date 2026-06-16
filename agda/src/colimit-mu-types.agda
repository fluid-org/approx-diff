{-# OPTIONS --prop --postfix-projections --safe #-}

-- μ-types (parameterised initial algebras of polynomial functors) in a category 𝒟 with an initial
-- object and colimits of ω-chains, via the initial-algebra chain 0 → F0 → F²0 → ⋯ . Counterpart of
-- fam-mu-types, which builds them in Fam(𝒞) via W-types.

import Data.Fin as Fin
open Fin using (Fin)
open import Data.Nat using (ℕ; zero; suc; _≤′_; ≤′-refl; ≤′-step)
open import categories
  using (Category; HasTerminal; HasProducts; HasCoproducts; HasStrongCoproducts;
         strong-coproducts→coproducts; HasInitial; IsInitial)
open import Level using (_⊔_)
open import functor
  using (Functor; HasColimits; Colimit; IsColimit; NatTrans; ≃-NatTrans; constF; constFmor;
         colambda-unique)
  renaming (_∘_ to _∘NT_)
open IsColimit
open Colimit
open import omega-chains
  using (ω; chain; chain-map; colim-map; colim-map-cong; colim-map-comp; colim-map-id; square-comp;
         step-cocone; cocone-step; const-chain-colimit; module interchange)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂)
import polynomial-functor-2

module colimit-mu-types
  {o m e} {𝒟 : Category o m e}
  (𝒟T : HasTerminal 𝒟) (𝒟P : HasProducts 𝒟) (𝒟SC : HasStrongCoproducts 𝒟 𝒟P)
  (𝒟I : HasInitial 𝒟)
  (colimits : HasColimits ω 𝒟)
  where

open Category 𝒟
open HasProducts 𝒟P
open HasCoproducts (strong-coproducts→coproducts 𝒟T 𝒟SC)
  using (coprod; coprod-m; coprod-m-cong; coprod-m-comp; coprod-m-id; in₁; in₂;
         copair; copair-cong; copair-in₁; copair-in₂; copair-ext; copair-coprod)
open HasStrongCoproducts 𝒟SC using () renaming (copair to scopair; copair-cong to scopair-cong;
       copair-in₁ to scopair-in₁; copair-in₂ to scopair-in₂; copair-ext to scopair-ext)
open HasInitial 𝒟I renaming (witness to 𝟘)
open polynomial-functor-2 𝒟T 𝒟P 𝒟SC using (Poly; extend; fobj; _∘co_; HasMu; HasMuLaws)
open Poly

-- The strong copair absorbs a coproduct reindexing precomposed in the recursion coordinate.
scopair-fuse : ∀ {Γ X Y X' Y' Z} (f : prod Γ X' ⇒ Z) (g : prod Γ Y' ⇒ Z) (h : X ⇒ X') (k : Y ⇒ Y') →
  scopair f g ∘ prod-m (id Γ) (coprod-m h k)
    ≈ scopair (f ∘ prod-m (id Γ) h) (g ∘ prod-m (id Γ) k)
scopair-fuse {Γ} f g h k =
  ≈-trans (≈-sym (scopair-ext (scopair f g ∘ prod-m (id Γ) (coprod-m h k))))
          (scopair-cong branch₁ branch₂)
  where
    commute₁ : prod-m (id Γ) (coprod-m h k) ∘ pair p₁ (in₁ ∘ p₂)
                 ≈ pair p₁ (in₁ ∘ p₂) ∘ prod-m (id Γ) h
    commute₁ =
      ≈-trans (≈-trans (pair-compose _ _ _ _)
                       (pair-cong₂ (≈-trans (≈-sym (assoc _ _ _)) (∘-cong₁ (copair-in₁ _ _)))))
              (≈-sym (≈-trans (pair-natural _ _ _)
                              (pair-cong (pair-p₁ _ _)
                                         (≈-trans (assoc _ _ _)
                                         (≈-trans (∘-cong₂ (pair-p₂ _ _)) (≈-sym (assoc _ _ _)))))))
    commute₂ : prod-m (id Γ) (coprod-m h k) ∘ pair p₁ (in₂ ∘ p₂) ≈ pair p₁ (in₂ ∘ p₂) ∘ prod-m (id Γ) k
    commute₂ =
      ≈-trans (≈-trans (pair-compose _ _ _ _)
                       (pair-cong₂ (≈-trans (≈-sym (assoc _ _ _)) (∘-cong₁ (copair-in₂ _ _)))))
              (≈-sym (≈-trans (pair-natural _ _ _)
                              (pair-cong (pair-p₁ _ _)
                                         (≈-trans (assoc _ _ _)
                                         (≈-trans (∘-cong₂ (pair-p₂ _ _)) (≈-sym (assoc _ _ _)))))))
    branch₁ = ≈-trans (assoc _ _ _)
              (≈-trans (∘-cong₂ commute₁)
              (≈-trans (≈-sym (assoc _ _ _)) (∘-cong₁ (scopair-in₁ _ _))))
    branch₂ = ≈-trans (assoc _ _ _)
              (≈-trans (∘-cong₂ commute₂)
              (≈-trans (≈-sym (assoc _ _ _)) (∘-cong₁ (scopair-in₂ _ _))))

-- The strong copair is natural in the target: post-composition distributes over it.
scopair-natural : ∀ {Γ X Y Z Z'} (h : Z ⇒ Z') (f : prod Γ X ⇒ Z) (g : prod Γ Y ⇒ Z) →
                  h ∘ scopair f g ≈ scopair (h ∘ f) (h ∘ g)
scopair-natural h f g =
  ≈-trans (≈-sym (scopair-ext (h ∘ scopair f g)))
          (scopair-cong (≈-trans (assoc _ _ _) (∘-cong₂ (scopair-in₁ _ _)))
                        (≈-trans (assoc _ _ _) (∘-cong₂ (scopair-in₂ _ _))))

-- Congruence and a prod-m absorption law for co-Kleisli composition.
∘co-cong₂ : ∀ {Γ X Y Z} {f : prod Γ Y ⇒ Z} {g g' : prod Γ X ⇒ Y} → g ≈ g' → f ∘co g ≈ f ∘co g'
∘co-cong₂ e = ∘-cong₂ (pair-cong₂ e)

∘co-prod-m : ∀ {Γ A X Y X'} (f : prod Γ Y ⇒ A) (g : prod Γ X ⇒ Y) (h : X' ⇒ X) →
             (f ∘co g) ∘ prod-m (id Γ) h ≈ f ∘co (g ∘ prod-m (id Γ) h)
∘co-prod-m f g h =
  ≈-trans (assoc _ _ _)
          (∘-cong₂ (≈-trans (pair-natural _ _ _)
                            (pair-cong₁ (≈-trans (pair-p₁ _ _) id-left))))

-- The interpretation of a polynomial, by structural recursion: at μ, the colimit of the
-- initial-algebra chain. (fobj cannot be used directly: it takes the complete μ-obj as an argument,
-- which would not be structurally recursive. That fobj μ-carrier and ⟦_⟧ agree is ⟦⟧-fobj below.)
mutual
  ⟦_⟧ : ∀ {n} → Poly n → (Fin n → obj) → obj
  ⟦ const A ⟧ δ = A
  ⟦ var i ⟧   δ = δ i
  ⟦ P + Q ⟧   δ = coprod (⟦ P ⟧ δ) (⟦ Q ⟧ δ)
  ⟦ P × Q ⟧   δ = prod (⟦ P ⟧ δ) (⟦ Q ⟧ δ)
  ⟦ μ P ⟧     δ = μ-carrier P δ

  μ-carrier : ∀ {n} → Poly (suc n) → (Fin n → obj) → obj
  μ-carrier P δ = colimits (chain (iter P δ) (step P δ)) .apex

  -- The initial-algebra chain for P at parameters δ.
  iter : ∀ {n} → Poly (suc n) → (Fin n → obj) → ℕ → obj
  iter P δ zero    = 𝟘
  iter P δ (suc k) = ⟦ P ⟧ (extend δ (iter P δ k))

  step : ∀ {n} (P : Poly (suc n)) (δ : Fin n → obj) (k : ℕ) → iter P δ k ⇒ iter P δ (suc k)
  step P δ zero    = from-initial
  step P δ (suc k) = ⟦ P ⟧mor (extend-fam (step P δ k))

  -- Carrier-shaped morphism family: f at position 0, id at positions 1..n.
  extend-fam : ∀ {n} {δ : Fin n → obj} {X Y} → (X ⇒ Y) → ∀ i → extend δ X i ⇒ extend δ Y i
  extend-fam f Fin.zero    = f
  extend-fam f (Fin.suc i) = id _

  -- Two-family version: fs on the parameters, f at the recursion slot.
  extend-mor : ∀ {n} {δ δ' : Fin n → obj} {X Y} →
               (∀ i → δ i ⇒ δ' i) → (X ⇒ Y) → ∀ i → extend δ X i ⇒ extend δ' Y i
  extend-mor fs f Fin.zero    = f
  extend-mor fs f (Fin.suc i) = fs i

  -- Stage maps between the chains at different parameters.
  iter-mor : ∀ {n} (P : Poly (suc n)) {δ δ' : Fin n → obj} →
             (∀ i → δ i ⇒ δ' i) → ∀ k → iter P δ k ⇒ iter P δ' k
  iter-mor P fs zero    = id 𝟘
  iter-mor P fs (suc k) = ⟦ P ⟧mor (extend-mor fs (iter-mor P fs k))

  -- The stage maps commute with the chain steps.
  iter-mor-step : ∀ {n} (P : Poly (suc n)) {δ δ' : Fin n → obj} (fs : ∀ i → δ i ⇒ δ' i) (k : ℕ) →
                  iter-mor P fs (suc k) ∘ step P δ k ≈ step P δ' k ∘ iter-mor P fs k
  iter-mor-step P fs zero = ≈-trans (≈-sym (from-initial-ext _)) (from-initial-ext _)
  iter-mor-step P {δ} {δ'} fs (suc k) =
    ≈-trans (≈-sym (⟦ P ⟧mor-comp (extend-mor fs (iter-mor P fs (suc k))) (extend-fam (step P δ k))))
    (≈-trans (⟦ P ⟧mor-cong pointwise)
             (⟦ P ⟧mor-comp (extend-fam (step P δ' k)) (extend-mor fs (iter-mor P fs k))))
    where
      pointwise : ∀ i → extend-mor fs (iter-mor P fs (suc k)) i ∘ extend-fam (step P δ k) i
                      ≈ extend-fam (step P δ' k) i ∘ extend-mor fs (iter-mor P fs k) i
      pointwise Fin.zero    = iter-mor-step P fs k
      pointwise (Fin.suc i) = id-swap'

  -- The stage maps respect pointwise-equal parameter families, and compose.
  iter-mor-cong : ∀ {n} (P : Poly (suc n)) {δ δ' : Fin n → obj} {fs gs : ∀ i → δ i ⇒ δ' i} →
                  (∀ i → fs i ≈ gs i) → ∀ k → iter-mor P fs k ≈ iter-mor P gs k
  iter-mor-cong P fs≈gs zero    = ≈-refl
  iter-mor-cong P {fs = fs} {gs} fs≈gs (suc k) = ⟦ P ⟧mor-cong pointwise
    where
      pointwise : ∀ i → extend-mor fs (iter-mor P fs k) i ≈ extend-mor gs (iter-mor P gs k) i
      pointwise Fin.zero    = iter-mor-cong P fs≈gs k
      pointwise (Fin.suc i) = fs≈gs i

  iter-mor-comp : ∀ {n} (P : Poly (suc n)) {δ δ' δ'' : Fin n → obj}
                  (fs : ∀ i → δ' i ⇒ δ'' i) (gs : ∀ i → δ i ⇒ δ' i) →
                  ∀ k → iter-mor P (λ i → fs i ∘ gs i) k ≈ iter-mor P fs k ∘ iter-mor P gs k
  iter-mor-comp P fs gs zero    = ≈-sym id-left
  iter-mor-comp P fs gs (suc k) =
    ≈-trans (⟦ P ⟧mor-cong pointwise)
            (⟦ P ⟧mor-comp (extend-mor fs (iter-mor P fs k)) (extend-mor gs (iter-mor P gs k)))
    where
      pointwise : ∀ i → extend-mor (λ j → fs j ∘ gs j) (iter-mor P (λ j → fs j ∘ gs j) k) i ≈
                        extend-mor fs (iter-mor P fs k) i ∘ extend-mor gs (iter-mor P gs k) i
      pointwise Fin.zero    = iter-mor-comp P fs gs k
      pointwise (Fin.suc i) = ≈-refl

  -- Functorial action of ⟦ P ⟧.
  ⟦_⟧mor : ∀ {n} (P : Poly n) {δ δ' : Fin n → obj} → (∀ i → δ i ⇒ δ' i) → ⟦ P ⟧ δ ⇒ ⟦ P ⟧ δ'
  ⟦ const A ⟧mor fs = id A
  ⟦ var i ⟧mor   fs = fs i
  ⟦ P + Q ⟧mor   fs = coprod-m (⟦ P ⟧mor fs) (⟦ Q ⟧mor fs)
  ⟦ P × Q ⟧mor   fs = prod-m (⟦ P ⟧mor fs) (⟦ Q ⟧mor fs)
  ⟦ μ P ⟧mor {δ} {δ'} fs =
    colim-map (step P δ) (step P δ') (iter-mor P fs) (iter-mor-step P fs)
      (colimits (chain (iter P δ) (step P δ))) (colimits (chain (iter P δ') (step P δ')))

  iter-mor-id : ∀ {n} (P : Poly (suc n)) {δ : Fin n → obj} (k : ℕ) →
                iter-mor P (λ i → id (δ i)) k ≈ id (iter P δ k)
  iter-mor-id P zero        = ≈-refl
  iter-mor-id P {δ} (suc k) = ≈-trans (⟦ P ⟧mor-cong pointwise) ⟦ P ⟧mor-id
    where
      pointwise : ∀ i → extend-mor (λ j → id (δ j)) (iter-mor P (λ j → id (δ j)) k) i ≈
                        id (extend δ (iter P δ k) i)
      pointwise Fin.zero    = iter-mor-id P k
      pointwise (Fin.suc i) = ≈-refl

  ⟦_⟧mor-id : ∀ {n} (P : Poly n) {δ : Fin n → obj} → ⟦ P ⟧mor (λ i → id (δ i)) ≈ id (⟦ P ⟧ δ)
  ⟦ const A ⟧mor-id = ≈-refl
  ⟦ var i ⟧mor-id   = ≈-refl
  ⟦ P + Q ⟧mor-id   = ≈-trans (coprod-m-cong ⟦ P ⟧mor-id ⟦ Q ⟧mor-id) coprod-m-id
  ⟦ P × Q ⟧mor-id   = ≈-trans (prod-m-cong ⟦ P ⟧mor-id ⟦ Q ⟧mor-id) prod-m-id
  ⟦ μ P ⟧mor-id {δ} =
    ≈-trans (colim-map-cong {h'-step = λ k → id-swap} (iter-mor-id P) (colimits _) (colimits _))
            (colim-map-id (colimits _))

  ⟦_⟧mor-cong : ∀ {n} (P : Poly n) {δ δ' : Fin n → obj} {fs gs : ∀ i → δ i ⇒ δ' i} →
                (∀ i → fs i ≈ gs i) → ⟦ P ⟧mor fs ≈ ⟦ P ⟧mor gs
  ⟦ const A ⟧mor-cong fs≈gs = ≈-refl
  ⟦ var i ⟧mor-cong   fs≈gs = fs≈gs i
  ⟦ P + Q ⟧mor-cong   fs≈gs = coprod-m-cong (⟦ P ⟧mor-cong fs≈gs) (⟦ Q ⟧mor-cong fs≈gs)
  ⟦ P × Q ⟧mor-cong   fs≈gs = prod-m-cong (⟦ P ⟧mor-cong fs≈gs) (⟦ Q ⟧mor-cong fs≈gs)
  ⟦ μ P ⟧mor-cong     fs≈gs = colim-map-cong (iter-mor-cong P fs≈gs) (colimits _) (colimits _)

  ⟦_⟧mor-comp : ∀ {n} (P : Poly n) {δ δ' δ'' : Fin n → obj}
                (fs : ∀ i → δ' i ⇒ δ'' i) (gs : ∀ i → δ i ⇒ δ' i) →
                ⟦ P ⟧mor (λ i → fs i ∘ gs i) ≈ ⟦ P ⟧mor fs ∘ ⟦ P ⟧mor gs
  ⟦ const A ⟧mor-comp fs gs = ≈-sym id-left
  ⟦ var i ⟧mor-comp   fs gs = ≈-refl
  ⟦ P + Q ⟧mor-comp   fs gs =
    ≈-trans (coprod-m-cong (⟦ P ⟧mor-comp fs gs) (⟦ Q ⟧mor-comp fs gs)) (coprod-m-comp _ _ _ _)
  ⟦ P × Q ⟧mor-comp   fs gs =
    ≈-trans (prod-m-cong (⟦ P ⟧mor-comp fs gs) (⟦ Q ⟧mor-comp fs gs)) (prod-m-comp _ _ _ _)
  ⟦ μ P ⟧mor-comp {δ = δ} {δ'} {δ''} fs gs =
    ≈-trans (colim-map-cong {h'-step = comp-sq} (iter-mor-comp P fs gs) (colimits _) (colimits _))
            (colim-map-comp (colimits _) (colimits _) (colimits _))
    where
      comp-sq : ∀ k → (iter-mor P fs (suc k) ∘ iter-mor P gs (suc k)) ∘ step P δ k
                    ≈ step P δ'' k ∘ (iter-mor P fs k ∘ iter-mor P gs k)
      comp-sq = square-comp {𝒞 = 𝒟} (iter-mor-step P gs) (iter-mor-step P fs)

-- ⟦_⟧ agrees with fobj at μ-carrier: the two are defined by matching clauses, so every case is a congruence.
⟦⟧-fobj : ∀ {n} (P : Poly n) (δ : Fin n → obj) → ⟦ P ⟧ δ ≡ fobj μ-carrier P δ
⟦⟧-fobj (const A) δ = refl
⟦⟧-fobj (var i)   δ = refl
⟦⟧-fobj (P + Q)   δ = cong₂ coprod (⟦⟧-fobj P δ) (⟦⟧-fobj Q δ)
⟦⟧-fobj (P × Q)   δ = cong₂ prod (⟦⟧-fobj P δ) (⟦⟧-fobj Q δ)
⟦⟧-fobj (μ P)     δ = refl

-- An environment chain: a chain of environments with a coordinatewise colimit. A record (with η)
-- rather than a Fin-indexed family of packaged chains: the μ case extends an environment chain
-- with the recursion coordinate, and needs the stage-k environment of the extension to reduce
-- definitionally to an extend.
record EnvChain (n : ℕ) : Set (o ⊔ m ⊔ e) where
  field
    obs      : ℕ → Fin n → obj
    steps    : ∀ k i → obs k i ⇒ obs (suc k) i
    apex     : Fin n → obj
    inj      : ∀ k i → obs k i ⇒ apex i
    inj-step : ∀ k i → inj k i ≈ inj (suc k) i ∘ steps k i
    colimiting : ∀ i → IsColimit (chain {𝒞 = 𝒟} (λ k → obs k i) (λ k → steps k i)) (apex i)
                                 (step-cocone (λ k → inj k i) (λ k → inj-step k i))
open EnvChain

-- The image of an environment chain under ⟦ P ⟧, and the statement that ⟦ P ⟧ preserves its
-- colimit. (Cocontinuity must be joint in all coordinates: the chain defining a μ varies the
-- recursion coordinate together with the parameters.)
module _ {n} (P : Poly n) (E : EnvChain n) where

  img-step : ∀ k → ⟦ P ⟧ (obs E k) ⇒ ⟦ P ⟧ (obs E (suc k))
  img-step k = ⟦ P ⟧mor (steps E k)

  img-chain : Functor ω 𝒟
  img-chain = chain (λ k → ⟦ P ⟧ (obs E k)) img-step

  img-inj : ∀ k → ⟦ P ⟧ (obs E k) ⇒ ⟦ P ⟧ (apex E)
  img-inj k = ⟦ P ⟧mor (inj E k)

  img-inj-step : ∀ k → img-inj k ≈ img-inj (suc k) ∘ img-step k
  img-inj-step k =
    ≈-trans (⟦ P ⟧mor-cong (inj-step E k)) (⟦ P ⟧mor-comp (inj E (suc k)) (steps E k))

  img-cocone : NatTrans img-chain (constF ω (⟦ P ⟧ (apex E)))
  img-cocone = step-cocone img-inj img-inj-step

  -- ⟦ P ⟧ preserves the environment-chain colimit when the image cocone is itself colimiting.
  PreservesChain : Set (o ⊔ m ⊔ e)
  PreservesChain = IsColimit img-chain (⟦ P ⟧ (apex E)) img-cocone

-- Canonical cocones: the pointwise product, coproduct and T-image of cocones, over the
-- corresponding pointwise chains. Built with step-cocone so that they align definitionally with
-- the image cocones of the corresponding polynomials.
module _ {X Y : ℕ → obj} {f : ∀ k → X k ⇒ X (suc k)} {g : ∀ k → Y k ⇒ Y (suc k)} {a b : obj}
         (cX : NatTrans (chain {𝒞 = 𝒟} X f) (constF ω a))
         (cY : NatTrans (chain {𝒞 = 𝒟} Y g) (constF ω b)) where

  open NatTrans

  prod-cocone : NatTrans (chain {𝒞 = 𝒟} (λ k → prod (X k) (Y k)) (λ k → prod-m (f k) (g k)))
                         (constF ω (prod a b))
  prod-cocone =
    step-cocone (λ k → prod-m (cX .transf k) (cY .transf k))
      (λ k → ≈-trans (prod-m-cong (cocone-step cX k) (cocone-step cY k)) (prod-m-comp _ _ _ _))

  coprod-cocone : NatTrans (chain {𝒞 = 𝒟} (λ k → coprod (X k) (Y k)) (λ k → coprod-m (f k) (g k)))
                           (constF ω (coprod a b))
  coprod-cocone =
    step-cocone (λ k → coprod-m (cX .transf k) (cY .transf k))
      (λ k → ≈-trans (coprod-m-cong (cocone-step cX k) (cocone-step cY k)) (coprod-m-comp _ _ _ _))

-- Coproducts preserve chain colimits: no assumption needed. A cocone over the coproduct chain
-- restricts along each injection, and the copairing of the mediated maps mediates.
module _ {X Y : ℕ → obj} {f : ∀ k → X k ⇒ X (suc k)} {g : ∀ k → Y k ⇒ Y (suc k)} {a b : obj}
         {cX : NatTrans (chain {𝒞 = 𝒟} X f) (constF ω a)}
         {cY : NatTrans (chain {𝒞 = 𝒟} Y g) (constF ω b)} where

  open NatTrans

  private
    module _ {x : obj} (β : NatTrans (chain {𝒞 = 𝒟} (λ k → coprod (X k) (Y k)) (λ k → coprod-m (f k) (g k)))
                                     (constF ω x)) where

      restrict₁ : NatTrans (chain {𝒞 = 𝒟} X f) (constF ω x)
      restrict₁ = step-cocone (λ k → β .transf k ∘ in₁)
        (λ k → ≈-trans (∘-cong₁ (cocone-step β k))
               (≈-trans (assoc _ _ _)
               (≈-trans (∘-cong₂ (copair-in₁ _ _)) (≈-sym (assoc _ _ _)))))

      restrict₂ : NatTrans (chain {𝒞 = 𝒟} Y g) (constF ω x)
      restrict₂ = step-cocone (λ k → β .transf k ∘ in₂)
        (λ k → ≈-trans (∘-cong₁ (cocone-step β k))
               (≈-trans (assoc _ _ _)
               (≈-trans (∘-cong₂ (copair-in₂ _ _)) (≈-sym (assoc _ _ _)))))

  +-cocont : IsColimit (chain {𝒞 = 𝒟} X f) a cX → IsColimit (chain {𝒞 = 𝒟} Y g) b cY →
             IsColimit (chain {𝒞 = 𝒟} (λ k → coprod (X k) (Y k)) (λ k → coprod-m (f k) (g k)))
                       (coprod a b) (coprod-cocone cX cY)
  +-cocont LX LY .colambda x β =
    copair (LX .colambda x (restrict₁ β)) (LY .colambda x (restrict₂ β))
  +-cocont LX LY .colambda-cong β≃γ =
    copair-cong
      (LX .colambda-cong (record { transf-eq = λ k → ∘-cong₁ (β≃γ .≃-NatTrans.transf-eq k) }))
      (LY .colambda-cong (record { transf-eq = λ k → ∘-cong₁ (β≃γ .≃-NatTrans.transf-eq k) }))
  +-cocont LX LY .colambda-coeval x β .≃-NatTrans.transf-eq k =
    ≈-trans (≈-sym (copair-coprod _ _ _ _))
    (≈-trans (copair-cong (LX .colambda-coeval x (restrict₁ β) .≃-NatTrans.transf-eq k)
                          (LY .colambda-coeval x (restrict₂ β) .≃-NatTrans.transf-eq k))
             (copair-ext _))
  +-cocont LX LY .colambda-ext x h =
    ≈-trans (copair-cong
              (≈-trans (LX .colambda-cong E₁) (LX .colambda-ext x (h ∘ in₁)))
              (≈-trans (LY .colambda-cong E₂) (LY .colambda-ext x (h ∘ in₂))))
            (copair-ext h)
    where
      E₁ : ≃-NatTrans (restrict₁ (constFmor h ∘NT coprod-cocone cX cY)) (constFmor (h ∘ in₁) ∘NT cX)
      E₁ .≃-NatTrans.transf-eq k =
        ≈-trans (assoc _ _ _) (≈-trans (∘-cong₂ (copair-in₁ _ _)) (≈-sym (assoc _ _ _)))

      E₂ : ≃-NatTrans (restrict₂ (constFmor h ∘NT coprod-cocone cX cY)) (constFmor (h ∘ in₂) ∘NT cY)
      E₂ .≃-NatTrans.transf-eq k =
        ≈-trans (assoc _ _ _) (≈-trans (∘-cong₂ (copair-in₂ _ _)) (≈-sym (assoc _ _ _)))

-- Cocontinuity of the interpretation: assuming products and T preserve chain colimits, every
-- ⟦ P ⟧ (extend δ −) does. Coproducts need no assumption (they commute with all colimits, proved below), and
-- the μ case is the interchange of colimits.
module cocont
  (×-cocont : ∀ {X Y : ℕ → obj} {f : ∀ k → X k ⇒ X (suc k)} {g : ∀ k → Y k ⇒ Y (suc k)} {a b : obj}
              {cX : NatTrans (chain {𝒞 = 𝒟} X f) (constF ω a)}
              {cY : NatTrans (chain {𝒞 = 𝒟} Y g) (constF ω b)} →
              IsColimit (chain {𝒞 = 𝒟} X f) a cX → IsColimit (chain {𝒞 = 𝒟} Y g) b cY →
              IsColimit _ (prod a b) (prod-cocone cX cY))
  -- The catamorphism's base leg prod Γ 𝟘 ⇒ A needs prod Γ 𝟘 to be initial. (Automatic with
  -- exponentials, and holds in Fam 𝒟 since the index of prod Γ 𝟘 is empty.)
  (prod𝟘-initial : ∀ {Γ} → IsInitial 𝒟 (prod Γ 𝟘))
  where

  open functor using (IsColimit-cong)

  ⟦_⟧-cocont : ∀ {n} (P : Poly n) (E : EnvChain n) → PreservesChain P E
  ⟦ const A ⟧-cocont E =
    IsColimit-cong (record { transf-eq = λ k → ≈-refl }) (const-chain-colimit A .isColimit)
  ⟦ var i ⟧-cocont   E =
    IsColimit-cong (record { transf-eq = λ k → ≈-refl }) (colimiting E i)
  ⟦ P + Q ⟧-cocont   E = +-cocont (⟦ P ⟧-cocont E) (⟦ Q ⟧-cocont E)
  ⟦ P × Q ⟧-cocont   E = ×-cocont (⟦ P ⟧-cocont E) (⟦ Q ⟧-cocont E)
  ⟦_⟧-cocont {n} (μ P) E = IsColimit-cong (record { transf-eq = legs-eq }) IC.is-colimit
    where
      Rk : ∀ k → Colimit (chain {𝒞 = 𝒟} (iter P (obs E k)) (step P (obs E k)))
      Rk k = colimits (chain (iter P (obs E k)) (step P (obs E k)))

      -- Column cocone legs commute with the horizontal steps, and with the vertical steps.
      ℓ-step : ∀ k j → iter-mor P (inj E k) j ≈ iter-mor P (inj E (suc k)) j ∘ iter-mor P (steps E k) j
      ℓ-step k j =
        ≈-trans (iter-mor-cong P (inj-step E k) j) (iter-mor-comp P (inj E (suc k)) (steps E k) j)

      ℓ-v : ∀ k j → step P (apex E) j ∘ iter-mor P (inj E k) j ≈
                    iter-mor P (inj E k) (suc j) ∘ step P (obs E k) j
      ℓ-v k j = ≈-sym (iter-mor-step P (inj E k) j)

      -- Column j has colimit iter P (apex E) j, by induction on j: column 0 is constantly 𝟘, and
      -- column j+1 is the ⟦ P ⟧-image of the environment chain extended with column j.
      extend-env : ℕ → EnvChain (suc n)
      columns : ∀ j → IsColimit (chain {𝒞 = 𝒟} (λ k → iter P (obs E k) j) (λ k → iter-mor P (steps E k) j))
                                (iter P (apex E) j)
                                (step-cocone (λ k → iter-mor P (inj E k) j) (λ k → ℓ-step k j))

      extend-env j .obs k      = extend (obs E k) (iter P (obs E k) j)
      extend-env j .steps k    = extend-mor (steps E k) (iter-mor P (steps E k) j)
      extend-env j .apex       = extend (apex E) (iter P (apex E) j)
      extend-env j .inj k      = extend-mor (inj E k) (iter-mor P (inj E k) j)
      extend-env j .inj-step k Fin.zero    = ℓ-step k j
      extend-env j .inj-step k (Fin.suc i) = inj-step E k i
      extend-env j .colimiting Fin.zero    = columns j
      extend-env j .colimiting (Fin.suc i) = colimiting E i

      columns zero    = IsColimit-cong (record { transf-eq = λ k → ≈-refl }) (const-chain-colimit 𝟘 .isColimit)
      columns (suc j) = ⟦ P ⟧-cocont (extend-env j)

      module IC = interchange {𝒞 = 𝒟}
        (λ k j → iter P (obs E k) j)
        (λ k j → step P (obs E k) j)
        (λ k j → iter-mor P (steps E k) j)
        (λ k j → iter-mor-step P (steps E k) j)
        Rk
        (iter P (apex E)) (step P (apex E))
        (λ k j → iter-mor P (inj E k) j)
        ℓ-step ℓ-v columns
        (colimits (chain (iter P (apex E)) (step P (apex E))))

      -- The interchange cocone legs agree with the canonical ones (both mediate the same legs).
      legs-eq : ∀ k → IC.ρ-inj k ≈ ⟦ μ P ⟧mor (inj E k)
      legs-eq k = Rk k .colambda-cong (record { transf-eq = λ j → ≈-refl })

  -- The initial-algebra colimit and its injections.
  μ-colim : ∀ {n} (P : Poly (suc n)) (δ : Fin n → obj) → Colimit (chain {𝒞 = 𝒟} (iter P δ) (step P δ))
  μ-colim P δ = colimits (chain (iter P δ) (step P δ))

  μ-inj : ∀ {n} (P : Poly (suc n)) (δ : Fin n → obj) (k : ℕ) → iter P δ k ⇒ μ-carrier P δ
  μ-inj P δ k = μ-colim P δ .cocone .NatTrans.transf k

  -- The constant environment δ, extended in the recursion coordinate by the initial-algebra
  -- chain and its colimit.
  carrier-env : ∀ {n} (P : Poly (suc n)) (δ : Fin n → obj) → EnvChain (suc n)
  carrier-env P δ .obs k   = extend δ (iter P δ k)
  carrier-env P δ .steps k = extend-fam (step P δ k)
  carrier-env P δ .apex    = extend δ (μ-carrier P δ)
  carrier-env P δ .inj k   = extend-fam (μ-inj P δ k)
  carrier-env P δ .inj-step k Fin.zero    = cocone-step (μ-colim P δ .cocone) k
  carrier-env P δ .inj-step k (Fin.suc i) = ≈-sym id-left
  carrier-env P δ .colimiting Fin.zero    =
    IsColimit-cong (record { transf-eq = λ k → ≈-refl }) (μ-colim P δ .isColimit)
  carrier-env P δ .colimiting (Fin.suc i) =
    IsColimit-cong (record { transf-eq = λ k → ≈-refl }) (const-chain-colimit (δ i) .isColimit)

  -- The shifted cocone whose mediator is the algebra map.
  shifted-cocone : ∀ {n} (P : Poly (suc n)) (δ : Fin n → obj) →
                   NatTrans (chain {𝒞 = 𝒟} (λ k → iter P δ (suc k)) (λ k → step P δ (suc k)))
                            (constF ω (μ-carrier P δ))
  shifted-cocone P δ = step-cocone (λ k → μ-inj P δ (suc k)) (λ k → cocone-step (μ-colim P δ .cocone) (suc k))

  -- The algebra map: by cocontinuity, ⟦ P ⟧ at the carrier is the colimit of the shifted
  -- initial-algebra chain, which the shifted injections mediate back into the carrier.
  α : ∀ {n} (P : Poly (suc n)) (δ : Fin n → obj) → ⟦ P ⟧ (extend δ (μ-carrier P δ)) ⇒ μ-carrier P δ
  α P δ = ⟦ P ⟧-cocont (carrier-env P δ) .colambda (μ-carrier P δ) (shifted-cocone P δ)

  -- α mediates the shifted injections: precomposing with the k-th image leg gives the (k+1)-th.
  α-coeval : ∀ {n} (P : Poly (suc n)) (δ : Fin n → obj) (k : ℕ) →
             α P δ ∘ ⟦ P ⟧mor (extend-fam (μ-inj P δ k)) ≈ μ-inj P δ (suc k)
  α-coeval P δ k =
    ⟦ P ⟧-cocont (carrier-env P δ) .colambda-coeval (μ-carrier P δ) (shifted-cocone P δ) .≃-NatTrans.transf-eq k

  -- The μ-functorial action mediates the injections: it sends the m-th δ-leg to the m-th δ'-leg
  -- precomposed with the stage map.
  μ-mor-coeval : ∀ {n} (P : Poly (suc n)) {δ δ' : Fin n → obj} (fs : ∀ i → δ i ⇒ δ' i) (m : ℕ) →
                 ⟦ μ P ⟧mor fs ∘ μ-inj P δ m ≈ μ-inj P δ' m ∘ iter-mor P fs m
  μ-mor-coeval P {δ} {δ'} fs m =
    μ-colim P δ .colambda-coeval _
      (μ-colim P δ' .cocone ∘NT chain-map (step P δ) (step P δ') (iter-mor P fs) (iter-mor-step P fs))
      .≃-NatTrans.transf-eq m

  -- Context-Γ version of extend-mor, for the strong action below.
  strong-extend-mor : ∀ {n Γ} {δ δ' : Fin n → obj} {X Y} →
                      (∀ i → prod Γ (δ i) ⇒ δ' i) → (prod Γ X ⇒ Y) →
                      ∀ i → prod Γ (extend δ X i) ⇒ extend δ' Y i
  strong-extend-mor fs f Fin.zero    = f
  strong-extend-mor fs f (Fin.suc i) = fs i

  mutual
    -- Fold legs: leg 0 out of the initial prod Γ 𝟘, leg (k+1) by the algebra after folding the
    -- children. These form a cocone over the Γ-product of the initial-algebra chain (legs-step).
    legs : ∀ {n Γ A} {P : Poly (suc n)} {δ : Fin n → obj} →
           (prod Γ (⟦ P ⟧ (extend δ A)) ⇒ A) → ∀ k → prod Γ (iter P δ k) ⇒ A
    legs alg zero             = prod𝟘-initial .IsInitial.from-initial
    legs {P = P} alg (suc k)  = alg ∘co ⟦ P ⟧ˢ (strong-extend-mor (λ i → p₂) (legs alg k))

    legs-step : ∀ {n Γ A} {P : Poly (suc n)} {δ : Fin n → obj}
                (alg : prod Γ (⟦ P ⟧ (extend δ A)) ⇒ A) →
                ∀ k → legs alg k ≈ legs alg (suc k) ∘ prod-m (id Γ) (step P δ k)
    legs-step alg zero    = prod𝟘-initial .IsInitial.from-initial-ext _
    legs-step {Γ = Γ} {P = P} {δ = δ} alg (suc k) =
      ≈-trans (∘-cong₂ (pair-cong₂
        (≈-trans (⟦ P ⟧ˢ-cong pointwise)
                 (≈-sym (⟦ P ⟧ˢ-fuse (strong-extend-mor (λ i → p₂) (legs alg (suc k)))
                                     (extend-fam (step P δ k)))))))
        (≈-sym rhs-rewrite)
      where
        Z  = prod-m (id Γ) (step P δ (suc k))
        G' = ⟦ P ⟧ˢ (strong-extend-mor (λ i → p₂) (legs alg (suc k)))

        pointwise : ∀ i → strong-extend-mor (λ i → p₂) (legs alg k) i ≈
                          strong-extend-mor (λ i → p₂) (legs alg (suc k)) i ∘ prod-m (id Γ) (extend-fam (step P δ k) i)
        pointwise Fin.zero    = legs-step alg k
        pointwise (Fin.suc i) = ≈-sym (≈-trans (∘-cong₂ prod-m-id) id-right)

        -- Move the outer chain step inside the co-Kleisli composition.
        rhs-rewrite : (alg ∘ pair p₁ G') ∘ Z ≈ alg ∘ pair p₁ (G' ∘ Z)
        rhs-rewrite =
          ≈-trans (assoc _ _ _)
                  (∘-cong₂ (≈-trans (pair-natural _ _ _)
                                    (pair-cong₁ (≈-trans (pair-p₁ _ _) id-left))))

    -- Congruence of the fold legs in the algebra.
    legs-cong : ∀ {n Γ A} (P : Poly (suc n)) (δ : Fin n → obj)
                {alg alg' : prod Γ (⟦ P ⟧ (extend δ A)) ⇒ A} →
                alg ≈ alg' → ∀ k → legs {P = P} {δ = δ} alg k ≈ legs {P = P} {δ = δ} alg' k
    legs-cong P δ alg≈ zero    = ≈-refl
    legs-cong P δ alg≈ (suc k) =
      ∘-cong alg≈ (pair-cong ≈-refl
        (⟦ P ⟧ˢ-cong (λ { Fin.zero → legs-cong P δ alg≈ k ; (Fin.suc i) → ≈-refl })))

    -- The catamorphism in context Γ: mediate the cocone of fold legs out of the Γ-product of the
    -- initial-algebra chain (a colimit by ×-cocont at the constant-Γ and initial-algebra chains).
    ⦅_⦆ : ∀ {n Γ A} {P : Poly (suc n)} {δ : Fin n → obj} →
          (prod Γ (⟦ P ⟧ (extend δ A)) ⇒ A) → prod Γ (μ-carrier P δ) ⇒ A
    ⦅_⦆ {Γ = Γ} {A = A} {P = P} {δ = δ} alg =
      ×-cocont (const-chain-colimit Γ .isColimit)
               (colimits (chain (iter P δ) (step P δ)) .isColimit) .colambda A
        (step-cocone (legs alg) (legs-step alg))

    -- Congruence of the catamorphism in the algebra, by colimit uniqueness.
    cata-cong : ∀ {n Γ A} {P : Poly (suc n)} {δ : Fin n → obj}
                {alg alg' : prod Γ (⟦ P ⟧ (extend δ A)) ⇒ A} →
                alg ≈ alg' → ⦅ alg ⦆ ≈ ⦅ alg' ⦆
    cata-cong {Γ = Γ} {A = A} {P = P} {δ = δ} {alg = alg} {alg' = alg'} alg≈ =
      ×-cocont (const-chain-colimit Γ .isColimit)
               (colimits (chain (iter P δ) (step P δ)) .isColimit) .colambda-cong cocone-eq
      where
        cocone-eq : ≃-NatTrans (step-cocone (legs alg) (legs-step alg))
                               (step-cocone (legs alg') (legs-step alg'))
        cocone-eq .≃-NatTrans.transf-eq k = legs-cong P δ alg≈ k

    -- Strong (context-Γ) functorial action of ⟦ P ⟧, as needed for the catamorphism legs. The μ case
    -- is the catamorphism formula, mutually with the catamorphism itself (structurally decreasing:
    -- the catamorphism at P uses the strong action of P's body).
    ⟦_⟧ˢ : ∀ {n Γ} (P : Poly n) {δ δ' : Fin n → obj} →
           (∀ i → prod Γ (δ i) ⇒ δ' i) → prod Γ (⟦ P ⟧ δ) ⇒ ⟦ P ⟧ δ'
    ⟦ const A ⟧ˢ fs = p₂
    ⟦ var i ⟧ˢ   fs = fs i
    ⟦ P + Q ⟧ˢ   fs = scopair (in₁ ∘ ⟦ P ⟧ˢ fs) (in₂ ∘ ⟦ Q ⟧ˢ fs)
    ⟦ P × Q ⟧ˢ   fs = pair (⟦ P ⟧ˢ fs ∘ pair p₁ (p₁ ∘ p₂)) (⟦ Q ⟧ˢ fs ∘ pair p₁ (p₂ ∘ p₂))
    ⟦ μ P ⟧ˢ {δ = δ} {δ' = δ'} fs = ⦅_⦆ {P = P} {δ = δ} (α P δ' ∘ ⟦ P ⟧ˢ (strong-extend-mor fs p₂))

    -- Congruence for the strong action.
    ⟦_⟧ˢ-cong : ∀ {n Γ} (P : Poly n) {δ δ' : Fin n → obj} {fs gs : ∀ i → prod Γ (δ i) ⇒ δ' i} →
                (∀ i → fs i ≈ gs i) → ⟦ P ⟧ˢ fs ≈ ⟦ P ⟧ˢ gs
    ⟦ const A ⟧ˢ-cong fs≈gs = ≈-refl
    ⟦ var i ⟧ˢ-cong   fs≈gs = fs≈gs i
    ⟦ P + Q ⟧ˢ-cong   fs≈gs = scopair-cong (∘-cong₂ (⟦ P ⟧ˢ-cong fs≈gs)) (∘-cong₂ (⟦ Q ⟧ˢ-cong fs≈gs))
    ⟦ P × Q ⟧ˢ-cong   fs≈gs = pair-cong (∘-cong₁ (⟦ P ⟧ˢ-cong fs≈gs)) (∘-cong₁ (⟦ Q ⟧ˢ-cong fs≈gs))
    ⟦ μ P ⟧ˢ-cong     fs≈gs =
      cata-cong (∘-cong₂ (⟦ P ⟧ˢ-cong (λ { Fin.zero → ≈-refl ; (Fin.suc i) → fs≈gs i })))

    -- Fusion: the strong action absorbs a precomposed Γ-image of a reindexing.
    ⟦_⟧ˢ-fuse : ∀ {n} (P : Poly n) {Γ} {δ δ' δ'' : Fin n → obj}
                (fs : ∀ i → prod Γ (δ' i) ⇒ δ'' i) (gs : ∀ i → δ i ⇒ δ' i) →
                ⟦ P ⟧ˢ fs ∘ prod-m (id Γ) (⟦ P ⟧mor gs) ≈ ⟦ P ⟧ˢ (λ i → fs i ∘ prod-m (id Γ) (gs i))
    ⟦ const A ⟧ˢ-fuse fs gs = ≈-trans (∘-cong₂ prod-m-id) id-right
    ⟦ var i ⟧ˢ-fuse   fs gs = ≈-refl
    ⟦ P + Q ⟧ˢ-fuse   fs gs =
      ≈-trans (scopair-fuse _ _ _ _)
              (scopair-cong (≈-trans (assoc _ _ _) (∘-cong₂ (⟦ P ⟧ˢ-fuse fs gs)))
                            (≈-trans (assoc _ _ _) (∘-cong₂ (⟦ Q ⟧ˢ-fuse fs gs))))
    ⟦ P × Q ⟧ˢ-fuse {Γ = Γ} fs gs = ≈-trans (pair-natural _ _ _) (pair-cong P-comp Q-comp)
      where
        A' = ⟦ P ⟧mor gs
        B' = ⟦ Q ⟧mor gs
        -- The (Γ, left)-projection commutes past the product reindexing.
        q₁-nat : pair p₁ (p₁ ∘ p₂) ∘ prod-m (id Γ) (prod-m A' B')
                   ≈ prod-m (id Γ) A' ∘ pair p₁ (p₁ ∘ p₂)
        q₁-nat =
          ≈-trans (pair-natural _ _ _)
          (≈-trans (pair-cong (≈-trans (pair-p₁ _ _) id-left)
                              (≈-trans (assoc _ _ _)
                              (≈-trans (∘-cong₂ (pair-p₂ _ _))
                              (≈-trans (≈-sym (assoc _ _ _))
                              (≈-trans (∘-cong₁ (pair-p₁ _ _)) (assoc _ _ _))))))
                   (≈-sym (≈-trans (pair-compose _ _ _ _) (pair-cong₁ id-left))))
        q₂-nat : pair p₁ (p₂ ∘ p₂) ∘ prod-m (id Γ) (prod-m A' B')
                   ≈ prod-m (id Γ) B' ∘ pair p₁ (p₂ ∘ p₂)
        q₂-nat =
          ≈-trans (pair-natural _ _ _)
          (≈-trans (pair-cong (≈-trans (pair-p₁ _ _) id-left)
                              (≈-trans (assoc _ _ _)
                              (≈-trans (∘-cong₂ (pair-p₂ _ _))
                              (≈-trans (≈-sym (assoc _ _ _))
                              (≈-trans (∘-cong₁ (pair-p₂ _ _)) (assoc _ _ _))))))
                   (≈-sym (≈-trans (pair-compose _ _ _ _) (pair-cong₁ id-left))))
        P-comp = ≈-trans (assoc _ _ _)
                 (≈-trans (∘-cong₂ q₁-nat)
                 (≈-trans (≈-sym (assoc _ _ _)) (∘-cong₁ (⟦ P ⟧ˢ-fuse fs gs))))
        Q-comp = ≈-trans (assoc _ _ _)
                 (≈-trans (∘-cong₂ q₂-nat)
                 (≈-trans (≈-sym (assoc _ _ _)) (∘-cong₁ (⟦ Q ⟧ˢ-fuse fs gs))))
    ⟦ μ P ⟧ˢ-fuse {Γ = Γ} {δ = δ} {δ' = δ'} {δ'' = δ''} fs gs =
      colambda-unique Rδ (λ k →
        ≈-trans (assoc _ _ _)
        (≈-trans (∘-cong₂ (≈-sym (prod-m-comp _ _ _ _)))
        (≈-trans (∘-cong₂ (prod-m-cong ≈-refl
                   (colimits (chain (iter P δ) (step P δ)) .colambda-coeval _ _ .≃-NatTrans.transf-eq k)))
        (≈-trans (∘-cong₂ (prod-m-comp _ _ _ _))
        (≈-trans (≈-sym (assoc _ _ _))
        (≈-trans (∘-cong₁ (Rδ' .colambda-coeval _ _ .≃-NatTrans.transf-eq k))
        (≈-trans (legs-fuse P δ δ' δ'' fs gs k)
                 (≈-sym (Rδ .colambda-coeval _ _ .≃-NatTrans.transf-eq k)))))))))
      where
        Rδ  = ×-cocont (const-chain-colimit Γ .isColimit)
                       (colimits (chain (iter P δ) (step P δ)) .isColimit)
        Rδ' = ×-cocont (const-chain-colimit Γ .isColimit)
                       (colimits (chain (iter P δ') (step P δ')) .isColimit)

    -- Left fusion: the plain action absorbs into the strong action on the left.
    ⟦_⟧ˢ-fuse-left : ∀ {n} (P : Poly n) {Γ} {δ δ' δ'' : Fin n → obj}
                     (fs : ∀ i → δ' i ⇒ δ'' i) (gs : ∀ i → prod Γ (δ i) ⇒ δ' i) →
                     ⟦ P ⟧mor fs ∘ ⟦ P ⟧ˢ gs ≈ ⟦ P ⟧ˢ (λ i → fs i ∘ gs i)
    ⟦ const A ⟧ˢ-fuse-left fs gs = id-left
    ⟦ var i ⟧ˢ-fuse-left fs gs = ≈-refl
    ⟦ P + Q ⟧ˢ-fuse-left fs gs =
      ≈-trans (scopair-natural _ _ _)
              (scopair-cong (≈-trans (≈-sym (assoc _ _ _))
                            (≈-trans (∘-cong₁ (copair-in₁ _ _))
                            (≈-trans (assoc _ _ _) (∘-cong₂ (⟦ P ⟧ˢ-fuse-left fs gs)))))
                            (≈-trans (≈-sym (assoc _ _ _))
                            (≈-trans (∘-cong₁ (copair-in₂ _ _))
                            (≈-trans (assoc _ _ _) (∘-cong₂ (⟦ Q ⟧ˢ-fuse-left fs gs))))))
    ⟦ P × Q ⟧ˢ-fuse-left fs gs =
      ≈-trans (pair-compose _ _ _ _)
              (pair-cong (≈-trans (≈-sym (assoc _ _ _)) (∘-cong₁ (⟦ P ⟧ˢ-fuse-left fs gs)))
                         (≈-trans (≈-sym (assoc _ _ _)) (∘-cong₁ (⟦ Q ⟧ˢ-fuse-left fs gs))))
    ⟦ μ P ⟧ˢ-fuse-left {Γ = Γ} {δ = δ} {δ' = δ'} {δ'' = δ''} fs gs =
      colambda-unique Rδ (λ k →
        ≈-trans (assoc _ _ _)
        (≈-trans (∘-cong₂ (Rδ .colambda-coeval _ _ .≃-NatTrans.transf-eq k))
        (≈-trans (legs-left-fuse P δ δ' δ'' fs gs k)
                 (≈-sym (Rδ .colambda-coeval _ _ .≃-NatTrans.transf-eq k)))))
      where
        Rδ = ×-cocont (const-chain-colimit Γ .isColimit)
                      (colimits (chain (iter P δ) (step P δ)) .isColimit)

    -- Fold-leg fusion: folding the δ-chain directly equals mapping δ→δ' then folding the δ'-chain.
    legs-fuse : ∀ {n Γ} (P : Poly (suc n)) (δ δ' δ'' : Fin n → obj)
                (fs : ∀ i → prod Γ (δ' i) ⇒ δ'' i) (gs : ∀ i → δ i ⇒ δ' i) (k : ℕ) →
                legs {P = P} {δ = δ'} (α P δ'' ∘ ⟦ P ⟧ˢ (strong-extend-mor fs p₂)) k ∘ prod-m (id Γ) (iter-mor P gs k) ≈
                legs (α P δ'' ∘ ⟦ P ⟧ˢ (strong-extend-mor (λ i → fs i ∘ prod-m (id Γ) (gs i)) p₂)) k
    legs-fuse P δ δ' δ'' fs gs zero =
      ≈-trans (≈-sym (prod𝟘-initial .IsInitial.from-initial-ext _))
              (prod𝟘-initial .IsInitial.from-initial-ext _)
    legs-fuse {Γ = Γ} P δ δ' δ'' fs gs (suc k) =
      ≈-trans (∘co-prod-m _ _ _)
        (≈-trans (∘co-cong₂ (⟦ P ⟧ˢ-fuse (strong-extend-mor (λ i → p₂) (legs alg-fs k))
                                         (extend-mor gs (iter-mor P gs k))))
          (≈-trans (∘co-cong₂ (⟦ P ⟧ˢ-cong {gs = λ i → extend-mor gs (id _) i ∘ leg i} leg-ih))
            (≈-trans (∘co-cong₂ (≈-sym (⟦ P ⟧ˢ-fuse-left (extend-mor gs (id _)) leg)))
              (≈-trans (∘-cong₂ (≈-sym (≈-trans (pair-compose _ _ _ _) (pair-cong₁ id-left))))
                (≈-trans (≈-sym (assoc _ _ _))
                  (∘-cong₁
                    (≈-trans (assoc _ _ _)
                      (∘-cong₂
                        (≈-trans (⟦ P ⟧ˢ-fuse (strong-extend-mor fs p₂) (extend-mor gs (id _)))
                          (⟦ P ⟧ˢ-cong route-gs))))))))))
      where
        alg-fs = α P δ'' ∘ ⟦ P ⟧ˢ (strong-extend-mor fs p₂)
        alg-fg = α P δ'' ∘ ⟦ P ⟧ˢ (strong-extend-mor (λ i → fs i ∘ prod-m (id Γ) (gs i)) p₂)

        leg : ∀ i → prod Γ (extend δ (iter P δ k) i) ⇒ extend δ (μ-carrier P δ'') i
        leg = strong-extend-mor (λ i → p₂) (legs alg-fg k)

        leg-ih : ∀ i → strong-extend-mor (λ i → p₂) (legs alg-fs k) i ∘ prod-m (id Γ) (extend-mor gs (iter-mor P gs k) i) ≈
                       extend-mor gs (id _) i ∘ leg i
        leg-ih Fin.zero    = ≈-trans (legs-fuse P δ δ' δ'' fs gs k) (≈-sym id-left)
        leg-ih (Fin.suc j) = pair-p₂ _ _

        route-gs : ∀ i → strong-extend-mor fs p₂ i ∘ prod-m (id Γ) (extend-mor gs (id _) i) ≈
                         strong-extend-mor (λ i → fs i ∘ prod-m (id Γ) (gs i)) p₂ i
        route-gs Fin.zero    = ≈-trans (∘-cong₂ prod-m-id) id-right
        route-gs (Fin.suc j) = ≈-refl

    -- α is natural: the algebra commutes with the μ-functorial action.
    α-nat : ∀ {n} (P : Poly (suc n)) (δ δ' : Fin n → obj) (fs : ∀ i → δ i ⇒ δ' i) →
            ⟦ μ P ⟧mor fs ∘ α P δ ≈ α P δ' ∘ ⟦ P ⟧mor (extend-mor fs (⟦ μ P ⟧mor fs))
    α-nat P δ δ' fs = colambda-unique (⟦ P ⟧-cocont (carrier-env P δ)) (λ k →
      ≈-trans (≈-trans (assoc _ _ _) (≈-trans (∘-cong₂ (α-coeval P δ k)) (μ-mor-coeval P fs (suc k))))
              (≈-sym (≈-trans (assoc _ _ _)
                      (≈-trans (∘-cong₂ (≈-sym (⟦ P ⟧mor-comp _ _)))
                      (≈-trans (∘-cong₂ (⟦ P ⟧mor-cong (famR k)))
                      (≈-trans (∘-cong₂ (⟦ P ⟧mor-comp _ _))
                      (≈-trans (≈-sym (assoc _ _ _))
                               (∘-cong₁ (α-coeval P δ' k)))))))))
      where
        famR : ∀ k i → extend-mor fs (⟦ μ P ⟧mor fs) i ∘ extend-fam (μ-inj P δ k) i ≈
                       extend-fam (μ-inj P δ' k) i ∘ extend-mor fs (iter-mor P fs k) i
        famR k Fin.zero    = μ-mor-coeval P fs k
        famR k (Fin.suc j) = id-swap'

    -- Left fusion at the level of fold legs: post-composing a leg with the μ-functorial action.
    legs-left-fuse : ∀ {n Γ} (P : Poly (suc n)) (δ δ' δ'' : Fin n → obj)
                     (fs : ∀ i → δ' i ⇒ δ'' i) (gs : ∀ i → prod Γ (δ i) ⇒ δ' i) (k : ℕ) →
                     ⟦ μ P ⟧mor fs ∘ legs {P = P} {δ = δ} (α P δ' ∘ ⟦ P ⟧ˢ (strong-extend-mor gs p₂)) k ≈
                     legs {P = P} {δ = δ} (α P δ'' ∘ ⟦ P ⟧ˢ (strong-extend-mor (λ i → fs i ∘ gs i) p₂)) k
    legs-left-fuse P δ δ' δ'' fs gs zero =
      ≈-trans (≈-sym (prod𝟘-initial .IsInitial.from-initial-ext _))
              (prod𝟘-initial .IsInitial.from-initial-ext _)
    legs-left-fuse {Γ = Γ} P δ δ' δ'' fs gs (suc k) =
      ≈-trans (≈-sym (assoc _ _ _))
        (≈-trans (∘-cong₁ (≈-sym (assoc _ _ _)))
          (≈-trans (∘-cong₁ (∘-cong₁ (α-nat P δ' δ'' fs)))
            (≈-trans (∘-cong₁ (assoc _ _ _))
              (≈-trans (assoc _ _ _)
                (≈-trans
                  (∘-cong₂
                    (≈-trans
                      (∘-cong₁
                        (≈-trans (⟦ P ⟧ˢ-fuse-left (extend-mor fs (⟦ μ P ⟧mor fs)) (strong-extend-mor gs p₂))
                          (≈-trans (⟦ P ⟧ˢ-cong route-fs)
                            (≈-sym (⟦ P ⟧ˢ-fuse (strong-extend-mor (λ i → fs i ∘ gs i) p₂) (extend-fam (⟦ μ P ⟧mor fs)))))))
                      (≈-trans (assoc _ _ _)
                        (∘-cong₂
                          (≈-trans (pair-compose _ _ _ _)
                            (≈-trans (pair-cong₁ id-left)
                              (pair-cong₂
                                (≈-trans
                                  (⟦ P ⟧ˢ-fuse-left (extend-fam (⟦ μ P ⟧mor fs))
                                    (strong-extend-mor (λ i → p₂)
                                      (legs (α P δ' ∘ ⟦ P ⟧ˢ (strong-extend-mor gs p₂)) k)))
                                  (⟦ P ⟧ˢ-cong leg-ih)))))))))
                  (≈-sym (assoc _ _ _)))))))
      where
        route-fs : ∀ i → extend-mor fs (⟦ μ P ⟧mor fs) i ∘ strong-extend-mor gs p₂ i ≈
                         strong-extend-mor (λ i → fs i ∘ gs i) p₂ i ∘ prod-m (id Γ) (extend-fam (⟦ μ P ⟧mor fs) i)
        route-fs Fin.zero    = ≈-sym (pair-p₂ _ _)
        route-fs (Fin.suc j) = ≈-sym (≈-trans (∘-cong₂ prod-m-id) id-right)

        leg-ih : ∀ i → extend-fam (⟦ μ P ⟧mor fs) i ∘ strong-extend-mor (λ i → p₂) (legs (α P δ' ∘ ⟦ P ⟧ˢ (strong-extend-mor gs p₂)) k) i ≈
                       strong-extend-mor (λ i → p₂) (legs (α P δ'' ∘ ⟦ P ⟧ˢ (strong-extend-mor (λ i → fs i ∘ gs i) p₂)) k) i
        leg-ih Fin.zero    = legs-left-fuse P δ δ' δ'' fs gs k
        leg-ih (Fin.suc j) = id-left

  -- Catamorphism β: folding an α-image equals applying the algebra to the folded children.
  cata-β : ∀ {n Γ A} {P : Poly (suc n)} {δ : Fin n → obj}
           (alg : prod Γ (⟦ P ⟧ (extend δ A)) ⇒ A) →
           ⦅ alg ⦆ ∘co (α P δ ∘ p₂) ≈ alg ∘co ⟦ P ⟧ˢ (strong-extend-mor (λ i → p₂) ⦅ alg ⦆)
  cata-β alg = {!!}

  hasMu : HasMu
  hasMu .HasMu.μ-obj = μ-carrier
  hasMu .HasMu.α P δ = α P δ ∘ ≡-to-⇒ (sym (⟦⟧-fobj P (extend δ (μ-carrier P δ))))
  hasMu .HasMu.⦅_⦆ {_} {Γ} {A} {P} {δ} alg =
    ⦅ alg ∘ prod-m (id Γ) (≡-to-⇒ (⟦⟧-fobj P (extend δ A))) ⦆

  hasMuLaws : HasMuLaws hasMu
  hasMuLaws .HasMuLaws.⦅⦆-β alg =
    ≈-trans (∘co-cong₂ (assoc _ _ _))
    (≈-trans (∘co-cong₂ (∘-cong₂ (≈-sym (pair-p₂ (id _ ∘ p₁) _))))
    (≈-trans (∘co-cong₂ (≈-sym (assoc _ _ _)))
    (≈-trans (≈-sym (∘co-prod-m _ _ _))
    (≈-trans (∘-cong₁ (cata-β _))
    (≈-trans (∘co-prod-m _ _ _) {!!})))))
  hasMuLaws .HasMuLaws.⦅⦆-η alg h eq = {!!}
