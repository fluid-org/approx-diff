{-# OPTIONS --prop --postfix-projections #-}

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
  using (Functor; StrongFunctor; HasColimits; Colimit; IsColimit; NatTrans; ≃-NatTrans; constF; constFmor)
  renaming (_∘_ to _∘NT_)
open IsColimit
open Colimit
open import omega-chains
  using (ω; chain; colim-map; colim-map-cong; colim-map-comp; colim-map-id; square-comp;
         step-cocone; cocone-step; const-chain-colimit; module interchange)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
import polynomial-functor-2

module colimit-mu-types
  {o m e} {𝒟 : Category o m e}
  (𝒟T : HasTerminal 𝒟) (𝒟P : HasProducts 𝒟) (𝒟SC : HasStrongCoproducts 𝒟 𝒟P)
  (T-strong : StrongFunctor 𝒟P)
  (𝒟I : HasInitial 𝒟)
  (colimits : HasColimits ω 𝒟)
  where

open Category 𝒟
open HasProducts 𝒟P
open HasCoproducts (strong-coproducts→coproducts 𝒟T 𝒟SC)
  using (coprod; coprod-m; coprod-m-cong; coprod-m-comp; coprod-m-id; in₁; in₂;
         copair; copair-cong; copair-in₁; copair-in₂; copair-ext; copair-coprod)
open HasStrongCoproducts 𝒟SC using () renaming (copair to scopair)
open HasInitial 𝒟I renaming (witness to 𝟘)
open StrongFunctor T-strong using (strengthᵣ) renaming (F to T)
open polynomial-functor-2 𝒟T 𝒟P 𝒟SC T-strong using (Poly; extend; fobj; _∘co_)
open Poly

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
  ⟦ T∘ P ⟧    δ = Functor.fobj T (⟦ P ⟧ δ)

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
                  (iter-mor P fs (suc k) ∘ step P δ k) ≈ (step P δ' k ∘ iter-mor P fs k)
  iter-mor-step P fs zero = ≈-trans (≈-sym (from-initial-ext _)) (from-initial-ext _)
  iter-mor-step P {δ} {δ'} fs (suc k) =
    ≈-trans (≈-sym (⟦ P ⟧mor-comp (extend-mor fs (iter-mor P fs (suc k))) (extend-fam (step P δ k))))
    (≈-trans (⟦ P ⟧mor-cong pointwise)
             (⟦ P ⟧mor-comp (extend-fam (step P δ' k)) (extend-mor fs (iter-mor P fs k))))
    where
      pointwise : ∀ i → (extend-mor fs (iter-mor P fs (suc k)) i ∘ extend-fam (step P δ k) i)
                      ≈ (extend-fam (step P δ' k) i ∘ extend-mor fs (iter-mor P fs k) i)
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
                  ∀ k → iter-mor P (λ i → fs i ∘ gs i) k ≈ (iter-mor P fs k ∘ iter-mor P gs k)
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
  ⟦ T∘ P ⟧mor    fs = Functor.fmor T (⟦ P ⟧mor fs)

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
  ⟦ T∘ P ⟧mor-id    = ≈-trans (Functor.fmor-cong T ⟦ P ⟧mor-id) (Functor.fmor-id T)

  ⟦_⟧mor-cong : ∀ {n} (P : Poly n) {δ δ' : Fin n → obj} {fs gs : ∀ i → δ i ⇒ δ' i} →
                (∀ i → fs i ≈ gs i) → ⟦ P ⟧mor fs ≈ ⟦ P ⟧mor gs
  ⟦ const A ⟧mor-cong fs≈gs = ≈-refl
  ⟦ var i ⟧mor-cong   fs≈gs = fs≈gs i
  ⟦ P + Q ⟧mor-cong   fs≈gs = coprod-m-cong (⟦ P ⟧mor-cong fs≈gs) (⟦ Q ⟧mor-cong fs≈gs)
  ⟦ P × Q ⟧mor-cong   fs≈gs = prod-m-cong (⟦ P ⟧mor-cong fs≈gs) (⟦ Q ⟧mor-cong fs≈gs)
  ⟦ μ P ⟧mor-cong     fs≈gs = colim-map-cong (iter-mor-cong P fs≈gs) (colimits _) (colimits _)
  ⟦ T∘ P ⟧mor-cong    fs≈gs = Functor.fmor-cong T (⟦ P ⟧mor-cong fs≈gs)

  ⟦_⟧mor-comp : ∀ {n} (P : Poly n) {δ δ' δ'' : Fin n → obj}
                (fs : ∀ i → δ' i ⇒ δ'' i) (gs : ∀ i → δ i ⇒ δ' i) →
                ⟦ P ⟧mor (λ i → fs i ∘ gs i) ≈ (⟦ P ⟧mor fs ∘ ⟦ P ⟧mor gs)
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
      comp-sq : ∀ k → ((iter-mor P fs (suc k) ∘ iter-mor P gs (suc k)) ∘ step P δ k)
                    ≈ (step P δ'' k ∘ (iter-mor P fs k ∘ iter-mor P gs k))
      comp-sq = square-comp {𝒞 = 𝒟} (iter-mor-step P gs) (iter-mor-step P fs)
  ⟦ T∘ P ⟧mor-comp    fs gs =
    ≈-trans (Functor.fmor-cong T (⟦ P ⟧mor-comp fs gs)) (Functor.fmor-comp T _ _)

-- ⟦_⟧ agrees with fobj at μ-carrier: the two are defined by matching clauses, so every case is a congruence.
⟦⟧-fobj : ∀ {n} (P : Poly n) (δ : Fin n → obj) → ⟦ P ⟧ δ ≡ fobj μ-carrier P δ
⟦⟧-fobj (const A) δ = refl
⟦⟧-fobj (var i)   δ = refl
⟦⟧-fobj (P + Q)   δ = cong₂ coprod (⟦⟧-fobj P δ) (⟦⟧-fobj Q δ)
⟦⟧-fobj (P × Q)   δ = cong₂ prod (⟦⟧-fobj P δ) (⟦⟧-fobj Q δ)
⟦⟧-fobj (μ P)     δ = refl
⟦⟧-fobj (T∘ P)    δ = cong (Functor.fobj T) (⟦⟧-fobj P δ)

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
    inj-step : ∀ k i → inj k i ≈ (inj (suc k) i ∘ steps k i)
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

  img-inj-step : ∀ k → img-inj k ≈ (img-inj (suc k) ∘ img-step k)
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

module _ {X : ℕ → obj} {f : ∀ k → X k ⇒ X (suc k)} {a : obj}
         (c : NatTrans (chain {𝒞 = 𝒟} X f) (constF ω a)) where

  T-cocone : NatTrans (chain {𝒞 = 𝒟} (λ k → Functor.fobj T (X k)) (λ k → Functor.fmor T (f k)))
                      (constF ω (Functor.fobj T a))
  T-cocone =
    step-cocone (λ k → Functor.fmor T (c .NatTrans.transf k))
      (λ k → ≈-trans (Functor.fmor-cong T (cocone-step c k)) (Functor.fmor-comp T _ _))

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
  (T-cocont : ∀ {X : ℕ → obj} {f : ∀ k → X k ⇒ X (suc k)} {a : obj}
              {c : NatTrans (chain {𝒞 = 𝒟} X f) (constF ω a)} →
              IsColimit (chain {𝒞 = 𝒟} X f) a c →
              IsColimit _ (Functor.fobj T a) (T-cocone c))
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
      ℓ-step : ∀ k j → iter-mor P (inj E k) j ≈ (iter-mor P (inj E (suc k)) j ∘ iter-mor P (steps E k) j)
      ℓ-step k j =
        ≈-trans (iter-mor-cong P (inj-step E k) j) (iter-mor-comp P (inj E (suc k)) (steps E k) j)

      ℓ-v : ∀ k j → (step P (apex E) j ∘ iter-mor P (inj E k) j)
                  ≈ (iter-mor P (inj E k) (suc j) ∘ step P (obs E k) j)
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

      columns zero    = IsColimit-cong (record { transf-eq = λ k → ≈-refl })
                                       (const-chain-colimit 𝟘 .isColimit)
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
  ⟦ T∘ P ⟧-cocont    E = T-cocont (⟦ P ⟧-cocont E)

  -- The algebra map: by cocontinuity, ⟦ P ⟧ at the carrier is the colimit of the shifted
  -- initial-algebra chain, which the shifted injections mediate back into the carrier.
  α : ∀ {n} (P : Poly (suc n)) (δ : Fin n → obj) → ⟦ P ⟧ (extend δ (μ-carrier P δ)) ⇒ μ-carrier P δ
  α {n} P δ =
    ⟦ P ⟧-cocont carrier-env .colambda (μ-carrier P δ)
      (step-cocone (λ k → μC .cocone .NatTrans.transf (suc k))
                   (λ k → cocone-step (μC .cocone) (suc k)))
    where
      μC : Colimit (chain {𝒞 = 𝒟} (iter P δ) (step P δ))
      μC = colimits (chain (iter P δ) (step P δ))

      -- The constant environment δ, extended in the recursion coordinate by the initial-algebra
      -- chain and its colimit.
      carrier-env : EnvChain (suc n)
      carrier-env .obs k   = extend δ (iter P δ k)
      carrier-env .steps k = extend-fam (step P δ k)
      carrier-env .apex    = extend δ (μ-carrier P δ)
      carrier-env .inj k   = extend-fam (μC .cocone .NatTrans.transf k)
      carrier-env .inj-step k Fin.zero    = cocone-step (μC .cocone) k
      carrier-env .inj-step k (Fin.suc i) = ≈-sym id-left
      carrier-env .colimiting Fin.zero    =
        IsColimit-cong (record { transf-eq = λ k → ≈-refl }) (μC .isColimit)
      carrier-env .colimiting (Fin.suc i) =
        IsColimit-cong (record { transf-eq = λ k → ≈-refl }) (const-chain-colimit (δ i) .isColimit)

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
                ∀ k → legs alg k ≈ (legs alg (suc k) ∘ prod-m (id Γ) (step P δ k))
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
        pointwise : ∀ i → strong-extend-mor (λ i → p₂) (legs alg k) i
                          ≈ (strong-extend-mor (λ i → p₂) (legs alg (suc k)) i
                             ∘ prod-m (id Γ) (extend-fam (step P δ k) i))
        pointwise Fin.zero    = legs-step alg k
        pointwise (Fin.suc i) = ≈-sym (≈-trans (∘-cong₂ prod-m-id) id-right)
        -- Move the outer chain step inside the co-Kleisli composition.
        rhs-rewrite : ((alg ∘ pair p₁ G') ∘ Z) ≈ (alg ∘ pair p₁ (G' ∘ Z))
        rhs-rewrite =
          ≈-trans (assoc _ _ _)
                  (∘-cong₂ (≈-trans (pair-natural _ _ _)
                                    (pair-cong₁ (≈-trans (pair-p₁ _ _) id-left))))

    -- The catamorphism in context Γ: mediate the cocone of fold legs out of the Γ-product of the
    -- initial-algebra chain (a colimit by ×-cocont at the constant-Γ and initial-algebra chains).
    ⦅_⦆ : ∀ {n Γ A} {P : Poly (suc n)} {δ : Fin n → obj} →
          (prod Γ (⟦ P ⟧ (extend δ A)) ⇒ A) → prod Γ (μ-carrier P δ) ⇒ A
    ⦅_⦆ {Γ = Γ} {A = A} {P = P} {δ = δ} alg =
      ×-cocont (const-chain-colimit Γ .isColimit)
               (colimits (chain (iter P δ) (step P δ)) .isColimit) .colambda A
        (step-cocone (legs alg) (legs-step alg))

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
    ⟦ T∘ P ⟧ˢ    fs = Functor.fmor T (⟦ P ⟧ˢ fs) ∘ strengthᵣ

    -- Congruence for the strong action.
    ⟦_⟧ˢ-cong : ∀ {n Γ} (P : Poly n) {δ δ' : Fin n → obj} {fs gs : ∀ i → prod Γ (δ i) ⇒ δ' i} →
                (∀ i → fs i ≈ gs i) → ⟦ P ⟧ˢ fs ≈ ⟦ P ⟧ˢ gs
    ⟦ P ⟧ˢ-cong fs≈gs = {!!}

    -- Fusion: the strong action absorbs a precomposed Γ-image of a reindexing.
    ⟦_⟧ˢ-fuse : ∀ {n Γ} (P : Poly n) {δ δ' δ'' : Fin n → obj}
                (fs : ∀ i → prod Γ (δ' i) ⇒ δ'' i) (gs : ∀ i → δ i ⇒ δ' i) →
                ⟦ P ⟧ˢ fs ∘ prod-m (id Γ) (⟦ P ⟧mor gs) ≈ ⟦ P ⟧ˢ (λ i → fs i ∘ prod-m (id Γ) (gs i))
    ⟦ P ⟧ˢ-fuse fs gs = {!!}
