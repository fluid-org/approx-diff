{-# OPTIONS --prop --postfix-projections --safe #-}

-- μ-types (parameterised initial algebras of polynomial functors) in a category 𝒟 with an initial
-- object and colimits of ω-chains, via the initial-algebra chain 0 → F0 → F²0 → ⋯ . Counterpart of
-- fam-mu-types, which builds them in Fam(𝒞) via W-types.

import Data.Fin as Fin
open Fin using (Fin)
open import Data.Nat using (ℕ; zero; suc; _≤′_; ≤′-refl; ≤′-step)
open import categories
  using (Category; HasTerminal; HasProducts; HasCoproducts; HasStrongCoproducts;
         strong-coproducts→coproducts; HasInitial)
open import Level using (_⊔_)
open import functor
  using (Functor; StrongFunctor; HasColimits; Colimit; IsColimit; NatTrans; ≃-NatTrans; constF; constFmor)
  renaming (_∘_ to _∘NT_)
open import omega-chains
  using (ω; chain; colim-map; colim-map-cong; colim-map-comp; colim-map-id; square-comp;
         step-cocone; cocone-step; const-chain-colimit; module interchange)
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
open HasInitial 𝒟I renaming (witness to 𝟘)
open StrongFunctor T-strong using (strengthᵣ) renaming (F to T)
open polynomial-functor-2 𝒟T 𝒟P 𝒟SC T-strong using (Poly; extend)
open Poly

-- The interpretation of a polynomial, by structural recursion: at μ, the colimit of the
-- initial-algebra chain. (fobj can't used directly: it takes the complete μ-obj as an argument,
-- which would not be structurally recursive. Later we prove fobj μ-obj and ⟦_⟧ agree.)
mutual
  ⟦_⟧ : ∀ {n} → Poly n → (Fin n → obj) → obj
  ⟦ const A ⟧ δ = A
  ⟦ var i ⟧   δ = δ i
  ⟦ P + Q ⟧   δ = coprod (⟦ P ⟧ δ) (⟦ Q ⟧ δ)
  ⟦ P × Q ⟧   δ = prod (⟦ P ⟧ δ) (⟦ Q ⟧ δ)
  ⟦ μ P ⟧     δ = μ-carrier P δ
  ⟦ T∘ P ⟧    δ = Functor.fobj T (⟦ P ⟧ δ)

  μ-carrier : ∀ {n} → Poly (suc n) → (Fin n → obj) → obj
  μ-carrier P δ = colimits (chain (iter P δ) (step P δ)) .Colimit.apex

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
      pointwise : ∀ i → extend-mor (λ j → fs j ∘ gs j) (iter-mor P (λ j → fs j ∘ gs j) k) i
                      ≈ (extend-mor fs (iter-mor P fs k) i ∘ extend-mor gs (iter-mor P gs k) i)
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
      pointwise : ∀ i → extend-mor (λ j → id (δ j)) (iter-mor P (λ j → id (δ j)) k) i
                      ≈ id (extend δ (iter P δ k) i)
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

-- The image of an environment chain under ⟦ P ⟧, and the statement that ⟦ P ⟧ preserves its
-- colimit. (Cocontinuity must be joint in all coordinates: the chain defining a μ varies the
-- recursion coordinate together with the parameters.)
module _ {n} (P : Poly n) (E : EnvChain n) where
  open EnvChain E

  img-step : ∀ k → ⟦ P ⟧ (obs k) ⇒ ⟦ P ⟧ (obs (suc k))
  img-step k = ⟦ P ⟧mor (steps k)

  img-chain : Functor ω 𝒟
  img-chain = chain (λ k → ⟦ P ⟧ (obs k)) img-step

  img-inj : ∀ k → ⟦ P ⟧ (obs k) ⇒ ⟦ P ⟧ apex
  img-inj k = ⟦ P ⟧mor (inj k)

  img-inj-step : ∀ k → img-inj k ≈ (img-inj (suc k) ∘ img-step k)
  img-inj-step k =
    ≈-trans (⟦ P ⟧mor-cong (inj-step k)) (⟦ P ⟧mor-comp (inj (suc k)) (steps k))

  img-cocone : NatTrans img-chain (constF ω (⟦ P ⟧ apex))
  img-cocone = step-cocone img-inj img-inj-step

  -- ⟦ P ⟧ preserves the environment-chain colimit when the image cocone is itself colimiting.
  PreservesChain : Set (o ⊔ m ⊔ e)
  PreservesChain = IsColimit img-chain (⟦ P ⟧ apex) img-cocone

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
  +-cocont LX LY .IsColimit.colambda x β =
    copair (LX .IsColimit.colambda x (restrict₁ β)) (LY .IsColimit.colambda x (restrict₂ β))
  +-cocont LX LY .IsColimit.colambda-cong β≃γ =
    copair-cong
      (LX .IsColimit.colambda-cong (record { transf-eq = λ k → ∘-cong₁ (β≃γ .≃-NatTrans.transf-eq k) }))
      (LY .IsColimit.colambda-cong (record { transf-eq = λ k → ∘-cong₁ (β≃γ .≃-NatTrans.transf-eq k) }))
  +-cocont LX LY .IsColimit.colambda-coeval x β .≃-NatTrans.transf-eq k =
    ≈-trans (≈-sym (copair-coprod _ _ _ _))
    (≈-trans (copair-cong (LX .IsColimit.colambda-coeval x (restrict₁ β) .≃-NatTrans.transf-eq k)
                          (LY .IsColimit.colambda-coeval x (restrict₂ β) .≃-NatTrans.transf-eq k))
             (copair-ext _))
  +-cocont LX LY .IsColimit.colambda-ext x h =
    ≈-trans (copair-cong
              (≈-trans (LX .IsColimit.colambda-cong E₁) (LX .IsColimit.colambda-ext x (h ∘ in₁)))
              (≈-trans (LY .IsColimit.colambda-cong E₂) (LY .IsColimit.colambda-ext x (h ∘ in₂))))
            (copair-ext h)
    where
      E₁ : ≃-NatTrans (restrict₁ (constFmor h ∘NT coprod-cocone cX cY)) (constFmor (h ∘ in₁) ∘NT cX)
      E₁ .≃-NatTrans.transf-eq k =
        ≈-trans (assoc _ _ _) (≈-trans (∘-cong₂ (copair-in₁ _ _)) (≈-sym (assoc _ _ _)))

      E₂ : ≃-NatTrans (restrict₂ (constFmor h ∘NT coprod-cocone cX cY)) (constFmor (h ∘ in₂) ∘NT cY)
      E₂ .≃-NatTrans.transf-eq k =
        ≈-trans (assoc _ _ _) (≈-trans (∘-cong₂ (copair-in₂ _ _)) (≈-sym (assoc _ _ _)))


-- Cocontinuity of the interpretation: assuming products and T preserve chain colimits, every
-- ⟦ P ⟧ (extend δ −) does. Coproducts need no assumption (they commute with all colimits;
-- proved below), and the μ case is the interchange of colimits.
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
  where

  open functor using (IsColimit-cong)

  ⟦_⟧-cocont : ∀ {n} (P : Poly n) (E : EnvChain n) → PreservesChain P E
  ⟦ const A ⟧-cocont E =
    IsColimit-cong (record { transf-eq = λ k → ≈-refl }) (const-chain-colimit A .Colimit.isColimit)
  ⟦ var i ⟧-cocont   E =
    IsColimit-cong (record { transf-eq = λ k → ≈-refl }) (E .EnvChain.colimiting i)
  ⟦ P + Q ⟧-cocont   E = +-cocont (⟦ P ⟧-cocont E) (⟦ Q ⟧-cocont E)
  ⟦ P × Q ⟧-cocont   E = ×-cocont (⟦ P ⟧-cocont E) (⟦ Q ⟧-cocont E)
  ⟦_⟧-cocont {n} (μ P) E = IsColimit-cong (record { transf-eq = legs-eq }) IC.is-colimit
    where
      open EnvChain E

      Rk : ∀ k → Colimit (chain {𝒞 = 𝒟} (iter P (obs k)) (step P (obs k)))
      Rk k = colimits (chain (iter P (obs k)) (step P (obs k)))

      -- Column cocone legs commute with the horizontal steps, and with the vertical steps.
      ℓ-step : ∀ k j → iter-mor P (inj k) j ≈ (iter-mor P (inj (suc k)) j ∘ iter-mor P (steps k) j)
      ℓ-step k j =
        ≈-trans (iter-mor-cong P (inj-step k) j) (iter-mor-comp P (inj (suc k)) (steps k) j)

      ℓ-v : ∀ k j → (step P apex j ∘ iter-mor P (inj k) j)
                  ≈ (iter-mor P (inj k) (suc j) ∘ step P (obs k) j)
      ℓ-v k j = ≈-sym (iter-mor-step P (inj k) j)

      -- Column j has colimit iter P apex j, by induction on j: column 0 is constantly 𝟘, and
      -- column j+1 is the ⟦ P ⟧-image of the environment chain extended with column j.
      extend-env : ℕ → EnvChain (suc n)
      columns : ∀ j → IsColimit (chain {𝒞 = 𝒟} (λ k → iter P (obs k) j) (λ k → iter-mor P (steps k) j))
                                (iter P apex j)
                                (step-cocone (λ k → iter-mor P (inj k) j) (λ k → ℓ-step k j))

      extend-env j .EnvChain.obs k      = extend (obs k) (iter P (obs k) j)
      extend-env j .EnvChain.steps k    = extend-mor (steps k) (iter-mor P (steps k) j)
      extend-env j .EnvChain.apex       = extend apex (iter P apex j)
      extend-env j .EnvChain.inj k      = extend-mor (inj k) (iter-mor P (inj k) j)
      extend-env j .EnvChain.inj-step k Fin.zero    = ℓ-step k j
      extend-env j .EnvChain.inj-step k (Fin.suc i) = inj-step k i
      extend-env j .EnvChain.colimiting Fin.zero    = columns j
      extend-env j .EnvChain.colimiting (Fin.suc i) = colimiting i

      columns zero    = IsColimit-cong (record { transf-eq = λ k → ≈-refl })
                                       (const-chain-colimit 𝟘 .Colimit.isColimit)
      columns (suc j) = ⟦ P ⟧-cocont (extend-env j)

      module IC = interchange {𝒞 = 𝒟}
        (λ k j → iter P (obs k) j)
        (λ k j → step P (obs k) j)
        (λ k j → iter-mor P (steps k) j)
        (λ k j → iter-mor-step P (steps k) j)
        Rk
        (iter P apex) (step P apex)
        (λ k j → iter-mor P (inj k) j)
        ℓ-step ℓ-v columns
        (colimits (chain (iter P apex) (step P apex)))

      -- The interchange cocone legs agree with the canonical ones (both mediate the same legs).
      legs-eq : ∀ k → IC.ρ-inj k ≈ ⟦ μ P ⟧mor (inj k)
      legs-eq k = Rk k .Colimit.colambda-cong (record { transf-eq = λ j → ≈-refl })
  ⟦ T∘ P ⟧-cocont    E = T-cocont (⟦ P ⟧-cocont E)

  -- The algebra map: by cocontinuity, ⟦ P ⟧ at the carrier is the colimit of the shifted
  -- initial-algebra chain, which the shifted injections mediate back into the carrier.
  α : ∀ {n} (P : Poly (suc n)) (δ : Fin n → obj) → ⟦ P ⟧ (extend δ (μ-carrier P δ)) ⇒ μ-carrier P δ
  α {n} P δ =
    ⟦ P ⟧-cocont carrier-env .IsColimit.colambda (μ-carrier P δ)
      (step-cocone (λ k → μC .Colimit.cocone .NatTrans.transf (suc k))
                   (λ k → cocone-step (μC .Colimit.cocone) (suc k)))
    where
      μC : Colimit (chain {𝒞 = 𝒟} (iter P δ) (step P δ))
      μC = colimits (chain (iter P δ) (step P δ))

      -- The constant environment δ, extended in the recursion coordinate by the initial-algebra
      -- chain and its colimit.
      carrier-env : EnvChain (suc n)
      carrier-env .EnvChain.obs k   = extend δ (iter P δ k)
      carrier-env .EnvChain.steps k = extend-fam (step P δ k)
      carrier-env .EnvChain.apex    = extend δ (μ-carrier P δ)
      carrier-env .EnvChain.inj k   = extend-fam (μC .Colimit.cocone .NatTrans.transf k)
      carrier-env .EnvChain.inj-step k Fin.zero    = cocone-step (μC .Colimit.cocone) k
      carrier-env .EnvChain.inj-step k (Fin.suc i) = ≈-sym id-left
      carrier-env .EnvChain.colimiting Fin.zero    =
        IsColimit-cong (record { transf-eq = λ k → ≈-refl }) (μC .Colimit.isColimit)
      carrier-env .EnvChain.colimiting (Fin.suc i) =
        IsColimit-cong (record { transf-eq = λ k → ≈-refl }) (const-chain-colimit (δ i) .Colimit.isColimit)
