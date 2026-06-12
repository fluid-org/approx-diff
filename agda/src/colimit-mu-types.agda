{-# OPTIONS --prop --postfix-projections --safe #-}

-- μ-types (parameterised initial algebras of polynomial functors) in a category 𝒟 with an initial
-- object and colimits of ω-chains, via the initial-algebra chain 0 → F0 → F²0 → ⋯ . Counterpart of
-- fam-mu-types, which builds them in Fam(𝒞) via W-types.

import Data.Fin as Fin
open Fin using (Fin)
open import Data.Nat using (ℕ; zero; suc)
open import categories
  using (Category; HasTerminal; HasProducts; HasCoproducts; HasStrongCoproducts;
         strong-coproducts→coproducts; HasInitial)
open import functor using (Functor; StrongFunctor; HasColimits; Colimit)
open import omega-chains using (ω; chain; colim-map; colim-map-cong; colim-map-comp; colim-map-id; square-comp)
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
open HasCoproducts (strong-coproducts→coproducts 𝒟T 𝒟SC) using (coprod; coprod-m; coprod-m-cong; coprod-m-comp; coprod-m-id; in₁; in₂)
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
