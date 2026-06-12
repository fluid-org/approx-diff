{-# OPTIONS --prop --postfix-projections #-}

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
open import omega-chains using (ω; chain; colim-map)
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
open HasCoproducts (strong-coproducts→coproducts 𝒟T 𝒟SC) using (coprod; coprod-m; coprod-m-cong; coprod-m-comp; in₁; in₂)
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

  ⟦_⟧mor-cong : ∀ {n} (P : Poly n) {δ δ' : Fin n → obj} {fs gs : ∀ i → δ i ⇒ δ' i} →
                (∀ i → fs i ≈ gs i) → ⟦ P ⟧mor fs ≈ ⟦ P ⟧mor gs
  ⟦ const A ⟧mor-cong fs≈gs = ≈-refl
  ⟦ var i ⟧mor-cong   fs≈gs = fs≈gs i
  ⟦ P + Q ⟧mor-cong   fs≈gs = coprod-m-cong (⟦ P ⟧mor-cong fs≈gs) (⟦ Q ⟧mor-cong fs≈gs)
  ⟦ P × Q ⟧mor-cong   fs≈gs = prod-m-cong (⟦ P ⟧mor-cong fs≈gs) (⟦ Q ⟧mor-cong fs≈gs)
  ⟦ μ P ⟧mor-cong     fs≈gs = {!!}
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
  ⟦ μ P ⟧mor-comp     fs gs = {!!}
  ⟦ T∘ P ⟧mor-comp    fs gs =
    ≈-trans (Functor.fmor-cong T (⟦ P ⟧mor-comp fs gs)) (Functor.fmor-comp T _ _)
