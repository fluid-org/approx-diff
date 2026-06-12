{-# OPTIONS --prop --postfix-projections --safe #-}

import Data.Fin as Fin
open Fin using (Fin)
open import Data.Nat using (ℕ; zero; suc)
open import Level using (_⊔_)
open import categories
  using (Category; HasTerminal; HasProducts; HasCoproducts; HasStrongCoproducts;
         strong-coproducts→coproducts; coKleisli-prod; module Unitor)
open import functor using (Functor; StrongFunctor)
open import product-category using (_^_)
open import prop-setoid using (module ≈-Reasoning)

module polynomial-functor-2
  {o m e} {𝒞 : Category o m e}
  (𝒞T : HasTerminal 𝒞) (𝒞P : HasProducts 𝒞) (𝒞SCP : HasStrongCoproducts 𝒞 𝒞P)
  (T-strong : StrongFunctor 𝒞P) where

open Category 𝒞
open HasProducts 𝒞P
open HasCoproducts (strong-coproducts→coproducts 𝒞T 𝒞SCP)
open HasStrongCoproducts 𝒞SCP using () renaming (copair to scopair; copair-cong to scopair-cong; copair-ext0 to scopair-p₂; copair-ext to scopair-ext; copair-in₁ to scopair-in₁; copair-in₂ to scopair-in₂)
open StrongFunctor T-strong using (strengthᵣ; strengthᵣ-p₂; strengthᵣ-natural; strengthᵣ-assoc) renaming (F to T)
open Unitor 𝒞T 𝒞P using (unitor-natural; unitor-comp)

-- co-Kleisli notation: a morphism f : prod Γ X ⇒ Y lives in the co-Kleisli category for prod Γ -.
infixl 21 _∘co_
_∘co_ : ∀ {Γ X Y Z} → (prod Γ Y ⇒ Z) → (prod Γ X ⇒ Y) → (prod Γ X ⇒ Z)
_∘co_ {Γ} = Category._∘_ (coKleisli-prod 𝒞P Γ)

module _ {Γ : obj} where
  open Category (coKleisli-prod 𝒞P Γ) public using ()
    renaming (assoc to assoc-co; ∘-cong₁ to ∘-cong-co₁; ∘-cong₂ to ∘-cong-co₂)

data Poly (n : ℕ) : Set o where
  const : obj → Poly n
  var   : Fin n → Poly n
  _+_   : Poly n → Poly n → Poly n
  _×_   : Poly n → Poly n → Poly n
  μ     : Poly (suc n) → Poly n
  T∘_   : Poly n → Poly n

extend : ∀ {n} → (Fin n → obj) → obj → Fin (suc n) → obj
extend δ A Fin.zero    = A
extend δ A (Fin.suc i) = δ i

fobj : ∀ {n} → (μ-obj : ∀ {m} → Poly (suc m) → (Fin m → obj) → obj) → Poly n → (Fin n → obj) → obj
fobj μ-obj (const A) δ = A
fobj μ-obj (var i)   δ = δ i
fobj μ-obj (P + Q)   δ = coprod (fobj μ-obj P δ) (fobj μ-obj Q δ)
fobj μ-obj (P × Q)   δ = prod (fobj μ-obj P δ) (fobj μ-obj Q δ)
fobj μ-obj (μ P)     δ = μ-obj P δ
fobj μ-obj (T∘ P)    δ = Functor.fobj T (fobj μ-obj P δ)

-- Use a Mendler-style catamorphism (Mendler 1991, "Inductive types and type constraints
-- in the second-order lambda calculus") which abstracts over the recursive carrier, so β/η can be stated
-- without reference to a functorial action; otherwise things get circular. Usual ⦅_⦆ is then derived.
record HasMu : Set (o ⊔ m ⊔ e) where
  field
    μ-obj : ∀ {n} → Poly (suc n) → (Fin n → obj) → obj
    α     : ∀ {n} (P : Poly (suc n)) (δ : Fin n → obj) → fobj μ-obj P (extend δ (μ-obj P δ)) ⇒ μ-obj P δ
    ⦅_⦆ᴹ : ∀ {n Γ A} {P : Poly (suc n)} {δ : Fin n → obj} →
          (∀ X → (prod Γ X ⇒ A) → (prod Γ (fobj μ-obj P (extend δ X)) ⇒ A)) → prod Γ (μ-obj P δ) ⇒ A
    ⦅⦆ᴹ-β : ∀ {n Γ A} {P : Poly (suc n)} {δ : Fin n → obj}
           (step : ∀ X → (prod Γ X ⇒ A) → (prod Γ (fobj μ-obj P (extend δ X)) ⇒ A)) →
           (⦅ step ⦆ᴹ ∘co (α P δ ∘ p₂)) ≈ step (μ-obj P δ) ⦅ step ⦆ᴹ
    ⦅⦆ᴹ-η : ∀ {n Γ A} {P : Poly (suc n)} {δ : Fin n → obj}
           (step : ∀ X → (prod Γ X ⇒ A) → (prod Γ (fobj μ-obj P (extend δ X)) ⇒ A))
           (h : prod Γ (μ-obj P δ) ⇒ A) → (h ∘co (α P δ ∘ p₂)) ≈ step (μ-obj P δ) h → h ≈ ⦅ step ⦆ᴹ

  open HasTerminal 𝒞T using (witness; to-terminal; to-terminal-unique)

  extend-mor : ∀ {n Γ} {δ δ' : Fin n → obj} {X Y} →
               (∀ i → prod Γ (δ i) ⇒ δ' i) → (prod Γ X ⇒ Y) → ∀ i → prod Γ (extend δ X i) ⇒ extend δ' Y i
  extend-mor fs x→y Fin.zero    = x→y
  extend-mor fs x→y (Fin.suc i) = fs i

  mutual
    strong-fmor : ∀ {n Γ} (P : Poly n) {δ δ' : Fin n → obj} →
                  (∀ i → prod Γ (δ i) ⇒ δ' i) → prod Γ (fobj μ-obj P δ) ⇒ fobj μ-obj P δ'
    strong-fmor (const A) fs = p₂
    strong-fmor (var i)   fs = fs i
    strong-fmor (P + Q)   fs = scopair (in₁ ∘ strong-fmor P fs) (in₂ ∘ strong-fmor Q fs)
    strong-fmor (P × Q)   fs = pair (strong-fmor P fs ∘ pair p₁ (p₁ ∘ p₂))
                                    (strong-fmor Q fs ∘ pair p₁ (p₂ ∘ p₂))
    strong-fmor (μ P)     fs = strong-μ-fmor P fs
    strong-fmor (T∘ P)    fs = Functor.fmor T (strong-fmor P fs) ∘ strengthᵣ

    strong-μ-fmor : ∀ {n Γ} (P : Poly (suc n)) {δ δ' : Fin n → obj} →
                    (∀ i → prod Γ (δ i) ⇒ δ' i) → prod Γ (μ-obj P δ) ⇒ μ-obj P δ'
    strong-μ-fmor P {δ} {δ'} fs = ⦅ step ⦆ᴹ
      where
        step : ∀ X → (prod _ X ⇒ μ-obj P δ') → prod _ (fobj μ-obj P (extend δ X)) ⇒ μ-obj P δ'
        step X x→μ' = α P δ' ∘ strong-fmor P (extend-mor fs x→μ')

  fmor : ∀ {n} (P : Poly n) {δ δ' : Fin n → obj} → (∀ i → δ i ⇒ δ' i) → fobj μ-obj P δ ⇒ fobj μ-obj P δ'
  fmor P fs = strong-fmor P (λ i → fs i ∘ p₂) ∘ pair to-terminal (id _)

  ⦅_⦆ : ∀ {n Γ A} {P : Poly (suc n)} {δ : Fin n → obj} →
        (prod Γ (fobj μ-obj P (extend δ A)) ⇒ A) → prod Γ (μ-obj P δ) ⇒ A
  ⦅_⦆ {Γ = Γ} {A = A} {P = P} {δ = δ} alg = ⦅ step ⦆ᴹ
    where
      step : ∀ X → (prod Γ X ⇒ A) → prod Γ (fobj μ-obj P (extend δ X)) ⇒ A
      step X x→A = alg ∘ pair p₁ (strong-fmor P (extend-mor (λ _ → p₂) x→A))

  -- Carrier-shaped morphism family: f at position 0, id at positions 1..n.
  extend-fam : ∀ {n} {δ : Fin n → obj} {X Y} → (X ⇒ Y) → ∀ i → extend δ X i ⇒ extend δ Y i
  extend-fam f Fin.zero    = f
  extend-fam f (Fin.suc i) = id _

  -- Mendler step for μ-map, parameterized by an unfolding morphism family.
  -- P, δ, Q, δ' are explicit because fobj/μ-obj are not injective, so they can't be inferred from the family.
  μ-map-step : ∀ {m n} (P : Poly (suc m)) (δ : Fin m → obj) (Q : Poly (suc n)) (δ' : Fin n → obj) →
               (∀ X → fobj μ-obj P (extend δ X) ⇒ fobj μ-obj Q (extend δ' X)) →
               ∀ X → (prod witness X ⇒ μ-obj Q δ') → prod witness (fobj μ-obj P (extend δ X)) ⇒ μ-obj Q δ'
  μ-map-step P δ Q δ' unfold X x→μ' =
    α Q δ' ∘ fmor Q (extend-fam (x→μ' ∘ pair to-terminal (id _))) ∘ unfold X ∘ p₂

  -- μ-obj is functorial along unfolding morphism families. No naturality requirement: that is only
  -- needed for the iso laws (μ-obj-resp below), not to construct the map.
  μ-map : ∀ {m n} (P : Poly (suc m)) (δ : Fin m → obj) (Q : Poly (suc n)) (δ' : Fin n → obj) →
          (∀ X → fobj μ-obj P (extend δ X) ⇒ fobj μ-obj Q (extend δ' X)) →
          μ-obj P δ ⇒ μ-obj Q δ'
  μ-map P δ Q δ' unfold = ⦅ μ-map-step P δ Q δ' unfold ⦆ᴹ ∘ pair to-terminal (id _)

  -- Equational properties of the functorial actions, culminating in μ-obj-resp: initial algebras
  -- of pointwise-isomorphic functors are isomorphic. Nothing below is needed to define the term
  -- semantics; retained for the iso laws.

  ⦅_⦆ᴹ-cong : ∀ {n Γ A} {P : Poly (suc n)} {δ : Fin n → obj}
              {step₁ step₂ : ∀ X → (prod Γ X ⇒ A) → (prod Γ (fobj μ-obj P (extend δ X)) ⇒ A)} →
              (∀ X (x→A : prod Γ X ⇒ A) → step₁ X x→A ≈ step₂ X x→A) → ⦅ step₁ ⦆ᴹ ≈ ⦅ step₂ ⦆ᴹ
  ⦅_⦆ᴹ-cong {P = P} {δ = δ} {step₁ = step₁} {step₂ = step₂} step₁≈step₂ =
    ⦅⦆ᴹ-η {P = P} {δ = δ} step₂ ⦅ step₁ ⦆ᴹ
      (≈-trans (⦅⦆ᴹ-β {P = P} {δ = δ} step₁) (step₁≈step₂ (μ-obj P δ) ⦅ step₁ ⦆ᴹ))

  extend-mor-cong : ∀ {n Γ} {δ δ' : Fin n → obj} {X Y}
                    {fs gs : ∀ i → prod Γ (δ i) ⇒ δ' i} {x→y : prod Γ X ⇒ Y} →
                    (∀ i → fs i ≈ gs i) → ∀ i → extend-mor fs x→y i ≈ extend-mor gs x→y i
  extend-mor-cong fs≈gs Fin.zero    = ≈-refl
  extend-mor-cong fs≈gs (Fin.suc i) = fs≈gs i

  mutual
    strong-fmor-cong : ∀ {n Γ} (P : Poly n) {δ δ' : Fin n → obj}
                       {fs gs : ∀ i → prod Γ (δ i) ⇒ δ' i} →
                       (∀ i → fs i ≈ gs i) → strong-fmor P fs ≈ strong-fmor P gs
    strong-fmor-cong (const A) fs≈gs = ≈-refl
    strong-fmor-cong (var i)   fs≈gs = fs≈gs i
    strong-fmor-cong (P + Q)   fs≈gs =
      scopair-cong (∘-cong₂ (strong-fmor-cong P fs≈gs)) (∘-cong₂ (strong-fmor-cong Q fs≈gs))
    strong-fmor-cong (P × Q)   fs≈gs =
      pair-cong (∘-cong₁ (strong-fmor-cong P fs≈gs)) (∘-cong₁ (strong-fmor-cong Q fs≈gs))
    strong-fmor-cong (μ P)     fs≈gs = strong-μ-fmor-cong P fs≈gs
    strong-fmor-cong (T∘ P)    fs≈gs = ∘-cong₁ (Functor.fmor-cong T (strong-fmor-cong P fs≈gs))

    strong-μ-fmor-cong : ∀ {n Γ} (P : Poly (suc n)) {δ δ' : Fin n → obj}
                         {fs gs : ∀ i → prod Γ (δ i) ⇒ δ' i} →
                         (∀ i → fs i ≈ gs i) → strong-μ-fmor P fs ≈ strong-μ-fmor P gs
    strong-μ-fmor-cong P {δ} {δ'} fs≈gs = ⦅_⦆ᴹ-cong λ X x→μ' →
      ∘-cong₂ (strong-fmor-cong P (extend-mor-cong fs≈gs))

  extend-mor-p₂ : ∀ {n Γ} {δ : Fin n → obj} {X} →
                  ∀ i → extend-mor {δ = δ} {δ' = δ} (λ _ → p₂) (p₂ {Γ} {X}) i ≈ p₂
  extend-mor-p₂ Fin.zero    = ≈-refl
  extend-mor-p₂ (Fin.suc i) = ≈-refl

  mutual
    strong-fmor-id : ∀ {n Γ} (P : Poly n) {δ : Fin n → obj} →
                     strong-fmor {Γ = Γ} P {δ = δ} {δ' = δ} (λ _ → p₂) ≈ p₂
    strong-fmor-id (const A) = ≈-refl
    strong-fmor-id (var i) = ≈-refl
    strong-fmor-id (P + Q) =
      ≈-trans (scopair-cong (∘-cong₂ (strong-fmor-id P)) (∘-cong₂ (strong-fmor-id Q))) scopair-p₂
    strong-fmor-id (P × Q) =
      ≈-trans (pair-cong (∘-cong₁ (strong-fmor-id P)) (∘-cong₁ (strong-fmor-id Q)))
              (≈-trans (pair-cong (pair-p₂ _ _) (pair-p₂ _ _)) (pair-ext _))
    strong-fmor-id (μ P) = strong-μ-fmor-id P
    strong-fmor-id (T∘ P) =
      ≈-trans (∘-cong₁ (Functor.fmor-cong T (strong-fmor-id P))) strengthᵣ-p₂

    strong-μ-fmor-id : ∀ {n Γ} (P : Poly (suc n)) {δ : Fin n → obj} →
                       strong-μ-fmor {Γ = Γ} P {δ = δ} {δ' = δ} (λ _ → p₂) ≈ p₂
    strong-μ-fmor-id P {δ} =
      ≈-sym (⦅⦆ᴹ-η _ p₂
        (≈-trans (pair-p₂ _ _)
                 (≈-sym (∘-cong₂ (≈-trans (strong-fmor-cong P extend-mor-p₂) (strong-fmor-id P))))))

  -- Functoriality of strong-fmor in the co-Kleisli category for prod Γ -.
  mutual
    strong-fmor-comp : ∀ {n Γ} (P : Poly n) {δ δ' δ'' : Fin n → obj}
                       (fs : ∀ i → prod Γ (δ' i) ⇒ δ'' i) (gs : ∀ i → prod Γ (δ i) ⇒ δ' i) →
                       strong-fmor P fs ∘ pair p₁ (strong-fmor P gs) ≈ strong-fmor P (λ i → fs i ∘ pair p₁ (gs i))
    strong-fmor-comp (const A) fs gs = pair-p₂ _ _
    strong-fmor-comp (var i) fs gs = ≈-refl
    strong-fmor-comp (P + Q) fs gs =
      begin
        strong-fmor (P + Q) fs ∘ pair p₁ (strong-fmor (P + Q) gs)
      ≈⟨ ≈-sym (scopair-ext (strong-fmor (P + Q) fs ∘ pair p₁ (strong-fmor (P + Q) gs))) ⟩
        scopair (strong-fmor (P + Q) fs ∘ pair p₁ (strong-fmor (P + Q) gs) ∘ pair p₁ (in₁ ∘ p₂))
                (strong-fmor (P + Q) fs ∘ pair p₁ (strong-fmor (P + Q) gs) ∘ pair p₁ (in₂ ∘ p₂))
      ≈⟨ scopair-cong in₁-branch in₂-branch ⟩
        scopair (in₁ ∘ strong-fmor P (λ i → fs i ∘ pair p₁ (gs i))) (in₂ ∘ strong-fmor Q (λ i → fs i ∘ pair p₁ (gs i)))
      ∎
      where
        in₁-branch : strong-fmor (P + Q) fs ∘ pair p₁ (strong-fmor (P + Q) gs) ∘ pair p₁ (in₁ ∘ p₂) ≈
                     in₁ ∘ strong-fmor P (λ i → fs i ∘ pair p₁ (gs i))
        in₁-branch =
          begin
            strong-fmor (P + Q) fs ∘ pair p₁ (strong-fmor (P + Q) gs) ∘ pair p₁ (in₁ ∘ p₂)
          ≈⟨ assoc-co _ _ _ ⟩
            strong-fmor (P + Q) fs ∘ pair p₁ (strong-fmor (P + Q) gs ∘ pair p₁ (in₁ ∘ p₂))
          ≈⟨ ∘-cong₂ (pair-cong ≈-refl (≈-trans (scopair-in₁ _ _) (≈-sym (≈-trans (assoc _ _ _) (∘-cong₂ (pair-p₂ _ _)))))) ⟩
            strong-fmor (P + Q) fs ∘ pair p₁ ((in₁ ∘ p₂) ∘ pair p₁ (strong-fmor P gs))
          ≈⟨ ≈-sym (assoc-co _ _ _) ⟩
            (strong-fmor (P + Q) fs ∘ pair p₁ (in₁ ∘ p₂)) ∘ pair p₁ (strong-fmor P gs)
          ≈⟨ ∘-cong₁ (scopair-in₁ _ _) ⟩
            (in₁ ∘ strong-fmor P fs) ∘ pair p₁ (strong-fmor P gs)
          ≈⟨ assoc _ _ _ ⟩
            in₁ ∘ (strong-fmor P fs ∘ pair p₁ (strong-fmor P gs))
          ≈⟨ ∘-cong₂ (strong-fmor-comp P fs gs) ⟩
            in₁ ∘ strong-fmor P (λ i → fs i ∘ pair p₁ (gs i))
          ∎ where open ≈-Reasoning isEquiv
        in₂-branch : strong-fmor (P + Q) fs ∘ pair p₁ (strong-fmor (P + Q) gs) ∘ pair p₁ (in₂ ∘ p₂) ≈
                     in₂ ∘ strong-fmor Q (λ i → fs i ∘ pair p₁ (gs i))
        in₂-branch =
          begin
            strong-fmor (P + Q) fs ∘ pair p₁ (strong-fmor (P + Q) gs) ∘ pair p₁ (in₂ ∘ p₂)
          ≈⟨ assoc-co _ _ _ ⟩
            strong-fmor (P + Q) fs ∘ pair p₁ (strong-fmor (P + Q) gs ∘ pair p₁ (in₂ ∘ p₂))
          ≈⟨ ∘-cong₂ (pair-cong ≈-refl (≈-trans (scopair-in₂ _ _) (≈-sym (≈-trans (assoc _ _ _) (∘-cong₂ (pair-p₂ _ _)))))) ⟩
            strong-fmor (P + Q) fs ∘ pair p₁ ((in₂ ∘ p₂) ∘ pair p₁ (strong-fmor Q gs))
          ≈⟨ ≈-sym (assoc-co _ _ _) ⟩
            (strong-fmor (P + Q) fs ∘ pair p₁ (in₂ ∘ p₂)) ∘ pair p₁ (strong-fmor Q gs)
          ≈⟨ ∘-cong₁ (scopair-in₂ _ _) ⟩
            (in₂ ∘ strong-fmor Q fs) ∘ pair p₁ (strong-fmor Q gs)
          ≈⟨ assoc _ _ _ ⟩
            in₂ ∘ (strong-fmor Q fs ∘ pair p₁ (strong-fmor Q gs))
          ≈⟨ ∘-cong₂ (strong-fmor-comp Q fs gs) ⟩
            in₂ ∘ strong-fmor Q (λ i → fs i ∘ pair p₁ (gs i))
          ∎ where open ≈-Reasoning isEquiv
        open ≈-Reasoning isEquiv
    strong-fmor-comp (P × Q) fs gs =
      begin
        strong-fmor (P × Q) fs ∘ pair p₁ (strong-fmor (P × Q) gs)
      ≈⟨ pair-natural _ _ _ ⟩
        pair ((strong-fmor P fs ∘ pair p₁ (p₁ ∘ p₂)) ∘ pair p₁ (strong-fmor (P × Q) gs))
             ((strong-fmor Q fs ∘ pair p₁ (p₂ ∘ p₂)) ∘ pair p₁ (strong-fmor (P × Q) gs))
      ≈⟨ pair-cong fst-branch snd-branch ⟩
        pair (strong-fmor P (λ i → fs i ∘ pair p₁ (gs i)) ∘ pair p₁ (p₁ ∘ p₂))
             (strong-fmor Q (λ i → fs i ∘ pair p₁ (gs i)) ∘ pair p₁ (p₂ ∘ p₂))
      ∎
      where
        fst-branch : (strong-fmor P fs ∘ pair p₁ (p₁ ∘ p₂)) ∘ pair p₁ (strong-fmor (P × Q) gs) ≈
                     strong-fmor P (λ i → fs i ∘ pair p₁ (gs i)) ∘ pair p₁ (p₁ ∘ p₂)
        fst-branch =
          begin
            (strong-fmor P fs ∘ pair p₁ (p₁ ∘ p₂)) ∘ pair p₁ (strong-fmor (P × Q) gs)
          ≈⟨ assoc-co _ _ _ ⟩
            strong-fmor P fs ∘ pair p₁ ((p₁ ∘ p₂) ∘ pair p₁ (strong-fmor (P × Q) gs))
          ≈⟨ ∘-cong₂ (pair-cong ≈-refl (≈-trans (≈-trans (assoc _ _ _) (∘-cong₂ (pair-p₂ _ _))) (pair-p₁ _ _))) ⟩
            strong-fmor P fs ∘ pair p₁ (strong-fmor P gs ∘ pair p₁ (p₁ ∘ p₂))
          ≈⟨ ≈-sym (assoc-co _ _ _) ⟩
            (strong-fmor P fs ∘ pair p₁ (strong-fmor P gs)) ∘ pair p₁ (p₁ ∘ p₂)
          ≈⟨ ∘-cong₁ (strong-fmor-comp P fs gs) ⟩
            strong-fmor P (λ i → fs i ∘ pair p₁ (gs i)) ∘ pair p₁ (p₁ ∘ p₂)
          ∎ where open ≈-Reasoning isEquiv
        snd-branch : (strong-fmor Q fs ∘ pair p₁ (p₂ ∘ p₂)) ∘ pair p₁ (strong-fmor (P × Q) gs) ≈
                     strong-fmor Q (λ i → fs i ∘ pair p₁ (gs i)) ∘ pair p₁ (p₂ ∘ p₂)
        snd-branch =
          begin
            (strong-fmor Q fs ∘ pair p₁ (p₂ ∘ p₂)) ∘ pair p₁ (strong-fmor (P × Q) gs)
          ≈⟨ assoc-co _ _ _ ⟩
            strong-fmor Q fs ∘ pair p₁ ((p₂ ∘ p₂) ∘ pair p₁ (strong-fmor (P × Q) gs))
          ≈⟨ ∘-cong₂ (pair-cong ≈-refl (≈-trans (≈-trans (assoc _ _ _) (∘-cong₂ (pair-p₂ _ _))) (pair-p₂ _ _))) ⟩
            strong-fmor Q fs ∘ pair p₁ (strong-fmor Q gs ∘ pair p₁ (p₂ ∘ p₂))
          ≈⟨ ≈-sym (assoc-co _ _ _) ⟩
            (strong-fmor Q fs ∘ pair p₁ (strong-fmor Q gs)) ∘ pair p₁ (p₂ ∘ p₂)
          ≈⟨ ∘-cong₁ (strong-fmor-comp Q fs gs) ⟩
            strong-fmor Q (λ i → fs i ∘ pair p₁ (gs i)) ∘ pair p₁ (p₂ ∘ p₂)
          ∎ where open ≈-Reasoning isEquiv
        open ≈-Reasoning isEquiv
    strong-fmor-comp (μ P) fs gs = strong-μ-fmor-comp P fs gs
    strong-fmor-comp (T∘ P) fs gs =
      begin
        (Functor.fmor T (strong-fmor P fs) ∘ strengthᵣ) ∘ pair p₁ (Functor.fmor T (strong-fmor P gs) ∘ strengthᵣ)
      ≈⟨ assoc _ _ _ ⟩
        Functor.fmor T (strong-fmor P fs) ∘ (strengthᵣ ∘ pair p₁ (Functor.fmor T (strong-fmor P gs) ∘ strengthᵣ))
      ≈⟨ ∘-cong₂ (∘-cong₂ (≈-sym (push (Functor.fmor T (strong-fmor P gs)) strengthᵣ))) ⟩
        Functor.fmor T (strong-fmor P fs) ∘ (strengthᵣ ∘ (prod-m (id _) (Functor.fmor T (strong-fmor P gs)) ∘ pair p₁ strengthᵣ))
      ≈⟨ ∘-cong₂ (≈-sym (assoc _ _ _)) ⟩
        Functor.fmor T (strong-fmor P fs) ∘ ((strengthᵣ ∘ prod-m (id _) (Functor.fmor T (strong-fmor P gs))) ∘ pair p₁ strengthᵣ)
      ≈⟨ ∘-cong₂ (∘-cong₁ (≈-sym (strengthᵣ-natural (id _) (strong-fmor P gs)))) ⟩
        Functor.fmor T (strong-fmor P fs) ∘ ((Functor.fmor T (prod-m (id _) (strong-fmor P gs)) ∘ strengthᵣ) ∘ pair p₁ strengthᵣ)
      ≈⟨ ∘-cong₂ (assoc _ _ _) ⟩
        Functor.fmor T (strong-fmor P fs) ∘ (Functor.fmor T (prod-m (id _) (strong-fmor P gs)) ∘ (strengthᵣ ∘ pair p₁ strengthᵣ))
      ≈⟨ ∘-cong₂ (∘-cong₂ strengthᵣ-assoc) ⟩
        Functor.fmor T (strong-fmor P fs) ∘ (Functor.fmor T (prod-m (id _) (strong-fmor P gs)) ∘ (Functor.fmor T (pair p₁ (id _)) ∘ strengthᵣ))
      ≈⟨ ∘-cong₂ (≈-sym (assoc _ _ _)) ⟩
        Functor.fmor T (strong-fmor P fs) ∘ ((Functor.fmor T (prod-m (id _) (strong-fmor P gs)) ∘ Functor.fmor T (pair p₁ (id _))) ∘ strengthᵣ)
      ≈⟨ ∘-cong₂ (∘-cong₁ (≈-trans (≈-sym (Functor.fmor-comp T _ _))
                                   (Functor.fmor-cong T (≈-trans (push (strong-fmor P gs) (id _)) (pair-cong ≈-refl id-right))))) ⟩
        Functor.fmor T (strong-fmor P fs) ∘ (Functor.fmor T (pair p₁ (strong-fmor P gs)) ∘ strengthᵣ)
      ≈⟨ ≈-sym (assoc _ _ _) ⟩
        (Functor.fmor T (strong-fmor P fs) ∘ Functor.fmor T (pair p₁ (strong-fmor P gs))) ∘ strengthᵣ
      ≈⟨ ∘-cong₁ (≈-trans (≈-sym (Functor.fmor-comp T _ _)) (Functor.fmor-cong T (strong-fmor-comp P fs gs))) ⟩
        Functor.fmor T (strong-fmor P (λ i → fs i ∘ pair p₁ (gs i))) ∘ strengthᵣ
      ∎
      where
        -- Push a co-Kleisli pair p₁ k through prod-m (id _) h.
        push : ∀ {W A B C} (h : A ⇒ B) (k : prod W C ⇒ A) →
               prod-m (id _) h ∘ pair p₁ k ≈ pair p₁ (h ∘ k)
        push h k =
          begin
            prod-m (id _) h ∘ pair p₁ k
          ≈⟨ pair-natural _ _ _ ⟩
            pair ((id _ ∘ p₁) ∘ pair p₁ k) ((h ∘ p₂) ∘ pair p₁ k)
          ≈⟨ pair-cong (≈-trans (assoc _ _ _) (≈-trans (∘-cong₂ (pair-p₁ _ _)) id-left))
                       (≈-trans (assoc _ _ _) (∘-cong₂ (pair-p₂ _ _))) ⟩
            pair p₁ (h ∘ k)
          ∎ where open ≈-Reasoning isEquiv
        open ≈-Reasoning isEquiv

    strong-μ-fmor-comp : ∀ {n Γ} (P : Poly (suc n)) {δ δ' δ'' : Fin n → obj}
                         (fs : ∀ i → prod Γ (δ' i) ⇒ δ'' i) (gs : ∀ i → prod Γ (δ i) ⇒ δ' i) →
                         strong-μ-fmor P fs ∘ pair p₁ (strong-μ-fmor P gs) ≈ strong-μ-fmor P (λ i → fs i ∘ pair p₁ (gs i))
    strong-μ-fmor-comp P {δ = δ} {δ' = δ'} {δ'' = δ''} fs gs =
      ⦅⦆ᴹ-η _ (strong-μ-fmor P fs ∘ pair p₁ (strong-μ-fmor P gs))
        ( begin
            strong-μ-fmor P fs ∘ pair p₁ (strong-μ-fmor P gs) ∘ pair p₁ (α P δ ∘ p₂)
          ≈⟨ assoc-co _ _ _ ⟩
            strong-μ-fmor P fs ∘ pair p₁ (strong-μ-fmor P gs ∘ pair p₁ (α P δ ∘ p₂))
          ≈⟨ ∘-cong₂ (pair-cong ≈-refl (≈-trans (⦅⦆ᴹ-β _) (≈-sym (≈-trans (assoc _ _ _) (∘-cong₂ (pair-p₂ _ _)))))) ⟩
            strong-μ-fmor P fs ∘ pair p₁ ((α P δ' ∘ p₂) ∘ pair p₁ (strong-fmor P (extend-mor gs (strong-μ-fmor P gs))))
          ≈⟨ ≈-sym (assoc-co _ _ _) ⟩
            (strong-μ-fmor P fs ∘ pair p₁ (α P δ' ∘ p₂)) ∘ pair p₁ (strong-fmor P (extend-mor gs (strong-μ-fmor P gs)))
          ≈⟨ ∘-cong₁ (⦅⦆ᴹ-β _) ⟩
            (α P δ'' ∘ strong-fmor P (extend-mor fs (strong-μ-fmor P fs))) ∘ pair p₁ (strong-fmor P (extend-mor gs (strong-μ-fmor P gs)))
          ≈⟨ assoc _ _ _ ⟩
            α P δ'' ∘
            (strong-fmor P (extend-mor fs (strong-μ-fmor P fs)) ∘ pair p₁ (strong-fmor P (extend-mor gs (strong-μ-fmor P gs))))
          ≈⟨ ∘-cong₂ (≈-trans (strong-fmor-comp P (extend-mor fs (strong-μ-fmor P fs)) (extend-mor gs (strong-μ-fmor P gs)))
                              (strong-fmor-cong P (λ { Fin.zero → ≈-refl ; (Fin.suc _) → ≈-refl }))) ⟩
            α P δ'' ∘ strong-fmor P (extend-mor (λ i → fs i ∘ pair p₁ (gs i)) (strong-μ-fmor P fs ∘ pair p₁ (strong-μ-fmor P gs)))
          ∎)
      where open ≈-Reasoning isEquiv

  -- Precomposing fmor with the counit p₂ undoes the unit, leaving the co-Kleisli action.
  fmor-p₂ : ∀ {n} (P : Poly n) {δ δ' : Fin n → obj} (fs : ∀ i → δ i ⇒ δ' i) →
            fmor P fs ∘ p₂ ≈ strong-fmor P (λ i → fs i ∘ p₂)
  fmor-p₂ P fs = ≈-trans (assoc _ _ _) (≈-trans (∘-cong₂ (≈-trans (unitor-natural p₂) pair-ext0)) id-right)

  fmor-comp : ∀ {n} (P : Poly n) {δ δ' δ'' : Fin n → obj}
              (fs : ∀ i → δ' i ⇒ δ'' i) (gs : ∀ i → δ i ⇒ δ' i) →
              (fmor P fs ∘ fmor P gs) ≈ fmor P (λ i → fs i ∘ gs i)
  fmor-comp P fs gs =
    begin
      fmor P fs ∘ fmor P gs
    ≈⟨ assoc _ _ _ ⟩
      strong-fmor P (λ i → fs i ∘ p₂) ∘ (pair to-terminal (id _) ∘ fmor P gs)
    ≈⟨ ∘-cong₂ (≈-sym (assoc _ _ _)) ⟩
      strong-fmor P (λ i → fs i ∘ p₂) ∘ ((pair to-terminal (id _) ∘ strong-fmor P (λ i → gs i ∘ p₂)) ∘ pair to-terminal (id _))
    ≈⟨ ∘-cong₂ (∘-cong₁ (unitor-natural _)) ⟩
      strong-fmor P (λ i → fs i ∘ p₂) ∘ (pair p₁ (strong-fmor P (λ i → gs i ∘ p₂)) ∘ pair to-terminal (id _))
    ≈⟨ ≈-sym (assoc _ _ _) ⟩
      (strong-fmor P (λ i → fs i ∘ p₂) ∘ pair p₁ (strong-fmor P (λ i → gs i ∘ p₂))) ∘ pair to-terminal (id _)
    ≈⟨ ∘-cong₁ (strong-fmor-comp P (λ i → fs i ∘ p₂) (λ i → gs i ∘ p₂)) ⟩
      strong-fmor P (λ i → (fs i ∘ p₂) ∘ pair p₁ (gs i ∘ p₂)) ∘ pair to-terminal (id _)
    ≈⟨ ∘-cong₁ (strong-fmor-cong P (λ i → ≈-trans (assoc _ _ _) (≈-trans (∘-cong₂ (pair-p₂ _ _)) (≈-sym (assoc _ _ _))))) ⟩
      strong-fmor P (λ i → (fs i ∘ gs i) ∘ p₂) ∘ pair to-terminal (id _)
    ∎
    where open ≈-Reasoning isEquiv

  -- The two Mendler steps for μ-obj-resp, instances of μ-map-step at the iso's fwd and bwd legs.
  -- Swapping the iso (Iso-sym) exchanges them: μ-step-fwd (Iso-sym ∘ ι) ≡ μ-step-bwd ι, definitionally.
  μ-step-fwd : ∀ {m n} (P : Poly (suc m)) (δ : Fin m → obj) (Q : Poly (suc n)) (δ' : Fin n → obj) →
               (∀ X → Iso (fobj μ-obj P (extend δ X)) (fobj μ-obj Q (extend δ' X))) →
               ∀ X → (prod witness X ⇒ μ-obj Q δ') → prod witness (fobj μ-obj P (extend δ X)) ⇒ μ-obj Q δ'
  μ-step-fwd P δ Q δ' unfold-iso = μ-map-step P δ Q δ' (λ X → Iso.fwd (unfold-iso X))

  μ-step-bwd : ∀ {m n} (P : Poly (suc m)) (δ : Fin m → obj) (Q : Poly (suc n)) (δ' : Fin n → obj) →
               (∀ X → Iso (fobj μ-obj P (extend δ X)) (fobj μ-obj Q (extend δ' X))) →
               ∀ X → (prod witness X ⇒ μ-obj P δ) → prod witness (fobj μ-obj Q (extend δ' X)) ⇒ μ-obj P δ
  μ-step-bwd P δ Q δ' unfold-iso = μ-map-step Q δ' P δ (λ X → Iso.bwd (unfold-iso X))

  -- fwd ∘ bwd ≈ id for μ-obj-resp below; single proof serves both directions.
  roundtrip-id : ∀ {m n} (P : Poly (suc m)) (δ : Fin m → obj) (Q : Poly (suc n)) (δ' : Fin n → obj)
                 (unfold-iso : ∀ X → Iso (fobj μ-obj P (extend δ X)) (fobj μ-obj Q (extend δ' X)))
                 (unfold-natural-bwd : ∀ {X Y} (f : X ⇒ Y) →
                                       (fmor P (extend-fam f) ∘ Iso.bwd (unfold-iso X)) ≈
                                       (Iso.bwd (unfold-iso Y) ∘ fmor Q (extend-fam f))) →
                 (⦅ μ-step-fwd P δ Q δ' unfold-iso ⦆ᴹ ∘ pair to-terminal (id _))
                 ∘ (⦅ μ-step-bwd P δ Q δ' unfold-iso ⦆ᴹ ∘ pair to-terminal (id _))
                 ≈ id (μ-obj Q δ')
  roundtrip-id P δ Q δ' unfold-iso unfold-natural-bwd =
        let open ≈-Reasoning isEquiv in begin
            fwd ∘ bwd
          ≈⟨ assoc _ _ _ ⟩
            ⦅ step-fwd ⦆ᴹ ∘ (pair to-terminal (id _) ∘ bwd)
          ≈⟨ ∘-cong₂ (≈-sym (assoc _ _ _)) ⟩
            ⦅ step-fwd ⦆ᴹ ∘ ((pair to-terminal (id _) ∘ ⦅ step-bwd ⦆ᴹ) ∘ pair to-terminal (id _))
          ≈⟨ ∘-cong₂ (∘-cong₁ (pair-natural _ _ _)) ⟩
            ⦅ step-fwd ⦆ᴹ ∘ ((pair (to-terminal ∘ ⦅ step-bwd ⦆ᴹ) (id _ ∘ ⦅ step-bwd ⦆ᴹ)) ∘ pair to-terminal (id _))
          ≈⟨ ∘-cong₂ (∘-cong₁ (pair-cong (to-terminal-unique _ _) id-left)) ⟩
            ⦅ step-fwd ⦆ᴹ ∘ ((pair to-terminal ⦅ step-bwd ⦆ᴹ) ∘ pair to-terminal (id _))
          ≈⟨ ∘-cong₂ (pair-natural _ _ _) ⟩
            ⦅ step-fwd ⦆ᴹ ∘ pair (to-terminal ∘ pair to-terminal (id _)) (⦅ step-bwd ⦆ᴹ ∘ pair to-terminal (id _))
          ≈⟨ ∘-cong₂ (pair-cong₁ (≈-trans (to-terminal-unique _ _) (≈-sym (pair-p₁ _ _)))) ⟩
            ⦅ step-fwd ⦆ᴹ ∘ pair (p₁ ∘ pair to-terminal (id _)) (⦅ step-bwd ⦆ᴹ ∘ pair to-terminal (id _))
          ≈⟨ ∘-cong₂ (≈-sym (pair-natural _ _ _)) ⟩
            ⦅ step-fwd ⦆ᴹ ∘ (pair p₁ ⦅ step-bwd ⦆ᴹ ∘ pair to-terminal (id _))
          ≈⟨ ≈-sym (assoc _ _ _) ⟩
            (⦅ step-fwd ⦆ᴹ ∘co ⦅ step-bwd ⦆ᴹ) ∘ pair to-terminal (id _)
          ≈⟨ ∘-cong₁
               (≈-trans (⦅⦆ᴹ-η {P = Q} {δ = δ'} trivial-step (⦅ step-fwd ⦆ᴹ ∘co ⦅ step-bwd ⦆ᴹ) fwd∘bwd-β)
                        (strong-μ-fmor-id Q)) ⟩
            p₂ ∘ pair to-terminal (id _)
          ≈⟨ pair-p₂ _ _ ⟩
            id (μ-obj Q δ')
          ∎
        where
          step-fwd = μ-step-fwd P δ Q δ' unfold-iso
          step-bwd = μ-step-bwd P δ Q δ' unfold-iso
          fwd = ⦅ step-fwd ⦆ᴹ ∘ pair to-terminal (id _)
          bwd = ⦅ step-bwd ⦆ᴹ ∘ pair to-terminal (id _)

          -- The "trivial" Mendler step whose cata is p₂ (by strong-μ-fmor-id).
          trivial-step : ∀ X → (prod witness X ⇒ μ-obj Q δ') →
                         prod witness (fobj μ-obj Q (extend δ' X)) ⇒ μ-obj Q δ'
          trivial-step X x→μ' = α Q δ' ∘ strong-fmor Q (extend-mor (λ _ → p₂) x→μ')

          fwd∘bwd-β :
            ((⦅ step-fwd ⦆ᴹ ∘co ⦅ step-bwd ⦆ᴹ) ∘co (α Q δ' ∘ p₂))
            ≈ trivial-step (μ-obj Q δ') (⦅ step-fwd ⦆ᴹ ∘co ⦅ step-bwd ⦆ᴹ)
          fwd∘bwd-β =
            begin
              (⦅ step-fwd ⦆ᴹ ∘co ⦅ step-bwd ⦆ᴹ) ∘co (α Q δ' ∘ p₂)
            ≈⟨ assoc-co _ _ _ ⟩
              ⦅ step-fwd ⦆ᴹ ∘co (⦅ step-bwd ⦆ᴹ ∘co (α Q δ' ∘ p₂))
            ≈⟨ ∘-cong-co₂ (⦅⦆ᴹ-β {P = Q} {δ = δ'} step-bwd) ⟩
              ⦅ step-fwd ⦆ᴹ
                ∘co (α P δ ∘ fmor P (extend-fam (⦅ step-bwd ⦆ᴹ ∘ pair to-terminal (id _)))
                                    ∘ Iso.bwd (unfold-iso (μ-obj Q δ')) ∘ p₂)
            ≈⟨ ∘-cong-co₂ (assoc _ _ _) ⟩
              ⦅ step-fwd ⦆ᴹ
                ∘co ((α P δ ∘ fmor P (extend-fam (⦅ step-bwd ⦆ᴹ ∘ pair to-terminal (id _))))
                     ∘ (Iso.bwd (unfold-iso (μ-obj Q δ')) ∘ p₂))
            ≈⟨ ∘-cong-co₂ (assoc _ _ _) ⟩
              ⦅ step-fwd ⦆ᴹ
                ∘co (α P δ ∘ (fmor P (extend-fam (⦅ step-bwd ⦆ᴹ ∘ pair to-terminal (id _)))
                              ∘ (Iso.bwd (unfold-iso (μ-obj Q δ')) ∘ p₂)))
            ≈⟨ ∘-cong-co₂ (≈-trans (≈-sym (∘-cong₂ (pair-p₂ _ _))) (≈-sym (assoc _ _ _))) ⟩
              ⦅ step-fwd ⦆ᴹ
                ∘co ((α P δ ∘ p₂)
                     ∘co (fmor P (extend-fam (⦅ step-bwd ⦆ᴹ ∘ pair to-terminal (id _)))
                          ∘ (Iso.bwd (unfold-iso (μ-obj Q δ')) ∘ p₂)))
            ≈⟨ ≈-sym (assoc-co _ _ _) ⟩
              (⦅ step-fwd ⦆ᴹ ∘co (α P δ ∘ p₂))
                ∘co (fmor P (extend-fam (⦅ step-bwd ⦆ᴹ ∘ pair to-terminal (id _)))
                     ∘ (Iso.bwd (unfold-iso (μ-obj Q δ')) ∘ p₂))
            ≈⟨ ∘-cong-co₁ (⦅⦆ᴹ-β {P = P} {δ = δ} step-fwd) ⟩
              step-fwd (μ-obj P δ) ⦅ step-fwd ⦆ᴹ
                ∘co (fmor P (extend-fam (⦅ step-bwd ⦆ᴹ ∘ pair to-terminal (id _)))
                     ∘ (Iso.bwd (unfold-iso (μ-obj Q δ')) ∘ p₂))
            ≈⟨ ∘-cong-co₂ (≈-sym (assoc _ _ _)) ⟩
              step-fwd (μ-obj P δ) ⦅ step-fwd ⦆ᴹ
                ∘co ((fmor P (extend-fam (⦅ step-bwd ⦆ᴹ ∘ pair to-terminal (id _)))
                      ∘ Iso.bwd (unfold-iso (μ-obj Q δ'))) ∘ p₂)
            ≈⟨ ∘-cong-co₂ (∘-cong₁ (unfold-natural-bwd _)) ⟩
              (α Q δ' ∘ fmor Q (extend-fam (⦅ step-fwd ⦆ᴹ ∘ pair to-terminal (id _)))
                      ∘ Iso.fwd (unfold-iso (μ-obj P δ)) ∘ p₂)
                ∘ pair p₁ ((Iso.bwd (unfold-iso (μ-obj P δ))
                            ∘ fmor Q (extend-fam (⦅ step-bwd ⦆ᴹ ∘ pair to-terminal (id _)))) ∘ p₂)
            ≈⟨ assoc _ p₂ _ ⟩
              α Q δ' ∘ fmor Q (extend-fam (⦅ step-fwd ⦆ᴹ ∘ pair to-terminal (id _)))
                     ∘ Iso.fwd (unfold-iso (μ-obj P δ))
                     ∘ (p₂ ∘ pair p₁ ((Iso.bwd (unfold-iso (μ-obj P δ))
                                       ∘ fmor Q (extend-fam (⦅ step-bwd ⦆ᴹ ∘ pair to-terminal (id _)))) ∘ p₂))
            ≈⟨ ∘-cong₂ (pair-p₂ _ _) ⟩
              α Q δ' ∘ fmor Q (extend-fam (⦅ step-fwd ⦆ᴹ ∘ pair to-terminal (id _)))
                     ∘ Iso.fwd (unfold-iso (μ-obj P δ))
                     ∘ ((Iso.bwd (unfold-iso (μ-obj P δ))
                         ∘ fmor Q (extend-fam (⦅ step-bwd ⦆ᴹ ∘ pair to-terminal (id _)))) ∘ p₂)
            ≈⟨ ≈-trans (assoc _ _ _) (assoc _ _ _) ⟩
              α Q δ' ∘ (fmor Q (extend-fam (⦅ step-fwd ⦆ᴹ ∘ pair to-terminal (id _)))
                     ∘ (Iso.fwd (unfold-iso (μ-obj P δ))
                     ∘ ((Iso.bwd (unfold-iso (μ-obj P δ))
                         ∘ fmor Q (extend-fam (⦅ step-bwd ⦆ᴹ ∘ pair to-terminal (id _)))) ∘ p₂)))
            ≈⟨ ∘-cong₂ (∘-cong₂ (≈-trans (∘-cong₂ (assoc _ _ _))
                                  (≈-trans (≈-sym (assoc _ _ _))
                                    (≈-trans (∘-cong₁ (Iso.fwd∘bwd≈id (unfold-iso (μ-obj P δ)))) id-left)))) ⟩
              α Q δ' ∘ (fmor Q (extend-fam (⦅ step-fwd ⦆ᴹ ∘ pair to-terminal (id _)))
                     ∘ (fmor Q (extend-fam (⦅ step-bwd ⦆ᴹ ∘ pair to-terminal (id _))) ∘ p₂))
            ≈⟨ ∘-cong₂ (≈-trans (≈-sym (assoc _ _ _)) (∘-cong₁ (fmor-comp Q _ _))) ⟩
              α Q δ' ∘ (fmor Q (λ i → extend-fam (⦅ step-fwd ⦆ᴹ ∘ pair to-terminal (id _)) i
                                    ∘ extend-fam (⦅ step-bwd ⦆ᴹ ∘ pair to-terminal (id _)) i) ∘ p₂)
            ≈⟨ ∘-cong₂ (≈-trans (fmor-p₂ Q _) (strong-fmor-cong Q last-pointwise)) ⟩
              trivial-step (μ-obj Q δ') (⦅ step-fwd ⦆ᴹ ∘co ⦅ step-bwd ⦆ᴹ)
            ∎
            where
              last-pointwise : ∀ i →
                (extend-fam (⦅ step-fwd ⦆ᴹ ∘ pair to-terminal (id _)) i ∘ extend-fam (⦅ step-bwd ⦆ᴹ ∘ pair to-terminal (id _)) i) ∘ p₂ ≈
                extend-mor (λ _ → p₂) (⦅ step-fwd ⦆ᴹ ∘co ⦅ step-bwd ⦆ᴹ) i
              last-pointwise Fin.zero =
                begin
                  ((⦅ step-fwd ⦆ᴹ ∘ pair to-terminal (id _)) ∘ (⦅ step-bwd ⦆ᴹ ∘ pair to-terminal (id _))) ∘ p₂
                ≈⟨ ∘-cong₁ (unitor-comp ⦅ step-fwd ⦆ᴹ ⦅ step-bwd ⦆ᴹ) ⟩
                  ((⦅ step-fwd ⦆ᴹ ∘ pair p₁ ⦅ step-bwd ⦆ᴹ) ∘ pair to-terminal (id _)) ∘ p₂
                ≈⟨ assoc _ _ _ ⟩
                  (⦅ step-fwd ⦆ᴹ ∘ pair p₁ ⦅ step-bwd ⦆ᴹ) ∘ (pair to-terminal (id _) ∘ p₂)
                ≈⟨ ∘-cong₂ (≈-trans (unitor-natural p₂) pair-ext0) ⟩
                  (⦅ step-fwd ⦆ᴹ ∘ pair p₁ ⦅ step-bwd ⦆ᴹ) ∘ id _
                ≈⟨ id-right ⟩
                  ⦅ step-fwd ⦆ᴹ ∘ pair p₁ ⦅ step-bwd ⦆ᴹ
                ∎ where open ≈-Reasoning isEquiv
              last-pointwise (Fin.suc i) = ≈-trans (∘-cong₁ id-left) id-left
              open ≈-Reasoning isEquiv

  -- Initial algebras of pointwise-isomorphic functors are isomorphic.
  μ-obj-resp : ∀ {m n} {P : Poly (suc m)} {δ : Fin m → obj} {Q : Poly (suc n)} {δ' : Fin n → obj}
               (unfold-iso : ∀ X → Iso (fobj μ-obj P (extend δ X)) (fobj μ-obj Q (extend δ' X))) →
               (unfold-natural : ∀ {X Y} (f : X ⇒ Y) →
                                 (fmor Q (extend-fam f) ∘ Iso.fwd (unfold-iso X)) ≈
                                 (Iso.fwd (unfold-iso Y) ∘ fmor P (extend-fam f))) →
               Iso (μ-obj P δ) (μ-obj Q δ')
  μ-obj-resp {P = P} {δ = δ} {Q = Q} {δ' = δ'} unfold-iso unfold-natural = iso
    where
      unfold-natural-bwd : ∀ {X Y} (f : X ⇒ Y) →
                           (fmor P (extend-fam f) ∘ Iso.bwd (unfold-iso X)) ≈
                           (Iso.bwd (unfold-iso Y) ∘ fmor Q (extend-fam f))
      unfold-natural-bwd {X} {Y} f =
        begin
          fmor P (extend-fam f) ∘ Iso.bwd (unfold-iso X)
        ≈˘⟨ id-left ⟩
          id _ ∘ (fmor P (extend-fam f) ∘ Iso.bwd (unfold-iso X))
        ≈˘⟨ ∘-cong₁ (Iso.bwd∘fwd≈id (unfold-iso Y)) ⟩
          (Iso.bwd (unfold-iso Y) ∘ Iso.fwd (unfold-iso Y)) ∘ (fmor P (extend-fam f) ∘ Iso.bwd (unfold-iso X))
        ≈⟨ assoc _ _ _ ⟩
          Iso.bwd (unfold-iso Y) ∘ (Iso.fwd (unfold-iso Y) ∘ (fmor P (extend-fam f) ∘ Iso.bwd (unfold-iso X)))
        ≈˘⟨ ∘-cong₂ (assoc _ _ _) ⟩
          Iso.bwd (unfold-iso Y) ∘ ((Iso.fwd (unfold-iso Y) ∘ fmor P (extend-fam f)) ∘ Iso.bwd (unfold-iso X))
        ≈˘⟨ ∘-cong₂ (∘-cong₁ (unfold-natural f)) ⟩
          Iso.bwd (unfold-iso Y) ∘ ((fmor Q (extend-fam f) ∘ Iso.fwd (unfold-iso X)) ∘ Iso.bwd (unfold-iso X))
        ≈⟨ ∘-cong₂ (assoc _ _ _) ⟩
          Iso.bwd (unfold-iso Y) ∘ (fmor Q (extend-fam f) ∘ (Iso.fwd (unfold-iso X) ∘ Iso.bwd (unfold-iso X)))
        ≈⟨ ∘-cong₂ (∘-cong₂ (Iso.fwd∘bwd≈id (unfold-iso X))) ⟩
          Iso.bwd (unfold-iso Y) ∘ (fmor Q (extend-fam f) ∘ id _)
        ≈⟨ ∘-cong₂ id-right ⟩
          Iso.bwd (unfold-iso Y) ∘ fmor Q (extend-fam f)
        ∎ where open ≈-Reasoning isEquiv

      iso : Iso (μ-obj P δ) (μ-obj Q δ')
      iso .Iso.fwd = ⦅ μ-step-fwd P δ Q δ' unfold-iso ⦆ᴹ ∘ pair to-terminal (id _)
      iso .Iso.bwd = ⦅ μ-step-bwd P δ Q δ' unfold-iso ⦆ᴹ ∘ pair to-terminal (id _)
      iso .Iso.fwd∘bwd≈id = roundtrip-id P δ Q δ' unfold-iso unfold-natural-bwd
      iso .Iso.bwd∘fwd≈id = roundtrip-id Q δ' P δ (λ X → Iso-sym (unfold-iso X)) unfold-natural
