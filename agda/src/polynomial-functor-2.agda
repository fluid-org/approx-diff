{-# OPTIONS --prop --postfix-projections --safe #-}

import Data.Fin as Fin
open Fin using (Fin)
open import Data.Nat using (ℕ; zero; suc)
open import Level using (_⊔_)
open import categories
  using (Category; HasTerminal; HasProducts; HasCoproducts; HasStrongCoproducts;
         strong-coproducts→coproducts)
open import functor using (Functor; StrongFunctor)
open import product-category using (_^_)

module polynomial-functor-2
  {o m e} {𝒞 : Category o m e}
  (𝒞T : HasTerminal 𝒞) (𝒞P : HasProducts 𝒞) (𝒞SCP : HasStrongCoproducts 𝒞 𝒞P)
  (T-strong : StrongFunctor 𝒞P) where

open Category 𝒞
open HasProducts 𝒞P
open HasCoproducts (strong-coproducts→coproducts 𝒞T 𝒞SCP)
open HasStrongCoproducts 𝒞SCP using () renaming (copair to scopair)
open StrongFunctor T-strong using (right-strength) renaming (F to T)

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

record HasMu : Set (o ⊔ m) where
  -- Recursion needs to be "open" to avoid circularity with Poly's functor instance.
  field
    μ-obj : ∀ {n} → Poly (suc n) → (Fin n → obj) → obj
    α     : ∀ {n} (P : Poly (suc n)) (δ : Fin n → obj) →
            fobj μ-obj P (extend δ (μ-obj P δ)) ⇒ μ-obj P δ
    mcata : ∀ {n Γ A} {P : Poly (suc n)} {δ : Fin n → obj} →
            (∀ X → (prod Γ X ⇒ A) → (prod Γ (fobj μ-obj P (extend δ X)) ⇒ A)) →
            prod Γ (μ-obj P δ) ⇒ A

  open HasTerminal 𝒞T using (witness; to-terminal)

  extend-mor : ∀ {n Γ} {δ δ' : Fin n → obj} {X Y} →
               (∀ i → prod Γ (δ i) ⇒ δ' i) → (prod Γ X ⇒ Y) →
               ∀ i → prod Γ (extend δ X i) ⇒ extend δ' Y i
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
    strong-fmor (T∘ P)    fs = Functor.fmor T (strong-fmor P fs) ∘ right-strength

    strong-μ-fmor : ∀ {n Γ} (P : Poly (suc n)) {δ δ' : Fin n → obj} →
                    (∀ i → prod Γ (δ i) ⇒ δ' i) → prod Γ (μ-obj P δ) ⇒ μ-obj P δ'
    strong-μ-fmor P {δ} {δ'} fs = mcata step
      where
        step : ∀ X → (prod _ X ⇒ μ-obj P δ') → prod _ (fobj μ-obj P (extend δ X)) ⇒ μ-obj P δ'
        step X x→μ' = α P δ' ∘ strong-fmor P (extend-mor fs x→μ')

  fmor : ∀ {n} (P : Poly n) {δ δ' : Fin n → obj} → (∀ i → δ i ⇒ δ' i) → fobj μ-obj P δ ⇒ fobj μ-obj P δ'
  fmor P fs = strong-fmor P (λ i → fs i ∘ p₂) ∘ pair to-terminal (id _)

  μ-fmor : ∀ {n} (P : Poly (suc n)) {δ δ' : Fin n → obj} → (∀ i → δ i ⇒ δ' i) → μ-obj P δ ⇒ μ-obj P δ'
  μ-fmor P fs = strong-μ-fmor P (λ i → fs i ∘ p₂) ∘ pair to-terminal (id _)

  ⦅_⦆ : ∀ {n Γ A} {P : Poly (suc n)} {δ : Fin n → obj} →
        (prod Γ (fobj μ-obj P (extend δ A)) ⇒ A) → prod Γ (μ-obj P δ) ⇒ A
  ⦅_⦆ {Γ = Γ} {A = A} {P = P} {δ = δ} alg = mcata step
    where
      step : ∀ X → (prod Γ X ⇒ A) → prod Γ (fobj μ-obj P (extend δ X)) ⇒ A
      step X x→A = alg ∘ pair p₁ (strong-fmor P (extend-mor (λ _ → p₂) x→A))
