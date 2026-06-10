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

module polynomial-functor-2 where

data Poly {o m e} (𝒞 : Category o m e) (T : Functor 𝒞 𝒞) (n : ℕ) : Set o where
  const : Category.obj 𝒞 → Poly 𝒞 T n
  var   : Fin n → Poly 𝒞 T n
  _+_   : Poly 𝒞 T n → Poly 𝒞 T n → Poly 𝒞 T n
  _×_   : Poly 𝒞 T n → Poly 𝒞 T n → Poly 𝒞 T n
  μ     : Poly 𝒞 T (suc n) → Poly 𝒞 T n
  T∘_   : Poly 𝒞 T n → Poly 𝒞 T n

module Interp {o m e} {𝒞 : Category o m e}
              (𝒞T : HasTerminal 𝒞) (𝒞P : HasProducts 𝒞) (𝒞SCP : HasStrongCoproducts 𝒞 𝒞P)
              (T-strong : StrongFunctor 𝒞P) where
  open Category 𝒞
  open HasProducts 𝒞P
  open HasCoproducts (strong-coproducts→coproducts 𝒞T 𝒞SCP)
  open HasStrongCoproducts 𝒞SCP using () renaming (copair to scopair)
  open StrongFunctor T-strong using (right-strength) renaming (F to T)

  extend : ∀ {n} → (Fin n → obj) → obj → Fin (suc n) → obj
  extend δ A Fin.zero    = A
  extend δ A (Fin.suc i) = δ i

  fobj : ∀ {n} → (μ-obj : ∀ {m} → Poly 𝒞 T (suc m) → (Fin m → obj) → obj) → Poly 𝒞 T n → (Fin n → obj) → obj
  fobj μ-obj (const A) δ = A
  fobj μ-obj (var i)   δ = δ i
  fobj μ-obj (P + Q)   δ = coprod (fobj μ-obj P δ) (fobj μ-obj Q δ)
  fobj μ-obj (P × Q)   δ = prod (fobj μ-obj P δ) (fobj μ-obj Q δ)
  fobj μ-obj (μ P)     δ = μ-obj P δ
  fobj μ-obj (T∘ P)    δ = Functor.fobj T (fobj μ-obj P δ)

  module Functorial
    (μ-obj       : ∀ {m} → Poly 𝒞 T (suc m) → (Fin m → obj) → obj)
    (μ-fmor      : ∀ {m} (P : Poly 𝒞 T (suc m)) {δ δ' : Fin m → obj} →
                   (∀ i → δ i ⇒ δ' i) → μ-obj P δ ⇒ μ-obj P δ')
    (μ-fmor-cong : ∀ {m} (P : Poly 𝒞 T (suc m)) {δ δ' : Fin m → obj}
                   {fs gs : ∀ i → δ i ⇒ δ' i} →
                   (∀ i → fs i ≈ gs i) → μ-fmor P fs ≈ μ-fmor P gs)
    (μ-fmor-id   : ∀ {m} (P : Poly 𝒞 T (suc m)) {δ : Fin m → obj} →
                   μ-fmor P (λ i → id (δ i)) ≈ id (μ-obj P δ))
    (μ-fmor-comp : ∀ {m} (P : Poly 𝒞 T (suc m)) {δ δ' δ'' : Fin m → obj}
                   (fs : ∀ i → δ' i ⇒ δ'' i) (gs : ∀ i → δ i ⇒ δ' i) →
                   μ-fmor P (λ i → fs i ∘ gs i) ≈ (μ-fmor P fs ∘ μ-fmor P gs))
    where

    fmor : ∀ {n} (P : Poly 𝒞 T n) {δ δ' : Fin n → obj} →
           (∀ i → δ i ⇒ δ' i) → fobj μ-obj P δ ⇒ fobj μ-obj P δ'
    fmor (const A) fs = id A
    fmor (var i)   fs = fs i
    fmor (P + Q)   fs = coprod-m (fmor P fs) (fmor Q fs)
    fmor (P × Q)   fs = prod-m   (fmor P fs) (fmor Q fs)
    fmor (μ P)     fs = μ-fmor P fs
    fmor (T∘ P)    fs = Functor.fmor T (fmor P fs)

    fmor-cong : ∀ {n} (P : Poly 𝒞 T n) {δ δ' : Fin n → obj} {fs gs : ∀ i → δ i ⇒ δ' i} →
                (∀ i → fs i ≈ gs i) → fmor P fs ≈ fmor P gs
    fmor-cong (const A) fs≈gs = ≈-refl
    fmor-cong (var i)   fs≈gs = fs≈gs i
    fmor-cong (P + Q)   fs≈gs = coprod-m-cong (fmor-cong P fs≈gs) (fmor-cong Q fs≈gs)
    fmor-cong (P × Q)   fs≈gs = prod-m-cong   (fmor-cong P fs≈gs) (fmor-cong Q fs≈gs)
    fmor-cong (μ P)     fs≈gs = μ-fmor-cong P fs≈gs
    fmor-cong (T∘ P)    fs≈gs = Functor.fmor-cong T (fmor-cong P fs≈gs)

    fmor-id : ∀ {n} (P : Poly 𝒞 T n) {δ : Fin n → obj} →
              fmor P (λ i → id (δ i)) ≈ id (fobj μ-obj P δ)
    fmor-id (const A) = ≈-refl
    fmor-id (var i)   = ≈-refl
    fmor-id (P + Q)   = ≈-trans (coprod-m-cong (fmor-id P) (fmor-id Q)) coprod-m-id
    fmor-id (P × Q)   = ≈-trans (prod-m-cong   (fmor-id P) (fmor-id Q)) prod-m-id
    fmor-id (μ P)     = μ-fmor-id P
    fmor-id (T∘ P)    = ≈-trans (Functor.fmor-cong T (fmor-id P)) (Functor.fmor-id T)

    fmor-comp : ∀ {n} (P : Poly 𝒞 T n) {δ δ' δ'' : Fin n → obj}
                (fs : ∀ i → δ' i ⇒ δ'' i) (gs : ∀ i → δ i ⇒ δ' i) →
                fmor P (λ i → fs i ∘ gs i) ≈ (fmor P fs ∘ fmor P gs)
    fmor-comp (const A) fs gs = ≈-sym id-left
    fmor-comp (var i)   fs gs = ≈-refl
    fmor-comp (P + Q)   fs gs = ≈-trans (coprod-m-cong (fmor-comp P fs gs) (fmor-comp Q fs gs))
                                        (coprod-m-comp _ _ _ _)
    fmor-comp (P × Q)   fs gs = ≈-trans (prod-m-cong   (fmor-comp P fs gs) (fmor-comp Q fs gs))
                                        (pair-functorial _ _ _ _)
    fmor-comp (μ P)     fs gs = μ-fmor-comp P fs gs
    fmor-comp (T∘ P)    fs gs = ≈-trans (Functor.fmor-cong T (fmor-comp P fs gs))
                                        (Functor.fmor-comp T _ _)

    functor : ∀ {n} → Poly 𝒞 T n → Functor (𝒞 ^ n) 𝒞
    functor P .Functor.fobj      δ     = fobj μ-obj P δ
    functor P .Functor.fmor      fs    = fmor P fs
    functor P .Functor.fmor-cong fs≈gs = fmor-cong P fs≈gs
    functor P .Functor.fmor-id         = fmor-id P
    functor P .Functor.fmor-comp fs gs = fmor-comp P fs gs

  record HasMu : Set (o ⊔ m) where
    -- Recursion needs to be "open" to avoid circularity with Poly's functor instance.
    field
      μ-obj : ∀ {n} → Poly 𝒞 T (suc n) → (Fin n → obj) → obj
      α   : ∀ {n} (P : Poly 𝒞 T (suc n)) (δ : Fin n → obj) →
            fobj μ-obj P (extend δ (μ-obj P δ)) ⇒ μ-obj P δ
      ⦅_⦆   : ∀ {n Γ A} {P : Poly 𝒞 T (suc n)} {δ : Fin n → obj} →
             (prod Γ (fobj μ-obj P (extend δ A)) ⇒ A) → prod Γ (μ-obj P δ) ⇒ A
      mcata : ∀ {n Γ A} {P : Poly 𝒞 T (suc n)} {δ : Fin n → obj} →
              (∀ X → (prod Γ X ⇒ A) → (prod Γ (fobj μ-obj P (extend δ X)) ⇒ A)) →
              prod Γ (μ-obj P δ) ⇒ A

  module Derived (Mu : HasMu) where
    open HasMu Mu
    open HasTerminal 𝒞T using (witness; to-terminal)

    extend-mor : ∀ {n} {δ δ' : Fin n → obj} {X Y} →
                 (∀ i → δ i ⇒ δ' i) → (X ⇒ Y) → ∀ i → extend δ X i ⇒ extend δ' Y i
    extend-mor fs x→y Fin.zero    = x→y
    extend-mor fs x→y (Fin.suc i) = fs i

    mutual
      fmor : ∀ {n} (P : Poly 𝒞 T n) {δ δ' : Fin n → obj} →
             (∀ i → δ i ⇒ δ' i) → fobj μ-obj P δ ⇒ fobj μ-obj P δ'
      fmor (const A) fs = id A
      fmor (var i)   fs = fs i
      fmor (P + Q)   fs = coprod-m (fmor P fs) (fmor Q fs)
      fmor (P × Q)   fs = prod-m   (fmor P fs) (fmor Q fs)
      fmor (μ P)     fs = μ-fmor P fs
      fmor (T∘ P)    fs = Functor.fmor T (fmor P fs)

      μ-fmor : ∀ {n} (P : Poly 𝒞 T (suc n)) {δ δ' : Fin n → obj} → (∀ i → δ i ⇒ δ' i) → μ-obj P δ ⇒ μ-obj P δ'
      μ-fmor P {δ} {δ'} fs =
        mcata {Γ = witness} step ∘ pair to-terminal (id _)
        where
          step : ∀ X → (prod witness X ⇒ μ-obj P δ') → prod witness (fobj μ-obj P (extend δ X)) ⇒ μ-obj P δ'
          step X x→A = α P δ' ∘ fmor P (extend-mor fs (x→A ∘ pair to-terminal (id _))) ∘ p₂

    extend-mor-strong : ∀ {n Γ} {δ δ' : Fin n → obj} {X Y} →
                        (∀ i → prod Γ (δ i) ⇒ δ' i) → (prod Γ X ⇒ Y) →
                        ∀ i → prod Γ (extend δ X i) ⇒ extend δ' Y i
    extend-mor-strong fs x→y Fin.zero    = x→y
    extend-mor-strong fs x→y (Fin.suc i) = fs i

    mutual
      strong-fmor : ∀ {n Γ} (P : Poly 𝒞 T n) {δ δ' : Fin n → obj} →
                    (∀ i → prod Γ (δ i) ⇒ δ' i) → prod Γ (fobj μ-obj P δ) ⇒ fobj μ-obj P δ'
      strong-fmor (const A) fs = p₂
      strong-fmor (var i)   fs = fs i
      strong-fmor (P + Q)   fs = scopair (in₁ ∘ strong-fmor P fs) (in₂ ∘ strong-fmor Q fs)
      strong-fmor (P × Q)   fs = pair (strong-fmor P fs ∘ pair p₁ (p₁ ∘ p₂))
                                      (strong-fmor Q fs ∘ pair p₁ (p₂ ∘ p₂))
      strong-fmor (μ P)     fs = strong-μ-fmor P fs
      strong-fmor (T∘ P)    fs = Functor.fmor T (strong-fmor P fs) ∘ right-strength

      strong-μ-fmor : ∀ {n Γ} (P : Poly 𝒞 T (suc n)) {δ δ' : Fin n → obj} →
                      (∀ i → prod Γ (δ i) ⇒ δ' i) → prod Γ (μ-obj P δ) ⇒ μ-obj P δ'
      strong-μ-fmor P {δ} {δ'} fs = mcata step
        where
          step : ∀ X → (prod _ X ⇒ μ-obj P δ') → prod _ (fobj μ-obj P (extend δ X)) ⇒ μ-obj P δ'
          step X x→μ' = α P δ' ∘ strong-fmor P (extend-mor-strong fs x→μ')
