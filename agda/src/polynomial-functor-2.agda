{-# OPTIONS --prop --postfix-projections --safe #-}

import Data.Fin as Fin
open Fin using (Fin)
open import Data.Nat using (ℕ; zero; suc)
open import Level using (_⊔_)
open import categories
  using (Category; HasTerminal; HasProducts; HasCoproducts; HasStrongCoproducts;
         strong-coproducts→coproducts)
open import functor using (Functor)

module polynomial-functor-2 where

data Poly {o m e} (𝒞 : Category o m e) (T : Functor 𝒞 𝒞) (n : ℕ) : Set o where
  const : Category.obj 𝒞 → Poly 𝒞 T n
  var   : Fin n → Poly 𝒞 T n
  _+_   : Poly 𝒞 T n → Poly 𝒞 T n → Poly 𝒞 T n
  _×_   : Poly 𝒞 T n → Poly 𝒞 T n → Poly 𝒞 T n
  μ     : Poly 𝒞 T (suc n) → Poly 𝒞 T n
  T∘_   : Poly 𝒞 T n → Poly 𝒞 T n

module Interp {o m e} {𝒞 : Category o m e} {T : Functor 𝒞 𝒞}
              (𝒞T : HasTerminal 𝒞) (𝒞P : HasProducts 𝒞) (𝒞SCP : HasStrongCoproducts 𝒞 𝒞P) where
  open Category 𝒞
  open HasProducts 𝒞P
  open HasCoproducts (strong-coproducts→coproducts 𝒞T 𝒞SCP)

  extend : ∀ {n} → (Fin n → obj) → obj → Fin (suc n) → obj
  extend δ A Fin.zero    = A
  extend δ A (Fin.suc i) = δ i

  fobj : ∀ {n} → (μh : ∀ {m} → Poly 𝒞 T (suc m) → (Fin m → obj) → obj) → Poly 𝒞 T n → (Fin n → obj) → obj
  fobj μh (const A) δ = A
  fobj μh (var i)   δ = δ i
  fobj μh (P + Q)   δ = coprod (fobj μh P δ) (fobj μh Q δ)
  fobj μh (P × Q)   δ = prod (fobj μh P δ) (fobj μh Q δ)
  fobj μh (μ P)     δ = μh P δ
  fobj μh (T∘_ P)   δ = Functor.fobj T (fobj μh P δ)

  module Functorial
    (μh           : ∀ {m} → Poly 𝒞 T (suc m) → (Fin m → obj) → obj)
    (μh-fmor      : ∀ {m} (P : Poly 𝒞 T (suc m)) {δ δ' : Fin m → obj} →
                    (∀ i → δ i ⇒ δ' i) → μh P δ ⇒ μh P δ')
    (μh-fmor-cong : ∀ {m} (P : Poly 𝒞 T (suc m)) {δ δ' : Fin m → obj}
                    {fs gs : ∀ i → δ i ⇒ δ' i} →
                    (∀ i → fs i ≈ gs i) → μh-fmor P fs ≈ μh-fmor P gs)
    where

    fmor : ∀ {n} (P : Poly 𝒞 T n) {δ δ' : Fin n → obj} →
           (∀ i → δ i ⇒ δ' i) → fobj μh P δ ⇒ fobj μh P δ'
    fmor (const A) fs = id A
    fmor (var i)   fs = fs i
    fmor (P + Q)   fs = coprod-m (fmor P fs) (fmor Q fs)
    fmor (P × Q)   fs = prod-m   (fmor P fs) (fmor Q fs)
    fmor (μ P)     fs = μh-fmor P fs
    fmor (T∘_ P)   fs = Functor.fmor T (fmor P fs)

    fmor-cong : ∀ {n} (P : Poly 𝒞 T n) {δ δ' : Fin n → obj} {fs gs : ∀ i → δ i ⇒ δ' i} →
                (∀ i → fs i ≈ gs i) → fmor P fs ≈ fmor P gs
    fmor-cong (const A) fs≈gs = ≈-refl
    fmor-cong (var i)   fs≈gs = fs≈gs i
    fmor-cong (P + Q)   fs≈gs = coprod-m-cong (fmor-cong P fs≈gs) (fmor-cong Q fs≈gs)
    fmor-cong (P × Q)   fs≈gs = prod-m-cong   (fmor-cong P fs≈gs) (fmor-cong Q fs≈gs)
    fmor-cong (μ P)     fs≈gs = μh-fmor-cong P fs≈gs
    fmor-cong (T∘_ P)   fs≈gs = Functor.fmor-cong T (fmor-cong P fs≈gs)

  record HasMu : Set (o ⊔ m) where
    field
      μ-obj : ∀ {n} → Poly 𝒞 T (suc n) → (Fin n → obj) → obj
      inF   : ∀ {n} (P : Poly 𝒞 T (suc n)) (δ : Fin n → obj) →
              fobj μ-obj P (extend δ (μ-obj P δ)) ⇒ μ-obj P δ
      ⦅_⦆   : ∀ {n Γ y} {P : Poly 𝒞 T (suc n)} {δ : Fin n → obj} →
             (prod Γ (fobj μ-obj P (extend δ y)) ⇒ y) → prod Γ (μ-obj P δ) ⇒ y
