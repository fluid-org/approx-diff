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

  fmor : ∀ {n}
         (μh      : ∀ {m} → Poly 𝒞 T (suc m) → (Fin m → obj) → obj)
         (μh-fmor : ∀ {m} (P : Poly 𝒞 T (suc m)) {δ δ' : Fin m → obj} →
                    (∀ i → δ i ⇒ δ' i) → μh P δ ⇒ μh P δ')
         (P : Poly 𝒞 T n) {δ δ' : Fin n → obj} →
         (∀ i → δ i ⇒ δ' i) → fobj μh P δ ⇒ fobj μh P δ'
  fmor μh μh-fmor (const A) fs = id A
  fmor μh μh-fmor (var i)   fs = fs i
  fmor μh μh-fmor (P + Q)   fs = coprod-m (fmor μh μh-fmor P fs) (fmor μh μh-fmor Q fs)
  fmor μh μh-fmor (P × Q)   fs = prod-m (fmor μh μh-fmor P fs) (fmor μh μh-fmor Q fs)
  fmor μh μh-fmor (μ P)     fs = μh-fmor P fs
  fmor μh μh-fmor (T∘_ P)   fs = Functor.fmor T (fmor μh μh-fmor P fs)

  record HasMu : Set (o ⊔ m) where
    field
      μ-obj : ∀ {n} → Poly 𝒞 T (suc n) → (Fin n → obj) → obj
      inF   : ∀ {n} (P : Poly 𝒞 T (suc n)) (δ : Fin n → obj) →
              fobj μ-obj P (extend δ (μ-obj P δ)) ⇒ μ-obj P δ
      ⦅_⦆   : ∀ {n Γ y} {P : Poly 𝒞 T (suc n)} {δ : Fin n → obj} →
             (prod Γ (fobj μ-obj P (extend δ y)) ⇒ y) → prod Γ (μ-obj P δ) ⇒ y
