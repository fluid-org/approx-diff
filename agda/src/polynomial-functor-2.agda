{-# OPTIONS --prop --postfix-projections --safe #-}

import Data.Fin as Fin
open Fin using (Fin)
open import Data.Nat using (ℕ; zero; suc)
open import Level using (_⊔_)
open import categories
  using (Category; HasTerminal; HasProducts; HasCoproducts; HasStrongCoproducts;
         strong-coproducts→coproducts)

module polynomial-functor-2 where

data Poly {o m e} (𝒞 : Category o m e) (n : ℕ) : Set o where
  const : Category.obj 𝒞 → Poly 𝒞 n
  var   : Fin n → Poly 𝒞 n
  _+_   : Poly 𝒞 n → Poly 𝒞 n → Poly 𝒞 n
  _×_   : Poly 𝒞 n → Poly 𝒞 n → Poly 𝒞 n
  μ     : Poly 𝒞 (suc n) → Poly 𝒞 n

module Interp {o m e} {𝒞 : Category o m e}
              (𝒞T : HasTerminal 𝒞) (𝒞P : HasProducts 𝒞) (𝒞SCP : HasStrongCoproducts 𝒞 𝒞P) where
  open Category 𝒞
  open HasProducts 𝒞P
  open HasCoproducts (strong-coproducts→coproducts 𝒞T 𝒞SCP)

  extend : ∀ {n} → (Fin n → obj) → obj → Fin (suc n) → obj
  extend val A Fin.zero    = A
  extend val A (Fin.suc i) = val i

  fobj : ∀ {n} → (μh : ∀ {m} → Poly 𝒞 (suc m) → (Fin m → obj) → obj) → Poly 𝒞 n → (Fin n → obj) → obj
  fobj μh (const A) val = A
  fobj μh (var i)   val = val i
  fobj μh (P + Q)   val = coprod (fobj μh P val) (fobj μh Q val)
  fobj μh (P × Q)   val = prod   (fobj μh P val) (fobj μh Q val)
  fobj μh (μ P)     val = μh P val

  record HasMu : Set (o ⊔ m) where
    field
      μ-obj : ∀ {n} → Poly 𝒞 (suc n) → (Fin n → obj) → obj
      inF   : ∀ {n} (P : Poly 𝒞 (suc n)) (val : Fin n → obj) →
              fobj μ-obj P (extend val (μ-obj P val)) ⇒ μ-obj P val
      ⦅_⦆   : ∀ {n Γ y} {P : Poly 𝒞 (suc n)} {val : Fin n → obj} →
             (prod Γ (fobj μ-obj P (extend val y)) ⇒ y) → prod Γ (μ-obj P val) ⇒ y
