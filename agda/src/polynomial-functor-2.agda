{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
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
  extend val A fzero    = A
  extend val A (fsuc i) = val i

  fobj : ∀ {n} → (μh : ∀ {m} → Poly 𝒞 (suc m) → (Fin m → obj) → obj)
       → Poly 𝒞 n → (Fin n → obj) → obj
  fobj μh (const A) val = A
  fobj μh (var i)   val = val i
  fobj μh (P + Q)   val = coprod (fobj μh P val) (fobj μh Q val)
  fobj μh (P × Q)   val = prod   (fobj μh P val) (fobj μh Q val)
  fobj μh (μ P)     val = μh P val

  record HasMu : Set (o ⊔ m) where
    field
      μ-poly : ∀ {n} → Poly 𝒞 (suc n) → (Fin n → obj) → obj
      in-alg : ∀ {n} (P : Poly 𝒞 (suc n)) (val : Fin n → obj)
             → fobj μ-poly P (extend val (μ-poly P val)) ⇒ μ-poly P val
      cata   : ∀ {n Γ y} (P : Poly 𝒞 (suc n)) (val : Fin n → obj)
             → (prod Γ (fobj μ-poly P (extend val y)) ⇒ y)
             → prod Γ (μ-poly P val) ⇒ y
