{-# OPTIONS --prop --postfix-projections --safe #-}

import Data.Fin as Fin
open Fin using (Fin)
open import Data.Nat using (ℕ; suc)
open import Level using (_⊔_)
open import categories using (Category; HasProducts; HasStrongCoproducts)
open import functor using (Functor)

module polynomial-functor where

data Poly {o m e} (𝒞 : Category o m e) (n : ℕ) : Set o where
  const : Category.obj 𝒞 → Poly 𝒞 n
  var   : Fin n → Poly 𝒞 n
  _+_   : Poly 𝒞 n → Poly 𝒞 n → Poly 𝒞 n
  _×_   : Poly 𝒞 n → Poly 𝒞 n → Poly 𝒞 n
  μ     : Poly 𝒞 (suc n) → Poly 𝒞 n

extend : ∀ {n} {ℓ} {A : Set ℓ} → (Fin n → A) → A → Fin (suc n) → A
extend δ x Fin.zero    = x
extend δ x (Fin.suc i) = δ i

-- Interpretation of the polynomials with an endofunctor, strong for the products, applied at every
-- sum and product; initial algebras for the μ-polynomials, with the catamorphism in context.
module Interp
  {o m e} {𝒞 : Category o m e} (𝒞P : HasProducts 𝒞) (𝒞SC : HasStrongCoproducts 𝒞 𝒞P)
  (L : Category.obj 𝒞 → Category.obj 𝒞)
  (under : ∀ {Γ X Y} → Category._⇒_ 𝒞 (HasProducts.prod 𝒞P Γ X) Y →
                       Category._⇒_ 𝒞 (HasProducts.prod 𝒞P Γ (L X)) (L Y))
  where

  open Category 𝒞
  open HasProducts 𝒞P
  open HasStrongCoproducts 𝒞SC

  fobj : (μ-obj : ∀ {k} → Poly 𝒞 (suc k) → (Fin k → obj) → obj) → ∀ {n} → Poly 𝒞 n → (Fin n → obj) → obj
  fobj μ-obj (const A) δ = A
  fobj μ-obj (var i)   δ = δ i
  fobj μ-obj (P + Q)   δ = coprod (L (fobj μ-obj P δ)) (L (fobj μ-obj Q δ))
  fobj μ-obj (P × Q)   δ = L (prod (fobj μ-obj P δ) (fobj μ-obj Q δ))
  fobj μ-obj (μ P)     δ = μ-obj P δ

  record HasMu : Set (o ⊔ m ⊔ e) where
    field
      μ-obj : ∀ {k} → Poly 𝒞 (suc k) → (Fin k → obj) → obj
      inMap : ∀ {k} (P : Poly 𝒞 (suc k)) (δ : Fin k → obj) → fobj μ-obj P (extend δ (μ-obj P δ)) ⇒ μ-obj P δ
      ⦅_⦆   : ∀ {k} {Γ A : obj} {P : Poly 𝒞 (suc k)} {δ : Fin k → obj} →
              prod Γ (fobj μ-obj P (extend δ A)) ⇒ A → prod Γ (μ-obj P δ) ⇒ A

    strong-extend-mor : ∀ {k} {Γ : obj} {δ δ' : Fin k → obj} {X Y : obj} →
                        (∀ i → prod Γ (δ i) ⇒ δ' i) → prod Γ X ⇒ Y →
                        ∀ i → prod Γ (extend δ X i) ⇒ extend δ' Y i
    strong-extend-mor fs xy Fin.zero    = xy
    strong-extend-mor fs xy (Fin.suc i) = fs i

    mutual
      strong-fmor : ∀ {k} {Γ : obj} (P : Poly 𝒞 k) {δ δ' : Fin k → obj} →
                    (∀ i → prod Γ (δ i) ⇒ δ' i) → prod Γ (fobj μ-obj P δ) ⇒ fobj μ-obj P δ'
      strong-fmor (const A) fs = p₂
      strong-fmor (var i)   fs = fs i
      strong-fmor (P + Q)   fs = copair (in₁ ∘ under (strong-fmor P fs)) (in₂ ∘ under (strong-fmor Q fs))
      strong-fmor (P × Q)   fs = under (strong-prod-m (strong-fmor P fs) (strong-fmor Q fs))
      strong-fmor (μ P)     fs = strong-μ-fmor P fs

      strong-μ-fmor : ∀ {k} {Γ : obj} (P : Poly 𝒞 (suc k)) {δ δ' : Fin k → obj} →
                      (∀ i → prod Γ (δ i) ⇒ δ' i) → prod Γ (μ-obj P δ) ⇒ μ-obj P δ'
      strong-μ-fmor P {δ} {δ'} fs = ⦅ inMap P δ' ∘ strong-fmor P (strong-extend-mor fs p₂) ⦆

  infixl 21 _∘co_
  _∘co_ : ∀ {Γ X Y Z} → prod Γ Y ⇒ Z → prod Γ X ⇒ Y → prod Γ X ⇒ Z
  f ∘co g = f ∘ pair p₁ g

  record HasMuLaws (Mu : HasMu) : Set (o ⊔ m ⊔ e) where
    open HasMu Mu
    field
      ⦅⦆-β : ∀ {k} {Γ A : obj} {P : Poly 𝒞 (suc k)} {δ : Fin k → obj}
             (alg : prod Γ (fobj μ-obj P (extend δ A)) ⇒ A) →
             (⦅ alg ⦆ ∘co (inMap P δ ∘ p₂)) ≈ (alg ∘co strong-fmor P (strong-extend-mor (λ i → p₂) ⦅ alg ⦆))
      ⦅⦆-η : ∀ {k} {Γ A : obj} {P : Poly 𝒞 (suc k)} {δ : Fin k → obj}
             (alg : prod Γ (fobj μ-obj P (extend δ A)) ⇒ A) (h : prod Γ (μ-obj P δ) ⇒ A) →
             (h ∘co (inMap P δ ∘ p₂)) ≈ (alg ∘co strong-fmor P (strong-extend-mor (λ i → p₂) h)) → h ≈ ⦅ alg ⦆

-- Action of a functor on polynomials: apply the functor at the const leaves.
Poly-map : ∀ {o₁ m₁ e₁ o₂ m₂ e₂} {𝒞 : Category o₁ m₁ e₁} {𝒟 : Category o₂ m₂ e₂} →
           Functor 𝒞 𝒟 → ∀ {n} → Poly 𝒞 n → Poly 𝒟 n
Poly-map F (const A) = const (F .Functor.fobj A)
Poly-map F (var i)   = var i
Poly-map F (P + Q)   = Poly-map F P + Poly-map F Q
Poly-map F (P × Q)   = Poly-map F P × Poly-map F Q
Poly-map F (μ P)     = μ (Poly-map F P)

