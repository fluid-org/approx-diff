{-# OPTIONS --prop --postfix-projections --safe #-}

import Data.Fin as Fin
open Fin using (Fin)
open import Data.Nat using (ℕ; suc)
open import Level using (_⊔_)
open import categories
  using (Category; HasTerminal; HasProducts; HasCoproducts; HasStrongCoproducts;
         strong-coproducts→coproducts; coKleisli-prod)
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

-- Interpretation of the polynomials in a category with terminal object, products and strong coproducts.
module Interp
  {o m e} {𝒞 : Category o m e}
  (𝒞T : HasTerminal 𝒞) (𝒞P : HasProducts 𝒞) (𝒞SCP : HasStrongCoproducts 𝒞 𝒞P)
  where

  open Category 𝒞
  open HasProducts 𝒞P
  open HasCoproducts (strong-coproducts→coproducts 𝒞T 𝒞SCP)
  open HasStrongCoproducts 𝒞SCP using () renaming (copair to scopair)

  -- co-Kleisli notation: a morphism f : prod Γ X ⇒ Y lives in the co-Kleisli category for prod Γ -.
  infixl 21 _∘co_
  _∘co_ : ∀ {Γ X Y Z} → (prod Γ Y ⇒ Z) → (prod Γ X ⇒ Y) → (prod Γ X ⇒ Z)
  _∘co_ {Γ} = Category._∘_ (coKleisli-prod 𝒞P Γ)

  fobj : ∀ {n} → (μ-obj : ∀ {m} → Poly 𝒞 (suc m) → (Fin m → obj) → obj) → Poly 𝒞 n → (Fin n → obj) → obj
  fobj μ-obj (const A) δ = A
  fobj μ-obj (var i)   δ = δ i
  fobj μ-obj (P + Q)   δ = coprod (fobj μ-obj P δ) (fobj μ-obj Q δ)
  fobj μ-obj (P × Q)   δ = prod (fobj μ-obj P δ) (fobj μ-obj Q δ)
  fobj μ-obj (μ P)     δ = μ-obj P δ

  -- Parameterised initial algebras for the polynomials: carrier, algebra map and catamorphism, as
  -- operations only. The catamorphism is in context Γ (the open form avoids closure conversion, hence
  -- exponentials). The β/η laws live in HasMuLaws below, stated via the strong functorial action
  -- strong-fmor, which is defined from these operations; making the laws fields here would be circular.
  record HasMu : Set (o ⊔ m ⊔ e) where
    field
      μ-obj : ∀ {n} → Poly 𝒞 (suc n) → (Fin n → obj) → obj
      inMap     : ∀ {n} (P : Poly 𝒞 (suc n)) (δ : Fin n → obj) → fobj μ-obj P (extend δ (μ-obj P δ)) ⇒ μ-obj P δ
      ⦅_⦆  : ∀ {n Γ A} {P : Poly 𝒞 (suc n)} {δ : Fin n → obj} →
             (prod Γ (fobj μ-obj P (extend δ A)) ⇒ A) → prod Γ (μ-obj P δ) ⇒ A

    open HasTerminal 𝒞T using (witness; to-terminal; to-terminal-unique)

    strong-extend-mor : ∀ {n Γ} {δ δ' : Fin n → obj} {X Y} →
                 (∀ i → prod Γ (δ i) ⇒ δ' i) → (prod Γ X ⇒ Y) → ∀ i → prod Γ (extend δ X i) ⇒ extend δ' Y i
    strong-extend-mor fs x→y Fin.zero    = x→y
    strong-extend-mor fs x→y (Fin.suc i) = fs i

    mutual
      strong-fmor : ∀ {n Γ} (P : Poly 𝒞 n) {δ δ' : Fin n → obj} →
                    (∀ i → prod Γ (δ i) ⇒ δ' i) → prod Γ (fobj μ-obj P δ) ⇒ fobj μ-obj P δ'
      strong-fmor (const A) fs = p₂
      strong-fmor (var i)   fs = fs i
      strong-fmor (P + Q)   fs = scopair (in₁ ∘ strong-fmor P fs) (in₂ ∘ strong-fmor Q fs)
      strong-fmor (P × Q)   fs = strong-prod-m (strong-fmor P fs) (strong-fmor Q fs)
      strong-fmor (μ P)     fs = strong-μ-fmor P fs

      strong-μ-fmor : ∀ {n Γ} (P : Poly 𝒞 (suc n)) {δ δ' : Fin n → obj} →
                      (∀ i → prod Γ (δ i) ⇒ δ' i) → prod Γ (μ-obj P δ) ⇒ μ-obj P δ'
      strong-μ-fmor P {δ} {δ'} fs = ⦅ inMap P δ' ∘ strong-fmor P (strong-extend-mor fs p₂) ⦆

    fmor : ∀ {n} (P : Poly 𝒞 n) {δ δ' : Fin n → obj} → (∀ i → δ i ⇒ δ' i) → fobj μ-obj P δ ⇒ fobj μ-obj P δ'
    fmor P fs = strong-fmor P (λ i → fs i ∘ p₂) ∘ pair to-terminal (id _)

    -- A morphism between μ-objs, induced by an unfolding of P into Q at the target carrier.
    -- P, δ are explicit because fobj/μ-obj are not injective, so they can't be inferred from unfold.
    μ-map : ∀ {m n} (P : Poly 𝒞 (suc m)) (δ : Fin m → obj) (Q : Poly 𝒞 (suc n)) (δ' : Fin n → obj) →
            (fobj μ-obj P (extend δ (μ-obj Q δ')) ⇒ fobj μ-obj Q (extend δ' (μ-obj Q δ'))) →
            μ-obj P δ ⇒ μ-obj Q δ'
    μ-map P δ Q δ' unfold = ⦅_⦆ {P = P} {δ = δ} ((inMap Q δ' ∘ unfold) ∘ p₂) ∘ pair to-terminal (id _)

  -- The initiality laws for HasMu, stated via the strong functorial action derived from its operations.
  record HasMuLaws (Mu : HasMu) : Set (o ⊔ m ⊔ e) where
    open HasMu Mu
    field
      ⦅⦆-β : ∀ {n Γ A} {P : Poly 𝒞 (suc n)} {δ : Fin n → obj}
             (alg : prod Γ (fobj μ-obj P (extend δ A)) ⇒ A) →
             (⦅ alg ⦆ ∘co (inMap P δ ∘ p₂)) ≈ (alg ∘co strong-fmor P (strong-extend-mor (λ i → p₂) ⦅ alg ⦆))
      ⦅⦆-η : ∀ {n Γ A} {P : Poly 𝒞 (suc n)} {δ : Fin n → obj}
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


-- The functor preserves μ-types: each μ-object maps, up to isomorphism, to the
-- μ-object of the image polynomial in the image environment.
Preserves-μ : ∀ {o₁ m₁ e₁ o₂ m₂ e₂} {𝒞 : Category o₁ m₁ e₁} {𝒟 : Category o₂ m₂ e₂}
              (𝒞T : HasTerminal 𝒞) (𝒞P : HasProducts 𝒞) (𝒞SCP : HasStrongCoproducts 𝒞 𝒞P)
              (𝒟T : HasTerminal 𝒟) (𝒟P : HasProducts 𝒟) (𝒟SCP : HasStrongCoproducts 𝒟 𝒟P) →
              Interp.HasMu 𝒞T 𝒞P 𝒞SCP → Interp.HasMu 𝒟T 𝒟P 𝒟SCP → Functor 𝒞 𝒟 →
              Set (o₁ ⊔ m₂ ⊔ e₂)
Preserves-μ {𝒞 = 𝒞} {𝒟 = 𝒟} 𝒞T 𝒞P 𝒞SCP 𝒟T 𝒟P 𝒟SCP 𝒞Mu 𝒟Mu F =
  ∀ {n} (P : Poly 𝒞 (suc n)) (δ : Fin n → Category.obj 𝒞) →
  Category.Iso 𝒟 (F .Functor.fobj (CM.μ-obj P δ))
                 (DM.μ-obj (Poly-map F P) (λ i → F .Functor.fobj (δ i)))
  where
    module CM = Interp.HasMu 𝒞Mu
    module DM = Interp.HasMu 𝒟Mu

