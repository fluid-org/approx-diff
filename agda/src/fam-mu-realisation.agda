{-# OPTIONS --prop --postfix-projections --safe #-}

-- Parameterised initial algebras for a category ℰ with setoid-indexed
-- colimits, products, exponentials and strong coproducts, constructed by
-- realising the μ-types of Fam(ℰ). The realised μ-object carries an initial
-- algebra for the realised polynomial endofunctor; the algebra map, fold and
-- laws are established by a mutual induction on polynomials: the collapse
-- isomorphisms (realisation is invariant under replacing an environment entry
-- by a family with isomorphic realisation), initiality via folds transposed
-- through the adjunction between realisation and the singleton embedding, and
-- uniqueness of initial algebras at the inner-μ cases.

open import Level using (Level; _⊔_)
open import Data.Nat using (ℕ; suc)
import Data.Fin as Fin
open Fin using (Fin)
open import prop-setoid using (Setoid)
open import categories
  using (Category; setoid→category; HasTerminal; HasProducts; HasExponentials;
         HasStrongCoproducts)
open import functor using (Functor; HasColimits)
open import polynomial-functor-2 using (Poly; extend; Poly-map)
import fam
import fam-mu-types-2
import fam-realisation
import polynomial-functor-2

module fam-mu-realisation {o m e} (os es : Level) {ℰ : Category o m e}
  (EC : ∀ (A : Setoid os (os ⊔ es)) → HasColimits (setoid→category A) ℰ)
  (ET : HasTerminal ℰ) (EP : HasProducts ℰ) (EE : HasExponentials ℰ EP)
  (ESC : HasStrongCoproducts ℰ EP)
  where

open Category ℰ
open Functor

private
  module EP = HasProducts EP

module FR = fam-realisation os (os ⊔ es) EC
open FR using (realise; η; realise-η-iso; transpose; untranspose)

module FM = fam-mu-types-2 os es ET EP

private
  module FMu = FM.HasMu FM.hasMu

module EI = polynomial-functor-2.Interp ET EP ESC
open EI using (_∘co_)

-- The realised μ-carrier of the η-image polynomial.
Creal : ∀ {n} → Poly ℰ (suc n) → (Fin n → FM.Obj) → obj
Creal P δ̂ = realise .fobj (FM.μObj (Poly-map η P) δ̂)

-- The realised polynomial endofunctor, object part: apply the η-image
-- polynomial with A embedded at the bound variable, and realise.
Greal : ∀ {n} → Poly ℰ (suc n) → (Fin n → FM.Obj) → obj → obj
Greal P δ̂ A = realise .fobj (FM.fobj FM.μObj (Poly-map η P) (extend δ̂ (η .fobj A)))

-- A Fam(ℰ)-product with an η-embedded context realises to the ℰ-product.
prodη : ∀ (Γ : obj) (W : FM.Obj) →
        Iso (realise .fobj (FM.Fam𝒞-P.prod (η .fobj Γ) W)) (EP.prod Γ (realise .fobj W))
prodη Γ W =
  Iso-trans (FR.realise-products-iso EP EE (η .fobj Γ) W)
    (EP.product-preserves-iso (realise-η-iso Γ) Iso-refl)

-- The strong functorial action of the realised endofunctor: transpose the
-- context morphism to Fam(ℰ), act there, and realise.
Gmap : ∀ {n} (P : Poly ℰ (suc n)) (δ̂ : Fin n → FM.Obj) {Γ A B} →
       (EP.prod Γ A ⇒ B) → EP.prod Γ (Greal P δ̂ A) ⇒ Greal P δ̂ B
Gmap P δ̂ {Γ} {A} {B} h =
  realise .fmor
    (FMu.strong-fmor (Poly-map η P) (FMu.strong-extend-mor (λ i → FM.Fam𝒞-P.p₂) hFam))
    ∘ prodη Γ (FM.fobj FM.μObj (Poly-map η P) (extend δ̂ (η .fobj A))) .Iso.bwd
  where
    hFam : FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) (η .fobj A)) (η .fobj B)
    hFam = untranspose
      (h ∘ (EP.prod-m (id _) (realise-η-iso A .Iso.fwd) ∘ prodη Γ (η .fobj A) .Iso.fwd))

-- The initial-algebra package carried by a realised μ-object: algebra map and
-- strong catamorphism with the β/η laws, mirroring HasMu/HasMuLaws.
record MuReal {n} (P : Poly ℰ (suc n)) (δ̂ : Fin n → FM.Obj) : Set (o ⊔ m ⊔ e) where
  field
    inR    : Greal P δ̂ (Creal P δ̂) ⇒ Creal P δ̂
    foldR  : ∀ {Γ A} → (EP.prod Γ (Greal P δ̂ A) ⇒ A) → EP.prod Γ (Creal P δ̂) ⇒ A

    foldR-cong : ∀ {Γ A} {a₁ a₂ : EP.prod Γ (Greal P δ̂ A) ⇒ A} →
                 a₁ ≈ a₂ → foldR a₁ ≈ foldR a₂
    foldR-β : ∀ {Γ A} (a : EP.prod Γ (Greal P δ̂ A) ⇒ A) →
              (foldR a ∘co (inR ∘ EP.p₂)) ≈ (a ∘co Gmap P δ̂ (foldR a))
    foldR-η : ∀ {Γ A} (a : EP.prod Γ (Greal P δ̂ A) ⇒ A) (h : EP.prod Γ (Creal P δ̂) ⇒ A) →
              (h ∘co (inR ∘ EP.p₂)) ≈ (a ∘co Gmap P δ̂ h) → h ≈ foldR a

-- The collapse isomorphism family: realisation of a polynomial application is
-- invariant under replacing environment entries by families with isomorphic
-- realisations.
CollapseTy : ∀ n → Set (o ⊔ m ⊔ e ⊔ Level.suc os ⊔ Level.suc es)
CollapseTy n =
  (P : Poly ℰ n) (δ̂₁ δ̂₂ : Fin n → FM.Obj) →
  (∀ i → Iso (realise .fobj (δ̂₁ i)) (realise .fobj (δ̂₂ i))) →
  Iso (realise .fobj (FM.fobj FM.μObj (Poly-map η P) δ̂₁))
      (realise .fobj (FM.fobj FM.μObj (Poly-map η P) δ̂₂))
