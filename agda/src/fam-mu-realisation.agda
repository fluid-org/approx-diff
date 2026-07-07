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
open import prop-setoid using (Setoid; module ≈-Reasoning)
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
  (ℰC : ∀ (A : Setoid os (os ⊔ es)) → HasColimits (setoid→category A) ℰ)
  (ℰT : HasTerminal ℰ) (ℰP : HasProducts ℰ) (ℰE : HasExponentials ℰ ℰP)
  (ℰSC : HasStrongCoproducts ℰ ℰP)
  where

open Category ℰ
open Functor

private
  module ℰP = HasProducts ℰP

module FR = fam-realisation os (os ⊔ es) ℰC
open FR using (realise; η; realise-η-iso; transpose; untranspose)

module FM = fam-mu-types-2 os es ℰT ℰP

private
  module FMu = FM.HasMu FM.hasMu

module ℰI = polynomial-functor-2.Interp ℰT ℰP ℰSC
open ℰI using (_∘co_)

-- The realised μ-carrier of the η-image polynomial.
Creal : ∀ {n} → Poly ℰ (suc n) → (Fin n → FM.Obj) → obj
Creal P δ̂ = realise .fobj (FM.μObj (Poly-map η P) δ̂)

-- The realised polynomial endofunctor, object part: apply the η-image
-- polynomial with A embedded at the bound variable, and realise.
Greal : ∀ {n} → Poly ℰ (suc n) → (Fin n → FM.Obj) → obj → obj
Greal P δ̂ A = realise .fobj (FM.fobj FM.μObj (Poly-map η P) (extend δ̂ (η .fobj A)))

-- A Fam(ℰ)-product with an η-embedded context realises to the ℰ-product.
prodη : ∀ (Γ : obj) (W : FM.Obj) →
        Iso (realise .fobj (FM.Fam𝒞-P.prod (η .fobj Γ) W)) (ℰP.prod Γ (realise .fobj W))
prodη Γ W =
  Iso-trans (FR.realise-products-iso ℰP ℰE (η .fobj Γ) W)
    (ℰP.product-preserves-iso (realise-η-iso Γ) Iso-refl)

-- The strong functorial action of the realised endofunctor: transpose the
-- context morphism to Fam(ℰ), act there, and realise.
Gmap : ∀ {n} (P : Poly ℰ (suc n)) (δ̂ : Fin n → FM.Obj) {Γ A B} →
       (ℰP.prod Γ A ⇒ B) → ℰP.prod Γ (Greal P δ̂ A) ⇒ Greal P δ̂ B
Gmap P δ̂ {Γ} {A} {B} h =
  realise .fmor
    (FMu.strong-fmor (Poly-map η P) (FMu.strong-extend-mor (λ i → FM.Fam𝒞-P.p₂) hFam))
    ∘ prodη Γ (FM.fobj FM.μObj (Poly-map η P) (extend δ̂ (η .fobj A))) .Iso.bwd
  where
    hFam : FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) (η .fobj A)) (η .fobj B)
    hFam = untranspose
      (h ∘ (ℰP.prod-m (id _) (realise-η-iso A .Iso.fwd) ∘ prodη Γ (η .fobj A) .Iso.fwd))

-- The initial-algebra package carried by a realised μ-object: algebra map and
-- strong catamorphism with the β/η laws, mirroring HasMu/HasMuLaws.
record MuReal {n} (P : Poly ℰ (suc n)) (δ̂ : Fin n → FM.Obj) : Set (o ⊔ m ⊔ e) where
  field
    inR    : Greal P δ̂ (Creal P δ̂) ⇒ Creal P δ̂
    foldR  : ∀ {Γ A} → (ℰP.prod Γ (Greal P δ̂ A) ⇒ A) → ℰP.prod Γ (Creal P δ̂) ⇒ A

    foldR-cong : ∀ {Γ A} {a₁ a₂ : ℰP.prod Γ (Greal P δ̂ A) ⇒ A} →
                 a₁ ≈ a₂ → foldR a₁ ≈ foldR a₂
    foldR-β : ∀ {Γ A} (a : ℰP.prod Γ (Greal P δ̂ A) ⇒ A) →
              (foldR a ∘co (inR ∘ ℰP.p₂)) ≈ (a ∘co Gmap P δ̂ (foldR a))
    foldR-η : ∀ {Γ A} (a : ℰP.prod Γ (Greal P δ̂ A) ⇒ A) (h : ℰP.prod Γ (Creal P δ̂) ⇒ A) →
              (h ∘co (inR ∘ ℰP.p₂)) ≈ (a ∘co Gmap P δ̂ h) → h ≈ foldR a

-- The collapse isomorphism family: realisation of a polynomial application is
-- invariant under replacing environment entries by families with isomorphic
-- realisations.
CollapseTy : ∀ n → Set (o ⊔ m ⊔ e ⊔ Level.suc os ⊔ Level.suc es)
CollapseTy n =
  (P : Poly ℰ n) (δ̂₁ δ̂₂ : Fin n → FM.Obj) →
  (∀ i → Iso (realise .fobj (δ̂₁ i)) (realise .fobj (δ̂₂ i))) →
  Iso (realise .fobj (FM.fobj FM.μObj (Poly-map η P) δ̂₁))
      (realise .fobj (FM.fobj FM.μObj (Poly-map η P) δ̂₂))

-- The operations of the initial-algebra package for a polynomial, against an
-- assumed collapse family. The algebra map realises the Fam(ℰ) algebra map and
-- corrects the bound-variable entry by collapse; the fold transposes the
-- algebra to Fam(ℰ), folds there, and transposes back.
module Initiality {n} (P : Poly ℰ (suc n)) (δ̂ : Fin n → FM.Obj)
    (collapseP : CollapseTy (suc n))
  where

  private
    P̂ = Poly-map η P

    inIsos : ∀ i → Iso (realise .fobj (extend δ̂ (η .fobj (Creal P δ̂)) i))
                       (realise .fobj (extend δ̂ (FM.μObj P̂ δ̂) i))
    inIsos Fin.zero    = realise-η-iso (Creal P δ̂)
    inIsos (Fin.suc i) = Iso-refl

  inR : Greal P δ̂ (Creal P δ̂) ⇒ Creal P δ̂
  inR = realise .fmor (FMu.α P̂ δ̂) ∘
        collapseP P (extend δ̂ (η .fobj (Creal P δ̂))) (extend δ̂ (FM.μObj P̂ δ̂)) inIsos .Iso.fwd

  foldR : ∀ {Γ A} → (ℰP.prod Γ (Greal P δ̂ A) ⇒ A) → ℰP.prod Γ (Creal P δ̂) ⇒ A
  foldR {Γ} {A} a =
    transpose (FMu.⦅_⦆ {P = P̂} {δ = δ̂} bFam) ∘ prodη Γ (FM.μObj P̂ δ̂) .Iso.bwd
    where
      bFam : FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) (FM.fobj FM.μObj P̂ (extend δ̂ (η .fobj A))))
                    (η .fobj A)
      bFam = untranspose (a ∘ prodη Γ (FM.fobj FM.μObj P̂ (extend δ̂ (η .fobj A))) .Iso.fwd)

-- The co-Kleisli action of realisation: a Fam(ℰ)-morphism from a product with
-- an η-embedded context acts on realisations in that context.
fmorη : ∀ (Γ : obj) (X : FM.Obj) {Y : FM.Obj} →
        FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) X) Y → ℰP.prod Γ (realise .fobj X) ⇒ realise .fobj Y
fmorη Γ X u = realise .fmor u ∘ prodη Γ X .Iso.bwd

fmorη-cong : ∀ {Γ X Y} {u₁ u₂ : FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) X) Y} →
             Category._≈_ FM.cat u₁ u₂ → fmorη Γ X u₁ ≈ fmorη Γ X u₂
fmorη-cong u₁≃u₂ = ∘-cong (realise .fmor-cong u₁≃u₂) ≈-refl

-- Pair a context-preserving morphism with the context projection, with the
-- projection pinned (prod is not injective, so it cannot be inferred).
pairη : ∀ (Γ : obj) (X : FM.Obj) {Y : FM.Obj} →
        FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) X) Y →
        FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) X) (FM.Fam𝒞-P.prod (η .fobj Γ) Y)
pairη Γ X v = FM.Fam𝒞-P.pair (FM.Fam𝒞-P.p₁ {x = η .fobj Γ} {y = X}) v

-- The bridging iso commutes with the product projections.
prodη-p₁ : ∀ (Γ : obj) (X : FM.Obj) →
           (ℰP.p₁ ∘ prodη Γ X .Iso.fwd) ≈ (realise-η-iso Γ .Iso.fwd ∘ realise .fmor FM.Fam𝒞-P.p₁)
prodη-p₁ Γ X =
  begin
    ℰP.p₁ ∘ (ℰP.prod-m (realise-η-iso Γ .Iso.fwd) (id _) ∘ FR.realise-products-iso ℰP ℰE (η .fobj Γ) X .Iso.fwd)
  ≈˘⟨ assoc _ _ _ ⟩
    (ℰP.p₁ ∘ ℰP.prod-m (realise-η-iso Γ .Iso.fwd) (id _)) ∘ FR.realise-products-iso ℰP ℰE (η .fobj Γ) X .Iso.fwd
  ≈⟨ ∘-cong (ℰP.pair-p₁ _ _) ≈-refl ⟩
    (realise-η-iso Γ .Iso.fwd ∘ ℰP.p₁) ∘ FR.realise-products-iso ℰP ℰE (η .fobj Γ) X .Iso.fwd
  ≈⟨ assoc _ _ _ ⟩
    realise-η-iso Γ .Iso.fwd ∘ (ℰP.p₁ ∘ FR.realise-products-iso ℰP ℰE (η .fobj Γ) X .Iso.fwd)
  ≈⟨ ∘-cong ≈-refl (FR.realise-products-p₁ ℰP ℰE (η .fobj Γ) X) ⟩
    realise-η-iso Γ .Iso.fwd ∘ realise .fmor FM.Fam𝒞-P.p₁
  ∎ where open ≈-Reasoning isEquiv

prodη-p₂ : ∀ (Γ : obj) (X : FM.Obj) →
           (ℰP.p₂ ∘ prodη Γ X .Iso.fwd) ≈ realise .fmor FM.Fam𝒞-P.p₂
prodη-p₂ Γ X =
  begin
    ℰP.p₂ ∘ (ℰP.prod-m (realise-η-iso Γ .Iso.fwd) (id _) ∘ FR.realise-products-iso ℰP ℰE (η .fobj Γ) X .Iso.fwd)
  ≈˘⟨ assoc _ _ _ ⟩
    (ℰP.p₂ ∘ ℰP.prod-m (realise-η-iso Γ .Iso.fwd) (id _)) ∘ FR.realise-products-iso ℰP ℰE (η .fobj Γ) X .Iso.fwd
  ≈⟨ ∘-cong (ℰP.pair-p₂ _ _) ≈-refl ⟩
    (id _ ∘ ℰP.p₂) ∘ FR.realise-products-iso ℰP ℰE (η .fobj Γ) X .Iso.fwd
  ≈⟨ ∘-cong id-left ≈-refl ⟩
    ℰP.p₂ ∘ FR.realise-products-iso ℰP ℰE (η .fobj Γ) X .Iso.fwd
  ≈⟨ FR.realise-products-p₂ ℰP ℰE (η .fobj Γ) X ⟩
    realise .fmor FM.Fam𝒞-P.p₂
  ∎ where open ≈-Reasoning isEquiv

-- Realisation of a context-preserving pair against the bridging iso.
prodη-pair : ∀ (Γ : obj) (X : FM.Obj) {Y : FM.Obj} (v : FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) X) Y) →
             (realise .fmor (pairη Γ X v) ∘ prodη Γ X .Iso.bwd)
             ≈ (prodη Γ Y .Iso.bwd ∘ ℰP.pair (ℰP.p₁ {Γ} {realise .fobj X}) (fmorη Γ X v))
prodη-pair Γ X {Y} v =
  ≈-trans (≈-sym id-left)
    (≈-trans (∘-cong (≈-sym (prodη Γ Y .Iso.bwd∘fwd≈id)) ≈-refl)
      (≈-trans (assoc _ _ _) (∘-cong ≈-refl core)))
  where
    core : (prodη Γ Y .Iso.fwd ∘ (realise .fmor (pairη Γ X v) ∘ prodη Γ X .Iso.bwd))
           ≈ ℰP.pair (ℰP.p₁ {Γ} {realise .fobj X}) (fmorη Γ X v)
    core =
      ≈-trans (≈-sym (ℰP.pair-ext {y = Γ} {z = realise .fobj Y} _)) (ℰP.pair-cong core-p₁ core-p₂)
      where
        core-p₁ : (ℰP.p₁ {Γ} {realise .fobj Y} ∘ (prodη Γ Y .Iso.fwd ∘ (realise .fmor (pairη Γ X v) ∘ prodη Γ X .Iso.bwd)))
                  ≈ ℰP.p₁ {Γ} {realise .fobj X}
        core-p₁ =
          begin
            ℰP.p₁ {Γ} {realise .fobj Y} ∘ (prodη Γ Y .Iso.fwd ∘ (realise .fmor (pairη Γ X v) ∘ prodη Γ X .Iso.bwd))
          ≈˘⟨ assoc _ _ _ ⟩
            (ℰP.p₁ {Γ} {realise .fobj Y} ∘ prodη Γ Y .Iso.fwd) ∘ (realise .fmor (pairη Γ X v) ∘ prodη Γ X .Iso.bwd)
          ≈⟨ ∘-cong (prodη-p₁ Γ Y) ≈-refl ⟩
            (realise-η-iso Γ .Iso.fwd ∘ realise .fmor FM.Fam𝒞-P.p₁) ∘ (realise .fmor (pairη Γ X v) ∘ prodη Γ X .Iso.bwd)
          ≈⟨ assoc _ _ _ ⟩
            realise-η-iso Γ .Iso.fwd ∘ (realise .fmor FM.Fam𝒞-P.p₁ ∘ (realise .fmor (pairη Γ X v) ∘ prodη Γ X .Iso.bwd))
          ≈˘⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
            realise-η-iso Γ .Iso.fwd ∘ ((realise .fmor FM.Fam𝒞-P.p₁ ∘ realise .fmor (pairη Γ X v)) ∘ prodη Γ X .Iso.bwd)
          ≈˘⟨ ∘-cong ≈-refl (∘-cong (realise .fmor-comp _ _) ≈-refl) ⟩
            realise-η-iso Γ .Iso.fwd ∘ (realise .fmor (FM.Mor-∘ FM.Fam𝒞-P.p₁ (pairη Γ X v)) ∘ prodη Γ X .Iso.bwd)
          ≈⟨ ∘-cong ≈-refl (∘-cong (realise .fmor-cong (FM.Fam𝒞-P.pair-p₁ _ _)) ≈-refl) ⟩
            realise-η-iso Γ .Iso.fwd ∘ (realise .fmor (FM.Fam𝒞-P.p₁ {x = η .fobj Γ} {y = X}) ∘ prodη Γ X .Iso.bwd)
          ≈˘⟨ assoc _ _ _ ⟩
            (realise-η-iso Γ .Iso.fwd ∘ realise .fmor (FM.Fam𝒞-P.p₁ {x = η .fobj Γ} {y = X})) ∘ prodη Γ X .Iso.bwd
          ≈˘⟨ ∘-cong (prodη-p₁ Γ X) ≈-refl ⟩
            (ℰP.p₁ {Γ} {realise .fobj X} ∘ prodη Γ X .Iso.fwd) ∘ prodη Γ X .Iso.bwd
          ≈⟨ assoc _ _ _ ⟩
            ℰP.p₁ {Γ} {realise .fobj X} ∘ (prodη Γ X .Iso.fwd ∘ prodη Γ X .Iso.bwd)
          ≈⟨ ∘-cong ≈-refl (prodη Γ X .Iso.fwd∘bwd≈id) ⟩
            ℰP.p₁ {Γ} {realise .fobj X} ∘ id _
          ≈⟨ id-right ⟩
            ℰP.p₁ {Γ} {realise .fobj X}
          ∎ where open ≈-Reasoning isEquiv

        core-p₂ : (ℰP.p₂ {Γ} {realise .fobj Y} ∘ (prodη Γ Y .Iso.fwd ∘ (realise .fmor (pairη Γ X v) ∘ prodη Γ X .Iso.bwd)))
                  ≈ fmorη Γ X v
        core-p₂ =
          begin
            ℰP.p₂ {Γ} {realise .fobj Y} ∘ (prodη Γ Y .Iso.fwd ∘ (realise .fmor (pairη Γ X v) ∘ prodη Γ X .Iso.bwd))
          ≈˘⟨ assoc _ _ _ ⟩
            (ℰP.p₂ {Γ} {realise .fobj Y} ∘ prodη Γ Y .Iso.fwd) ∘ (realise .fmor (pairη Γ X v) ∘ prodη Γ X .Iso.bwd)
          ≈⟨ ∘-cong (prodη-p₂ Γ Y) ≈-refl ⟩
            realise .fmor FM.Fam𝒞-P.p₂ ∘ (realise .fmor (pairη Γ X v) ∘ prodη Γ X .Iso.bwd)
          ≈˘⟨ assoc _ _ _ ⟩
            (realise .fmor FM.Fam𝒞-P.p₂ ∘ realise .fmor (pairη Γ X v)) ∘ prodη Γ X .Iso.bwd
          ≈˘⟨ ∘-cong (realise .fmor-comp _ _) ≈-refl ⟩
            realise .fmor (FM.Mor-∘ FM.Fam𝒞-P.p₂ (pairη Γ X v)) ∘ prodη Γ X .Iso.bwd
          ≈⟨ ∘-cong (realise .fmor-cong (FM.Fam𝒞-P.pair-p₂ _ _)) ≈-refl ⟩
            realise .fmor v ∘ prodη Γ X .Iso.bwd
          ∎ where open ≈-Reasoning isEquiv

-- Realisation is a co-Kleisli functor: it sends composition in context over
-- Fam(ℰ) to composition in context over ℰ.
fmorη-∘co : ∀ (Γ : obj) (X : FM.Obj) {Y Z : FM.Obj}
            (u : FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) Y) Z)
            (v : FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) X) Y) →
            fmorη Γ X (FM.Mor-∘ u (pairη Γ X v)) ≈ (fmorη Γ Y u ∘co fmorη Γ X v)
fmorη-∘co Γ X {Y} {Z} u v =
  begin
    realise .fmor (FM.Mor-∘ u (pairη Γ X v)) ∘ prodη Γ X .Iso.bwd
  ≈⟨ ∘-cong (realise .fmor-comp _ _) ≈-refl ⟩
    (realise .fmor u ∘ realise .fmor (pairη Γ X v)) ∘ prodη Γ X .Iso.bwd
  ≈⟨ assoc _ _ _ ⟩
    realise .fmor u ∘ (realise .fmor (pairη Γ X v) ∘ prodη Γ X .Iso.bwd)
  ≈⟨ ∘-cong ≈-refl (prodη-pair Γ X v) ⟩
    realise .fmor u ∘ (prodη Γ Y .Iso.bwd ∘ ℰP.pair (ℰP.p₁ {Γ} {realise .fobj X}) (fmorη Γ X v))
  ≈˘⟨ assoc _ _ _ ⟩
    (realise .fmor u ∘ prodη Γ Y .Iso.bwd) ∘ ℰP.pair (ℰP.p₁ {Γ} {realise .fobj X}) (fmorη Γ X v)
  ∎ where open ≈-Reasoning isEquiv
