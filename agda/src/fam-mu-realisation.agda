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
         HasStrongCoproducts; coKleisli-prod)
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

private
  module CoK {Γ : obj} = Category (coKleisli-prod ℰP Γ)

-- The context projection realises to the projection.
fmorη-p₂ : ∀ (Γ : obj) (X : FM.Obj) →
           fmorη Γ X (FM.Fam𝒞-P.p₂ {x = η .fobj Γ} {y = X}) ≈ ℰP.p₂
fmorη-p₂ Γ X =
  begin
    realise .fmor (FM.Fam𝒞-P.p₂ {x = η .fobj Γ} {y = X}) ∘ prodη Γ X .Iso.bwd
  ≈˘⟨ ∘-cong (prodη-p₂ Γ X) ≈-refl ⟩
    (ℰP.p₂ ∘ prodη Γ X .Iso.fwd) ∘ prodη Γ X .Iso.bwd
  ≈⟨ assoc _ _ _ ⟩
    ℰP.p₂ ∘ (prodη Γ X .Iso.fwd ∘ prodη Γ X .Iso.bwd)
  ≈⟨ ∘-cong ≈-refl (prodη Γ X .Iso.fwd∘bwd≈id) ⟩
    ℰP.p₂ ∘ id _
  ≈⟨ id-right ⟩
    ℰP.p₂
  ∎ where open ≈-Reasoning isEquiv

-- A pure Fam(ℰ)-morphism precomposed with the projection realises purely.
fmorη-pure : ∀ (Γ : obj) (X : FM.Obj) {Y : FM.Obj} (w : FM.Mor X Y) →
             fmorη Γ X (FM.Mor-∘ w (FM.Fam𝒞-P.p₂ {x = η .fobj Γ} {y = X}))
             ≈ (realise .fmor w ∘ ℰP.p₂)
fmorη-pure Γ X w =
  begin
    realise .fmor (FM.Mor-∘ w (FM.Fam𝒞-P.p₂ {x = η .fobj Γ} {y = X})) ∘ prodη Γ X .Iso.bwd
  ≈⟨ ∘-cong (realise .fmor-comp _ _) ≈-refl ⟩
    (realise .fmor w ∘ realise .fmor (FM.Fam𝒞-P.p₂ {x = η .fobj Γ} {y = X})) ∘ prodη Γ X .Iso.bwd
  ≈⟨ assoc _ _ _ ⟩
    realise .fmor w ∘ (realise .fmor (FM.Fam𝒞-P.p₂ {x = η .fobj Γ} {y = X}) ∘ prodη Γ X .Iso.bwd)
  ≈⟨ ∘-cong ≈-refl (fmorη-p₂ Γ X) ⟩
    realise .fmor w ∘ ℰP.p₂
  ∎ where open ≈-Reasoning isEquiv

-- Realising an untransposed morphism and collapsing the target recovers it.
counit-fmorη : ∀ (Γ : obj) (X : FM.Obj) {A : obj}
               (g : realise .fobj (FM.Fam𝒞-P.prod (η .fobj Γ) X) ⇒ A) →
               (realise-η-iso A .Iso.fwd ∘ fmorη Γ X (untranspose g))
               ≈ (g ∘ prodη Γ X .Iso.bwd)
counit-fmorη Γ X {A} g =
  begin
    realise-η-iso A .Iso.fwd ∘ (realise .fmor (untranspose g) ∘ prodη Γ X .Iso.bwd)
  ≈˘⟨ assoc _ _ _ ⟩
    (realise-η-iso A .Iso.fwd ∘ realise .fmor (untranspose g)) ∘ prodη Γ X .Iso.bwd
  ≈˘⟨ ∘-cong (FR.transpose-realise (untranspose g)) ≈-refl ⟩
    transpose (untranspose g) ∘ prodη Γ X .Iso.bwd
  ≈⟨ ∘-cong (FR.transpose-untranspose g) ≈-refl ⟩
    g ∘ prodη Γ X .Iso.bwd
  ∎ where open ≈-Reasoning isEquiv

-- Composition in context of pure morphisms.
co-pure : ∀ {Γ X Y Z : obj} (x : Y ⇒ Z) (y : X ⇒ Y) →
          ((x ∘ ℰP.p₂ {Γ} {Y}) ∘co (y ∘ ℰP.p₂)) ≈ ((x ∘ y) ∘ ℰP.p₂)
co-pure x y =
  ≈-trans (assoc _ _ _)
    (≈-trans (∘-cong ≈-refl (ℰP.pair-p₂ _ _)) (≈-sym (assoc _ _ _)))

-- Cancel an isomorphism applied in context on the right of a composition.
co-iso-cancel : ∀ {Γ X Y Z : obj} (I : Iso X Y)
                {u : ℰP.prod Γ Y ⇒ Z} {v : ℰP.prod Γ X ⇒ Z} →
                (u ∘co (I .Iso.fwd ∘ ℰP.p₂)) ≈ v → (v ∘co (I .Iso.bwd ∘ ℰP.p₂)) ≈ u
co-iso-cancel I {u} {v} eq =
  begin
    v ∘co (I .Iso.bwd ∘ ℰP.p₂)
  ≈˘⟨ CoK.∘-cong eq ≈-refl ⟩
    (u ∘co (I .Iso.fwd ∘ ℰP.p₂)) ∘co (I .Iso.bwd ∘ ℰP.p₂)
  ≈⟨ CoK.assoc _ _ _ ⟩
    u ∘co ((I .Iso.fwd ∘ ℰP.p₂) ∘co (I .Iso.bwd ∘ ℰP.p₂))
  ≈⟨ CoK.∘-cong ≈-refl (co-pure (I .Iso.fwd) (I .Iso.bwd)) ⟩
    u ∘co ((I .Iso.fwd ∘ I .Iso.bwd) ∘ ℰP.p₂)
  ≈⟨ CoK.∘-cong ≈-refl (∘-cong (I .Iso.fwd∘bwd≈id) ≈-refl) ⟩
    u ∘co (id _ ∘ ℰP.p₂)
  ≈⟨ CoK.∘-cong ≈-refl id-left ⟩
    u ∘co ℰP.p₂
  ≈⟨ CoK.id-right ⟩
    u
  ∎ where open ≈-Reasoning isEquiv

-- Move an isomorphism across an equation.
iso-shuffle : ∀ {X Y Z : obj} (I : Iso Y Z) (f : X ⇒ Y) (g : X ⇒ Z) →
              (I .Iso.fwd ∘ f) ≈ g → f ≈ (I .Iso.bwd ∘ g)
iso-shuffle I f g eq =
  ≈-trans (≈-sym id-left)
    (≈-trans (∘-cong (≈-sym (I .Iso.bwd∘fwd≈id)) ≈-refl)
      (≈-trans (assoc _ _ _) (∘-cong ≈-refl eq)))

-- Realisation in context is injective on morphisms into embedded objects.
fmorη-inj : ∀ (Γ : obj) (X : FM.Obj) {A : obj}
            (u v : FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) X) (η .fobj A)) →
            fmorη Γ X u ≈ fmorη Γ X v → Category._≈_ FM.cat u v
fmorη-inj Γ X {A} u v eq =
  FM.≃-isEquivalence .prop-setoid.IsEquivalence.trans
    (FM.≃-isEquivalence .prop-setoid.IsEquivalence.sym (FR.untranspose-transpose u))
    (FM.≃-isEquivalence .prop-setoid.IsEquivalence.trans
      (FR.untranspose-cong tr-eq)
      (FR.untranspose-transpose v))
  where
    real-eq : realise .fmor u ≈ realise .fmor v
    real-eq =
      begin
        realise .fmor u
      ≈˘⟨ id-right ⟩
        realise .fmor u ∘ id _
      ≈˘⟨ ∘-cong ≈-refl (prodη Γ X .Iso.bwd∘fwd≈id) ⟩
        realise .fmor u ∘ (prodη Γ X .Iso.bwd ∘ prodη Γ X .Iso.fwd)
      ≈˘⟨ assoc _ _ _ ⟩
        fmorη Γ X u ∘ prodη Γ X .Iso.fwd
      ≈⟨ ∘-cong eq ≈-refl ⟩
        fmorη Γ X v ∘ prodη Γ X .Iso.fwd
      ≈⟨ assoc _ _ _ ⟩
        realise .fmor v ∘ (prodη Γ X .Iso.bwd ∘ prodη Γ X .Iso.fwd)
      ≈⟨ ∘-cong ≈-refl (prodη Γ X .Iso.bwd∘fwd≈id) ⟩
        realise .fmor v ∘ id _
      ≈⟨ id-right ⟩
        realise .fmor v
      ∎ where open ≈-Reasoning isEquiv

    tr-eq : transpose u ≈ transpose v
    tr-eq =
      ≈-trans (FR.transpose-realise u)
        (≈-trans (∘-cong ≈-refl real-eq) (≈-sym (FR.transpose-realise v)))

-- The pairing of the projections is the identity.
pair-p₁p₂-id : ∀ {Γ A : obj} → ℰP.pair (ℰP.p₁ {Γ} {A}) ℰP.p₂ ≈ id _
pair-p₁p₂-id =
  ≈-trans (ℰP.pair-cong (≈-sym id-right) (≈-sym id-right)) (ℰP.pair-ext (id _))

-- The initial-algebra package for a polynomial, against an assumed collapse
-- family and its naturality with respect to the strong action. The algebra
-- map realises the Fam(ℰ) algebra map and corrects the bound-variable entry
-- by collapse; the fold transposes the algebra to Fam(ℰ), folds there, and
-- transposes back; β follows from the Fam(ℰ) β law pushed through the
-- co-Kleisli functoriality of realisation.
module Initiality {n} (P : Poly ℰ (suc n)) (δ̂ : Fin n → FM.Obj)
    (collapseP : CollapseTy (suc n))
    (collapseNatP : ∀ {Γ : obj} {ε̂ : Fin (suc n) → FM.Obj}
                    (δ̂₁ δ̂₂ : Fin (suc n) → FM.Obj)
                    (isos : ∀ i → Iso (realise .fobj (δ̂₁ i)) (realise .fobj (δ̂₂ i)))
                    (gs₁ : ∀ i → FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) (δ̂₁ i)) (ε̂ i))
                    (gs₂ : ∀ i → FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) (δ̂₂ i)) (ε̂ i)) →
                    (∀ i → (fmorη Γ (δ̂₂ i) (gs₂ i) ∘co (isos i .Iso.fwd ∘ ℰP.p₂)) ≈ fmorη Γ (δ̂₁ i) (gs₁ i)) →
                    (fmorη Γ (FM.fobj FM.μObj (Poly-map η P) δ̂₂) (FMu.strong-fmor (Poly-map η P) gs₂)
                      ∘co (collapseP P δ̂₁ δ̂₂ isos .Iso.fwd ∘ ℰP.p₂))
                    ≈ fmorη Γ (FM.fobj FM.μObj (Poly-map η P) δ̂₁) (FMu.strong-fmor (Poly-map η P) gs₁))
  where

  private
    P̂ = Poly-map η P
    μ̂ = FM.μObj P̂ δ̂

    F^ : FM.Obj → FM.Obj
    F^ Ŷ = FM.fobj FM.μObj P̂ (extend δ̂ Ŷ)

    inIsos : ∀ i → Iso (realise .fobj (extend δ̂ (η .fobj (Creal P δ̂)) i))
                       (realise .fobj (extend δ̂ μ̂ i))
    inIsos Fin.zero    = realise-η-iso (Creal P δ̂)
    inIsos (Fin.suc i) = Iso-refl

    bF : ∀ {Γ A} → (ℰP.prod Γ (Greal P δ̂ A) ⇒ A) → FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) (F^ (η .fobj A))) (η .fobj A)
    bF {Γ} {A} a = untranspose (a ∘ prodη Γ (F^ (η .fobj A)) .Iso.fwd)

    -- Realising a morphism transposed to Fam(ℰ) and collapsing recovers it.
    absorb : ∀ {Γ A} (X : FM.Obj) (g : ℰP.prod Γ (realise .fobj X) ⇒ A) →
             (realise-η-iso A .Iso.fwd ∘ fmorη Γ X (untranspose (g ∘ prodη Γ X .Iso.fwd))) ≈ g
    absorb {Γ} {A} X g =
      ≈-trans (counit-fmorη Γ X _)
        (≈-trans (assoc _ _ _)
          (≈-trans (∘-cong ≈-refl (prodη Γ X .Iso.fwd∘bwd≈id)) id-right))

  inR : Greal P δ̂ (Creal P δ̂) ⇒ Creal P δ̂
  inR = realise .fmor (FMu.α P̂ δ̂) ∘
        collapseP P (extend δ̂ (η .fobj (Creal P δ̂))) (extend δ̂ μ̂) inIsos .Iso.fwd

  foldR : ∀ {Γ A} → (ℰP.prod Γ (Greal P δ̂ A) ⇒ A) → ℰP.prod Γ (Creal P δ̂) ⇒ A
  foldR {Γ} {A} a = transpose (FMu.⦅_⦆ {P = P̂} {δ = δ̂} (bF a)) ∘ prodη Γ μ̂ .Iso.bwd

  private
    -- The fold in counit-and-realisation form.
    foldR-real : ∀ {Γ A} (a : ℰP.prod Γ (Greal P δ̂ A) ⇒ A) →
                 foldR a ≈ (realise-η-iso A .Iso.fwd ∘ fmorη Γ μ̂ (FMu.⦅_⦆ {P = P̂} {δ = δ̂} (bF a)))
    foldR-real {Γ} {A} a =
      ≈-trans (∘-cong (FR.transpose-realise _) ≈-refl) (assoc _ _ _)

    -- The context morphism Gmap acts with, for a morphism out of the carrier.
    h~ : ∀ {Γ A} → (ℰP.prod Γ (Creal P δ̂) ⇒ A) →
         FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) (η .fobj (Creal P δ̂))) (η .fobj A)
    h~ {Γ} {A} h = untranspose
      (h ∘ (ℰP.prod-m (id _) (realise-η-iso (Creal P δ̂) .Iso.fwd) ∘ prodη Γ (η .fobj (Creal P δ̂)) .Iso.fwd))

    -- Compatibility of a transposed morphism with the counit component of the
    -- collapse, given its counit form.
    compat-zero : ∀ {Γ A} (u : FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) μ̂) (η .fobj A))
                  (h : ℰP.prod Γ (Creal P δ̂) ⇒ A) →
                  ((realise-η-iso A .Iso.fwd ∘ fmorη Γ μ̂ u) ≈ h) →
                  (fmorη Γ μ̂ u ∘co (realise-η-iso (Creal P δ̂) .Iso.fwd ∘ ℰP.p₂))
                  ≈ fmorη Γ (η .fobj (Creal P δ̂)) (h~ h)
    compat-zero {Γ} {A} u h hyp =
      ≈-trans (iso-shuffle (realise-η-iso A) _ _ middle)
        (≈-trans (≈-sym (assoc _ _ _))
          (≈-trans (∘-cong (realise-η-iso A .Iso.bwd∘fwd≈id) ≈-refl) id-left))
      where
        cA = realise-η-iso A .Iso.fwd
        cC = realise-η-iso (Creal P δ̂) .Iso.fwd

        left : (cA ∘ (fmorη Γ μ̂ u ∘co (cC ∘ ℰP.p₂))) ≈ (h ∘ ℰP.prod-m (id _) cC)
        left =
          ≈-trans (≈-sym (assoc _ _ _))
            (≈-trans (∘-cong hyp ≈-refl)
              (∘-cong ≈-refl (ℰP.pair-cong (≈-sym id-left) ≈-refl)))

        right : (cA ∘ fmorη Γ (η .fobj (Creal P δ̂)) (h~ h)) ≈ (h ∘ ℰP.prod-m (id _) cC)
        right =
          ≈-trans (counit-fmorη Γ (η .fobj (Creal P δ̂)) _)
            (≈-trans (assoc _ _ _)
              (∘-cong ≈-refl (≈-trans (assoc _ _ _) (≈-trans (∘-cong ≈-refl (prodη Γ (η .fobj (Creal P δ̂)) .Iso.fwd∘bwd≈id)) id-right))))

        middle : (cA ∘ (fmorη Γ μ̂ u ∘co (cC ∘ ℰP.p₂))) ≈ (cA ∘ fmorη Γ (η .fobj (Creal P δ̂)) (h~ h))
        middle = ≈-trans left (≈-sym right)

    compat-suc : ∀ {Γ : obj} (i : Fin n) →
                 (fmorη Γ (δ̂ i) (FM.Fam𝒞-P.p₂ {x = η .fobj Γ} {y = δ̂ i}) ∘co (Iso-refl .Iso.fwd ∘ ℰP.p₂))
                 ≈ fmorη Γ (δ̂ i) (FM.Fam𝒞-P.p₂ {x = η .fobj Γ} {y = δ̂ i})
    compat-suc {Γ} i =
      ≈-trans (∘-cong ≈-refl (ℰP.pair-cong ≈-refl id-left))
        (≈-trans (∘-cong ≈-refl pair-p₁p₂-id) id-right)

    -- The collapse-naturality square for a Fam(ℰ) morphism in counit form.
    key : ∀ {Γ A} (u : FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) μ̂) (η .fobj A))
          (h : ℰP.prod Γ (Creal P δ̂) ⇒ A) →
          ((realise-η-iso A .Iso.fwd ∘ fmorη Γ μ̂ u) ≈ h) →
          (fmorη Γ (F^ μ̂) (FMu.strong-fmor P̂ (FMu.strong-extend-mor (λ i → FM.Fam𝒞-P.p₂) u))
            ∘co (collapseP P (extend δ̂ (η .fobj (Creal P δ̂))) (extend δ̂ μ̂) inIsos .Iso.fwd ∘ ℰP.p₂))
          ≈ Gmap P δ̂ h
    key {Γ} {A} u h hyp =
      collapseNatP (extend δ̂ (η .fobj (Creal P δ̂))) (extend δ̂ μ̂) inIsos
        (FMu.strong-extend-mor (λ i → FM.Fam𝒞-P.p₂) (h~ h))
        (FMu.strong-extend-mor (λ i → FM.Fam𝒞-P.p₂) u)
        compats
      where
        compats : ∀ i → (fmorη Γ (extend δ̂ μ̂ i) (FMu.strong-extend-mor (λ j → FM.Fam𝒞-P.p₂) u i) ∘co (inIsos i .Iso.fwd ∘ ℰP.p₂))
                  ≈ fmorη Γ (extend δ̂ (η .fobj (Creal P δ̂)) i) (FMu.strong-extend-mor (λ j → FM.Fam𝒞-P.p₂) (h~ h) i)
        compats Fin.zero    = compat-zero u h hyp
        compats (Fin.suc i) = compat-suc i

  foldR-β : ∀ {Γ A} (a : ℰP.prod Γ (Greal P δ̂ A) ⇒ A) →
            (foldR a ∘co (inR ∘ ℰP.p₂)) ≈ (a ∘co Gmap P δ̂ (foldR a))
  foldR-β {Γ} {A} a =
    begin
      foldR a ∘co (inR ∘ ℰP.p₂)
    ≈⟨ CoK.∘-cong (foldR-real a) split ⟩
      (cA ∘ Φ⦅b⦆) ∘co ((Rα ∘ ℰP.p₂) ∘co (K ∘ ℰP.p₂))
    ≈˘⟨ CoK.assoc _ _ _ ⟩
      ((cA ∘ Φ⦅b⦆) ∘co (Rα ∘ ℰP.p₂)) ∘co (K ∘ ℰP.p₂)
    ≈⟨ CoK.∘-cong step₁ ≈-refl ⟩
      (cA ∘ fmorη Γ (F^ μ̂) (FM.Mor-∘ ⦅b⦆ (pairη Γ (F^ μ̂) (FM.Mor-∘ (FMu.α P̂ δ̂) p₂F)))) ∘co (K ∘ ℰP.p₂)
    ≈⟨ CoK.∘-cong (∘-cong ≈-refl (fmorη-cong (FM.hasMuLaws .FM.HasMuLaws.⦅⦆-β (bF a)))) ≈-refl ⟩
      (cA ∘ fmorη Γ (F^ μ̂) (FM.Mor-∘ (bF a) (pairη Γ (F^ μ̂) sfB))) ∘co (K ∘ ℰP.p₂)
    ≈⟨ CoK.∘-cong (∘-cong ≈-refl (fmorη-∘co Γ (F^ μ̂) (bF a) sfB)) ≈-refl ⟩
      (cA ∘ (fmorη Γ (F^ (η .fobj A)) (bF a) ∘co fmorη Γ (F^ μ̂) sfB)) ∘co (K ∘ ℰP.p₂)
    ≈˘⟨ CoK.∘-cong (assoc _ _ _) ≈-refl ⟩
      ((cA ∘ fmorη Γ (F^ (η .fobj A)) (bF a)) ∘co fmorη Γ (F^ μ̂) sfB) ∘co (K ∘ ℰP.p₂)
    ≈⟨ CoK.∘-cong (CoK.∘-cong (absorb (F^ (η .fobj A)) a) ≈-refl) ≈-refl ⟩
      (a ∘co fmorη Γ (F^ μ̂) sfB) ∘co (K ∘ ℰP.p₂)
    ≈⟨ CoK.assoc _ _ _ ⟩
      a ∘co (fmorη Γ (F^ μ̂) sfB ∘co (K ∘ ℰP.p₂))
    ≈⟨ CoK.∘-cong ≈-refl (key ⦅b⦆ (foldR a) (≈-sym (foldR-real a))) ⟩
      a ∘co Gmap P δ̂ (foldR a)
    ∎
    where
      open ≈-Reasoning isEquiv

      ⦅b⦆ = FMu.⦅_⦆ {P = P̂} {δ = δ̂} (bF a)
      cA = realise-η-iso A .Iso.fwd
      Φ⦅b⦆ = fmorη Γ μ̂ ⦅b⦆
      Rα = realise .fmor (FMu.α P̂ δ̂)
      K = collapseP P (extend δ̂ (η .fobj (Creal P δ̂))) (extend δ̂ μ̂) inIsos .Iso.fwd
      p₂F = FM.Fam𝒞-P.p₂ {x = η .fobj Γ} {y = F^ μ̂}
      sfB = FMu.strong-fmor P̂ (FMu.strong-extend-mor (λ i → FM.Fam𝒞-P.p₂) ⦅b⦆)

      split : (inR ∘ ℰP.p₂) ≈ ((Rα ∘ ℰP.p₂) ∘co (K ∘ ℰP.p₂))
      split = ≈-sym (co-pure Rα K)

      step₁ : ((cA ∘ Φ⦅b⦆) ∘co (Rα ∘ ℰP.p₂))
              ≈ (cA ∘ fmorη Γ (F^ μ̂) (FM.Mor-∘ ⦅b⦆ (pairη Γ (F^ μ̂) (FM.Mor-∘ (FMu.α P̂ δ̂) p₂F))))
      step₁ =
        ≈-trans (assoc _ _ _)
          (∘-cong ≈-refl
            (≈-sym (≈-trans (fmorη-∘co Γ (F^ μ̂) ⦅b⦆ (FM.Mor-∘ (FMu.α P̂ δ̂) p₂F))
              (CoK.∘-cong ≈-refl (fmorη-pure Γ (F^ μ̂) (FMu.α P̂ δ̂))))))

  foldR-η : ∀ {Γ A} (a : ℰP.prod Γ (Greal P δ̂ A) ⇒ A) (h : ℰP.prod Γ (Creal P δ̂) ⇒ A) →
            ((h ∘co (inR ∘ ℰP.p₂)) ≈ (a ∘co Gmap P δ̂ h)) → h ≈ foldR a
  foldR-η {Γ} {A} a h square =
    ≈-trans (≈-sym (≈-trans (assoc _ _ _) (≈-trans (∘-cong ≈-refl (prodη Γ μ̂ .Iso.fwd∘bwd≈id)) id-right)))
      (≈-trans (∘-cong (≈-sym (FR.transpose-untranspose _)) ≈-refl)
        (∘-cong (FR.transpose-cong famSquare') ≈-refl))
    where
      ĥ = untranspose (h ∘ prodη Γ μ̂ .Iso.fwd)
      cA = realise-η-iso A .Iso.fwd
      Rα = realise .fmor (FMu.α P̂ δ̂)
      Kiso = collapseP P (extend δ̂ (η .fobj (Creal P δ̂))) (extend δ̂ μ̂) inIsos
      p₂F = FM.Fam𝒞-P.p₂ {x = η .fobj Γ} {y = F^ μ̂}
      sfH = FMu.strong-fmor P̂ (FMu.strong-extend-mor (λ i → FM.Fam𝒞-P.p₂) ĥ)

      hypĥ : (cA ∘ fmorη Γ μ̂ ĥ) ≈ h
      hypĥ = absorb μ̂ h

      -- The given square, with the collapse cancelled and the algebra map bare.
      square' : (h ∘co (Rα ∘ ℰP.p₂)) ≈ (a ∘co fmorη Γ (F^ μ̂) sfH)
      square' =
        begin
          h ∘co (Rα ∘ ℰP.p₂)
        ≈˘⟨ co-iso-cancel Kiso (≈-trans (≈-trans (CoK.assoc _ _ _) (CoK.∘-cong ≈-refl (co-pure {Γ = Γ} Rα (Kiso .Iso.fwd)))) square) ⟩
          (a ∘co Gmap P δ̂ h) ∘co (Kiso .Iso.bwd ∘ ℰP.p₂)
        ≈⟨ CoK.assoc _ _ _ ⟩
          a ∘co (Gmap P δ̂ h ∘co (Kiso .Iso.bwd ∘ ℰP.p₂))
        ≈⟨ CoK.∘-cong ≈-refl (co-iso-cancel Kiso (key ĥ h hypĥ)) ⟩
          a ∘co fmorη Γ (F^ μ̂) sfH
        ∎ where open ≈-Reasoning isEquiv

      famSquare : Category._≈_ FM.cat
                    (FM.Mor-∘ ĥ (pairη Γ (F^ μ̂) (FM.Mor-∘ (FMu.α P̂ δ̂) p₂F)))
                    (FM.Mor-∘ (bF a) (pairη Γ (F^ μ̂) sfH))
      famSquare = fmorη-inj Γ (F^ μ̂) _ _ imgEq
        where
          inner : (cA ∘ (fmorη Γ μ̂ ĥ ∘co (Rα ∘ ℰP.p₂))) ≈ (a ∘co fmorη Γ (F^ μ̂) sfH)
          inner =
            ≈-trans (≈-sym (assoc _ _ _))
              (≈-trans (∘-cong hypĥ ≈-refl) square')

          imgEq : fmorη Γ (F^ μ̂) (FM.Mor-∘ ĥ (pairη Γ (F^ μ̂) (FM.Mor-∘ (FMu.α P̂ δ̂) p₂F)))
                  ≈ fmorη Γ (F^ μ̂) (FM.Mor-∘ (bF a) (pairη Γ (F^ μ̂) sfH))
          imgEq =
            begin
              fmorη Γ (F^ μ̂) (FM.Mor-∘ ĥ (pairη Γ (F^ μ̂) (FM.Mor-∘ (FMu.α P̂ δ̂) p₂F)))
            ≈⟨ ≈-trans (fmorη-∘co Γ (F^ μ̂) ĥ _) (CoK.∘-cong ≈-refl (fmorη-pure Γ (F^ μ̂) (FMu.α P̂ δ̂))) ⟩
              fmorη Γ μ̂ ĥ ∘co (Rα ∘ ℰP.p₂)
            ≈⟨ iso-shuffle (realise-η-iso A) _ _ inner ⟩
              realise-η-iso A .Iso.bwd ∘ (a ∘co fmorη Γ (F^ μ̂) sfH)
            ≈˘⟨ assoc _ _ _ ⟩
              (realise-η-iso A .Iso.bwd ∘ a) ∘co fmorη Γ (F^ μ̂) sfH
            ≈˘⟨ CoK.∘-cong (iso-shuffle (realise-η-iso A) _ _ (absorb (F^ (η .fobj A)) a)) ≈-refl ⟩
              fmorη Γ (F^ (η .fobj A)) (bF a) ∘co fmorη Γ (F^ μ̂) sfH
            ≈˘⟨ fmorη-∘co Γ (F^ μ̂) (bF a) sfH ⟩
              fmorη Γ (F^ μ̂) (FM.Mor-∘ (bF a) (pairη Γ (F^ μ̂) sfH))
            ∎ where open ≈-Reasoning isEquiv

      famSquare' : Category._≈_ FM.cat ĥ (FMu.⦅_⦆ {P = P̂} {δ = δ̂} (bF a))
      famSquare' = FM.hasMuLaws .FM.HasMuLaws.⦅⦆-η (bF a) ĥ famSquare
