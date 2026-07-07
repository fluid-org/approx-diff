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
         HasStrongCoproducts; HasCoproducts; strong-coproducts→coproducts; coKleisli-prod)
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
  module FamC = Category FM.cat
  module FamCoK {Γ̂ : FM.Obj} = Category (coKleisli-prod FM.products Γ̂)
  module FMuI = polynomial-functor-2.MuIso (FM.terminal ℰT) FM.products FM.strongCoproducts FM.hasMu FM.hasMuLaws

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

-- Move an isomorphism across an equation, and cancel one.
iso-mono : ∀ {X Y Z : obj} (I : Iso Y Z) {f g : X ⇒ Y} →
           (I .Iso.fwd ∘ f) ≈ (I .Iso.fwd ∘ g) → f ≈ g
iso-mono I {f} {g} eq =
  ≈-trans (iso-shuffle I _ _ eq)
    (≈-trans (≈-sym (assoc _ _ _)) (≈-trans (∘-cong (I .Iso.bwd∘fwd≈id) ≈-refl) id-left))

-- Realising a morphism transposed to Fam(ℰ) and collapsing recovers it.
absorb : ∀ {Γ A : obj} (X : FM.Obj) (g : ℰP.prod Γ (realise .fobj X) ⇒ A) →
         (realise-η-iso A .Iso.fwd ∘ fmorη Γ X (untranspose (g ∘ prodη Γ X .Iso.fwd))) ≈ g
absorb {Γ} {A} X g =
  ≈-trans (counit-fmorη Γ X _)
    (≈-trans (assoc _ _ _)
      (≈-trans (∘-cong ≈-refl (prodη Γ X .Iso.fwd∘bwd≈id)) id-right))

-- Transpose a context morphism between plain objects into Fam(ℰ), correcting
-- the domain by the counit.
ctxη : ∀ (Γ A₀ : obj) {A : obj} → (ℰP.prod Γ A₀ ⇒ A) →
       FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) (η .fobj A₀)) (η .fobj A)
ctxη Γ A₀ h = untranspose
  (h ∘ (ℰP.prod-m (id _) (realise-η-iso A₀ .Iso.fwd) ∘ prodη Γ (η .fobj A₀) .Iso.fwd))

ctxη-counit : ∀ (Γ A₀ : obj) {A : obj} (h : ℰP.prod Γ A₀ ⇒ A) →
              (realise-η-iso A .Iso.fwd ∘ fmorη Γ (η .fobj A₀) (ctxη Γ A₀ h))
              ≈ (h ∘ ℰP.prod-m (id _) (realise-η-iso A₀ .Iso.fwd))
ctxη-counit Γ A₀ {A} h =
  ≈-trans (∘-cong ≈-refl (fmorη-cong (FR.untranspose-cong (≈-sym (assoc _ _ _)))))
    (≈-trans (absorb (η .fobj A₀) (h ∘ ℰP.prod-m (id _) (realise-η-iso A₀ .Iso.fwd))) ≈-refl)

-- The strong functorial action of the realised endofunctor: transpose the
-- context morphism to Fam(ℰ), act there, and realise.
Gmap : ∀ {n} (P : Poly ℰ (suc n)) (δ̂ : Fin n → FM.Obj) {Γ A B} →
       (ℰP.prod Γ A ⇒ B) → ℰP.prod Γ (Greal P δ̂ A) ⇒ Greal P δ̂ B
Gmap P δ̂ {Γ} {A} {B} h =
  realise .fmor
    (FMu.strong-fmor (Poly-map η P) (FMu.strong-extend-mor (λ i → FM.Fam𝒞-P.p₂) (ctxη Γ A h)))
    ∘ prodη Γ (FM.fobj FM.μObj (Poly-map η P) (extend δ̂ (η .fobj A))) .Iso.bwd

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




-- Componentwise naturality squares for identity and projection components.
sq-refl : ∀ {Γ : obj} {X̂ Ŷ : FM.Obj} (u : FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) X̂) Ŷ) →
          (fmorη Γ X̂ u ∘co (Iso-refl .Iso.fwd ∘ ℰP.p₂)) ≈ (Iso-refl .Iso.fwd ∘ fmorη Γ X̂ u)
sq-refl {Γ} {X̂} u =
  ≈-trans (∘-cong ≈-refl (ℰP.pair-cong ≈-refl id-left))
    (≈-trans (∘-cong ≈-refl pair-p₁p₂-id) (≈-trans id-right (≈-sym id-left)))

sq-p₂ : ∀ {Γ : obj} {X̂ Ŷ : FM.Obj} (I : Iso (realise .fobj X̂) (realise .fobj Ŷ)) →
        (fmorη Γ Ŷ (FM.Fam𝒞-P.p₂ {x = η .fobj Γ} {y = Ŷ}) ∘co (I .Iso.fwd ∘ ℰP.p₂))
        ≈ (I .Iso.fwd ∘ fmorη Γ X̂ (FM.Fam𝒞-P.p₂ {x = η .fobj Γ} {y = X̂}))
sq-p₂ {Γ} {X̂} {Ŷ} I =
  ≈-trans (CoK.∘-cong (fmorη-p₂ Γ Ŷ) ≈-refl)
    (≈-trans CoK.id-left (≈-sym (∘-cong ≈-refl (fmorη-p₂ Γ X̂))))


-- The collapse interface for a polynomial: realisation of its application is
-- invariant under replacing environment entries by families with isomorphic
-- realisations, naturally in the strong action, and trivially so at identical
-- environments.
record CollapseAt {n} (P : Poly ℰ n) : Set (o ⊔ m ⊔ e ⊔ Level.suc os ⊔ Level.suc es) where
  field
    iso : (δ̂₁ δ̂₂ : Fin n → FM.Obj) →
          (∀ i → Iso (realise .fobj (δ̂₁ i)) (realise .fobj (δ̂₂ i))) →
          Iso (realise .fobj (FM.fobj FM.μObj (Poly-map η P) δ̂₁))
              (realise .fobj (FM.fobj FM.μObj (Poly-map η P) δ̂₂))
    natural : ∀ {Γ : obj} {ε̂₁ ε̂₂ : Fin n → FM.Obj}
              (δ̂₁ δ̂₂ : Fin n → FM.Obj)
              (isosδ : ∀ i → Iso (realise .fobj (δ̂₁ i)) (realise .fobj (δ̂₂ i)))
              (isosε : ∀ i → Iso (realise .fobj (ε̂₁ i)) (realise .fobj (ε̂₂ i)))
              (gs₁ : ∀ i → FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) (δ̂₁ i)) (ε̂₁ i))
              (gs₂ : ∀ i → FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) (δ̂₂ i)) (ε̂₂ i)) →
              (∀ i → (fmorη Γ (δ̂₂ i) (gs₂ i) ∘co (isosδ i .Iso.fwd ∘ ℰP.p₂))
                     ≈ (isosε i .Iso.fwd ∘ fmorη Γ (δ̂₁ i) (gs₁ i))) →
              (fmorη Γ (FM.fobj FM.μObj (Poly-map η P) δ̂₂) (FMu.strong-fmor (Poly-map η P) gs₂)
                ∘co (iso δ̂₁ δ̂₂ isosδ .Iso.fwd ∘ ℰP.p₂))
              ≈ (iso _ _ isosε .Iso.fwd ∘ fmorη Γ (FM.fobj FM.μObj (Poly-map η P) δ̂₁) (FMu.strong-fmor (Poly-map η P) gs₁))
    refl-iso : ∀ (δ̂ : Fin n → FM.Obj)
               (isos : ∀ i → Iso (realise .fobj (δ̂ i)) (realise .fobj (δ̂ i))) →
               (∀ i → isos i .Iso.fwd ≈ id _) →
               iso δ̂ δ̂ isos .Iso.fwd ≈ id _
    comp : ∀ (δ̂₁ δ̂₂ δ̂₃ : Fin n → FM.Obj)
           (isos₁₂ : ∀ i → Iso (realise .fobj (δ̂₁ i)) (realise .fobj (δ̂₂ i)))
           (isos₂₃ : ∀ i → Iso (realise .fobj (δ̂₂ i)) (realise .fobj (δ̂₃ i))) →
           iso δ̂₁ δ̂₃ (λ i → Iso-trans (isos₁₂ i) (isos₂₃ i)) .Iso.fwd
           ≈ (iso δ̂₂ δ̂₃ isos₂₃ .Iso.fwd ∘ iso δ̂₁ δ̂₂ isos₁₂ .Iso.fwd)

-- The realised strong action is a co-Kleisli functor.
private
  ctxη-p₂ : ∀ (Γ A : obj) → Category._≈_ FM.cat (ctxη Γ A ℰP.p₂) (FM.Fam𝒞-P.p₂ {x = η .fobj Γ} {y = η .fobj A})
  ctxη-p₂ Γ A = fmorη-inj Γ (η .fobj A) _ _
    (iso-mono (realise-η-iso A)
      (≈-trans (ctxη-counit Γ A ℰP.p₂)
        (≈-trans (ℰP.pair-p₂ _ _)
          (≈-sym (∘-cong ≈-refl (fmorη-p₂ Γ (η .fobj A)))))))

  ctxη-∘co : ∀ (Γ A B C₀ : obj) (h₂ : ℰP.prod Γ B ⇒ C₀) (h₁ : ℰP.prod Γ A ⇒ B) →
             Category._≈_ FM.cat (ctxη Γ A (h₂ ∘co h₁))
               (FM.Mor-∘ (ctxη Γ B h₂) (pairη Γ (η .fobj A) (ctxη Γ A h₁)))
  ctxη-∘co Γ A B C₀ h₂ h₁ = fmorη-inj Γ (η .fobj A) _ _
    (iso-mono (realise-η-iso C₀) (≈-trans lhs (≈-sym rhs)))
    where
      lhs : (realise-η-iso C₀ .Iso.fwd ∘ fmorη Γ (η .fobj A) (ctxη Γ A (h₂ ∘co h₁)))
            ≈ (h₂ ∘ ℰP.pair ℰP.p₁ (h₁ ∘ ℰP.prod-m (id _) (realise-η-iso A .Iso.fwd)))
      lhs =
        begin
          realise-η-iso C₀ .Iso.fwd ∘ fmorη Γ (η .fobj A) (ctxη Γ A (h₂ ∘co h₁))
        ≈⟨ ctxη-counit Γ A (h₂ ∘co h₁) ⟩
          (h₂ ∘ ℰP.pair ℰP.p₁ h₁) ∘ ℰP.prod-m (id _) (realise-η-iso A .Iso.fwd)
        ≈⟨ assoc _ _ _ ⟩
          h₂ ∘ (ℰP.pair ℰP.p₁ h₁ ∘ ℰP.prod-m (id _) (realise-η-iso A .Iso.fwd))
        ≈⟨ ∘-cong ≈-refl (ℰP.pair-natural _ _ _) ⟩
          h₂ ∘ ℰP.pair (ℰP.p₁ ∘ ℰP.prod-m (id _) (realise-η-iso A .Iso.fwd)) (h₁ ∘ ℰP.prod-m (id _) (realise-η-iso A .Iso.fwd))
        ≈⟨ ∘-cong ≈-refl (ℰP.pair-cong (≈-trans (ℰP.pair-p₁ _ _) id-left) ≈-refl) ⟩
          h₂ ∘ ℰP.pair ℰP.p₁ (h₁ ∘ ℰP.prod-m (id _) (realise-η-iso A .Iso.fwd))
        ∎ where open ≈-Reasoning isEquiv

      rhs : (realise-η-iso C₀ .Iso.fwd ∘ fmorη Γ (η .fobj A) (FM.Mor-∘ (ctxη Γ B h₂) (pairη Γ (η .fobj A) (ctxη Γ A h₁))))
            ≈ (h₂ ∘ ℰP.pair ℰP.p₁ (h₁ ∘ ℰP.prod-m (id _) (realise-η-iso A .Iso.fwd)))
      rhs =
        begin
          realise-η-iso C₀ .Iso.fwd ∘ fmorη Γ (η .fobj A) (FM.Mor-∘ (ctxη Γ B h₂) (pairη Γ (η .fobj A) (ctxη Γ A h₁)))
        ≈⟨ ∘-cong ≈-refl (fmorη-∘co Γ (η .fobj A) (ctxη Γ B h₂) (ctxη Γ A h₁)) ⟩
          realise-η-iso C₀ .Iso.fwd ∘ (fmorη Γ (η .fobj B) (ctxη Γ B h₂) ∘ ℰP.pair ℰP.p₁ (fmorη Γ (η .fobj A) (ctxη Γ A h₁)))
        ≈˘⟨ assoc _ _ _ ⟩
          (realise-η-iso C₀ .Iso.fwd ∘ fmorη Γ (η .fobj B) (ctxη Γ B h₂)) ∘ ℰP.pair ℰP.p₁ (fmorη Γ (η .fobj A) (ctxη Γ A h₁))
        ≈⟨ ∘-cong (ctxη-counit Γ B h₂) ≈-refl ⟩
          (h₂ ∘ ℰP.prod-m (id _) (realise-η-iso B .Iso.fwd)) ∘ ℰP.pair ℰP.p₁ (fmorη Γ (η .fobj A) (ctxη Γ A h₁))
        ≈⟨ assoc _ _ _ ⟩
          h₂ ∘ (ℰP.prod-m (id _) (realise-η-iso B .Iso.fwd) ∘ ℰP.pair ℰP.p₁ (fmorη Γ (η .fobj A) (ctxη Γ A h₁)))
        ≈⟨ ∘-cong ≈-refl (ℰP.pair-compose _ _ _ _) ⟩
          h₂ ∘ ℰP.pair (id _ ∘ ℰP.p₁) (realise-η-iso B .Iso.fwd ∘ fmorη Γ (η .fobj A) (ctxη Γ A h₁))
        ≈⟨ ∘-cong ≈-refl (ℰP.pair-cong id-left (ctxη-counit Γ A h₁)) ⟩
          h₂ ∘ ℰP.pair ℰP.p₁ (h₁ ∘ ℰP.prod-m (id _) (realise-η-iso A .Iso.fwd))
        ∎ where open ≈-Reasoning isEquiv

Gmap-id : ∀ {n} (P : Poly ℰ (suc n)) (δ̂ : Fin n → FM.Obj) {Γ A : obj} →
          Gmap P δ̂ {Γ} {A} {A} ℰP.p₂ ≈ ℰP.p₂
Gmap-id P δ̂ {Γ} {A} =
  ≈-trans (fmorη-cong (FMuI.strong-fmor-cong (Poly-map η P) eqs))
    (≈-trans (fmorη-cong (FMuI.strong-fmor-p₂ (Poly-map η P)))
      (fmorη-p₂ Γ (FM.fobj FM.μObj (Poly-map η P) (extend δ̂ (η .fobj A)))))
  where
    eqs : ∀ i → Category._≈_ FM.cat
           (FMu.strong-extend-mor (λ j → FM.Fam𝒞-P.p₂) (ctxη Γ A ℰP.p₂) i)
           (FM.Fam𝒞-P.p₂ {x = η .fobj Γ} {y = extend δ̂ (η .fobj A) i})
    eqs Fin.zero    = ctxη-p₂ Γ A
    eqs (Fin.suc i) = FamC.≈-refl

Gmap-∘co : ∀ {n} (P : Poly ℰ (suc n)) (δ̂ : Fin n → FM.Obj) {Γ A B C₀ : obj}
           (h₂ : ℰP.prod Γ B ⇒ C₀) (h₁ : ℰP.prod Γ A ⇒ B) →
           Gmap P δ̂ (h₂ ∘co h₁) ≈ (Gmap P δ̂ h₂ ∘co Gmap P δ̂ h₁)
Gmap-∘co P δ̂ {Γ} {A} {B} {C₀} h₂ h₁ =
  ≈-trans (fmorη-cong (FMuI.strong-fmor-cong (Poly-map η P) eqs))
    (≈-trans (fmorη-cong (FamC.≈-sym (FMuI.strong-fmor-comp (Poly-map η P) _ _)))
      (fmorη-∘co Γ (FM.fobj FM.μObj (Poly-map η P) (extend δ̂ (η .fobj A)))
        (FMu.strong-fmor (Poly-map η P) (FMu.strong-extend-mor (λ i → FM.Fam𝒞-P.p₂) (ctxη Γ B h₂)))
        (FMu.strong-fmor (Poly-map η P) (FMu.strong-extend-mor (λ i → FM.Fam𝒞-P.p₂) (ctxη Γ A h₁)))))
  where
    eqs : ∀ i → Category._≈_ FM.cat
           (FMu.strong-extend-mor (λ j → FM.Fam𝒞-P.p₂) (ctxη Γ A (h₂ ∘co h₁)) i)
           (FM.Mor-∘ (FMu.strong-extend-mor (λ j → FM.Fam𝒞-P.p₂) (ctxη Γ B h₂) i)
             (FM.Fam𝒞-P.pair FM.Fam𝒞-P.p₁ (FMu.strong-extend-mor (λ j → FM.Fam𝒞-P.p₂) (ctxη Γ A h₁) i)))
    eqs Fin.zero    = ctxη-∘co Γ A B C₀ h₂ h₁
    eqs (Fin.suc i) = FamC.≈-sym FamCoK.id-left

-- The collapse interface at constants and variables.
collapse-const : ∀ {n} (A : Category.obj ℰ) → CollapseAt {n} (polynomial-functor-2.Poly.const A)
collapse-const A .CollapseAt.iso δ̂₁ δ̂₂ isos = Iso-refl
collapse-const A .CollapseAt.natural δ̂₁ δ̂₂ isosδ isosε gs₁ gs₂ sqs = sq-refl _
collapse-const A .CollapseAt.refl-iso δ̂ isos hyps = ≈-refl
collapse-const A .CollapseAt.comp δ̂₁ δ̂₂ δ̂₃ isos₁₂ isos₂₃ = ≈-sym id-left

collapse-var : ∀ {n} (i : Fin n) → CollapseAt {n} (polynomial-functor-2.Poly.var i)
collapse-var i .CollapseAt.iso δ̂₁ δ̂₂ isos = isos i
collapse-var i .CollapseAt.natural δ̂₁ δ̂₂ isosδ isosε gs₁ gs₂ sqs = sqs i
collapse-var i .CollapseAt.refl-iso δ̂ isos hyps = hyps i
collapse-var i .CollapseAt.comp δ̂₁ δ̂₂ δ̂₃ isos₁₂ isos₂₃ = ≈-refl


-- Coproduct machinery for the sum case of the collapse.
private
  ℰCP = strong-coproducts→coproducts ℰT ℰSC
  module ℰCPm = HasCoproducts ℰCP
  module ℰSCm = HasStrongCoproducts ℰSC
  module FSC = HasStrongCoproducts FM.strongCoproducts
  module FCP = HasCoproducts FM.coproducts

  K⊕ : ∀ (X̂ Ŷ : FM.Obj) → Iso (realise .fobj (FCP.coprod X̂ Ŷ))
                              (ℰCPm.coprod (realise .fobj X̂) (realise .fobj Ŷ))
  K⊕ X̂ Ŷ = FR.realise-coproducts-iso ℰCP X̂ Ŷ

  K⊕-in₁ : ∀ (X̂ Ŷ : FM.Obj) → (K⊕ X̂ Ŷ .Iso.bwd ∘ ℰSCm.in₁) ≈ realise .fmor FCP.in₁
  K⊕-in₁ X̂ Ŷ = ℰCPm.copair-in₁ _ _

  K⊕-in₂ : ∀ (X̂ Ŷ : FM.Obj) → (K⊕ X̂ Ŷ .Iso.bwd ∘ ℰSCm.in₂) ≈ realise .fmor FCP.in₂
  K⊕-in₂ X̂ Ŷ = ℰCPm.copair-in₂ _ _

-- Postcomposition with a pure morphism under realisation in context.
fmorη-post : ∀ (Γ : obj) (X : FM.Obj) {Y Z : FM.Obj} (w : FM.Mor Y Z)
             (u : FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) X) Y) →
             fmorη Γ X (FM.Mor-∘ w u) ≈ (realise .fmor w ∘ fmorη Γ X u)
fmorη-post Γ X w u =
  ≈-trans (∘-cong (realise .fmor-comp _ _) ≈-refl) (assoc _ _ _)

-- Cancel an isomorphism applied backwards in context on the right.
co-iso-epi : ∀ {Γ X Y Z : obj} (I : Iso X Y)
             {u v : ℰP.prod Γ X ⇒ Z} →
             ((u ∘co (I .Iso.bwd ∘ ℰP.p₂)) ≈ (v ∘co (I .Iso.bwd ∘ ℰP.p₂))) → u ≈ v
co-iso-epi I {u} {v} eq =
  begin
    u
  ≈˘⟨ CoK.id-right ⟩
    u ∘co ℰP.p₂
  ≈˘⟨ CoK.∘-cong ≈-refl (≈-trans (co-pure _ _) (≈-trans (∘-cong (I .Iso.bwd∘fwd≈id) ≈-refl) id-left)) ⟩
    u ∘co ((I .Iso.bwd ∘ ℰP.p₂) ∘co (I .Iso.fwd ∘ ℰP.p₂))
  ≈˘⟨ CoK.assoc _ _ _ ⟩
    (u ∘co (I .Iso.bwd ∘ ℰP.p₂)) ∘co (I .Iso.fwd ∘ ℰP.p₂)
  ≈⟨ CoK.∘-cong eq ≈-refl ⟩
    (v ∘co (I .Iso.bwd ∘ ℰP.p₂)) ∘co (I .Iso.fwd ∘ ℰP.p₂)
  ≈⟨ CoK.assoc _ _ _ ⟩
    v ∘co ((I .Iso.bwd ∘ ℰP.p₂) ∘co (I .Iso.fwd ∘ ℰP.p₂))
  ≈⟨ CoK.∘-cong ≈-refl (≈-trans (co-pure _ _) (≈-trans (∘-cong (I .Iso.bwd∘fwd≈id) ≈-refl) id-left)) ⟩
    v ∘co ℰP.p₂
  ≈⟨ CoK.id-right ⟩
    v
  ∎ where open ≈-Reasoning isEquiv

private
  K⊕-in₁' : ∀ (X̂ Ŷ : FM.Obj) → (K⊕ X̂ Ŷ .Iso.fwd ∘ realise .fmor FCP.in₁) ≈ ℰSCm.in₁
  K⊕-in₁' X̂ Ŷ =
    ≈-trans (∘-cong ≈-refl (≈-sym (K⊕-in₁ X̂ Ŷ)))
      (≈-trans (≈-sym (assoc _ _ _)) (≈-trans (∘-cong (K⊕ X̂ Ŷ .Iso.fwd∘bwd≈id) ≈-refl) id-left))

  K⊕-in₂' : ∀ (X̂ Ŷ : FM.Obj) → (K⊕ X̂ Ŷ .Iso.fwd ∘ realise .fmor FCP.in₂) ≈ ℰSCm.in₂
  K⊕-in₂' X̂ Ŷ =
    ≈-trans (∘-cong ≈-refl (≈-sym (K⊕-in₂ X̂ Ŷ)))
      (≈-trans (≈-sym (assoc _ _ _)) (≈-trans (∘-cong (K⊕ X̂ Ŷ .Iso.fwd∘bwd≈id) ≈-refl) id-left))

  -- Strong copair against a coproduct of morphisms, in context.
  scopair-coprod-m : ∀ {Γ X₁ X₂ Y₁ Y₂ Z : obj}
                     (a : ℰP.prod Γ Y₁ ⇒ Z) (b : ℰP.prod Γ Y₂ ⇒ Z)
                     (f : X₁ ⇒ Y₁) (g : X₂ ⇒ Y₂) →
                     (ℰSCm.copair a b ∘co (ℰCPm.coprod-m f g ∘ ℰP.p₂))
                     ≈ ℰSCm.copair (a ∘co (f ∘ ℰP.p₂)) (b ∘co (g ∘ ℰP.p₂))
  scopair-coprod-m {Γ} a b f g =
    ≈-trans (≈-sym (ℰSCm.copair-ext _)) (ℰSCm.copair-cong c₁ c₂)
    where
      c₁ : ((ℰSCm.copair a b ∘co (ℰCPm.coprod-m f g ∘ ℰP.p₂)) ∘ ℰP.pair ℰP.p₁ (ℰSCm.in₁ ∘ ℰP.p₂))
           ≈ (a ∘co (f ∘ ℰP.p₂))
      c₁ =
        begin
          (ℰSCm.copair a b ∘co (ℰCPm.coprod-m f g ∘ ℰP.p₂)) ∘co (ℰSCm.in₁ ∘ ℰP.p₂)
        ≈⟨ CoK.assoc _ _ _ ⟩
          ℰSCm.copair a b ∘co ((ℰCPm.coprod-m f g ∘ ℰP.p₂) ∘co (ℰSCm.in₁ ∘ ℰP.p₂))
        ≈⟨ CoK.∘-cong ≈-refl (co-pure _ _) ⟩
          ℰSCm.copair a b ∘co ((ℰCPm.coprod-m f g ∘ ℰSCm.in₁) ∘ ℰP.p₂)
        ≈⟨ CoK.∘-cong ≈-refl (∘-cong (ℰCPm.copair-in₁ _ _) ≈-refl) ⟩
          ℰSCm.copair a b ∘co ((ℰSCm.in₁ ∘ f) ∘ ℰP.p₂)
        ≈˘⟨ CoK.∘-cong ≈-refl (co-pure _ _) ⟩
          ℰSCm.copair a b ∘co ((ℰSCm.in₁ ∘ ℰP.p₂) ∘co (f ∘ ℰP.p₂))
        ≈˘⟨ CoK.assoc _ _ _ ⟩
          (ℰSCm.copair a b ∘co (ℰSCm.in₁ ∘ ℰP.p₂)) ∘co (f ∘ ℰP.p₂)
        ≈⟨ CoK.∘-cong (ℰSCm.copair-in₁ a b) ≈-refl ⟩
          a ∘co (f ∘ ℰP.p₂)
        ∎ where open ≈-Reasoning isEquiv

      c₂ : ((ℰSCm.copair a b ∘co (ℰCPm.coprod-m f g ∘ ℰP.p₂)) ∘ ℰP.pair ℰP.p₁ (ℰSCm.in₂ ∘ ℰP.p₂))
           ≈ (b ∘co (g ∘ ℰP.p₂))
      c₂ =
        begin
          (ℰSCm.copair a b ∘co (ℰCPm.coprod-m f g ∘ ℰP.p₂)) ∘co (ℰSCm.in₂ ∘ ℰP.p₂)
        ≈⟨ CoK.assoc _ _ _ ⟩
          ℰSCm.copair a b ∘co ((ℰCPm.coprod-m f g ∘ ℰP.p₂) ∘co (ℰSCm.in₂ ∘ ℰP.p₂))
        ≈⟨ CoK.∘-cong ≈-refl (co-pure _ _) ⟩
          ℰSCm.copair a b ∘co ((ℰCPm.coprod-m f g ∘ ℰSCm.in₂) ∘ ℰP.p₂)
        ≈⟨ CoK.∘-cong ≈-refl (∘-cong (ℰCPm.copair-in₂ _ _) ≈-refl) ⟩
          ℰSCm.copair a b ∘co ((ℰSCm.in₂ ∘ g) ∘ ℰP.p₂)
        ≈˘⟨ CoK.∘-cong ≈-refl (co-pure _ _) ⟩
          ℰSCm.copair a b ∘co ((ℰSCm.in₂ ∘ ℰP.p₂) ∘co (g ∘ ℰP.p₂))
        ≈˘⟨ CoK.assoc _ _ _ ⟩
          (ℰSCm.copair a b ∘co (ℰSCm.in₂ ∘ ℰP.p₂)) ∘co (g ∘ ℰP.p₂)
        ≈⟨ CoK.∘-cong (ℰSCm.copair-in₂ a b) ≈-refl ⟩
          b ∘co (g ∘ ℰP.p₂)
        ∎ where open ≈-Reasoning isEquiv

-- Realisation in context sends the strong copair to the strong copair, across
-- the coproduct comparison iso.
fmorη-scopair : ∀ (Γ : obj) (X̂ Ŷ : FM.Obj) {Ẑ : FM.Obj}
                (u : FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) X̂) Ẑ)
                (v : FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) Ŷ) Ẑ) →
                (fmorη Γ (FCP.coprod X̂ Ŷ) (FSC.copair u v) ∘co (K⊕ X̂ Ŷ .Iso.bwd ∘ ℰP.p₂))
                ≈ ℰSCm.copair (fmorη Γ X̂ u) (fmorη Γ Ŷ v)
fmorη-scopair Γ X̂ Ŷ {Ẑ} u v =
  ≈-trans (≈-sym (ℰSCm.copair-ext _)) (ℰSCm.copair-cong c₁ c₂)
  where
    c₁ : ((fmorη Γ (FCP.coprod X̂ Ŷ) (FSC.copair u v) ∘co (K⊕ X̂ Ŷ .Iso.bwd ∘ ℰP.p₂)) ∘ ℰP.pair ℰP.p₁ (ℰSCm.in₁ ∘ ℰP.p₂))
         ≈ fmorη Γ X̂ u
    c₁ =
      begin
        (fmorη Γ (FCP.coprod X̂ Ŷ) (FSC.copair u v) ∘co (K⊕ X̂ Ŷ .Iso.bwd ∘ ℰP.p₂)) ∘co (ℰSCm.in₁ ∘ ℰP.p₂)
      ≈⟨ CoK.assoc _ _ _ ⟩
        fmorη Γ (FCP.coprod X̂ Ŷ) (FSC.copair u v) ∘co ((K⊕ X̂ Ŷ .Iso.bwd ∘ ℰP.p₂) ∘co (ℰSCm.in₁ ∘ ℰP.p₂))
      ≈⟨ CoK.∘-cong ≈-refl (co-pure _ _) ⟩
        fmorη Γ (FCP.coprod X̂ Ŷ) (FSC.copair u v) ∘co ((K⊕ X̂ Ŷ .Iso.bwd ∘ ℰSCm.in₁) ∘ ℰP.p₂)
      ≈⟨ CoK.∘-cong ≈-refl (∘-cong (K⊕-in₁ X̂ Ŷ) ≈-refl) ⟩
        fmorη Γ (FCP.coprod X̂ Ŷ) (FSC.copair u v) ∘co (realise .fmor FCP.in₁ ∘ ℰP.p₂)
      ≈˘⟨ CoK.∘-cong ≈-refl (fmorη-pure Γ X̂ FCP.in₁) ⟩
        fmorη Γ (FCP.coprod X̂ Ŷ) (FSC.copair u v) ∘co fmorη Γ X̂ (FM.Mor-∘ FCP.in₁ (FM.Fam𝒞-P.p₂ {x = η .fobj Γ} {y = X̂}))
      ≈˘⟨ fmorη-∘co Γ X̂ (FSC.copair u v) _ ⟩
        fmorη Γ X̂ (FM.Mor-∘ (FSC.copair u v) (pairη Γ X̂ (FM.Mor-∘ FCP.in₁ (FM.Fam𝒞-P.p₂ {x = η .fobj Γ} {y = X̂}))))
      ≈⟨ fmorη-cong (FSC.copair-in₁ u v) ⟩
        fmorη Γ X̂ u
      ∎ where open ≈-Reasoning isEquiv

    c₂ : ((fmorη Γ (FCP.coprod X̂ Ŷ) (FSC.copair u v) ∘co (K⊕ X̂ Ŷ .Iso.bwd ∘ ℰP.p₂)) ∘ ℰP.pair ℰP.p₁ (ℰSCm.in₂ ∘ ℰP.p₂))
         ≈ fmorη Γ Ŷ v
    c₂ =
      begin
        (fmorη Γ (FCP.coprod X̂ Ŷ) (FSC.copair u v) ∘co (K⊕ X̂ Ŷ .Iso.bwd ∘ ℰP.p₂)) ∘co (ℰSCm.in₂ ∘ ℰP.p₂)
      ≈⟨ CoK.assoc _ _ _ ⟩
        fmorη Γ (FCP.coprod X̂ Ŷ) (FSC.copair u v) ∘co ((K⊕ X̂ Ŷ .Iso.bwd ∘ ℰP.p₂) ∘co (ℰSCm.in₂ ∘ ℰP.p₂))
      ≈⟨ CoK.∘-cong ≈-refl (co-pure _ _) ⟩
        fmorη Γ (FCP.coprod X̂ Ŷ) (FSC.copair u v) ∘co ((K⊕ X̂ Ŷ .Iso.bwd ∘ ℰSCm.in₂) ∘ ℰP.p₂)
      ≈⟨ CoK.∘-cong ≈-refl (∘-cong (K⊕-in₂ X̂ Ŷ) ≈-refl) ⟩
        fmorη Γ (FCP.coprod X̂ Ŷ) (FSC.copair u v) ∘co (realise .fmor FCP.in₂ ∘ ℰP.p₂)
      ≈˘⟨ CoK.∘-cong ≈-refl (fmorη-pure Γ Ŷ FCP.in₂) ⟩
        fmorη Γ (FCP.coprod X̂ Ŷ) (FSC.copair u v) ∘co fmorη Γ Ŷ (FM.Mor-∘ FCP.in₂ (FM.Fam𝒞-P.p₂ {x = η .fobj Γ} {y = Ŷ}))
      ≈˘⟨ fmorη-∘co Γ Ŷ (FSC.copair u v) _ ⟩
        fmorη Γ Ŷ (FM.Mor-∘ (FSC.copair u v) (pairη Γ Ŷ (FM.Mor-∘ FCP.in₂ (FM.Fam𝒞-P.p₂ {x = η .fobj Γ} {y = Ŷ}))))
      ≈⟨ fmorη-cong (FSC.copair-in₂ u v) ⟩
        fmorη Γ Ŷ v
      ∎ where open ≈-Reasoning isEquiv

-- The collapse interface at sums.
collapse-sum : ∀ {n} {P Q : Poly ℰ n} → CollapseAt P → CollapseAt Q →
               CollapseAt (P polynomial-functor-2.Poly.+ Q)
collapse-sum {n} {P} {Q} CP CQ = record { iso = sumIso ; natural = sumNat ; refl-iso = sumRefl ; comp = sumComp }
  where
    X̂ : (Fin n → FM.Obj) → FM.Obj
    X̂ δ̂ = FM.fobj FM.μObj (Poly-map η P) δ̂

    Ŷ : (Fin n → FM.Obj) → FM.Obj
    Ŷ δ̂ = FM.fobj FM.μObj (Poly-map η Q) δ̂

    sumIso : ∀ δ̂₁ δ̂₂ (isos : ∀ i → Iso (realise .fobj (δ̂₁ i)) (realise .fobj (δ̂₂ i))) →
             Iso (realise .fobj (FCP.coprod (X̂ δ̂₁) (Ŷ δ̂₁))) (realise .fobj (FCP.coprod (X̂ δ̂₂) (Ŷ δ̂₂)))
    sumIso δ̂₁ δ̂₂ isos =
      Iso-trans (K⊕ (X̂ δ̂₁) (Ŷ δ̂₁))
        (Iso-trans (ℰCPm.coproduct-preserve-iso (CP .CollapseAt.iso δ̂₁ δ̂₂ isos) (CQ .CollapseAt.iso δ̂₁ δ̂₂ isos))
          (Iso-sym (K⊕ (X̂ δ̂₂) (Ŷ δ̂₂))))

    -- The composite forward map, with the source comparison iso cancelled.
    sumIso-bwd : ∀ δ̂₁ δ̂₂ isos →
                 (sumIso δ̂₁ δ̂₂ isos .Iso.fwd ∘ K⊕ (X̂ δ̂₁) (Ŷ δ̂₁) .Iso.bwd)
                 ≈ (K⊕ (X̂ δ̂₂) (Ŷ δ̂₂) .Iso.bwd ∘ ℰCPm.coprod-m (CP .CollapseAt.iso δ̂₁ δ̂₂ isos .Iso.fwd) (CQ .CollapseAt.iso δ̂₁ δ̂₂ isos .Iso.fwd))
    sumIso-bwd δ̂₁ δ̂₂ isos =
      ≈-trans (assoc _ _ _)
        (≈-trans (∘-cong ≈-refl (K⊕ (X̂ δ̂₁) (Ŷ δ̂₁) .Iso.fwd∘bwd≈id)) id-right)

    sumRefl : ∀ δ̂ (isos : ∀ i → Iso (realise .fobj (δ̂ i)) (realise .fobj (δ̂ i))) →
              (∀ i → isos i .Iso.fwd ≈ id _) →
              sumIso δ̂ δ̂ isos .Iso.fwd ≈ id _
    sumRefl δ̂ isos hyps =
      begin
        (K⊕ (X̂ δ̂) (Ŷ δ̂) .Iso.bwd ∘ ℰCPm.coprod-m (CP .CollapseAt.iso δ̂ δ̂ isos .Iso.fwd) (CQ .CollapseAt.iso δ̂ δ̂ isos .Iso.fwd)) ∘ K⊕ (X̂ δ̂) (Ŷ δ̂) .Iso.fwd
      ≈⟨ ∘-cong (∘-cong ≈-refl (≈-trans (ℰCPm.coprod-m-cong (CP .CollapseAt.refl-iso δ̂ isos hyps) (CQ .CollapseAt.refl-iso δ̂ isos hyps)) ℰCPm.coprod-m-id)) ≈-refl ⟩
        (K⊕ (X̂ δ̂) (Ŷ δ̂) .Iso.bwd ∘ id _) ∘ K⊕ (X̂ δ̂) (Ŷ δ̂) .Iso.fwd
      ≈⟨ ∘-cong id-right ≈-refl ⟩
        K⊕ (X̂ δ̂) (Ŷ δ̂) .Iso.bwd ∘ K⊕ (X̂ δ̂) (Ŷ δ̂) .Iso.fwd
      ≈⟨ K⊕ (X̂ δ̂) (Ŷ δ̂) .Iso.bwd∘fwd≈id ⟩
        id _
      ∎ where open ≈-Reasoning isEquiv

    sumComp : ∀ δ̂₁ δ̂₂ δ̂₃ (isos₁₂ : ∀ i → Iso (realise .fobj (δ̂₁ i)) (realise .fobj (δ̂₂ i)))
              (isos₂₃ : ∀ i → Iso (realise .fobj (δ̂₂ i)) (realise .fobj (δ̂₃ i))) →
              sumIso δ̂₁ δ̂₃ (λ i → Iso-trans (isos₁₂ i) (isos₂₃ i)) .Iso.fwd
              ≈ (sumIso δ̂₂ δ̂₃ isos₂₃ .Iso.fwd ∘ sumIso δ̂₁ δ̂₂ isos₁₂ .Iso.fwd)
    sumComp δ̂₁ δ̂₂ δ̂₃ isos₁₂ isos₂₃ = ≈-trans toM (≈-sym fromM)
      where
        cm₁₂ = ℰCPm.coprod-m (CP .CollapseAt.iso δ̂₁ δ̂₂ isos₁₂ .Iso.fwd) (CQ .CollapseAt.iso δ̂₁ δ̂₂ isos₁₂ .Iso.fwd)
        cm₂₃ = ℰCPm.coprod-m (CP .CollapseAt.iso δ̂₂ δ̂₃ isos₂₃ .Iso.fwd) (CQ .CollapseAt.iso δ̂₂ δ̂₃ isos₂₃ .Iso.fwd)

        toM : sumIso δ̂₁ δ̂₃ (λ i → Iso-trans (isos₁₂ i) (isos₂₃ i)) .Iso.fwd
              ≈ ((K⊕ (X̂ δ̂₃) (Ŷ δ̂₃) .Iso.bwd ∘ (cm₂₃ ∘ cm₁₂)) ∘ K⊕ (X̂ δ̂₁) (Ŷ δ̂₁) .Iso.fwd)
        toM =
          ∘-cong (∘-cong ≈-refl
            (≈-trans (ℰCPm.coprod-m-cong (CP .CollapseAt.comp δ̂₁ δ̂₂ δ̂₃ isos₁₂ isos₂₃) (CQ .CollapseAt.comp δ̂₁ δ̂₂ δ̂₃ isos₁₂ isos₂₃))
              (ℰCPm.coprod-m-comp _ _ _ _))) ≈-refl

        fromM : (sumIso δ̂₂ δ̂₃ isos₂₃ .Iso.fwd ∘ sumIso δ̂₁ δ̂₂ isos₁₂ .Iso.fwd)
                ≈ ((K⊕ (X̂ δ̂₃) (Ŷ δ̂₃) .Iso.bwd ∘ (cm₂₃ ∘ cm₁₂)) ∘ K⊕ (X̂ δ̂₁) (Ŷ δ̂₁) .Iso.fwd)
        fromM =
          begin
            ((K⊕ (X̂ δ̂₃) (Ŷ δ̂₃) .Iso.bwd ∘ cm₂₃) ∘ K⊕ (X̂ δ̂₂) (Ŷ δ̂₂) .Iso.fwd) ∘ ((K⊕ (X̂ δ̂₂) (Ŷ δ̂₂) .Iso.bwd ∘ cm₁₂) ∘ K⊕ (X̂ δ̂₁) (Ŷ δ̂₁) .Iso.fwd)
          ≈˘⟨ assoc _ _ _ ⟩
            (((K⊕ (X̂ δ̂₃) (Ŷ δ̂₃) .Iso.bwd ∘ cm₂₃) ∘ K⊕ (X̂ δ̂₂) (Ŷ δ̂₂) .Iso.fwd) ∘ (K⊕ (X̂ δ̂₂) (Ŷ δ̂₂) .Iso.bwd ∘ cm₁₂)) ∘ K⊕ (X̂ δ̂₁) (Ŷ δ̂₁) .Iso.fwd
          ≈⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
            ((K⊕ (X̂ δ̂₃) (Ŷ δ̂₃) .Iso.bwd ∘ cm₂₃) ∘ (K⊕ (X̂ δ̂₂) (Ŷ δ̂₂) .Iso.fwd ∘ (K⊕ (X̂ δ̂₂) (Ŷ δ̂₂) .Iso.bwd ∘ cm₁₂))) ∘ K⊕ (X̂ δ̂₁) (Ŷ δ̂₁) .Iso.fwd
          ≈⟨ ∘-cong (∘-cong ≈-refl (≈-trans (≈-sym (assoc _ _ _)) (≈-trans (∘-cong (K⊕ (X̂ δ̂₂) (Ŷ δ̂₂) .Iso.fwd∘bwd≈id) ≈-refl) id-left))) ≈-refl ⟩
            ((K⊕ (X̂ δ̂₃) (Ŷ δ̂₃) .Iso.bwd ∘ cm₂₃) ∘ cm₁₂) ∘ K⊕ (X̂ δ̂₁) (Ŷ δ̂₁) .Iso.fwd
          ≈⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
            (K⊕ (X̂ δ̂₃) (Ŷ δ̂₃) .Iso.bwd ∘ (cm₂₃ ∘ cm₁₂)) ∘ K⊕ (X̂ δ̂₁) (Ŷ δ̂₁) .Iso.fwd
          ∎ where open ≈-Reasoning isEquiv

    sumNat : ∀ {Γ : obj} {ε̂₁ ε̂₂ : Fin n → FM.Obj}
             (δ̂₁ δ̂₂ : Fin n → FM.Obj)
             (isosδ : ∀ i → Iso (realise .fobj (δ̂₁ i)) (realise .fobj (δ̂₂ i)))
             (isosε : ∀ i → Iso (realise .fobj (ε̂₁ i)) (realise .fobj (ε̂₂ i)))
             (gs₁ : ∀ i → FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) (δ̂₁ i)) (ε̂₁ i))
             (gs₂ : ∀ i → FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) (δ̂₂ i)) (ε̂₂ i)) →
             (∀ i → (fmorη Γ (δ̂₂ i) (gs₂ i) ∘co (isosδ i .Iso.fwd ∘ ℰP.p₂))
                    ≈ (isosε i .Iso.fwd ∘ fmorη Γ (δ̂₁ i) (gs₁ i))) →
             (fmorη Γ (FCP.coprod (X̂ δ̂₂) (Ŷ δ̂₂)) (FMu.strong-fmor (Poly-map η (P polynomial-functor-2.Poly.+ Q)) gs₂)
               ∘co (sumIso δ̂₁ δ̂₂ isosδ .Iso.fwd ∘ ℰP.p₂))
             ≈ (sumIso _ _ isosε .Iso.fwd ∘ fmorη Γ (FCP.coprod (X̂ δ̂₁) (Ŷ δ̂₁)) (FMu.strong-fmor (Poly-map η (P polynomial-functor-2.Poly.+ Q)) gs₁))
    sumNat {Γ} {ε̂₁} {ε̂₂} δ̂₁ δ̂₂ isosδ isosε gs₁ gs₂ sqs =
      co-iso-epi (K⊕ (X̂ δ̂₁) (Ŷ δ̂₁)) (≈-trans lhs (≈-sym rhs))
      where
        sfP : ∀ δ̂ ε̂ → (∀ i → FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) (δ̂ i)) (ε̂ i)) → FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) (X̂ δ̂)) (X̂ ε̂)
        sfP δ̂ ε̂ gs = FMu.strong-fmor (Poly-map η P) gs

        sfQ : ∀ δ̂ ε̂ → (∀ i → FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) (δ̂ i)) (ε̂ i)) → FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) (Ŷ δ̂)) (Ŷ ε̂)
        sfQ δ̂ ε̂ gs = FMu.strong-fmor (Poly-map η Q) gs

        mid : ℰP.prod Γ (ℰCPm.coprod (realise .fobj (X̂ δ̂₁)) (realise .fobj (Ŷ δ̂₁))) ⇒ realise .fobj (FCP.coprod (X̂ ε̂₂) (Ŷ ε̂₂))
        mid = ℰSCm.copair
                (realise .fmor FCP.in₁ ∘ (CP .CollapseAt.iso ε̂₁ ε̂₂ isosε .Iso.fwd ∘ fmorη Γ (X̂ δ̂₁) (sfP δ̂₁ ε̂₁ gs₁)))
                (realise .fmor FCP.in₂ ∘ (CQ .CollapseAt.iso ε̂₁ ε̂₂ isosε .Iso.fwd ∘ fmorη Γ (Ŷ δ̂₁) (sfQ δ̂₁ ε̂₁ gs₁)))

        lhs : ((fmorη Γ (FCP.coprod (X̂ δ̂₂) (Ŷ δ̂₂)) (FSC.copair (FM.Mor-∘ FCP.in₁ (sfP δ̂₂ ε̂₂ gs₂)) (FM.Mor-∘ FCP.in₂ (sfQ δ̂₂ ε̂₂ gs₂)))
                ∘co (sumIso δ̂₁ δ̂₂ isosδ .Iso.fwd ∘ ℰP.p₂)) ∘co (K⊕ (X̂ δ̂₁) (Ŷ δ̂₁) .Iso.bwd ∘ ℰP.p₂))
              ≈ mid
        lhs =
          begin
            (fmorη Γ (FCP.coprod (X̂ δ̂₂) (Ŷ δ̂₂)) (FSC.copair (FM.Mor-∘ FCP.in₁ (sfP δ̂₂ ε̂₂ gs₂)) (FM.Mor-∘ FCP.in₂ (sfQ δ̂₂ ε̂₂ gs₂))) ∘co (sumIso δ̂₁ δ̂₂ isosδ .Iso.fwd ∘ ℰP.p₂)) ∘co (K⊕ (X̂ δ̂₁) (Ŷ δ̂₁) .Iso.bwd ∘ ℰP.p₂)
          ≈⟨ CoK.assoc _ _ _ ⟩
            fmorη Γ (FCP.coprod (X̂ δ̂₂) (Ŷ δ̂₂)) (FSC.copair (FM.Mor-∘ FCP.in₁ (sfP δ̂₂ ε̂₂ gs₂)) (FM.Mor-∘ FCP.in₂ (sfQ δ̂₂ ε̂₂ gs₂))) ∘co ((sumIso δ̂₁ δ̂₂ isosδ .Iso.fwd ∘ ℰP.p₂) ∘co (K⊕ (X̂ δ̂₁) (Ŷ δ̂₁) .Iso.bwd ∘ ℰP.p₂))
          ≈⟨ CoK.∘-cong ≈-refl (≈-trans (co-pure _ _) (∘-cong (sumIso-bwd δ̂₁ δ̂₂ isosδ) ≈-refl)) ⟩
            fmorη Γ (FCP.coprod (X̂ δ̂₂) (Ŷ δ̂₂)) (FSC.copair (FM.Mor-∘ FCP.in₁ (sfP δ̂₂ ε̂₂ gs₂)) (FM.Mor-∘ FCP.in₂ (sfQ δ̂₂ ε̂₂ gs₂))) ∘co ((K⊕ (X̂ δ̂₂) (Ŷ δ̂₂) .Iso.bwd ∘ ℰCPm.coprod-m (CP .CollapseAt.iso δ̂₁ δ̂₂ isosδ .Iso.fwd) (CQ .CollapseAt.iso δ̂₁ δ̂₂ isosδ .Iso.fwd)) ∘ ℰP.p₂)
          ≈˘⟨ CoK.∘-cong ≈-refl (co-pure _ _) ⟩
            fmorη Γ (FCP.coprod (X̂ δ̂₂) (Ŷ δ̂₂)) (FSC.copair (FM.Mor-∘ FCP.in₁ (sfP δ̂₂ ε̂₂ gs₂)) (FM.Mor-∘ FCP.in₂ (sfQ δ̂₂ ε̂₂ gs₂))) ∘co ((K⊕ (X̂ δ̂₂) (Ŷ δ̂₂) .Iso.bwd ∘ ℰP.p₂) ∘co (ℰCPm.coprod-m (CP .CollapseAt.iso δ̂₁ δ̂₂ isosδ .Iso.fwd) (CQ .CollapseAt.iso δ̂₁ δ̂₂ isosδ .Iso.fwd) ∘ ℰP.p₂))
          ≈˘⟨ CoK.assoc _ _ _ ⟩
            (fmorη Γ (FCP.coprod (X̂ δ̂₂) (Ŷ δ̂₂)) (FSC.copair (FM.Mor-∘ FCP.in₁ (sfP δ̂₂ ε̂₂ gs₂)) (FM.Mor-∘ FCP.in₂ (sfQ δ̂₂ ε̂₂ gs₂))) ∘co (K⊕ (X̂ δ̂₂) (Ŷ δ̂₂) .Iso.bwd ∘ ℰP.p₂)) ∘co (ℰCPm.coprod-m (CP .CollapseAt.iso δ̂₁ δ̂₂ isosδ .Iso.fwd) (CQ .CollapseAt.iso δ̂₁ δ̂₂ isosδ .Iso.fwd) ∘ ℰP.p₂)
          ≈⟨ CoK.∘-cong (fmorη-scopair Γ (X̂ δ̂₂) (Ŷ δ̂₂) _ _) ≈-refl ⟩
            ℰSCm.copair (fmorη Γ (X̂ δ̂₂) (FM.Mor-∘ FCP.in₁ (sfP δ̂₂ ε̂₂ gs₂))) (fmorη Γ (Ŷ δ̂₂) (FM.Mor-∘ FCP.in₂ (sfQ δ̂₂ ε̂₂ gs₂))) ∘co (ℰCPm.coprod-m (CP .CollapseAt.iso δ̂₁ δ̂₂ isosδ .Iso.fwd) (CQ .CollapseAt.iso δ̂₁ δ̂₂ isosδ .Iso.fwd) ∘ ℰP.p₂)
          ≈⟨ scopair-coprod-m _ _ _ _ ⟩
            ℰSCm.copair (fmorη Γ (X̂ δ̂₂) (FM.Mor-∘ FCP.in₁ (sfP δ̂₂ ε̂₂ gs₂)) ∘co (CP .CollapseAt.iso δ̂₁ δ̂₂ isosδ .Iso.fwd ∘ ℰP.p₂)) (fmorη Γ (Ŷ δ̂₂) (FM.Mor-∘ FCP.in₂ (sfQ δ̂₂ ε̂₂ gs₂)) ∘co (CQ .CollapseAt.iso δ̂₁ δ̂₂ isosδ .Iso.fwd ∘ ℰP.p₂))
          ≈⟨ ℰSCm.copair-cong comp₁ comp₂ ⟩
            mid
          ∎
          where
            open ≈-Reasoning isEquiv

            comp₁ : (fmorη Γ (X̂ δ̂₂) (FM.Mor-∘ FCP.in₁ (sfP δ̂₂ ε̂₂ gs₂)) ∘co (CP .CollapseAt.iso δ̂₁ δ̂₂ isosδ .Iso.fwd ∘ ℰP.p₂))
                    ≈ (realise .fmor FCP.in₁ ∘ (CP .CollapseAt.iso ε̂₁ ε̂₂ isosε .Iso.fwd ∘ fmorη Γ (X̂ δ̂₁) (sfP δ̂₁ ε̂₁ gs₁)))
            comp₁ =
              ≈-trans (CoK.∘-cong (fmorη-post Γ (X̂ δ̂₂) FCP.in₁ _) ≈-refl)
                (≈-trans (assoc _ _ _)
                  (∘-cong ≈-refl (CP .CollapseAt.natural δ̂₁ δ̂₂ isosδ isosε gs₁ gs₂ sqs)))

            comp₂ : (fmorη Γ (Ŷ δ̂₂) (FM.Mor-∘ FCP.in₂ (sfQ δ̂₂ ε̂₂ gs₂)) ∘co (CQ .CollapseAt.iso δ̂₁ δ̂₂ isosδ .Iso.fwd ∘ ℰP.p₂))
                    ≈ (realise .fmor FCP.in₂ ∘ (CQ .CollapseAt.iso ε̂₁ ε̂₂ isosε .Iso.fwd ∘ fmorη Γ (Ŷ δ̂₁) (sfQ δ̂₁ ε̂₁ gs₁)))
            comp₂ =
              ≈-trans (CoK.∘-cong (fmorη-post Γ (Ŷ δ̂₂) FCP.in₂ _) ≈-refl)
                (≈-trans (assoc _ _ _)
                  (∘-cong ≈-refl (CQ .CollapseAt.natural δ̂₁ δ̂₂ isosδ isosε gs₁ gs₂ sqs)))

        rhs : (((sumIso _ _ isosε .Iso.fwd ∘ fmorη Γ (FCP.coprod (X̂ δ̂₁) (Ŷ δ̂₁)) (FSC.copair (FM.Mor-∘ FCP.in₁ (sfP δ̂₁ ε̂₁ gs₁)) (FM.Mor-∘ FCP.in₂ (sfQ δ̂₁ ε̂₁ gs₁))))
                ∘co (K⊕ (X̂ δ̂₁) (Ŷ δ̂₁) .Iso.bwd ∘ ℰP.p₂)))
              ≈ mid
        rhs =
          begin
            (sumIso _ _ isosε .Iso.fwd ∘ fmorη Γ (FCP.coprod (X̂ δ̂₁) (Ŷ δ̂₁)) (FSC.copair (FM.Mor-∘ FCP.in₁ (sfP δ̂₁ ε̂₁ gs₁)) (FM.Mor-∘ FCP.in₂ (sfQ δ̂₁ ε̂₁ gs₁)))) ∘co (K⊕ (X̂ δ̂₁) (Ŷ δ̂₁) .Iso.bwd ∘ ℰP.p₂)
          ≈⟨ assoc _ _ _ ⟩
            sumIso _ _ isosε .Iso.fwd ∘ (fmorη Γ (FCP.coprod (X̂ δ̂₁) (Ŷ δ̂₁)) (FSC.copair (FM.Mor-∘ FCP.in₁ (sfP δ̂₁ ε̂₁ gs₁)) (FM.Mor-∘ FCP.in₂ (sfQ δ̂₁ ε̂₁ gs₁))) ∘co (K⊕ (X̂ δ̂₁) (Ŷ δ̂₁) .Iso.bwd ∘ ℰP.p₂))
          ≈⟨ ∘-cong ≈-refl (fmorη-scopair Γ (X̂ δ̂₁) (Ŷ δ̂₁) _ _) ⟩
            sumIso _ _ isosε .Iso.fwd ∘ ℰSCm.copair (fmorη Γ (X̂ δ̂₁) (FM.Mor-∘ FCP.in₁ (sfP δ̂₁ ε̂₁ gs₁))) (fmorη Γ (Ŷ δ̂₁) (FM.Mor-∘ FCP.in₂ (sfQ δ̂₁ ε̂₁ gs₁)))
          ≈⟨ ℰSCm.copair-natural _ _ _ ⟩
            ℰSCm.copair (sumIso _ _ isosε .Iso.fwd ∘ fmorη Γ (X̂ δ̂₁) (FM.Mor-∘ FCP.in₁ (sfP δ̂₁ ε̂₁ gs₁))) (sumIso _ _ isosε .Iso.fwd ∘ fmorη Γ (Ŷ δ̂₁) (FM.Mor-∘ FCP.in₂ (sfQ δ̂₁ ε̂₁ gs₁)))
          ≈⟨ ℰSCm.copair-cong rcomp₁ rcomp₂ ⟩
            mid
          ∎
          where
            open ≈-Reasoning isEquiv

            push-in₁ : (sumIso _ _ isosε .Iso.fwd ∘ realise .fmor FCP.in₁)
                       ≈ (realise .fmor FCP.in₁ ∘ CP .CollapseAt.iso ε̂₁ ε̂₂ isosε .Iso.fwd)
            push-in₁ =
              ≈-trans (assoc _ _ _)
                (≈-trans (∘-cong ≈-refl (K⊕-in₁' (X̂ ε̂₁) (Ŷ ε̂₁)))
                  (≈-trans (assoc _ _ _)
                    (≈-trans (∘-cong ≈-refl (ℰCPm.copair-in₁ _ _))
                      (≈-trans (≈-sym (assoc _ _ _)) (∘-cong (K⊕-in₁ (X̂ ε̂₂) (Ŷ ε̂₂)) ≈-refl)))))

            push-in₂ : (sumIso _ _ isosε .Iso.fwd ∘ realise .fmor FCP.in₂)
                       ≈ (realise .fmor FCP.in₂ ∘ CQ .CollapseAt.iso ε̂₁ ε̂₂ isosε .Iso.fwd)
            push-in₂ =
              ≈-trans (assoc _ _ _)
                (≈-trans (∘-cong ≈-refl (K⊕-in₂' (X̂ ε̂₁) (Ŷ ε̂₁)))
                  (≈-trans (assoc _ _ _)
                    (≈-trans (∘-cong ≈-refl (ℰCPm.copair-in₂ _ _))
                      (≈-trans (≈-sym (assoc _ _ _)) (∘-cong (K⊕-in₂ (X̂ ε̂₂) (Ŷ ε̂₂)) ≈-refl)))))

            rcomp₁ : (sumIso _ _ isosε .Iso.fwd ∘ fmorη Γ (X̂ δ̂₁) (FM.Mor-∘ FCP.in₁ (sfP δ̂₁ ε̂₁ gs₁)))
                     ≈ (realise .fmor FCP.in₁ ∘ (CP .CollapseAt.iso ε̂₁ ε̂₂ isosε .Iso.fwd ∘ fmorη Γ (X̂ δ̂₁) (sfP δ̂₁ ε̂₁ gs₁)))
            rcomp₁ =
              ≈-trans (∘-cong ≈-refl (fmorη-post Γ (X̂ δ̂₁) FCP.in₁ _))
                (≈-trans (≈-sym (assoc _ _ _))
                  (≈-trans (∘-cong push-in₁ ≈-refl) (assoc _ _ _)))

            rcomp₂ : (sumIso _ _ isosε .Iso.fwd ∘ fmorη Γ (Ŷ δ̂₁) (FM.Mor-∘ FCP.in₂ (sfQ δ̂₁ ε̂₁ gs₁)))
                     ≈ (realise .fmor FCP.in₂ ∘ (CQ .CollapseAt.iso ε̂₁ ε̂₂ isosε .Iso.fwd ∘ fmorη Γ (Ŷ δ̂₁) (sfQ δ̂₁ ε̂₁ gs₁)))
            rcomp₂ =
              ≈-trans (∘-cong ≈-refl (fmorη-post Γ (Ŷ δ̂₁) FCP.in₂ _))
                (≈-trans (≈-sym (assoc _ _ _))
                  (≈-trans (∘-cong push-in₂ ≈-refl) (assoc _ _ _)))

-- Product machinery for the product case of the collapse.
private
  K× : ∀ (X̂ Ŷ : FM.Obj) → Iso (realise .fobj (FM.Fam𝒞-P.prod X̂ Ŷ))
                              (ℰP.prod (realise .fobj X̂) (realise .fobj Ŷ))
  K× X̂ Ŷ = FR.realise-products-iso ℰP ℰE X̂ Ŷ

  K×-p₁ : ∀ (X̂ Ŷ : FM.Obj) → (realise .fmor (FM.Fam𝒞-P.p₁ {x = X̂} {y = Ŷ}) ∘ K× X̂ Ŷ .Iso.bwd) ≈ ℰP.p₁
  K×-p₁ X̂ Ŷ =
    ≈-trans (∘-cong (≈-sym (FR.realise-products-p₁ ℰP ℰE X̂ Ŷ)) ≈-refl)
      (≈-trans (assoc _ _ _) (≈-trans (∘-cong ≈-refl (K× X̂ Ŷ .Iso.fwd∘bwd≈id)) id-right))

  K×-p₂ : ∀ (X̂ Ŷ : FM.Obj) → (realise .fmor (FM.Fam𝒞-P.p₂ {x = X̂} {y = Ŷ}) ∘ K× X̂ Ŷ .Iso.bwd) ≈ ℰP.p₂
  K×-p₂ X̂ Ŷ =
    ≈-trans (∘-cong (≈-sym (FR.realise-products-p₂ ℰP ℰE X̂ Ŷ)) ≈-refl)
      (≈-trans (assoc _ _ _) (≈-trans (∘-cong ≈-refl (K× X̂ Ŷ .Iso.fwd∘bwd≈id)) id-right))

-- Realisation in context sends the strong product action to the strong
-- product action, across the product comparison isos.
fmorη-sprodm : ∀ (Γ : obj) (X̂ Ŷ : FM.Obj) {Ẑ₁ Ẑ₂ : FM.Obj}
               (u : FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) X̂) Ẑ₁)
               (v : FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) Ŷ) Ẑ₂) →
               (fmorη Γ (FM.Fam𝒞-P.prod X̂ Ŷ) (FM.Fam𝒞-P.strong-prod-m u v) ∘co (K× X̂ Ŷ .Iso.bwd ∘ ℰP.p₂))
               ≈ (K× Ẑ₁ Ẑ₂ .Iso.bwd ∘ ℰP.strong-prod-m (fmorη Γ X̂ u) (fmorη Γ Ŷ v))
fmorη-sprodm Γ X̂ Ŷ {Ẑ₁} {Ẑ₂} u v =
  iso-shuffle (K× Ẑ₁ Ẑ₂) _ _
    (≈-trans (≈-sym (ℰP.pair-ext _)) (ℰP.pair-cong core₁ core₂))
  where
    core₁ : (ℰP.p₁ ∘ (K× Ẑ₁ Ẑ₂ .Iso.fwd ∘ (fmorη Γ (FM.Fam𝒞-P.prod X̂ Ŷ) (FM.Fam𝒞-P.strong-prod-m u v) ∘co (K× X̂ Ŷ .Iso.bwd ∘ ℰP.p₂))))
            ≈ (fmorη Γ X̂ u ∘ ℰP.strong-p₁)
    core₁ =
      begin
        ℰP.p₁ ∘ (K× Ẑ₁ Ẑ₂ .Iso.fwd ∘ (fmorη Γ (FM.Fam𝒞-P.prod X̂ Ŷ) (FM.Fam𝒞-P.strong-prod-m u v) ∘co (K× X̂ Ŷ .Iso.bwd ∘ ℰP.p₂)))
      ≈˘⟨ assoc _ _ _ ⟩
        (ℰP.p₁ ∘ K× Ẑ₁ Ẑ₂ .Iso.fwd) ∘ (fmorη Γ (FM.Fam𝒞-P.prod X̂ Ŷ) (FM.Fam𝒞-P.strong-prod-m u v) ∘co (K× X̂ Ŷ .Iso.bwd ∘ ℰP.p₂))
      ≈⟨ ∘-cong (FR.realise-products-p₁ ℰP ℰE Ẑ₁ Ẑ₂) ≈-refl ⟩
        realise .fmor (FM.Fam𝒞-P.p₁ {x = Ẑ₁} {y = Ẑ₂}) ∘ (fmorη Γ (FM.Fam𝒞-P.prod X̂ Ŷ) (FM.Fam𝒞-P.strong-prod-m u v) ∘co (K× X̂ Ŷ .Iso.bwd ∘ ℰP.p₂))
      ≈˘⟨ assoc _ _ _ ⟩
        (realise .fmor (FM.Fam𝒞-P.p₁ {x = Ẑ₁} {y = Ẑ₂}) ∘ fmorη Γ (FM.Fam𝒞-P.prod X̂ Ŷ) (FM.Fam𝒞-P.strong-prod-m u v)) ∘co (K× X̂ Ŷ .Iso.bwd ∘ ℰP.p₂)
      ≈˘⟨ CoK.∘-cong (fmorη-post Γ (FM.Fam𝒞-P.prod X̂ Ŷ) _ _) ≈-refl ⟩
        fmorη Γ (FM.Fam𝒞-P.prod X̂ Ŷ) (FM.Mor-∘ (FM.Fam𝒞-P.p₁ {x = Ẑ₁} {y = Ẑ₂}) (FM.Fam𝒞-P.strong-prod-m u v)) ∘co (K× X̂ Ŷ .Iso.bwd ∘ ℰP.p₂)
      ≈⟨ CoK.∘-cong (fmorη-cong (FM.Fam𝒞-P.pair-p₁ _ _)) ≈-refl ⟩
        fmorη Γ (FM.Fam𝒞-P.prod X̂ Ŷ) (FM.Mor-∘ u FM.Fam𝒞-P.strong-p₁) ∘co (K× X̂ Ŷ .Iso.bwd ∘ ℰP.p₂)
      ≈⟨ CoK.∘-cong (fmorη-∘co Γ (FM.Fam𝒞-P.prod X̂ Ŷ) u _) ≈-refl ⟩
        (fmorη Γ X̂ u ∘co fmorη Γ (FM.Fam𝒞-P.prod X̂ Ŷ) (FM.Mor-∘ (FM.Fam𝒞-P.p₁ {x = X̂} {y = Ŷ}) FM.Fam𝒞-P.p₂)) ∘co (K× X̂ Ŷ .Iso.bwd ∘ ℰP.p₂)
      ≈⟨ CoK.∘-cong (CoK.∘-cong ≈-refl (fmorη-pure Γ (FM.Fam𝒞-P.prod X̂ Ŷ) (FM.Fam𝒞-P.p₁ {x = X̂} {y = Ŷ}))) ≈-refl ⟩
        (fmorη Γ X̂ u ∘co (realise .fmor (FM.Fam𝒞-P.p₁ {x = X̂} {y = Ŷ}) ∘ ℰP.p₂)) ∘co (K× X̂ Ŷ .Iso.bwd ∘ ℰP.p₂)
      ≈⟨ CoK.assoc _ _ _ ⟩
        fmorη Γ X̂ u ∘co ((realise .fmor (FM.Fam𝒞-P.p₁ {x = X̂} {y = Ŷ}) ∘ ℰP.p₂) ∘co (K× X̂ Ŷ .Iso.bwd ∘ ℰP.p₂))
      ≈⟨ CoK.∘-cong ≈-refl (co-pure _ _) ⟩
        fmorη Γ X̂ u ∘co ((realise .fmor (FM.Fam𝒞-P.p₁ {x = X̂} {y = Ŷ}) ∘ K× X̂ Ŷ .Iso.bwd) ∘ ℰP.p₂)
      ≈⟨ CoK.∘-cong ≈-refl (∘-cong (K×-p₁ X̂ Ŷ) ≈-refl) ⟩
        fmorη Γ X̂ u ∘co (ℰP.p₁ ∘ ℰP.p₂)
      ∎ where open ≈-Reasoning isEquiv

    core₂ : (ℰP.p₂ ∘ (K× Ẑ₁ Ẑ₂ .Iso.fwd ∘ (fmorη Γ (FM.Fam𝒞-P.prod X̂ Ŷ) (FM.Fam𝒞-P.strong-prod-m u v) ∘co (K× X̂ Ŷ .Iso.bwd ∘ ℰP.p₂))))
            ≈ (fmorη Γ Ŷ v ∘ ℰP.strong-p₂)
    core₂ =
      begin
        ℰP.p₂ ∘ (K× Ẑ₁ Ẑ₂ .Iso.fwd ∘ (fmorη Γ (FM.Fam𝒞-P.prod X̂ Ŷ) (FM.Fam𝒞-P.strong-prod-m u v) ∘co (K× X̂ Ŷ .Iso.bwd ∘ ℰP.p₂)))
      ≈˘⟨ assoc _ _ _ ⟩
        (ℰP.p₂ ∘ K× Ẑ₁ Ẑ₂ .Iso.fwd) ∘ (fmorη Γ (FM.Fam𝒞-P.prod X̂ Ŷ) (FM.Fam𝒞-P.strong-prod-m u v) ∘co (K× X̂ Ŷ .Iso.bwd ∘ ℰP.p₂))
      ≈⟨ ∘-cong (FR.realise-products-p₂ ℰP ℰE Ẑ₁ Ẑ₂) ≈-refl ⟩
        realise .fmor (FM.Fam𝒞-P.p₂ {x = Ẑ₁} {y = Ẑ₂}) ∘ (fmorη Γ (FM.Fam𝒞-P.prod X̂ Ŷ) (FM.Fam𝒞-P.strong-prod-m u v) ∘co (K× X̂ Ŷ .Iso.bwd ∘ ℰP.p₂))
      ≈˘⟨ assoc _ _ _ ⟩
        (realise .fmor (FM.Fam𝒞-P.p₂ {x = Ẑ₁} {y = Ẑ₂}) ∘ fmorη Γ (FM.Fam𝒞-P.prod X̂ Ŷ) (FM.Fam𝒞-P.strong-prod-m u v)) ∘co (K× X̂ Ŷ .Iso.bwd ∘ ℰP.p₂)
      ≈˘⟨ CoK.∘-cong (fmorη-post Γ (FM.Fam𝒞-P.prod X̂ Ŷ) _ _) ≈-refl ⟩
        fmorη Γ (FM.Fam𝒞-P.prod X̂ Ŷ) (FM.Mor-∘ (FM.Fam𝒞-P.p₂ {x = Ẑ₁} {y = Ẑ₂}) (FM.Fam𝒞-P.strong-prod-m u v)) ∘co (K× X̂ Ŷ .Iso.bwd ∘ ℰP.p₂)
      ≈⟨ CoK.∘-cong (fmorη-cong (FM.Fam𝒞-P.pair-p₂ _ _)) ≈-refl ⟩
        fmorη Γ (FM.Fam𝒞-P.prod X̂ Ŷ) (FM.Mor-∘ v FM.Fam𝒞-P.strong-p₂) ∘co (K× X̂ Ŷ .Iso.bwd ∘ ℰP.p₂)
      ≈⟨ CoK.∘-cong (fmorη-∘co Γ (FM.Fam𝒞-P.prod X̂ Ŷ) v _) ≈-refl ⟩
        (fmorη Γ Ŷ v ∘co fmorη Γ (FM.Fam𝒞-P.prod X̂ Ŷ) (FM.Mor-∘ (FM.Fam𝒞-P.p₂ {x = X̂} {y = Ŷ}) FM.Fam𝒞-P.p₂)) ∘co (K× X̂ Ŷ .Iso.bwd ∘ ℰP.p₂)
      ≈⟨ CoK.∘-cong (CoK.∘-cong ≈-refl (fmorη-pure Γ (FM.Fam𝒞-P.prod X̂ Ŷ) (FM.Fam𝒞-P.p₂ {x = X̂} {y = Ŷ}))) ≈-refl ⟩
        (fmorη Γ Ŷ v ∘co (realise .fmor (FM.Fam𝒞-P.p₂ {x = X̂} {y = Ŷ}) ∘ ℰP.p₂)) ∘co (K× X̂ Ŷ .Iso.bwd ∘ ℰP.p₂)
      ≈⟨ CoK.assoc _ _ _ ⟩
        fmorη Γ Ŷ v ∘co ((realise .fmor (FM.Fam𝒞-P.p₂ {x = X̂} {y = Ŷ}) ∘ ℰP.p₂) ∘co (K× X̂ Ŷ .Iso.bwd ∘ ℰP.p₂))
      ≈⟨ CoK.∘-cong ≈-refl (co-pure _ _) ⟩
        fmorη Γ Ŷ v ∘co ((realise .fmor (FM.Fam𝒞-P.p₂ {x = X̂} {y = Ŷ}) ∘ K× X̂ Ŷ .Iso.bwd) ∘ ℰP.p₂)
      ≈⟨ CoK.∘-cong ≈-refl (∘-cong (K×-p₂ X̂ Ŷ) ≈-refl) ⟩
        fmorη Γ Ŷ v ∘co (ℰP.p₂ ∘ ℰP.p₂)
      ∎ where open ≈-Reasoning isEquiv

-- The collapse interface at products.
collapse-prod : ∀ {n} {P Q : Poly ℰ n} → CollapseAt P → CollapseAt Q →
                CollapseAt (P polynomial-functor-2.Poly.× Q)
collapse-prod {n} {P} {Q} CP CQ = record { iso = prodIso ; natural = prodNat ; refl-iso = prodRefl ; comp = prodComp }
  where
    X̂ : (Fin n → FM.Obj) → FM.Obj
    X̂ δ̂ = FM.fobj FM.μObj (Poly-map η P) δ̂

    Ŷ : (Fin n → FM.Obj) → FM.Obj
    Ŷ δ̂ = FM.fobj FM.μObj (Poly-map η Q) δ̂

    prodIso : ∀ δ̂₁ δ̂₂ (isos : ∀ i → Iso (realise .fobj (δ̂₁ i)) (realise .fobj (δ̂₂ i))) →
              Iso (realise .fobj (FM.Fam𝒞-P.prod (X̂ δ̂₁) (Ŷ δ̂₁))) (realise .fobj (FM.Fam𝒞-P.prod (X̂ δ̂₂) (Ŷ δ̂₂)))
    prodIso δ̂₁ δ̂₂ isos =
      Iso-trans (K× (X̂ δ̂₁) (Ŷ δ̂₁))
        (Iso-trans (ℰP.product-preserves-iso (CP .CollapseAt.iso δ̂₁ δ̂₂ isos) (CQ .CollapseAt.iso δ̂₁ δ̂₂ isos))
          (Iso-sym (K× (X̂ δ̂₂) (Ŷ δ̂₂))))

    prodIso-bwd : ∀ δ̂₁ δ̂₂ isos →
                  (prodIso δ̂₁ δ̂₂ isos .Iso.fwd ∘ K× (X̂ δ̂₁) (Ŷ δ̂₁) .Iso.bwd)
                  ≈ (K× (X̂ δ̂₂) (Ŷ δ̂₂) .Iso.bwd ∘ ℰP.prod-m (CP .CollapseAt.iso δ̂₁ δ̂₂ isos .Iso.fwd) (CQ .CollapseAt.iso δ̂₁ δ̂₂ isos .Iso.fwd))
    prodIso-bwd δ̂₁ δ̂₂ isos =
      ≈-trans (assoc _ _ _)
        (≈-trans (∘-cong ≈-refl (K× (X̂ δ̂₁) (Ŷ δ̂₁) .Iso.fwd∘bwd≈id)) id-right)

    prodRefl : ∀ δ̂ (isos : ∀ i → Iso (realise .fobj (δ̂ i)) (realise .fobj (δ̂ i))) →
               (∀ i → isos i .Iso.fwd ≈ id _) →
               prodIso δ̂ δ̂ isos .Iso.fwd ≈ id _
    prodRefl δ̂ isos hyps =
      begin
        (K× (X̂ δ̂) (Ŷ δ̂) .Iso.bwd ∘ ℰP.prod-m (CP .CollapseAt.iso δ̂ δ̂ isos .Iso.fwd) (CQ .CollapseAt.iso δ̂ δ̂ isos .Iso.fwd)) ∘ K× (X̂ δ̂) (Ŷ δ̂) .Iso.fwd
      ≈⟨ ∘-cong (∘-cong ≈-refl (≈-trans (ℰP.prod-m-cong (CP .CollapseAt.refl-iso δ̂ isos hyps) (CQ .CollapseAt.refl-iso δ̂ isos hyps)) ℰP.prod-m-id)) ≈-refl ⟩
        (K× (X̂ δ̂) (Ŷ δ̂) .Iso.bwd ∘ id _) ∘ K× (X̂ δ̂) (Ŷ δ̂) .Iso.fwd
      ≈⟨ ∘-cong id-right ≈-refl ⟩
        K× (X̂ δ̂) (Ŷ δ̂) .Iso.bwd ∘ K× (X̂ δ̂) (Ŷ δ̂) .Iso.fwd
      ≈⟨ K× (X̂ δ̂) (Ŷ δ̂) .Iso.bwd∘fwd≈id ⟩
        id _
      ∎ where open ≈-Reasoning isEquiv

    prodComp : ∀ δ̂₁ δ̂₂ δ̂₃ (isos₁₂ : ∀ i → Iso (realise .fobj (δ̂₁ i)) (realise .fobj (δ̂₂ i)))
               (isos₂₃ : ∀ i → Iso (realise .fobj (δ̂₂ i)) (realise .fobj (δ̂₃ i))) →
               prodIso δ̂₁ δ̂₃ (λ i → Iso-trans (isos₁₂ i) (isos₂₃ i)) .Iso.fwd
               ≈ (prodIso δ̂₂ δ̂₃ isos₂₃ .Iso.fwd ∘ prodIso δ̂₁ δ̂₂ isos₁₂ .Iso.fwd)
    prodComp δ̂₁ δ̂₂ δ̂₃ isos₁₂ isos₂₃ = ≈-trans toM (≈-sym fromM)
      where
        pm₁₂ = ℰP.prod-m (CP .CollapseAt.iso δ̂₁ δ̂₂ isos₁₂ .Iso.fwd) (CQ .CollapseAt.iso δ̂₁ δ̂₂ isos₁₂ .Iso.fwd)
        pm₂₃ = ℰP.prod-m (CP .CollapseAt.iso δ̂₂ δ̂₃ isos₂₃ .Iso.fwd) (CQ .CollapseAt.iso δ̂₂ δ̂₃ isos₂₃ .Iso.fwd)

        toM : prodIso δ̂₁ δ̂₃ (λ i → Iso-trans (isos₁₂ i) (isos₂₃ i)) .Iso.fwd
              ≈ ((K× (X̂ δ̂₃) (Ŷ δ̂₃) .Iso.bwd ∘ (pm₂₃ ∘ pm₁₂)) ∘ K× (X̂ δ̂₁) (Ŷ δ̂₁) .Iso.fwd)
        toM =
          ∘-cong (∘-cong ≈-refl
            (≈-trans (ℰP.prod-m-cong (CP .CollapseAt.comp δ̂₁ δ̂₂ δ̂₃ isos₁₂ isos₂₃) (CQ .CollapseAt.comp δ̂₁ δ̂₂ δ̂₃ isos₁₂ isos₂₃))
              (ℰP.prod-m-comp _ _ _ _))) ≈-refl

        fromM : (prodIso δ̂₂ δ̂₃ isos₂₃ .Iso.fwd ∘ prodIso δ̂₁ δ̂₂ isos₁₂ .Iso.fwd)
                ≈ ((K× (X̂ δ̂₃) (Ŷ δ̂₃) .Iso.bwd ∘ (pm₂₃ ∘ pm₁₂)) ∘ K× (X̂ δ̂₁) (Ŷ δ̂₁) .Iso.fwd)
        fromM =
          begin
            ((K× (X̂ δ̂₃) (Ŷ δ̂₃) .Iso.bwd ∘ pm₂₃) ∘ K× (X̂ δ̂₂) (Ŷ δ̂₂) .Iso.fwd) ∘ ((K× (X̂ δ̂₂) (Ŷ δ̂₂) .Iso.bwd ∘ pm₁₂) ∘ K× (X̂ δ̂₁) (Ŷ δ̂₁) .Iso.fwd)
          ≈˘⟨ assoc _ _ _ ⟩
            (((K× (X̂ δ̂₃) (Ŷ δ̂₃) .Iso.bwd ∘ pm₂₃) ∘ K× (X̂ δ̂₂) (Ŷ δ̂₂) .Iso.fwd) ∘ (K× (X̂ δ̂₂) (Ŷ δ̂₂) .Iso.bwd ∘ pm₁₂)) ∘ K× (X̂ δ̂₁) (Ŷ δ̂₁) .Iso.fwd
          ≈⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
            ((K× (X̂ δ̂₃) (Ŷ δ̂₃) .Iso.bwd ∘ pm₂₃) ∘ (K× (X̂ δ̂₂) (Ŷ δ̂₂) .Iso.fwd ∘ (K× (X̂ δ̂₂) (Ŷ δ̂₂) .Iso.bwd ∘ pm₁₂))) ∘ K× (X̂ δ̂₁) (Ŷ δ̂₁) .Iso.fwd
          ≈⟨ ∘-cong (∘-cong ≈-refl (≈-trans (≈-sym (assoc _ _ _)) (≈-trans (∘-cong (K× (X̂ δ̂₂) (Ŷ δ̂₂) .Iso.fwd∘bwd≈id) ≈-refl) id-left))) ≈-refl ⟩
            ((K× (X̂ δ̂₃) (Ŷ δ̂₃) .Iso.bwd ∘ pm₂₃) ∘ pm₁₂) ∘ K× (X̂ δ̂₁) (Ŷ δ̂₁) .Iso.fwd
          ≈⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
            (K× (X̂ δ̂₃) (Ŷ δ̂₃) .Iso.bwd ∘ (pm₂₃ ∘ pm₁₂)) ∘ K× (X̂ δ̂₁) (Ŷ δ̂₁) .Iso.fwd
          ∎ where open ≈-Reasoning isEquiv

    prodNat : ∀ {Γ : obj} {ε̂₁ ε̂₂ : Fin n → FM.Obj}
              (δ̂₁ δ̂₂ : Fin n → FM.Obj)
              (isosδ : ∀ i → Iso (realise .fobj (δ̂₁ i)) (realise .fobj (δ̂₂ i)))
              (isosε : ∀ i → Iso (realise .fobj (ε̂₁ i)) (realise .fobj (ε̂₂ i)))
              (gs₁ : ∀ i → FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) (δ̂₁ i)) (ε̂₁ i))
              (gs₂ : ∀ i → FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) (δ̂₂ i)) (ε̂₂ i)) →
              (∀ i → (fmorη Γ (δ̂₂ i) (gs₂ i) ∘co (isosδ i .Iso.fwd ∘ ℰP.p₂))
                     ≈ (isosε i .Iso.fwd ∘ fmorη Γ (δ̂₁ i) (gs₁ i))) →
              (fmorη Γ (FM.Fam𝒞-P.prod (X̂ δ̂₂) (Ŷ δ̂₂)) (FMu.strong-fmor (Poly-map η (P polynomial-functor-2.Poly.× Q)) gs₂)
                ∘co (prodIso δ̂₁ δ̂₂ isosδ .Iso.fwd ∘ ℰP.p₂))
              ≈ (prodIso _ _ isosε .Iso.fwd ∘ fmorη Γ (FM.Fam𝒞-P.prod (X̂ δ̂₁) (Ŷ δ̂₁)) (FMu.strong-fmor (Poly-map η (P polynomial-functor-2.Poly.× Q)) gs₁))
    prodNat {Γ} {ε̂₁} {ε̂₂} δ̂₁ δ̂₂ isosδ isosε gs₁ gs₂ sqs =
      co-iso-epi (K× (X̂ δ̂₁) (Ŷ δ̂₁)) (≈-trans lhs (≈-sym rhs))
      where
        sfP = FMu.strong-fmor (Poly-map η P)
        sfQ = FMu.strong-fmor (Poly-map η Q)

        mid : ℰP.prod Γ (ℰP.prod (realise .fobj (X̂ δ̂₁)) (realise .fobj (Ŷ δ̂₁))) ⇒ realise .fobj (FM.Fam𝒞-P.prod (X̂ ε̂₂) (Ŷ ε̂₂))
        mid = K× (X̂ ε̂₂) (Ŷ ε̂₂) .Iso.bwd ∘
              ℰP.strong-prod-m
                (CP .CollapseAt.iso ε̂₁ ε̂₂ isosε .Iso.fwd ∘ fmorη Γ (X̂ δ̂₁) (sfP gs₁))
                (CQ .CollapseAt.iso ε̂₁ ε̂₂ isosε .Iso.fwd ∘ fmorη Γ (Ŷ δ̂₁) (sfQ gs₁))

        lhs : ((fmorη Γ (FM.Fam𝒞-P.prod (X̂ δ̂₂) (Ŷ δ̂₂)) (FM.Fam𝒞-P.strong-prod-m (sfP gs₂) (sfQ gs₂))
                ∘co (prodIso δ̂₁ δ̂₂ isosδ .Iso.fwd ∘ ℰP.p₂)) ∘co (K× (X̂ δ̂₁) (Ŷ δ̂₁) .Iso.bwd ∘ ℰP.p₂))
              ≈ mid
        lhs =
          begin
            (fmorη Γ (FM.Fam𝒞-P.prod (X̂ δ̂₂) (Ŷ δ̂₂)) (FM.Fam𝒞-P.strong-prod-m (sfP gs₂) (sfQ gs₂)) ∘co (prodIso δ̂₁ δ̂₂ isosδ .Iso.fwd ∘ ℰP.p₂)) ∘co (K× (X̂ δ̂₁) (Ŷ δ̂₁) .Iso.bwd ∘ ℰP.p₂)
          ≈⟨ CoK.assoc _ _ _ ⟩
            fmorη Γ (FM.Fam𝒞-P.prod (X̂ δ̂₂) (Ŷ δ̂₂)) (FM.Fam𝒞-P.strong-prod-m (sfP gs₂) (sfQ gs₂)) ∘co ((prodIso δ̂₁ δ̂₂ isosδ .Iso.fwd ∘ ℰP.p₂) ∘co (K× (X̂ δ̂₁) (Ŷ δ̂₁) .Iso.bwd ∘ ℰP.p₂))
          ≈⟨ CoK.∘-cong ≈-refl (≈-trans (co-pure _ _) (∘-cong (prodIso-bwd δ̂₁ δ̂₂ isosδ) ≈-refl)) ⟩
            fmorη Γ (FM.Fam𝒞-P.prod (X̂ δ̂₂) (Ŷ δ̂₂)) (FM.Fam𝒞-P.strong-prod-m (sfP gs₂) (sfQ gs₂)) ∘co ((K× (X̂ δ̂₂) (Ŷ δ̂₂) .Iso.bwd ∘ ℰP.prod-m (CP .CollapseAt.iso δ̂₁ δ̂₂ isosδ .Iso.fwd) (CQ .CollapseAt.iso δ̂₁ δ̂₂ isosδ .Iso.fwd)) ∘ ℰP.p₂)
          ≈˘⟨ CoK.∘-cong ≈-refl (co-pure _ _) ⟩
            fmorη Γ (FM.Fam𝒞-P.prod (X̂ δ̂₂) (Ŷ δ̂₂)) (FM.Fam𝒞-P.strong-prod-m (sfP gs₂) (sfQ gs₂)) ∘co ((K× (X̂ δ̂₂) (Ŷ δ̂₂) .Iso.bwd ∘ ℰP.p₂) ∘co (ℰP.prod-m (CP .CollapseAt.iso δ̂₁ δ̂₂ isosδ .Iso.fwd) (CQ .CollapseAt.iso δ̂₁ δ̂₂ isosδ .Iso.fwd) ∘ ℰP.p₂))
          ≈˘⟨ CoK.assoc _ _ _ ⟩
            (fmorη Γ (FM.Fam𝒞-P.prod (X̂ δ̂₂) (Ŷ δ̂₂)) (FM.Fam𝒞-P.strong-prod-m (sfP gs₂) (sfQ gs₂)) ∘co (K× (X̂ δ̂₂) (Ŷ δ̂₂) .Iso.bwd ∘ ℰP.p₂)) ∘co (ℰP.prod-m (CP .CollapseAt.iso δ̂₁ δ̂₂ isosδ .Iso.fwd) (CQ .CollapseAt.iso δ̂₁ δ̂₂ isosδ .Iso.fwd) ∘ ℰP.p₂)
          ≈⟨ CoK.∘-cong (fmorη-sprodm Γ (X̂ δ̂₂) (Ŷ δ̂₂) _ _) ≈-refl ⟩
            (K× (X̂ ε̂₂) (Ŷ ε̂₂) .Iso.bwd ∘ ℰP.strong-prod-m (fmorη Γ (X̂ δ̂₂) (sfP gs₂)) (fmorη Γ (Ŷ δ̂₂) (sfQ gs₂))) ∘co (ℰP.prod-m (CP .CollapseAt.iso δ̂₁ δ̂₂ isosδ .Iso.fwd) (CQ .CollapseAt.iso δ̂₁ δ̂₂ isosδ .Iso.fwd) ∘ ℰP.p₂)
          ≈⟨ assoc _ _ _ ⟩
            K× (X̂ ε̂₂) (Ŷ ε̂₂) .Iso.bwd ∘ (ℰP.strong-prod-m (fmorη Γ (X̂ δ̂₂) (sfP gs₂)) (fmorη Γ (Ŷ δ̂₂) (sfQ gs₂)) ∘co (ℰP.prod-m (CP .CollapseAt.iso δ̂₁ δ̂₂ isosδ .Iso.fwd) (CQ .CollapseAt.iso δ̂₁ δ̂₂ isosδ .Iso.fwd) ∘ ℰP.p₂))
          ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl (ℰP.pair-cong (≈-sym id-left) ≈-refl)) ⟩
            K× (X̂ ε̂₂) (Ŷ ε̂₂) .Iso.bwd ∘ (ℰP.strong-prod-m (fmorη Γ (X̂ δ̂₂) (sfP gs₂)) (fmorη Γ (Ŷ δ̂₂) (sfQ gs₂)) ∘ ℰP.prod-m (id _) (ℰP.prod-m (CP .CollapseAt.iso δ̂₁ δ̂₂ isosδ .Iso.fwd) (CQ .CollapseAt.iso δ̂₁ δ̂₂ isosδ .Iso.fwd)))
          ≈⟨ ∘-cong ≈-refl (ℰP.strong-prod-m-pre _ _ _ _ _) ⟩
            K× (X̂ ε̂₂) (Ŷ ε̂₂) .Iso.bwd ∘ ℰP.strong-prod-m (fmorη Γ (X̂ δ̂₂) (sfP gs₂) ∘ ℰP.prod-m (id _) (CP .CollapseAt.iso δ̂₁ δ̂₂ isosδ .Iso.fwd)) (fmorη Γ (Ŷ δ̂₂) (sfQ gs₂) ∘ ℰP.prod-m (id _) (CQ .CollapseAt.iso δ̂₁ δ̂₂ isosδ .Iso.fwd))
          ≈⟨ ∘-cong ≈-refl (ℰP.strong-prod-m-cong comp₁ comp₂) ⟩
            mid
          ∎
          where
            open ≈-Reasoning isEquiv

            comp₁ : (fmorη Γ (X̂ δ̂₂) (sfP gs₂) ∘ ℰP.prod-m (id _) (CP .CollapseAt.iso δ̂₁ δ̂₂ isosδ .Iso.fwd))
                    ≈ (CP .CollapseAt.iso ε̂₁ ε̂₂ isosε .Iso.fwd ∘ fmorη Γ (X̂ δ̂₁) (sfP gs₁))
            comp₁ =
              ≈-trans (∘-cong ≈-refl (ℰP.pair-cong id-left ≈-refl))
                (CP .CollapseAt.natural δ̂₁ δ̂₂ isosδ isosε gs₁ gs₂ sqs)

            comp₂ : (fmorη Γ (Ŷ δ̂₂) (sfQ gs₂) ∘ ℰP.prod-m (id _) (CQ .CollapseAt.iso δ̂₁ δ̂₂ isosδ .Iso.fwd))
                    ≈ (CQ .CollapseAt.iso ε̂₁ ε̂₂ isosε .Iso.fwd ∘ fmorη Γ (Ŷ δ̂₁) (sfQ gs₁))
            comp₂ =
              ≈-trans (∘-cong ≈-refl (ℰP.pair-cong id-left ≈-refl))
                (CQ .CollapseAt.natural δ̂₁ δ̂₂ isosδ isosε gs₁ gs₂ sqs)

        rhs : (((prodIso _ _ isosε .Iso.fwd ∘ fmorη Γ (FM.Fam𝒞-P.prod (X̂ δ̂₁) (Ŷ δ̂₁)) (FM.Fam𝒞-P.strong-prod-m (sfP gs₁) (sfQ gs₁)))
                ∘co (K× (X̂ δ̂₁) (Ŷ δ̂₁) .Iso.bwd ∘ ℰP.p₂)))
              ≈ mid
        rhs =
          begin
            (prodIso _ _ isosε .Iso.fwd ∘ fmorη Γ (FM.Fam𝒞-P.prod (X̂ δ̂₁) (Ŷ δ̂₁)) (FM.Fam𝒞-P.strong-prod-m (sfP gs₁) (sfQ gs₁))) ∘co (K× (X̂ δ̂₁) (Ŷ δ̂₁) .Iso.bwd ∘ ℰP.p₂)
          ≈⟨ assoc _ _ _ ⟩
            prodIso _ _ isosε .Iso.fwd ∘ (fmorη Γ (FM.Fam𝒞-P.prod (X̂ δ̂₁) (Ŷ δ̂₁)) (FM.Fam𝒞-P.strong-prod-m (sfP gs₁) (sfQ gs₁)) ∘co (K× (X̂ δ̂₁) (Ŷ δ̂₁) .Iso.bwd ∘ ℰP.p₂))
          ≈⟨ ∘-cong ≈-refl (fmorη-sprodm Γ (X̂ δ̂₁) (Ŷ δ̂₁) _ _) ⟩
            prodIso _ _ isosε .Iso.fwd ∘ (K× (X̂ ε̂₁) (Ŷ ε̂₁) .Iso.bwd ∘ ℰP.strong-prod-m (fmorη Γ (X̂ δ̂₁) (sfP gs₁)) (fmorη Γ (Ŷ δ̂₁) (sfQ gs₁)))
          ≈˘⟨ assoc _ _ _ ⟩
            (prodIso _ _ isosε .Iso.fwd ∘ K× (X̂ ε̂₁) (Ŷ ε̂₁) .Iso.bwd) ∘ ℰP.strong-prod-m (fmorη Γ (X̂ δ̂₁) (sfP gs₁)) (fmorη Γ (Ŷ δ̂₁) (sfQ gs₁))
          ≈⟨ ∘-cong (prodIso-bwd ε̂₁ ε̂₂ isosε) ≈-refl ⟩
            (K× (X̂ ε̂₂) (Ŷ ε̂₂) .Iso.bwd ∘ ℰP.prod-m (CP .CollapseAt.iso ε̂₁ ε̂₂ isosε .Iso.fwd) (CQ .CollapseAt.iso ε̂₁ ε̂₂ isosε .Iso.fwd)) ∘ ℰP.strong-prod-m (fmorη Γ (X̂ δ̂₁) (sfP gs₁)) (fmorη Γ (Ŷ δ̂₁) (sfQ gs₁))
          ≈⟨ assoc _ _ _ ⟩
            K× (X̂ ε̂₂) (Ŷ ε̂₂) .Iso.bwd ∘ (ℰP.prod-m (CP .CollapseAt.iso ε̂₁ ε̂₂ isosε .Iso.fwd) (CQ .CollapseAt.iso ε̂₁ ε̂₂ isosε .Iso.fwd) ∘ ℰP.strong-prod-m (fmorη Γ (X̂ δ̂₁) (sfP gs₁)) (fmorη Γ (Ŷ δ̂₁) (sfQ gs₁)))
          ≈⟨ ∘-cong ≈-refl (ℰP.strong-prod-m-post _ _ _ _) ⟩
            mid
          ∎ where open ≈-Reasoning isEquiv

-- The initial-algebra package for a polynomial, against an assumed collapse
-- family and its naturality with respect to the strong action. The algebra
-- map realises the Fam(ℰ) algebra map and corrects the bound-variable entry
-- by collapse; the fold transposes the algebra to Fam(ℰ), folds there, and
-- transposes back; β follows from the Fam(ℰ) β law pushed through the
-- co-Kleisli functoriality of realisation.
module Initiality {n} (P : Poly ℰ (suc n)) (δ̂ : Fin n → FM.Obj)
    (CP : CollapseAt P)
  where

  open CollapseAt CP using () renaming (iso to Kiso'; natural to Knat; refl-iso to Krefl)

  private
    P̂ = Poly-map η P
    μ̂ = FM.μObj P̂ δ̂

    F^ : FM.Obj → FM.Obj
    F^ Ŷ = FM.fobj FM.μObj P̂ (extend δ̂ Ŷ)

  inIsos : ∀ i → Iso (realise .fobj (extend δ̂ (η .fobj (Creal P δ̂)) i))
                     (realise .fobj (extend δ̂ (FM.μObj (Poly-map η P) δ̂) i))
  inIsos Fin.zero    = realise-η-iso (Creal P δ̂)
  inIsos (Fin.suc i) = Iso-refl

  private

    bF : ∀ {Γ A} → (ℰP.prod Γ (Greal P δ̂ A) ⇒ A) → FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) (F^ (η .fobj A))) (η .fobj A)
    bF {Γ} {A} a = untranspose (a ∘ prodη Γ (F^ (η .fobj A)) .Iso.fwd)

  inR : Greal P δ̂ (Creal P δ̂) ⇒ Creal P δ̂
  inR = realise .fmor (FMu.α P̂ δ̂) ∘
        Kiso' (extend δ̂ (η .fobj (Creal P δ̂))) (extend δ̂ μ̂) inIsos .Iso.fwd

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
    h~ {Γ} {A} h = ctxη Γ (Creal P δ̂) h

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
            ∘co (Kiso' (extend δ̂ (η .fobj (Creal P δ̂))) (extend δ̂ μ̂) inIsos .Iso.fwd ∘ ℰP.p₂))
          ≈ Gmap P δ̂ h
    key {Γ} {A} u h hyp =
      ≈-trans
        (Knat (extend δ̂ (η .fobj (Creal P δ̂))) (extend δ̂ μ̂) inIsos (λ i → Iso-refl)
          (FMu.strong-extend-mor (λ i → FM.Fam𝒞-P.p₂) (h~ h))
          (FMu.strong-extend-mor (λ i → FM.Fam𝒞-P.p₂) u)
          compats)
        (≈-trans (∘-cong (Krefl (extend δ̂ (η .fobj A)) (λ i → Iso-refl) (λ i → ≈-refl)) ≈-refl) id-left)
      where
        compats : ∀ i → (fmorη Γ (extend δ̂ μ̂ i) (FMu.strong-extend-mor (λ j → FM.Fam𝒞-P.p₂) u i) ∘co (inIsos i .Iso.fwd ∘ ℰP.p₂))
                  ≈ (Iso-refl .Iso.fwd ∘ fmorη Γ (extend δ̂ (η .fobj (Creal P δ̂)) i) (FMu.strong-extend-mor (λ j → FM.Fam𝒞-P.p₂) (h~ h) i))
        compats Fin.zero    = ≈-trans (compat-zero u h hyp) (≈-sym id-left)
        compats (Fin.suc i) = ≈-trans (compat-suc i) (≈-sym id-left)

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
      K = Kiso' (extend δ̂ (η .fobj (Creal P δ̂))) (extend δ̂ μ̂) inIsos .Iso.fwd
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
      Kiso = Kiso' (extend δ̂ (η .fobj (Creal P δ̂))) (extend δ̂ μ̂) inIsos
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

  foldR-cong : ∀ {Γ A} {a₁ a₂ : ℰP.prod Γ (Greal P δ̂ A) ⇒ A} →
               a₁ ≈ a₂ → foldR a₁ ≈ foldR a₂
  foldR-cong {Γ} {A} {a₁} {a₂} e =
    ∘-cong (FR.transpose-cong (FMuI.⦅⦆-cong P̂ δ̂ (FR.untranspose-cong (∘-cong e ≈-refl)))) ≈-refl

  muReal : MuReal P δ̂
  muReal = record
    { inR = inR ; foldR = foldR ; foldR-cong = foldR-cong ; foldR-β = foldR-β ; foldR-η = foldR-η }

-- Realisations of the μ-object at environments with isomorphic realisations
-- are isomorphic: fold each carrier into the other through the collapse of
-- the polynomial's action, with the roundtrips by uniqueness of folds.
module MuCollapse {n} (Q : Poly ℰ (suc n)) (CQ : CollapseAt Q)
    (δ̂₁ δ̂₂ : Fin n → FM.Obj)
    (isos : ∀ i → Iso (realise .fobj (δ̂₁ i)) (realise .fobj (δ̂₂ i)))
  where

  module M₁ = Initiality Q δ̂₁ CQ
  module M₂ = Initiality Q δ̂₂ CQ
  module ℰTm = HasTerminal ℰT

  𝟙 = ℰTm.witness

  extIsos : ∀ (A : obj) i → Iso (realise .fobj (extend δ̂₁ (η .fobj A) i))
                                (realise .fobj (extend δ̂₂ (η .fobj A) i))
  extIsos A Fin.zero    = Iso-refl
  extIsos A (Fin.suc i) = isos i

  GI : ∀ (A : obj) → Iso (Greal Q δ̂₁ A) (Greal Q δ̂₂ A)
  GI A = CQ .CollapseAt.iso (extend δ̂₁ (η .fobj A)) (extend δ̂₂ (η .fobj A)) (extIsos A)

  F' : ℰP.prod 𝟙 (Creal Q δ̂₁) ⇒ Creal Q δ̂₂
  F' = M₁.foldR (M₂.inR ∘ (GI (Creal Q δ̂₂) .Iso.fwd ∘ ℰP.p₂))

  G' : ℰP.prod 𝟙 (Creal Q δ̂₂) ⇒ Creal Q δ̂₁
  G' = M₂.foldR (M₁.inR ∘ (GI (Creal Q δ̂₁) .Iso.bwd ∘ ℰP.p₂))

  -- (componentwise naturality squares hoisted to top level)

  -- The crossing square: the strong action commutes with the collapse.
  cross : ∀ {A B : obj} (h : ℰP.prod 𝟙 A ⇒ B) →
          (Gmap Q δ̂₂ h ∘co (GI A .Iso.fwd ∘ ℰP.p₂)) ≈ (GI B .Iso.fwd ∘ Gmap Q δ̂₁ h)
  cross {A} {B} h =
    CQ .CollapseAt.natural (extend δ̂₁ (η .fobj A)) (extend δ̂₂ (η .fobj A)) (extIsos A) (extIsos B)
      (FMu.strong-extend-mor (λ i → FM.Fam𝒞-P.p₂) (ctxη 𝟙 A h))
      (FMu.strong-extend-mor (λ i → FM.Fam𝒞-P.p₂) (ctxη 𝟙 A h))
      sqs
    where
      sqs : ∀ i → (fmorη 𝟙 (extend δ̂₂ (η .fobj A) i) (FMu.strong-extend-mor (λ j → FM.Fam𝒞-P.p₂) (ctxη 𝟙 A h) i) ∘co (extIsos A i .Iso.fwd ∘ ℰP.p₂))
            ≈ (extIsos B i .Iso.fwd ∘ fmorη 𝟙 (extend δ̂₁ (η .fobj A) i) (FMu.strong-extend-mor (λ j → FM.Fam𝒞-P.p₂) (ctxη 𝟙 A h) i))
      sqs Fin.zero    = sq-refl (ctxη 𝟙 A h)
      sqs (Fin.suc i) = sq-p₂ (isos i)

  -- The crossing square over an arbitrary context.
  crossΓ : ∀ {Γ' A B : obj} (h : ℰP.prod Γ' A ⇒ B) →
           (Gmap Q δ̂₂ h ∘co (GI A .Iso.fwd ∘ ℰP.p₂)) ≈ (GI B .Iso.fwd ∘ Gmap Q δ̂₁ h)
  crossΓ {Γ'} {A} {B} h =
    CQ .CollapseAt.natural (extend δ̂₁ (η .fobj A)) (extend δ̂₂ (η .fobj A)) (extIsos A) (extIsos B)
      (FMu.strong-extend-mor (λ i → FM.Fam𝒞-P.p₂) (ctxη Γ' A h))
      (FMu.strong-extend-mor (λ i → FM.Fam𝒞-P.p₂) (ctxη Γ' A h))
      sqs
    where
      sqs : ∀ i → (fmorη Γ' (extend δ̂₂ (η .fobj A) i) (FMu.strong-extend-mor (λ j → FM.Fam𝒞-P.p₂) (ctxη Γ' A h) i) ∘co (extIsos A i .Iso.fwd ∘ ℰP.p₂))
            ≈ (extIsos B i .Iso.fwd ∘ fmorη Γ' (extend δ̂₁ (η .fobj A) i) (FMu.strong-extend-mor (λ j → FM.Fam𝒞-P.p₂) (ctxη Γ' A h) i))
      sqs Fin.zero    = sq-refl (ctxη Γ' A h)
      sqs (Fin.suc i) = sq-p₂ (isos i)

  -- The crossing square, backwards.
  cross-flip : ∀ {A B : obj} (h : ℰP.prod 𝟙 A ⇒ B) →
               (Gmap Q δ̂₁ h ∘co (GI A .Iso.bwd ∘ ℰP.p₂)) ≈ (GI B .Iso.bwd ∘ Gmap Q δ̂₂ h)
  cross-flip {A} {B} h =
    iso-shuffle (GI B) _ _
      (≈-trans (≈-sym (assoc _ _ _)) (co-iso-cancel (GI A) (cross h)))

  -- Fusion of a fold against a composed algebra morphism, both directions.
  square-p₂₁ : (ℰP.p₂ ∘co (M₁.inR ∘ ℰP.p₂)) ≈ ((M₁.inR ∘ ℰP.p₂) ∘co Gmap Q δ̂₁ ℰP.p₂)
  square-p₂₁ =
    ≈-trans (CoK.id-left {Γ = 𝟙})
      (≈-sym (≈-trans (CoK.∘-cong ≈-refl (Gmap-id Q δ̂₁)) (CoK.id-right {Γ = 𝟙})))

  square-p₂₂ : (ℰP.p₂ ∘co (M₂.inR ∘ ℰP.p₂)) ≈ ((M₂.inR ∘ ℰP.p₂) ∘co Gmap Q δ̂₂ ℰP.p₂)
  square-p₂₂ =
    ≈-trans (CoK.id-left {Γ = 𝟙})
      (≈-sym (≈-trans (CoK.∘-cong ≈-refl (Gmap-id Q δ̂₂)) (CoK.id-right {Γ = 𝟙})))

  ag-cross : ((M₁.inR ∘ (GI (Creal Q δ̂₁) .Iso.bwd ∘ ℰP.p₂)) ∘co (GI (Creal Q δ̂₁) .Iso.fwd ∘ Gmap Q δ̂₁ G'))
             ≈ ((M₁.inR ∘ ℰP.p₂) ∘co Gmap Q δ̂₁ G')
  ag-cross =
    begin
      (M₁.inR ∘ (GI (Creal Q δ̂₁) .Iso.bwd ∘ ℰP.p₂)) ∘ ℰP.pair ℰP.p₁ (GI (Creal Q δ̂₁) .Iso.fwd ∘ Gmap Q δ̂₁ G')
    ≈⟨ assoc _ _ _ ⟩
      M₁.inR ∘ ((GI (Creal Q δ̂₁) .Iso.bwd ∘ ℰP.p₂) ∘ ℰP.pair ℰP.p₁ (GI (Creal Q δ̂₁) .Iso.fwd ∘ Gmap Q δ̂₁ G'))
    ≈⟨ ∘-cong ≈-refl (≈-trans (assoc _ _ _) (∘-cong ≈-refl (ℰP.pair-p₂ _ _))) ⟩
      M₁.inR ∘ (GI (Creal Q δ̂₁) .Iso.bwd ∘ (GI (Creal Q δ̂₁) .Iso.fwd ∘ Gmap Q δ̂₁ G'))
    ≈˘⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
      M₁.inR ∘ ((GI (Creal Q δ̂₁) .Iso.bwd ∘ GI (Creal Q δ̂₁) .Iso.fwd) ∘ Gmap Q δ̂₁ G')
    ≈⟨ ∘-cong ≈-refl (≈-trans (∘-cong (GI (Creal Q δ̂₁) .Iso.bwd∘fwd≈id) ≈-refl) id-left) ⟩
      M₁.inR ∘ Gmap Q δ̂₁ G'
    ≈˘⟨ ≈-trans (assoc _ _ _) (∘-cong ≈-refl (ℰP.pair-p₂ _ _)) ⟩
      (M₁.inR ∘ ℰP.p₂) ∘ ℰP.pair ℰP.p₁ (Gmap Q δ̂₁ G')
    ∎ where open ≈-Reasoning isEquiv


  -- The composite G' ∘co F' satisfies the fold square for the algebra of the identity.
  square-GF : ((G' ∘co F') ∘co (M₁.inR ∘ ℰP.p₂)) ≈ ((M₁.inR ∘ ℰP.p₂) ∘co Gmap Q δ̂₁ (G' ∘co F'))
  square-GF =
    begin
      (G' ∘co F') ∘co (M₁.inR ∘ ℰP.p₂)
    ≈⟨ CoK.assoc _ _ _ ⟩
      G' ∘co (F' ∘co (M₁.inR ∘ ℰP.p₂))
    ≈⟨ CoK.∘-cong ≈-refl (M₁.foldR-β _) ⟩
      G' ∘co ((M₂.inR ∘ (GI (Creal Q δ̂₂) .Iso.fwd ∘ ℰP.p₂)) ∘co Gmap Q δ̂₁ F')
    ≈⟨ CoK.∘-cong ≈-refl (CoK.∘-cong (≈-trans (≈-sym (assoc _ _ _)) (≈-sym (co-pure M₂.inR (GI (Creal Q δ̂₂) .Iso.fwd)))) ≈-refl) ⟩
      G' ∘co (((M₂.inR ∘ ℰP.p₂) ∘co (GI (Creal Q δ̂₂) .Iso.fwd ∘ ℰP.p₂)) ∘co Gmap Q δ̂₁ F')
    ≈˘⟨ CoK.assoc _ _ _ ⟩
      (G' ∘co ((M₂.inR ∘ ℰP.p₂) ∘co (GI (Creal Q δ̂₂) .Iso.fwd ∘ ℰP.p₂))) ∘co Gmap Q δ̂₁ F'
    ≈˘⟨ CoK.∘-cong (CoK.assoc _ _ _) ≈-refl ⟩
      ((G' ∘co (M₂.inR ∘ ℰP.p₂)) ∘co (GI (Creal Q δ̂₂) .Iso.fwd ∘ ℰP.p₂)) ∘co Gmap Q δ̂₁ F'
    ≈⟨ CoK.∘-cong (CoK.∘-cong (M₂.foldR-β _) ≈-refl) ≈-refl ⟩
      (((M₁.inR ∘ (GI (Creal Q δ̂₁) .Iso.bwd ∘ ℰP.p₂)) ∘co Gmap Q δ̂₂ G') ∘co (GI (Creal Q δ̂₂) .Iso.fwd ∘ ℰP.p₂)) ∘co Gmap Q δ̂₁ F'
    ≈⟨ CoK.∘-cong (CoK.assoc _ _ _) ≈-refl ⟩
      ((M₁.inR ∘ (GI (Creal Q δ̂₁) .Iso.bwd ∘ ℰP.p₂)) ∘co (Gmap Q δ̂₂ G' ∘co (GI (Creal Q δ̂₂) .Iso.fwd ∘ ℰP.p₂))) ∘co Gmap Q δ̂₁ F'
    ≈⟨ CoK.∘-cong (CoK.∘-cong ≈-refl (cross G')) ≈-refl ⟩
      ((M₁.inR ∘ (GI (Creal Q δ̂₁) .Iso.bwd ∘ ℰP.p₂)) ∘co (GI (Creal Q δ̂₁) .Iso.fwd ∘ Gmap Q δ̂₁ G')) ∘co Gmap Q δ̂₁ F'
    ≈⟨ CoK.∘-cong ag-cross ≈-refl ⟩
      ((M₁.inR ∘ ℰP.p₂) ∘co Gmap Q δ̂₁ G') ∘co Gmap Q δ̂₁ F'
    ≈⟨ CoK.assoc _ _ _ ⟩
      (M₁.inR ∘ ℰP.p₂) ∘co (Gmap Q δ̂₁ G' ∘co Gmap Q δ̂₁ F')
    ≈˘⟨ CoK.∘-cong ≈-refl (Gmap-∘co Q δ̂₁ G' F') ⟩
      (M₁.inR ∘ ℰP.p₂) ∘co Gmap Q δ̂₁ (G' ∘co F')
    ∎
    where open ≈-Reasoning isEquiv

  af-cross : ((M₂.inR ∘ (GI (Creal Q δ̂₂) .Iso.fwd ∘ ℰP.p₂)) ∘co (GI (Creal Q δ̂₂) .Iso.bwd ∘ Gmap Q δ̂₂ F'))
             ≈ ((M₂.inR ∘ ℰP.p₂) ∘co Gmap Q δ̂₂ F')
  af-cross =
    begin
      (M₂.inR ∘ (GI (Creal Q δ̂₂) .Iso.fwd ∘ ℰP.p₂)) ∘ ℰP.pair ℰP.p₁ (GI (Creal Q δ̂₂) .Iso.bwd ∘ Gmap Q δ̂₂ F')
    ≈⟨ assoc _ _ _ ⟩
      M₂.inR ∘ ((GI (Creal Q δ̂₂) .Iso.fwd ∘ ℰP.p₂) ∘ ℰP.pair ℰP.p₁ (GI (Creal Q δ̂₂) .Iso.bwd ∘ Gmap Q δ̂₂ F'))
    ≈⟨ ∘-cong ≈-refl (≈-trans (assoc _ _ _) (∘-cong ≈-refl (ℰP.pair-p₂ _ _))) ⟩
      M₂.inR ∘ (GI (Creal Q δ̂₂) .Iso.fwd ∘ (GI (Creal Q δ̂₂) .Iso.bwd ∘ Gmap Q δ̂₂ F'))
    ≈˘⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
      M₂.inR ∘ ((GI (Creal Q δ̂₂) .Iso.fwd ∘ GI (Creal Q δ̂₂) .Iso.bwd) ∘ Gmap Q δ̂₂ F')
    ≈⟨ ∘-cong ≈-refl (≈-trans (∘-cong (GI (Creal Q δ̂₂) .Iso.fwd∘bwd≈id) ≈-refl) id-left) ⟩
      M₂.inR ∘ Gmap Q δ̂₂ F'
    ≈˘⟨ ≈-trans (assoc _ _ _) (∘-cong ≈-refl (ℰP.pair-p₂ _ _)) ⟩
      (M₂.inR ∘ ℰP.p₂) ∘ ℰP.pair ℰP.p₁ (Gmap Q δ̂₂ F')
    ∎ where open ≈-Reasoning isEquiv


  -- The composite F' ∘co G' likewise, using the flipped crossing.
  square-FG : ((F' ∘co G') ∘co (M₂.inR ∘ ℰP.p₂)) ≈ ((M₂.inR ∘ ℰP.p₂) ∘co Gmap Q δ̂₂ (F' ∘co G'))
  square-FG =
    begin
      (F' ∘co G') ∘co (M₂.inR ∘ ℰP.p₂)
    ≈⟨ CoK.assoc _ _ _ ⟩
      F' ∘co (G' ∘co (M₂.inR ∘ ℰP.p₂))
    ≈⟨ CoK.∘-cong ≈-refl (M₂.foldR-β _) ⟩
      F' ∘co ((M₁.inR ∘ (GI (Creal Q δ̂₁) .Iso.bwd ∘ ℰP.p₂)) ∘co Gmap Q δ̂₂ G')
    ≈⟨ CoK.∘-cong ≈-refl (CoK.∘-cong (≈-trans (≈-sym (assoc _ _ _)) (≈-sym (co-pure M₁.inR (GI (Creal Q δ̂₁) .Iso.bwd)))) ≈-refl) ⟩
      F' ∘co (((M₁.inR ∘ ℰP.p₂) ∘co (GI (Creal Q δ̂₁) .Iso.bwd ∘ ℰP.p₂)) ∘co Gmap Q δ̂₂ G')
    ≈˘⟨ CoK.assoc _ _ _ ⟩
      (F' ∘co ((M₁.inR ∘ ℰP.p₂) ∘co (GI (Creal Q δ̂₁) .Iso.bwd ∘ ℰP.p₂))) ∘co Gmap Q δ̂₂ G'
    ≈˘⟨ CoK.∘-cong (CoK.assoc _ _ _) ≈-refl ⟩
      ((F' ∘co (M₁.inR ∘ ℰP.p₂)) ∘co (GI (Creal Q δ̂₁) .Iso.bwd ∘ ℰP.p₂)) ∘co Gmap Q δ̂₂ G'
    ≈⟨ CoK.∘-cong (CoK.∘-cong (M₁.foldR-β _) ≈-refl) ≈-refl ⟩
      (((M₂.inR ∘ (GI (Creal Q δ̂₂) .Iso.fwd ∘ ℰP.p₂)) ∘co Gmap Q δ̂₁ F') ∘co (GI (Creal Q δ̂₁) .Iso.bwd ∘ ℰP.p₂)) ∘co Gmap Q δ̂₂ G'
    ≈⟨ CoK.∘-cong (CoK.assoc _ _ _) ≈-refl ⟩
      ((M₂.inR ∘ (GI (Creal Q δ̂₂) .Iso.fwd ∘ ℰP.p₂)) ∘co (Gmap Q δ̂₁ F' ∘co (GI (Creal Q δ̂₁) .Iso.bwd ∘ ℰP.p₂))) ∘co Gmap Q δ̂₂ G'
    ≈⟨ CoK.∘-cong (CoK.∘-cong ≈-refl (cross-flip F')) ≈-refl ⟩
      ((M₂.inR ∘ (GI (Creal Q δ̂₂) .Iso.fwd ∘ ℰP.p₂)) ∘co (GI (Creal Q δ̂₂) .Iso.bwd ∘ Gmap Q δ̂₂ F')) ∘co Gmap Q δ̂₂ G'
    ≈⟨ CoK.∘-cong af-cross ≈-refl ⟩
      ((M₂.inR ∘ ℰP.p₂) ∘co Gmap Q δ̂₂ F') ∘co Gmap Q δ̂₂ G'
    ≈⟨ CoK.assoc _ _ _ ⟩
      (M₂.inR ∘ ℰP.p₂) ∘co (Gmap Q δ̂₂ F' ∘co Gmap Q δ̂₂ G')
    ≈˘⟨ CoK.∘-cong ≈-refl (Gmap-∘co Q δ̂₂ F' G') ⟩
      (M₂.inR ∘ ℰP.p₂) ∘co Gmap Q δ̂₂ (F' ∘co G')
    ∎
    where open ≈-Reasoning isEquiv

  -- Composites in context agree with plain composites of the induced maps.
  plait : ∀ {X Y Z : obj} (u : ℰP.prod 𝟙 Y ⇒ Z) (v : ℰP.prod 𝟙 X ⇒ Y) →
          ((u ∘ ℰP.pair ℰTm.to-terminal (id _)) ∘ (v ∘ ℰP.pair ℰTm.to-terminal (id _)))
          ≈ ((u ∘co v) ∘ ℰP.pair ℰTm.to-terminal (id _))
  plait u v =
    begin
      (u ∘ ℰP.pair ℰTm.to-terminal (id _)) ∘ (v ∘ ℰP.pair ℰTm.to-terminal (id _))
    ≈⟨ assoc _ _ _ ⟩
      u ∘ (ℰP.pair ℰTm.to-terminal (id _) ∘ (v ∘ ℰP.pair ℰTm.to-terminal (id _)))
    ≈⟨ ∘-cong ≈-refl (ℰP.pair-natural _ _ _) ⟩
      u ∘ ℰP.pair (ℰTm.to-terminal ∘ (v ∘ ℰP.pair ℰTm.to-terminal (id _))) (id _ ∘ (v ∘ ℰP.pair ℰTm.to-terminal (id _)))
    ≈⟨ ∘-cong ≈-refl (ℰP.pair-cong (ℰTm.to-terminal-unique _ _) id-left) ⟩
      u ∘ ℰP.pair (ℰP.p₁ ∘ ℰP.pair ℰTm.to-terminal (id _)) (v ∘ ℰP.pair ℰTm.to-terminal (id _))
    ≈˘⟨ ∘-cong ≈-refl (ℰP.pair-natural _ _ _) ⟩
      u ∘ (ℰP.pair ℰP.p₁ v ∘ ℰP.pair ℰTm.to-terminal (id _))
    ≈˘⟨ assoc _ _ _ ⟩
      (u ∘ ℰP.pair ℰP.p₁ v) ∘ ℰP.pair ℰTm.to-terminal (id _)
    ∎ where open ≈-Reasoning isEquiv

  mu-collapse : Iso (Creal Q δ̂₁) (Creal Q δ̂₂)
  mu-collapse .Iso.fwd = F' ∘ ℰP.pair ℰTm.to-terminal (id _)
  mu-collapse .Iso.bwd = G' ∘ ℰP.pair ℰTm.to-terminal (id _)
  mu-collapse .Iso.bwd∘fwd≈id =
    ≈-trans (plait G' F')
      (≈-trans (∘-cong (≈-trans (M₁.foldR-η _ _ square-GF) (≈-sym (M₁.foldR-η {Γ = 𝟙} _ _ square-p₂₁))) ≈-refl)
        (ℰP.pair-p₂ _ _))
  mu-collapse .Iso.fwd∘bwd≈id =
    ≈-trans (plait F' G')
      (≈-trans (∘-cong (≈-trans (M₂.foldR-η _ _ square-FG) (≈-sym (M₂.foldR-η {Γ = 𝟙} _ _ square-p₂₂))) ≈-refl)
        (ℰP.pair-p₂ _ _))

-- The μ-collapse at pointwise-identity isomorphisms is the identity.
mu-collapse-refl : ∀ {n} (Q : Poly ℰ (suc n)) (CQ : CollapseAt Q) (δ̂ : Fin n → FM.Obj)
                   (isos : ∀ i → Iso (realise .fobj (δ̂ i)) (realise .fobj (δ̂ i))) →
                   (∀ i → isos i .Iso.fwd ≈ id _) →
                   MuCollapse.mu-collapse Q CQ δ̂ δ̂ isos .Iso.fwd ≈ id _
mu-collapse-refl {n} Q CQ δ̂ isos hyps =
  begin
    MC.F' ∘ ℰP.pair MC.ℰTm.to-terminal (id _)
  ≈⟨ ∘-cong F'-id ≈-refl ⟩
    ℰP.p₂ ∘ ℰP.pair MC.ℰTm.to-terminal (id _)
  ≈⟨ ℰP.pair-p₂ _ _ ⟩
    id _
  ∎
  where
    open ≈-Reasoning isEquiv

    module MC = MuCollapse Q CQ δ̂ δ̂ isos

    GI-id : ∀ (A : obj) → MC.GI A .Iso.fwd ≈ id _
    GI-id A = CQ .CollapseAt.refl-iso (extend δ̂ (η .fobj A)) (MC.extIsos A) exthyps
      where
        exthyps : ∀ i → MC.extIsos A i .Iso.fwd ≈ id _
        exthyps Fin.zero    = ≈-refl
        exthyps (Fin.suc i) = hyps i

    F'-id : MC.F' ≈ ℰP.p₂
    F'-id =
      ≈-trans
        (MC.M₁.foldR-cong
          (∘-cong ≈-refl (≈-trans (∘-cong (GI-id (Creal Q δ̂)) ≈-refl) id-left)))
        (≈-sym (MC.M₁.foldR-η {Γ = MC.𝟙} _ ℰP.p₂ MC.square-p₂₁))


-- A transposed morphism squares with the counits against its own counit form.
fmorη-ctxη-square : ∀ (Γ : obj) (X̂ Ŷ : FM.Obj) (w : FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) X̂) Ŷ) →
                    (fmorη Γ X̂ w ∘co (realise-η-iso (realise .fobj X̂) .Iso.fwd ∘ ℰP.p₂))
                    ≈ (realise-η-iso (realise .fobj Ŷ) .Iso.fwd ∘ fmorη Γ (η .fobj (realise .fobj X̂)) (ctxη Γ (realise .fobj X̂) (fmorη Γ X̂ w)))
fmorη-ctxη-square Γ X̂ Ŷ w =
  ≈-sym (≈-trans (ctxη-counit Γ (realise .fobj X̂) (fmorη Γ X̂ w))
    (∘-cong ≈-refl (ℰP.pair-cong id-left ≈-refl)))

-- Congruence of the realised strong action.
Gmap-cong : ∀ {n} (P : Poly ℰ (suc n)) (δ̂ : Fin n → FM.Obj) {Γ A B : obj}
            {h₁ h₂ : ℰP.prod Γ A ⇒ B} → h₁ ≈ h₂ → Gmap P δ̂ h₁ ≈ Gmap P δ̂ h₂
Gmap-cong P δ̂ {Γ} {A} {B} {h₁} {h₂} e =
  ∘-cong (realise .fmor-cong (FMuI.strong-fmor-cong (Poly-map η P) eqs)) ≈-refl
  where
    eqs : ∀ i → Category._≈_ FM.cat
            (FMu.strong-extend-mor (λ j → FM.Fam𝒞-P.p₂) (ctxη Γ A h₁) i)
            (FMu.strong-extend-mor (λ j → FM.Fam𝒞-P.p₂) (ctxη Γ A h₂) i)
    eqs Fin.zero    = FR.untranspose-cong (∘-cong e ≈-refl)
    eqs (Fin.suc i) = FamC.≈-refl

-- The realised strong μ-action is the fold of the realised algebra, corrected
-- by the collapse at the bound-variable entry.
module SμfFold {n} (Q : Poly ℰ (suc n)) (CQ : CollapseAt Q) {Γ : obj}
    (δ̂ ε̂ : Fin n → FM.Obj)
    (gs : ∀ i → FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) (δ̂ i)) (ε̂ i))
  where

  private
    Q̂ = Poly-map η Q
    module Mδ = Initiality Q δ̂ CQ

    sμf : FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) (FM.μObj Q̂ δ̂)) (FM.μObj Q̂ ε̂)
    sμf = FMu.strong-μ-fmor Q̂ gs

    alg : FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) (FM.fobj FM.μObj Q̂ (extend δ̂ (FM.μObj Q̂ ε̂)))) (FM.μObj Q̂ ε̂)
    alg = FM.Mor-∘ (FMu.α Q̂ ε̂) (FMu.strong-fmor Q̂ (FMu.strong-extend-mor gs FM.Fam𝒞-P.p₂))

  KKisos : ∀ i → Iso (realise .fobj (extend δ̂ (η .fobj (Creal Q ε̂)) i))
                     (realise .fobj (extend δ̂ (FM.μObj Q̂ ε̂) i))
  KKisos Fin.zero    = realise-η-iso (Creal Q ε̂)
  KKisos (Fin.suc i) = Iso-refl

  KKε : Iso (realise .fobj (FM.fobj FM.μObj Q̂ (extend δ̂ (η .fobj (Creal Q ε̂)))))
            (realise .fobj (FM.fobj FM.μObj Q̂ (extend δ̂ (FM.μObj Q̂ ε̂))))
  KKε = CQ .CollapseAt.iso (extend δ̂ (η .fobj (Creal Q ε̂))) (extend δ̂ (FM.μObj Q̂ ε̂)) KKisos

  aStar : ℰP.prod Γ (Greal Q δ̂ (Creal Q ε̂)) ⇒ Creal Q ε̂
  aStar = fmorη Γ (FM.fobj FM.μObj Q̂ (extend δ̂ (FM.μObj Q̂ ε̂))) alg ∘co (KKε .Iso.fwd ∘ ℰP.p₂)

  A' : ℰP.prod Γ (Creal Q δ̂) ⇒ Creal Q ε̂
  A' = fmorη Γ (FM.μObj (Poly-map η Q) δ̂) (FMu.strong-μ-fmor (Poly-map η Q) gs)

  sμf-square : (A' ∘co (Mδ.inR ∘ ℰP.p₂)) ≈ (aStar ∘co Gmap Q δ̂ A')
  sμf-square =
    begin
      A' ∘co (Mδ.inR ∘ ℰP.p₂)
    ≈˘⟨ CoK.∘-cong ≈-refl (co-pure _ _) ⟩
      A' ∘co ((realise .fmor (FMu.α Q̂ δ̂) ∘ ℰP.p₂) ∘co (CQ .CollapseAt.iso (extend δ̂ (η .fobj (Creal Q δ̂))) (extend δ̂ (FM.μObj Q̂ δ̂)) Mδ.inIsos .Iso.fwd ∘ ℰP.p₂))
    ≈˘⟨ CoK.assoc _ _ _ ⟩
      (A' ∘co (realise .fmor (FMu.α Q̂ δ̂) ∘ ℰP.p₂)) ∘co (CQ .CollapseAt.iso (extend δ̂ (η .fobj (Creal Q δ̂))) (extend δ̂ (FM.μObj Q̂ δ̂)) Mδ.inIsos .Iso.fwd ∘ ℰP.p₂)
    ≈⟨ CoK.∘-cong step-β ≈-refl ⟩
      (fmorη Γ (FM.fobj FM.μObj Q̂ (extend δ̂ (FM.μObj Q̂ ε̂))) alg ∘co fmorη Γ (FM.fobj FM.μObj Q̂ (extend δ̂ (FM.μObj Q̂ δ̂))) (FMu.strong-fmor Q̂ (FMu.strong-extend-mor (λ i → FM.Fam𝒞-P.p₂) sμf))) ∘co (CQ .CollapseAt.iso (extend δ̂ (η .fobj (Creal Q δ̂))) (extend δ̂ (FM.μObj Q̂ δ̂)) Mδ.inIsos .Iso.fwd ∘ ℰP.p₂)
    ≈⟨ CoK.assoc _ _ _ ⟩
      fmorη Γ (FM.fobj FM.μObj Q̂ (extend δ̂ (FM.μObj Q̂ ε̂))) alg ∘co (fmorη Γ (FM.fobj FM.μObj Q̂ (extend δ̂ (FM.μObj Q̂ δ̂))) (FMu.strong-fmor Q̂ (FMu.strong-extend-mor (λ i → FM.Fam𝒞-P.p₂) sμf)) ∘co (CQ .CollapseAt.iso (extend δ̂ (η .fobj (Creal Q δ̂))) (extend δ̂ (FM.μObj Q̂ δ̂)) Mδ.inIsos .Iso.fwd ∘ ℰP.p₂))
    ≈⟨ CoK.∘-cong ≈-refl inner-nat ⟩
      fmorη Γ (FM.fobj FM.μObj Q̂ (extend δ̂ (FM.μObj Q̂ ε̂))) alg ∘co (KKε .Iso.fwd ∘ Gmap Q δ̂ A')
    ≈˘⟨ CoK.∘-cong ≈-refl (≈-trans (assoc _ _ _) (∘-cong ≈-refl (ℰP.pair-p₂ _ _))) ⟩
      fmorη Γ (FM.fobj FM.μObj Q̂ (extend δ̂ (FM.μObj Q̂ ε̂))) alg ∘co ((KKε .Iso.fwd ∘ ℰP.p₂) ∘co Gmap Q δ̂ A')
    ≈˘⟨ CoK.assoc _ _ _ ⟩
      aStar ∘co Gmap Q δ̂ A'
    ∎
    where
      open ≈-Reasoning isEquiv

      step-β : (A' ∘co (realise .fmor (FMu.α Q̂ δ̂) ∘ ℰP.p₂))
               ≈ (fmorη Γ (FM.fobj FM.μObj Q̂ (extend δ̂ (FM.μObj Q̂ ε̂))) alg ∘co fmorη Γ (FM.fobj FM.μObj Q̂ (extend δ̂ (FM.μObj Q̂ δ̂))) (FMu.strong-fmor Q̂ (FMu.strong-extend-mor (λ i → FM.Fam𝒞-P.p₂) sμf)))
      step-β =
        ≈-trans (CoK.∘-cong ≈-refl (≈-sym (fmorη-pure Γ (FM.fobj FM.μObj Q̂ (extend δ̂ (FM.μObj Q̂ δ̂))) (FMu.α Q̂ δ̂))))
          (≈-trans (≈-sym (fmorη-∘co Γ (FM.fobj FM.μObj Q̂ (extend δ̂ (FM.μObj Q̂ δ̂))) sμf _))
            (≈-trans (fmorη-cong (FM.hasMuLaws .FM.HasMuLaws.⦅⦆-β {P = Q̂} {δ = δ̂} _))
              (fmorη-∘co Γ (FM.fobj FM.μObj Q̂ (extend δ̂ (FM.μObj Q̂ δ̂))) alg _)))

      inner-nat : (fmorη Γ (FM.fobj FM.μObj Q̂ (extend δ̂ (FM.μObj Q̂ δ̂))) (FMu.strong-fmor Q̂ (FMu.strong-extend-mor (λ i → FM.Fam𝒞-P.p₂) sμf))
                    ∘co (CQ .CollapseAt.iso (extend δ̂ (η .fobj (Creal Q δ̂))) (extend δ̂ (FM.μObj Q̂ δ̂)) Mδ.inIsos .Iso.fwd ∘ ℰP.p₂))
                  ≈ (KKε .Iso.fwd ∘ Gmap Q δ̂ A')
      inner-nat =
        CQ .CollapseAt.natural (extend δ̂ (η .fobj (Creal Q δ̂))) (extend δ̂ (FM.μObj Q̂ δ̂)) Mδ.inIsos KKisos
          (FMu.strong-extend-mor (λ i → FM.Fam𝒞-P.p₂) (ctxη Γ (Creal Q δ̂) A'))
          (FMu.strong-extend-mor (λ i → FM.Fam𝒞-P.p₂) sμf)
          compats
        where
          compats : ∀ i → (fmorη Γ (extend δ̂ (FM.μObj Q̂ δ̂) i) (FMu.strong-extend-mor (λ j → FM.Fam𝒞-P.p₂) sμf i) ∘co (Mδ.inIsos i .Iso.fwd ∘ ℰP.p₂))
                    ≈ (KKisos i .Iso.fwd ∘ fmorη Γ (extend δ̂ (η .fobj (Creal Q δ̂)) i) (FMu.strong-extend-mor (λ j → FM.Fam𝒞-P.p₂) (ctxη Γ (Creal Q δ̂) A') i))
          compats Fin.zero    = fmorη-ctxη-square Γ (FM.μObj Q̂ δ̂) (FM.μObj Q̂ ε̂) sμf
          compats (Fin.suc i) = sq-refl _

  -- The characterisation.
  sμf-fold : fmorη Γ (FM.μObj Q̂ δ̂) (FMu.strong-μ-fmor Q̂ gs) ≈ Mδ.foldR aStar
  sμf-fold = Mδ.foldR-η aStar A' sμf-square

-- Plain-context conversions at the terminal object.
private
  module ℰT' = HasTerminal ℰT

  sect-p₂ : ∀ {X : obj} → (ℰP.pair (ℰT'.to-terminal {X}) (id X) ∘ ℰP.p₂ {ℰT'.witness} {X}) ≈ id _
  sect-p₂ {X} =
    ≈-trans (ℰP.pair-natural _ _ _)
      (≈-trans (ℰP.pair-cong (ℰT'.to-terminal-unique _ _) id-left) pair-p₁p₂-id)

-- The plain form of a fold in the terminal context commutes with the algebra
-- map, against the plain form of the realised strong action.
plain-β : ∀ {n} (Q : Poly ℰ (suc n)) (δ̂ : Fin n → FM.Obj) (CQ : CollapseAt Q) {D : obj}
          (c : ℰP.prod ℰT'.witness (Greal Q δ̂ D) ⇒ D) →
          ((Initiality.foldR Q δ̂ CQ c ∘ ℰP.pair ℰT'.to-terminal (id _)) ∘ Initiality.inR Q δ̂ CQ)
          ≈ (c ∘ ℰP.pair ℰT'.to-terminal (Gmap Q δ̂ (Initiality.foldR Q δ̂ CQ c) ∘ ℰP.pair ℰT'.to-terminal (id _)))
plain-β Q δ̂ CQ {D} c =
  ≈-trans left
    (≈-trans (≈-sym lhs-sect)
      (≈-trans (∘-cong (M.foldR-β {Γ = ℰT'.witness} c) ≈-refl) rhs-sect))
  where
    module M = Initiality Q δ̂ CQ

    left : ((M.foldR c ∘ ℰP.pair ℰT'.to-terminal (id _)) ∘ M.inR)
           ≈ (M.foldR c ∘ ℰP.pair ℰT'.to-terminal M.inR)
    left =
      ≈-trans (assoc _ _ _)
        (≈-trans (∘-cong ≈-refl (ℰP.pair-natural _ _ _))
          (∘-cong ≈-refl (ℰP.pair-cong (ℰT'.to-terminal-unique _ _) id-left)))

    lhs-sect : ((M.foldR c ∘co (M.inR ∘ ℰP.p₂)) ∘ ℰP.pair ℰT'.to-terminal (id _))
               ≈ (M.foldR c ∘ ℰP.pair ℰT'.to-terminal M.inR)
    lhs-sect =
      ≈-trans (assoc _ _ _)
        (≈-trans (∘-cong ≈-refl (ℰP.pair-natural _ _ _))
          (∘-cong ≈-refl (ℰP.pair-cong (ℰT'.to-terminal-unique _ _)
            (≈-trans (assoc _ _ _) (≈-trans (∘-cong ≈-refl (ℰP.pair-p₂ _ _)) id-right)))))

    rhs-sect : ((c ∘co Gmap Q δ̂ (M.foldR c)) ∘ ℰP.pair ℰT'.to-terminal (id _))
               ≈ (c ∘ ℰP.pair ℰT'.to-terminal (Gmap Q δ̂ (M.foldR c) ∘ ℰP.pair ℰT'.to-terminal (id _)))
    rhs-sect =
      ≈-trans (assoc _ _ _)
        (≈-trans (∘-cong ≈-refl (ℰP.pair-natural _ _ _))
          (∘-cong ≈-refl (ℰP.pair-cong (ℰT'.to-terminal-unique _ _) ≈-refl)))

-- Move an isomorphism in context across an equation.
co-iso-move : ∀ {Γ X Y Z : obj} (I : Iso X Y)
              {u : ℰP.prod Γ Y ⇒ Z} {v : ℰP.prod Γ X ⇒ Z} →
              u ≈ (v ∘co (I .Iso.bwd ∘ ℰP.p₂)) → (u ∘co (I .Iso.fwd ∘ ℰP.p₂)) ≈ v
co-iso-move I {u} {v} eq =
  ≈-trans (CoK.∘-cong eq ≈-refl)
    (≈-trans (CoK.assoc _ _ _)
      (≈-trans (CoK.∘-cong ≈-refl (≈-trans (co-pure _ _) (≈-trans (∘-cong (I .Iso.bwd∘fwd≈id) ≈-refl) id-left)))
        CoK.id-right))

-- The realised algebra map, recovered from the collapse form of inR.
inR-K : ∀ {n} (Q : Poly ℰ (suc n)) (δ̂ : Fin n → FM.Obj) (CQ : CollapseAt Q) →
        realise .fmor (FMu.α (Poly-map η Q) δ̂)
        ≈ (Initiality.inR Q δ̂ CQ ∘
           CQ .CollapseAt.iso (extend δ̂ (η .fobj (Creal Q δ̂))) (extend δ̂ (FM.μObj (Poly-map η Q) δ̂)) (Initiality.inIsos Q δ̂ CQ) .Iso.bwd)
inR-K Q δ̂ CQ =
  ≈-sym (≈-trans (assoc _ _ _)
    (≈-trans (∘-cong ≈-refl (CQ .CollapseAt.iso _ _ (Initiality.inIsos Q δ̂ CQ) .Iso.fwd∘bwd≈id)) id-right))

-- The forward map of the μ-collapse is a morphism of algebras.
mu-collapse-fwd-in : ∀ {n} (Q : Poly ℰ (suc n)) (CQ : CollapseAt Q)
                     (δ̂₁ δ̂₂ : Fin n → FM.Obj)
                     (isos : ∀ i → Iso (realise .fobj (δ̂₁ i)) (realise .fobj (δ̂₂ i))) →
                     (MuCollapse.mu-collapse Q CQ δ̂₁ δ̂₂ isos .Iso.fwd ∘ Initiality.inR Q δ̂₁ CQ)
                     ≈ (Initiality.inR Q δ̂₂ CQ ∘
                        (MuCollapse.GI Q CQ δ̂₁ δ̂₂ isos (Creal Q δ̂₂) .Iso.fwd ∘
                         (Gmap Q δ̂₁ (MuCollapse.mu-collapse Q CQ δ̂₁ δ̂₂ isos .Iso.fwd ∘ ℰP.p₂) ∘ ℰP.pair ℰT'.to-terminal (id _))))
mu-collapse-fwd-in Q CQ δ̂₁ δ̂₂ isos =
  ≈-trans (plain-β Q δ̂₁ CQ _)
    (≈-trans (assoc _ _ _)
      (∘-cong ≈-refl
        (≈-trans (≈-trans (assoc _ _ _) (∘-cong ≈-refl (ℰP.pair-p₂ _ _)))
          (∘-cong ≈-refl (∘-cong (Gmap-cong Q δ̂₁ plain-eq) ≈-refl)))))
  where
    module MC = MuCollapse Q CQ δ̂₁ δ̂₂ isos

    plain-eq : MC.F' ≈ (MC.mu-collapse .Iso.fwd ∘ ℰP.p₂)
    plain-eq =
      ≈-sym (≈-trans (assoc _ _ _) (≈-trans (∘-cong ≈-refl sect-p₂) id-right))

-- The backward map of the μ-collapse is a morphism of algebras.
mu-collapse-bwd-in : ∀ {n} (Q : Poly ℰ (suc n)) (CQ : CollapseAt Q)
                     (δ̂₁ δ̂₂ : Fin n → FM.Obj)
                     (isos : ∀ i → Iso (realise .fobj (δ̂₁ i)) (realise .fobj (δ̂₂ i))) →
                     (MuCollapse.mu-collapse Q CQ δ̂₁ δ̂₂ isos .Iso.bwd ∘ Initiality.inR Q δ̂₂ CQ)
                     ≈ (Initiality.inR Q δ̂₁ CQ ∘
                        (MuCollapse.GI Q CQ δ̂₁ δ̂₂ isos (Creal Q δ̂₁) .Iso.bwd ∘
                         (Gmap Q δ̂₂ (MuCollapse.mu-collapse Q CQ δ̂₁ δ̂₂ isos .Iso.bwd ∘ ℰP.p₂) ∘ ℰP.pair ℰT'.to-terminal (id _))))
mu-collapse-bwd-in Q CQ δ̂₁ δ̂₂ isos =
  ≈-trans (plain-β Q δ̂₂ CQ _)
    (≈-trans (assoc _ _ _)
      (∘-cong ≈-refl
        (≈-trans (≈-trans (assoc _ _ _) (∘-cong ≈-refl (ℰP.pair-p₂ _ _)))
          (∘-cong ≈-refl (∘-cong (Gmap-cong Q δ̂₂ plain-eq) ≈-refl)))))
  where
    module MC = MuCollapse Q CQ δ̂₁ δ̂₂ isos

    plain-eq : MC.G' ≈ (MC.mu-collapse .Iso.bwd ∘ ℰP.p₂)
    plain-eq =
      ≈-sym (≈-trans (assoc _ _ _) (≈-trans (∘-cong ≈-refl sect-p₂) id-right))

-- Extend an isomorphism family by an isomorphism at the bound entry.
mixed : ∀ {n} {δ̂₁ δ̂₂ : Fin n → FM.Obj}
        (isos : ∀ i → Iso (realise .fobj (δ̂₁ i)) (realise .fobj (δ̂₂ i)))
        {Ŷ₁ Ŷ₂ : FM.Obj} (J : Iso (realise .fobj Ŷ₁) (realise .fobj Ŷ₂)) →
        ∀ i → Iso (realise .fobj (extend δ̂₁ Ŷ₁ i)) (realise .fobj (extend δ̂₂ Ŷ₂ i))
mixed isos J Fin.zero    = J
mixed isos J (Fin.suc i) = isos i

-- The strong action at extended environments commutes with an isomorphism at
-- the bound entry and the given isomorphisms elsewhere.
cross-mixed : ∀ {n} (Q : Poly ℰ (suc n)) (CQ : CollapseAt Q) {Γ : obj}
              {δ̂₁ δ̂₂ ε̂₁ ε̂₂ : Fin n → FM.Obj}
              (isosδ : ∀ i → Iso (realise .fobj (δ̂₁ i)) (realise .fobj (δ̂₂ i)))
              (isosε : ∀ i → Iso (realise .fobj (ε̂₁ i)) (realise .fobj (ε̂₂ i)))
              {Ŷ₁ Ŷ₂ : FM.Obj} (J : Iso (realise .fobj Ŷ₁) (realise .fobj Ŷ₂))
              (gs₁ : ∀ i → FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) (δ̂₁ i)) (ε̂₁ i))
              (gs₂ : ∀ i → FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) (δ̂₂ i)) (ε̂₂ i)) →
              (∀ i → (fmorη Γ (δ̂₂ i) (gs₂ i) ∘co (isosδ i .Iso.fwd ∘ ℰP.p₂))
                     ≈ (isosε i .Iso.fwd ∘ fmorη Γ (δ̂₁ i) (gs₁ i))) →
              (fmorη Γ (FM.fobj FM.μObj (Poly-map η Q) (extend δ̂₂ Ŷ₂))
                 (FMu.strong-fmor (Poly-map η Q) (FMu.strong-extend-mor gs₂ FM.Fam𝒞-P.p₂))
                ∘co (CQ .CollapseAt.iso (extend δ̂₁ Ŷ₁) (extend δ̂₂ Ŷ₂) (mixed isosδ J) .Iso.fwd ∘ ℰP.p₂))
              ≈ (CQ .CollapseAt.iso (extend ε̂₁ Ŷ₁) (extend ε̂₂ Ŷ₂) (mixed isosε J) .Iso.fwd
                 ∘ fmorη Γ (FM.fobj FM.μObj (Poly-map η Q) (extend δ̂₁ Ŷ₁))
                     (FMu.strong-fmor (Poly-map η Q) (FMu.strong-extend-mor gs₁ FM.Fam𝒞-P.p₂)))
cross-mixed Q CQ {Γ} {δ̂₁} {δ̂₂} {ε̂₁} {ε̂₂} isosδ isosε {Ŷ₁} {Ŷ₂} J gs₁ gs₂ sqs =
  CQ .CollapseAt.natural (extend δ̂₁ Ŷ₁) (extend δ̂₂ Ŷ₂) (mixed isosδ J) (mixed isosε J)
    (FMu.strong-extend-mor gs₁ FM.Fam𝒞-P.p₂)
    (FMu.strong-extend-mor gs₂ FM.Fam𝒞-P.p₂)
    compats
  where
    compats : ∀ i → (fmorη Γ (extend δ̂₂ Ŷ₂ i) (FMu.strong-extend-mor gs₂ FM.Fam𝒞-P.p₂ i) ∘co (mixed isosδ J i .Iso.fwd ∘ ℰP.p₂))
              ≈ (mixed isosε J i .Iso.fwd ∘ fmorη Γ (extend δ̂₁ Ŷ₁ i) (FMu.strong-extend-mor gs₁ FM.Fam𝒞-P.p₂ i))
    compats Fin.zero    = sq-p₂ J
    compats (Fin.suc i) = sqs i

-- Untransposition absorbs realised precomposition.
untranspose-pre : ∀ {V W : FM.Obj} {X : obj}
                  (g : realise .fobj W ⇒ X) (w : FM.Mor V W) →
                  Category._≈_ FM.cat (untranspose (g ∘ realise .fmor w)) (FM.Mor-∘ (untranspose g) w)
untranspose-pre {V} {W} {X} g w =
  FamC.≈-sym
    (FamC.≈-trans (FamC.≈-sym (FR.untranspose-transpose (FM.Mor-∘ (untranspose g) w)))
      (FR.untranspose-cong
        (≈-trans (FR.transpose-natural₁ (untranspose g) w)
          (∘-cong (FR.transpose-untranspose g) ≈-refl))))

-- The transposed form of a pure context morphism.
ctxη-pure : ∀ (Γ A : obj) {B : obj} (m : A ⇒ B) →
            Category._≈_ FM.cat (ctxη Γ A (m ∘ ℰP.p₂))
              (FM.Mor-∘ (untranspose (m ∘ realise-η-iso A .Iso.fwd)) (FM.Fam𝒞-P.p₂ {x = η .fobj Γ} {y = η .fobj A}))
ctxη-pure Γ A {B} m =
  FamC.≈-trans (FR.untranspose-cong inner) (untranspose-pre (m ∘ realise-η-iso A .Iso.fwd) _)
  where
    inner : ((m ∘ ℰP.p₂) ∘ (ℰP.prod-m (id _) (realise-η-iso A .Iso.fwd) ∘ prodη Γ (η .fobj A) .Iso.fwd))
            ≈ ((m ∘ realise-η-iso A .Iso.fwd) ∘ realise .fmor (FM.Fam𝒞-P.p₂ {x = η .fobj Γ} {y = η .fobj A}))
    inner =
      begin
        (m ∘ ℰP.p₂) ∘ (ℰP.prod-m (id _) (realise-η-iso A .Iso.fwd) ∘ prodη Γ (η .fobj A) .Iso.fwd)
      ≈˘⟨ assoc _ _ _ ⟩
        ((m ∘ ℰP.p₂) ∘ ℰP.prod-m (id _) (realise-η-iso A .Iso.fwd)) ∘ prodη Γ (η .fobj A) .Iso.fwd
      ≈⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
        (m ∘ (ℰP.p₂ ∘ ℰP.prod-m (id _) (realise-η-iso A .Iso.fwd))) ∘ prodη Γ (η .fobj A) .Iso.fwd
      ≈⟨ ∘-cong (∘-cong ≈-refl (ℰP.pair-p₂ _ _)) ≈-refl ⟩
        (m ∘ (realise-η-iso A .Iso.fwd ∘ ℰP.p₂)) ∘ prodη Γ (η .fobj A) .Iso.fwd
      ≈˘⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
        ((m ∘ realise-η-iso A .Iso.fwd) ∘ ℰP.p₂) ∘ prodη Γ (η .fobj A) .Iso.fwd
      ≈⟨ assoc _ _ _ ⟩
        (m ∘ realise-η-iso A .Iso.fwd) ∘ (ℰP.p₂ ∘ prodη Γ (η .fobj A) .Iso.fwd)
      ≈⟨ ∘-cong ≈-refl (prodη-p₂ Γ (η .fobj A)) ⟩
        (m ∘ realise-η-iso A .Iso.fwd) ∘ realise .fmor (FM.Fam𝒞-P.p₂ {x = η .fobj Γ} {y = η .fobj A})
      ∎ where open ≈-Reasoning isEquiv

-- Extend a pure morphism to the bound entry, identities elsewhere.
pureExt : ∀ {n} (δ̂ : Fin n → FM.Obj) {Â B̂ : FM.Obj} → FM.Mor Â B̂ →
          ∀ i → FM.Mor (extend δ̂ Â i) (extend δ̂ B̂ i)
pureExt δ̂ m̂ Fin.zero    = m̂
pureExt δ̂ m̂ (Fin.suc i) = Category.id FM.cat _

private
  module FamT = HasTerminal (FM.terminal ℰT)

-- The Fam(ℰ) strong action at a purely-precomposed family is the plain action
-- precomposed with the projection.
sf-pure : ∀ {n} (Q : Poly ℰ (suc n)) (δ̂₁ δ̂₂ : Fin (suc n) → FM.Obj) {Γ : obj}
          (ms : ∀ i → FM.Mor (δ̂₁ i) (δ̂₂ i)) →
          Category._≈_ FM.cat
            (FM.Mor-∘ (FMu.fmor (Poly-map η Q) ms) (FM.Fam𝒞-P.p₂ {x = η .fobj Γ} {y = FM.fobj FM.μObj (Poly-map η Q) δ̂₁}))
            (FMu.strong-fmor (Poly-map η Q) (λ i → FM.Mor-∘ (ms i) (FM.Fam𝒞-P.p₂ {x = η .fobj Γ} {y = δ̂₁ i})))
sf-pure {n} Q δ̂₁ δ̂₂ {Γ} ms =
  FamC.≈-trans (FamC.assoc _ _ _)
    (FamC.≈-trans (FamC.∘-cong FamC.≈-refl sect-proj)
      (FamC.≈-trans (FMuI.strong-fmor-reindex (Poly-map η Q) FamT.to-terminal _)
        (FMuI.strong-fmor-cong (Poly-map η Q) pointwise)))
  where
    sect-proj : Category._≈_ FM.cat
                  (FM.Mor-∘ (FM.Fam𝒞-P.pair FamT.to-terminal (Category.id FM.cat _)) (FM.Fam𝒞-P.p₂ {x = η .fobj Γ} {y = FM.fobj FM.μObj (Poly-map η Q) δ̂₁}))
                  (FM.Fam𝒞-P.prod-m FamT.to-terminal (Category.id FM.cat _))
    sect-proj =
      FamC.≈-trans (FM.Fam𝒞-P.pair-natural _ _ _)
        (FM.Fam𝒞-P.pair-cong (FamT.to-terminal-unique _ _) FamC.≈-refl)

    pointwise : ∀ i → Category._≈_ FM.cat
                  (FM.Mor-∘ (FM.Mor-∘ (ms i) (FM.Fam𝒞-P.p₂ {x = FamT.witness} {y = δ̂₁ i})) (FM.Fam𝒞-P.prod-m FamT.to-terminal (Category.id FM.cat _)))
                  (FM.Mor-∘ (ms i) (FM.Fam𝒞-P.p₂ {x = η .fobj Γ} {y = δ̂₁ i}))
    pointwise i =
      FamC.≈-trans (FamC.assoc _ _ _)
        (FamC.∘-cong FamC.≈-refl
          (FamC.≈-trans (FM.Fam𝒞-P.pair-p₂ _ _) FamC.id-left))

-- The realised strong action on a pure morphism is a pure lift of the
-- realised plain Fam(ℰ) action.
Gmap-pure : ∀ {n} (Q : Poly ℰ (suc n)) (δ̂ : Fin n → FM.Obj) {Γ A B : obj} (m : A ⇒ B) →
            Gmap Q δ̂ {Γ} {A} {B} (m ∘ ℰP.p₂)
            ≈ (realise .fmor (FMu.fmor (Poly-map η Q) (pureExt δ̂ (untranspose (m ∘ realise-η-iso A .Iso.fwd)))) ∘ ℰP.p₂)
Gmap-pure {n} Q δ̂ {Γ} {A} {B} m =
  ≈-trans (fmorη-cong (FMuI.strong-fmor-cong (Poly-map η Q) pw))
    (≈-trans (fmorη-cong (FamC.≈-sym (sf-pure Q (extend δ̂ (η .fobj A)) (extend δ̂ (η .fobj B)) (pureExt δ̂ m̂))))
      (fmorη-pure Γ (FM.fobj FM.μObj (Poly-map η Q) (extend δ̂ (η .fobj A))) (FMu.fmor (Poly-map η Q) (pureExt δ̂ m̂))))
  where
    m̂ = untranspose (m ∘ realise-η-iso A .Iso.fwd)

    pw : ∀ i → Category._≈_ FM.cat
           (FMu.strong-extend-mor (λ j → FM.Fam𝒞-P.p₂) (ctxη Γ A (m ∘ ℰP.p₂)) i)
           (FM.Mor-∘ (pureExt δ̂ m̂ i) (FM.Fam𝒞-P.p₂ {x = η .fobj Γ} {y = extend δ̂ (η .fobj A) i}))
    pw Fin.zero    = ctxη-pure Γ A m
    pw (Fin.suc i) = FamC.≈-sym FamC.id-left

-- Cancel a projection from the terminal context.
p₂-cancel : ∀ {X Z : obj} {f g : X ⇒ Z} →
            ((f ∘ ℰP.p₂ {ℰT'.witness} {X}) ≈ (g ∘ ℰP.p₂)) → f ≈ g
p₂-cancel {X} {Z} {f} {g} eq =
  ≈-trans (≈-sym id-right)
    (≈-trans (∘-cong ≈-refl (≈-sym (ℰP.pair-p₂ ℰT'.to-terminal (id _))))
      (≈-trans (≈-sym (assoc _ _ _))
        (≈-trans (∘-cong eq ≈-refl)
          (≈-trans (assoc _ _ _)
            (≈-trans (∘-cong ≈-refl (ℰP.pair-p₂ ℰT'.to-terminal (id _))) id-right)))))

-- Collapses at pointwise-equal isomorphism families are equal.
collapse-ext : ∀ {n} (Q : Poly ℰ n) (CQ' : CollapseAt Q) (δ̂₁ δ̂₂ : Fin n → FM.Obj)
               (isos isos' : ∀ i → Iso (realise .fobj (δ̂₁ i)) (realise .fobj (δ̂₂ i))) →
               (∀ i → isos i .Iso.fwd ≈ isos' i .Iso.fwd) →
               CQ' .CollapseAt.iso δ̂₁ δ̂₂ isos .Iso.fwd ≈ CQ' .CollapseAt.iso δ̂₁ δ̂₂ isos' .Iso.fwd
collapse-ext {n} Q CQ' δ̂₁ δ̂₂ isos isos' hyps =
  p₂-cancel (≈-trans (≈-sym strip₁) (≈-trans (CQ' .CollapseAt.natural δ̂₁ δ̂₂ isos isos' (λ i → FM.Fam𝒞-P.p₂ {x = η .fobj ℰT'.witness} {y = δ̂₁ i}) (λ i → FM.Fam𝒞-P.p₂ {x = η .fobj ℰT'.witness} {y = δ̂₂ i}) sqs) strip₂))
  where
    strip₁ : (fmorη ℰT'.witness (FM.fobj FM.μObj (Poly-map η Q) δ̂₂) (FMu.strong-fmor (Poly-map η Q) (λ i → FM.Fam𝒞-P.p₂ {x = η .fobj ℰT'.witness} {y = δ̂₂ i}))
              ∘co (CQ' .CollapseAt.iso δ̂₁ δ̂₂ isos .Iso.fwd ∘ ℰP.p₂))
             ≈ (CQ' .CollapseAt.iso δ̂₁ δ̂₂ isos .Iso.fwd ∘ ℰP.p₂)
    strip₁ =
      ≈-trans (CoK.∘-cong (≈-trans (fmorη-cong (FMuI.strong-fmor-p₂ (Poly-map η Q))) (fmorη-p₂ ℰT'.witness _)) ≈-refl)
        (CoK.id-left {Γ = ℰT'.witness})

    strip₂ : (CQ' .CollapseAt.iso δ̂₁ δ̂₂ isos' .Iso.fwd
              ∘ fmorη ℰT'.witness (FM.fobj FM.μObj (Poly-map η Q) δ̂₁) (FMu.strong-fmor (Poly-map η Q) (λ i → FM.Fam𝒞-P.p₂ {x = η .fobj ℰT'.witness} {y = δ̂₁ i})))
             ≈ (CQ' .CollapseAt.iso δ̂₁ δ̂₂ isos' .Iso.fwd ∘ ℰP.p₂)
    strip₂ =
      ∘-cong ≈-refl (≈-trans (fmorη-cong (FMuI.strong-fmor-p₂ (Poly-map η Q))) (fmorη-p₂ ℰT'.witness _))

    sqs : ∀ i → (fmorη ℰT'.witness (δ̂₂ i) (FM.Fam𝒞-P.p₂ {x = η .fobj ℰT'.witness} {y = δ̂₂ i}) ∘co (isos i .Iso.fwd ∘ ℰP.p₂))
                ≈ (isos' i .Iso.fwd ∘ fmorη ℰT'.witness (δ̂₁ i) (FM.Fam𝒞-P.p₂ {x = η .fobj ℰT'.witness} {y = δ̂₁ i}))
    sqs i =
      ≈-trans (CoK.∘-cong (fmorη-p₂ ℰT'.witness (δ̂₂ i)) ≈-refl)
        (≈-trans (CoK.id-left {Γ = ℰT'.witness})
          (≈-trans (∘-cong (hyps i) ≈-refl)
            (≈-sym (∘-cong ≈-refl (fmorη-p₂ ℰT'.witness (δ̂₁ i))))))

-- A collapse at realisations of pure Fam(ℰ) morphisms is the realised plain
-- action.
pure-collapse : ∀ {n} (Q : Poly ℰ (suc n)) (CQ' : CollapseAt Q) (δ̂₁ δ̂₂ : Fin (suc n) → FM.Obj)
                (ms : ∀ i → FM.Mor (δ̂₁ i) (δ̂₂ i))
                (isos : ∀ i → Iso (realise .fobj (δ̂₁ i)) (realise .fobj (δ̂₂ i))) →
                (∀ i → isos i .Iso.fwd ≈ realise .fmor (ms i)) →
                CQ' .CollapseAt.iso δ̂₁ δ̂₂ isos .Iso.fwd ≈ realise .fmor (FMu.fmor (Poly-map η Q) ms)
pure-collapse {n} Q CQ' δ̂₁ δ̂₂ ms isos hyps =
  p₂-cancel (≈-trans (≈-sym strip₁) (≈-trans (CQ' .CollapseAt.natural δ̂₁ δ̂₂ isos (λ i → Iso-refl) (λ i → FM.Mor-∘ (ms i) (FM.Fam𝒞-P.p₂ {x = η .fobj ℰT'.witness} {y = δ̂₁ i})) (λ i → FM.Fam𝒞-P.p₂ {x = η .fobj ℰT'.witness} {y = δ̂₂ i}) sqs) strip₂))
  where
    strip₁ : (fmorη ℰT'.witness (FM.fobj FM.μObj (Poly-map η Q) δ̂₂) (FMu.strong-fmor (Poly-map η Q) (λ i → FM.Fam𝒞-P.p₂ {x = η .fobj ℰT'.witness} {y = δ̂₂ i}))
              ∘co (CQ' .CollapseAt.iso δ̂₁ δ̂₂ isos .Iso.fwd ∘ ℰP.p₂))
             ≈ (CQ' .CollapseAt.iso δ̂₁ δ̂₂ isos .Iso.fwd ∘ ℰP.p₂)
    strip₁ =
      ≈-trans (CoK.∘-cong (≈-trans (fmorη-cong (FMuI.strong-fmor-p₂ (Poly-map η Q))) (fmorη-p₂ ℰT'.witness _)) ≈-refl)
        (CoK.id-left {Γ = ℰT'.witness})

    strip₂ : (CQ' .CollapseAt.iso δ̂₂ δ̂₂ (λ i → Iso-refl) .Iso.fwd
              ∘ fmorη ℰT'.witness (FM.fobj FM.μObj (Poly-map η Q) δ̂₁) (FMu.strong-fmor (Poly-map η Q) (λ i → FM.Mor-∘ (ms i) (FM.Fam𝒞-P.p₂ {x = η .fobj ℰT'.witness} {y = δ̂₁ i}))))
             ≈ (realise .fmor (FMu.fmor (Poly-map η Q) ms) ∘ ℰP.p₂)
    strip₂ =
      ≈-trans (∘-cong (CQ' .CollapseAt.refl-iso δ̂₂ (λ i → Iso-refl) (λ i → ≈-refl)) ≈-refl)
        (≈-trans id-left
          (≈-trans (fmorη-cong (FamC.≈-sym (sf-pure Q δ̂₁ δ̂₂ ms)))
            (fmorη-pure ℰT'.witness (FM.fobj FM.μObj (Poly-map η Q) δ̂₁) (FMu.fmor (Poly-map η Q) ms))))

    sqs : ∀ i → (fmorη ℰT'.witness (δ̂₂ i) (FM.Fam𝒞-P.p₂ {x = η .fobj ℰT'.witness} {y = δ̂₂ i}) ∘co (isos i .Iso.fwd ∘ ℰP.p₂))
                ≈ (Iso-refl .Iso.fwd ∘ fmorη ℰT'.witness (δ̂₁ i) (FM.Mor-∘ (ms i) (FM.Fam𝒞-P.p₂ {x = η .fobj ℰT'.witness} {y = δ̂₁ i})))
    sqs i =
      ≈-trans (CoK.∘-cong (fmorη-p₂ ℰT'.witness (δ̂₂ i)) ≈-refl)
        (≈-trans (CoK.id-left {Γ = ℰT'.witness})
          (≈-trans (∘-cong (hyps i) ≈-refl)
            (≈-sym (≈-trans id-left (fmorη-pure ℰT'.witness (δ̂₁ i) (ms i))))))

-- The μ-collapse at a composite isomorphism family is the composite of the
-- μ-collapses.
mu-collapse-comp : ∀ {n} (Q : Poly ℰ (suc n)) (CQ : CollapseAt Q)
                   (δ̂₁ δ̂₂ δ̂₃ : Fin n → FM.Obj)
                   (isos₁₂ : ∀ i → Iso (realise .fobj (δ̂₁ i)) (realise .fobj (δ̂₂ i)))
                   (isos₂₃ : ∀ i → Iso (realise .fobj (δ̂₂ i)) (realise .fobj (δ̂₃ i))) →
                   MuCollapse.mu-collapse Q CQ δ̂₁ δ̂₃ (λ i → Iso-trans (isos₁₂ i) (isos₂₃ i)) .Iso.fwd
                   ≈ (MuCollapse.mu-collapse Q CQ δ̂₂ δ̂₃ isos₂₃ .Iso.fwd ∘ MuCollapse.mu-collapse Q CQ δ̂₁ δ̂₂ isos₁₂ .Iso.fwd)
mu-collapse-comp {n} Q CQ δ̂₁ δ̂₂ δ̂₃ isos₁₂ isos₂₃ =
  ≈-trans (∘-cong (≈-sym (MC₁₃.M₁.foldR-η {Γ = ℰT'.witness} _ (MC₂₃.F' ∘co MC₁₂.F') square)) ≈-refl)
    (≈-sym (MC₁₂.plait MC₂₃.F' MC₁₂.F'))
  where
    module MC₁₂ = MuCollapse Q CQ δ̂₁ δ̂₂ isos₁₂
    module MC₂₃ = MuCollapse Q CQ δ̂₂ δ̂₃ isos₂₃
    module MC₁₃ = MuCollapse Q CQ δ̂₁ δ̂₃ (λ i → Iso-trans (isos₁₂ i) (isos₂₃ i))

    C₃ = Creal Q δ̂₃

    GIcomp : (MC₂₃.GI C₃ .Iso.fwd ∘ MC₁₂.GI C₃ .Iso.fwd) ≈ MC₁₃.GI C₃ .Iso.fwd
    GIcomp =
      ≈-sym (≈-trans (collapse-ext Q CQ _ _ (MC₁₃.extIsos C₃) (λ i → Iso-trans (MC₁₂.extIsos C₃ i) (MC₂₃.extIsos C₃ i)) pw)
        (CQ .CollapseAt.comp _ _ _ (MC₁₂.extIsos C₃) (MC₂₃.extIsos C₃)))
      where
        pw : ∀ i → MC₁₃.extIsos C₃ i .Iso.fwd ≈ Iso-trans (MC₁₂.extIsos C₃ i) (MC₂₃.extIsos C₃ i) .Iso.fwd
        pw Fin.zero    = ≈-sym id-left
        pw (Fin.suc i) = ≈-refl

    inner-split : ((MC₁₂.GI C₃ .Iso.fwd ∘ ℰP.p₂) ∘co Gmap Q δ̂₁ MC₂₃.F')
                  ≈ (MC₁₂.GI C₃ .Iso.fwd ∘ Gmap Q δ̂₁ MC₂₃.F')
    inner-split = ≈-trans (assoc _ _ _) (∘-cong ≈-refl (ℰP.pair-p₂ _ _))

    head-comp : ((MC₂₃.M₂.inR ∘ (MC₂₃.GI C₃ .Iso.fwd ∘ ℰP.p₂)) ∘co (MC₁₂.GI C₃ .Iso.fwd ∘ ℰP.p₂))
                ≈ (MC₁₃.M₂.inR ∘ (MC₁₃.GI C₃ .Iso.fwd ∘ ℰP.p₂))
    head-comp =
      begin
        (MC₂₃.M₂.inR ∘ (MC₂₃.GI C₃ .Iso.fwd ∘ ℰP.p₂)) ∘co (MC₁₂.GI C₃ .Iso.fwd ∘ ℰP.p₂)
      ≈˘⟨ CoK.∘-cong (assoc _ _ _) ≈-refl ⟩
        ((MC₂₃.M₂.inR ∘ MC₂₃.GI C₃ .Iso.fwd) ∘ ℰP.p₂) ∘co (MC₁₂.GI C₃ .Iso.fwd ∘ ℰP.p₂)
      ≈⟨ co-pure _ _ ⟩
        ((MC₂₃.M₂.inR ∘ MC₂₃.GI C₃ .Iso.fwd) ∘ MC₁₂.GI C₃ .Iso.fwd) ∘ ℰP.p₂
      ≈⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
        (MC₂₃.M₂.inR ∘ (MC₂₃.GI C₃ .Iso.fwd ∘ MC₁₂.GI C₃ .Iso.fwd)) ∘ ℰP.p₂
      ≈⟨ ∘-cong (∘-cong ≈-refl GIcomp) ≈-refl ⟩
        (MC₁₃.M₂.inR ∘ MC₁₃.GI C₃ .Iso.fwd) ∘ ℰP.p₂
      ≈⟨ assoc _ _ _ ⟩
        MC₁₃.M₂.inR ∘ (MC₁₃.GI C₃ .Iso.fwd ∘ ℰP.p₂)
      ∎ where open ≈-Reasoning isEquiv

    square : ((MC₂₃.F' ∘co MC₁₂.F') ∘co (MC₁₃.M₁.inR ∘ ℰP.p₂))
             ≈ ((MC₁₃.M₂.inR ∘ (MC₁₃.GI C₃ .Iso.fwd ∘ ℰP.p₂)) ∘co Gmap Q δ̂₁ (MC₂₃.F' ∘co MC₁₂.F'))
    square =
      begin
        (MC₂₃.F' ∘co MC₁₂.F') ∘co (MC₁₃.M₁.inR ∘ ℰP.p₂)
      ≈⟨ CoK.assoc _ _ _ ⟩
        MC₂₃.F' ∘co (MC₁₂.F' ∘co (MC₁₂.M₁.inR ∘ ℰP.p₂))
      ≈⟨ CoK.∘-cong ≈-refl (MC₁₂.M₁.foldR-β _) ⟩
        MC₂₃.F' ∘co ((MC₁₂.M₂.inR ∘ (MC₁₂.GI (Creal Q δ̂₂) .Iso.fwd ∘ ℰP.p₂)) ∘co Gmap Q δ̂₁ MC₁₂.F')
      ≈⟨ CoK.∘-cong ≈-refl (CoK.∘-cong (≈-trans (≈-sym (assoc _ _ _)) (≈-sym (co-pure _ _))) ≈-refl) ⟩
        MC₂₃.F' ∘co (((MC₁₂.M₂.inR ∘ ℰP.p₂) ∘co (MC₁₂.GI (Creal Q δ̂₂) .Iso.fwd ∘ ℰP.p₂)) ∘co Gmap Q δ̂₁ MC₁₂.F')
      ≈⟨ CoK.∘-cong ≈-refl (CoK.assoc _ _ _) ⟩
        MC₂₃.F' ∘co ((MC₁₂.M₂.inR ∘ ℰP.p₂) ∘co ((MC₁₂.GI (Creal Q δ̂₂) .Iso.fwd ∘ ℰP.p₂) ∘co Gmap Q δ̂₁ MC₁₂.F'))
      ≈˘⟨ CoK.assoc _ _ _ ⟩
        (MC₂₃.F' ∘co (MC₂₃.M₁.inR ∘ ℰP.p₂)) ∘co ((MC₁₂.GI (Creal Q δ̂₂) .Iso.fwd ∘ ℰP.p₂) ∘co Gmap Q δ̂₁ MC₁₂.F')
      ≈⟨ CoK.∘-cong (MC₂₃.M₁.foldR-β _) ≈-refl ⟩
        ((MC₂₃.M₂.inR ∘ (MC₂₃.GI C₃ .Iso.fwd ∘ ℰP.p₂)) ∘co Gmap Q δ̂₂ MC₂₃.F') ∘co ((MC₁₂.GI (Creal Q δ̂₂) .Iso.fwd ∘ ℰP.p₂) ∘co Gmap Q δ̂₁ MC₁₂.F')
      ≈⟨ CoK.assoc _ _ _ ⟩
        (MC₂₃.M₂.inR ∘ (MC₂₃.GI C₃ .Iso.fwd ∘ ℰP.p₂)) ∘co (Gmap Q δ̂₂ MC₂₃.F' ∘co ((MC₁₂.GI (Creal Q δ̂₂) .Iso.fwd ∘ ℰP.p₂) ∘co Gmap Q δ̂₁ MC₁₂.F'))
      ≈˘⟨ CoK.∘-cong ≈-refl (CoK.assoc _ _ _) ⟩
        (MC₂₃.M₂.inR ∘ (MC₂₃.GI C₃ .Iso.fwd ∘ ℰP.p₂)) ∘co ((Gmap Q δ̂₂ MC₂₃.F' ∘co (MC₁₂.GI (Creal Q δ̂₂) .Iso.fwd ∘ ℰP.p₂)) ∘co Gmap Q δ̂₁ MC₁₂.F')
      ≈⟨ CoK.∘-cong ≈-refl (CoK.∘-cong (MC₁₂.cross MC₂₃.F') ≈-refl) ⟩
        (MC₂₃.M₂.inR ∘ (MC₂₃.GI C₃ .Iso.fwd ∘ ℰP.p₂)) ∘co ((MC₁₂.GI C₃ .Iso.fwd ∘ Gmap Q δ̂₁ MC₂₃.F') ∘co Gmap Q δ̂₁ MC₁₂.F')
      ≈⟨ CoK.∘-cong ≈-refl (CoK.∘-cong (≈-sym inner-split) ≈-refl) ⟩
        (MC₂₃.M₂.inR ∘ (MC₂₃.GI C₃ .Iso.fwd ∘ ℰP.p₂)) ∘co (((MC₁₂.GI C₃ .Iso.fwd ∘ ℰP.p₂) ∘co Gmap Q δ̂₁ MC₂₃.F') ∘co Gmap Q δ̂₁ MC₁₂.F')
      ≈⟨ CoK.∘-cong ≈-refl (CoK.assoc _ _ _) ⟩
        (MC₂₃.M₂.inR ∘ (MC₂₃.GI C₃ .Iso.fwd ∘ ℰP.p₂)) ∘co ((MC₁₂.GI C₃ .Iso.fwd ∘ ℰP.p₂) ∘co (Gmap Q δ̂₁ MC₂₃.F' ∘co Gmap Q δ̂₁ MC₁₂.F'))
      ≈˘⟨ CoK.assoc _ _ _ ⟩
        ((MC₂₃.M₂.inR ∘ (MC₂₃.GI C₃ .Iso.fwd ∘ ℰP.p₂)) ∘co (MC₁₂.GI C₃ .Iso.fwd ∘ ℰP.p₂)) ∘co (Gmap Q δ̂₁ MC₂₃.F' ∘co Gmap Q δ̂₁ MC₁₂.F')
      ≈⟨ CoK.∘-cong head-comp (≈-sym (Gmap-∘co Q δ̂₁ MC₂₃.F' MC₁₂.F')) ⟩
        (MC₁₃.M₂.inR ∘ (MC₁₃.GI C₃ .Iso.fwd ∘ ℰP.p₂)) ∘co Gmap Q δ̂₁ (MC₂₃.F' ∘co MC₁₂.F')
      ∎
      where open ≈-Reasoning isEquiv


-- Realising an untransposed morphism is the counit inverse followed by it.
realise-untranspose : ∀ {W : FM.Obj} {X : obj} (g : realise .fobj W ⇒ X) →
                      realise .fmor (untranspose {W = W} g) ≈ (realise-η-iso X .Iso.bwd ∘ g)
realise-untranspose {W} {X} g =
  iso-shuffle (realise-η-iso X) _ _
    (≈-trans (≈-sym (FR.transpose-realise {W = W} (untranspose {W = W} g))) (FR.transpose-untranspose {W = W} g))

-- Transport an isomorphism of realisations across the singleton embedding.
pureJ : ∀ {A B : obj} (I : Iso A B) → Iso (realise .fobj (η .fobj A)) (realise .fobj (η .fobj B))
pureJ {A} {B} I =
  Iso-trans (realise-η-iso A) (Iso-trans I (Iso-sym (realise-η-iso B)))

pureJ-fwd : ∀ {A B : obj} (I : Iso A B) →
            pureJ I .Iso.fwd ≈ realise .fmor (untranspose {W = η .fobj A} (I .Iso.fwd ∘ realise-η-iso A .Iso.fwd))
pureJ-fwd {A} {B} I =
  ≈-sym (≈-trans (realise-untranspose {W = η .fobj A} (I .Iso.fwd ∘ realise-η-iso A .Iso.fwd)) (≈-sym (assoc _ _ _)))

-- The algebra-map squares for the μ-collapse, with the strong action in its
-- realised plain form.
mu-collapse-fwd-in' : ∀ {n} (Q : Poly ℰ (suc n)) (CQ : CollapseAt Q)
                      (δ̂₁ δ̂₂ : Fin n → FM.Obj)
                      (isos : ∀ i → Iso (realise .fobj (δ̂₁ i)) (realise .fobj (δ̂₂ i))) →
                      (MuCollapse.mu-collapse Q CQ δ̂₁ δ̂₂ isos .Iso.fwd ∘ Initiality.inR Q δ̂₁ CQ)
                      ≈ (Initiality.inR Q δ̂₂ CQ ∘
                         (MuCollapse.GI Q CQ δ̂₁ δ̂₂ isos (Creal Q δ̂₂) .Iso.fwd ∘
                          realise .fmor (FMu.fmor (Poly-map η Q) (pureExt δ̂₁ (untranspose (MuCollapse.mu-collapse Q CQ δ̂₁ δ̂₂ isos .Iso.fwd ∘ realise-η-iso (Creal Q δ̂₁) .Iso.fwd))))))
mu-collapse-fwd-in' Q CQ δ̂₁ δ̂₂ isos =
  ≈-trans (mu-collapse-fwd-in Q CQ δ̂₁ δ̂₂ isos)
    (∘-cong ≈-refl (∘-cong ≈-refl
      (≈-trans (∘-cong (Gmap-pure Q δ̂₁ (MuCollapse.mu-collapse Q CQ δ̂₁ δ̂₂ isos .Iso.fwd)) ≈-refl)
        (≈-trans (assoc _ _ _)
          (≈-trans (∘-cong ≈-refl (ℰP.pair-p₂ _ _)) id-right)))))

mu-collapse-bwd-in' : ∀ {n} (Q : Poly ℰ (suc n)) (CQ : CollapseAt Q)
                      (δ̂₁ δ̂₂ : Fin n → FM.Obj)
                      (isos : ∀ i → Iso (realise .fobj (δ̂₁ i)) (realise .fobj (δ̂₂ i))) →
                      (MuCollapse.mu-collapse Q CQ δ̂₁ δ̂₂ isos .Iso.bwd ∘ Initiality.inR Q δ̂₂ CQ)
                      ≈ (Initiality.inR Q δ̂₁ CQ ∘
                         (MuCollapse.GI Q CQ δ̂₁ δ̂₂ isos (Creal Q δ̂₁) .Iso.bwd ∘
                          realise .fmor (FMu.fmor (Poly-map η Q) (pureExt δ̂₂ (untranspose (MuCollapse.mu-collapse Q CQ δ̂₁ δ̂₂ isos .Iso.bwd ∘ realise-η-iso (Creal Q δ̂₂) .Iso.fwd))))))
mu-collapse-bwd-in' Q CQ δ̂₁ δ̂₂ isos =
  ≈-trans (mu-collapse-bwd-in Q CQ δ̂₁ δ̂₂ isos)
    (∘-cong ≈-refl (∘-cong ≈-refl
      (≈-trans (∘-cong (Gmap-pure Q δ̂₂ (MuCollapse.mu-collapse Q CQ δ̂₁ δ̂₂ isos .Iso.bwd)) ≈-refl)
        (≈-trans (assoc _ _ _)
          (≈-trans (∘-cong ≈-refl (ℰP.pair-p₂ _ _)) id-right)))))

-- The naturality of the μ-collapse: the last field of the collapse interface
-- at μ. Established by fold uniqueness, with the collapse paths identified
-- through composition coherence and extensionality.
module MuNat {n} (Q : Poly ℰ (suc n)) (CQ : CollapseAt Q) {Γ : obj}
    (δ̂₁ δ̂₂ ε̂₁ ε̂₂ : Fin n → FM.Obj)
    (isosδ : ∀ i → Iso (realise .fobj (δ̂₁ i)) (realise .fobj (δ̂₂ i)))
    (isosε : ∀ i → Iso (realise .fobj (ε̂₁ i)) (realise .fobj (ε̂₂ i)))
    (gs₁ : ∀ i → FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) (δ̂₁ i)) (ε̂₁ i))
    (gs₂ : ∀ i → FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) (δ̂₂ i)) (ε̂₂ i))
    (sqs : ∀ i → (fmorη Γ (δ̂₂ i) (gs₂ i) ∘co (isosδ i .Iso.fwd ∘ ℰP.p₂))
                 ≈ (isosε i .Iso.fwd ∘ fmorη Γ (δ̂₁ i) (gs₁ i)))
  where

  private
    Q̂ = Poly-map η Q

    module Mδ₁ = Initiality Q δ̂₁ CQ
    module Mδ₂ = Initiality Q δ̂₂ CQ
    module Mε₁ = Initiality Q ε̂₁ CQ
    module Mε₂ = Initiality Q ε̂₂ CQ
    module Sδ₁ = SμfFold Q CQ δ̂₁ ε̂₁ gs₁
    module Sδ₂ = SμfFold Q CQ δ̂₂ ε̂₂ gs₂
    module MCδ = MuCollapse Q CQ δ̂₁ δ̂₂ isosδ
    module MCε = MuCollapse Q CQ ε̂₁ ε̂₂ isosε

    muδ = MCδ.mu-collapse
    muε = MCε.mu-collapse
    C₁ε = Creal Q ε̂₁
    C₂ε = Creal Q ε̂₂

    f̂ε : FM.Mor (η .fobj C₁ε) (η .fobj C₂ε)
    f̂ε = untranspose {W = η .fobj C₁ε} (muε .Iso.fwd ∘ realise-η-iso C₁ε .Iso.fwd)

    NFε₁ = FMu.fmor Q̂ (pureExt ε̂₁ f̂ε)

    Kε₁ = CQ .CollapseAt.iso (extend ε̂₁ (η .fobj C₁ε)) (extend ε̂₁ (FM.μObj Q̂ ε̂₁)) Mε₁.inIsos
    Kε₂ = CQ .CollapseAt.iso (extend ε̂₂ (η .fobj C₂ε)) (extend ε̂₂ (FM.μObj Q̂ ε̂₂)) Mε₂.inIsos
    Mεμ = CQ .CollapseAt.iso (extend ε̂₁ (FM.μObj Q̂ ε̂₁)) (extend ε̂₂ (FM.μObj Q̂ ε̂₂)) (mixed isosε muε)

    Pc-isos = mixed {δ̂₁ = ε̂₁} {δ̂₂ = ε̂₁} (λ i → Iso-refl) {Ŷ₁ = η .fobj C₁ε} {Ŷ₂ = η .fobj C₂ε} (pureJ muε)

    Pc-real : CQ .CollapseAt.iso (extend ε̂₁ (η .fobj C₁ε)) (extend ε̂₁ (η .fobj C₂ε)) Pc-isos .Iso.fwd
              ≈ realise .fmor NFε₁
    Pc-real = pure-collapse Q CQ _ _ (pureExt ε̂₁ f̂ε) Pc-isos hyps
      where
        hyps : ∀ i → Pc-isos i .Iso.fwd ≈ realise .fmor (pureExt ε̂₁ f̂ε i)
        hyps Fin.zero    = pureJ-fwd muε
        hyps (Fin.suc i) = ≈-sym (realise .fmor-id)

    counit-collapse-square : (Kε₂ .Iso.fwd ∘ (MCε.GI C₂ε .Iso.fwd ∘ realise .fmor NFε₁))
                             ≈ (Mεμ .Iso.fwd ∘ Kε₁ .Iso.fwd)
    counit-collapse-square =
      begin
        Kε₂ .Iso.fwd ∘ (MCε.GI C₂ε .Iso.fwd ∘ realise .fmor NFε₁)
      ≈˘⟨ ∘-cong ≈-refl (∘-cong ≈-refl Pc-real) ⟩
        Kε₂ .Iso.fwd ∘ (MCε.GI C₂ε .Iso.fwd ∘ CQ .CollapseAt.iso _ _ Pc-isos .Iso.fwd)
      ≈˘⟨ ∘-cong ≈-refl (CQ .CollapseAt.comp _ _ _ Pc-isos (MCε.extIsos C₂ε)) ⟩
        Kε₂ .Iso.fwd ∘ CQ .CollapseAt.iso _ _ (λ i → Iso-trans (Pc-isos i) (MCε.extIsos C₂ε i)) .Iso.fwd
      ≈˘⟨ CQ .CollapseAt.comp _ _ _ (λ i → Iso-trans (Pc-isos i) (MCε.extIsos C₂ε i)) Mε₂.inIsos ⟩
        CQ .CollapseAt.iso _ _ (λ i → Iso-trans (Iso-trans (Pc-isos i) (MCε.extIsos C₂ε i)) (Mε₂.inIsos i)) .Iso.fwd
      ≈⟨ collapse-ext Q CQ (extend ε̂₁ (η .fobj C₁ε)) (extend ε̂₂ (FM.μObj Q̂ ε̂₂))
           (λ i → Iso-trans (Iso-trans (Pc-isos i) (MCε.extIsos C₂ε i)) (Mε₂.inIsos i))
           (λ i → Iso-trans (Mε₁.inIsos i) (mixed isosε muε i)) pointwise ⟩
        CQ .CollapseAt.iso _ _ (λ i → Iso-trans (Mε₁.inIsos i) (mixed isosε muε i)) .Iso.fwd
      ≈⟨ CQ .CollapseAt.comp _ _ _ Mε₁.inIsos (mixed isosε muε) ⟩
        Mεμ .Iso.fwd ∘ Kε₁ .Iso.fwd
      ∎
      where
        open ≈-Reasoning isEquiv

        pointwise : ∀ i → Iso-trans (Iso-trans (Pc-isos i) (MCε.extIsos C₂ε i)) (Mε₂.inIsos i) .Iso.fwd
                          ≈ Iso-trans (Mε₁.inIsos i) (mixed isosε muε i) .Iso.fwd
        pointwise Fin.zero =
          ≈-trans (∘-cong ≈-refl id-left)
            (≈-trans (≈-sym (assoc _ _ _))
              (≈-trans (∘-cong (≈-sym (assoc _ _ _)) ≈-refl)
                (∘-cong (≈-trans (∘-cong (realise-η-iso C₂ε .Iso.fwd∘bwd≈id) ≈-refl) id-left) ≈-refl)))
        pointwise (Fin.suc i) = id-left

    -- Abbreviations for the δ̂-side collapse paths.
    KK₁ = Sδ₁.KKε
    KK₂ = Sδ₂.KKε
    Mδμ = CQ .CollapseAt.iso (extend δ̂₁ (FM.μObj Q̂ ε̂₁)) (extend δ̂₂ (FM.μObj Q̂ ε̂₂)) (mixed isosδ muε)

    NF₂ = FMu.fmor Q̂ (pureExt δ̂₂ f̂ε)

    Pc2-isos = mixed {δ̂₁ = δ̂₂} {δ̂₂ = δ̂₂} (λ i → Iso-refl) {Ŷ₁ = η .fobj C₁ε} {Ŷ₂ = η .fobj C₂ε} (pureJ muε)

    Pc2-real : CQ .CollapseAt.iso (extend δ̂₂ (η .fobj C₁ε)) (extend δ̂₂ (η .fobj C₂ε)) Pc2-isos .Iso.fwd
               ≈ realise .fmor NF₂
    Pc2-real = pure-collapse Q CQ _ _ (pureExt δ̂₂ f̂ε) Pc2-isos hyps
      where
        hyps : ∀ i → Pc2-isos i .Iso.fwd ≈ realise .fmor (pureExt δ̂₂ f̂ε i)
        hyps Fin.zero    = pureJ-fwd muε
        hyps (Fin.suc i) = ≈-sym (realise .fmor-id)

    -- The δ̂-side collapse paths from the fold algebra's environment agree.
    env-collapse-square : (Mδμ .Iso.fwd ∘ KK₁ .Iso.fwd)
                          ≈ ((KK₂ .Iso.fwd ∘ realise .fmor NF₂) ∘ MCδ.GI C₁ε .Iso.fwd)
    env-collapse-square =
      begin
        Mδμ .Iso.fwd ∘ KK₁ .Iso.fwd
      ≈˘⟨ CQ .CollapseAt.comp _ _ _ Sδ₁.KKisos (mixed isosδ muε) ⟩
        CQ .CollapseAt.iso _ _ (λ i → Iso-trans (Sδ₁.KKisos i) (mixed isosδ muε i)) .Iso.fwd
      ≈⟨ collapse-ext Q CQ (extend δ̂₁ (η .fobj C₁ε)) (extend δ̂₂ (FM.μObj Q̂ ε̂₂))
           (λ i → Iso-trans (Sδ₁.KKisos i) (mixed isosδ muε i))
           (λ i → Iso-trans (MCδ.extIsos C₁ε i) (Iso-trans (Pc2-isos i) (Sδ₂.KKisos i))) pointwise ⟩
        CQ .CollapseAt.iso _ _ (λ i → Iso-trans (MCδ.extIsos C₁ε i) (Iso-trans (Pc2-isos i) (Sδ₂.KKisos i))) .Iso.fwd
      ≈⟨ CQ .CollapseAt.comp _ _ _ (MCδ.extIsos C₁ε) (λ i → Iso-trans (Pc2-isos i) (Sδ₂.KKisos i)) ⟩
        CQ .CollapseAt.iso _ _ (λ i → Iso-trans (Pc2-isos i) (Sδ₂.KKisos i)) .Iso.fwd ∘ MCδ.GI C₁ε .Iso.fwd
      ≈⟨ ∘-cong (CQ .CollapseAt.comp _ _ _ Pc2-isos Sδ₂.KKisos) ≈-refl ⟩
        (KK₂ .Iso.fwd ∘ CQ .CollapseAt.iso _ _ Pc2-isos .Iso.fwd) ∘ MCδ.GI C₁ε .Iso.fwd
      ≈⟨ ∘-cong (∘-cong ≈-refl Pc2-real) ≈-refl ⟩
        (KK₂ .Iso.fwd ∘ realise .fmor NF₂) ∘ MCδ.GI C₁ε .Iso.fwd
      ∎
      where
        open ≈-Reasoning isEquiv

        pointwise : ∀ i → Iso-trans (Sδ₁.KKisos i) (mixed isosδ muε i) .Iso.fwd
                          ≈ Iso-trans (MCδ.extIsos C₁ε i) (Iso-trans (Pc2-isos i) (Sδ₂.KKisos i)) .Iso.fwd
        pointwise Fin.zero =
          ≈-sym (≈-trans id-right
            (≈-trans (≈-sym (assoc _ _ _))
              (≈-trans (∘-cong (≈-sym (assoc _ _ _)) ≈-refl)
                (∘-cong (≈-trans (∘-cong (realise-η-iso C₂ε .Iso.fwd∘bwd≈id) ≈-refl) id-left) ≈-refl))))
        pointwise (Fin.suc i) =
          ≈-trans id-right (≈-sym (≈-trans (∘-cong id-left ≈-refl) id-left))

    -- Remaining abbreviations for the fold-square assembly.
    sfp₁ : FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) (FM.fobj FM.μObj Q̂ (extend δ̂₁ (FM.μObj Q̂ ε̂₁))))
                  (FM.fobj FM.μObj Q̂ (extend ε̂₁ (FM.μObj Q̂ ε̂₁)))
    sfp₁ = FMu.strong-fmor Q̂ (FMu.strong-extend-mor gs₁ FM.Fam𝒞-P.p₂)

    sfp₂ : FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) (FM.fobj FM.μObj Q̂ (extend δ̂₂ (FM.μObj Q̂ ε̂₂))))
                  (FM.fobj FM.μObj Q̂ (extend ε̂₂ (FM.μObj Q̂ ε̂₂)))
    sfp₂ = FMu.strong-fmor Q̂ (FMu.strong-extend-mor gs₂ FM.Fam𝒞-P.p₂)

    b̂δ : FM.Mor (η .fobj (Creal Q δ̂₂)) (η .fobj (Creal Q δ̂₁))
    b̂δ = untranspose {W = η .fobj (Creal Q δ̂₂)} (muδ .Iso.bwd ∘ realise-η-iso (Creal Q δ̂₂) .Iso.fwd)

    NB₂ = FMu.fmor Q̂ (pureExt δ̂₂ b̂δ)

    A₁ = Sδ₁.A'
    A₂ = Sδ₂.A'

    B' : ℰP.prod Γ (Creal Q δ̂₂) ⇒ Creal Q ε̂₂
    B' = (muε .Iso.fwd ∘ A₁) ∘co (muδ .Iso.bwd ∘ ℰP.p₂)

    -- The backward form of the counit collapse square.
    counit-collapse-bwd : ((MCε.GI C₂ε .Iso.fwd ∘ realise .fmor NFε₁) ∘ Kε₁ .Iso.bwd)
                          ≈ (Kε₂ .Iso.bwd ∘ Mεμ .Iso.fwd)
    counit-collapse-bwd =
      begin
        (MCε.GI C₂ε .Iso.fwd ∘ realise .fmor NFε₁) ∘ Kε₁ .Iso.bwd
      ≈˘⟨ id-left ⟩
        id _ ∘ ((MCε.GI C₂ε .Iso.fwd ∘ realise .fmor NFε₁) ∘ Kε₁ .Iso.bwd)
      ≈˘⟨ ∘-cong (Kε₂ .Iso.bwd∘fwd≈id) ≈-refl ⟩
        (Kε₂ .Iso.bwd ∘ Kε₂ .Iso.fwd) ∘ ((MCε.GI C₂ε .Iso.fwd ∘ realise .fmor NFε₁) ∘ Kε₁ .Iso.bwd)
      ≈⟨ assoc _ _ _ ⟩
        Kε₂ .Iso.bwd ∘ (Kε₂ .Iso.fwd ∘ ((MCε.GI C₂ε .Iso.fwd ∘ realise .fmor NFε₁) ∘ Kε₁ .Iso.bwd))
      ≈˘⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
        Kε₂ .Iso.bwd ∘ ((Kε₂ .Iso.fwd ∘ (MCε.GI C₂ε .Iso.fwd ∘ realise .fmor NFε₁)) ∘ Kε₁ .Iso.bwd)
      ≈⟨ ∘-cong ≈-refl (∘-cong counit-collapse-square ≈-refl) ⟩
        Kε₂ .Iso.bwd ∘ ((Mεμ .Iso.fwd ∘ Kε₁ .Iso.fwd) ∘ Kε₁ .Iso.bwd)
      ≈⟨ ∘-cong ≈-refl (≈-trans (assoc _ _ _) (≈-trans (∘-cong ≈-refl (Kε₁ .Iso.fwd∘bwd≈id)) id-right)) ⟩
        Kε₂ .Iso.bwd ∘ Mεμ .Iso.fwd
      ∎ where open ≈-Reasoning isEquiv

    -- The μ-collapse against the realised algebra map, in collapse form.
    head-eq : (muε .Iso.fwd ∘ realise .fmor (FMu.α Q̂ ε̂₁))
              ≈ (Mε₂.inR ∘ (Kε₂ .Iso.bwd ∘ Mεμ .Iso.fwd))
    head-eq =
      ≈-trans (∘-cong ≈-refl (inR-K Q ε̂₁ CQ))
        (≈-trans (≈-sym (assoc _ _ _))
          (≈-trans (∘-cong (mu-collapse-fwd-in' Q CQ ε̂₁ ε̂₂ isosε) ≈-refl)
            (≈-trans (assoc _ _ _) (∘-cong ≈-refl counit-collapse-bwd))))

    -- Gmap of the composite, decomposed into pure lifts around the crossing.
    gmapB' : Gmap Q δ̂₂ B' ≈ (((realise .fmor NF₂ ∘ ℰP.p₂) ∘co Gmap Q δ̂₂ A₁) ∘co (realise .fmor NB₂ ∘ ℰP.p₂))
    gmapB' =
      ≈-trans (Gmap-cong Q δ̂₂ (CoK.∘-cong split ≈-refl))
        (≈-trans (Gmap-∘co Q δ̂₂ ((muε .Iso.fwd ∘ ℰP.p₂) ∘co A₁) (muδ .Iso.bwd ∘ ℰP.p₂))
          (CoK.∘-cong
            (≈-trans (Gmap-∘co Q δ̂₂ (muε .Iso.fwd ∘ ℰP.p₂) A₁)
              (CoK.∘-cong (Gmap-pure Q δ̂₂ (muε .Iso.fwd)) ≈-refl))
            (Gmap-pure Q δ̂₂ (muδ .Iso.bwd))))
      where
        split : (muε .Iso.fwd ∘ A₁) ≈ ((muε .Iso.fwd ∘ ℰP.p₂) ∘co A₁)
        split = ≈-sym (≈-trans (assoc _ _ _) (∘-cong ≈-refl (ℰP.pair-p₂ _ _)))

    -- The composite tails agree, over any head.
    bracket : (((MCδ.GI C₁ε .Iso.fwd ∘ ℰP.p₂) ∘co Gmap Q δ̂₁ A₁) ∘co ((MCδ.GI (Creal Q δ̂₁) .Iso.bwd ∘ realise .fmor NB₂) ∘ ℰP.p₂))
              ≈ (Gmap Q δ̂₂ A₁ ∘co (realise .fmor NB₂ ∘ ℰP.p₂))
    bracket =
      begin
        ((MCδ.GI C₁ε .Iso.fwd ∘ ℰP.p₂) ∘co Gmap Q δ̂₁ A₁) ∘co ((MCδ.GI (Creal Q δ̂₁) .Iso.bwd ∘ realise .fmor NB₂) ∘ ℰP.p₂)
      ≈⟨ CoK.∘-cong (≈-trans (assoc _ _ _) (∘-cong ≈-refl (ℰP.pair-p₂ _ _))) ≈-refl ⟩
        (MCδ.GI C₁ε .Iso.fwd ∘ Gmap Q δ̂₁ A₁) ∘co ((MCδ.GI (Creal Q δ̂₁) .Iso.bwd ∘ realise .fmor NB₂) ∘ ℰP.p₂)
      ≈˘⟨ CoK.∘-cong (MCδ.crossΓ A₁) ≈-refl ⟩
        (Gmap Q δ̂₂ A₁ ∘co (MCδ.GI (Creal Q δ̂₁) .Iso.fwd ∘ ℰP.p₂)) ∘co ((MCδ.GI (Creal Q δ̂₁) .Iso.bwd ∘ realise .fmor NB₂) ∘ ℰP.p₂)
      ≈⟨ CoK.assoc _ _ _ ⟩
        Gmap Q δ̂₂ A₁ ∘co ((MCδ.GI (Creal Q δ̂₁) .Iso.fwd ∘ ℰP.p₂) ∘co ((MCδ.GI (Creal Q δ̂₁) .Iso.bwd ∘ realise .fmor NB₂) ∘ ℰP.p₂))
      ≈⟨ CoK.∘-cong ≈-refl (co-pure _ _) ⟩
        Gmap Q δ̂₂ A₁ ∘co ((MCδ.GI (Creal Q δ̂₁) .Iso.fwd ∘ (MCδ.GI (Creal Q δ̂₁) .Iso.bwd ∘ realise .fmor NB₂)) ∘ ℰP.p₂)
      ≈⟨ CoK.∘-cong ≈-refl (∘-cong (≈-trans (≈-sym (assoc _ _ _)) (≈-trans (∘-cong (MCδ.GI (Creal Q δ̂₁) .Iso.fwd∘bwd≈id) ≈-refl) id-left)) ≈-refl) ⟩
        Gmap Q δ̂₂ A₁ ∘co (realise .fmor NB₂ ∘ ℰP.p₂)
      ∎ where open ≈-Reasoning isEquiv

    -- The δ̂₁-side tail transforms into the δ̂₂-side tail (named factors,
    -- normalised to right-nested form on both sides).
    tail-eq : ∀ {Z : obj} (X : ℰP.prod Γ (realise .fobj (FM.fobj FM.μObj Q̂ (extend δ̂₁ (FM.μObj Q̂ ε̂₁)))) ⇒ Z) →
              (((X ∘co (KK₁ .Iso.fwd ∘ ℰP.p₂)) ∘co Gmap Q δ̂₁ A₁) ∘co ((MCδ.GI (Creal Q δ̂₁) .Iso.bwd ∘ realise .fmor NB₂) ∘ ℰP.p₂))
              ≈ (((X ∘co (Mδμ .Iso.bwd ∘ ℰP.p₂)) ∘co (KK₂ .Iso.fwd ∘ ℰP.p₂)) ∘co (((realise .fmor NF₂ ∘ ℰP.p₂) ∘co Gmap Q δ̂₂ A₁) ∘co (realise .fmor NB₂ ∘ ℰP.p₂)))
    tail-eq {Z} X = ≈-trans lhs-norm (≈-sym rhs-norm)
      where
        k₁ = KK₁ .Iso.fwd ∘ ℰP.p₂
        g₁ = Gmap Q δ̂₁ A₁
        r  = (MCδ.GI (Creal Q δ̂₁) .Iso.bwd ∘ realise .fmor NB₂) ∘ ℰP.p₂
        mδ = Mδμ .Iso.bwd ∘ ℰP.p₂
        k₂ = KK₂ .Iso.fwd ∘ ℰP.p₂
        nf = realise .fmor NF₂ ∘ ℰP.p₂
        gi = MCδ.GI C₁ε .Iso.fwd ∘ ℰP.p₂
        g₂ = Gmap Q δ̂₂ A₁
        nb = realise .fmor NB₂ ∘ ℰP.p₂

        KK₁-path : KK₁ .Iso.fwd ≈ (Mδμ .Iso.bwd ∘ ((KK₂ .Iso.fwd ∘ realise .fmor NF₂) ∘ MCδ.GI C₁ε .Iso.fwd))
        KK₁-path = iso-shuffle Mδμ _ _ env-collapse-square

        k₁-split : k₁ ≈ (mδ ∘co (k₂ ∘co (nf ∘co gi)))
        k₁-split =
          begin
            KK₁ .Iso.fwd ∘ ℰP.p₂
          ≈⟨ ∘-cong KK₁-path ≈-refl ⟩
            (Mδμ .Iso.bwd ∘ ((KK₂ .Iso.fwd ∘ realise .fmor NF₂) ∘ MCδ.GI C₁ε .Iso.fwd)) ∘ ℰP.p₂
          ≈˘⟨ co-pure _ _ ⟩
            mδ ∘co (((KK₂ .Iso.fwd ∘ realise .fmor NF₂) ∘ MCδ.GI C₁ε .Iso.fwd) ∘ ℰP.p₂)
          ≈˘⟨ CoK.∘-cong ≈-refl (co-pure _ _) ⟩
            mδ ∘co (((KK₂ .Iso.fwd ∘ realise .fmor NF₂) ∘ ℰP.p₂) ∘co gi)
          ≈˘⟨ CoK.∘-cong ≈-refl (CoK.∘-cong (co-pure _ _) ≈-refl) ⟩
            mδ ∘co ((k₂ ∘co nf) ∘co gi)
          ≈⟨ CoK.∘-cong ≈-refl (CoK.assoc _ _ _) ⟩
            mδ ∘co (k₂ ∘co (nf ∘co gi))
          ∎ where open ≈-Reasoning isEquiv

        lhs-norm : (((X ∘co k₁) ∘co g₁) ∘co r) ≈ (X ∘co (mδ ∘co (k₂ ∘co (nf ∘co (g₂ ∘co nb)))))
        lhs-norm =
          begin
            ((X ∘co k₁) ∘co g₁) ∘co r
          ≈⟨ CoK.assoc _ _ _ ⟩
            (X ∘co k₁) ∘co (g₁ ∘co r)
          ≈⟨ CoK.assoc _ _ _ ⟩
            X ∘co (k₁ ∘co (g₁ ∘co r))
          ≈⟨ CoK.∘-cong ≈-refl (CoK.∘-cong k₁-split ≈-refl) ⟩
            X ∘co ((mδ ∘co (k₂ ∘co (nf ∘co gi))) ∘co (g₁ ∘co r))
          ≈⟨ CoK.∘-cong ≈-refl (CoK.assoc _ _ _) ⟩
            X ∘co (mδ ∘co ((k₂ ∘co (nf ∘co gi)) ∘co (g₁ ∘co r)))
          ≈⟨ CoK.∘-cong ≈-refl (CoK.∘-cong ≈-refl (CoK.assoc _ _ _)) ⟩
            X ∘co (mδ ∘co (k₂ ∘co ((nf ∘co gi) ∘co (g₁ ∘co r))))
          ≈⟨ CoK.∘-cong ≈-refl (CoK.∘-cong ≈-refl (CoK.∘-cong ≈-refl (CoK.assoc _ _ _))) ⟩
            X ∘co (mδ ∘co (k₂ ∘co (nf ∘co (gi ∘co (g₁ ∘co r)))))
          ≈⟨ CoK.∘-cong ≈-refl (CoK.∘-cong ≈-refl (CoK.∘-cong ≈-refl (CoK.∘-cong ≈-refl (≈-trans (≈-sym (CoK.assoc _ _ _)) bracket)))) ⟩
            X ∘co (mδ ∘co (k₂ ∘co (nf ∘co (g₂ ∘co nb))))
          ∎ where open ≈-Reasoning isEquiv

        rhs-norm : (((X ∘co mδ) ∘co k₂) ∘co ((nf ∘co g₂) ∘co nb)) ≈ (X ∘co (mδ ∘co (k₂ ∘co (nf ∘co (g₂ ∘co nb)))))
        rhs-norm =
          begin
            ((X ∘co mδ) ∘co k₂) ∘co ((nf ∘co g₂) ∘co nb)
          ≈⟨ CoK.assoc _ _ _ ⟩
            (X ∘co mδ) ∘co (k₂ ∘co ((nf ∘co g₂) ∘co nb))
          ≈⟨ CoK.assoc _ _ _ ⟩
            X ∘co (mδ ∘co (k₂ ∘co ((nf ∘co g₂) ∘co nb)))
          ≈⟨ CoK.∘-cong ≈-refl (CoK.∘-cong ≈-refl (CoK.∘-cong ≈-refl (CoK.assoc _ _ _))) ⟩
            X ∘co (mδ ∘co (k₂ ∘co (nf ∘co (g₂ ∘co nb))))
          ∎ where open ≈-Reasoning isEquiv

    HEAD : ℰP.prod Γ (realise .fobj (FM.fobj FM.μObj Q̂ (extend δ̂₁ (FM.μObj Q̂ ε̂₁)))) ⇒ Creal Q ε̂₂
    HEAD = (Mε₂.inR ∘ (Kε₂ .Iso.bwd ∘ Mεμ .Iso.fwd)) ∘ fmorη Γ _ sfp₁

    head-assoc : ((Mε₂.inR ∘ Kε₂ .Iso.bwd) ∘ (Mεμ .Iso.fwd ∘ fmorη Γ _ sfp₁)) ≈ HEAD
    head-assoc = ≈-trans (≈-sym (assoc _ _ _)) (∘-cong (assoc _ _ _) ≈-refl)

    -- The δ̂₂-side fold algebra, in composite form.
    head₂-eq : fmorη Γ (FM.fobj FM.μObj Q̂ (extend δ̂₂ (FM.μObj Q̂ ε̂₂)))
                 (FM.Mor-∘ (FMu.α Q̂ ε̂₂) sfp₂)
               ≈ (HEAD ∘co (Mδμ .Iso.bwd ∘ ℰP.p₂))
    head₂-eq =
      ≈-trans (fmorη-post Γ _ (FMu.α Q̂ ε̂₂) sfp₂)
        (≈-trans (∘-cong (inR-K Q ε̂₂ CQ) ≈-refl)
          (≈-trans (∘-cong ≈-refl (≈-sym (co-iso-cancel Mδμ (cross-mixed Q CQ isosδ isosε {Ŷ₁ = FM.μObj Q̂ ε̂₁} {Ŷ₂ = FM.μObj Q̂ ε̂₂} muε gs₁ gs₂ sqs))))
            (≈-trans (≈-sym (assoc _ _ _)) (CoK.∘-cong head-assoc ≈-refl))))

    -- The δ̂₁-side fold algebra, pushed under the ε̂-collapse.
    head₁-eq : (muε .Iso.fwd ∘ Sδ₁.aStar) ≈ (HEAD ∘co (KK₁ .Iso.fwd ∘ ℰP.p₂))
    head₁-eq =
      ≈-trans (≈-sym (assoc _ _ _)) (CoK.∘-cong head-inner ≈-refl)
      where
        head-inner : (muε .Iso.fwd ∘ fmorη Γ (FM.fobj FM.μObj Q̂ (extend δ̂₁ (FM.μObj Q̂ ε̂₁))) (FM.Mor-∘ (FMu.α Q̂ ε̂₁) sfp₁)) ≈ HEAD
        head-inner =
          ≈-trans (∘-cong ≈-refl (fmorη-post Γ _ (FMu.α Q̂ ε̂₁) sfp₁))
            (≈-trans (≈-sym (assoc _ _ _)) (∘-cong head-eq ≈-refl))

    -- The fold square for the composite candidate.
    B-square : (B' ∘co (Mδ₂.inR ∘ ℰP.p₂)) ≈ (Sδ₂.aStar ∘co Gmap Q δ̂₂ B')
    B-square = ≈-trans lhs-eq (≈-sym (CoK.∘-cong (CoK.∘-cong head₂-eq ≈-refl) gmapB'))
      where
        step-fold : ((muε .Iso.fwd ∘ A₁) ∘co (Mδ₁.inR ∘ ℰP.p₂))
                    ≈ ((HEAD ∘co (KK₁ .Iso.fwd ∘ ℰP.p₂)) ∘co Gmap Q δ̂₁ A₁)
        step-fold =
          ≈-trans (assoc _ _ _)
            (≈-trans (∘-cong ≈-refl Sδ₁.sμf-square)
              (≈-trans (≈-sym (assoc _ _ _)) (CoK.∘-cong head₁-eq ≈-refl)))

        lhs-eq : (B' ∘co (Mδ₂.inR ∘ ℰP.p₂))
                 ≈ (((HEAD ∘co (Mδμ .Iso.bwd ∘ ℰP.p₂)) ∘co (KK₂ .Iso.fwd ∘ ℰP.p₂)) ∘co (((realise .fmor NF₂ ∘ ℰP.p₂) ∘co Gmap Q δ̂₂ A₁) ∘co (realise .fmor NB₂ ∘ ℰP.p₂)))
        lhs-eq =
          begin
            B' ∘co (Mδ₂.inR ∘ ℰP.p₂)
          ≈⟨ CoK.assoc _ _ _ ⟩
            (muε .Iso.fwd ∘ A₁) ∘co ((muδ .Iso.bwd ∘ ℰP.p₂) ∘co (Mδ₂.inR ∘ ℰP.p₂))
          ≈⟨ CoK.∘-cong ≈-refl (co-pure _ _) ⟩
            (muε .Iso.fwd ∘ A₁) ∘co ((muδ .Iso.bwd ∘ Mδ₂.inR) ∘ ℰP.p₂)
          ≈⟨ CoK.∘-cong ≈-refl (∘-cong (mu-collapse-bwd-in' Q CQ δ̂₁ δ̂₂ isosδ) ≈-refl) ⟩
            (muε .Iso.fwd ∘ A₁) ∘co ((Mδ₁.inR ∘ (MCδ.GI (Creal Q δ̂₁) .Iso.bwd ∘ realise .fmor NB₂)) ∘ ℰP.p₂)
          ≈˘⟨ CoK.∘-cong ≈-refl (co-pure _ _) ⟩
            (muε .Iso.fwd ∘ A₁) ∘co ((Mδ₁.inR ∘ ℰP.p₂) ∘co ((MCδ.GI (Creal Q δ̂₁) .Iso.bwd ∘ realise .fmor NB₂) ∘ ℰP.p₂))
          ≈˘⟨ CoK.assoc _ _ _ ⟩
            ((muε .Iso.fwd ∘ A₁) ∘co (Mδ₁.inR ∘ ℰP.p₂)) ∘co ((MCδ.GI (Creal Q δ̂₁) .Iso.bwd ∘ realise .fmor NB₂) ∘ ℰP.p₂)
          ≈⟨ CoK.∘-cong step-fold ≈-refl ⟩
            ((HEAD ∘co (KK₁ .Iso.fwd ∘ ℰP.p₂)) ∘co Gmap Q δ̂₁ A₁) ∘co ((MCδ.GI (Creal Q δ̂₁) .Iso.bwd ∘ realise .fmor NB₂) ∘ ℰP.p₂)
          ≈⟨ tail-eq HEAD ⟩
            ((HEAD ∘co (Mδμ .Iso.bwd ∘ ℰP.p₂)) ∘co (KK₂ .Iso.fwd ∘ ℰP.p₂)) ∘co (((realise .fmor NF₂ ∘ ℰP.p₂) ∘co Gmap Q δ̂₂ A₁) ∘co (realise .fmor NB₂ ∘ ℰP.p₂))
          ∎ where open ≈-Reasoning isEquiv

  -- The naturality square of the μ-collapse.
  mu-natural : (Sδ₂.A' ∘co (muδ .Iso.fwd ∘ ℰP.p₂)) ≈ (muε .Iso.fwd ∘ Sδ₁.A')
  mu-natural =
    co-iso-move muδ (≈-trans Sδ₂.sμf-fold (≈-sym (Mδ₂.foldR-η Sδ₂.aStar B' B-square)))

-- The μ case of the collapse interface.
collapse-mu : ∀ {n} {P : Poly ℰ (suc n)} → CollapseAt P → CollapseAt (polynomial-functor-2.Poly.μ P)
collapse-mu {n} {P} CP = record
  { iso = MuCollapse.mu-collapse P CP
  ; natural = λ {Γ} {ε̂₁} {ε̂₂} δ̂₁ δ̂₂ isosδ isosε gs₁ gs₂ sqs →
      MuNat.mu-natural P CP δ̂₁ δ̂₂ ε̂₁ ε̂₂ isosδ isosε gs₁ gs₂ sqs
  ; refl-iso = mu-collapse-refl P CP
  ; comp = λ δ̂₁ δ̂₂ δ̂₃ isos₁₂ isos₂₃ → mu-collapse-comp P CP δ̂₁ δ̂₂ δ̂₃ isos₁₂ isos₂₃
  }

-- Every polynomial admits environment collapse.
collapseAt : ∀ {n} (P : Poly ℰ n) → CollapseAt P
collapseAt (polynomial-functor-2.Poly.const A) = collapse-const A
collapseAt (polynomial-functor-2.Poly.var i)   = collapse-var i
collapseAt (P polynomial-functor-2.Poly.+ Q)   = collapse-sum (collapseAt P) (collapseAt Q)
collapseAt (P polynomial-functor-2.Poly.× Q)   = collapse-prod (collapseAt P) (collapseAt Q)
collapseAt (polynomial-functor-2.Poly.μ P)     = collapse-mu (collapseAt P)
