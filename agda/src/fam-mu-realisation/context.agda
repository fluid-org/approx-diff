{-# OPTIONS --prop --postfix-projections --safe #-}

-- The co-Kleisli context calculus of realisation: objects and actions of
-- the realised polynomial endofunctor, realisation of morphisms in an
-- η-embedded context, and the in-context isomorphism algebra.

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

module fam-mu-realisation.context {o m e} (os es : Level) {ℰ : Category o m e}
  (ℰC : ∀ (A : Setoid os (os ⊔ es)) → HasColimits (setoid→category A) ℰ)
  (ℰT : HasTerminal ℰ) (ℰP : HasProducts ℰ) (ℰE : HasExponentials ℰ ℰP)
  (ℰSC : HasStrongCoproducts ℰ ℰP)
  where

open Category ℰ public
open Functor public

module ℰP = HasProducts ℰP
module ℰT' = HasTerminal ℰT

module FR = fam-realisation os (os ⊔ es) ℰC
open FR using (realise; η; realise-η-iso; transpose; untranspose) public

module FM = fam-mu-types-2 os es ℰT ℰP

module FMu = FM.HasMu FM.hasMu
module FamC = Category FM.cat
module FamCoK {Γ̂ : FM.Obj} = Category (coKleisli-prod FM.products Γ̂)
module FMuI = polynomial-functor-2.MuIso (FM.terminal ℰT) FM.products FM.strongCoproducts FM.hasMu FM.hasMuLaws

module ℰI = polynomial-functor-2.Interp ℰT ℰP ℰSC
open ℰI using (_∘co_) public

module CoK {Γ : obj} = Category (coKleisli-prod ℰP Γ)

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
fmorη-cong u₁≃u₂ = ∘-cong₁ (realise .fmor-cong u₁≃u₂)

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
  ≈⟨ ∘-cong₁ (ℰP.pair-p₁ _ _) ⟩
    (realise-η-iso Γ .Iso.fwd ∘ ℰP.p₁) ∘ FR.realise-products-iso ℰP ℰE (η .fobj Γ) X .Iso.fwd
  ≈⟨ assoc _ _ _ ⟩
    realise-η-iso Γ .Iso.fwd ∘ (ℰP.p₁ ∘ FR.realise-products-iso ℰP ℰE (η .fobj Γ) X .Iso.fwd)
  ≈⟨ ∘-cong₂ (FR.realise-products-p₁ ℰP ℰE (η .fobj Γ) X) ⟩
    realise-η-iso Γ .Iso.fwd ∘ realise .fmor FM.Fam𝒞-P.p₁
  ∎ where open ≈-Reasoning isEquiv

prodη-p₂ : ∀ (Γ : obj) (X : FM.Obj) →
           (ℰP.p₂ ∘ prodη Γ X .Iso.fwd) ≈ realise .fmor FM.Fam𝒞-P.p₂
prodη-p₂ Γ X =
  begin
    ℰP.p₂ ∘ (ℰP.prod-m (realise-η-iso Γ .Iso.fwd) (id _) ∘ FR.realise-products-iso ℰP ℰE (η .fobj Γ) X .Iso.fwd)
  ≈˘⟨ assoc _ _ _ ⟩
    (ℰP.p₂ ∘ ℰP.prod-m (realise-η-iso Γ .Iso.fwd) (id _)) ∘ FR.realise-products-iso ℰP ℰE (η .fobj Γ) X .Iso.fwd
  ≈⟨ ∘-cong₁ (ℰP.pair-p₂ _ _) ⟩
    (id _ ∘ ℰP.p₂) ∘ FR.realise-products-iso ℰP ℰE (η .fobj Γ) X .Iso.fwd
  ≈⟨ ∘-cong₁ id-left ⟩
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
    (≈-trans (∘-cong₁ (≈-sym (prodη Γ Y .Iso.bwd∘fwd≈id)))
      (≈-trans (assoc _ _ _) (∘-cong₂ core)))
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
          ≈⟨ ∘-cong₁ (prodη-p₁ Γ Y) ⟩
            (realise-η-iso Γ .Iso.fwd ∘ realise .fmor FM.Fam𝒞-P.p₁) ∘ (realise .fmor (pairη Γ X v) ∘ prodη Γ X .Iso.bwd)
          ≈⟨ assoc _ _ _ ⟩
            realise-η-iso Γ .Iso.fwd ∘ (realise .fmor FM.Fam𝒞-P.p₁ ∘ (realise .fmor (pairη Γ X v) ∘ prodη Γ X .Iso.bwd))
          ≈˘⟨ ∘-cong₂ (assoc _ _ _) ⟩
            realise-η-iso Γ .Iso.fwd ∘ ((realise .fmor FM.Fam𝒞-P.p₁ ∘ realise .fmor (pairη Γ X v)) ∘ prodη Γ X .Iso.bwd)
          ≈˘⟨ ∘-cong₂ (∘-cong₁ (realise .fmor-comp _ _)) ⟩
            realise-η-iso Γ .Iso.fwd ∘ (realise .fmor (FM.Mor-∘ FM.Fam𝒞-P.p₁ (pairη Γ X v)) ∘ prodη Γ X .Iso.bwd)
          ≈⟨ ∘-cong₂ (∘-cong₁ (realise .fmor-cong (FM.Fam𝒞-P.pair-p₁ _ _))) ⟩
            realise-η-iso Γ .Iso.fwd ∘ (realise .fmor (FM.Fam𝒞-P.p₁ {x = η .fobj Γ} {y = X}) ∘ prodη Γ X .Iso.bwd)
          ≈˘⟨ assoc _ _ _ ⟩
            (realise-η-iso Γ .Iso.fwd ∘ realise .fmor (FM.Fam𝒞-P.p₁ {x = η .fobj Γ} {y = X})) ∘ prodη Γ X .Iso.bwd
          ≈˘⟨ ∘-cong₁ (prodη-p₁ Γ X) ⟩
            (ℰP.p₁ {Γ} {realise .fobj X} ∘ prodη Γ X .Iso.fwd) ∘ prodη Γ X .Iso.bwd
          ≈⟨ assoc _ _ _ ⟩
            ℰP.p₁ {Γ} {realise .fobj X} ∘ (prodη Γ X .Iso.fwd ∘ prodη Γ X .Iso.bwd)
          ≈⟨ ∘-cong₂ (prodη Γ X .Iso.fwd∘bwd≈id) ⟩
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
          ≈⟨ ∘-cong₁ (prodη-p₂ Γ Y) ⟩
            realise .fmor FM.Fam𝒞-P.p₂ ∘ (realise .fmor (pairη Γ X v) ∘ prodη Γ X .Iso.bwd)
          ≈˘⟨ assoc _ _ _ ⟩
            (realise .fmor FM.Fam𝒞-P.p₂ ∘ realise .fmor (pairη Γ X v)) ∘ prodη Γ X .Iso.bwd
          ≈˘⟨ ∘-cong₁ (realise .fmor-comp _ _) ⟩
            realise .fmor (FM.Mor-∘ FM.Fam𝒞-P.p₂ (pairη Γ X v)) ∘ prodη Γ X .Iso.bwd
          ≈⟨ ∘-cong₁ (realise .fmor-cong (FM.Fam𝒞-P.pair-p₂ _ _)) ⟩
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
  ≈⟨ ∘-cong₁ (realise .fmor-comp _ _) ⟩
    (realise .fmor u ∘ realise .fmor (pairη Γ X v)) ∘ prodη Γ X .Iso.bwd
  ≈⟨ assoc _ _ _ ⟩
    realise .fmor u ∘ (realise .fmor (pairη Γ X v) ∘ prodη Γ X .Iso.bwd)
  ≈⟨ ∘-cong₂ (prodη-pair Γ X v) ⟩
    realise .fmor u ∘ (prodη Γ Y .Iso.bwd ∘ ℰP.pair (ℰP.p₁ {Γ} {realise .fobj X}) (fmorη Γ X v))
  ≈˘⟨ assoc _ _ _ ⟩
    (realise .fmor u ∘ prodη Γ Y .Iso.bwd) ∘ ℰP.pair (ℰP.p₁ {Γ} {realise .fobj X}) (fmorη Γ X v)
  ∎ where open ≈-Reasoning isEquiv

-- The context projection realises to the projection.
fmorη-p₂ : ∀ (Γ : obj) (X : FM.Obj) →
           fmorη Γ X (FM.Fam𝒞-P.p₂ {x = η .fobj Γ} {y = X}) ≈ ℰP.p₂
fmorη-p₂ Γ X =
  begin
    realise .fmor (FM.Fam𝒞-P.p₂ {x = η .fobj Γ} {y = X}) ∘ prodη Γ X .Iso.bwd
  ≈˘⟨ ∘-cong₁ (prodη-p₂ Γ X) ⟩
    (ℰP.p₂ ∘ prodη Γ X .Iso.fwd) ∘ prodη Γ X .Iso.bwd
  ≈⟨ assoc _ _ _ ⟩
    ℰP.p₂ ∘ (prodη Γ X .Iso.fwd ∘ prodη Γ X .Iso.bwd)
  ≈⟨ ∘-cong₂ (prodη Γ X .Iso.fwd∘bwd≈id) ⟩
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
  ≈⟨ ∘-cong₁ (realise .fmor-comp _ _) ⟩
    (realise .fmor w ∘ realise .fmor (FM.Fam𝒞-P.p₂ {x = η .fobj Γ} {y = X})) ∘ prodη Γ X .Iso.bwd
  ≈⟨ assoc _ _ _ ⟩
    realise .fmor w ∘ (realise .fmor (FM.Fam𝒞-P.p₂ {x = η .fobj Γ} {y = X}) ∘ prodη Γ X .Iso.bwd)
  ≈⟨ ∘-cong₂ (fmorη-p₂ Γ X) ⟩
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
  ≈˘⟨ ∘-cong₁ (FR.transpose-realise (untranspose g)) ⟩
    transpose (untranspose g) ∘ prodη Γ X .Iso.bwd
  ≈⟨ ∘-cong₁ (FR.transpose-untranspose g) ⟩
    g ∘ prodη Γ X .Iso.bwd
  ∎ where open ≈-Reasoning isEquiv

-- Composition in context of pure morphisms.
co-pure : ∀ {Γ X Y Z : obj} (x : Y ⇒ Z) (y : X ⇒ Y) →
          ((x ∘ ℰP.p₂ {Γ} {Y}) ∘co (y ∘ ℰP.p₂)) ≈ ((x ∘ y) ∘ ℰP.p₂)
co-pure x y =
  ≈-trans (assoc _ _ _)
    (≈-trans (∘-cong₂ (ℰP.pair-p₂ _ _)) (≈-sym (assoc _ _ _)))

-- Cancel an isomorphism applied in context on the right of a composition.
co-iso-cancel : ∀ {Γ X Y Z : obj} (I : Iso X Y)
                {u : ℰP.prod Γ Y ⇒ Z} {v : ℰP.prod Γ X ⇒ Z} →
                (u ∘co (I .Iso.fwd ∘ ℰP.p₂)) ≈ v → (v ∘co (I .Iso.bwd ∘ ℰP.p₂)) ≈ u
co-iso-cancel I {u} {v} eq =
  begin
    v ∘co (I .Iso.bwd ∘ ℰP.p₂)
  ≈˘⟨ CoK.∘-cong₁ eq ⟩
    (u ∘co (I .Iso.fwd ∘ ℰP.p₂)) ∘co (I .Iso.bwd ∘ ℰP.p₂)
  ≈⟨ CoK.assoc _ _ _ ⟩
    u ∘co ((I .Iso.fwd ∘ ℰP.p₂) ∘co (I .Iso.bwd ∘ ℰP.p₂))
  ≈⟨ CoK.∘-cong₂ (co-pure (I .Iso.fwd) (I .Iso.bwd)) ⟩
    u ∘co ((I .Iso.fwd ∘ I .Iso.bwd) ∘ ℰP.p₂)
  ≈⟨ CoK.∘-cong₂ (∘-cong₁ (I .Iso.fwd∘bwd≈id)) ⟩
    u ∘co (id _ ∘ ℰP.p₂)
  ≈⟨ CoK.∘-cong₂ id-left ⟩
    u ∘co ℰP.p₂
  ≈⟨ CoK.id-right ⟩
    u
  ∎ where open ≈-Reasoning isEquiv

-- Move an isomorphism across an equation.
iso-shuffle : ∀ {X Y Z : obj} (I : Iso Y Z) (f : X ⇒ Y) (g : X ⇒ Z) →
              (I .Iso.fwd ∘ f) ≈ g → f ≈ (I .Iso.bwd ∘ g)
iso-shuffle I f g eq =
  ≈-trans (≈-sym id-left)
    (≈-trans (∘-cong₁ (≈-sym (I .Iso.bwd∘fwd≈id)))
      (≈-trans (assoc _ _ _) (∘-cong₂ eq)))

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
      ≈˘⟨ ∘-cong₂ (prodη Γ X .Iso.bwd∘fwd≈id) ⟩
        realise .fmor u ∘ (prodη Γ X .Iso.bwd ∘ prodη Γ X .Iso.fwd)
      ≈˘⟨ assoc _ _ _ ⟩
        fmorη Γ X u ∘ prodη Γ X .Iso.fwd
      ≈⟨ ∘-cong₁ eq ⟩
        fmorη Γ X v ∘ prodη Γ X .Iso.fwd
      ≈⟨ assoc _ _ _ ⟩
        realise .fmor v ∘ (prodη Γ X .Iso.bwd ∘ prodη Γ X .Iso.fwd)
      ≈⟨ ∘-cong₂ (prodη Γ X .Iso.bwd∘fwd≈id) ⟩
        realise .fmor v ∘ id _
      ≈⟨ id-right ⟩
        realise .fmor v
      ∎ where open ≈-Reasoning isEquiv

    tr-eq : transpose u ≈ transpose v
    tr-eq =
      ≈-trans (FR.transpose-realise u)
        (≈-trans (∘-cong₂ real-eq) (≈-sym (FR.transpose-realise v)))

-- The pairing of the projections is the identity.
pair-p₁p₂-id : ∀ {Γ A : obj} → ℰP.pair (ℰP.p₁ {Γ} {A}) ℰP.p₂ ≈ id _
pair-p₁p₂-id =
  ≈-trans (ℰP.pair-cong (≈-sym id-right) (≈-sym id-right)) (ℰP.pair-ext (id _))

-- Move an isomorphism across an equation, and cancel one.
iso-mono : ∀ {X Y Z : obj} (I : Iso Y Z) {f g : X ⇒ Y} →
           (I .Iso.fwd ∘ f) ≈ (I .Iso.fwd ∘ g) → f ≈ g
iso-mono I {f} {g} eq =
  ≈-trans (iso-shuffle I _ _ eq)
    (≈-trans (≈-sym (assoc _ _ _)) (≈-trans (∘-cong₁ (I .Iso.bwd∘fwd≈id)) id-left))

-- Realising a morphism transposed to Fam(ℰ) and collapsing recovers it.
absorb : ∀ {Γ A : obj} (X : FM.Obj) (g : ℰP.prod Γ (realise .fobj X) ⇒ A) →
         (realise-η-iso A .Iso.fwd ∘ fmorη Γ X (untranspose (g ∘ prodη Γ X .Iso.fwd))) ≈ g
absorb {Γ} {A} X g =
  ≈-trans (counit-fmorη Γ X _)
    (≈-trans (assoc _ _ _)
      (≈-trans (∘-cong₂ (prodη Γ X .Iso.fwd∘bwd≈id)) id-right))

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
  ≈-trans (∘-cong₂ (fmorη-cong (FR.untranspose-cong (≈-sym (assoc _ _ _)))))
    (≈-trans (absorb (η .fobj A₀) (h ∘ ℰP.prod-m (id _) (realise-η-iso A₀ .Iso.fwd))) ≈-refl)

-- The transposed context morphism against the counit inverses.
ctxη-counit-sq : ∀ (Γ A₀ : obj) {A : obj} (h : ℰP.prod Γ A₀ ⇒ A) →
                 (fmorη Γ (η .fobj A₀) (ctxη Γ A₀ h) ∘co (realise-η-iso A₀ .Iso.bwd ∘ ℰP.p₂))
                 ≈ (realise-η-iso A .Iso.bwd ∘ h)
ctxη-counit-sq Γ A₀ {A} h =
  begin
    fmorη Γ (η .fobj A₀) (ctxη Γ A₀ h) ∘co (realise-η-iso A₀ .Iso.bwd ∘ ℰP.p₂)
  ≈⟨ CoK.∘-cong₁ (iso-shuffle (realise-η-iso A) _ _ (ctxη-counit Γ A₀ h)) ⟩
    (realise-η-iso A .Iso.bwd ∘ (h ∘ ℰP.prod-m (id _) (realise-η-iso A₀ .Iso.fwd))) ∘co (realise-η-iso A₀ .Iso.bwd ∘ ℰP.p₂)
  ≈⟨ assoc _ _ _ ⟩
    realise-η-iso A .Iso.bwd ∘ ((h ∘ ℰP.prod-m (id _) (realise-η-iso A₀ .Iso.fwd)) ∘ ℰP.pair ℰP.p₁ (realise-η-iso A₀ .Iso.bwd ∘ ℰP.p₂))
  ≈⟨ ∘-cong₂ (assoc _ _ _) ⟩
    realise-η-iso A .Iso.bwd ∘ (h ∘ (ℰP.prod-m (id _) (realise-η-iso A₀ .Iso.fwd) ∘ ℰP.pair ℰP.p₁ (realise-η-iso A₀ .Iso.bwd ∘ ℰP.p₂)))
  ≈⟨ ∘-cong₂ (∘-cong₂ (ℰP.pair-compose _ _ _ _)) ⟩
    realise-η-iso A .Iso.bwd ∘ (h ∘ ℰP.pair (id _ ∘ ℰP.p₁) (realise-η-iso A₀ .Iso.fwd ∘ (realise-η-iso A₀ .Iso.bwd ∘ ℰP.p₂)))
  ≈⟨ ∘-cong₂ (∘-cong₂ (ℰP.pair-cong id-left (≈-trans (≈-sym (assoc _ _ _)) (≈-trans (∘-cong₁ (realise-η-iso A₀ .Iso.fwd∘bwd≈id)) id-left)))) ⟩
    realise-η-iso A .Iso.bwd ∘ (h ∘ ℰP.pair ℰP.p₁ ℰP.p₂)
  ≈⟨ ∘-cong₂ (≈-trans (∘-cong₂ pair-p₁p₂-id) id-right) ⟩
    realise-η-iso A .Iso.bwd ∘ h
  ∎ where open ≈-Reasoning isEquiv

-- The strong functorial action of the realised endofunctor: transpose the
-- context morphism to Fam(ℰ), act there, and realise.
Gmap : ∀ {n} (P : Poly ℰ (suc n)) (δ̂ : Fin n → FM.Obj) {Γ A B} →
       (ℰP.prod Γ A ⇒ B) → ℰP.prod Γ (Greal P δ̂ A) ⇒ Greal P δ̂ B
Gmap P δ̂ {Γ} {A} {B} h =
  realise .fmor
    (FMu.strong-fmor (Poly-map η P) (FMu.strong-extend-mor (λ i → FM.Fam𝒞-P.p₂) (ctxη Γ A h)))
    ∘ prodη Γ (FM.fobj FM.μObj (Poly-map η P) (extend δ̂ (η .fobj A))) .Iso.bwd

-- Componentwise naturality squares for identity and projection components.
sq-refl : ∀ {Γ : obj} {X̂ Ŷ : FM.Obj} (u : FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) X̂) Ŷ) →
          (fmorη Γ X̂ u ∘co (Iso-refl .Iso.fwd ∘ ℰP.p₂)) ≈ (Iso-refl .Iso.fwd ∘ fmorη Γ X̂ u)
sq-refl {Γ} {X̂} u =
  ≈-trans (∘-cong₂ (ℰP.pair-cong ≈-refl id-left))
    (≈-trans (∘-cong₂ pair-p₁p₂-id) (≈-trans id-right (≈-sym id-left)))

sq-p₂ : ∀ {Γ : obj} {X̂ Ŷ : FM.Obj} (I : Iso (realise .fobj X̂) (realise .fobj Ŷ)) →
        (fmorη Γ Ŷ (FM.Fam𝒞-P.p₂ {x = η .fobj Γ} {y = Ŷ}) ∘co (I .Iso.fwd ∘ ℰP.p₂))
        ≈ (I .Iso.fwd ∘ fmorη Γ X̂ (FM.Fam𝒞-P.p₂ {x = η .fobj Γ} {y = X̂}))
sq-p₂ {Γ} {X̂} {Ŷ} I =
  ≈-trans (CoK.∘-cong₁ (fmorη-p₂ Γ Ŷ))
    (≈-trans CoK.id-left (≈-sym (∘-cong₂ (fmorη-p₂ Γ X̂))))

-- The realised strong action is a co-Kleisli functor.
private
  ctxη-p₂ : ∀ (Γ A : obj) → Category._≈_ FM.cat (ctxη Γ A ℰP.p₂) (FM.Fam𝒞-P.p₂ {x = η .fobj Γ} {y = η .fobj A})
  ctxη-p₂ Γ A = fmorη-inj Γ (η .fobj A) _ _
    (iso-mono (realise-η-iso A)
      (≈-trans (ctxη-counit Γ A ℰP.p₂)
        (≈-trans (ℰP.pair-p₂ _ _)
          (≈-sym (∘-cong₂ (fmorη-p₂ Γ (η .fobj A)))))))

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
        ≈⟨ ∘-cong₂ (ℰP.pair-natural _ _ _) ⟩
          h₂ ∘ ℰP.pair (ℰP.p₁ ∘ ℰP.prod-m (id _) (realise-η-iso A .Iso.fwd)) (h₁ ∘ ℰP.prod-m (id _) (realise-η-iso A .Iso.fwd))
        ≈⟨ ∘-cong₂ (ℰP.pair-cong (≈-trans (ℰP.pair-p₁ _ _) id-left) ≈-refl) ⟩
          h₂ ∘ ℰP.pair ℰP.p₁ (h₁ ∘ ℰP.prod-m (id _) (realise-η-iso A .Iso.fwd))
        ∎ where open ≈-Reasoning isEquiv

      rhs : (realise-η-iso C₀ .Iso.fwd ∘ fmorη Γ (η .fobj A) (FM.Mor-∘ (ctxη Γ B h₂) (pairη Γ (η .fobj A) (ctxη Γ A h₁))))
            ≈ (h₂ ∘ ℰP.pair ℰP.p₁ (h₁ ∘ ℰP.prod-m (id _) (realise-η-iso A .Iso.fwd)))
      rhs =
        begin
          realise-η-iso C₀ .Iso.fwd ∘ fmorη Γ (η .fobj A) (FM.Mor-∘ (ctxη Γ B h₂) (pairη Γ (η .fobj A) (ctxη Γ A h₁)))
        ≈⟨ ∘-cong₂ (fmorη-∘co Γ (η .fobj A) (ctxη Γ B h₂) (ctxη Γ A h₁)) ⟩
          realise-η-iso C₀ .Iso.fwd ∘ (fmorη Γ (η .fobj B) (ctxη Γ B h₂) ∘ ℰP.pair ℰP.p₁ (fmorη Γ (η .fobj A) (ctxη Γ A h₁)))
        ≈˘⟨ assoc _ _ _ ⟩
          (realise-η-iso C₀ .Iso.fwd ∘ fmorη Γ (η .fobj B) (ctxη Γ B h₂)) ∘ ℰP.pair ℰP.p₁ (fmorη Γ (η .fobj A) (ctxη Γ A h₁))
        ≈⟨ ∘-cong₁ (ctxη-counit Γ B h₂) ⟩
          (h₂ ∘ ℰP.prod-m (id _) (realise-η-iso B .Iso.fwd)) ∘ ℰP.pair ℰP.p₁ (fmorη Γ (η .fobj A) (ctxη Γ A h₁))
        ≈⟨ assoc _ _ _ ⟩
          h₂ ∘ (ℰP.prod-m (id _) (realise-η-iso B .Iso.fwd) ∘ ℰP.pair ℰP.p₁ (fmorη Γ (η .fobj A) (ctxη Γ A h₁)))
        ≈⟨ ∘-cong₂ (ℰP.pair-compose _ _ _ _) ⟩
          h₂ ∘ ℰP.pair (id _ ∘ ℰP.p₁) (realise-η-iso B .Iso.fwd ∘ fmorη Γ (η .fobj A) (ctxη Γ A h₁))
        ≈⟨ ∘-cong₂ (ℰP.pair-cong id-left (ctxη-counit Γ A h₁)) ⟩
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

-- Congruence of the realised strong action.
Gmap-cong : ∀ {n} (P : Poly ℰ (suc n)) (δ̂ : Fin n → FM.Obj) {Γ A B : obj}
            {h₁ h₂ : ℰP.prod Γ A ⇒ B} → h₁ ≈ h₂ → Gmap P δ̂ h₁ ≈ Gmap P δ̂ h₂
Gmap-cong P δ̂ {Γ} {A} {B} {h₁} {h₂} e =
  ∘-cong₁ (realise .fmor-cong (FMuI.strong-fmor-cong (Poly-map η P) eqs))
  where
    eqs : ∀ i → Category._≈_ FM.cat
            (FMu.strong-extend-mor (λ j → FM.Fam𝒞-P.p₂) (ctxη Γ A h₁) i)
            (FMu.strong-extend-mor (λ j → FM.Fam𝒞-P.p₂) (ctxη Γ A h₂) i)
    eqs Fin.zero    = FR.untranspose-cong (∘-cong₁ e)
    eqs (Fin.suc i) = FamC.≈-refl

-- A transposed morphism squares with the counits against its own counit form.
fmorη-ctxη-square : ∀ (Γ : obj) (X̂ Ŷ : FM.Obj) (w : FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) X̂) Ŷ) →
                    (fmorη Γ X̂ w ∘co (realise-η-iso (realise .fobj X̂) .Iso.fwd ∘ ℰP.p₂))
                    ≈ (realise-η-iso (realise .fobj Ŷ) .Iso.fwd ∘ fmorη Γ (η .fobj (realise .fobj X̂)) (ctxη Γ (realise .fobj X̂) (fmorη Γ X̂ w)))
fmorη-ctxη-square Γ X̂ Ŷ w =
  ≈-sym (≈-trans (ctxη-counit Γ (realise .fobj X̂) (fmorη Γ X̂ w))
    (∘-cong₂ (ℰP.pair-cong id-left ≈-refl)))

-- Postcomposition with a pure morphism under realisation in context.
fmorη-post : ∀ (Γ : obj) (X : FM.Obj) {Y Z : FM.Obj} (w : FM.Mor Y Z)
             (u : FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) X) Y) →
             fmorη Γ X (FM.Mor-∘ w u) ≈ (realise .fmor w ∘ fmorη Γ X u)
fmorη-post Γ X w u =
  ≈-trans (∘-cong₁ (realise .fmor-comp _ _)) (assoc _ _ _)

-- Cancel an isomorphism applied backwards in context on the right.
co-iso-epi : ∀ {Γ X Y Z : obj} (I : Iso X Y)
             {u v : ℰP.prod Γ X ⇒ Z} →
             ((u ∘co (I .Iso.bwd ∘ ℰP.p₂)) ≈ (v ∘co (I .Iso.bwd ∘ ℰP.p₂))) → u ≈ v
co-iso-epi I {u} {v} eq =
  begin
    u
  ≈˘⟨ CoK.id-right ⟩
    u ∘co ℰP.p₂
  ≈˘⟨ CoK.∘-cong₂ (≈-trans (co-pure _ _) (≈-trans (∘-cong₁ (I .Iso.bwd∘fwd≈id)) id-left)) ⟩
    u ∘co ((I .Iso.bwd ∘ ℰP.p₂) ∘co (I .Iso.fwd ∘ ℰP.p₂))
  ≈˘⟨ CoK.assoc _ _ _ ⟩
    (u ∘co (I .Iso.bwd ∘ ℰP.p₂)) ∘co (I .Iso.fwd ∘ ℰP.p₂)
  ≈⟨ CoK.∘-cong₁ eq ⟩
    (v ∘co (I .Iso.bwd ∘ ℰP.p₂)) ∘co (I .Iso.fwd ∘ ℰP.p₂)
  ≈⟨ CoK.assoc _ _ _ ⟩
    v ∘co ((I .Iso.bwd ∘ ℰP.p₂) ∘co (I .Iso.fwd ∘ ℰP.p₂))
  ≈⟨ CoK.∘-cong₂ (≈-trans (co-pure _ _) (≈-trans (∘-cong₁ (I .Iso.bwd∘fwd≈id)) id-left)) ⟩
    v ∘co ℰP.p₂
  ≈⟨ CoK.id-right ⟩
    v
  ∎ where open ≈-Reasoning isEquiv

-- Move an isomorphism in context across an equation.
co-iso-move : ∀ {Γ X Y Z : obj} (I : Iso X Y)
              {u : ℰP.prod Γ Y ⇒ Z} {v : ℰP.prod Γ X ⇒ Z} →
              u ≈ (v ∘co (I .Iso.bwd ∘ ℰP.p₂)) → (u ∘co (I .Iso.fwd ∘ ℰP.p₂)) ≈ v
co-iso-move I {u} {v} eq =
  ≈-trans (CoK.∘-cong₁ eq)
    (≈-trans (CoK.assoc _ _ _)
      (≈-trans (CoK.∘-cong₂ (≈-trans (co-pure _ _) (≈-trans (∘-cong₁ (I .Iso.bwd∘fwd≈id)) id-left)))
        CoK.id-right))

-- Cancel a projection from the terminal context.
p₂-cancel : ∀ {X Z : obj} {f g : X ⇒ Z} →
            ((f ∘ ℰP.p₂ {ℰT'.witness} {X}) ≈ (g ∘ ℰP.p₂)) → f ≈ g
p₂-cancel {X} {Z} {f} {g} eq =
  ≈-trans (≈-sym id-right)
    (≈-trans (∘-cong₂ (≈-sym (ℰP.pair-p₂ ℰT'.to-terminal (id _))))
      (≈-trans (≈-sym (assoc _ _ _))
        (≈-trans (∘-cong₁ eq)
          (≈-trans (assoc _ _ _)
            (≈-trans (∘-cong₂ (ℰP.pair-p₂ ℰT'.to-terminal (id _))) id-right)))))
