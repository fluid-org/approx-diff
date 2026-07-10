{-# OPTIONS --prop --postfix-projections --safe #-}

-- Pure lifts: realisation in context of pure Fam(ℰ) morphisms reduces to
-- the realised plain functorial action.

open import Level using (Level; _⊔_)
open import Data.Nat using (ℕ; suc)
import Data.Fin as Fin
open Fin using (Fin)
open import prop-setoid using (Setoid; module ≈-Reasoning)
open import categories
  using (Category; setoid→category; HasTerminal; HasProducts; HasExponentials;
         HasStrongCoproducts; HasCoproducts; strong-coproducts→coproducts; coKleisli-prod)
open import functor using (Functor; HasColimits)
open import polynomial-functor using (Poly; extend; Poly-map)
import fam
import fam-mu-types
import fam-realisation
import polynomial-functor
import fam-mu-realisation.context

module fam-mu-realisation.pure {o m e} (os es : Level) {ℰ : Category o m e}
  (ℰC : ∀ (A : Setoid os (os ⊔ es)) → HasColimits (setoid→category A) ℰ)
  (ℰT : HasTerminal ℰ) (ℰP : HasProducts ℰ) (ℰE : HasExponentials ℰ ℰP)
  (ℰSC : HasStrongCoproducts ℰ ℰP)
  where

open fam-mu-realisation.context os es ℰC ℰT ℰP ℰE ℰSC public

-- Untransposition absorbs realised precomposition.
untranspose-pre : ∀ {V W : FM.Obj} {X : obj}
                  (g : realise .fobj W ⇒ X) (w : FM.Mor V W) →
                  FamC._≈_ (untranspose (g ∘ realise .fmor w)) (FM.Mor-∘ (untranspose g) w)
untranspose-pre {V} {W} {X} g w =
  FamC.≈-sym
    (FamC.≈-trans (FamC.≈-sym (FR.untranspose-transpose (FM.Mor-∘ (untranspose g) w)))
      (FR.untranspose-cong
        (≈-trans (FR.transpose-natural₁ (untranspose g) w)
          (∘-cong₁ (FR.transpose-untranspose g)))))

-- The transposed form of a pure context morphism.
ctxη-pure : ∀ (Γ A : obj) {B : obj} (m : A ⇒ B) →
            FamC._≈_ (ctxη Γ A (m ∘ ℰP.p₂))
              (FM.Mor-∘ (untranspose (m ∘ realise-η-iso A .fwd)) (FamP.p₂ {x = η .fobj Γ} {y = η .fobj A}))
ctxη-pure Γ A {B} m =
  FamC.≈-trans (FR.untranspose-cong inner) (untranspose-pre (m ∘ realise-η-iso A .fwd) _)
  where
    inner : (m ∘ ℰP.p₂) ∘ (ℰP.prod-m (id _) (realise-η-iso A .fwd) ∘ prodη Γ (η .fobj A) .fwd)
            ≈ (m ∘ realise-η-iso A .fwd) ∘ realise .fmor (FamP.p₂ {x = η .fobj Γ} {y = η .fobj A})
    inner =
      begin
        (m ∘ ℰP.p₂) ∘ (ℰP.prod-m (id _) (realise-η-iso A .fwd) ∘ prodη Γ (η .fobj A) .fwd)
      ≈˘⟨ assoc _ _ _ ⟩
        ((m ∘ ℰP.p₂) ∘ ℰP.prod-m (id _) (realise-η-iso A .fwd)) ∘ prodη Γ (η .fobj A) .fwd
      ≈⟨ ∘-cong₁ (assoc _ _ _) ⟩
        (m ∘ (ℰP.p₂ ∘ ℰP.prod-m (id _) (realise-η-iso A .fwd))) ∘ prodη Γ (η .fobj A) .fwd
      ≈⟨ ∘-cong₁ (∘-cong₂ (ℰP.pair-p₂ _ _)) ⟩
        (m ∘ (realise-η-iso A .fwd ∘ ℰP.p₂)) ∘ prodη Γ (η .fobj A) .fwd
      ≈˘⟨ ∘-cong₁ (assoc _ _ _) ⟩
        ((m ∘ realise-η-iso A .fwd) ∘ ℰP.p₂) ∘ prodη Γ (η .fobj A) .fwd
      ≈⟨ assoc _ _ _ ⟩
        (m ∘ realise-η-iso A .fwd) ∘ (ℰP.p₂ ∘ prodη Γ (η .fobj A) .fwd)
      ≈⟨ ∘-cong₂ (prodη-p₂ Γ (η .fobj A)) ⟩
        (m ∘ realise-η-iso A .fwd) ∘ realise .fmor (FamP.p₂ {x = η .fobj Γ} {y = η .fobj A})
      ∎ where open ≈-Reasoning isEquiv

-- Extend a pure morphism to the bound entry, identities elsewhere.
pureExt : ∀ {n} (δ̂ : Fin n → FM.Obj) {Â B̂ : FM.Obj} → FM.Mor Â B̂ →
          ∀ i → FM.Mor (extend δ̂ Â i) (extend δ̂ B̂ i)
pureExt δ̂ m̂ Fin.zero    = m̂
pureExt δ̂ m̂ (Fin.suc i) = FamC.id _

module FamT = HasTerminal (FM.terminal ℰT)

-- The Fam(ℰ) strong action at a purely-precomposed family is the plain action
-- precomposed with the projection.
sf-pure : ∀ {n} (Q : Poly ℰ (suc n)) (δ̂₁ δ̂₂ : Fin (suc n) → FM.Obj) {Γ : obj}
          (ms : ∀ i → FM.Mor (δ̂₁ i) (δ̂₂ i)) →
          FamC._≈_
            (FM.Mor-∘ (FMu.fmor (Poly-map η Q) ms) (FamP.p₂ {x = η .fobj Γ} {y = FM.fobj FM.μObj (Poly-map η Q) δ̂₁}))
            (FMu.strong-fmor (Poly-map η Q) (λ i → FM.Mor-∘ (ms i) (FamP.p₂ {x = η .fobj Γ} {y = δ̂₁ i})))
sf-pure {n} Q δ̂₁ δ̂₂ {Γ} ms =
  FamC.≈-trans (FamC.assoc _ _ _)
    (FamC.≈-trans (FamC.∘-cong₂ sect-proj)
      (FamC.≈-trans (FMuI.strong-fmor-reindex (Poly-map η Q) FamT.to-terminal _)
        (FMuI.strong-fmor-cong (Poly-map η Q) pointwise)))
  where
    sect-proj : FamC._≈_
                  (FM.Mor-∘ (FamP.pair FamT.to-terminal (FamC.id _)) (FamP.p₂ {x = η .fobj Γ} {y = FM.fobj FM.μObj (Poly-map η Q) δ̂₁}))
                  (FamP.prod-m FamT.to-terminal (FamC.id _))
    sect-proj =
      FamC.≈-trans (FamP.pair-natural _ _ _)
        (FamP.pair-cong (FamT.to-terminal-unique _ _) FamC.≈-refl)

    pointwise : ∀ i → FamC._≈_
                  (FM.Mor-∘ (FM.Mor-∘ (ms i) (FamP.p₂ {x = FamT.witness} {y = δ̂₁ i})) (FamP.prod-m FamT.to-terminal (FamC.id _)))
                  (FM.Mor-∘ (ms i) (FamP.p₂ {x = η .fobj Γ} {y = δ̂₁ i}))
    pointwise i =
      FamC.≈-trans (FamC.assoc _ _ _)
        (FamC.∘-cong₂
          (FamC.≈-trans (FamP.pair-p₂ _ _) FamC.id-left))

-- The realised strong action on a pure morphism is a pure lift of the
-- realised plain Fam(ℰ) action.
Gmap-pure : ∀ {n} (Q : Poly ℰ (suc n)) (δ̂ : Fin n → FM.Obj) {Γ A B : obj} (m : A ⇒ B) →
            Gmap Q δ̂ {Γ} {A} {B} (m ∘ ℰP.p₂)
            ≈ realise .fmor (FMu.fmor (Poly-map η Q) (pureExt δ̂ (untranspose (m ∘ realise-η-iso A .fwd)))) ∘ ℰP.p₂
Gmap-pure {n} Q δ̂ {Γ} {A} {B} m =
  ≈-trans (fmorη-cong (FMuI.strong-fmor-cong (Poly-map η Q) pw))
    (≈-trans (fmorη-cong (FamC.≈-sym (sf-pure Q (extend δ̂ (η .fobj A)) (extend δ̂ (η .fobj B)) (pureExt δ̂ m̂))))
      (fmorη-pure Γ (FM.fobj FM.μObj (Poly-map η Q) (extend δ̂ (η .fobj A))) (FMu.fmor (Poly-map η Q) (pureExt δ̂ m̂))))
  where
    m̂ = untranspose (m ∘ realise-η-iso A .fwd)

    pw : ∀ i → FamC._≈_
           (FMu.strong-extend-mor (λ j → FamP.p₂) (ctxη Γ A (m ∘ ℰP.p₂)) i)
           (FM.Mor-∘ (pureExt δ̂ m̂ i) (FamP.p₂ {x = η .fobj Γ} {y = extend δ̂ (η .fobj A) i}))
    pw Fin.zero    = ctxη-pure Γ A m
    pw (Fin.suc i) = FamC.≈-sym FamC.id-left

-- Realising an untransposed morphism is the counit inverse followed by it.
realise-untranspose : ∀ {W : FM.Obj} {X : obj} (g : realise .fobj W ⇒ X) →
                      realise .fmor (untranspose {W = W} g) ≈ realise-η-iso X .bwd ∘ g
realise-untranspose {W} {X} g =
  iso-shuffle (realise-η-iso X) _ _
    (≈-trans (≈-sym (FR.transpose-realise {W = W} (untranspose {W = W} g))) (FR.transpose-untranspose {W = W} g))

-- Transport an isomorphism of realisations across the singleton embedding.
pureJ : ∀ {A B : obj} (I : Iso A B) → Iso (realise .fobj (η .fobj A)) (realise .fobj (η .fobj B))
pureJ {A} {B} I =
  Iso-trans (realise-η-iso A) (Iso-trans I (Iso-sym (realise-η-iso B)))

pureJ-fwd : ∀ {A B : obj} (I : Iso A B) →
            pureJ I .fwd ≈ realise .fmor (untranspose {W = η .fobj A} (I .fwd ∘ realise-η-iso A .fwd))
pureJ-fwd {A} {B} I =
  ≈-sym (≈-trans (realise-untranspose {W = η .fobj A} (I .fwd ∘ realise-η-iso A .fwd)) (≈-sym (assoc _ _ _)))
