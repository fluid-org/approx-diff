{-# OPTIONS --prop --postfix-projections --safe #-}

-- The initial-algebra package carried by a realised μ-object, against an
-- assumed invariance family for its polynomial.

open import Level using (Level; _⊔_)
open import Data.Nat using (suc)
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
import fam-mu-realisation.invariance

module fam-mu-realisation.initial {o m e} (os es : Level) {ℰ : Category o m e}
  (ℰC : ∀ (A : Setoid os (os ⊔ es)) → HasColimits (setoid→category A) ℰ)
  (ℰT : HasTerminal ℰ) (ℰP : HasProducts ℰ) (ℰE : HasExponentials ℰ ℰP)
  (ℰSC : HasStrongCoproducts ℰ ℰP)
  where

open fam-mu-realisation.invariance os es ℰC ℰT ℰP ℰE ℰSC public

-- The initial-algebra package for a polynomial, against an assumed invariance
-- family and its naturality with respect to the strong action. The algebra
-- map realises the Fam(ℰ) algebra map and corrects the bound-variable entry
-- by invariance; the fold transposes the algebra to Fam(ℰ), folds there, and
-- transposes back; β follows from the Fam(ℰ) β law pushed through the
-- co-Kleisli functoriality of realisation.
module Initiality {n} (P : Poly ℰ (suc n)) (δ̂ : Fin n → FM.Obj)
    (CP : InvarianceAt P)
  where

  open InvarianceAt CP using () renaming (iso to Kiso'; natural to Knat)

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

    bF : ∀ {Γ A} → (ℰP.prod Γ (Greal P δ̂ A) ⇒ A) → FM.Mor (FamP.prod (η .fobj Γ) (F^ (η .fobj A))) (η .fobj A)
    bF {Γ} {A} a = untranspose (a ∘ prodη Γ (F^ (η .fobj A)) .fwd)

  inR : Greal P δ̂ (Creal P δ̂) ⇒ Creal P δ̂
  inR = realise .fmor (FMu.inMap P̂ δ̂) ∘
        Kiso' (extend δ̂ (η .fobj (Creal P δ̂))) (extend δ̂ μ̂) inIsos .fwd

  foldR : ∀ {Γ A} → (ℰP.prod Γ (Greal P δ̂ A) ⇒ A) → ℰP.prod Γ (Creal P δ̂) ⇒ A
  foldR {Γ} {A} a = transpose (FMu.⦅_⦆ {P = P̂} {δ = δ̂} (bF a)) ∘ prodη Γ μ̂ .bwd

  private
    -- The fold in counit-and-realisation form.
    foldR-real : ∀ {Γ A} (a : ℰP.prod Γ (Greal P δ̂ A) ⇒ A) →
                 foldR a ≈ realise-η-iso A .fwd ∘ fmorη Γ μ̂ (FMu.⦅_⦆ {P = P̂} {δ = δ̂} (bF a))
    foldR-real {Γ} {A} a =
      ≈-trans (∘-cong₁ (FR.transpose-realise _)) (assoc _ _ _)

    -- The context morphism Gmap acts with, for a morphism out of the carrier.
    h~ : ∀ {Γ A} → (ℰP.prod Γ (Creal P δ̂) ⇒ A) →
         FM.Mor (FamP.prod (η .fobj Γ) (η .fobj (Creal P δ̂))) (η .fobj A)
    h~ {Γ} {A} h = ctxη Γ (Creal P δ̂) h

    -- Compatibility of a transposed morphism with the counit component of the
    -- invariance, given its counit form.
    compat-zero : ∀ {Γ A} (u : FM.Mor (FamP.prod (η .fobj Γ) μ̂) (η .fobj A))
                  (h : ℰP.prod Γ (Creal P δ̂) ⇒ A) →
                  (realise-η-iso A .fwd ∘ fmorη Γ μ̂ u ≈ h) →
                  fmorη Γ μ̂ u ∘co (realise-η-iso (Creal P δ̂) .fwd ∘ ℰP.p₂)
                  ≈ fmorη Γ (η .fobj (Creal P δ̂)) (h~ h)
    compat-zero {Γ} {A} u h hyp =
      ≈-trans (iso-shuffle (realise-η-iso A) _ _ middle)
        (≈-trans (≈-sym (assoc _ _ _))
          (≈-trans (∘-cong₁ (realise-η-iso A .bwd∘fwd≈id)) id-left))
      where
        cA = realise-η-iso A .fwd
        cC = realise-η-iso (Creal P δ̂) .fwd

        left : cA ∘ (fmorη Γ μ̂ u ∘co (cC ∘ ℰP.p₂)) ≈ h ∘ ℰP.prod-m (id _) cC
        left =
          ≈-trans (≈-sym (assoc _ _ _))
            (≈-trans (∘-cong₁ hyp)
              (∘-cong₂ (ℰP.pair-cong (≈-sym id-left) ≈-refl)))

        right : cA ∘ fmorη Γ (η .fobj (Creal P δ̂)) (h~ h) ≈ h ∘ ℰP.prod-m (id _) cC
        right =
          ≈-trans (counit-fmorη Γ (η .fobj (Creal P δ̂)) _)
            (≈-trans (assoc _ _ _)
              (∘-cong₂ (≈-trans (assoc _ _ _) (≈-trans (∘-cong₂ (prodη Γ (η .fobj (Creal P δ̂)) .fwd∘bwd≈id)) id-right))))

        middle : cA ∘ (fmorη Γ μ̂ u ∘co (cC ∘ ℰP.p₂)) ≈ cA ∘ fmorη Γ (η .fobj (Creal P δ̂)) (h~ h)
        middle = ≈-trans left (≈-sym right)

    compat-suc : ∀ {Γ : obj} (i : Fin n) →
                 fmorη Γ (δ̂ i) (FamP.p₂ {x = η .fobj Γ} {y = δ̂ i}) ∘co (Iso-refl .fwd ∘ ℰP.p₂)
                 ≈ fmorη Γ (δ̂ i) (FamP.p₂ {x = η .fobj Γ} {y = δ̂ i})
    compat-suc {Γ} i =
      ≈-trans (∘-cong₂ (ℰP.pair-cong ≈-refl id-left))
        (≈-trans (∘-cong₂ pair-p₁p₂-id) id-right)

    -- The invariance-naturality square for a Fam(ℰ) morphism in counit form.
    key : ∀ {Γ A} (u : FM.Mor (FamP.prod (η .fobj Γ) μ̂) (η .fobj A))
          (h : ℰP.prod Γ (Creal P δ̂) ⇒ A) →
          (realise-η-iso A .fwd ∘ fmorη Γ μ̂ u ≈ h) →
          fmorη Γ (F^ μ̂) (FMu.strong-fmor P̂ (FMu.strong-extend-mor (λ i → FamP.p₂) u))
            ∘co (Kiso' (extend δ̂ (η .fobj (Creal P δ̂))) (extend δ̂ μ̂) inIsos .fwd ∘ ℰP.p₂)
          ≈ Gmap P δ̂ h
    key {Γ} {A} u h hyp =
      ≈-trans
        (Knat (extend δ̂ (η .fobj (Creal P δ̂))) (extend δ̂ μ̂) inIsos (λ i → Iso-refl)
          (FMu.strong-extend-mor (λ i → FamP.p₂) (h~ h))
          (FMu.strong-extend-mor (λ i → FamP.p₂) u)
          compats)
        (≈-trans (∘-cong₁ (invariance-refl P CP (extend δ̂ (η .fobj A)) (λ i → Iso-refl) (λ i → ≈-refl))) id-left)
      where
        compats : ∀ i → fmorη Γ (extend δ̂ μ̂ i) (FMu.strong-extend-mor (λ j → FamP.p₂) u i) ∘co (inIsos i .fwd ∘ ℰP.p₂)
                  ≈ Iso-refl .fwd ∘ fmorη Γ (extend δ̂ (η .fobj (Creal P δ̂)) i) (FMu.strong-extend-mor (λ j → FamP.p₂) (h~ h) i)
        compats Fin.zero    = ≈-trans (compat-zero u h hyp) (≈-sym id-left)
        compats (Fin.suc i) = ≈-trans (compat-suc i) (≈-sym id-left)

  foldR-β : ∀ {Γ A} (a : ℰP.prod Γ (Greal P δ̂ A) ⇒ A) →
            foldR a ∘co (inR ∘ ℰP.p₂) ≈ a ∘co Gmap P δ̂ (foldR a)
  foldR-β {Γ} {A} a =
    begin
      foldR a ∘co (inR ∘ ℰP.p₂)
    ≈⟨ CoK.∘-cong (foldR-real a) split ⟩
      (cA ∘ Φ⦅b⦆) ∘co ((Rin ∘ ℰP.p₂) ∘co (K ∘ ℰP.p₂))
    ≈˘⟨ CoK.assoc _ _ _ ⟩
      ((cA ∘ Φ⦅b⦆) ∘co (Rin ∘ ℰP.p₂)) ∘co (K ∘ ℰP.p₂)
    ≈⟨ CoK.∘-cong₁ step₁ ⟩
      (cA ∘ fmorη Γ (F^ μ̂) (FM.Mor-∘ ⦅b⦆ (pairη Γ (F^ μ̂) (FM.Mor-∘ (FMu.inMap P̂ δ̂) p₂F)))) ∘co (K ∘ ℰP.p₂)
    ≈⟨ CoK.∘-cong₁ (∘-cong₂ (fmorη-cong (FM.hasMuLaws .FM.HasMuLaws.⦅⦆-β (bF a)))) ⟩
      (cA ∘ fmorη Γ (F^ μ̂) (FM.Mor-∘ (bF a) (pairη Γ (F^ μ̂) sfB))) ∘co (K ∘ ℰP.p₂)
    ≈⟨ CoK.∘-cong₁ (∘-cong₂ (fmorη-∘co Γ (F^ μ̂) (bF a) sfB)) ⟩
      (cA ∘ (fmorη Γ (F^ (η .fobj A)) (bF a) ∘co fmorη Γ (F^ μ̂) sfB)) ∘co (K ∘ ℰP.p₂)
    ≈˘⟨ CoK.∘-cong₁ (assoc _ _ _) ⟩
      ((cA ∘ fmorη Γ (F^ (η .fobj A)) (bF a)) ∘co fmorη Γ (F^ μ̂) sfB) ∘co (K ∘ ℰP.p₂)
    ≈⟨ CoK.∘-cong₁ (CoK.∘-cong₁ (absorb (F^ (η .fobj A)) a)) ⟩
      (a ∘co fmorη Γ (F^ μ̂) sfB) ∘co (K ∘ ℰP.p₂)
    ≈⟨ CoK.assoc _ _ _ ⟩
      a ∘co (fmorη Γ (F^ μ̂) sfB ∘co (K ∘ ℰP.p₂))
    ≈⟨ CoK.∘-cong₂ (key ⦅b⦆ (foldR a) (≈-sym (foldR-real a))) ⟩
      a ∘co Gmap P δ̂ (foldR a)
    ∎
    where
      open ≈-Reasoning isEquiv

      ⦅b⦆ = FMu.⦅_⦆ {P = P̂} {δ = δ̂} (bF a)
      cA = realise-η-iso A .fwd
      Φ⦅b⦆ = fmorη Γ μ̂ ⦅b⦆
      Rin = realise .fmor (FMu.inMap P̂ δ̂)
      K = Kiso' (extend δ̂ (η .fobj (Creal P δ̂))) (extend δ̂ μ̂) inIsos .fwd
      p₂F = FamP.p₂ {x = η .fobj Γ} {y = F^ μ̂}
      sfB = FMu.strong-fmor P̂ (FMu.strong-extend-mor (λ i → FamP.p₂) ⦅b⦆)

      split : inR ∘ ℰP.p₂ ≈ (Rin ∘ ℰP.p₂) ∘co (K ∘ ℰP.p₂)
      split = ≈-sym (co-pure Rin K)

      step₁ : (cA ∘ Φ⦅b⦆) ∘co (Rin ∘ ℰP.p₂)
              ≈ cA ∘ fmorη Γ (F^ μ̂) (FM.Mor-∘ ⦅b⦆ (pairη Γ (F^ μ̂) (FM.Mor-∘ (FMu.inMap P̂ δ̂) p₂F)))
      step₁ =
        ≈-trans (assoc _ _ _)
          (∘-cong₂
            (≈-sym (≈-trans (fmorη-∘co Γ (F^ μ̂) ⦅b⦆ (FM.Mor-∘ (FMu.inMap P̂ δ̂) p₂F))
              (CoK.∘-cong₂ (fmorη-pure Γ (F^ μ̂) (FMu.inMap P̂ δ̂))))))

  foldR-η : ∀ {Γ A} (a : ℰP.prod Γ (Greal P δ̂ A) ⇒ A) (h : ℰP.prod Γ (Creal P δ̂) ⇒ A) →
            (h ∘co (inR ∘ ℰP.p₂) ≈ a ∘co Gmap P δ̂ h) → h ≈ foldR a
  foldR-η {Γ} {A} a h square =
    ≈-trans (≈-sym (≈-trans (assoc _ _ _) (≈-trans (∘-cong₂ (prodη Γ μ̂ .fwd∘bwd≈id)) id-right)))
      (≈-trans (∘-cong₁ (≈-sym (FR.transpose-untranspose _)))
        (∘-cong₁ (FR.transpose-cong famSquare')))
    where
      ĥ = untranspose (h ∘ prodη Γ μ̂ .fwd)
      cA = realise-η-iso A .fwd
      Rin = realise .fmor (FMu.inMap P̂ δ̂)
      Kiso = Kiso' (extend δ̂ (η .fobj (Creal P δ̂))) (extend δ̂ μ̂) inIsos
      p₂F = FamP.p₂ {x = η .fobj Γ} {y = F^ μ̂}
      sfH = FMu.strong-fmor P̂ (FMu.strong-extend-mor (λ i → FamP.p₂) ĥ)

      hypĥ : cA ∘ fmorη Γ μ̂ ĥ ≈ h
      hypĥ = absorb μ̂ h

      -- The given square, with the invariance cancelled and the algebra map bare.
      square' : h ∘co (Rin ∘ ℰP.p₂) ≈ a ∘co fmorη Γ (F^ μ̂) sfH
      square' =
        begin
          h ∘co (Rin ∘ ℰP.p₂)
        ≈˘⟨ co-iso-cancel Kiso (≈-trans (≈-trans (CoK.assoc _ _ _) (CoK.∘-cong₂ (co-pure {Γ = Γ} Rin (Kiso .fwd)))) square) ⟩
          (a ∘co Gmap P δ̂ h) ∘co (Kiso .bwd ∘ ℰP.p₂)
        ≈⟨ CoK.assoc _ _ _ ⟩
          a ∘co (Gmap P δ̂ h ∘co (Kiso .bwd ∘ ℰP.p₂))
        ≈⟨ CoK.∘-cong₂ (co-iso-cancel Kiso (key ĥ h hypĥ)) ⟩
          a ∘co fmorη Γ (F^ μ̂) sfH
        ∎ where open ≈-Reasoning isEquiv

      famSquare : FamC._≈_
                    (FM.Mor-∘ ĥ (pairη Γ (F^ μ̂) (FM.Mor-∘ (FMu.inMap P̂ δ̂) p₂F)))
                    (FM.Mor-∘ (bF a) (pairη Γ (F^ μ̂) sfH))
      famSquare = fmorη-inj Γ (F^ μ̂) _ _ imgEq
        where
          inner : cA ∘ (fmorη Γ μ̂ ĥ ∘co (Rin ∘ ℰP.p₂)) ≈ a ∘co fmorη Γ (F^ μ̂) sfH
          inner =
            ≈-trans (≈-sym (assoc _ _ _))
              (≈-trans (∘-cong₁ hypĥ) square')

          imgEq : fmorη Γ (F^ μ̂) (FM.Mor-∘ ĥ (pairη Γ (F^ μ̂) (FM.Mor-∘ (FMu.inMap P̂ δ̂) p₂F)))
                  ≈ fmorη Γ (F^ μ̂) (FM.Mor-∘ (bF a) (pairη Γ (F^ μ̂) sfH))
          imgEq =
            begin
              fmorη Γ (F^ μ̂) (FM.Mor-∘ ĥ (pairη Γ (F^ μ̂) (FM.Mor-∘ (FMu.inMap P̂ δ̂) p₂F)))
            ≈⟨ ≈-trans (fmorη-∘co Γ (F^ μ̂) ĥ _) (CoK.∘-cong₂ (fmorη-pure Γ (F^ μ̂) (FMu.inMap P̂ δ̂))) ⟩
              fmorη Γ μ̂ ĥ ∘co (Rin ∘ ℰP.p₂)
            ≈⟨ iso-shuffle (realise-η-iso A) _ _ inner ⟩
              realise-η-iso A .bwd ∘ (a ∘co fmorη Γ (F^ μ̂) sfH)
            ≈˘⟨ assoc _ _ _ ⟩
              (realise-η-iso A .bwd ∘ a) ∘co fmorη Γ (F^ μ̂) sfH
            ≈˘⟨ CoK.∘-cong₁ (iso-shuffle (realise-η-iso A) _ _ (absorb (F^ (η .fobj A)) a)) ⟩
              fmorη Γ (F^ (η .fobj A)) (bF a) ∘co fmorη Γ (F^ μ̂) sfH
            ≈˘⟨ fmorη-∘co Γ (F^ μ̂) (bF a) sfH ⟩
              fmorη Γ (F^ μ̂) (FM.Mor-∘ (bF a) (pairη Γ (F^ μ̂) sfH))
            ∎ where open ≈-Reasoning isEquiv

      famSquare' : FamC._≈_ ĥ (FMu.⦅_⦆ {P = P̂} {δ = δ̂} (bF a))
      famSquare' = FM.hasMuLaws .FM.HasMuLaws.⦅⦆-η (bF a) ĥ famSquare

  foldR-cong : ∀ {Γ A} {a₁ a₂ : ℰP.prod Γ (Greal P δ̂ A) ⇒ A} →
               a₁ ≈ a₂ → foldR a₁ ≈ foldR a₂
  foldR-cong {Γ} {A} {a₁} {a₂} e =
    ∘-cong₁ (FR.transpose-cong (FMuI.⦅⦆-cong P̂ δ̂ (FR.untranspose-cong (∘-cong₁ e))))


-- Plain-context conversions at the terminal object.

sect-p₂ : ∀ {X : obj} → ℰP.pair (ℰT'.to-terminal {X}) (id X) ∘ ℰP.p₂ {ℰT'.witness} {X} ≈ id _
sect-p₂ {X} =
  ≈-trans (ℰP.pair-natural _ _ _)
    (≈-trans (ℰP.pair-cong (ℰT'.to-terminal-unique _ _) id-left) pair-p₁p₂-id)

-- The plain form of a fold in the terminal context commutes with the algebra
-- map, against the plain form of the realised strong action.
plain-β : ∀ {n} (Q : Poly ℰ (suc n)) (δ̂ : Fin n → FM.Obj) (CQ : InvarianceAt Q) {D : obj}
          (c : ℰP.prod ℰT'.witness (Greal Q δ̂ D) ⇒ D) →
          (Initiality.foldR Q δ̂ CQ c ∘ ℰP.pair ℰT'.to-terminal (id _)) ∘ Initiality.inR Q δ̂ CQ
          ≈ c ∘ ℰP.pair ℰT'.to-terminal (Gmap Q δ̂ (Initiality.foldR Q δ̂ CQ c) ∘ ℰP.pair ℰT'.to-terminal (id _))
plain-β Q δ̂ CQ {D} c =
  ≈-trans left
    (≈-trans (≈-sym lhs-sect)
      (≈-trans (∘-cong₁ (M.foldR-β {Γ = ℰT'.witness} c)) rhs-sect))
  where
    module M = Initiality Q δ̂ CQ

    left : (M.foldR c ∘ ℰP.pair ℰT'.to-terminal (id _)) ∘ M.inR
           ≈ M.foldR c ∘ ℰP.pair ℰT'.to-terminal M.inR
    left =
      ≈-trans (assoc _ _ _)
        (≈-trans (∘-cong₂ (ℰP.pair-natural _ _ _))
          (∘-cong₂ (ℰP.pair-cong (ℰT'.to-terminal-unique _ _) id-left)))

    lhs-sect : (M.foldR c ∘co (M.inR ∘ ℰP.p₂)) ∘ ℰP.pair ℰT'.to-terminal (id _)
               ≈ M.foldR c ∘ ℰP.pair ℰT'.to-terminal M.inR
    lhs-sect =
      ≈-trans (assoc _ _ _)
        (≈-trans (∘-cong₂ (ℰP.pair-natural _ _ _))
          (∘-cong₂ (ℰP.pair-cong (ℰT'.to-terminal-unique _ _)
            (≈-trans (assoc _ _ _) (≈-trans (∘-cong₂ (ℰP.pair-p₂ _ _)) id-right)))))

    rhs-sect : (c ∘co Gmap Q δ̂ (M.foldR c)) ∘ ℰP.pair ℰT'.to-terminal (id _)
               ≈ c ∘ ℰP.pair ℰT'.to-terminal (Gmap Q δ̂ (M.foldR c) ∘ ℰP.pair ℰT'.to-terminal (id _))
    rhs-sect =
      ≈-trans (assoc _ _ _)
        (≈-trans (∘-cong₂ (ℰP.pair-natural _ _ _))
          (∘-cong₂ (ℰP.pair-cong (ℰT'.to-terminal-unique _ _) ≈-refl)))

-- The realised algebra map, recovered from the invariance form of inR.
inR-K : ∀ {n} (Q : Poly ℰ (suc n)) (δ̂ : Fin n → FM.Obj) (CQ : InvarianceAt Q) →
        realise .fmor (FMu.inMap (Poly-map η Q) δ̂)
        ≈ Initiality.inR Q δ̂ CQ ∘
           CQ .iso (extend δ̂ (η .fobj (Creal Q δ̂))) (extend δ̂ (FM.μObj (Poly-map η Q) δ̂)) (Initiality.inIsos Q δ̂ CQ) .bwd
inR-K Q δ̂ CQ =
  ≈-sym (≈-trans (assoc _ _ _)
    (≈-trans (∘-cong₂ (CQ .iso _ _ (Initiality.inIsos Q δ̂ CQ) .fwd∘bwd≈id)) id-right))
