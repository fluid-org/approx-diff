{-# OPTIONS --prop --postfix-projections --safe #-}

-- Naturality of the μ-invariance in the strong action, closing the invariance
-- induction: every polynomial admits environment invariance.

open import Level using (Level; _⊔_)
open import Data.Nat using (ℕ; suc)
import Data.Fin as Fin
open Fin using (Fin)
open import prop-setoid using (Setoid; module ≈-Reasoning)
open import categories
  using (Category; setoid→category; HasTerminal; HasProducts; HasExponentials;
         HasStrongCoproducts; HasCoproducts; strong-coproducts→coproducts; coKleisli-prod)
open import functor using (Functor; HasColimits; _∘F_)
open import polynomial-functor using (Poly; extend; Poly-map)
import fam
import fam-mu-types
import functor
import fam-realisation
import fam-mu-realisation.context
import fam-functor
import polynomial-functor
import fam-mu-realisation.mu-iso

module fam-mu-realisation.natural {o m e} (os es : Level) {ℰ : Category o m e}
  (ℰC : ∀ (A : Setoid os (os ⊔ es)) → HasColimits (setoid→category A) ℰ)
  (ℰT : HasTerminal ℰ) (ℰP : HasProducts ℰ) (ℰE : HasExponentials ℰ ℰP)
  (ℰSC : HasStrongCoproducts ℰ ℰP) (ℰL : functor.StrongFunctor ℰP)
  (LC : fam-mu-realisation.context.LiftCoherence os es ℰC ℰT ℰP ℰE ℰSC ℰL)
  where

open fam-mu-realisation.mu-iso os es ℰC ℰT ℰP ℰE ℰSC ℰL LC public

-- The realised strong μ-action is the fold of the realised algebra, corrected
-- by the invariance at the bound-variable entry.
module SμfFold {n} (Q : Poly ℰ (suc n)) (CQ : InvarianceAt Q) {Γ : obj}
    (δ̂ ε̂ : Fin n → FM.Obj)
    (gs : ∀ i → FM.Mor (FamP.prod (η .fobj Γ) (δ̂ i)) (ε̂ i))
  where

  private
    Q̂ = Poly-map η Q
    module Mδ = Initiality Q δ̂ CQ

    sμf : FM.Mor (FamP.prod (η .fobj Γ) (FM.μObj Q̂ δ̂)) (FM.μObj Q̂ ε̂)
    sμf = FMu.strong-μ-fmor Q̂ gs

    alg : FM.Mor (FamP.prod (η .fobj Γ) (FM.fobj FM.μObj Q̂ (extend δ̂ (FM.μObj Q̂ ε̂)))) (FM.μObj Q̂ ε̂)
    alg = FM.Mor-∘ (FMu.inMap Q̂ ε̂) (FMu.strong-fmor Q̂ (FMu.strong-extend-mor gs FamP.p₂))

  KKisos : ∀ i → Iso (realise .fobj (extend δ̂ (η .fobj (Creal Q ε̂)) i))
                     (realise .fobj (extend δ̂ (FM.μObj Q̂ ε̂) i))
  KKisos Fin.zero    = realise-η-iso (Creal Q ε̂)
  KKisos (Fin.suc i) = Iso-refl

  KKε : Iso (realise .fobj (FM.fobj FM.μObj Q̂ (extend δ̂ (η .fobj (Creal Q ε̂)))))
            (realise .fobj (FM.fobj FM.μObj Q̂ (extend δ̂ (FM.μObj Q̂ ε̂))))
  KKε = CQ .iso (extend δ̂ (η .fobj (Creal Q ε̂))) (extend δ̂ (FM.μObj Q̂ ε̂)) KKisos

  aStar : ℰP.prod Γ (Greal Q δ̂ (Creal Q ε̂)) ⇒ Creal Q ε̂
  aStar = fmorη Γ (FM.fobj FM.μObj Q̂ (extend δ̂ (FM.μObj Q̂ ε̂))) alg ∘co (KKε .fwd ∘ ℰP.p₂)

  A' : ℰP.prod Γ (Creal Q δ̂) ⇒ Creal Q ε̂
  A' = fmorη Γ (FM.μObj (Poly-map η Q) δ̂) (FMu.strong-μ-fmor (Poly-map η Q) gs)

  sμf-square : A' ∘co (Mδ.inR ∘ ℰP.p₂) ≈ aStar ∘co Gmap Q δ̂ A'
  sμf-square =
    begin
      A' ∘co (Mδ.inR ∘ ℰP.p₂)
    ≈˘⟨ CoK.∘-cong₂ (co-pure _ _) ⟩
      A' ∘co ((realise .fmor (FMu.inMap Q̂ δ̂) ∘ ℰP.p₂) ∘co (CQ .iso (extend δ̂ (η .fobj (Creal Q δ̂))) (extend δ̂ (FM.μObj Q̂ δ̂)) Mδ.inIsos .fwd ∘ ℰP.p₂))
    ≈˘⟨ CoK.assoc _ _ _ ⟩
      (A' ∘co (realise .fmor (FMu.inMap Q̂ δ̂) ∘ ℰP.p₂)) ∘co (CQ .iso (extend δ̂ (η .fobj (Creal Q δ̂))) (extend δ̂ (FM.μObj Q̂ δ̂)) Mδ.inIsos .fwd ∘ ℰP.p₂)
    ≈⟨ CoK.∘-cong₁ step-β ⟩
      (fmorη Γ (FM.fobj FM.μObj Q̂ (extend δ̂ (FM.μObj Q̂ ε̂))) alg ∘co fmorη Γ (FM.fobj FM.μObj Q̂ (extend δ̂ (FM.μObj Q̂ δ̂))) (FMu.strong-fmor Q̂ (FMu.strong-extend-mor (λ i → FamP.p₂) sμf))) ∘co (CQ .iso (extend δ̂ (η .fobj (Creal Q δ̂))) (extend δ̂ (FM.μObj Q̂ δ̂)) Mδ.inIsos .fwd ∘ ℰP.p₂)
    ≈⟨ CoK.assoc _ _ _ ⟩
      fmorη Γ (FM.fobj FM.μObj Q̂ (extend δ̂ (FM.μObj Q̂ ε̂))) alg ∘co (fmorη Γ (FM.fobj FM.μObj Q̂ (extend δ̂ (FM.μObj Q̂ δ̂))) (FMu.strong-fmor Q̂ (FMu.strong-extend-mor (λ i → FamP.p₂) sμf)) ∘co (CQ .iso (extend δ̂ (η .fobj (Creal Q δ̂))) (extend δ̂ (FM.μObj Q̂ δ̂)) Mδ.inIsos .fwd ∘ ℰP.p₂))
    ≈⟨ CoK.∘-cong₂ inner-nat ⟩
      fmorη Γ (FM.fobj FM.μObj Q̂ (extend δ̂ (FM.μObj Q̂ ε̂))) alg ∘co (KKε .fwd ∘ Gmap Q δ̂ A')
    ≈˘⟨ CoK.∘-cong₂ (≈-trans (assoc _ _ _) (∘-cong₂ (ℰP.pair-p₂ _ _))) ⟩
      fmorη Γ (FM.fobj FM.μObj Q̂ (extend δ̂ (FM.μObj Q̂ ε̂))) alg ∘co ((KKε .fwd ∘ ℰP.p₂) ∘co Gmap Q δ̂ A')
    ≈˘⟨ CoK.assoc _ _ _ ⟩
      aStar ∘co Gmap Q δ̂ A'
    ∎
    where
      open ≈-Reasoning isEquiv

      step-β : A' ∘co (realise .fmor (FMu.inMap Q̂ δ̂) ∘ ℰP.p₂)
               ≈ fmorη Γ (FM.fobj FM.μObj Q̂ (extend δ̂ (FM.μObj Q̂ ε̂))) alg ∘co fmorη Γ (FM.fobj FM.μObj Q̂ (extend δ̂ (FM.μObj Q̂ δ̂))) (FMu.strong-fmor Q̂ (FMu.strong-extend-mor (λ i → FamP.p₂) sμf))
      step-β =
        ≈-trans (CoK.∘-cong₂ (≈-sym (fmorη-pure Γ (FM.fobj FM.μObj Q̂ (extend δ̂ (FM.μObj Q̂ δ̂))) (FMu.inMap Q̂ δ̂))))
          (≈-trans (≈-sym (fmorη-∘co Γ (FM.fobj FM.μObj Q̂ (extend δ̂ (FM.μObj Q̂ δ̂))) sμf _))
            (≈-trans (fmorη-cong (FM.hasMuLaws .FM.HasMuLaws.⦅⦆-β {P = Q̂} {δ = δ̂} _))
              (fmorη-∘co Γ (FM.fobj FM.μObj Q̂ (extend δ̂ (FM.μObj Q̂ δ̂))) alg _)))

      inner-nat : fmorη Γ (FM.fobj FM.μObj Q̂ (extend δ̂ (FM.μObj Q̂ δ̂))) (FMu.strong-fmor Q̂ (FMu.strong-extend-mor (λ i → FamP.p₂) sμf))
                    ∘co (CQ .iso (extend δ̂ (η .fobj (Creal Q δ̂))) (extend δ̂ (FM.μObj Q̂ δ̂)) Mδ.inIsos .fwd ∘ ℰP.p₂)
                  ≈ KKε .fwd ∘ Gmap Q δ̂ A'
      inner-nat =
        CQ .natural (extend δ̂ (η .fobj (Creal Q δ̂))) (extend δ̂ (FM.μObj Q̂ δ̂)) Mδ.inIsos KKisos
          (FMu.strong-extend-mor (λ i → FamP.p₂) (ctxη Γ (Creal Q δ̂) A'))
          (FMu.strong-extend-mor (λ i → FamP.p₂) sμf)
          compats
        where
          compats : ∀ i → fmorη Γ (extend δ̂ (FM.μObj Q̂ δ̂) i) (FMu.strong-extend-mor (λ j → FamP.p₂) sμf i) ∘co (Mδ.inIsos i .fwd ∘ ℰP.p₂)
                    ≈ KKisos i .fwd ∘ fmorη Γ (extend δ̂ (η .fobj (Creal Q δ̂)) i) (FMu.strong-extend-mor (λ j → FamP.p₂) (ctxη Γ (Creal Q δ̂) A') i)
          compats Fin.zero    = fmorη-ctxη-square Γ (FM.μObj Q̂ δ̂) (FM.μObj Q̂ ε̂) sμf
          compats (Fin.suc i) = sq-refl _

  -- The characterisation.
  sμf-fold : fmorη Γ (FM.μObj Q̂ δ̂) (FMu.strong-μ-fmor Q̂ gs) ≈ Mδ.foldR aStar
  sμf-fold = Mδ.foldR-η aStar A' sμf-square

-- The naturality of the μ-invariance: the last field of the invariance interface
-- at μ. Established by fold uniqueness, with the invariance paths identified
-- through composition coherence and extensionality.
module MuNat {n} (Q : Poly ℰ (suc n)) (CQ : InvarianceAt Q) {Γ : obj}
    (δ̂₁ δ̂₂ ε̂₁ ε̂₂ : Fin n → FM.Obj)
    (isosδ : ∀ i → Iso (realise .fobj (δ̂₁ i)) (realise .fobj (δ̂₂ i)))
    (isosε : ∀ i → Iso (realise .fobj (ε̂₁ i)) (realise .fobj (ε̂₂ i)))
    (gs₁ : ∀ i → FM.Mor (FamP.prod (η .fobj Γ) (δ̂₁ i)) (ε̂₁ i))
    (gs₂ : ∀ i → FM.Mor (FamP.prod (η .fobj Γ) (δ̂₂ i)) (ε̂₂ i))
    (sqs : ∀ i → fmorη Γ (δ̂₂ i) (gs₂ i) ∘co (isosδ i .fwd ∘ ℰP.p₂)
                 ≈ isosε i .fwd ∘ fmorη Γ (δ̂₁ i) (gs₁ i))
  where

  private
    Q̂ = Poly-map η Q

    module Mδ₁ = Initiality Q δ̂₁ CQ
    module Mδ₂ = Initiality Q δ̂₂ CQ
    module Mε₁ = Initiality Q ε̂₁ CQ
    module Mε₂ = Initiality Q ε̂₂ CQ
    module Sδ₁ = SμfFold Q CQ δ̂₁ ε̂₁ gs₁
    module Sδ₂ = SμfFold Q CQ δ̂₂ ε̂₂ gs₂
    module MCδ = MuInvariance Q CQ δ̂₁ δ̂₂ isosδ
    module MCε = MuInvariance Q CQ ε̂₁ ε̂₂ isosε

    muδ = MCδ.mu-invariance
    muε = MCε.mu-invariance
    C₁ε = Creal Q ε̂₁
    C₂ε = Creal Q ε̂₂

    f̂ε : FM.Mor (η .fobj C₁ε) (η .fobj C₂ε)
    f̂ε = untranspose {W = η .fobj C₁ε} (muε .fwd ∘ realise-η-iso C₁ε .fwd)

    NFε₁ = FMu.fmor Q̂ (pureExt ε̂₁ f̂ε)

    Kε₁ = CQ .iso (extend ε̂₁ (η .fobj C₁ε)) (extend ε̂₁ (FM.μObj Q̂ ε̂₁)) Mε₁.inIsos
    Kε₂ = CQ .iso (extend ε̂₂ (η .fobj C₂ε)) (extend ε̂₂ (FM.μObj Q̂ ε̂₂)) Mε₂.inIsos
    Mεμ = CQ .iso (extend ε̂₁ (FM.μObj Q̂ ε̂₁)) (extend ε̂₂ (FM.μObj Q̂ ε̂₂)) (mixed isosε muε)

    Pc-isos = mixed {δ̂₁ = ε̂₁} {δ̂₂ = ε̂₁} (λ i → Iso-refl) {Ŷ₁ = η .fobj C₁ε} {Ŷ₂ = η .fobj C₂ε} (pureJ muε)

    Pc-real : CQ .iso (extend ε̂₁ (η .fobj C₁ε)) (extend ε̂₁ (η .fobj C₂ε)) Pc-isos .fwd
              ≈ realise .fmor NFε₁
    Pc-real = pure-invariance Q CQ _ _ (pureExt ε̂₁ f̂ε) Pc-isos hyps
      where
        hyps : ∀ i → Pc-isos i .fwd ≈ realise .fmor (pureExt ε̂₁ f̂ε i)
        hyps Fin.zero    = pureJ-fwd muε
        hyps (Fin.suc i) = ≈-sym (realise .fmor-id)

    counit-invariance-square : Kε₂ .fwd ∘ (MCε.GI C₂ε .fwd ∘ realise .fmor NFε₁)
                             ≈ Mεμ .fwd ∘ Kε₁ .fwd
    counit-invariance-square =
      ≈-trans (∘-cong₂ (∘-cong₂ (≈-sym Pc-real)))
        (≈-trans (∘-cong₂ (≈-sym (CQ .comp _ _ _ Pc-isos (MCε.extIsos C₂ε))))
          (invariance-path-eq Q CQ (extend ε̂₁ (η .fobj C₁ε)) (extend ε̂₂ (η .fobj C₂ε)) (extend ε̂₁ (FM.μObj Q̂ ε̂₁)) (extend ε̂₂ (FM.μObj Q̂ ε̂₂)) (λ i → Iso-trans (Pc-isos i) (MCε.extIsos C₂ε i)) Mε₂.inIsos Mε₁.inIsos (mixed isosε muε) pointwise))
      where
        pointwise : ∀ i → Iso-trans (Iso-trans (Pc-isos i) (MCε.extIsos C₂ε i)) (Mε₂.inIsos i) .fwd
                          ≈ Iso-trans (Mε₁.inIsos i) (mixed isosε muε i) .fwd
        pointwise Fin.zero =
          ≈-trans (∘-cong₂ id-left)
            (≈-trans (≈-sym (assoc _ _ _))
              (≈-trans (∘-cong₁ (≈-sym (assoc _ _ _)))
                (∘-cong₁ (≈-trans (∘-cong₁ (realise-η-iso C₂ε .fwd∘bwd≈id)) id-left))))
        pointwise (Fin.suc i) = id-left

    -- Abbreviations for the δ̂-side invariance paths.
    KK₁ = Sδ₁.KKε
    KK₂ = Sδ₂.KKε
    Mδμ = CQ .iso (extend δ̂₁ (FM.μObj Q̂ ε̂₁)) (extend δ̂₂ (FM.μObj Q̂ ε̂₂)) (mixed isosδ muε)

    NF₂ = FMu.fmor Q̂ (pureExt δ̂₂ f̂ε)

    Pc2-isos = mixed {δ̂₁ = δ̂₂} {δ̂₂ = δ̂₂} (λ i → Iso-refl) {Ŷ₁ = η .fobj C₁ε} {Ŷ₂ = η .fobj C₂ε} (pureJ muε)

    Pc2-real : CQ .iso (extend δ̂₂ (η .fobj C₁ε)) (extend δ̂₂ (η .fobj C₂ε)) Pc2-isos .fwd
               ≈ realise .fmor NF₂
    Pc2-real = pure-invariance Q CQ _ _ (pureExt δ̂₂ f̂ε) Pc2-isos hyps
      where
        hyps : ∀ i → Pc2-isos i .fwd ≈ realise .fmor (pureExt δ̂₂ f̂ε i)
        hyps Fin.zero    = pureJ-fwd muε
        hyps (Fin.suc i) = ≈-sym (realise .fmor-id)

    -- The δ̂-side invariance paths from the fold algebra's environment agree.
    env-invariance-square : Mδμ .fwd ∘ KK₁ .fwd
                          ≈ (KK₂ .fwd ∘ realise .fmor NF₂) ∘ MCδ.GI C₁ε .fwd
    env-invariance-square =
      ≈-trans (invariance-path-eq Q CQ (extend δ̂₁ (η .fobj C₁ε)) (extend δ̂₁ (FM.μObj Q̂ ε̂₁)) (extend δ̂₂ (η .fobj C₁ε)) (extend δ̂₂ (FM.μObj Q̂ ε̂₂)) Sδ₁.KKisos (mixed isosδ muε) (MCδ.extIsos C₁ε) (λ i → Iso-trans (Pc2-isos i) (Sδ₂.KKisos i)) pointwise)
        (∘-cong₁ (≈-trans (CQ .comp _ _ _ Pc2-isos Sδ₂.KKisos) (∘-cong₂ Pc2-real)))
      where
        pointwise : ∀ i → Iso-trans (Sδ₁.KKisos i) (mixed isosδ muε i) .fwd
                          ≈ Iso-trans (MCδ.extIsos C₁ε i) (Iso-trans (Pc2-isos i) (Sδ₂.KKisos i)) .fwd
        pointwise Fin.zero =
          ≈-sym (≈-trans id-right
            (≈-trans (≈-sym (assoc _ _ _))
              (≈-trans (∘-cong₁ (≈-sym (assoc _ _ _)))
                (∘-cong₁ (≈-trans (∘-cong₁ (realise-η-iso C₂ε .fwd∘bwd≈id)) id-left)))))
        pointwise (Fin.suc i) =
          ≈-trans id-right (≈-sym (≈-trans (∘-cong₁ id-left) id-left))

    -- Remaining abbreviations for the fold-square assembly.
    sfp₁ : FM.Mor (FamP.prod (η .fobj Γ) (FM.fobj FM.μObj Q̂ (extend δ̂₁ (FM.μObj Q̂ ε̂₁))))
                  (FM.fobj FM.μObj Q̂ (extend ε̂₁ (FM.μObj Q̂ ε̂₁)))
    sfp₁ = FMu.strong-fmor Q̂ (FMu.strong-extend-mor gs₁ FamP.p₂)

    sfp₂ : FM.Mor (FamP.prod (η .fobj Γ) (FM.fobj FM.μObj Q̂ (extend δ̂₂ (FM.μObj Q̂ ε̂₂))))
                  (FM.fobj FM.μObj Q̂ (extend ε̂₂ (FM.μObj Q̂ ε̂₂)))
    sfp₂ = FMu.strong-fmor Q̂ (FMu.strong-extend-mor gs₂ FamP.p₂)

    b̂δ : FM.Mor (η .fobj (Creal Q δ̂₂)) (η .fobj (Creal Q δ̂₁))
    b̂δ = untranspose {W = η .fobj (Creal Q δ̂₂)} (muδ .bwd ∘ realise-η-iso (Creal Q δ̂₂) .fwd)

    NB₂ = FMu.fmor Q̂ (pureExt δ̂₂ b̂δ)

    A₁ = Sδ₁.A'
    A₂ = Sδ₂.A'

    B' : ℰP.prod Γ (Creal Q δ̂₂) ⇒ Creal Q ε̂₂
    B' = (muε .fwd ∘ A₁) ∘co (muδ .bwd ∘ ℰP.p₂)

    -- The backward form of the counit invariance square.
    counit-invariance-bwd : (MCε.GI C₂ε .fwd ∘ realise .fmor NFε₁) ∘ Kε₁ .bwd
                          ≈ Kε₂ .bwd ∘ Mεμ .fwd
    counit-invariance-bwd =
      begin
        (MCε.GI C₂ε .fwd ∘ realise .fmor NFε₁) ∘ Kε₁ .bwd
      ≈˘⟨ id-left ⟩
        id _ ∘ ((MCε.GI C₂ε .fwd ∘ realise .fmor NFε₁) ∘ Kε₁ .bwd)
      ≈˘⟨ ∘-cong₁ (Kε₂ .bwd∘fwd≈id) ⟩
        (Kε₂ .bwd ∘ Kε₂ .fwd) ∘ ((MCε.GI C₂ε .fwd ∘ realise .fmor NFε₁) ∘ Kε₁ .bwd)
      ≈⟨ assoc _ _ _ ⟩
        Kε₂ .bwd ∘ (Kε₂ .fwd ∘ ((MCε.GI C₂ε .fwd ∘ realise .fmor NFε₁) ∘ Kε₁ .bwd))
      ≈˘⟨ ∘-cong₂ (assoc _ _ _) ⟩
        Kε₂ .bwd ∘ ((Kε₂ .fwd ∘ (MCε.GI C₂ε .fwd ∘ realise .fmor NFε₁)) ∘ Kε₁ .bwd)
      ≈⟨ ∘-cong₂ (∘-cong₁ counit-invariance-square) ⟩
        Kε₂ .bwd ∘ ((Mεμ .fwd ∘ Kε₁ .fwd) ∘ Kε₁ .bwd)
      ≈⟨ ∘-cong₂ (≈-trans (assoc _ _ _) (≈-trans (∘-cong₂ (Kε₁ .fwd∘bwd≈id)) id-right)) ⟩
        Kε₂ .bwd ∘ Mεμ .fwd
      ∎ where open ≈-Reasoning isEquiv

    -- The μ-invariance against the realised algebra map, in invariance form.
    head-eq : muε .fwd ∘ realise .fmor (FMu.inMap Q̂ ε̂₁)
              ≈ Mε₂.inR ∘ (Kε₂ .bwd ∘ Mεμ .fwd)
    head-eq =
      ≈-trans (∘-cong₂ (inR-K Q ε̂₁ CQ))
        (≈-trans (≈-sym (assoc _ _ _))
          (≈-trans (∘-cong₁ (mu-invariance-fwd-in Q CQ ε̂₁ ε̂₂ isosε))
            (≈-trans (assoc _ _ _) (∘-cong₂ counit-invariance-bwd))))

    -- Gmap of the composite, decomposed into pure lifts around the crossing.
    gmapB' : Gmap Q δ̂₂ B' ≈ ((realise .fmor NF₂ ∘ ℰP.p₂) ∘co Gmap Q δ̂₂ A₁) ∘co (realise .fmor NB₂ ∘ ℰP.p₂)
    gmapB' =
      ≈-trans (Gmap-cong Q δ̂₂ (CoK.∘-cong₁ split))
        (≈-trans (Gmap-∘co Q δ̂₂ ((muε .fwd ∘ ℰP.p₂) ∘co A₁) (muδ .bwd ∘ ℰP.p₂))
          (CoK.∘-cong
            (≈-trans (Gmap-∘co Q δ̂₂ (muε .fwd ∘ ℰP.p₂) A₁)
              (CoK.∘-cong₁ (Gmap-pure Q δ̂₂ (muε .fwd))))
            (Gmap-pure Q δ̂₂ (muδ .bwd))))
      where
        split : muε .fwd ∘ A₁ ≈ (muε .fwd ∘ ℰP.p₂) ∘co A₁
        split = ≈-sym (≈-trans (assoc _ _ _) (∘-cong₂ (ℰP.pair-p₂ _ _)))

    -- The composite tails agree, over any head.
    bracket : ((MCδ.GI C₁ε .fwd ∘ ℰP.p₂) ∘co Gmap Q δ̂₁ A₁) ∘co ((MCδ.GI (Creal Q δ̂₁) .bwd ∘ realise .fmor NB₂) ∘ ℰP.p₂)
              ≈ Gmap Q δ̂₂ A₁ ∘co (realise .fmor NB₂ ∘ ℰP.p₂)
    bracket =
      begin
        ((MCδ.GI C₁ε .fwd ∘ ℰP.p₂) ∘co Gmap Q δ̂₁ A₁) ∘co ((MCδ.GI (Creal Q δ̂₁) .bwd ∘ realise .fmor NB₂) ∘ ℰP.p₂)
      ≈⟨ CoK.∘-cong₁ (≈-trans (assoc _ _ _) (∘-cong₂ (ℰP.pair-p₂ _ _))) ⟩
        (MCδ.GI C₁ε .fwd ∘ Gmap Q δ̂₁ A₁) ∘co ((MCδ.GI (Creal Q δ̂₁) .bwd ∘ realise .fmor NB₂) ∘ ℰP.p₂)
      ≈˘⟨ CoK.∘-cong₁ (MCδ.crossΓ A₁) ⟩
        (Gmap Q δ̂₂ A₁ ∘co (MCδ.GI (Creal Q δ̂₁) .fwd ∘ ℰP.p₂)) ∘co ((MCδ.GI (Creal Q δ̂₁) .bwd ∘ realise .fmor NB₂) ∘ ℰP.p₂)
      ≈⟨ CoK.assoc _ _ _ ⟩
        Gmap Q δ̂₂ A₁ ∘co ((MCδ.GI (Creal Q δ̂₁) .fwd ∘ ℰP.p₂) ∘co ((MCδ.GI (Creal Q δ̂₁) .bwd ∘ realise .fmor NB₂) ∘ ℰP.p₂))
      ≈⟨ CoK.∘-cong₂ (co-pure _ _) ⟩
        Gmap Q δ̂₂ A₁ ∘co ((MCδ.GI (Creal Q δ̂₁) .fwd ∘ (MCδ.GI (Creal Q δ̂₁) .bwd ∘ realise .fmor NB₂)) ∘ ℰP.p₂)
      ≈⟨ CoK.∘-cong₂ (∘-cong₁ (≈-trans (≈-sym (assoc _ _ _)) (≈-trans (∘-cong₁ (MCδ.GI (Creal Q δ̂₁) .fwd∘bwd≈id)) id-left))) ⟩
        Gmap Q δ̂₂ A₁ ∘co (realise .fmor NB₂ ∘ ℰP.p₂)
      ∎ where open ≈-Reasoning isEquiv

    -- The δ̂₁-side tail transforms into the δ̂₂-side tail (named factors,
    -- normalised to right-nested form on both sides).
    tail-eq : ∀ {Z : obj} (X : ℰP.prod Γ (realise .fobj (FM.fobj FM.μObj Q̂ (extend δ̂₁ (FM.μObj Q̂ ε̂₁)))) ⇒ Z) →
              ((X ∘co (KK₁ .fwd ∘ ℰP.p₂)) ∘co Gmap Q δ̂₁ A₁) ∘co ((MCδ.GI (Creal Q δ̂₁) .bwd ∘ realise .fmor NB₂) ∘ ℰP.p₂)
              ≈ ((X ∘co (Mδμ .bwd ∘ ℰP.p₂)) ∘co (KK₂ .fwd ∘ ℰP.p₂)) ∘co (((realise .fmor NF₂ ∘ ℰP.p₂) ∘co Gmap Q δ̂₂ A₁) ∘co (realise .fmor NB₂ ∘ ℰP.p₂))
    tail-eq {Z} X = ≈-trans lhs-norm (≈-sym rhs-norm)
      where
        k₁ = KK₁ .fwd ∘ ℰP.p₂
        g₁ = Gmap Q δ̂₁ A₁
        r  = (MCδ.GI (Creal Q δ̂₁) .bwd ∘ realise .fmor NB₂) ∘ ℰP.p₂
        mδ = Mδμ .bwd ∘ ℰP.p₂
        k₂ = KK₂ .fwd ∘ ℰP.p₂
        nf = realise .fmor NF₂ ∘ ℰP.p₂
        gi = MCδ.GI C₁ε .fwd ∘ ℰP.p₂
        g₂ = Gmap Q δ̂₂ A₁
        nb = realise .fmor NB₂ ∘ ℰP.p₂


        k₁-split : k₁ ≈ mδ ∘co (k₂ ∘co (nf ∘co gi))
        k₁-split =
          begin
            KK₁ .fwd ∘ ℰP.p₂
          ≈⟨ ∘-cong₁ (iso-shuffle Mδμ _ _ env-invariance-square) ⟩
            (Mδμ .bwd ∘ ((KK₂ .fwd ∘ realise .fmor NF₂) ∘ MCδ.GI C₁ε .fwd)) ∘ ℰP.p₂
          ≈˘⟨ co-pure _ _ ⟩
            mδ ∘co (((KK₂ .fwd ∘ realise .fmor NF₂) ∘ MCδ.GI C₁ε .fwd) ∘ ℰP.p₂)
          ≈˘⟨ CoK.∘-cong₂ (co-pure _ _) ⟩
            mδ ∘co (((KK₂ .fwd ∘ realise .fmor NF₂) ∘ ℰP.p₂) ∘co gi)
          ≈˘⟨ CoK.∘-cong₂ (CoK.∘-cong₁ (co-pure _ _)) ⟩
            mδ ∘co ((k₂ ∘co nf) ∘co gi)
          ≈⟨ CoK.∘-cong₂ (CoK.assoc _ _ _) ⟩
            mδ ∘co (k₂ ∘co (nf ∘co gi))
          ∎ where open ≈-Reasoning isEquiv

        lhs-norm : ((X ∘co k₁) ∘co g₁) ∘co r ≈ X ∘co (mδ ∘co (k₂ ∘co (nf ∘co (g₂ ∘co nb))))
        lhs-norm =
          begin
            ((X ∘co k₁) ∘co g₁) ∘co r
          ≈⟨ CoK.assoc _ _ _ ⟩
            (X ∘co k₁) ∘co (g₁ ∘co r)
          ≈⟨ CoK.assoc _ _ _ ⟩
            X ∘co (k₁ ∘co (g₁ ∘co r))
          ≈⟨ CoK.∘-cong₂ (CoK.∘-cong₁ k₁-split) ⟩
            X ∘co ((mδ ∘co (k₂ ∘co (nf ∘co gi))) ∘co (g₁ ∘co r))
          ≈⟨ CoK.∘-cong₂ (CoK.assoc _ _ _) ⟩
            X ∘co (mδ ∘co ((k₂ ∘co (nf ∘co gi)) ∘co (g₁ ∘co r)))
          ≈⟨ CoK.∘-cong₂ (CoK.∘-cong₂ (CoK.assoc _ _ _)) ⟩
            X ∘co (mδ ∘co (k₂ ∘co ((nf ∘co gi) ∘co (g₁ ∘co r))))
          ≈⟨ CoK.∘-cong₂ (CoK.∘-cong₂ (CoK.∘-cong₂ (CoK.assoc _ _ _))) ⟩
            X ∘co (mδ ∘co (k₂ ∘co (nf ∘co (gi ∘co (g₁ ∘co r)))))
          ≈⟨ CoK.∘-cong₂ (CoK.∘-cong₂ (CoK.∘-cong₂ (CoK.∘-cong₂ (≈-trans (≈-sym (CoK.assoc _ _ _)) bracket)))) ⟩
            X ∘co (mδ ∘co (k₂ ∘co (nf ∘co (g₂ ∘co nb))))
          ∎ where open ≈-Reasoning isEquiv

        rhs-norm : ((X ∘co mδ) ∘co k₂) ∘co ((nf ∘co g₂) ∘co nb) ≈ X ∘co (mδ ∘co (k₂ ∘co (nf ∘co (g₂ ∘co nb))))
        rhs-norm =
          begin
            ((X ∘co mδ) ∘co k₂) ∘co ((nf ∘co g₂) ∘co nb)
          ≈⟨ CoK.assoc _ _ _ ⟩
            (X ∘co mδ) ∘co (k₂ ∘co ((nf ∘co g₂) ∘co nb))
          ≈⟨ CoK.assoc _ _ _ ⟩
            X ∘co (mδ ∘co (k₂ ∘co ((nf ∘co g₂) ∘co nb)))
          ≈⟨ CoK.∘-cong₂ (CoK.∘-cong₂ (CoK.∘-cong₂ (CoK.assoc _ _ _))) ⟩
            X ∘co (mδ ∘co (k₂ ∘co (nf ∘co (g₂ ∘co nb))))
          ∎ where open ≈-Reasoning isEquiv

    HEAD : ℰP.prod Γ (realise .fobj (FM.fobj FM.μObj Q̂ (extend δ̂₁ (FM.μObj Q̂ ε̂₁)))) ⇒ Creal Q ε̂₂
    HEAD = (Mε₂.inR ∘ (Kε₂ .bwd ∘ Mεμ .fwd)) ∘ fmorη Γ _ sfp₁


    -- The δ̂₂-side fold algebra, in composite form.
    head₂-eq : fmorη Γ (FM.fobj FM.μObj Q̂ (extend δ̂₂ (FM.μObj Q̂ ε̂₂)))
                 (FM.Mor-∘ (FMu.inMap Q̂ ε̂₂) sfp₂)
               ≈ HEAD ∘co (Mδμ .bwd ∘ ℰP.p₂)
    head₂-eq =
      ≈-trans (fmorη-post Γ _ (FMu.inMap Q̂ ε̂₂) sfp₂)
        (≈-trans (∘-cong₁ (inR-K Q ε̂₂ CQ))
          (≈-trans (∘-cong₂ (≈-sym (co-iso-cancel Mδμ (cross-mixed Q CQ isosδ isosε {Ŷ₁ = FM.μObj Q̂ ε̂₁} {Ŷ₂ = FM.μObj Q̂ ε̂₂} muε gs₁ gs₂ sqs))))
            (≈-trans (≈-sym (assoc _ _ _)) (CoK.∘-cong₁ (≈-trans (≈-sym (assoc _ _ _)) (∘-cong₁ (assoc _ _ _)))))))

    -- The δ̂₁-side fold algebra, pushed under the ε̂-invariance.
    head₁-eq : muε .fwd ∘ Sδ₁.aStar ≈ HEAD ∘co (KK₁ .fwd ∘ ℰP.p₂)
    head₁-eq =
      ≈-trans (≈-sym (assoc _ _ _)) (CoK.∘-cong₁ head-inner)
      where
        head-inner : muε .fwd ∘ fmorη Γ (FM.fobj FM.μObj Q̂ (extend δ̂₁ (FM.μObj Q̂ ε̂₁))) (FM.Mor-∘ (FMu.inMap Q̂ ε̂₁) sfp₁) ≈ HEAD
        head-inner =
          ≈-trans (∘-cong₂ (fmorη-post Γ _ (FMu.inMap Q̂ ε̂₁) sfp₁))
            (≈-trans (≈-sym (assoc _ _ _)) (∘-cong₁ head-eq))

    -- The fold square for the composite candidate.
    B-square : B' ∘co (Mδ₂.inR ∘ ℰP.p₂) ≈ Sδ₂.aStar ∘co Gmap Q δ̂₂ B'
    B-square = ≈-trans lhs-eq (≈-sym (CoK.∘-cong (CoK.∘-cong₁ head₂-eq) gmapB'))
      where
        step-fold : (muε .fwd ∘ A₁) ∘co (Mδ₁.inR ∘ ℰP.p₂)
                    ≈ (HEAD ∘co (KK₁ .fwd ∘ ℰP.p₂)) ∘co Gmap Q δ̂₁ A₁
        step-fold =
          ≈-trans (assoc _ _ _)
            (≈-trans (∘-cong₂ Sδ₁.sμf-square)
              (≈-trans (≈-sym (assoc _ _ _)) (CoK.∘-cong₁ head₁-eq)))

        lhs-eq : B' ∘co (Mδ₂.inR ∘ ℰP.p₂)
                 ≈ ((HEAD ∘co (Mδμ .bwd ∘ ℰP.p₂)) ∘co (KK₂ .fwd ∘ ℰP.p₂)) ∘co (((realise .fmor NF₂ ∘ ℰP.p₂) ∘co Gmap Q δ̂₂ A₁) ∘co (realise .fmor NB₂ ∘ ℰP.p₂))
        lhs-eq =
          begin
            B' ∘co (Mδ₂.inR ∘ ℰP.p₂)
          ≈⟨ CoK.assoc _ _ _ ⟩
            (muε .fwd ∘ A₁) ∘co ((muδ .bwd ∘ ℰP.p₂) ∘co (Mδ₂.inR ∘ ℰP.p₂))
          ≈⟨ CoK.∘-cong₂ (co-pure _ _) ⟩
            (muε .fwd ∘ A₁) ∘co ((muδ .bwd ∘ Mδ₂.inR) ∘ ℰP.p₂)
          ≈⟨ CoK.∘-cong₂ (∘-cong₁ (mu-invariance-bwd-in Q CQ δ̂₁ δ̂₂ isosδ)) ⟩
            (muε .fwd ∘ A₁) ∘co ((Mδ₁.inR ∘ (MCδ.GI (Creal Q δ̂₁) .bwd ∘ realise .fmor NB₂)) ∘ ℰP.p₂)
          ≈˘⟨ CoK.∘-cong₂ (co-pure _ _) ⟩
            (muε .fwd ∘ A₁) ∘co ((Mδ₁.inR ∘ ℰP.p₂) ∘co ((MCδ.GI (Creal Q δ̂₁) .bwd ∘ realise .fmor NB₂) ∘ ℰP.p₂))
          ≈˘⟨ CoK.assoc _ _ _ ⟩
            ((muε .fwd ∘ A₁) ∘co (Mδ₁.inR ∘ ℰP.p₂)) ∘co ((MCδ.GI (Creal Q δ̂₁) .bwd ∘ realise .fmor NB₂) ∘ ℰP.p₂)
          ≈⟨ CoK.∘-cong₁ step-fold ⟩
            ((HEAD ∘co (KK₁ .fwd ∘ ℰP.p₂)) ∘co Gmap Q δ̂₁ A₁) ∘co ((MCδ.GI (Creal Q δ̂₁) .bwd ∘ realise .fmor NB₂) ∘ ℰP.p₂)
          ≈⟨ tail-eq HEAD ⟩
            ((HEAD ∘co (Mδμ .bwd ∘ ℰP.p₂)) ∘co (KK₂ .fwd ∘ ℰP.p₂)) ∘co (((realise .fmor NF₂ ∘ ℰP.p₂) ∘co Gmap Q δ̂₂ A₁) ∘co (realise .fmor NB₂ ∘ ℰP.p₂))
          ∎ where open ≈-Reasoning isEquiv

  -- The naturality square of the μ-invariance.
  mu-natural : Sδ₂.A' ∘co (muδ .fwd ∘ ℰP.p₂) ≈ muε .fwd ∘ Sδ₁.A'
  mu-natural =
    co-iso-move muδ (≈-trans Sδ₂.sμf-fold (≈-sym (Mδ₂.foldR-η Sδ₂.aStar B' B-square)))

-- The μ case of the invariance interface.
invariance-mu : ∀ {n} {P : Poly ℰ (suc n)} → InvarianceAt P → InvarianceAt (μ P)
invariance-mu {n} {P} CP .iso = MuInvariance.mu-invariance P CP
invariance-mu {n} {P} CP .natural {Γ} {ε̂₁} {ε̂₂} δ̂₁ δ̂₂ isosδ isosε gs₁ gs₂ sqs =
  MuNat.mu-natural P CP δ̂₁ δ̂₂ ε̂₁ ε̂₂ isosδ isosε gs₁ gs₂ sqs
invariance-mu {n} {P} CP .comp δ̂₁ δ̂₂ δ̂₃ isos₁₂ isos₂₃ = mu-invariance-comp P CP δ̂₁ δ̂₂ δ̂₃ isos₁₂ isos₂₃

-- Every polynomial admits environment invariance.
invarianceAt : ∀ {n} (P : Poly ℰ n) → InvarianceAt P
invarianceAt (const A) = invariance-const A
invarianceAt (var i)   = invariance-var i
invarianceAt (P + Q)   = invariance-sum (invarianceAt P) (invarianceAt Q)
invarianceAt (P × Q)   = invariance-prod (invarianceAt P) (invarianceAt Q)
invarianceAt (μ P)     = invariance-mu (invarianceAt P)
invarianceAt (lift P)  = invariance-lift (invarianceAt P)
