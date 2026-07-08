{-# OPTIONS --prop --postfix-projections --safe #-}

-- Naturality of the μ-collapse in the strong action, closing the collapse
-- induction: every polynomial admits environment collapse.

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
import fam-mu-realisation.mu-iso

module fam-mu-realisation.natural {o m e} (os es : Level) {ℰ : Category o m e}
  (ℰC : ∀ (A : Setoid os (os ⊔ es)) → HasColimits (setoid→category A) ℰ)
  (ℰT : HasTerminal ℰ) (ℰP : HasProducts ℰ) (ℰE : HasExponentials ℰ ℰP)
  (ℰSC : HasStrongCoproducts ℰ ℰP)
  where

open fam-mu-realisation.mu-iso os es ℰC ℰT ℰP ℰE ℰSC public

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
