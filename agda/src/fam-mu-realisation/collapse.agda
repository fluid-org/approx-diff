{-# OPTIONS --prop --postfix-projections --safe #-}

-- The collapse interface: realisation of the polynomial interpretation is
-- invariant under replacing environment entries by families with isomorphic
-- realisations, naturally in the strong action, compatibly with identities
-- and composition. Cases: constants, variables, sums and products.

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
import fam-mu-realisation.pure

module fam-mu-realisation.collapse {o m e} (os es : Level) {ℰ : Category o m e}
  (ℰC : ∀ (A : Setoid os (os ⊔ es)) → HasColimits (setoid→category A) ℰ)
  (ℰT : HasTerminal ℰ) (ℰP : HasProducts ℰ) (ℰE : HasExponentials ℰ ℰP)
  (ℰSC : HasStrongCoproducts ℰ ℰP)
  where

open fam-mu-realisation.pure os es ℰC ℰT ℰP ℰE ℰSC public

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
