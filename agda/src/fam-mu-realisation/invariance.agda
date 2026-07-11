{-# OPTIONS --prop --postfix-projections --safe #-}

-- The invariance interface: realisation of the polynomial interpretation is
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
open import polynomial-functor using (Poly; extend; Poly-map)
import fam
import fam-mu-types
import fam-realisation
import polynomial-functor
import fam-mu-realisation.pure

module fam-mu-realisation.invariance {o m e} (os es : Level) {ℰ : Category o m e}
  (ℰC : ∀ (A : Setoid os (os ⊔ es)) → HasColimits (setoid→category A) ℰ)
  (ℰT : HasTerminal ℰ) (ℰP : HasProducts ℰ) (ℰE : HasExponentials ℰ ℰP)
  (ℰSC : HasStrongCoproducts ℰ ℰP)
  where

open fam-mu-realisation.pure os es ℰC ℰT ℰP ℰE ℰSC public

-- The invariance interface for a polynomial: realisation of its application is
-- invariant under replacing environment entries by families with isomorphic
-- realisations, naturally in the strong action, and trivially so at identical
-- environments.
record InvarianceAt {n} (P : Poly ℰ n) : Set (o ⊔ m ⊔ e ⊔ Level.suc os ⊔ Level.suc es) where
  field
    iso : (δ̂₁ δ̂₂ : Fin n → FM.Obj) →
          (∀ i → Iso (realise .fobj (δ̂₁ i)) (realise .fobj (δ̂₂ i))) →
          Iso (realise .fobj (FM.fobj FM.μObj (Poly-map η P) δ̂₁))
              (realise .fobj (FM.fobj FM.μObj (Poly-map η P) δ̂₂))
    natural : ∀ {Γ : obj} {ε̂₁ ε̂₂ : Fin n → FM.Obj}
              (δ̂₁ δ̂₂ : Fin n → FM.Obj)
              (isosδ : ∀ i → Iso (realise .fobj (δ̂₁ i)) (realise .fobj (δ̂₂ i)))
              (isosε : ∀ i → Iso (realise .fobj (ε̂₁ i)) (realise .fobj (ε̂₂ i)))
              (gs₁ : ∀ i → FM.Mor (FamP.prod (η .fobj Γ) (δ̂₁ i)) (ε̂₁ i))
              (gs₂ : ∀ i → FM.Mor (FamP.prod (η .fobj Γ) (δ̂₂ i)) (ε̂₂ i)) →
              (∀ i → fmorη Γ (δ̂₂ i) (gs₂ i) ∘co (isosδ i .fwd ∘ ℰP.p₂)
                     ≈ isosε i .fwd ∘ fmorη Γ (δ̂₁ i) (gs₁ i)) →
              fmorη Γ (FM.fobj FM.μObj (Poly-map η P) δ̂₂) (FMu.strong-fmor (Poly-map η P) gs₂)
                ∘co (iso δ̂₁ δ̂₂ isosδ .fwd ∘ ℰP.p₂)
              ≈ iso _ _ isosε .fwd ∘ fmorη Γ (FM.fobj FM.μObj (Poly-map η P) δ̂₁) (FMu.strong-fmor (Poly-map η P) gs₁)
    comp : ∀ (δ̂₁ δ̂₂ δ̂₃ : Fin n → FM.Obj)
           (isos₁₂ : ∀ i → Iso (realise .fobj (δ̂₁ i)) (realise .fobj (δ̂₂ i)))
           (isos₂₃ : ∀ i → Iso (realise .fobj (δ̂₂ i)) (realise .fobj (δ̂₃ i))) →
           iso δ̂₁ δ̂₃ (λ i → Iso-trans (isos₁₂ i) (isos₂₃ i)) .fwd
           ≈ iso δ̂₂ δ̂₃ isos₂₃ .fwd ∘ iso δ̂₁ δ̂₂ isos₁₂ .fwd

open InvarianceAt public

-- The invariance interface at constants and variables.
invariance-const : ∀ {n} (A : obj) → InvarianceAt {n} (const A)
invariance-const A .iso δ̂₁ δ̂₂ isos = Iso-refl
invariance-const A .natural δ̂₁ δ̂₂ isosδ isosε gs₁ gs₂ sqs = sq-refl _
invariance-const A .comp δ̂₁ δ̂₂ δ̂₃ isos₁₂ isos₂₃ = ≈-sym id-left

invariance-var : ∀ {n} (i : Fin n) → InvarianceAt {n} (var i)
invariance-var i .iso δ̂₁ δ̂₂ isos = isos i
invariance-var i .natural δ̂₁ δ̂₂ isosδ isosε gs₁ gs₂ sqs = sqs i
invariance-var i .comp δ̂₁ δ̂₂ δ̂₃ isos₁₂ isos₂₃ = ≈-refl

-- Invariance isomorphisms at pointwise-equal isomorphism families are equal.
invariance-ext : ∀ {n} (Q : Poly ℰ n) (CQ' : InvarianceAt Q) (δ̂₁ δ̂₂ : Fin n → FM.Obj)
               (isos isos' : ∀ i → Iso (realise .fobj (δ̂₁ i)) (realise .fobj (δ̂₂ i))) →
               (∀ i → isos i .fwd ≈ isos' i .fwd) →
               CQ' .iso δ̂₁ δ̂₂ isos .fwd ≈ CQ' .iso δ̂₁ δ̂₂ isos' .fwd
invariance-ext {n} Q CQ' δ̂₁ δ̂₂ isos isos' hyps =
  p₂-cancel (≈-trans (≈-sym strip₁) (≈-trans (CQ' .natural δ̂₁ δ̂₂ isos isos' (λ i → FamP.p₂ {x = η .fobj ℰT'.witness} {y = δ̂₁ i}) (λ i → FamP.p₂ {x = η .fobj ℰT'.witness} {y = δ̂₂ i}) sqs) strip₂))
  where
    strip₁ : fmorη ℰT'.witness (FM.fobj FM.μObj (Poly-map η Q) δ̂₂) (FMu.strong-fmor (Poly-map η Q) (λ i → FamP.p₂ {x = η .fobj ℰT'.witness} {y = δ̂₂ i}))
              ∘co (CQ' .iso δ̂₁ δ̂₂ isos .fwd ∘ ℰP.p₂)
             ≈ CQ' .iso δ̂₁ δ̂₂ isos .fwd ∘ ℰP.p₂
    strip₁ =
      ≈-trans (CoK.∘-cong₁ (≈-trans (fmorη-cong (FMuI.strong-fmor-p₂ (Poly-map η Q))) (fmorη-p₂ ℰT'.witness _)))
        (CoK.id-left {Γ = ℰT'.witness})

    strip₂ : CQ' .iso δ̂₁ δ̂₂ isos' .fwd
              ∘ fmorη ℰT'.witness (FM.fobj FM.μObj (Poly-map η Q) δ̂₁) (FMu.strong-fmor (Poly-map η Q) (λ i → FamP.p₂ {x = η .fobj ℰT'.witness} {y = δ̂₁ i}))
             ≈ CQ' .iso δ̂₁ δ̂₂ isos' .fwd ∘ ℰP.p₂
    strip₂ =
      ∘-cong₂ (≈-trans (fmorη-cong (FMuI.strong-fmor-p₂ (Poly-map η Q))) (fmorη-p₂ ℰT'.witness _))

    sqs : ∀ i → fmorη ℰT'.witness (δ̂₂ i) (FamP.p₂ {x = η .fobj ℰT'.witness} {y = δ̂₂ i}) ∘co (isos i .fwd ∘ ℰP.p₂)
                ≈ isos' i .fwd ∘ fmorη ℰT'.witness (δ̂₁ i) (FamP.p₂ {x = η .fobj ℰT'.witness} {y = δ̂₁ i})
    sqs i =
      ≈-trans (CoK.∘-cong₁ (fmorη-p₂ ℰT'.witness (δ̂₂ i)))
        (≈-trans (CoK.id-left {Γ = ℰT'.witness})
          (≈-trans (∘-cong₁ (hyps i))
            (≈-sym (∘-cong₂ (fmorη-p₂ ℰT'.witness (δ̂₁ i))))))

-- Invariance at pointwise-identity isomorphisms is the identity: by
-- extensionality it is the invariance at reflexivity families, which is
-- idempotent by composition coherence, and an idempotent isomorphism is the
-- identity.
invariance-refl : ∀ {n} (Q : Poly ℰ n) (CQ' : InvarianceAt Q) (δ̂ : Fin n → FM.Obj)
                (isos : ∀ i → Iso (realise .fobj (δ̂ i)) (realise .fobj (δ̂ i))) →
                (∀ i → isos i .fwd ≈ id _) →
                CQ' .iso δ̂ δ̂ isos .fwd ≈ id _
invariance-refl Q CQ' δ̂ isos hyps =
  ≈-trans (invariance-ext Q CQ' δ̂ δ̂ isos (λ i → Iso-refl) hyps)
    (≈-trans (≈-sym id-right)
      (≈-trans (∘-cong₂ (≈-sym (CQ' .iso δ̂ δ̂ (λ i → Iso-refl) .fwd∘bwd≈id)))
        (≈-trans (≈-sym (assoc _ _ _))
          (≈-trans (∘-cong₁ idem) (CQ' .iso δ̂ δ̂ (λ i → Iso-refl) .fwd∘bwd≈id)))))
  where
    idem : CQ' .iso δ̂ δ̂ (λ i → Iso-refl) .fwd ∘ CQ' .iso δ̂ δ̂ (λ i → Iso-refl) .fwd
           ≈ CQ' .iso δ̂ δ̂ (λ i → Iso-refl) .fwd
    idem =
      ≈-trans (≈-sym (CQ' .comp δ̂ δ̂ δ̂ (λ i → Iso-refl) (λ i → Iso-refl)))
        (invariance-ext Q CQ' δ̂ δ̂ (λ i → Iso-trans Iso-refl Iso-refl) (λ i → Iso-refl) (λ i → id-left))

-- Two composite invariance paths with pointwise-equal composite agreements
-- coincide.
invariance-path-eq : ∀ {n} (Q : Poly ℰ n) (CQ' : InvarianceAt Q)
                   (δ̂₁ δ̂₂ δ̂₂' δ̂₃ : Fin n → FM.Obj)
                   (as₁ : ∀ i → Iso (realise .fobj (δ̂₁ i)) (realise .fobj (δ̂₂ i)))
                   (as₂ : ∀ i → Iso (realise .fobj (δ̂₂ i)) (realise .fobj (δ̂₃ i)))
                   (bs₁ : ∀ i → Iso (realise .fobj (δ̂₁ i)) (realise .fobj (δ̂₂' i)))
                   (bs₂ : ∀ i → Iso (realise .fobj (δ̂₂' i)) (realise .fobj (δ̂₃ i))) →
                   (∀ i → Iso-trans (as₁ i) (as₂ i) .fwd ≈ Iso-trans (bs₁ i) (bs₂ i) .fwd) →
                   CQ' .iso _ _ as₂ .fwd ∘ CQ' .iso _ _ as₁ .fwd
                   ≈ CQ' .iso _ _ bs₂ .fwd ∘ CQ' .iso _ _ bs₁ .fwd
invariance-path-eq Q CQ' δ̂₁ δ̂₂ δ̂₂' δ̂₃ as₁ as₂ bs₁ bs₂ pw =
  ≈-trans (≈-sym (CQ' .comp δ̂₁ δ̂₂ δ̂₃ as₁ as₂))
    (≈-trans (invariance-ext Q CQ' δ̂₁ δ̂₃ _ _ pw) (CQ' .comp δ̂₁ δ̂₂' δ̂₃ bs₁ bs₂))

-- Coproduct machinery for the sum case of the invariance.
ℰCP = strong-coproducts→coproducts ℰT ℰSC
module ℰCPm = HasCoproducts ℰCP
module ℰSCm = HasStrongCoproducts ℰSC
module FSC = HasStrongCoproducts FM.strongCoproducts
module FCP = HasCoproducts FM.coproducts

K⊕ : ∀ (X̂ Ŷ : FM.Obj) → Iso (realise .fobj (FCP.coprod X̂ Ŷ))
                            (ℰCPm.coprod (realise .fobj X̂) (realise .fobj Ŷ))
K⊕ X̂ Ŷ = FR.realise-coproducts-iso ℰCP X̂ Ŷ

K⊕-in₁ : ∀ (X̂ Ŷ : FM.Obj) → K⊕ X̂ Ŷ .bwd ∘ ℰSCm.in₁ ≈ realise .fmor FCP.in₁
K⊕-in₁ X̂ Ŷ = ℰCPm.copair-in₁ _ _

K⊕-in₂ : ∀ (X̂ Ŷ : FM.Obj) → K⊕ X̂ Ŷ .bwd ∘ ℰSCm.in₂ ≈ realise .fmor FCP.in₂
K⊕-in₂ X̂ Ŷ = ℰCPm.copair-in₂ _ _

K⊕-in₁' : ∀ (X̂ Ŷ : FM.Obj) → K⊕ X̂ Ŷ .fwd ∘ realise .fmor FCP.in₁ ≈ ℰSCm.in₁
K⊕-in₁' X̂ Ŷ =
  ≈-trans (∘-cong₂ (≈-sym (K⊕-in₁ X̂ Ŷ)))
    (≈-trans (≈-sym (assoc _ _ _)) (≈-trans (∘-cong₁ (K⊕ X̂ Ŷ .fwd∘bwd≈id)) id-left))

K⊕-in₂' : ∀ (X̂ Ŷ : FM.Obj) → K⊕ X̂ Ŷ .fwd ∘ realise .fmor FCP.in₂ ≈ ℰSCm.in₂
K⊕-in₂' X̂ Ŷ =
  ≈-trans (∘-cong₂ (≈-sym (K⊕-in₂ X̂ Ŷ)))
    (≈-trans (≈-sym (assoc _ _ _)) (≈-trans (∘-cong₁ (K⊕ X̂ Ŷ .fwd∘bwd≈id)) id-left))

-- Strong copair against a coproduct of morphisms, in context.
scopair-coprod-m : ∀ {Γ X₁ X₂ Y₁ Y₂ Z : obj}
                   (a : ℰP.prod Γ Y₁ ⇒ Z) (b : ℰP.prod Γ Y₂ ⇒ Z)
                   (f : X₁ ⇒ Y₁) (g : X₂ ⇒ Y₂) →
                   ℰSCm.copair a b ∘co (ℰCPm.coprod-m f g ∘ ℰP.p₂)
                   ≈ ℰSCm.copair (a ∘co (f ∘ ℰP.p₂)) (b ∘co (g ∘ ℰP.p₂))
scopair-coprod-m {Γ} a b f g =
  ≈-trans (≈-sym (ℰSCm.copair-ext _)) (ℰSCm.copair-cong c₁ c₂)
  where
    c₁ : (ℰSCm.copair a b ∘co (ℰCPm.coprod-m f g ∘ ℰP.p₂)) ∘ ℰP.pair ℰP.p₁ (ℰSCm.in₁ ∘ ℰP.p₂)
         ≈ a ∘co (f ∘ ℰP.p₂)
    c₁ =
      begin
        (ℰSCm.copair a b ∘co (ℰCPm.coprod-m f g ∘ ℰP.p₂)) ∘co (ℰSCm.in₁ ∘ ℰP.p₂)
      ≈⟨ CoK.assoc _ _ _ ⟩
        ℰSCm.copair a b ∘co ((ℰCPm.coprod-m f g ∘ ℰP.p₂) ∘co (ℰSCm.in₁ ∘ ℰP.p₂))
      ≈⟨ CoK.∘-cong₂ (co-pure _ _) ⟩
        ℰSCm.copair a b ∘co ((ℰCPm.coprod-m f g ∘ ℰSCm.in₁) ∘ ℰP.p₂)
      ≈⟨ CoK.∘-cong₂ (∘-cong₁ (ℰCPm.copair-in₁ _ _)) ⟩
        ℰSCm.copair a b ∘co ((ℰSCm.in₁ ∘ f) ∘ ℰP.p₂)
      ≈˘⟨ CoK.∘-cong₂ (co-pure _ _) ⟩
        ℰSCm.copair a b ∘co ((ℰSCm.in₁ ∘ ℰP.p₂) ∘co (f ∘ ℰP.p₂))
      ≈˘⟨ CoK.assoc _ _ _ ⟩
        (ℰSCm.copair a b ∘co (ℰSCm.in₁ ∘ ℰP.p₂)) ∘co (f ∘ ℰP.p₂)
      ≈⟨ CoK.∘-cong₁ (ℰSCm.copair-in₁ a b) ⟩
        a ∘co (f ∘ ℰP.p₂)
      ∎ where open ≈-Reasoning isEquiv

    c₂ : (ℰSCm.copair a b ∘co (ℰCPm.coprod-m f g ∘ ℰP.p₂)) ∘ ℰP.pair ℰP.p₁ (ℰSCm.in₂ ∘ ℰP.p₂)
         ≈ b ∘co (g ∘ ℰP.p₂)
    c₂ =
      begin
        (ℰSCm.copair a b ∘co (ℰCPm.coprod-m f g ∘ ℰP.p₂)) ∘co (ℰSCm.in₂ ∘ ℰP.p₂)
      ≈⟨ CoK.assoc _ _ _ ⟩
        ℰSCm.copair a b ∘co ((ℰCPm.coprod-m f g ∘ ℰP.p₂) ∘co (ℰSCm.in₂ ∘ ℰP.p₂))
      ≈⟨ CoK.∘-cong₂ (co-pure _ _) ⟩
        ℰSCm.copair a b ∘co ((ℰCPm.coprod-m f g ∘ ℰSCm.in₂) ∘ ℰP.p₂)
      ≈⟨ CoK.∘-cong₂ (∘-cong₁ (ℰCPm.copair-in₂ _ _)) ⟩
        ℰSCm.copair a b ∘co ((ℰSCm.in₂ ∘ g) ∘ ℰP.p₂)
      ≈˘⟨ CoK.∘-cong₂ (co-pure _ _) ⟩
        ℰSCm.copair a b ∘co ((ℰSCm.in₂ ∘ ℰP.p₂) ∘co (g ∘ ℰP.p₂))
      ≈˘⟨ CoK.assoc _ _ _ ⟩
        (ℰSCm.copair a b ∘co (ℰSCm.in₂ ∘ ℰP.p₂)) ∘co (g ∘ ℰP.p₂)
      ≈⟨ CoK.∘-cong₁ (ℰSCm.copair-in₂ a b) ⟩
        b ∘co (g ∘ ℰP.p₂)
      ∎ where open ≈-Reasoning isEquiv

-- Realisation in context sends the strong copair to the strong copair, across
-- the coproduct comparison iso.
fmorη-scopair : ∀ (Γ : obj) (X̂ Ŷ : FM.Obj) {Ẑ : FM.Obj}
                (u : FM.Mor (FamP.prod (η .fobj Γ) X̂) Ẑ)
                (v : FM.Mor (FamP.prod (η .fobj Γ) Ŷ) Ẑ) →
                fmorη Γ (FCP.coprod X̂ Ŷ) (FSC.copair u v) ∘co (K⊕ X̂ Ŷ .bwd ∘ ℰP.p₂)
                ≈ ℰSCm.copair (fmorη Γ X̂ u) (fmorη Γ Ŷ v)
fmorη-scopair Γ X̂ Ŷ {Ẑ} u v =
  ≈-trans (≈-sym (ℰSCm.copair-ext _)) (ℰSCm.copair-cong c₁ c₂)
  where
    c₁ : (fmorη Γ (FCP.coprod X̂ Ŷ) (FSC.copair u v) ∘co (K⊕ X̂ Ŷ .bwd ∘ ℰP.p₂)) ∘ ℰP.pair ℰP.p₁ (ℰSCm.in₁ ∘ ℰP.p₂)
         ≈ fmorη Γ X̂ u
    c₁ =
      begin
        (fmorη Γ (FCP.coprod X̂ Ŷ) (FSC.copair u v) ∘co (K⊕ X̂ Ŷ .bwd ∘ ℰP.p₂)) ∘co (ℰSCm.in₁ ∘ ℰP.p₂)
      ≈⟨ CoK.assoc _ _ _ ⟩
        fmorη Γ (FCP.coprod X̂ Ŷ) (FSC.copair u v) ∘co ((K⊕ X̂ Ŷ .bwd ∘ ℰP.p₂) ∘co (ℰSCm.in₁ ∘ ℰP.p₂))
      ≈⟨ CoK.∘-cong₂ (co-pure _ _) ⟩
        fmorη Γ (FCP.coprod X̂ Ŷ) (FSC.copair u v) ∘co ((K⊕ X̂ Ŷ .bwd ∘ ℰSCm.in₁) ∘ ℰP.p₂)
      ≈⟨ CoK.∘-cong₂ (∘-cong₁ (K⊕-in₁ X̂ Ŷ)) ⟩
        fmorη Γ (FCP.coprod X̂ Ŷ) (FSC.copair u v) ∘co (realise .fmor FCP.in₁ ∘ ℰP.p₂)
      ≈˘⟨ CoK.∘-cong₂ (fmorη-pure Γ X̂ FCP.in₁) ⟩
        fmorη Γ (FCP.coprod X̂ Ŷ) (FSC.copair u v) ∘co fmorη Γ X̂ (FM.Mor-∘ FCP.in₁ (FamP.p₂ {x = η .fobj Γ} {y = X̂}))
      ≈˘⟨ fmorη-∘co Γ X̂ (FSC.copair u v) _ ⟩
        fmorη Γ X̂ (FM.Mor-∘ (FSC.copair u v) (pairη Γ X̂ (FM.Mor-∘ FCP.in₁ (FamP.p₂ {x = η .fobj Γ} {y = X̂}))))
      ≈⟨ fmorη-cong (FSC.copair-in₁ u v) ⟩
        fmorη Γ X̂ u
      ∎ where open ≈-Reasoning isEquiv

    c₂ : (fmorη Γ (FCP.coprod X̂ Ŷ) (FSC.copair u v) ∘co (K⊕ X̂ Ŷ .bwd ∘ ℰP.p₂)) ∘ ℰP.pair ℰP.p₁ (ℰSCm.in₂ ∘ ℰP.p₂)
         ≈ fmorη Γ Ŷ v
    c₂ =
      begin
        (fmorη Γ (FCP.coprod X̂ Ŷ) (FSC.copair u v) ∘co (K⊕ X̂ Ŷ .bwd ∘ ℰP.p₂)) ∘co (ℰSCm.in₂ ∘ ℰP.p₂)
      ≈⟨ CoK.assoc _ _ _ ⟩
        fmorη Γ (FCP.coprod X̂ Ŷ) (FSC.copair u v) ∘co ((K⊕ X̂ Ŷ .bwd ∘ ℰP.p₂) ∘co (ℰSCm.in₂ ∘ ℰP.p₂))
      ≈⟨ CoK.∘-cong₂ (co-pure _ _) ⟩
        fmorη Γ (FCP.coprod X̂ Ŷ) (FSC.copair u v) ∘co ((K⊕ X̂ Ŷ .bwd ∘ ℰSCm.in₂) ∘ ℰP.p₂)
      ≈⟨ CoK.∘-cong₂ (∘-cong₁ (K⊕-in₂ X̂ Ŷ)) ⟩
        fmorη Γ (FCP.coprod X̂ Ŷ) (FSC.copair u v) ∘co (realise .fmor FCP.in₂ ∘ ℰP.p₂)
      ≈˘⟨ CoK.∘-cong₂ (fmorη-pure Γ Ŷ FCP.in₂) ⟩
        fmorη Γ (FCP.coprod X̂ Ŷ) (FSC.copair u v) ∘co fmorη Γ Ŷ (FM.Mor-∘ FCP.in₂ (FamP.p₂ {x = η .fobj Γ} {y = Ŷ}))
      ≈˘⟨ fmorη-∘co Γ Ŷ (FSC.copair u v) _ ⟩
        fmorη Γ Ŷ (FM.Mor-∘ (FSC.copair u v) (pairη Γ Ŷ (FM.Mor-∘ FCP.in₂ (FamP.p₂ {x = η .fobj Γ} {y = Ŷ}))))
      ≈⟨ fmorη-cong (FSC.copair-in₂ u v) ⟩
        fmorη Γ Ŷ v
      ∎ where open ≈-Reasoning isEquiv

-- The invariance interface at sums.
invariance-sum : ∀ {n} {P Q : Poly ℰ n} → InvarianceAt P → InvarianceAt Q →
               InvarianceAt (P + Q)
private
  module SumCase {n} {P Q : Poly ℰ n} (CP : InvarianceAt P) (CQ : InvarianceAt Q) where
    X̂ : (Fin n → FM.Obj) → FM.Obj
    X̂ δ̂ = FM.fobj FM.μObj (Poly-map η P) δ̂

    Ŷ : (Fin n → FM.Obj) → FM.Obj
    Ŷ δ̂ = FM.fobj FM.μObj (Poly-map η Q) δ̂

    sumIso : ∀ δ̂₁ δ̂₂ (isos : ∀ i → Iso (realise .fobj (δ̂₁ i)) (realise .fobj (δ̂₂ i))) →
             Iso (realise .fobj (FCP.coprod (X̂ δ̂₁) (Ŷ δ̂₁))) (realise .fobj (FCP.coprod (X̂ δ̂₂) (Ŷ δ̂₂)))
    sumIso δ̂₁ δ̂₂ isos =
      Iso-trans (K⊕ (X̂ δ̂₁) (Ŷ δ̂₁))
        (Iso-trans (ℰCPm.coproduct-preserve-iso (CP .iso δ̂₁ δ̂₂ isos) (CQ .iso δ̂₁ δ̂₂ isos))
          (Iso-sym (K⊕ (X̂ δ̂₂) (Ŷ δ̂₂))))

    -- The composite forward map, with the source comparison iso cancelled.
    sumIso-bwd : ∀ δ̂₁ δ̂₂ isos →
                 sumIso δ̂₁ δ̂₂ isos .fwd ∘ K⊕ (X̂ δ̂₁) (Ŷ δ̂₁) .bwd
                 ≈ K⊕ (X̂ δ̂₂) (Ŷ δ̂₂) .bwd ∘ ℰCPm.coprod-m (CP .iso δ̂₁ δ̂₂ isos .fwd) (CQ .iso δ̂₁ δ̂₂ isos .fwd)
    sumIso-bwd δ̂₁ δ̂₂ isos =
      ≈-trans (assoc _ _ _)
        (≈-trans (∘-cong₂ (K⊕ (X̂ δ̂₁) (Ŷ δ̂₁) .fwd∘bwd≈id)) id-right)


    sumComp : ∀ δ̂₁ δ̂₂ δ̂₃ (isos₁₂ : ∀ i → Iso (realise .fobj (δ̂₁ i)) (realise .fobj (δ̂₂ i)))
              (isos₂₃ : ∀ i → Iso (realise .fobj (δ̂₂ i)) (realise .fobj (δ̂₃ i))) →
              sumIso δ̂₁ δ̂₃ (λ i → Iso-trans (isos₁₂ i) (isos₂₃ i)) .fwd
              ≈ sumIso δ̂₂ δ̂₃ isos₂₃ .fwd ∘ sumIso δ̂₁ δ̂₂ isos₁₂ .fwd
    sumComp δ̂₁ δ̂₂ δ̂₃ isos₁₂ isos₂₃ = ≈-trans toM (≈-sym fromM)
      where
        cm₁₂ = ℰCPm.coprod-m (CP .iso δ̂₁ δ̂₂ isos₁₂ .fwd) (CQ .iso δ̂₁ δ̂₂ isos₁₂ .fwd)
        cm₂₃ = ℰCPm.coprod-m (CP .iso δ̂₂ δ̂₃ isos₂₃ .fwd) (CQ .iso δ̂₂ δ̂₃ isos₂₃ .fwd)

        toM : sumIso δ̂₁ δ̂₃ (λ i → Iso-trans (isos₁₂ i) (isos₂₃ i)) .fwd
              ≈ (K⊕ (X̂ δ̂₃) (Ŷ δ̂₃) .bwd ∘ (cm₂₃ ∘ cm₁₂)) ∘ K⊕ (X̂ δ̂₁) (Ŷ δ̂₁) .fwd
        toM =
          ∘-cong₁ (∘-cong₂
            (≈-trans (ℰCPm.coprod-m-cong (CP .comp δ̂₁ δ̂₂ δ̂₃ isos₁₂ isos₂₃) (CQ .comp δ̂₁ δ̂₂ δ̂₃ isos₁₂ isos₂₃))
              (ℰCPm.coprod-m-comp _ _ _ _)))

        fromM : sumIso δ̂₂ δ̂₃ isos₂₃ .fwd ∘ sumIso δ̂₁ δ̂₂ isos₁₂ .fwd
                ≈ (K⊕ (X̂ δ̂₃) (Ŷ δ̂₃) .bwd ∘ (cm₂₃ ∘ cm₁₂)) ∘ K⊕ (X̂ δ̂₁) (Ŷ δ̂₁) .fwd
        fromM =
          begin
            ((K⊕ (X̂ δ̂₃) (Ŷ δ̂₃) .bwd ∘ cm₂₃) ∘ K⊕ (X̂ δ̂₂) (Ŷ δ̂₂) .fwd) ∘ ((K⊕ (X̂ δ̂₂) (Ŷ δ̂₂) .bwd ∘ cm₁₂) ∘ K⊕ (X̂ δ̂₁) (Ŷ δ̂₁) .fwd)
          ≈˘⟨ assoc _ _ _ ⟩
            (((K⊕ (X̂ δ̂₃) (Ŷ δ̂₃) .bwd ∘ cm₂₃) ∘ K⊕ (X̂ δ̂₂) (Ŷ δ̂₂) .fwd) ∘ (K⊕ (X̂ δ̂₂) (Ŷ δ̂₂) .bwd ∘ cm₁₂)) ∘ K⊕ (X̂ δ̂₁) (Ŷ δ̂₁) .fwd
          ≈⟨ ∘-cong₁ (assoc _ _ _) ⟩
            ((K⊕ (X̂ δ̂₃) (Ŷ δ̂₃) .bwd ∘ cm₂₃) ∘ (K⊕ (X̂ δ̂₂) (Ŷ δ̂₂) .fwd ∘ (K⊕ (X̂ δ̂₂) (Ŷ δ̂₂) .bwd ∘ cm₁₂))) ∘ K⊕ (X̂ δ̂₁) (Ŷ δ̂₁) .fwd
          ≈⟨ ∘-cong₁ (∘-cong₂ (≈-trans (≈-sym (assoc _ _ _)) (≈-trans (∘-cong₁ (K⊕ (X̂ δ̂₂) (Ŷ δ̂₂) .fwd∘bwd≈id)) id-left))) ⟩
            ((K⊕ (X̂ δ̂₃) (Ŷ δ̂₃) .bwd ∘ cm₂₃) ∘ cm₁₂) ∘ K⊕ (X̂ δ̂₁) (Ŷ δ̂₁) .fwd
          ≈⟨ ∘-cong₁ (assoc _ _ _) ⟩
            (K⊕ (X̂ δ̂₃) (Ŷ δ̂₃) .bwd ∘ (cm₂₃ ∘ cm₁₂)) ∘ K⊕ (X̂ δ̂₁) (Ŷ δ̂₁) .fwd
          ∎ where open ≈-Reasoning isEquiv

    sumNat : ∀ {Γ : obj} {ε̂₁ ε̂₂ : Fin n → FM.Obj}
             (δ̂₁ δ̂₂ : Fin n → FM.Obj)
             (isosδ : ∀ i → Iso (realise .fobj (δ̂₁ i)) (realise .fobj (δ̂₂ i)))
             (isosε : ∀ i → Iso (realise .fobj (ε̂₁ i)) (realise .fobj (ε̂₂ i)))
             (gs₁ : ∀ i → FM.Mor (FamP.prod (η .fobj Γ) (δ̂₁ i)) (ε̂₁ i))
             (gs₂ : ∀ i → FM.Mor (FamP.prod (η .fobj Γ) (δ̂₂ i)) (ε̂₂ i)) →
             (∀ i → fmorη Γ (δ̂₂ i) (gs₂ i) ∘co (isosδ i .fwd ∘ ℰP.p₂)
                    ≈ isosε i .fwd ∘ fmorη Γ (δ̂₁ i) (gs₁ i)) →
             fmorη Γ (FCP.coprod (X̂ δ̂₂) (Ŷ δ̂₂)) (FMu.strong-fmor (Poly-map η (P + Q)) gs₂)
               ∘co (sumIso δ̂₁ δ̂₂ isosδ .fwd ∘ ℰP.p₂)
             ≈ sumIso _ _ isosε .fwd ∘ fmorη Γ (FCP.coprod (X̂ δ̂₁) (Ŷ δ̂₁)) (FMu.strong-fmor (Poly-map η (P + Q)) gs₁)
    sumNat {Γ} {ε̂₁} {ε̂₂} δ̂₁ δ̂₂ isosδ isosε gs₁ gs₂ sqs =
      co-iso-epi (K⊕ (X̂ δ̂₁) (Ŷ δ̂₁)) (≈-trans lhs (≈-sym rhs))
      where
        sfP : ∀ δ̂ ε̂ → (∀ i → FM.Mor (FamP.prod (η .fobj Γ) (δ̂ i)) (ε̂ i)) → FM.Mor (FamP.prod (η .fobj Γ) (X̂ δ̂)) (X̂ ε̂)
        sfP δ̂ ε̂ gs = FMu.strong-fmor (Poly-map η P) gs

        sfQ : ∀ δ̂ ε̂ → (∀ i → FM.Mor (FamP.prod (η .fobj Γ) (δ̂ i)) (ε̂ i)) → FM.Mor (FamP.prod (η .fobj Γ) (Ŷ δ̂)) (Ŷ ε̂)
        sfQ δ̂ ε̂ gs = FMu.strong-fmor (Poly-map η Q) gs

        mid : ℰP.prod Γ (ℰCPm.coprod (realise .fobj (X̂ δ̂₁)) (realise .fobj (Ŷ δ̂₁))) ⇒ realise .fobj (FCP.coprod (X̂ ε̂₂) (Ŷ ε̂₂))
        mid = ℰSCm.copair
                (realise .fmor FCP.in₁ ∘ (CP .iso ε̂₁ ε̂₂ isosε .fwd ∘ fmorη Γ (X̂ δ̂₁) (sfP δ̂₁ ε̂₁ gs₁)))
                (realise .fmor FCP.in₂ ∘ (CQ .iso ε̂₁ ε̂₂ isosε .fwd ∘ fmorη Γ (Ŷ δ̂₁) (sfQ δ̂₁ ε̂₁ gs₁)))

        lhs : (fmorη Γ (FCP.coprod (X̂ δ̂₂) (Ŷ δ̂₂)) (FSC.copair (FM.Mor-∘ FCP.in₁ (sfP δ̂₂ ε̂₂ gs₂)) (FM.Mor-∘ FCP.in₂ (sfQ δ̂₂ ε̂₂ gs₂)))
                ∘co (sumIso δ̂₁ δ̂₂ isosδ .fwd ∘ ℰP.p₂)) ∘co (K⊕ (X̂ δ̂₁) (Ŷ δ̂₁) .bwd ∘ ℰP.p₂)
              ≈ mid
        lhs =
          begin
            (fmorη Γ (FCP.coprod (X̂ δ̂₂) (Ŷ δ̂₂)) (FSC.copair (FM.Mor-∘ FCP.in₁ (sfP δ̂₂ ε̂₂ gs₂)) (FM.Mor-∘ FCP.in₂ (sfQ δ̂₂ ε̂₂ gs₂))) ∘co (sumIso δ̂₁ δ̂₂ isosδ .fwd ∘ ℰP.p₂)) ∘co (K⊕ (X̂ δ̂₁) (Ŷ δ̂₁) .bwd ∘ ℰP.p₂)
          ≈⟨ CoK.assoc _ _ _ ⟩
            fmorη Γ (FCP.coprod (X̂ δ̂₂) (Ŷ δ̂₂)) (FSC.copair (FM.Mor-∘ FCP.in₁ (sfP δ̂₂ ε̂₂ gs₂)) (FM.Mor-∘ FCP.in₂ (sfQ δ̂₂ ε̂₂ gs₂))) ∘co ((sumIso δ̂₁ δ̂₂ isosδ .fwd ∘ ℰP.p₂) ∘co (K⊕ (X̂ δ̂₁) (Ŷ δ̂₁) .bwd ∘ ℰP.p₂))
          ≈⟨ CoK.∘-cong₂ (≈-trans (co-pure _ _) (∘-cong₁ (sumIso-bwd δ̂₁ δ̂₂ isosδ))) ⟩
            fmorη Γ (FCP.coprod (X̂ δ̂₂) (Ŷ δ̂₂)) (FSC.copair (FM.Mor-∘ FCP.in₁ (sfP δ̂₂ ε̂₂ gs₂)) (FM.Mor-∘ FCP.in₂ (sfQ δ̂₂ ε̂₂ gs₂))) ∘co ((K⊕ (X̂ δ̂₂) (Ŷ δ̂₂) .bwd ∘ ℰCPm.coprod-m (CP .iso δ̂₁ δ̂₂ isosδ .fwd) (CQ .iso δ̂₁ δ̂₂ isosδ .fwd)) ∘ ℰP.p₂)
          ≈˘⟨ CoK.∘-cong₂ (co-pure _ _) ⟩
            fmorη Γ (FCP.coprod (X̂ δ̂₂) (Ŷ δ̂₂)) (FSC.copair (FM.Mor-∘ FCP.in₁ (sfP δ̂₂ ε̂₂ gs₂)) (FM.Mor-∘ FCP.in₂ (sfQ δ̂₂ ε̂₂ gs₂))) ∘co ((K⊕ (X̂ δ̂₂) (Ŷ δ̂₂) .bwd ∘ ℰP.p₂) ∘co (ℰCPm.coprod-m (CP .iso δ̂₁ δ̂₂ isosδ .fwd) (CQ .iso δ̂₁ δ̂₂ isosδ .fwd) ∘ ℰP.p₂))
          ≈˘⟨ CoK.assoc _ _ _ ⟩
            (fmorη Γ (FCP.coprod (X̂ δ̂₂) (Ŷ δ̂₂)) (FSC.copair (FM.Mor-∘ FCP.in₁ (sfP δ̂₂ ε̂₂ gs₂)) (FM.Mor-∘ FCP.in₂ (sfQ δ̂₂ ε̂₂ gs₂))) ∘co (K⊕ (X̂ δ̂₂) (Ŷ δ̂₂) .bwd ∘ ℰP.p₂)) ∘co (ℰCPm.coprod-m (CP .iso δ̂₁ δ̂₂ isosδ .fwd) (CQ .iso δ̂₁ δ̂₂ isosδ .fwd) ∘ ℰP.p₂)
          ≈⟨ CoK.∘-cong₁ (fmorη-scopair Γ (X̂ δ̂₂) (Ŷ δ̂₂) _ _) ⟩
            ℰSCm.copair (fmorη Γ (X̂ δ̂₂) (FM.Mor-∘ FCP.in₁ (sfP δ̂₂ ε̂₂ gs₂))) (fmorη Γ (Ŷ δ̂₂) (FM.Mor-∘ FCP.in₂ (sfQ δ̂₂ ε̂₂ gs₂))) ∘co (ℰCPm.coprod-m (CP .iso δ̂₁ δ̂₂ isosδ .fwd) (CQ .iso δ̂₁ δ̂₂ isosδ .fwd) ∘ ℰP.p₂)
          ≈⟨ scopair-coprod-m _ _ _ _ ⟩
            ℰSCm.copair (fmorη Γ (X̂ δ̂₂) (FM.Mor-∘ FCP.in₁ (sfP δ̂₂ ε̂₂ gs₂)) ∘co (CP .iso δ̂₁ δ̂₂ isosδ .fwd ∘ ℰP.p₂)) (fmorη Γ (Ŷ δ̂₂) (FM.Mor-∘ FCP.in₂ (sfQ δ̂₂ ε̂₂ gs₂)) ∘co (CQ .iso δ̂₁ δ̂₂ isosδ .fwd ∘ ℰP.p₂))
          ≈⟨ ℰSCm.copair-cong (≈-trans (CoK.∘-cong₁ (fmorη-post Γ (X̂ δ̂₂) FCP.in₁ _)) (≈-trans (assoc _ _ _) (∘-cong₂ (CP .natural δ̂₁ δ̂₂ isosδ isosε gs₁ gs₂ sqs)))) (≈-trans (CoK.∘-cong₁ (fmorη-post Γ (Ŷ δ̂₂) FCP.in₂ _)) (≈-trans (assoc _ _ _) (∘-cong₂ (CQ .natural δ̂₁ δ̂₂ isosδ isosε gs₁ gs₂ sqs)))) ⟩
            mid
          ∎
          where
            open ≈-Reasoning isEquiv



        rhs : (sumIso _ _ isosε .fwd ∘ fmorη Γ (FCP.coprod (X̂ δ̂₁) (Ŷ δ̂₁)) (FSC.copair (FM.Mor-∘ FCP.in₁ (sfP δ̂₁ ε̂₁ gs₁)) (FM.Mor-∘ FCP.in₂ (sfQ δ̂₁ ε̂₁ gs₁))))
                ∘co (K⊕ (X̂ δ̂₁) (Ŷ δ̂₁) .bwd ∘ ℰP.p₂)
              ≈ mid
        rhs =
          begin
            (sumIso _ _ isosε .fwd ∘ fmorη Γ (FCP.coprod (X̂ δ̂₁) (Ŷ δ̂₁)) (FSC.copair (FM.Mor-∘ FCP.in₁ (sfP δ̂₁ ε̂₁ gs₁)) (FM.Mor-∘ FCP.in₂ (sfQ δ̂₁ ε̂₁ gs₁)))) ∘co (K⊕ (X̂ δ̂₁) (Ŷ δ̂₁) .bwd ∘ ℰP.p₂)
          ≈⟨ assoc _ _ _ ⟩
            sumIso _ _ isosε .fwd ∘ (fmorη Γ (FCP.coprod (X̂ δ̂₁) (Ŷ δ̂₁)) (FSC.copair (FM.Mor-∘ FCP.in₁ (sfP δ̂₁ ε̂₁ gs₁)) (FM.Mor-∘ FCP.in₂ (sfQ δ̂₁ ε̂₁ gs₁))) ∘co (K⊕ (X̂ δ̂₁) (Ŷ δ̂₁) .bwd ∘ ℰP.p₂))
          ≈⟨ ∘-cong₂ (fmorη-scopair Γ (X̂ δ̂₁) (Ŷ δ̂₁) _ _) ⟩
            sumIso _ _ isosε .fwd ∘ ℰSCm.copair (fmorη Γ (X̂ δ̂₁) (FM.Mor-∘ FCP.in₁ (sfP δ̂₁ ε̂₁ gs₁))) (fmorη Γ (Ŷ δ̂₁) (FM.Mor-∘ FCP.in₂ (sfQ δ̂₁ ε̂₁ gs₁)))
          ≈⟨ ℰSCm.copair-natural _ _ _ ⟩
            ℰSCm.copair (sumIso _ _ isosε .fwd ∘ fmorη Γ (X̂ δ̂₁) (FM.Mor-∘ FCP.in₁ (sfP δ̂₁ ε̂₁ gs₁))) (sumIso _ _ isosε .fwd ∘ fmorη Γ (Ŷ δ̂₁) (FM.Mor-∘ FCP.in₂ (sfQ δ̂₁ ε̂₁ gs₁)))
          ≈⟨ ℰSCm.copair-cong (≈-trans (∘-cong₂ (fmorη-post Γ (X̂ δ̂₁) FCP.in₁ _)) (≈-trans (≈-sym (assoc _ _ _)) (≈-trans (∘-cong₁ push-in₁) (assoc _ _ _)))) (≈-trans (∘-cong₂ (fmorη-post Γ (Ŷ δ̂₁) FCP.in₂ _)) (≈-trans (≈-sym (assoc _ _ _)) (≈-trans (∘-cong₁ push-in₂) (assoc _ _ _)))) ⟩
            mid
          ∎
          where
            open ≈-Reasoning isEquiv

            push-in₁ : sumIso _ _ isosε .fwd ∘ realise .fmor FCP.in₁
                       ≈ realise .fmor FCP.in₁ ∘ CP .iso ε̂₁ ε̂₂ isosε .fwd
            push-in₁ =
              ≈-trans (assoc _ _ _)
                (≈-trans (∘-cong₂ (K⊕-in₁' (X̂ ε̂₁) (Ŷ ε̂₁)))
                  (≈-trans (assoc _ _ _)
                    (≈-trans (∘-cong₂ (ℰCPm.copair-in₁ _ _))
                      (≈-trans (≈-sym (assoc _ _ _)) (∘-cong₁ (K⊕-in₁ (X̂ ε̂₂) (Ŷ ε̂₂)))))))

            push-in₂ : sumIso _ _ isosε .fwd ∘ realise .fmor FCP.in₂
                       ≈ realise .fmor FCP.in₂ ∘ CQ .iso ε̂₁ ε̂₂ isosε .fwd
            push-in₂ =
              ≈-trans (assoc _ _ _)
                (≈-trans (∘-cong₂ (K⊕-in₂' (X̂ ε̂₁) (Ŷ ε̂₁)))
                  (≈-trans (assoc _ _ _)
                    (≈-trans (∘-cong₂ (ℰCPm.copair-in₂ _ _))
                      (≈-trans (≈-sym (assoc _ _ _)) (∘-cong₁ (K⊕-in₂ (X̂ ε̂₂) (Ŷ ε̂₂)))))))

invariance-sum {n} {P} {Q} CP CQ .iso = SumCase.sumIso CP CQ
invariance-sum {n} {P} {Q} CP CQ .natural = SumCase.sumNat CP CQ
invariance-sum {n} {P} {Q} CP CQ .comp = SumCase.sumComp CP CQ

-- Product machinery for the product case of the invariance.
K× : ∀ (X̂ Ŷ : FM.Obj) → Iso (realise .fobj (FamP.prod X̂ Ŷ))
                            (ℰP.prod (realise .fobj X̂) (realise .fobj Ŷ))
K× X̂ Ŷ = FR.realise-products-iso ℰP ℰE X̂ Ŷ

K×-p₁ : ∀ (X̂ Ŷ : FM.Obj) → realise .fmor (FamP.p₁ {x = X̂} {y = Ŷ}) ∘ K× X̂ Ŷ .bwd ≈ ℰP.p₁
K×-p₁ X̂ Ŷ =
  ≈-trans (∘-cong₁ (≈-sym (FR.realise-products-p₁ ℰP ℰE X̂ Ŷ)))
    (≈-trans (assoc _ _ _) (≈-trans (∘-cong₂ (K× X̂ Ŷ .fwd∘bwd≈id)) id-right))

K×-p₂ : ∀ (X̂ Ŷ : FM.Obj) → realise .fmor (FamP.p₂ {x = X̂} {y = Ŷ}) ∘ K× X̂ Ŷ .bwd ≈ ℰP.p₂
K×-p₂ X̂ Ŷ =
  ≈-trans (∘-cong₁ (≈-sym (FR.realise-products-p₂ ℰP ℰE X̂ Ŷ)))
    (≈-trans (assoc _ _ _) (≈-trans (∘-cong₂ (K× X̂ Ŷ .fwd∘bwd≈id)) id-right))

-- Realisation in context sends the strong product action to the strong
-- product action, across the product comparison isos.
fmorη-sprodm : ∀ (Γ : obj) (X̂ Ŷ : FM.Obj) {Ẑ₁ Ẑ₂ : FM.Obj}
               (u : FM.Mor (FamP.prod (η .fobj Γ) X̂) Ẑ₁)
               (v : FM.Mor (FamP.prod (η .fobj Γ) Ŷ) Ẑ₂) →
               fmorη Γ (FamP.prod X̂ Ŷ) (FamP.strong-prod-m u v) ∘co (K× X̂ Ŷ .bwd ∘ ℰP.p₂)
               ≈ K× Ẑ₁ Ẑ₂ .bwd ∘ ℰP.strong-prod-m (fmorη Γ X̂ u) (fmorη Γ Ŷ v)
fmorη-sprodm Γ X̂ Ŷ {Ẑ₁} {Ẑ₂} u v =
  iso-shuffle (K× Ẑ₁ Ẑ₂) _ _
    (≈-trans (≈-sym (ℰP.pair-ext _)) (ℰP.pair-cong core₁ core₂))
  where
    core₁ : ℰP.p₁ ∘ (K× Ẑ₁ Ẑ₂ .fwd ∘ (fmorη Γ (FamP.prod X̂ Ŷ) (FamP.strong-prod-m u v) ∘co (K× X̂ Ŷ .bwd ∘ ℰP.p₂)))
            ≈ fmorη Γ X̂ u ∘ ℰP.strong-p₁
    core₁ =
      begin
        ℰP.p₁ ∘ (K× Ẑ₁ Ẑ₂ .fwd ∘ (fmorη Γ (FamP.prod X̂ Ŷ) (FamP.strong-prod-m u v) ∘co (K× X̂ Ŷ .bwd ∘ ℰP.p₂)))
      ≈˘⟨ assoc _ _ _ ⟩
        (ℰP.p₁ ∘ K× Ẑ₁ Ẑ₂ .fwd) ∘ (fmorη Γ (FamP.prod X̂ Ŷ) (FamP.strong-prod-m u v) ∘co (K× X̂ Ŷ .bwd ∘ ℰP.p₂))
      ≈⟨ ∘-cong₁ (FR.realise-products-p₁ ℰP ℰE Ẑ₁ Ẑ₂) ⟩
        realise .fmor (FamP.p₁ {x = Ẑ₁} {y = Ẑ₂}) ∘ (fmorη Γ (FamP.prod X̂ Ŷ) (FamP.strong-prod-m u v) ∘co (K× X̂ Ŷ .bwd ∘ ℰP.p₂))
      ≈˘⟨ assoc _ _ _ ⟩
        (realise .fmor (FamP.p₁ {x = Ẑ₁} {y = Ẑ₂}) ∘ fmorη Γ (FamP.prod X̂ Ŷ) (FamP.strong-prod-m u v)) ∘co (K× X̂ Ŷ .bwd ∘ ℰP.p₂)
      ≈˘⟨ CoK.∘-cong₁ (fmorη-post Γ (FamP.prod X̂ Ŷ) _ _) ⟩
        fmorη Γ (FamP.prod X̂ Ŷ) (FM.Mor-∘ (FamP.p₁ {x = Ẑ₁} {y = Ẑ₂}) (FamP.strong-prod-m u v)) ∘co (K× X̂ Ŷ .bwd ∘ ℰP.p₂)
      ≈⟨ CoK.∘-cong₁ (fmorη-cong (FamP.pair-p₁ _ _)) ⟩
        fmorη Γ (FamP.prod X̂ Ŷ) (FM.Mor-∘ u FamP.strong-p₁) ∘co (K× X̂ Ŷ .bwd ∘ ℰP.p₂)
      ≈⟨ CoK.∘-cong₁ (fmorη-∘co Γ (FamP.prod X̂ Ŷ) u _) ⟩
        (fmorη Γ X̂ u ∘co fmorη Γ (FamP.prod X̂ Ŷ) (FM.Mor-∘ (FamP.p₁ {x = X̂} {y = Ŷ}) FamP.p₂)) ∘co (K× X̂ Ŷ .bwd ∘ ℰP.p₂)
      ≈⟨ CoK.∘-cong₁ (CoK.∘-cong₂ (fmorη-pure Γ (FamP.prod X̂ Ŷ) (FamP.p₁ {x = X̂} {y = Ŷ}))) ⟩
        (fmorη Γ X̂ u ∘co (realise .fmor (FamP.p₁ {x = X̂} {y = Ŷ}) ∘ ℰP.p₂)) ∘co (K× X̂ Ŷ .bwd ∘ ℰP.p₂)
      ≈⟨ CoK.assoc _ _ _ ⟩
        fmorη Γ X̂ u ∘co ((realise .fmor (FamP.p₁ {x = X̂} {y = Ŷ}) ∘ ℰP.p₂) ∘co (K× X̂ Ŷ .bwd ∘ ℰP.p₂))
      ≈⟨ CoK.∘-cong₂ (co-pure _ _) ⟩
        fmorη Γ X̂ u ∘co ((realise .fmor (FamP.p₁ {x = X̂} {y = Ŷ}) ∘ K× X̂ Ŷ .bwd) ∘ ℰP.p₂)
      ≈⟨ CoK.∘-cong₂ (∘-cong₁ (K×-p₁ X̂ Ŷ)) ⟩
        fmorη Γ X̂ u ∘co (ℰP.p₁ ∘ ℰP.p₂)
      ∎ where open ≈-Reasoning isEquiv

    core₂ : ℰP.p₂ ∘ (K× Ẑ₁ Ẑ₂ .fwd ∘ (fmorη Γ (FamP.prod X̂ Ŷ) (FamP.strong-prod-m u v) ∘co (K× X̂ Ŷ .bwd ∘ ℰP.p₂)))
            ≈ fmorη Γ Ŷ v ∘ ℰP.strong-p₂
    core₂ =
      begin
        ℰP.p₂ ∘ (K× Ẑ₁ Ẑ₂ .fwd ∘ (fmorη Γ (FamP.prod X̂ Ŷ) (FamP.strong-prod-m u v) ∘co (K× X̂ Ŷ .bwd ∘ ℰP.p₂)))
      ≈˘⟨ assoc _ _ _ ⟩
        (ℰP.p₂ ∘ K× Ẑ₁ Ẑ₂ .fwd) ∘ (fmorη Γ (FamP.prod X̂ Ŷ) (FamP.strong-prod-m u v) ∘co (K× X̂ Ŷ .bwd ∘ ℰP.p₂))
      ≈⟨ ∘-cong₁ (FR.realise-products-p₂ ℰP ℰE Ẑ₁ Ẑ₂) ⟩
        realise .fmor (FamP.p₂ {x = Ẑ₁} {y = Ẑ₂}) ∘ (fmorη Γ (FamP.prod X̂ Ŷ) (FamP.strong-prod-m u v) ∘co (K× X̂ Ŷ .bwd ∘ ℰP.p₂))
      ≈˘⟨ assoc _ _ _ ⟩
        (realise .fmor (FamP.p₂ {x = Ẑ₁} {y = Ẑ₂}) ∘ fmorη Γ (FamP.prod X̂ Ŷ) (FamP.strong-prod-m u v)) ∘co (K× X̂ Ŷ .bwd ∘ ℰP.p₂)
      ≈˘⟨ CoK.∘-cong₁ (fmorη-post Γ (FamP.prod X̂ Ŷ) _ _) ⟩
        fmorη Γ (FamP.prod X̂ Ŷ) (FM.Mor-∘ (FamP.p₂ {x = Ẑ₁} {y = Ẑ₂}) (FamP.strong-prod-m u v)) ∘co (K× X̂ Ŷ .bwd ∘ ℰP.p₂)
      ≈⟨ CoK.∘-cong₁ (fmorη-cong (FamP.pair-p₂ _ _)) ⟩
        fmorη Γ (FamP.prod X̂ Ŷ) (FM.Mor-∘ v FamP.strong-p₂) ∘co (K× X̂ Ŷ .bwd ∘ ℰP.p₂)
      ≈⟨ CoK.∘-cong₁ (fmorη-∘co Γ (FamP.prod X̂ Ŷ) v _) ⟩
        (fmorη Γ Ŷ v ∘co fmorη Γ (FamP.prod X̂ Ŷ) (FM.Mor-∘ (FamP.p₂ {x = X̂} {y = Ŷ}) FamP.p₂)) ∘co (K× X̂ Ŷ .bwd ∘ ℰP.p₂)
      ≈⟨ CoK.∘-cong₁ (CoK.∘-cong₂ (fmorη-pure Γ (FamP.prod X̂ Ŷ) (FamP.p₂ {x = X̂} {y = Ŷ}))) ⟩
        (fmorη Γ Ŷ v ∘co (realise .fmor (FamP.p₂ {x = X̂} {y = Ŷ}) ∘ ℰP.p₂)) ∘co (K× X̂ Ŷ .bwd ∘ ℰP.p₂)
      ≈⟨ CoK.assoc _ _ _ ⟩
        fmorη Γ Ŷ v ∘co ((realise .fmor (FamP.p₂ {x = X̂} {y = Ŷ}) ∘ ℰP.p₂) ∘co (K× X̂ Ŷ .bwd ∘ ℰP.p₂))
      ≈⟨ CoK.∘-cong₂ (co-pure _ _) ⟩
        fmorη Γ Ŷ v ∘co ((realise .fmor (FamP.p₂ {x = X̂} {y = Ŷ}) ∘ K× X̂ Ŷ .bwd) ∘ ℰP.p₂)
      ≈⟨ CoK.∘-cong₂ (∘-cong₁ (K×-p₂ X̂ Ŷ)) ⟩
        fmorη Γ Ŷ v ∘co (ℰP.p₂ ∘ ℰP.p₂)
      ∎ where open ≈-Reasoning isEquiv

-- The invariance interface at products.
invariance-prod : ∀ {n} {P Q : Poly ℰ n} → InvarianceAt P → InvarianceAt Q →
                InvarianceAt (P × Q)
private
  module ProdCase {n} {P Q : Poly ℰ n} (CP : InvarianceAt P) (CQ : InvarianceAt Q) where
    X̂ : (Fin n → FM.Obj) → FM.Obj
    X̂ δ̂ = FM.fobj FM.μObj (Poly-map η P) δ̂

    Ŷ : (Fin n → FM.Obj) → FM.Obj
    Ŷ δ̂ = FM.fobj FM.μObj (Poly-map η Q) δ̂

    prodIso : ∀ δ̂₁ δ̂₂ (isos : ∀ i → Iso (realise .fobj (δ̂₁ i)) (realise .fobj (δ̂₂ i))) →
              Iso (realise .fobj (FamP.prod (X̂ δ̂₁) (Ŷ δ̂₁))) (realise .fobj (FamP.prod (X̂ δ̂₂) (Ŷ δ̂₂)))
    prodIso δ̂₁ δ̂₂ isos =
      Iso-trans (K× (X̂ δ̂₁) (Ŷ δ̂₁))
        (Iso-trans (ℰP.product-preserves-iso (CP .iso δ̂₁ δ̂₂ isos) (CQ .iso δ̂₁ δ̂₂ isos))
          (Iso-sym (K× (X̂ δ̂₂) (Ŷ δ̂₂))))

    prodIso-bwd : ∀ δ̂₁ δ̂₂ isos →
                  prodIso δ̂₁ δ̂₂ isos .fwd ∘ K× (X̂ δ̂₁) (Ŷ δ̂₁) .bwd
                  ≈ K× (X̂ δ̂₂) (Ŷ δ̂₂) .bwd ∘ ℰP.prod-m (CP .iso δ̂₁ δ̂₂ isos .fwd) (CQ .iso δ̂₁ δ̂₂ isos .fwd)
    prodIso-bwd δ̂₁ δ̂₂ isos =
      ≈-trans (assoc _ _ _)
        (≈-trans (∘-cong₂ (K× (X̂ δ̂₁) (Ŷ δ̂₁) .fwd∘bwd≈id)) id-right)


    prodComp : ∀ δ̂₁ δ̂₂ δ̂₃ (isos₁₂ : ∀ i → Iso (realise .fobj (δ̂₁ i)) (realise .fobj (δ̂₂ i)))
               (isos₂₃ : ∀ i → Iso (realise .fobj (δ̂₂ i)) (realise .fobj (δ̂₃ i))) →
               prodIso δ̂₁ δ̂₃ (λ i → Iso-trans (isos₁₂ i) (isos₂₃ i)) .fwd
               ≈ prodIso δ̂₂ δ̂₃ isos₂₃ .fwd ∘ prodIso δ̂₁ δ̂₂ isos₁₂ .fwd
    prodComp δ̂₁ δ̂₂ δ̂₃ isos₁₂ isos₂₃ = ≈-trans toM (≈-sym fromM)
      where
        pm₁₂ = ℰP.prod-m (CP .iso δ̂₁ δ̂₂ isos₁₂ .fwd) (CQ .iso δ̂₁ δ̂₂ isos₁₂ .fwd)
        pm₂₃ = ℰP.prod-m (CP .iso δ̂₂ δ̂₃ isos₂₃ .fwd) (CQ .iso δ̂₂ δ̂₃ isos₂₃ .fwd)

        toM : prodIso δ̂₁ δ̂₃ (λ i → Iso-trans (isos₁₂ i) (isos₂₃ i)) .fwd
              ≈ (K× (X̂ δ̂₃) (Ŷ δ̂₃) .bwd ∘ (pm₂₃ ∘ pm₁₂)) ∘ K× (X̂ δ̂₁) (Ŷ δ̂₁) .fwd
        toM =
          ∘-cong₁ (∘-cong₂
            (≈-trans (ℰP.prod-m-cong (CP .comp δ̂₁ δ̂₂ δ̂₃ isos₁₂ isos₂₃) (CQ .comp δ̂₁ δ̂₂ δ̂₃ isos₁₂ isos₂₃))
              (ℰP.prod-m-comp _ _ _ _)))

        fromM : prodIso δ̂₂ δ̂₃ isos₂₃ .fwd ∘ prodIso δ̂₁ δ̂₂ isos₁₂ .fwd
                ≈ (K× (X̂ δ̂₃) (Ŷ δ̂₃) .bwd ∘ (pm₂₃ ∘ pm₁₂)) ∘ K× (X̂ δ̂₁) (Ŷ δ̂₁) .fwd
        fromM =
          begin
            ((K× (X̂ δ̂₃) (Ŷ δ̂₃) .bwd ∘ pm₂₃) ∘ K× (X̂ δ̂₂) (Ŷ δ̂₂) .fwd) ∘ ((K× (X̂ δ̂₂) (Ŷ δ̂₂) .bwd ∘ pm₁₂) ∘ K× (X̂ δ̂₁) (Ŷ δ̂₁) .fwd)
          ≈˘⟨ assoc _ _ _ ⟩
            (((K× (X̂ δ̂₃) (Ŷ δ̂₃) .bwd ∘ pm₂₃) ∘ K× (X̂ δ̂₂) (Ŷ δ̂₂) .fwd) ∘ (K× (X̂ δ̂₂) (Ŷ δ̂₂) .bwd ∘ pm₁₂)) ∘ K× (X̂ δ̂₁) (Ŷ δ̂₁) .fwd
          ≈⟨ ∘-cong₁ (assoc _ _ _) ⟩
            ((K× (X̂ δ̂₃) (Ŷ δ̂₃) .bwd ∘ pm₂₃) ∘ (K× (X̂ δ̂₂) (Ŷ δ̂₂) .fwd ∘ (K× (X̂ δ̂₂) (Ŷ δ̂₂) .bwd ∘ pm₁₂))) ∘ K× (X̂ δ̂₁) (Ŷ δ̂₁) .fwd
          ≈⟨ ∘-cong₁ (∘-cong₂ (≈-trans (≈-sym (assoc _ _ _)) (≈-trans (∘-cong₁ (K× (X̂ δ̂₂) (Ŷ δ̂₂) .fwd∘bwd≈id)) id-left))) ⟩
            ((K× (X̂ δ̂₃) (Ŷ δ̂₃) .bwd ∘ pm₂₃) ∘ pm₁₂) ∘ K× (X̂ δ̂₁) (Ŷ δ̂₁) .fwd
          ≈⟨ ∘-cong₁ (assoc _ _ _) ⟩
            (K× (X̂ δ̂₃) (Ŷ δ̂₃) .bwd ∘ (pm₂₃ ∘ pm₁₂)) ∘ K× (X̂ δ̂₁) (Ŷ δ̂₁) .fwd
          ∎ where open ≈-Reasoning isEquiv

    prodNat : ∀ {Γ : obj} {ε̂₁ ε̂₂ : Fin n → FM.Obj}
              (δ̂₁ δ̂₂ : Fin n → FM.Obj)
              (isosδ : ∀ i → Iso (realise .fobj (δ̂₁ i)) (realise .fobj (δ̂₂ i)))
              (isosε : ∀ i → Iso (realise .fobj (ε̂₁ i)) (realise .fobj (ε̂₂ i)))
              (gs₁ : ∀ i → FM.Mor (FamP.prod (η .fobj Γ) (δ̂₁ i)) (ε̂₁ i))
              (gs₂ : ∀ i → FM.Mor (FamP.prod (η .fobj Γ) (δ̂₂ i)) (ε̂₂ i)) →
              (∀ i → fmorη Γ (δ̂₂ i) (gs₂ i) ∘co (isosδ i .fwd ∘ ℰP.p₂)
                     ≈ isosε i .fwd ∘ fmorη Γ (δ̂₁ i) (gs₁ i)) →
              fmorη Γ (FamP.prod (X̂ δ̂₂) (Ŷ δ̂₂)) (FMu.strong-fmor (Poly-map η (P × Q)) gs₂)
                ∘co (prodIso δ̂₁ δ̂₂ isosδ .fwd ∘ ℰP.p₂)
              ≈ prodIso _ _ isosε .fwd ∘ fmorη Γ (FamP.prod (X̂ δ̂₁) (Ŷ δ̂₁)) (FMu.strong-fmor (Poly-map η (P × Q)) gs₁)
    prodNat {Γ} {ε̂₁} {ε̂₂} δ̂₁ δ̂₂ isosδ isosε gs₁ gs₂ sqs =
      co-iso-epi (K× (X̂ δ̂₁) (Ŷ δ̂₁)) (≈-trans lhs (≈-sym rhs))
      where
        sfP = FMu.strong-fmor (Poly-map η P)
        sfQ = FMu.strong-fmor (Poly-map η Q)

        mid : ℰP.prod Γ (ℰP.prod (realise .fobj (X̂ δ̂₁)) (realise .fobj (Ŷ δ̂₁))) ⇒ realise .fobj (FamP.prod (X̂ ε̂₂) (Ŷ ε̂₂))
        mid = K× (X̂ ε̂₂) (Ŷ ε̂₂) .bwd ∘
              ℰP.strong-prod-m
                (CP .iso ε̂₁ ε̂₂ isosε .fwd ∘ fmorη Γ (X̂ δ̂₁) (sfP gs₁))
                (CQ .iso ε̂₁ ε̂₂ isosε .fwd ∘ fmorη Γ (Ŷ δ̂₁) (sfQ gs₁))

        lhs : (fmorη Γ (FamP.prod (X̂ δ̂₂) (Ŷ δ̂₂)) (FamP.strong-prod-m (sfP gs₂) (sfQ gs₂))
                ∘co (prodIso δ̂₁ δ̂₂ isosδ .fwd ∘ ℰP.p₂)) ∘co (K× (X̂ δ̂₁) (Ŷ δ̂₁) .bwd ∘ ℰP.p₂)
              ≈ mid
        lhs =
          begin
            (fmorη Γ (FamP.prod (X̂ δ̂₂) (Ŷ δ̂₂)) (FamP.strong-prod-m (sfP gs₂) (sfQ gs₂)) ∘co (prodIso δ̂₁ δ̂₂ isosδ .fwd ∘ ℰP.p₂)) ∘co (K× (X̂ δ̂₁) (Ŷ δ̂₁) .bwd ∘ ℰP.p₂)
          ≈⟨ CoK.assoc _ _ _ ⟩
            fmorη Γ (FamP.prod (X̂ δ̂₂) (Ŷ δ̂₂)) (FamP.strong-prod-m (sfP gs₂) (sfQ gs₂)) ∘co ((prodIso δ̂₁ δ̂₂ isosδ .fwd ∘ ℰP.p₂) ∘co (K× (X̂ δ̂₁) (Ŷ δ̂₁) .bwd ∘ ℰP.p₂))
          ≈⟨ CoK.∘-cong₂ (≈-trans (co-pure _ _) (∘-cong₁ (prodIso-bwd δ̂₁ δ̂₂ isosδ))) ⟩
            fmorη Γ (FamP.prod (X̂ δ̂₂) (Ŷ δ̂₂)) (FamP.strong-prod-m (sfP gs₂) (sfQ gs₂)) ∘co ((K× (X̂ δ̂₂) (Ŷ δ̂₂) .bwd ∘ ℰP.prod-m (CP .iso δ̂₁ δ̂₂ isosδ .fwd) (CQ .iso δ̂₁ δ̂₂ isosδ .fwd)) ∘ ℰP.p₂)
          ≈˘⟨ CoK.∘-cong₂ (co-pure _ _) ⟩
            fmorη Γ (FamP.prod (X̂ δ̂₂) (Ŷ δ̂₂)) (FamP.strong-prod-m (sfP gs₂) (sfQ gs₂)) ∘co ((K× (X̂ δ̂₂) (Ŷ δ̂₂) .bwd ∘ ℰP.p₂) ∘co (ℰP.prod-m (CP .iso δ̂₁ δ̂₂ isosδ .fwd) (CQ .iso δ̂₁ δ̂₂ isosδ .fwd) ∘ ℰP.p₂))
          ≈˘⟨ CoK.assoc _ _ _ ⟩
            (fmorη Γ (FamP.prod (X̂ δ̂₂) (Ŷ δ̂₂)) (FamP.strong-prod-m (sfP gs₂) (sfQ gs₂)) ∘co (K× (X̂ δ̂₂) (Ŷ δ̂₂) .bwd ∘ ℰP.p₂)) ∘co (ℰP.prod-m (CP .iso δ̂₁ δ̂₂ isosδ .fwd) (CQ .iso δ̂₁ δ̂₂ isosδ .fwd) ∘ ℰP.p₂)
          ≈⟨ CoK.∘-cong₁ (fmorη-sprodm Γ (X̂ δ̂₂) (Ŷ δ̂₂) _ _) ⟩
            (K× (X̂ ε̂₂) (Ŷ ε̂₂) .bwd ∘ ℰP.strong-prod-m (fmorη Γ (X̂ δ̂₂) (sfP gs₂)) (fmorη Γ (Ŷ δ̂₂) (sfQ gs₂))) ∘co (ℰP.prod-m (CP .iso δ̂₁ δ̂₂ isosδ .fwd) (CQ .iso δ̂₁ δ̂₂ isosδ .fwd) ∘ ℰP.p₂)
          ≈⟨ assoc _ _ _ ⟩
            K× (X̂ ε̂₂) (Ŷ ε̂₂) .bwd ∘ (ℰP.strong-prod-m (fmorη Γ (X̂ δ̂₂) (sfP gs₂)) (fmorη Γ (Ŷ δ̂₂) (sfQ gs₂)) ∘co (ℰP.prod-m (CP .iso δ̂₁ δ̂₂ isosδ .fwd) (CQ .iso δ̂₁ δ̂₂ isosδ .fwd) ∘ ℰP.p₂))
          ≈⟨ ∘-cong₂ (∘-cong₂ (ℰP.pair-cong (≈-sym id-left) ≈-refl)) ⟩
            K× (X̂ ε̂₂) (Ŷ ε̂₂) .bwd ∘ (ℰP.strong-prod-m (fmorη Γ (X̂ δ̂₂) (sfP gs₂)) (fmorη Γ (Ŷ δ̂₂) (sfQ gs₂)) ∘ ℰP.prod-m (id _) (ℰP.prod-m (CP .iso δ̂₁ δ̂₂ isosδ .fwd) (CQ .iso δ̂₁ δ̂₂ isosδ .fwd)))
          ≈⟨ ∘-cong₂ (ℰP.strong-prod-m-pre _ _ _ _ _) ⟩
            K× (X̂ ε̂₂) (Ŷ ε̂₂) .bwd ∘ ℰP.strong-prod-m (fmorη Γ (X̂ δ̂₂) (sfP gs₂) ∘ ℰP.prod-m (id _) (CP .iso δ̂₁ δ̂₂ isosδ .fwd)) (fmorη Γ (Ŷ δ̂₂) (sfQ gs₂) ∘ ℰP.prod-m (id _) (CQ .iso δ̂₁ δ̂₂ isosδ .fwd))
          ≈⟨ ∘-cong₂ (ℰP.strong-prod-m-cong (≈-trans (∘-cong₂ (ℰP.pair-cong id-left ≈-refl)) (CP .natural δ̂₁ δ̂₂ isosδ isosε gs₁ gs₂ sqs)) (≈-trans (∘-cong₂ (ℰP.pair-cong id-left ≈-refl)) (CQ .natural δ̂₁ δ̂₂ isosδ isosε gs₁ gs₂ sqs))) ⟩
            mid
          ∎
          where
            open ≈-Reasoning isEquiv



        rhs : (prodIso _ _ isosε .fwd ∘ fmorη Γ (FamP.prod (X̂ δ̂₁) (Ŷ δ̂₁)) (FamP.strong-prod-m (sfP gs₁) (sfQ gs₁)))
                ∘co (K× (X̂ δ̂₁) (Ŷ δ̂₁) .bwd ∘ ℰP.p₂)
              ≈ mid
        rhs =
          begin
            (prodIso _ _ isosε .fwd ∘ fmorη Γ (FamP.prod (X̂ δ̂₁) (Ŷ δ̂₁)) (FamP.strong-prod-m (sfP gs₁) (sfQ gs₁))) ∘co (K× (X̂ δ̂₁) (Ŷ δ̂₁) .bwd ∘ ℰP.p₂)
          ≈⟨ assoc _ _ _ ⟩
            prodIso _ _ isosε .fwd ∘ (fmorη Γ (FamP.prod (X̂ δ̂₁) (Ŷ δ̂₁)) (FamP.strong-prod-m (sfP gs₁) (sfQ gs₁)) ∘co (K× (X̂ δ̂₁) (Ŷ δ̂₁) .bwd ∘ ℰP.p₂))
          ≈⟨ ∘-cong₂ (fmorη-sprodm Γ (X̂ δ̂₁) (Ŷ δ̂₁) _ _) ⟩
            prodIso _ _ isosε .fwd ∘ (K× (X̂ ε̂₁) (Ŷ ε̂₁) .bwd ∘ ℰP.strong-prod-m (fmorη Γ (X̂ δ̂₁) (sfP gs₁)) (fmorη Γ (Ŷ δ̂₁) (sfQ gs₁)))
          ≈˘⟨ assoc _ _ _ ⟩
            (prodIso _ _ isosε .fwd ∘ K× (X̂ ε̂₁) (Ŷ ε̂₁) .bwd) ∘ ℰP.strong-prod-m (fmorη Γ (X̂ δ̂₁) (sfP gs₁)) (fmorη Γ (Ŷ δ̂₁) (sfQ gs₁))
          ≈⟨ ∘-cong₁ (prodIso-bwd ε̂₁ ε̂₂ isosε) ⟩
            (K× (X̂ ε̂₂) (Ŷ ε̂₂) .bwd ∘ ℰP.prod-m (CP .iso ε̂₁ ε̂₂ isosε .fwd) (CQ .iso ε̂₁ ε̂₂ isosε .fwd)) ∘ ℰP.strong-prod-m (fmorη Γ (X̂ δ̂₁) (sfP gs₁)) (fmorη Γ (Ŷ δ̂₁) (sfQ gs₁))
          ≈⟨ assoc _ _ _ ⟩
            K× (X̂ ε̂₂) (Ŷ ε̂₂) .bwd ∘ (ℰP.prod-m (CP .iso ε̂₁ ε̂₂ isosε .fwd) (CQ .iso ε̂₁ ε̂₂ isosε .fwd) ∘ ℰP.strong-prod-m (fmorη Γ (X̂ δ̂₁) (sfP gs₁)) (fmorη Γ (Ŷ δ̂₁) (sfQ gs₁)))
          ≈⟨ ∘-cong₂ (ℰP.strong-prod-m-post _ _ _ _) ⟩
            mid
          ∎ where open ≈-Reasoning isEquiv

invariance-prod {n} {P} {Q} CP CQ .iso = ProdCase.prodIso CP CQ
invariance-prod {n} {P} {Q} CP CQ .natural = ProdCase.prodNat CP CQ
invariance-prod {n} {P} {Q} CP CQ .comp = ProdCase.prodComp CP CQ

-- Extend an isomorphism family by an isomorphism at the bound entry.
mixed : ∀ {n} {δ̂₁ δ̂₂ : Fin n → FM.Obj}
        (isos : ∀ i → Iso (realise .fobj (δ̂₁ i)) (realise .fobj (δ̂₂ i)))
        {Ŷ₁ Ŷ₂ : FM.Obj} (J : Iso (realise .fobj Ŷ₁) (realise .fobj Ŷ₂)) →
        ∀ i → Iso (realise .fobj (extend δ̂₁ Ŷ₁ i)) (realise .fobj (extend δ̂₂ Ŷ₂ i))
mixed isos J Fin.zero    = J
mixed isos J (Fin.suc i) = isos i

-- The strong action at extended environments commutes with an isomorphism at
-- the bound entry and the given isomorphisms elsewhere.
cross-mixed : ∀ {n} (Q : Poly ℰ (suc n)) (CQ : InvarianceAt Q) {Γ : obj}
              {δ̂₁ δ̂₂ ε̂₁ ε̂₂ : Fin n → FM.Obj}
              (isosδ : ∀ i → Iso (realise .fobj (δ̂₁ i)) (realise .fobj (δ̂₂ i)))
              (isosε : ∀ i → Iso (realise .fobj (ε̂₁ i)) (realise .fobj (ε̂₂ i)))
              {Ŷ₁ Ŷ₂ : FM.Obj} (J : Iso (realise .fobj Ŷ₁) (realise .fobj Ŷ₂))
              (gs₁ : ∀ i → FM.Mor (FamP.prod (η .fobj Γ) (δ̂₁ i)) (ε̂₁ i))
              (gs₂ : ∀ i → FM.Mor (FamP.prod (η .fobj Γ) (δ̂₂ i)) (ε̂₂ i)) →
              (∀ i → fmorη Γ (δ̂₂ i) (gs₂ i) ∘co (isosδ i .fwd ∘ ℰP.p₂)
                     ≈ isosε i .fwd ∘ fmorη Γ (δ̂₁ i) (gs₁ i)) →
              fmorη Γ (FM.fobj FM.μObj (Poly-map η Q) (extend δ̂₂ Ŷ₂))
                 (FMu.strong-fmor (Poly-map η Q) (FMu.strong-extend-mor gs₂ FamP.p₂))
                ∘co (CQ .iso (extend δ̂₁ Ŷ₁) (extend δ̂₂ Ŷ₂) (mixed isosδ J) .fwd ∘ ℰP.p₂)
              ≈ CQ .iso (extend ε̂₁ Ŷ₁) (extend ε̂₂ Ŷ₂) (mixed isosε J) .fwd
                 ∘ fmorη Γ (FM.fobj FM.μObj (Poly-map η Q) (extend δ̂₁ Ŷ₁))
                     (FMu.strong-fmor (Poly-map η Q) (FMu.strong-extend-mor gs₁ FamP.p₂))
cross-mixed Q CQ {Γ} {δ̂₁} {δ̂₂} {ε̂₁} {ε̂₂} isosδ isosε {Ŷ₁} {Ŷ₂} J gs₁ gs₂ sqs =
  CQ .natural (extend δ̂₁ Ŷ₁) (extend δ̂₂ Ŷ₂) (mixed isosδ J) (mixed isosε J)
    (FMu.strong-extend-mor gs₁ FamP.p₂)
    (FMu.strong-extend-mor gs₂ FamP.p₂)
    compats
  where
    compats : ∀ i → fmorη Γ (extend δ̂₂ Ŷ₂ i) (FMu.strong-extend-mor gs₂ FamP.p₂ i) ∘co (mixed isosδ J i .fwd ∘ ℰP.p₂)
              ≈ mixed isosε J i .fwd ∘ fmorη Γ (extend δ̂₁ Ŷ₁ i) (FMu.strong-extend-mor gs₁ FamP.p₂ i)
    compats Fin.zero    = sq-p₂ J
    compats (Fin.suc i) = sqs i

-- A invariance at realisations of pure Fam(ℰ) morphisms is the realised plain
-- action.
pure-invariance : ∀ {n} (Q : Poly ℰ (suc n)) (CQ' : InvarianceAt Q) (δ̂₁ δ̂₂ : Fin (suc n) → FM.Obj)
                (ms : ∀ i → FM.Mor (δ̂₁ i) (δ̂₂ i))
                (isos : ∀ i → Iso (realise .fobj (δ̂₁ i)) (realise .fobj (δ̂₂ i))) →
                (∀ i → isos i .fwd ≈ realise .fmor (ms i)) →
                CQ' .iso δ̂₁ δ̂₂ isos .fwd ≈ realise .fmor (FMu.fmor (Poly-map η Q) ms)
pure-invariance {n} Q CQ' δ̂₁ δ̂₂ ms isos hyps =
  p₂-cancel (≈-trans (≈-sym strip₁) (≈-trans (CQ' .natural δ̂₁ δ̂₂ isos (λ i → Iso-refl) (λ i → FM.Mor-∘ (ms i) (FamP.p₂ {x = η .fobj ℰT'.witness} {y = δ̂₁ i})) (λ i → FamP.p₂ {x = η .fobj ℰT'.witness} {y = δ̂₂ i}) sqs) strip₂))
  where
    strip₁ : fmorη ℰT'.witness (FM.fobj FM.μObj (Poly-map η Q) δ̂₂) (FMu.strong-fmor (Poly-map η Q) (λ i → FamP.p₂ {x = η .fobj ℰT'.witness} {y = δ̂₂ i}))
              ∘co (CQ' .iso δ̂₁ δ̂₂ isos .fwd ∘ ℰP.p₂)
             ≈ CQ' .iso δ̂₁ δ̂₂ isos .fwd ∘ ℰP.p₂
    strip₁ =
      ≈-trans (CoK.∘-cong₁ (≈-trans (fmorη-cong (FMuI.strong-fmor-p₂ (Poly-map η Q))) (fmorη-p₂ ℰT'.witness _)))
        (CoK.id-left {Γ = ℰT'.witness})

    strip₂ : CQ' .iso δ̂₂ δ̂₂ (λ i → Iso-refl) .fwd
              ∘ fmorη ℰT'.witness (FM.fobj FM.μObj (Poly-map η Q) δ̂₁) (FMu.strong-fmor (Poly-map η Q) (λ i → FM.Mor-∘ (ms i) (FamP.p₂ {x = η .fobj ℰT'.witness} {y = δ̂₁ i})))
             ≈ realise .fmor (FMu.fmor (Poly-map η Q) ms) ∘ ℰP.p₂
    strip₂ =
      ≈-trans (∘-cong₁ (invariance-refl Q CQ' δ̂₂ (λ i → Iso-refl) (λ i → ≈-refl)))
        (≈-trans id-left
          (≈-trans (fmorη-cong (FamC.≈-sym (sf-pure Q δ̂₁ δ̂₂ ms)))
            (fmorη-pure ℰT'.witness (FM.fobj FM.μObj (Poly-map η Q) δ̂₁) (FMu.fmor (Poly-map η Q) ms))))

    sqs : ∀ i → fmorη ℰT'.witness (δ̂₂ i) (FamP.p₂ {x = η .fobj ℰT'.witness} {y = δ̂₂ i}) ∘co (isos i .fwd ∘ ℰP.p₂)
                ≈ Iso-refl .fwd ∘ fmorη ℰT'.witness (δ̂₁ i) (FM.Mor-∘ (ms i) (FamP.p₂ {x = η .fobj ℰT'.witness} {y = δ̂₁ i}))
    sqs i =
      ≈-trans (CoK.∘-cong₁ (fmorη-p₂ ℰT'.witness (δ̂₂ i)))
        (≈-trans (CoK.id-left {Γ = ℰT'.witness})
          (≈-trans (∘-cong₁ (hyps i))
            (≈-sym (≈-trans id-left (fmorη-pure ℰT'.witness (δ̂₁ i) (ms i))))))
