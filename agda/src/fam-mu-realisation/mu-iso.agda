{-# OPTIONS --prop --postfix-projections --safe #-}

-- The μ-collapse: environment collapse at μ-polynomials, by uniqueness of
-- folds; its identity and composition coherences and algebra-map squares.

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
import fam-mu-realisation.initial

module fam-mu-realisation.mu-iso {o m e} (os es : Level) {ℰ : Category o m e}
  (ℰC : ∀ (A : Setoid os (os ⊔ es)) → HasColimits (setoid→category A) ℰ)
  (ℰT : HasTerminal ℰ) (ℰP : HasProducts ℰ) (ℰE : HasExponentials ℰ ℰP)
  (ℰSC : HasStrongCoproducts ℰ ℰP)
  where

open fam-mu-realisation.initial os es ℰC ℰT ℰP ℰE ℰSC public

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
      (≈-trans (≈-sym (assoc _ _ _)) (co-iso-cancel (GI A) (crossΓ h)))

  -- Fusion of a fold against a composed algebra morphism, both directions.
  square-p₂₁ : (ℰP.p₂ ∘co (M₁.inR ∘ ℰP.p₂)) ≈ ((M₁.inR ∘ ℰP.p₂) ∘co Gmap Q δ̂₁ ℰP.p₂)
  square-p₂₁ =
    ≈-trans (CoK.id-left {Γ = 𝟙})
      (≈-sym (≈-trans (CoK.∘-cong₂ (Gmap-id Q δ̂₁)) (CoK.id-right {Γ = 𝟙})))

  square-p₂₂ : (ℰP.p₂ ∘co (M₂.inR ∘ ℰP.p₂)) ≈ ((M₂.inR ∘ ℰP.p₂) ∘co Gmap Q δ̂₂ ℰP.p₂)
  square-p₂₂ =
    ≈-trans (CoK.id-left {Γ = 𝟙})
      (≈-sym (≈-trans (CoK.∘-cong₂ (Gmap-id Q δ̂₂)) (CoK.id-right {Γ = 𝟙})))

  ag-cross : ((M₁.inR ∘ (GI (Creal Q δ̂₁) .Iso.bwd ∘ ℰP.p₂)) ∘co (GI (Creal Q δ̂₁) .Iso.fwd ∘ Gmap Q δ̂₁ G'))
             ≈ ((M₁.inR ∘ ℰP.p₂) ∘co Gmap Q δ̂₁ G')
  ag-cross =
    begin
      (M₁.inR ∘ (GI (Creal Q δ̂₁) .Iso.bwd ∘ ℰP.p₂)) ∘ ℰP.pair ℰP.p₁ (GI (Creal Q δ̂₁) .Iso.fwd ∘ Gmap Q δ̂₁ G')
    ≈⟨ assoc _ _ _ ⟩
      M₁.inR ∘ ((GI (Creal Q δ̂₁) .Iso.bwd ∘ ℰP.p₂) ∘ ℰP.pair ℰP.p₁ (GI (Creal Q δ̂₁) .Iso.fwd ∘ Gmap Q δ̂₁ G'))
    ≈⟨ ∘-cong₂ (≈-trans (assoc _ _ _) (∘-cong₂ (ℰP.pair-p₂ _ _))) ⟩
      M₁.inR ∘ (GI (Creal Q δ̂₁) .Iso.bwd ∘ (GI (Creal Q δ̂₁) .Iso.fwd ∘ Gmap Q δ̂₁ G'))
    ≈˘⟨ ∘-cong₂ (assoc _ _ _) ⟩
      M₁.inR ∘ ((GI (Creal Q δ̂₁) .Iso.bwd ∘ GI (Creal Q δ̂₁) .Iso.fwd) ∘ Gmap Q δ̂₁ G')
    ≈⟨ ∘-cong₂ (≈-trans (∘-cong₁ (GI (Creal Q δ̂₁) .Iso.bwd∘fwd≈id)) id-left) ⟩
      M₁.inR ∘ Gmap Q δ̂₁ G'
    ≈˘⟨ ≈-trans (assoc _ _ _) (∘-cong₂ (ℰP.pair-p₂ _ _)) ⟩
      (M₁.inR ∘ ℰP.p₂) ∘ ℰP.pair ℰP.p₁ (Gmap Q δ̂₁ G')
    ∎ where open ≈-Reasoning isEquiv


  -- The composite G' ∘co F' satisfies the fold square for the algebra of the identity.
  square-GF : ((G' ∘co F') ∘co (M₁.inR ∘ ℰP.p₂)) ≈ ((M₁.inR ∘ ℰP.p₂) ∘co Gmap Q δ̂₁ (G' ∘co F'))
  square-GF =
    begin
      (G' ∘co F') ∘co (M₁.inR ∘ ℰP.p₂)
    ≈⟨ CoK.assoc _ _ _ ⟩
      G' ∘co (F' ∘co (M₁.inR ∘ ℰP.p₂))
    ≈⟨ CoK.∘-cong₂ (M₁.foldR-β _) ⟩
      G' ∘co ((M₂.inR ∘ (GI (Creal Q δ̂₂) .Iso.fwd ∘ ℰP.p₂)) ∘co Gmap Q δ̂₁ F')
    ≈⟨ CoK.∘-cong₂ (CoK.∘-cong₁ (≈-trans (≈-sym (assoc _ _ _)) (≈-sym (co-pure M₂.inR (GI (Creal Q δ̂₂) .Iso.fwd))))) ⟩
      G' ∘co (((M₂.inR ∘ ℰP.p₂) ∘co (GI (Creal Q δ̂₂) .Iso.fwd ∘ ℰP.p₂)) ∘co Gmap Q δ̂₁ F')
    ≈˘⟨ CoK.assoc _ _ _ ⟩
      (G' ∘co ((M₂.inR ∘ ℰP.p₂) ∘co (GI (Creal Q δ̂₂) .Iso.fwd ∘ ℰP.p₂))) ∘co Gmap Q δ̂₁ F'
    ≈˘⟨ CoK.∘-cong₁ (CoK.assoc _ _ _) ⟩
      ((G' ∘co (M₂.inR ∘ ℰP.p₂)) ∘co (GI (Creal Q δ̂₂) .Iso.fwd ∘ ℰP.p₂)) ∘co Gmap Q δ̂₁ F'
    ≈⟨ CoK.∘-cong₁ (CoK.∘-cong₁ (M₂.foldR-β _)) ⟩
      (((M₁.inR ∘ (GI (Creal Q δ̂₁) .Iso.bwd ∘ ℰP.p₂)) ∘co Gmap Q δ̂₂ G') ∘co (GI (Creal Q δ̂₂) .Iso.fwd ∘ ℰP.p₂)) ∘co Gmap Q δ̂₁ F'
    ≈⟨ CoK.∘-cong₁ (CoK.assoc _ _ _) ⟩
      ((M₁.inR ∘ (GI (Creal Q δ̂₁) .Iso.bwd ∘ ℰP.p₂)) ∘co (Gmap Q δ̂₂ G' ∘co (GI (Creal Q δ̂₂) .Iso.fwd ∘ ℰP.p₂))) ∘co Gmap Q δ̂₁ F'
    ≈⟨ CoK.∘-cong₁ (CoK.∘-cong₂ (crossΓ G')) ⟩
      ((M₁.inR ∘ (GI (Creal Q δ̂₁) .Iso.bwd ∘ ℰP.p₂)) ∘co (GI (Creal Q δ̂₁) .Iso.fwd ∘ Gmap Q δ̂₁ G')) ∘co Gmap Q δ̂₁ F'
    ≈⟨ CoK.∘-cong₁ ag-cross ⟩
      ((M₁.inR ∘ ℰP.p₂) ∘co Gmap Q δ̂₁ G') ∘co Gmap Q δ̂₁ F'
    ≈⟨ CoK.assoc _ _ _ ⟩
      (M₁.inR ∘ ℰP.p₂) ∘co (Gmap Q δ̂₁ G' ∘co Gmap Q δ̂₁ F')
    ≈˘⟨ CoK.∘-cong₂ (Gmap-∘co Q δ̂₁ G' F') ⟩
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
    ≈⟨ ∘-cong₂ (≈-trans (assoc _ _ _) (∘-cong₂ (ℰP.pair-p₂ _ _))) ⟩
      M₂.inR ∘ (GI (Creal Q δ̂₂) .Iso.fwd ∘ (GI (Creal Q δ̂₂) .Iso.bwd ∘ Gmap Q δ̂₂ F'))
    ≈˘⟨ ∘-cong₂ (assoc _ _ _) ⟩
      M₂.inR ∘ ((GI (Creal Q δ̂₂) .Iso.fwd ∘ GI (Creal Q δ̂₂) .Iso.bwd) ∘ Gmap Q δ̂₂ F')
    ≈⟨ ∘-cong₂ (≈-trans (∘-cong₁ (GI (Creal Q δ̂₂) .Iso.fwd∘bwd≈id)) id-left) ⟩
      M₂.inR ∘ Gmap Q δ̂₂ F'
    ≈˘⟨ ≈-trans (assoc _ _ _) (∘-cong₂ (ℰP.pair-p₂ _ _)) ⟩
      (M₂.inR ∘ ℰP.p₂) ∘ ℰP.pair ℰP.p₁ (Gmap Q δ̂₂ F')
    ∎ where open ≈-Reasoning isEquiv


  -- The composite F' ∘co G' likewise, using the flipped crossing.
  square-FG : ((F' ∘co G') ∘co (M₂.inR ∘ ℰP.p₂)) ≈ ((M₂.inR ∘ ℰP.p₂) ∘co Gmap Q δ̂₂ (F' ∘co G'))
  square-FG =
    begin
      (F' ∘co G') ∘co (M₂.inR ∘ ℰP.p₂)
    ≈⟨ CoK.assoc _ _ _ ⟩
      F' ∘co (G' ∘co (M₂.inR ∘ ℰP.p₂))
    ≈⟨ CoK.∘-cong₂ (M₂.foldR-β _) ⟩
      F' ∘co ((M₁.inR ∘ (GI (Creal Q δ̂₁) .Iso.bwd ∘ ℰP.p₂)) ∘co Gmap Q δ̂₂ G')
    ≈⟨ CoK.∘-cong₂ (CoK.∘-cong₁ (≈-trans (≈-sym (assoc _ _ _)) (≈-sym (co-pure M₁.inR (GI (Creal Q δ̂₁) .Iso.bwd))))) ⟩
      F' ∘co (((M₁.inR ∘ ℰP.p₂) ∘co (GI (Creal Q δ̂₁) .Iso.bwd ∘ ℰP.p₂)) ∘co Gmap Q δ̂₂ G')
    ≈˘⟨ CoK.assoc _ _ _ ⟩
      (F' ∘co ((M₁.inR ∘ ℰP.p₂) ∘co (GI (Creal Q δ̂₁) .Iso.bwd ∘ ℰP.p₂))) ∘co Gmap Q δ̂₂ G'
    ≈˘⟨ CoK.∘-cong₁ (CoK.assoc _ _ _) ⟩
      ((F' ∘co (M₁.inR ∘ ℰP.p₂)) ∘co (GI (Creal Q δ̂₁) .Iso.bwd ∘ ℰP.p₂)) ∘co Gmap Q δ̂₂ G'
    ≈⟨ CoK.∘-cong₁ (CoK.∘-cong₁ (M₁.foldR-β _)) ⟩
      (((M₂.inR ∘ (GI (Creal Q δ̂₂) .Iso.fwd ∘ ℰP.p₂)) ∘co Gmap Q δ̂₁ F') ∘co (GI (Creal Q δ̂₁) .Iso.bwd ∘ ℰP.p₂)) ∘co Gmap Q δ̂₂ G'
    ≈⟨ CoK.∘-cong₁ (CoK.assoc _ _ _) ⟩
      ((M₂.inR ∘ (GI (Creal Q δ̂₂) .Iso.fwd ∘ ℰP.p₂)) ∘co (Gmap Q δ̂₁ F' ∘co (GI (Creal Q δ̂₁) .Iso.bwd ∘ ℰP.p₂))) ∘co Gmap Q δ̂₂ G'
    ≈⟨ CoK.∘-cong₁ (CoK.∘-cong₂ (cross-flip F')) ⟩
      ((M₂.inR ∘ (GI (Creal Q δ̂₂) .Iso.fwd ∘ ℰP.p₂)) ∘co (GI (Creal Q δ̂₂) .Iso.bwd ∘ Gmap Q δ̂₂ F')) ∘co Gmap Q δ̂₂ G'
    ≈⟨ CoK.∘-cong₁ af-cross ⟩
      ((M₂.inR ∘ ℰP.p₂) ∘co Gmap Q δ̂₂ F') ∘co Gmap Q δ̂₂ G'
    ≈⟨ CoK.assoc _ _ _ ⟩
      (M₂.inR ∘ ℰP.p₂) ∘co (Gmap Q δ̂₂ F' ∘co Gmap Q δ̂₂ G')
    ≈˘⟨ CoK.∘-cong₂ (Gmap-∘co Q δ̂₂ F' G') ⟩
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
    ≈⟨ ∘-cong₂ (ℰP.pair-natural _ _ _) ⟩
      u ∘ ℰP.pair (ℰTm.to-terminal ∘ (v ∘ ℰP.pair ℰTm.to-terminal (id _))) (id _ ∘ (v ∘ ℰP.pair ℰTm.to-terminal (id _)))
    ≈⟨ ∘-cong₂ (ℰP.pair-cong (ℰTm.to-terminal-unique _ _) id-left) ⟩
      u ∘ ℰP.pair (ℰP.p₁ ∘ ℰP.pair ℰTm.to-terminal (id _)) (v ∘ ℰP.pair ℰTm.to-terminal (id _))
    ≈˘⟨ ∘-cong₂ (ℰP.pair-natural _ _ _) ⟩
      u ∘ (ℰP.pair ℰP.p₁ v ∘ ℰP.pair ℰTm.to-terminal (id _))
    ≈˘⟨ assoc _ _ _ ⟩
      (u ∘ ℰP.pair ℰP.p₁ v) ∘ ℰP.pair ℰTm.to-terminal (id _)
    ∎ where open ≈-Reasoning isEquiv

  mu-collapse : Iso (Creal Q δ̂₁) (Creal Q δ̂₂)
  mu-collapse .Iso.fwd = F' ∘ ℰP.pair ℰTm.to-terminal (id _)
  mu-collapse .Iso.bwd = G' ∘ ℰP.pair ℰTm.to-terminal (id _)
  mu-collapse .Iso.bwd∘fwd≈id =
    ≈-trans (plait G' F')
      (≈-trans (∘-cong₁ (≈-trans (M₁.foldR-η _ _ square-GF) (≈-sym (M₁.foldR-η {Γ = 𝟙} _ _ square-p₂₁))))
        (ℰP.pair-p₂ _ _))
  mu-collapse .Iso.fwd∘bwd≈id =
    ≈-trans (plait F' G')
      (≈-trans (∘-cong₁ (≈-trans (M₂.foldR-η _ _ square-FG) (≈-sym (M₂.foldR-η {Γ = 𝟙} _ _ square-p₂₂))))
        (ℰP.pair-p₂ _ _))

-- The μ-collapse at pointwise-identity isomorphisms is the identity.
mu-collapse-refl : ∀ {n} (Q : Poly ℰ (suc n)) (CQ : CollapseAt Q) (δ̂ : Fin n → FM.Obj)
                   (isos : ∀ i → Iso (realise .fobj (δ̂ i)) (realise .fobj (δ̂ i))) →
                   (∀ i → isos i .Iso.fwd ≈ id _) →
                   MuCollapse.mu-collapse Q CQ δ̂ δ̂ isos .Iso.fwd ≈ id _
mu-collapse-refl {n} Q CQ δ̂ isos hyps =
  begin
    MC.F' ∘ ℰP.pair MC.ℰTm.to-terminal (id _)
  ≈⟨ ∘-cong₁ F'-id ⟩
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
          (∘-cong₂ (≈-trans (∘-cong₁ (GI-id (Creal Q δ̂))) id-left)))
        (≈-sym (MC.M₁.foldR-η {Γ = MC.𝟙} _ ℰP.p₂ MC.square-p₂₁))

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
      (∘-cong₂
        (≈-trans (≈-trans (assoc _ _ _) (∘-cong₂ (ℰP.pair-p₂ _ _)))
          (∘-cong₂ (∘-cong₁ (Gmap-cong Q δ̂₁ plain-eq))))))
  where
    module MC = MuCollapse Q CQ δ̂₁ δ̂₂ isos

    plain-eq : MC.F' ≈ (MC.mu-collapse .Iso.fwd ∘ ℰP.p₂)
    plain-eq =
      ≈-sym (≈-trans (assoc _ _ _) (≈-trans (∘-cong₂ sect-p₂) id-right))

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
      (∘-cong₂
        (≈-trans (≈-trans (assoc _ _ _) (∘-cong₂ (ℰP.pair-p₂ _ _)))
          (∘-cong₂ (∘-cong₁ (Gmap-cong Q δ̂₂ plain-eq))))))
  where
    module MC = MuCollapse Q CQ δ̂₁ δ̂₂ isos

    plain-eq : MC.G' ≈ (MC.mu-collapse .Iso.bwd ∘ ℰP.p₂)
    plain-eq =
      ≈-sym (≈-trans (assoc _ _ _) (≈-trans (∘-cong₂ sect-p₂) id-right))

-- The μ-collapse at a composite isomorphism family is the composite of the
-- μ-collapses.
mu-collapse-comp : ∀ {n} (Q : Poly ℰ (suc n)) (CQ : CollapseAt Q)
                   (δ̂₁ δ̂₂ δ̂₃ : Fin n → FM.Obj)
                   (isos₁₂ : ∀ i → Iso (realise .fobj (δ̂₁ i)) (realise .fobj (δ̂₂ i)))
                   (isos₂₃ : ∀ i → Iso (realise .fobj (δ̂₂ i)) (realise .fobj (δ̂₃ i))) →
                   MuCollapse.mu-collapse Q CQ δ̂₁ δ̂₃ (λ i → Iso-trans (isos₁₂ i) (isos₂₃ i)) .Iso.fwd
                   ≈ (MuCollapse.mu-collapse Q CQ δ̂₂ δ̂₃ isos₂₃ .Iso.fwd ∘ MuCollapse.mu-collapse Q CQ δ̂₁ δ̂₂ isos₁₂ .Iso.fwd)
mu-collapse-comp {n} Q CQ δ̂₁ δ̂₂ δ̂₃ isos₁₂ isos₂₃ =
  ≈-trans (∘-cong₁ (≈-sym (MC₁₃.M₁.foldR-η {Γ = ℰT'.witness} _ (MC₂₃.F' ∘co MC₁₂.F') square)))
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


    head-comp : ((MC₂₃.M₂.inR ∘ (MC₂₃.GI C₃ .Iso.fwd ∘ ℰP.p₂)) ∘co (MC₁₂.GI C₃ .Iso.fwd ∘ ℰP.p₂))
                ≈ (MC₁₃.M₂.inR ∘ (MC₁₃.GI C₃ .Iso.fwd ∘ ℰP.p₂))
    head-comp =
      begin
        (MC₂₃.M₂.inR ∘ (MC₂₃.GI C₃ .Iso.fwd ∘ ℰP.p₂)) ∘co (MC₁₂.GI C₃ .Iso.fwd ∘ ℰP.p₂)
      ≈˘⟨ CoK.∘-cong₁ (assoc _ _ _) ⟩
        ((MC₂₃.M₂.inR ∘ MC₂₃.GI C₃ .Iso.fwd) ∘ ℰP.p₂) ∘co (MC₁₂.GI C₃ .Iso.fwd ∘ ℰP.p₂)
      ≈⟨ co-pure _ _ ⟩
        ((MC₂₃.M₂.inR ∘ MC₂₃.GI C₃ .Iso.fwd) ∘ MC₁₂.GI C₃ .Iso.fwd) ∘ ℰP.p₂
      ≈⟨ ∘-cong₁ (assoc _ _ _) ⟩
        (MC₂₃.M₂.inR ∘ (MC₂₃.GI C₃ .Iso.fwd ∘ MC₁₂.GI C₃ .Iso.fwd)) ∘ ℰP.p₂
      ≈⟨ ∘-cong₁ (∘-cong₂ GIcomp) ⟩
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
      ≈⟨ CoK.∘-cong₂ (MC₁₂.M₁.foldR-β _) ⟩
        MC₂₃.F' ∘co ((MC₁₂.M₂.inR ∘ (MC₁₂.GI (Creal Q δ̂₂) .Iso.fwd ∘ ℰP.p₂)) ∘co Gmap Q δ̂₁ MC₁₂.F')
      ≈⟨ CoK.∘-cong₂ (CoK.∘-cong₁ (≈-trans (≈-sym (assoc _ _ _)) (≈-sym (co-pure _ _)))) ⟩
        MC₂₃.F' ∘co (((MC₁₂.M₂.inR ∘ ℰP.p₂) ∘co (MC₁₂.GI (Creal Q δ̂₂) .Iso.fwd ∘ ℰP.p₂)) ∘co Gmap Q δ̂₁ MC₁₂.F')
      ≈⟨ CoK.∘-cong₂ (CoK.assoc _ _ _) ⟩
        MC₂₃.F' ∘co ((MC₁₂.M₂.inR ∘ ℰP.p₂) ∘co ((MC₁₂.GI (Creal Q δ̂₂) .Iso.fwd ∘ ℰP.p₂) ∘co Gmap Q δ̂₁ MC₁₂.F'))
      ≈˘⟨ CoK.assoc _ _ _ ⟩
        (MC₂₃.F' ∘co (MC₂₃.M₁.inR ∘ ℰP.p₂)) ∘co ((MC₁₂.GI (Creal Q δ̂₂) .Iso.fwd ∘ ℰP.p₂) ∘co Gmap Q δ̂₁ MC₁₂.F')
      ≈⟨ CoK.∘-cong₁ (MC₂₃.M₁.foldR-β _) ⟩
        ((MC₂₃.M₂.inR ∘ (MC₂₃.GI C₃ .Iso.fwd ∘ ℰP.p₂)) ∘co Gmap Q δ̂₂ MC₂₃.F') ∘co ((MC₁₂.GI (Creal Q δ̂₂) .Iso.fwd ∘ ℰP.p₂) ∘co Gmap Q δ̂₁ MC₁₂.F')
      ≈⟨ CoK.assoc _ _ _ ⟩
        (MC₂₃.M₂.inR ∘ (MC₂₃.GI C₃ .Iso.fwd ∘ ℰP.p₂)) ∘co (Gmap Q δ̂₂ MC₂₃.F' ∘co ((MC₁₂.GI (Creal Q δ̂₂) .Iso.fwd ∘ ℰP.p₂) ∘co Gmap Q δ̂₁ MC₁₂.F'))
      ≈˘⟨ CoK.∘-cong₂ (CoK.assoc _ _ _) ⟩
        (MC₂₃.M₂.inR ∘ (MC₂₃.GI C₃ .Iso.fwd ∘ ℰP.p₂)) ∘co ((Gmap Q δ̂₂ MC₂₃.F' ∘co (MC₁₂.GI (Creal Q δ̂₂) .Iso.fwd ∘ ℰP.p₂)) ∘co Gmap Q δ̂₁ MC₁₂.F')
      ≈⟨ CoK.∘-cong₂ (CoK.∘-cong₁ (MC₁₂.crossΓ MC₂₃.F')) ⟩
        (MC₂₃.M₂.inR ∘ (MC₂₃.GI C₃ .Iso.fwd ∘ ℰP.p₂)) ∘co ((MC₁₂.GI C₃ .Iso.fwd ∘ Gmap Q δ̂₁ MC₂₃.F') ∘co Gmap Q δ̂₁ MC₁₂.F')
      ≈⟨ CoK.∘-cong₂ (CoK.∘-cong₁ (≈-sym (≈-trans (assoc _ _ _) (∘-cong₂ (ℰP.pair-p₂ _ _))))) ⟩
        (MC₂₃.M₂.inR ∘ (MC₂₃.GI C₃ .Iso.fwd ∘ ℰP.p₂)) ∘co (((MC₁₂.GI C₃ .Iso.fwd ∘ ℰP.p₂) ∘co Gmap Q δ̂₁ MC₂₃.F') ∘co Gmap Q δ̂₁ MC₁₂.F')
      ≈⟨ CoK.∘-cong₂ (CoK.assoc _ _ _) ⟩
        (MC₂₃.M₂.inR ∘ (MC₂₃.GI C₃ .Iso.fwd ∘ ℰP.p₂)) ∘co ((MC₁₂.GI C₃ .Iso.fwd ∘ ℰP.p₂) ∘co (Gmap Q δ̂₁ MC₂₃.F' ∘co Gmap Q δ̂₁ MC₁₂.F'))
      ≈˘⟨ CoK.assoc _ _ _ ⟩
        ((MC₂₃.M₂.inR ∘ (MC₂₃.GI C₃ .Iso.fwd ∘ ℰP.p₂)) ∘co (MC₁₂.GI C₃ .Iso.fwd ∘ ℰP.p₂)) ∘co (Gmap Q δ̂₁ MC₂₃.F' ∘co Gmap Q δ̂₁ MC₁₂.F')
      ≈⟨ CoK.∘-cong head-comp (≈-sym (Gmap-∘co Q δ̂₁ MC₂₃.F' MC₁₂.F')) ⟩
        (MC₁₃.M₂.inR ∘ (MC₁₃.GI C₃ .Iso.fwd ∘ ℰP.p₂)) ∘co Gmap Q δ̂₁ (MC₂₃.F' ∘co MC₁₂.F')
      ∎
      where open ≈-Reasoning isEquiv

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
    (∘-cong₂ (∘-cong₂
      (≈-trans (∘-cong₁ (Gmap-pure Q δ̂₁ (MuCollapse.mu-collapse Q CQ δ̂₁ δ̂₂ isos .Iso.fwd)))
        (≈-trans (assoc _ _ _)
          (≈-trans (∘-cong₂ (ℰP.pair-p₂ _ _)) id-right)))))

mu-collapse-bwd-in' : ∀ {n} (Q : Poly ℰ (suc n)) (CQ : CollapseAt Q)
                      (δ̂₁ δ̂₂ : Fin n → FM.Obj)
                      (isos : ∀ i → Iso (realise .fobj (δ̂₁ i)) (realise .fobj (δ̂₂ i))) →
                      (MuCollapse.mu-collapse Q CQ δ̂₁ δ̂₂ isos .Iso.bwd ∘ Initiality.inR Q δ̂₂ CQ)
                      ≈ (Initiality.inR Q δ̂₁ CQ ∘
                         (MuCollapse.GI Q CQ δ̂₁ δ̂₂ isos (Creal Q δ̂₁) .Iso.bwd ∘
                          realise .fmor (FMu.fmor (Poly-map η Q) (pureExt δ̂₂ (untranspose (MuCollapse.mu-collapse Q CQ δ̂₁ δ̂₂ isos .Iso.bwd ∘ realise-η-iso (Creal Q δ̂₂) .Iso.fwd))))))
mu-collapse-bwd-in' Q CQ δ̂₁ δ̂₂ isos =
  ≈-trans (mu-collapse-bwd-in Q CQ δ̂₁ δ̂₂ isos)
    (∘-cong₂ (∘-cong₂
      (≈-trans (∘-cong₁ (Gmap-pure Q δ̂₂ (MuCollapse.mu-collapse Q CQ δ̂₁ δ̂₂ isos .Iso.bwd)))
        (≈-trans (assoc _ _ _)
          (≈-trans (∘-cong₂ (ℰP.pair-p₂ _ _)) id-right)))))
