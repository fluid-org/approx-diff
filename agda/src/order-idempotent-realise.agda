{-# OPTIONS --prop --postfix-projections --safe #-}

-- The realisation of position orders in plain semimodules: a position order realises as its
-- selection semimodule and a morphism as itself. With the root an isolated position, realising a
-- lifted order is forming the biproduct with the scalars, so the comparison between the two
-- liftings is biproduct preservation and needs no support structure. This replaces the supported
-- realisation, whose bounds existed only to state domination.
open import Level using (0ℓ)
open import Data.Fin using (Fin; zero)
open import commutative-monoid using (CommutativeMonoid)
open import prop using (∃ₛ) renaming (_,_ to _,ₚ_)
open import prop-setoid using (Setoid; IsEquivalence; module ≈-Reasoning)
open import commutative-semiring using (CommutativeSemiring)
open import categories using (Category; HasTerminal; IsTerminal)
open import cmon-enriched
  using (CMonEnriched; Biproduct; biproduct-iso; biproducts→products)
open import functor using (Functor)
open import finite-product-functor using (preserve-chosen-terminal; preserve-chosen-products)
open import lifting using (Lifting)
import lifting-biproduct
import biproduct-transport
import matrix
import semimodule
import order-idempotent
import order-idempotent-roots

module order-idempotent-realise
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (let module S = CommutativeSemiring S)
  (∨-idem    : ∀ {x} → (x S.+ x) S.≈ x)
  (∧-idem    : ∀ {x} → (x S.· x) S.≈ x)
  (⊤-add-top : ∀ {x} → (S.ι S.+ x) S.≈ S.ι)
  where

module M = matrix.Mat S
module OI = order-idempotent S ∨-idem ∧-idem ⊤-add-top
module Roots = order-idempotent-roots S ∨-idem ∧-idem ⊤-add-top
module SemiMod = semimodule S

open OI using (Pos; dim; ord)
open SemiMod using (Semimodule; 𝕀)
open SemiMod._⇒_
open SemiMod._≈m_
open Functor
open Category SemiMod.cat
open CMonEnriched SemiMod.cmon-enriched
open Biproduct

-- The realisation: the selection semimodule, the identity on morphisms.
𝓥 : Pos → Semimodule
𝓥 = OI.𝒟

𝓥F : Functor OI.cat SemiMod.cat
𝓥F .fobj = 𝓥
𝓥F .fmor f = f
𝓥F .fmor-cong h = h
𝓥F .fmor-id {P} = OI.≈p-refl {f = OI.id P}
𝓥F .fmor-comp f g = OI.≈p-refl {f = OI._∘_ f g}

-- The empty order realises as the zero module.
𝓥-𝟘-bwd : SemiMod._⇒_ SemiMod.𝟘 (𝓥 OI.𝟘p)
𝓥-𝟘-bwd .*→* .prop-setoid._⇒_.func _ = (λ ()) ,ₚ (λ ())
𝓥-𝟘-bwd .*→* .prop-setoid._⇒_.func-resp-≈ _ = λ ()
𝓥-𝟘-bwd .preserve-ze = λ ()
𝓥-𝟘-bwd .preserve-+ = λ ()
𝓥-𝟘-bwd .preserve-· = λ ()

𝓥F-preserve-terminal : preserve-chosen-terminal 𝓥F OI.terminal SemiMod.terminal
𝓥F-preserve-terminal .Category.IsIso.inverse = 𝓥-𝟘-bwd
𝓥F-preserve-terminal .Category.IsIso.f∘inverse≈id =
  HasTerminal.to-terminal-unique SemiMod.terminal _ (id _)
𝓥F-preserve-terminal .Category.IsIso.inverse∘f≈id .*≈* .prop-setoid._≃m_.func-eq _ = λ ()

-- The realised biproduct on the image of a block order: the laws are those of the position-order
-- biproduct, since morphisms realise as themselves.
𝓥-image-biproduct : ∀ P Q → Biproduct SemiMod.cmon-enriched (𝓥 P) (𝓥 Q)
𝓥-image-biproduct P Q .prod = 𝓥 (P OI.⊕ Q)
𝓥-image-biproduct P Q .p₁ = OI.π₁ P Q
𝓥-image-biproduct P Q .p₂ = OI.π₂ P Q
𝓥-image-biproduct P Q .in₁ = OI.ι₁ P Q
𝓥-image-biproduct P Q .in₂ = OI.ι₂ P Q
𝓥-image-biproduct P Q .id-1 = OI.biproduct P Q .id-1
𝓥-image-biproduct P Q .id-2 = OI.biproduct P Q .id-2
𝓥-image-biproduct P Q .zero-1 = OI.biproduct P Q .zero-1
𝓥-image-biproduct P Q .zero-2 = OI.biproduct P Q .zero-2
𝓥-image-biproduct P Q .id-+ = OI.biproduct P Q .id-+

𝓥F-preserve-products :
  preserve-chosen-products 𝓥F (biproducts→products OI.cmon OI.biproduct)
    (biproducts→products SemiMod.cmon-enriched SemiMod.biproduct)
𝓥F-preserve-products {P} {Q} =
  biproduct-iso SemiMod.cmon-enriched (𝓥-image-biproduct P Q) (SemiMod.biproduct (𝓥 P) (𝓥 Q))

-- The one-position order realises as the scalars.
disc-fixed : ∀ {n} (v : M.Vec n) → OI.Fixed (OI.disc n) v
disc-fixed v i = M.Σ-unit i v

scalar : Setoid.Carrier A → ∃ₛ (M.Vec 1) (OI.Fixed Roots.𝟙p)
scalar a = (λ _ → a) ,ₚ disc-fixed (λ _ → a)

ι1-fwd : SemiMod._⇒_ (𝓥 Roots.𝟙p) 𝕀
ι1-fwd .*→* .prop-setoid._⇒_.func (v ,ₚ _) = v zero
ι1-fwd .*→* .prop-setoid._⇒_.func-resp-≈ e = e zero
ι1-fwd .preserve-ze = S.refl
ι1-fwd .preserve-+ = S.refl
ι1-fwd .preserve-· = S.refl

ι1-bwd : SemiMod._⇒_ 𝕀 (𝓥 Roots.𝟙p)
ι1-bwd .*→* .prop-setoid._⇒_.func = scalar
ι1-bwd .*→* .prop-setoid._⇒_.func-resp-≈ e i = e
ι1-bwd .preserve-ze i = S.refl
ι1-bwd .preserve-+ i = S.refl
ι1-bwd .preserve-· i = S.refl

ι1-fwd∘bwd : SemiMod._≈m_ {𝕀} {𝕀}
               (SemiMod._∘_ {𝕀} {𝓥 Roots.𝟙p} {𝕀} ι1-fwd ι1-bwd) (SemiMod.id 𝕀)
ι1-fwd∘bwd .*≈* .prop-setoid._≃m_.func-eq e = e

ι1-bwd∘fwd : SemiMod._≈m_ {𝓥 Roots.𝟙p} {𝓥 Roots.𝟙p}
               (SemiMod._∘_ {𝓥 Roots.𝟙p} {𝕀} {𝓥 Roots.𝟙p} ι1-bwd ι1-fwd)
               (SemiMod.id (𝓥 Roots.𝟙p))
ι1-bwd∘fwd .*≈* .prop-setoid._≃m_.func-eq e = λ { zero → e zero }


module BT = biproduct-transport SemiMod.cmon-enriched

-- The direct root witness, repackaged over the semimodule enrichment: same morphisms, same laws.
𝓥-root-biproduct : ∀ P → Biproduct SemiMod.cmon-enriched (𝓥 Roots.𝟙p) (𝓥 P)
𝓥-root-biproduct P .prod = 𝓥 (Roots.Lp P)
𝓥-root-biproduct P .p₁ = Roots.root-biproduct P .p₁
𝓥-root-biproduct P .p₂ = Roots.root-biproduct P .p₂
𝓥-root-biproduct P .in₁ = Roots.root-biproduct P .in₁
𝓥-root-biproduct P .in₂ = Roots.root-biproduct P .in₂
𝓥-root-biproduct P .id-1 = Roots.root-biproduct P .id-1
𝓥-root-biproduct P .id-2 = Roots.root-biproduct P .id-2
𝓥-root-biproduct P .zero-1 = Roots.root-biproduct P .zero-1
𝓥-root-biproduct P .zero-2 = Roots.root-biproduct P .zero-2
𝓥-root-biproduct P .id-+ = Roots.root-biproduct P .id-+

-- The realisation of a lifted order is a biproduct of the scalars and the realised payload: the
-- root witness transported along the scalar comparison at the root.
Lp-biproduct : ∀ P → Biproduct SemiMod.cmon-enriched 𝕀 (𝓥 P)
Lp-biproduct P =
  BT.transport₁ (𝓥-root-biproduct P) ι1-fwd ι1-bwd ι1-fwd∘bwd ι1-bwd∘fwd

-- The chosen lifting on the model side: the biproduct with the scalars.
module LsB = lifting-biproduct SemiMod.cmon-enriched 𝕀 (λ X → SemiMod.biproduct 𝕀 X)

Ls-lifting : Lifting SemiMod.cmon-enriched 𝕀
Ls-lifting = LsB.biproduct-lifting

-- The comparison isomorphism between the realised lifted order and the lifted realisation, as the
-- canonical comparison of the two biproducts.
𝓥-Lp-iso : ∀ P → Category.Iso SemiMod.cat (𝓥 (Roots.Lp P)) (Lifting.L Ls-lifting (𝓥 P))
𝓥-Lp-iso P =
  IsIso→Iso (biproduct-iso SemiMod.cmon-enriched (Lp-biproduct P) (SemiMod.biproduct 𝕀 (𝓥 P)))

-- The comparison intertwines the lifted actions: both keep the root and map the payload.
𝓥-Lp-natural : ∀ {P Q} (f : P OI.⇒ Q) →
  SemiMod._≈m_ {𝓥 (Roots.Lp P)} {LsB.Lb (𝓥 Q)}
    (SemiMod._∘_ {𝓥 (Roots.Lp P)} {𝓥 (Roots.Lp Q)} {LsB.Lb (𝓥 Q)}
      (𝓥-Lp-iso Q .Category.Iso.fwd) (Lifting.Lmap Roots.Lp-lifting f))
    (SemiMod._∘_ {𝓥 (Roots.Lp P)} {LsB.Lb (𝓥 P)} {LsB.Lb (𝓥 Q)}
      (Lifting.Lmap Ls-lifting f) (𝓥-Lp-iso P .Category.Iso.fwd))
𝓥-Lp-natural {P} {Q} f =
  BT.compare-natural
    (𝓥-root-biproduct P) (𝓥-root-biproduct Q)
    (SemiMod.biproduct 𝕀 (𝓥 P)) (SemiMod.biproduct 𝕀 (𝓥 Q))
    ι1-fwd ι1-bwd ι1-fwd∘bwd ι1-bwd∘fwd f
