{-# OPTIONS --postfix-projections --prop --safe #-}

-- The rooted higher-order model at position orders: families over the position orders as the
-- first-order side, families over the supported semimodules as the model, the realisation as the
-- change of base, and the dominated products supplying the weak exponentials. The unit object is
-- the lifted terminal, so the unit value carries one root; the primitives are interpreted as in
-- the first-order model, with the relations' booleans injected under the roots.
open import Level using (0ℓ)
import Data.Fin as Fin
open import prop using () renaming (_,_ to _,ₚ_)
open import prop-setoid using (Setoid; IsEquivalence)
open import commutative-semiring using (CommutativeSemiring)
open import categories using (Category; HasTerminal; HasCoproducts; HasWeakExponentials)
open import signature using (Signature; Model; PFPC[_,_,_,_])
open import primitives using (Primitives)
open import finite-product-functor using (preserve-chosen-terminal)
open import indexed-family using (_[_])
import language-syntax
import matrix
import fam
import fam-mu-lifting.in-map
import order-idempotent-supported
import ho-model-order-idempotent
import language-rooted-fo-interpretation

module ho-model-rooted-order-idempotent
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (let open CommutativeSemiring S hiding (_≈_; trans; sym; refl); open Setoid A)
  (∨-idem    : ∀ {x} → x + x ≈ x)
  (∧-idem    : ∀ {x} → x · x ≈ x)
  (⊤-add-top : ∀ {x} → ι + x ≈ ι)
  where

open order-idempotent-supported S ∨-idem ∧-idem ⊤-add-top public
module HMO = ho-model-order-idempotent S ∨-idem ∧-idem ⊤-add-top

open Category.IsIso
open SemiMod._≈m_

private
  module SC = Category SS.Sup.cat

-- The realisation preserves the chosen terminal: the empty order realises as the zero module.
𝓥F-preserve-terminal : preserve-chosen-terminal 𝓥F OI.terminal Sup-terminal
𝓥F-preserve-terminal .inverse = 𝓥-𝟘-bwd
𝓥F-preserve-terminal .f∘inverse≈id =
  HasTerminal.to-terminal-unique Sup-terminal
    (SC._∘_ (HasTerminal.to-terminal Sup-terminal) 𝓥-𝟘-bwd) (SC.id _)
𝓥F-preserve-terminal .inverse∘f≈id .*≈* .prop-setoid._≃m_.func-eq e = λ ()

module Fam⟨𝒞⟩μ = fam-mu-lifting.in-map 0ℓ 0ℓ OI.terminal OI.cmon OI.biproduct OF.Lp-lifting

private
  module FCμ = Category Fam⟨𝒞⟩μ.cat
  module FCC = HasCoproducts Fam⟨𝒞⟩μ.coproducts

-- The unit object: the lifted terminal, one root for the unit value.
𝟙F = HasTerminal.witness (Fam⟨𝒞⟩μ.terminal OI.terminal)

𝒞𝟙ty : Fam⟨𝒞⟩μ.Obj
𝒞𝟙ty = Fam⟨𝒞⟩μ.Lf 𝟙F

𝒞unit-pt : Fam⟨𝒞⟩μ.Mor 𝟙F 𝒞𝟙ty
𝒞unit-pt = Fam⟨𝒞⟩μ.injF

𝒞Bool = FCC.coprod (Fam⟨𝒞⟩μ.Lf 𝒞𝟙ty) (Fam⟨𝒞⟩μ.Lf 𝒞𝟙ty)

module Fam⟨𝒟⟩μ =
  fam-mu-lifting.in-map 0ℓ 0ℓ Sup-terminal SS.Sup.cmon Sup-biproduct SS.supported-lifting

private
  module Sc = CommutativeSemiring S
  module OIC = Category OI.cat

open SS.Sup using (mor; bound)
open SemiMod._⇒_
open prop-setoid._⇒_ using (func; func-resp-≈)
open prop-setoid._≃m_ using (func-eq)

-- The full selection, as a constant of a discrete order.
disc-full : ∀ n → OF.𝟙p OI.⇒ OI.disc n
disc-full n .*→* .func (v ,ₚ _) = (λ i → v Fin.zero) ,ₚ OF.disc-fixed _
disc-full n .*→* .func-resp-≈ e i = e Fin.zero
disc-full n .preserve-ze i = Sc.refl
disc-full n .preserve-+ i = Sc.refl
disc-full n .preserve-· i = Sc.refl

-- A constant of a simple family: the same constant at every index; the transports are identities.
simple-pointed : ∀ {A : Setoid 0ℓ 0ℓ} {P : Category.obj OI.cat} →
                 OF.𝟙p OI.⇒ P → Fam⟨𝒞⟩μ.Pointed Fam⟨𝒞⟩μ.simple[ A , P ]
simple-pointed c .Fam⟨𝒞⟩μ.pt a = c
simple-pointed c .Fam⟨𝒞⟩μ.pt-natural e = OIC.id-left {f = c}

-- The unit object's constant: its root.
𝒞𝟙ty-pt : Fam⟨𝒞⟩μ.Pointed 𝒞𝟙ty
𝒞𝟙ty-pt = Fam⟨𝒞⟩μ.Lf-pointed Fam⟨𝒞⟩μ.zero-pointed

-- The dominated product's constant: the scalar as its root, the target's constants as its
-- components, admitted by their bounds.
SupExp-pointed : ∀ {X Y : Fam⟨𝒟⟩μ.Obj} → Fam⟨𝒟⟩μ.Pointed Y →
                 Fam⟨𝒟⟩μ.Pointed (HasWeakExponentials.exp SupExp.exponentials X Y)
SupExp-pointed {X} {Y} pY .Fam⟨𝒟⟩μ.pt f = c
  where
  module D = SupProducts.Dominated (X .Fam⟨𝒟⟩μ.idx) ((Y .Fam⟨𝒟⟩μ.fam) [ f .Fam⟨𝒟⟩μ.idxf ])

  ptY = λ x → pY .Fam⟨𝒟⟩μ.pt (f .Fam⟨𝒟⟩μ.idxf .func x)

  elem : Setoid.Carrier A → D.ΠsCarrier
  elem s .D.ΠsCarrier.root = s
  elem s .D.ΠsCarrier.part x = ptY x .mor .*→* .func s
  elem s .D.ΠsCarrier.part-natural {x₁} {x₂} e =
    pY .Fam⟨𝒟⟩μ.pt-natural (f .Fam⟨𝒟⟩μ.idxf .func-resp-≈ e) .*≈* .func-eq Sc.refl
  elem s .D.ΠsCarrier.dominated x = ptY x .bound .*≈* .func-eq Sc.refl

  c : SS.Sup.Mor SS.𝟙s (D.Πs)
  c .mor .*→* .func s = elem s
  c .mor .*→* .func-resp-≈ e = e ,ₚ (λ x → ptY x .mor .*→* .func-resp-≈ e)
  c .mor .preserve-ze = Sc.refl ,ₚ (λ x → ptY x .mor .preserve-ze)
  c .mor .preserve-+ = Sc.refl ,ₚ (λ x → ptY x .mor .preserve-+)
  c .mor .preserve-· = Sc.refl ,ₚ (λ x → ptY x .mor .preserve-·)
  c .bound .*≈* .func-eq e = Sc.trans ∨-idem e
SupExp-pointed {X} {Y} pY .Fam⟨𝒟⟩μ.pt-natural {f₁} {f₂} e .*≈* .func-eq {s₁} {s₂} e' =
  e' ,ₚ (λ x →
    pY .Fam⟨𝒟⟩μ.pt-natural
      (Fam⟨𝒟⟩μ._≃_.idxf-eq e .func-eq (X .Fam⟨𝒟⟩μ.idx .Setoid.refl))
      .*≈* .func-eq e')

-- The rooted interpretation of the primitives: the first-order interpretation, with the
-- relations' booleans injected under the roots of the rooted booleans.
module rooted-primitives (Sig : Signature 0ℓ) (𝒫 : Primitives S Sig) where

  private
    module IP = HMO.interp-primitives Sig 𝒫

  boolify : Fam⟨𝒞⟩μ.Mor HMO.Fam⟨𝒞⟩-bool 𝒞Bool
  boolify =
    FCC.coprod-m
      (FCμ._∘_ (Fam⟨𝒞⟩μ.injF {X = 𝒞𝟙ty}) (Fam⟨𝒞⟩μ.injF {X = 𝟙F}))
      (FCμ._∘_ (Fam⟨𝒞⟩μ.injF {X = 𝒞𝟙ty}) (Fam⟨𝒞⟩μ.injF {X = 𝟙F}))

  model : Model PFPC[ Fam⟨𝒞⟩μ.cat , Fam⟨𝒞⟩μ.terminal OI.terminal , Fam⟨𝒞⟩μ.products , 𝒞Bool ] Sig
  model = IP.over.model-over 𝒞Bool boolify

  -- The sorts' constants: the full selection of each discrete order.
  sort-pt : ∀ s → Fam⟨𝒞⟩μ.Pointed (model .Model.⟦sort⟧ s)
  sort-pt s = simple-pointed (disc-full (Primitives.sort-width 𝒫 s))

-- The rooted higher-order model and the first-order comparison at the realisation.
module rooted-interp (Sig : Signature 0ℓ) (𝒫 : Primitives S Sig) where

  open rooted-primitives Sig 𝒫

  open language-rooted-fo-interpretation Sig 0ℓ 0ℓ
    OI.terminal OI.cmon OI.biproduct OF.Lp-lifting
    Sup-terminal SS.Sup.cmon Sup-biproduct SS.supported-lifting
    𝓥F 𝓥F-preserve-terminal (λ {P} {Q} → 𝓥F-preserve-products {P} {Q})
    𝓥-Lp-iso (λ {P} {Q} f → Lmap-intertwine {P} {Q} f)
    ι1-bwd
    SupExp.exponentials (λ {X} {Y} pY → SupExp-pointed {X} {Y} pY)
    𝒞𝟙ty 𝒞unit-pt 𝒞𝟙ty-pt model sort-pt
    public

  open language-syntax Sig using (ctxt; type; _⊢_; first-order; first-order-ctxt)
  open Category.Iso
  open indexed-family._⇒f_ using (transf)

  -- Reading a first-order term's dependency relation back as a matrix: conjugate the fibre map at
  -- an input through the comparison isomorphisms. The realisation is full, so the conjugate's
  -- underlying map is a morphism of position orders, presented by its matrix.
  module readback {Γ : ctxt} {τ : type 0} (Γ-fo : first-order-ctxt Γ) (fo : first-order τ)
                  (t : Γ ⊢ τ) (γ : Setoid.Carrier (𝒞⟦ Γ-fo ⟧ctxt .Fam⟨𝒞⟩μ.idx)) where

    γ𝒟 = ⟦ Γ-fo ⟧ctxt-iso .fwd .Fam⟨𝒟⟩μ.idxf .func γ
    out𝒟 = 𝒟⟦ t ⟧tm .Fam⟨𝒟⟩μ.idxf .func γ𝒟
    out = closed-iso fo .bwd .Fam⟨𝒟⟩μ.idxf .func out𝒟

    abstract
      dep : (𝒞⟦ Γ-fo ⟧ctxt .Fam⟨𝒞⟩μ.fam .Fam⟨𝒞⟩μ.fm γ) OI.⇒
            (𝒞⟦ fo ⟧ty ∅𝒞 .Fam⟨𝒞⟩μ.fam .Fam⟨𝒞⟩μ.fm out)
      dep = SC._∘_ (closed-iso fo .bwd .Fam⟨𝒟⟩μ.famf .transf out𝒟)
             (SC._∘_ (𝒟⟦ t ⟧tm .Fam⟨𝒟⟩μ.famf .transf γ𝒟)
                     (⟦ Γ-fo ⟧ctxt-iso .fwd .Fam⟨𝒟⟩μ.famf .transf γ))
            .mor

      dep-mat : matrix.Mat.Matrix S
                  (OI.Pos.dim (𝒞⟦ fo ⟧ty ∅𝒞 .Fam⟨𝒞⟩μ.fam .Fam⟨𝒞⟩μ.fm out))
                  (OI.Pos.dim (𝒞⟦ Γ-fo ⟧ctxt .Fam⟨𝒞⟩μ.fam .Fam⟨𝒞⟩μ.fm γ))
      dep-mat = OI.mor→mat dep .OI._⇒ₘ_.mat
