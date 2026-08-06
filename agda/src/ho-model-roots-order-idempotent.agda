{-# OPTIONS --postfix-projections --prop --safe #-}

-- The rooted higher-order model with roots as isolated positions: families over the position
-- orders as the first-order side, families over plain semimodules as the model, the plain
-- realisation as the change of base, and the function spaces the exponentials that setoid
-- products of semimodules give, lifted at the interpretation so a closure carries a root. The
-- unit object is the lifted terminal; the primitives are interpreted as in the first-order model,
-- with the relations' booleans injected under zero roots.
open import Level using (0ℓ)
import Data.Fin as Fin
open import prop using () renaming (_,_ to _,ₚ_)
open import prop-setoid using (Setoid; IsEquivalence)
open import commutative-semiring using (CommutativeSemiring)
open import categories
  using (Category; HasTerminal; HasCoproducts; HasWeakExponentials; HasExponentials;
         exponentials→weak)
open import signature using (Signature; Model; PFPC[_,_,_,_])
open import primitives using (Primitives; sort-vals-setoid)
open import lifting using (Lifting)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import functor using (limits→limits')
open import indexed-family using (HasSetoidProducts; Fam; _⇒f_; constantFam; _[_])
import matrix
import fam
import fam-mu-lifting.in-map
import fam-exponentials
import semimod-products
import order-idempotent-blocks
import order-idempotent-realise
import order-idempotent-primitives
import language-roots-fo-interpretation
import language-syntax

module ho-model-roots-order-idempotent
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (let open CommutativeSemiring S hiding (_≈_; trans; sym; refl); open Setoid A)
  (∨-idem    : ∀ {x} → x + x ≈ x)
  (∧-idem    : ∀ {x} → x · x ≈ x)
  (⊤-add-top : ∀ {x} → ι + x ≈ ι)
  where

open order-idempotent-realise S ∨-idem ∧-idem ⊤-add-top public
module OB = order-idempotent-blocks S ∨-idem ∧-idem ⊤-add-top
module OIP = order-idempotent-primitives S ∨-idem ∧-idem ⊤-add-top
module OIPB = OIP.over-biproducts OB.blocks-biproduct (λ x y → _≡_.refl)

open SemiMod._≈m_
open SemiMod._⇒_
open prop-setoid._⇒_ using (func; func-resp-≈)
open prop-setoid._≃m_ using (func-eq)

module Fam⟨𝒞⟩μ = fam-mu-lifting.in-map 0ℓ 0ℓ OI.cmon OB.blocks-biproduct Roots.Lp-lifting
module Fam⟨𝒟⟩μ = fam-mu-lifting.in-map 0ℓ 0ℓ SemiMod.cmon-enriched SemiMod.biproduct Ls-lifting

private
  module FCμ = Category Fam⟨𝒞⟩μ.cat
  module FCC = HasCoproducts Fam⟨𝒞⟩μ.coproducts
  module Sc = CommutativeSemiring S
  module OIC = Category OI.cat
  module SMC = Category SemiMod.cat

-- The unit object: the lifted terminal, one root for the unit value.
𝟙F = HasTerminal.witness (Fam⟨𝒞⟩μ.terminal OI.terminal)

𝒞𝟙ty : Fam⟨𝒞⟩μ.Obj
𝒞𝟙ty = Fam⟨𝒞⟩μ.Lf 𝟙F

𝒞unit-pt : Fam⟨𝒞⟩μ.Mor 𝟙F 𝒞𝟙ty
𝒞unit-pt = Fam⟨𝒞⟩μ.injF

𝒞Bool = FCC.coprod (Fam⟨𝒞⟩μ.Lf 𝒞𝟙ty) (Fam⟨𝒞⟩μ.Lf 𝒞𝟙ty)

-- The full selection, as a constant of a discrete order.
disc-full : ∀ n → Roots.𝟙p OI.⇒ OI.disc n
disc-full n .*→* .func (v ,ₚ _) = (λ i → v Fin.zero) ,ₚ disc-fixed _
disc-full n .*→* .func-resp-≈ e i = e Fin.zero
disc-full n .preserve-ze i = Sc.refl
disc-full n .preserve-+ i = Sc.refl
disc-full n .preserve-· i = Sc.refl

-- A constant of a simple family: the same constant at every index; the transports are identities.
simple-pointed : ∀ {B : Setoid 0ℓ 0ℓ} {P : Category.obj OI.cat} →
                 Roots.𝟙p OI.⇒ P → Fam⟨𝒞⟩μ.Pointed Fam⟨𝒞⟩μ.simple[ B , P ]
simple-pointed c .Fam⟨𝒞⟩μ.pt a = c
simple-pointed c .Fam⟨𝒞⟩μ.pt-natural e = OIC.id-left {f = c}

-- The unit object's constant: its root.
𝒞𝟙ty-pt : Fam⟨𝒞⟩μ.Pointed 𝒞𝟙ty
𝒞𝟙ty-pt = Fam⟨𝒞⟩μ.Lf-pointed Fam⟨𝒞⟩μ.zero-pointed

-- The model-side function spaces: exponentials on Fam(SemiMod), from the direct setoid products
-- of plain semimodules.
module SMP = semimod-products S

SPmod : HasSetoidProducts 0ℓ 0ℓ SemiMod.cat
SPmod = SMP.semimod-setoid-products

module FE = fam-exponentials 0ℓ 0ℓ SemiMod.cat SemiMod.cmon-enriched SemiMod.biproduct SPmod

SemiModExp : HasWeakExponentials Fam⟨𝒟⟩μ.cat Fam⟨𝒟⟩μ.products
SemiModExp = exponentials→weak FE.exponentials

-- The exponential's constant: pointwise the target's constant, paired by the setoid product.
private
  pt-fam : ∀ {X Y : Fam⟨𝒟⟩μ.Obj} → Fam⟨𝒟⟩μ.Pointed Y → (f : Fam⟨𝒟⟩μ.Mor X Y) →
           constantFam (X .Fam⟨𝒟⟩μ.idx) SemiMod.cat SemiMod.𝕀
             ⇒f (Y .Fam⟨𝒟⟩μ.fam [ f .Fam⟨𝒟⟩μ.idxf ])
  pt-fam pY f ._⇒f_.transf x = pY .Fam⟨𝒟⟩μ.pt (f .Fam⟨𝒟⟩μ.idxf .func x)
  pt-fam pY f ._⇒f_.natural e =
    SMC.≈-trans SMC.id-right
      (SMC.≈-sym (pY .Fam⟨𝒟⟩μ.pt-natural (f .Fam⟨𝒟⟩μ.idxf .func-resp-≈ e)))

SemiModExp-pointed : ∀ {X Y : Fam⟨𝒟⟩μ.Obj} → Fam⟨𝒟⟩μ.Pointed Y →
                     Fam⟨𝒟⟩μ.Pointed (HasWeakExponentials.exp SemiModExp X Y)
SemiModExp-pointed {X} {Y} pY .Fam⟨𝒟⟩μ.pt f =
  SPmod .HasSetoidProducts.lambdaΠ SemiMod.𝕀 (Y .Fam⟨𝒟⟩μ.fam [ f .Fam⟨𝒟⟩μ.idxf ])
    (pt-fam pY f)
SemiModExp-pointed {X} {Y} pY .Fam⟨𝒟⟩μ.pt-natural {f₁} {f₂} e =
  SMC.≈-trans
    (SMC.≈-sym (HasSetoidProducts.lambda-compose SPmod
      (indexed-family.reindex-≈ (f₁ .Fam⟨𝒟⟩μ.idxf) (f₂ .Fam⟨𝒟⟩μ.idxf)
        (e .Fam⟨𝒟⟩μ._≃_.idxf-eq)) (pt-fam pY f₁)))
    (SPmod .HasSetoidProducts.lambdaΠ-cong
      {f₁ = indexed-family._∘f_
              (indexed-family.reindex-≈ (f₁ .Fam⟨𝒟⟩μ.idxf) (f₂ .Fam⟨𝒟⟩μ.idxf)
                (e .Fam⟨𝒟⟩μ._≃_.idxf-eq))
              (pt-fam pY f₁)}
      {f₂ = pt-fam pY f₂}
      (record { transf-eq = λ {x} →
        pY .Fam⟨𝒟⟩μ.pt-natural
          (e .Fam⟨𝒟⟩μ._≃_.idxf-eq .func-eq (X .Fam⟨𝒟⟩μ.idx .Setoid.refl)) }))

-- The rooted interpretation of the primitives: the first-order interpretation, with the
-- relations' booleans injected under zero roots.
module rooted-primitives (Sig : Signature 0ℓ) (𝒫 : Primitives S Sig) where

  private
    module IP = OIPB.interp-primitives Sig 𝒫

  boolify : Fam⟨𝒞⟩μ.Mor OIPB.Fam⟨𝒞⟩-bool 𝒞Bool
  boolify =
    FCC.coprod-m
      (FCμ._∘_ (Fam⟨𝒞⟩μ.injF {X = 𝒞𝟙ty}) (Fam⟨𝒞⟩μ.injF {X = 𝟙F}))
      (FCμ._∘_ (Fam⟨𝒞⟩μ.injF {X = 𝒞𝟙ty}) (Fam⟨𝒞⟩μ.injF {X = 𝟙F}))

  private
    module IPO = IP.over 𝒞Bool boolify
    module Pm = Primitives 𝒫
    module MS = matrix.Mat S
    module Lft = Lifting Roots.Lp-lifting
    open indexed-family._⇒f_

    disc-morₘ : ∀ {m n} → Category._⇒_ MS.cat m n → OI._⇒ₘ_ (OI.disc m) (OI.disc n)
    disc-morₘ R .OI._⇒ₘ_.mat = R
    disc-morₘ R .OI._⇒ₘ_.absorbed =
      OI.≈ₘ-trans (MS.∘-cong (MS.id-left {M = R}) (OI.≈ₘ-refl {M = MS.I}))
                  (MS.id-right {M = R})

    d' : ∀ {is} (ψ : Signature.rel Sig is)
         (c : Setoid.Carrier (sort-vals-setoid Pm.sort-index is)) →
         OI._⇒_ (OI.disc (Pm.bases-width is)) Roots.𝟙p
    d' ψ c = OI.mat→mor (disc-morₘ (Pm.rel-deps ψ .func c))

    deps-resp : ∀ {is} (ψ : Signature.rel Sig is)
                {c c' : Setoid.Carrier (sort-vals-setoid Pm.sort-index is)} →
                Setoid._≈_ (sort-vals-setoid Pm.sort-index is) c c' →
                OIC._≈_ (d' ψ c') (d' ψ c)
    deps-resp ψ {c} {c'} e =
      OI.mat→mor-congₘ {f = disc-morₘ (Pm.rel-deps ψ .func c')}
                       {g = disc-morₘ (Pm.rel-deps ψ .func c)}
        (OI.≈ₘ-sym (Pm.rel-deps ψ .func-resp-≈ e))

    -- The boolean's roots as its constants, so a test's fibre map is the point at the outcome
    -- after its dependence row.
    bool-root-pt : Fam⟨𝒞⟩μ.Pointed 𝒞Bool
    bool-root-pt =
      Fam⟨𝒞⟩μ.coprod-pointed (Fam⟨𝒞⟩μ.root-pointed {X = 𝒞𝟙ty})
                             (Fam⟨𝒞⟩μ.root-pointed {X = 𝒞𝟙ty})

  -- Tests write their dependence into the outcome's root: which branch runs reads the scalars the
  -- test read.
  rel-simple : ∀ is (ψ : Signature.rel Sig is) →
               Fam⟨𝒞⟩μ.Mor
                 Fam⟨𝒞⟩μ.simple[ sort-vals-setoid Pm.sort-index is ,
                                 OI.disc (Pm.bases-width is) ]
                 𝒞Bool
  rel-simple is ψ .Fam⟨𝒞⟩μ.idxf = Pm.rel-pred ψ
  rel-simple is ψ .Fam⟨𝒞⟩μ.famf .transf c =
    OIC._∘_ (bool-root-pt .Fam⟨𝒞⟩μ.pt (Pm.rel-pred ψ .func c)) (d' ψ c)
  rel-simple is ψ .Fam⟨𝒞⟩μ.famf .natural {c} {c'} e = pf
    where
    o  = Pm.rel-pred ψ .func c
    o' = Pm.rel-pred ψ .func c'
    P  = bool-root-pt .Fam⟨𝒞⟩μ.pt o
    P' = bool-root-pt .Fam⟨𝒞⟩μ.pt o'
    sub = 𝒞Bool .Fam⟨𝒞⟩μ.fam .Fam⟨𝒞⟩μ.subst {o} {o'} (Pm.rel-pred ψ .func-resp-≈ e)

    step1 : OIC._≈_ (OIC._∘_ sub (OIC._∘_ P (d' ψ c))) (OIC._∘_ (OIC._∘_ sub P) (d' ψ c))
    step1 = OIC.≈-sym (OIC.assoc sub P (d' ψ c))

    step2 : OIC._≈_ (OIC._∘_ (OIC._∘_ sub P) (d' ψ c)) (OIC._∘_ P' (d' ψ c))
    step2 = OIC.∘-cong (bool-root-pt .Fam⟨𝒞⟩μ.pt-natural {x₁ = o} {x₂ = o'}
                          (Pm.rel-pred ψ .func-resp-≈ e))
                       (OIC.≈-refl {f = d' ψ c})

    step3 : OIC._≈_ (OIC._∘_ P' (d' ψ c)) (OIC._∘_ P' (d' ψ c'))
    step3 = OIC.∘-cong (OIC.≈-refl {f = P'}) (OIC.≈-sym (deps-resp ψ e))

    pf : OIC._≈_ (OIC._∘_ (OIC._∘_ P' (d' ψ c')) (OIC.id (OI.disc (Pm.bases-width is))))
                 (OIC._∘_ sub (OIC._∘_ P (d' ψ c)))
    pf = OIC.≈-trans (OIC.id-right {f = OIC._∘_ P' (d' ψ c')})
           (OIC.≈-sym (OIC.≈-trans step1 (OIC.≈-trans step2 step3)))

  model : Model PFPC[ Fam⟨𝒞⟩μ.cat , Fam⟨𝒞⟩μ.terminal OI.terminal , Fam⟨𝒞⟩μ.products , 𝒞Bool ] Sig
  model = record IPO.model-over
    { ⟦rel⟧ = λ {is} ψ → FCμ._∘_ (rel-simple is ψ) (IPO.arg-collect is) }

  -- The sorts' constants: the full selection of each discrete order.
  sort-pt : ∀ s → Fam⟨𝒞⟩μ.Pointed (model .Model.⟦sort⟧ s)
  sort-pt s = simple-pointed (disc-full (Primitives.sort-width 𝒫 s))

-- The rooted higher-order model and the first-order comparison at the realisation.
module rooted-interp (Sig : Signature 0ℓ) (𝒫 : Primitives S Sig) where

  open rooted-primitives Sig 𝒫

  open language-roots-fo-interpretation Sig 0ℓ 0ℓ
    OI.terminal OI.cmon OB.blocks-biproduct Roots.Lp-lifting
    SemiMod.terminal SemiMod.cmon-enriched SemiMod.biproduct Ls-lifting
    𝓥F 𝓥F-preserve-terminal (λ {P} {Q} → 𝓥F-preserve-products-blocks {P} {Q})
    𝓥-Lp-iso (λ {P} {Q} f → 𝓥-Lp-natural {P} {Q} f)
    ι1-bwd
    SemiModExp (λ {X} {Y} pY → SemiModExp-pointed {X} {Y} pY)
    𝒞𝟙ty 𝒞unit-pt 𝒞𝟙ty-pt model sort-pt
    public

  open language-syntax Sig using (ctxt; type; _⊢_; first-order; first-order-ctxt)
  open Category.Iso
  open indexed-family._⇒f_ using (transf)

  -- Reading a first-order term's dependency relation back as a matrix: conjugate the fibre map at
  -- an input through the comparison isomorphisms; the composite is a morphism of position orders,
  -- presented by its matrix.
  module readback {Γ : ctxt} {τ : type 0} (Γ-fo : first-order-ctxt Γ) (fo : first-order τ)
                  (t : Γ ⊢ τ) (γ : Setoid.Carrier (𝒞⟦ Γ-fo ⟧ctxt .Fam⟨𝒞⟩μ.idx)) where

    γ𝒟 = ⟦ Γ-fo ⟧ctxt-iso .fwd .Fam⟨𝒟⟩μ.idxf .func γ
    out𝒟 = 𝒟⟦ t ⟧tm .Fam⟨𝒟⟩μ.idxf .func γ𝒟
    out = closed-iso fo .bwd .Fam⟨𝒟⟩μ.idxf .func out𝒟

    abstract
      dep : (𝒞⟦ Γ-fo ⟧ctxt .Fam⟨𝒞⟩μ.fam .Fam⟨𝒞⟩μ.fm γ) OI.⇒
            (𝒞⟦ fo ⟧ty ∅𝒞 .Fam⟨𝒞⟩μ.fam .Fam⟨𝒞⟩μ.fm out)
      dep = SemiMod._∘_
              {𝓥 (𝒞⟦ Γ-fo ⟧ctxt .Fam⟨𝒞⟩μ.fam .Fam⟨𝒞⟩μ.fm γ)}
              {𝒟⟦ τ ⟧ty (λ ()) .Fam⟨𝒟⟩μ.fam .Fam⟨𝒟⟩μ.fm out𝒟}
              {𝓥 (𝒞⟦ fo ⟧ty ∅𝒞 .Fam⟨𝒞⟩μ.fam .Fam⟨𝒞⟩μ.fm out)}
              (closed-iso fo .bwd .Fam⟨𝒟⟩μ.famf .transf out𝒟)
              (SemiMod._∘_
                {𝓥 (𝒞⟦ Γ-fo ⟧ctxt .Fam⟨𝒞⟩μ.fam .Fam⟨𝒞⟩μ.fm γ)}
                {𝒟⟦ Γ ⟧ctxt .Fam⟨𝒟⟩μ.fam .Fam⟨𝒟⟩μ.fm γ𝒟}
                {𝒟⟦ τ ⟧ty (λ ()) .Fam⟨𝒟⟩μ.fam .Fam⟨𝒟⟩μ.fm out𝒟}
                (𝒟⟦ t ⟧tm .Fam⟨𝒟⟩μ.famf .transf γ𝒟)
                (⟦ Γ-fo ⟧ctxt-iso .fwd .Fam⟨𝒟⟩μ.famf .transf γ))

      -- The presentation matrix, read entrywise on tabulated basis columns so the evaluation's
      -- coordinate reads hit a lookup rather than recompute a block-order entry each time.
      dep-mat : matrix.Mat.Matrix S
                  (OI.Pos.dim (𝒞⟦ fo ⟧ty ∅𝒞 .Fam⟨𝒞⟩μ.fam .Fam⟨𝒞⟩μ.fm out))
                  (OI.Pos.dim (𝒞⟦ Γ-fo ⟧ctxt .Fam⟨𝒞⟩μ.fam .Fam⟨𝒞⟩μ.fm γ))
      dep-mat q p =
        OI.vec (𝒞⟦ fo ⟧ty ∅𝒞 .Fam⟨𝒞⟩μ.fam .Fam⟨𝒞⟩μ.fm out)
               (SemiMod._⇒_.func dep
                 (OI.colv-tab (𝒞⟦ Γ-fo ⟧ctxt .Fam⟨𝒞⟩μ.fam .Fam⟨𝒞⟩μ.fm γ) p))
               q

  -- The realisation is identity on morphisms, so fullness holds with each morphism its own
  -- preimage.
  module syntactic = definability (λ e → e) (λ k → k ,ₚ SMC.≈-refl)
