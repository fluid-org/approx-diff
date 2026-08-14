{-# OPTIONS --postfix-projections --prop --safe #-}

-- The higher-order model: families of dimensions as the first-order
-- side, families over plain semimodules as the model, the free realisation as the change of base,
-- and the function spaces the exponentials that setoid products of semimodules give, lifted at the
-- interpretation so a closure carries a root. Positions carry no order, so a fibre map is an
-- arbitrary weighted relation and a value's positions are its scalar leaves together with one
-- coordinate per constructor. The unit object is the lifted terminal; the primitives are
-- interpreted as in the first-order model, with the relations' booleans injected under zero roots.
open import Level using (0ℓ)
open import Data.Nat using (ℕ)
import Data.Fin as Fin
import prop
open import prop-setoid using (Setoid; IsEquivalence)
open import commutative-semiring using (CommutativeSemiring)
open import categories
  using (Category; HasTerminal; IsTerminal; HasCoproducts; HasWeakExponentials; HasExponentials;
         exponentials→weak; setoid→category)
open import signature using (Signature; Model; PFPC[_,_,_,_])
open import primitives using (Primitives; sort-vals-setoid)
open import Data.Sum using (inj₁; inj₂)
open import cmon-enriched using (CMonEnriched)
open import functor using (cones→limits)
import indexed-family
open import indexed-family
  using (HasSetoidProducts; Fam; _⇒f_; _≃f_; _∘f_; constantFam; _[_]; reindex-≈)
import matrix
import fam
import fam-mu-lifting.in-map
import fam-exponentials
import matrix-embedding
import matrix-primitives
import language-fo-interpretation
import language-syntax

module ho-model
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (elim-weight : Setoid.Carrier A)
  where

open matrix-embedding S public
module FP = matrix-primitives S
private
  module Sc = CommutativeSemiring S

open SemiMod._≈m_
open SemiMod._⇒_
open prop-setoid._⇒_ using (func; func-resp-≈)
open prop-setoid._≃m_ using (func-eq)

module Fam⟨𝒞⟩μ = fam-mu-lifting.in-map 0ℓ 0ℓ M.cmon M.biproduct 1
module Fam⟨𝒟⟩μ = fam-mu-lifting.in-map 0ℓ 0ℓ SemiMod.cmon-enriched SemiMod.biproduct SemiMod.𝕀

private
  module FCμ = Category Fam⟨𝒞⟩μ.cat
  module FCC = HasCoproducts Fam⟨𝒞⟩μ.coproducts
  module MC = Category M.cat
  module MCM = CMonEnriched M.cmon
  module SMC = Category SemiMod.cat

elim-weight-endo : SemiMod._⇒_ SemiMod.𝕀 SemiMod.𝕀
elim-weight-endo = SMC._∘_ ι1-fwd (SMC._∘_ (mat (matrix.Mat.block S elim-weight)) ι1-bwd)

-- The unit object: the lifted terminal, one root for the unit value.
𝟙F = HasTerminal.witness (Fam⟨𝒞⟩μ.terminal M.terminal)

𝒞𝟙ty : Fam⟨𝒞⟩μ.Obj
𝒞𝟙ty = Fam⟨𝒞⟩μ.Lf 𝟙F

𝒞unit-pt : Fam⟨𝒞⟩μ.Mor 𝟙F 𝒞𝟙ty
𝒞unit-pt = Fam⟨𝒞⟩μ.injF

𝒞Bool = FCC.coprod (Fam⟨𝒞⟩μ.Lf 𝒞𝟙ty) (Fam⟨𝒞⟩μ.Lf 𝒞𝟙ty)

-- The row of units: the unit constant of a simple family of dimensions.
ι-row : ∀ n → MC._⇒_ 1 n
ι-row n _ _ = Sc.ι

-- The unit constants on the first-order side: the terminal fibre has no positions, and each root
-- the lifting adjoins carries the unit weight.
𝟙F-const : Fam⟨𝒞⟩μ.Constant 𝟙F
𝟙F-const = Fam⟨𝒞⟩μ.simple-constant (M.terminal .HasTerminal.is-terminal .IsTerminal.to-terminal)

𝒞𝟙ty-const : Fam⟨𝒞⟩μ.Constant 𝒞𝟙ty
𝒞𝟙ty-const = Fam⟨𝒞⟩μ.Lf-constant 𝟙F-const

𝒞Bool-const : Fam⟨𝒞⟩μ.Constant 𝒞Bool
𝒞Bool-const =
  Fam⟨𝒞⟩μ.coprod-constant (Fam⟨𝒞⟩μ.Lf-constant 𝒞𝟙ty-const) (Fam⟨𝒞⟩μ.Lf-constant 𝒞𝟙ty-const)

-- The model-side function spaces: exponentials on Fam(SemiMod), from the direct setoid products
-- of plain semimodules.
SPmod : HasSetoidProducts 0ℓ 0ℓ SemiMod.cat
SPmod =
  indexed-family.hasSetoidProducts 0ℓ 0ℓ SemiMod.cat
    (λ A → cones→limits (SemiMod.limits (setoid→category A)))

module FE = fam-exponentials 0ℓ 0ℓ SemiMod.cat SemiMod.cmon-enriched SemiMod.biproduct SPmod

SemiModExp : HasWeakExponentials Fam⟨𝒟⟩μ.cat Fam⟨𝒟⟩μ.products
SemiModExp = exponentials→weak FE.exponentials

-- The unit constant of a function space: at each fibre map, the tuple of the target's constants
-- over its index action.
private
  module SPm = HasSetoidProducts SPmod

private
  exp-tuple : ∀ {X Y : Fam⟨𝒟⟩μ.Obj} → Fam⟨𝒟⟩μ.Constant Y → (f : Fam⟨𝒟⟩μ.Mor X Y) →
              constantFam (X .Fam⟨𝒟⟩μ.idx) SemiMod.cat SemiMod.𝕀
                ⇒f (Y .Fam⟨𝒟⟩μ.fam [ f .Fam⟨𝒟⟩μ.idxf ])
  exp-tuple cY f ._⇒f_.transf x = cY .Fam⟨𝒟⟩μ.at (f .Fam⟨𝒟⟩μ.idxf .func x)
  exp-tuple cY f ._⇒f_.natural e =
    SMC.≈-trans SMC.id-right
      (SMC.≈-sym (cY .Fam⟨𝒟⟩μ.at-natural (f .Fam⟨𝒟⟩μ.idxf .func-resp-≈ e)))

exp-const : ∀ {X Y : Fam⟨𝒟⟩μ.Obj} → Fam⟨𝒟⟩μ.Constant Y → Fam⟨𝒟⟩μ.Constant (FE._⟶_ X Y)
exp-const {X} {Y} cY .Fam⟨𝒟⟩μ.at f =
  SPm.lambdaΠ SemiMod.𝕀 (Y .Fam⟨𝒟⟩μ.fam [ f .Fam⟨𝒟⟩μ.idxf ]) (exp-tuple cY f)
exp-const {X} {Y} cY .Fam⟨𝒟⟩μ.at-natural {f₁} {f₂} e =
  SMC.≈-trans
    (SMC.≈-sym
      (SPm.lambda-compose
        (reindex-≈ (f₁ .Fam⟨𝒟⟩μ.idxf) (f₂ .Fam⟨𝒟⟩μ.idxf) (Fam⟨𝒟⟩μ._≃_.idxf-eq e))
        (exp-tuple cY f₁)))
    (SPm.lambdaΠ-cong pw)
  where
  pw : (reindex-≈ (f₁ .Fam⟨𝒟⟩μ.idxf) (f₂ .Fam⟨𝒟⟩μ.idxf) (Fam⟨𝒟⟩μ._≃_.idxf-eq e)
          ∘f exp-tuple cY f₁)
         ≃f exp-tuple cY f₂
  pw ._≃f_.transf-eq = cY .Fam⟨𝒟⟩μ.at-natural _

-- The interpretation of the primitives: the first-order interpretation, with the relations'
-- booleans injected under zero roots.
module sig-model (Sig : Signature 0ℓ) (𝒫 : Primitives S Sig) where

  private
    module IP = FP.interp-primitives Sig 𝒫

  boolify : Fam⟨𝒞⟩μ.Mor FP.Fam⟨𝒞⟩-bool 𝒞Bool
  boolify =
    FCC.coprod-m
      (FCμ._∘_ (Fam⟨𝒞⟩μ.injF {X = 𝒞𝟙ty}) (Fam⟨𝒞⟩μ.injF {X = 𝟙F}))
      (FCμ._∘_ (Fam⟨𝒞⟩μ.injF {X = 𝒞𝟙ty}) (Fam⟨𝒞⟩μ.injF {X = 𝟙F}))

  private
    module IPO = IP.over 𝒞Bool boolify
    module Pm = Primitives 𝒫
    open indexed-family._⇒f_

    -- The positions a test reads, as a single row into the outcome's root.
    d' : ∀ {is} (ψ : Signature.rel Sig is)
         (c : Setoid.Carrier (sort-vals-setoid Pm.sort-index is)) →
         MC._⇒_ (Pm.bases-width is) 1
    d' ψ c = Pm.rel-deps ψ .func c

    deps-resp : ∀ {is} (ψ : Signature.rel Sig is)
                {c c' : Setoid.Carrier (sort-vals-setoid Pm.sort-index is)} →
                Setoid._≈_ (sort-vals-setoid Pm.sort-index is) c c' →
                MC._≈_ (d' ψ c') (d' ψ c)
    deps-resp ψ e = MC.≈-sym (Pm.rel-deps ψ .func-resp-≈ e)

  -- Tests write their dependence into the outcome's root: which branch runs reads the scalars the
  -- test read.
  rel-simple : ∀ is (ψ : Signature.rel Sig is) →
               Fam⟨𝒞⟩μ.Mor
                 Fam⟨𝒞⟩μ.simple[ sort-vals-setoid Pm.sort-index is , Pm.bases-width is ]
                 𝒞Bool
  rel-simple is ψ .Fam⟨𝒞⟩μ.idxf = Pm.rel-pred ψ
  rel-simple is ψ .Fam⟨𝒞⟩μ.famf .transf c =
    MC._∘_ (𝒞Bool-const .Fam⟨𝒞⟩μ.at (Pm.rel-pred ψ .func c)) (d' ψ c)
  rel-simple is ψ .Fam⟨𝒞⟩μ.famf .natural {c} {c'} e = pf
    where
    o  = Pm.rel-pred ψ .func c
    o' = Pm.rel-pred ψ .func c'
    P  = 𝒞Bool-const .Fam⟨𝒞⟩μ.at o
    P' = 𝒞Bool-const .Fam⟨𝒞⟩μ.at o'
    sub = 𝒞Bool .Fam⟨𝒞⟩μ.fam .Fam⟨𝒞⟩μ.subst {o} {o'} (Pm.rel-pred ψ .func-resp-≈ e)

    step1 : MC._≈_ (MC._∘_ sub (MC._∘_ P (d' ψ c))) (MC._∘_ (MC._∘_ sub P) (d' ψ c))
    step1 = MC.≈-sym (MC.assoc sub P (d' ψ c))

    step2 : MC._≈_ (MC._∘_ (MC._∘_ sub P) (d' ψ c)) (MC._∘_ P' (d' ψ c))
    step2 = MC.∘-cong (𝒞Bool-const .Fam⟨𝒞⟩μ.at-natural {x₁ = o} {x₂ = o'}
                         (Pm.rel-pred ψ .func-resp-≈ e))
                      (MC.≈-refl {f = d' ψ c})

    step3 : MC._≈_ (MC._∘_ P' (d' ψ c)) (MC._∘_ P' (d' ψ c'))
    step3 = MC.∘-cong (MC.≈-refl {f = P'}) (MC.≈-sym (deps-resp ψ e))

    pf : MC._≈_ (MC._∘_ (MC._∘_ P' (d' ψ c')) (MC.id (Pm.bases-width is)))
                (MC._∘_ sub (MC._∘_ P (d' ψ c)))
    pf = MC.≈-trans (MC.id-right {f = MC._∘_ P' (d' ψ c')})
           (MC.≈-sym (MC.≈-trans step1 (MC.≈-trans step2 step3)))

  model : Model PFPC[ Fam⟨𝒞⟩μ.cat , Fam⟨𝒞⟩μ.terminal M.terminal , Fam⟨𝒞⟩μ.products , 𝒞Bool ] Sig
  model = record IPO.model-over
    { ⟦rel⟧ = λ {is} ψ → FCμ._∘_ (rel-simple is ψ) (IPO.arg-collect is) }

-- The higher-order model and the first-order comparison at the realisation.
module interp (Sig : Signature 0ℓ) (𝒫 : Primitives S Sig) where

  open sig-model Sig 𝒫

  𝒞-sort-const : ∀ s → Fam⟨𝒞⟩μ.Constant (model .Model.⟦sort⟧ s)
  𝒞-sort-const s = Fam⟨𝒞⟩μ.simple-constant (ι-row (Primitives.sort-width 𝒫 s))

  open language-fo-interpretation Sig 0ℓ 0ℓ
    M.terminal M.cmon M.biproduct 1
    SemiMod.terminal SemiMod.cmon-enriched SemiMod.biproduct SemiMod.𝕀
    𝔽F 𝔽F-preserve-terminal (λ {m} {n} → 𝔽F-preserve-products {m} {n})
    𝔽-L-iso (λ {P} {Q} f → 𝔽-L-natural {P} {Q} f)
    SemiModExp
    𝒞𝟙ty 𝒞unit-pt model
    elim-weight-endo (λ {X} {Y} → exp-const {X} {Y}) ι1-bwd 𝒞𝟙ty-const 𝒞-sort-const
    public

  open language-syntax Sig using (ctxt; type; _⊢_; first-order; first-order-ctxt)
  open Category.Iso
  open indexed-family._⇒f_ using (transf)

  -- The fibre map at an input, conjugated through the comparison isomorphisms and evaluated on
  -- the basis. With the fibres free, the basis vector at an input position is the selection of
  -- that position alone, so no closure intervenes between the relation and its matrix.
  module dependency {Γ : ctxt} {τ : type 0} (Γ-fo : first-order-ctxt Γ) (fo : first-order τ)
                  (t : Γ ⊢ τ) (γ : Setoid.Carrier (𝒞⟦ Γ-fo ⟧ctxt .Fam⟨𝒞⟩μ.idx)) where

    γ𝒟 = ⟦ Γ-fo ⟧ctxt-iso .fwd .Fam⟨𝒟⟩μ.idxf .func γ
    out𝒟 = 𝒟⟦ t ⟧tm .Fam⟨𝒟⟩μ.idxf .func γ𝒟
    out = closed-iso fo .bwd .Fam⟨𝒟⟩μ.idxf .func out𝒟

    src = 𝒞⟦ Γ-fo ⟧ctxt .Fam⟨𝒞⟩μ.fam .Fam⟨𝒞⟩μ.fm γ
    tgt = 𝒞⟦ fo ⟧ty ∅𝒞 .Fam⟨𝒞⟩μ.fam .Fam⟨𝒞⟩μ.fm out

    abstract
      rel : SemiMod._⇒_ (𝔽 src) (𝔽 tgt)
      rel = SemiMod._∘_
              {𝔽 src}
              {𝒟⟦ τ ⟧ty (λ ()) .Fam⟨𝒟⟩μ.fam .Fam⟨𝒟⟩μ.fm out𝒟}
              {𝔽 tgt}
              (closed-iso fo .bwd .Fam⟨𝒟⟩μ.famf .transf out𝒟)
              (SemiMod._∘_
                {𝔽 src}
                {𝒟⟦ Γ ⟧ctxt .Fam⟨𝒟⟩μ.fam .Fam⟨𝒟⟩μ.fm γ𝒟}
                {𝒟⟦ τ ⟧ty (λ ()) .Fam⟨𝒟⟩μ.fam .Fam⟨𝒟⟩μ.fm out𝒟}
                (𝒟⟦ t ⟧tm .Fam⟨𝒟⟩μ.famf .transf γ𝒟)
                (⟦ Γ-fo ⟧ctxt-iso .fwd .Fam⟨𝒟⟩μ.famf .transf γ))

      -- The image of each input position's basis vector, which presents the fibre map rather
      -- than tabulating it.
      mat-of : MC._⇒_ src tgt
      mat-of q p = SemiMod._⇒_.func rel (M.e p) q

      presents : SMC._≈_ (mat mat-of) rel
      presents = 𝔽F-full rel .prop.∃ₛ.snd
