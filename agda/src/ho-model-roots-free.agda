{-# OPTIONS --postfix-projections --prop --safe #-}

-- The rooted higher-order model over free positions: families of dimensions as the first-order
-- side, families over plain semimodules as the model, the free realisation as the change of base,
-- and the function spaces the exponentials that setoid products of semimodules give, lifted at the
-- interpretation so a closure carries a root. Positions carry no order, so a fibre map is an
-- arbitrary weighted relation and a value's positions are its scalar leaves together with one
-- coordinate per constructor. The unit object is the lifted terminal; the primitives are
-- interpreted as in the first-order model, with the relations' booleans injected under zero roots.
open import Level using (0ℓ)
open import Data.Nat using (ℕ)
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
open import functor using (limits→limits')
open import indexed-family using (HasSetoidProducts; Fam; _⇒f_; constantFam; _[_])
import matrix
import fam
import fam-mu-lifting.in-map
import fam-exponentials
import semimod-products
import free-realise
import free-primitives
import language-roots-fo-interpretation
import language-syntax

module ho-model-roots-free
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (charge : Setoid.Carrier A)
  where

open free-realise S public
module FP = free-primitives S

open SemiMod._≈m_
open SemiMod._⇒_
open prop-setoid._⇒_ using (func; func-resp-≈)
open prop-setoid._≃m_ using (func-eq)

module Fam⟨𝒞⟩μ = fam-mu-lifting.in-map 0ℓ 0ℓ M.cmon M.biproduct Lm-lifting
module Fam⟨𝒟⟩μ = fam-mu-lifting.in-map 0ℓ 0ℓ SemiMod.cmon-enriched SemiMod.biproduct Ls-lifting

private
  module FCμ = Category Fam⟨𝒞⟩μ.cat
  module FCC = HasCoproducts Fam⟨𝒞⟩μ.coproducts
  module Sc = CommutativeSemiring S
  module MC = Category M.cat
  module SMC = Category SemiMod.cat

-- The charge as an endomorphism of the model lifting's unit, conjugated through the realised unit
-- dimension.
charge-endo : Category._⇒_ SemiMod.cat SemiMod.𝕀 SemiMod.𝕀
charge-endo = SMC._∘_ ι1-fwd (SMC._∘_ (mat (matrix.Mat.block S charge)) ι1-bwd)

-- The unit object: the lifted terminal, one root for the unit value.
𝟙F = HasTerminal.witness (Fam⟨𝒞⟩μ.terminal M.terminal)

𝒞𝟙ty : Fam⟨𝒞⟩μ.Obj
𝒞𝟙ty = Fam⟨𝒞⟩μ.Lf 𝟙F

𝒞unit-pt : Fam⟨𝒞⟩μ.Mor 𝟙F 𝒞𝟙ty
𝒞unit-pt = Fam⟨𝒞⟩μ.injF

𝒞Bool = FCC.coprod (Fam⟨𝒞⟩μ.Lf 𝒞𝟙ty) (Fam⟨𝒞⟩μ.Lf 𝒞𝟙ty)

-- The full selection: every position at the top weight.
full : ∀ n → Category._⇒_ M.cat 1 n
full n _ _ = Sc.ι

-- A constant of a simple family: the same constant at every index; the transports are identities.
simple-pointed : ∀ {B : Setoid 0ℓ 0ℓ} {P : ℕ} →
                 Category._⇒_ M.cat 1 P → Fam⟨𝒞⟩μ.Pointed Fam⟨𝒞⟩μ.simple[ B , P ]
simple-pointed c .Fam⟨𝒞⟩μ.pt a = c
simple-pointed c .Fam⟨𝒞⟩μ.pt-natural e = MC.id-left {f = c}

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

-- The rooted interpretation of the primitives: the first-order interpretation, with the relations'
-- booleans injected under zero roots.
module rooted-primitives (Sig : Signature 0ℓ) (𝒫 : Primitives S Sig) where

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
         Category._⇒_ M.cat (Pm.bases-width is) 1
    d' ψ c = Pm.rel-deps ψ .func c

    deps-resp : ∀ {is} (ψ : Signature.rel Sig is)
                {c c' : Setoid.Carrier (sort-vals-setoid Pm.sort-index is)} →
                Setoid._≈_ (sort-vals-setoid Pm.sort-index is) c c' →
                MC._≈_ (d' ψ c') (d' ψ c)
    deps-resp ψ e = MC.≈-sym (Pm.rel-deps ψ .func-resp-≈ e)

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
                 Fam⟨𝒞⟩μ.simple[ sort-vals-setoid Pm.sort-index is , Pm.bases-width is ]
                 𝒞Bool
  rel-simple is ψ .Fam⟨𝒞⟩μ.idxf = Pm.rel-pred ψ
  rel-simple is ψ .Fam⟨𝒞⟩μ.famf .transf c =
    MC._∘_ (bool-root-pt .Fam⟨𝒞⟩μ.pt (Pm.rel-pred ψ .func c)) (d' ψ c)
  rel-simple is ψ .Fam⟨𝒞⟩μ.famf .natural {c} {c'} e = pf
    where
    o  = Pm.rel-pred ψ .func c
    o' = Pm.rel-pred ψ .func c'
    P  = bool-root-pt .Fam⟨𝒞⟩μ.pt o
    P' = bool-root-pt .Fam⟨𝒞⟩μ.pt o'
    sub = 𝒞Bool .Fam⟨𝒞⟩μ.fam .Fam⟨𝒞⟩μ.subst {o} {o'} (Pm.rel-pred ψ .func-resp-≈ e)

    step1 : MC._≈_ (MC._∘_ sub (MC._∘_ P (d' ψ c))) (MC._∘_ (MC._∘_ sub P) (d' ψ c))
    step1 = MC.≈-sym (MC.assoc sub P (d' ψ c))

    step2 : MC._≈_ (MC._∘_ (MC._∘_ sub P) (d' ψ c)) (MC._∘_ P' (d' ψ c))
    step2 = MC.∘-cong (bool-root-pt .Fam⟨𝒞⟩μ.pt-natural {x₁ = o} {x₂ = o'}
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

  -- The sorts' constants: the full selection of each width.
  sort-pt : ∀ s → Fam⟨𝒞⟩μ.Pointed (model .Model.⟦sort⟧ s)
  sort-pt s = simple-pointed (full (Primitives.sort-width 𝒫 s))

-- The rooted higher-order model and the first-order comparison at the realisation.
module rooted-interp (Sig : Signature 0ℓ) (𝒫 : Primitives S Sig) where

  open rooted-primitives Sig 𝒫

  open language-roots-fo-interpretation Sig 0ℓ 0ℓ
    M.terminal M.cmon M.biproduct Lm-lifting
    SemiMod.terminal SemiMod.cmon-enriched SemiMod.biproduct Ls-lifting
    charge-endo
    𝔽F 𝔽F-preserve-terminal (λ {m} {n} → 𝔽F-preserve-products {m} {n})
    𝔽-L-iso (λ {P} {Q} f → 𝔽-L-natural {P} {Q} f)
    ι1-bwd
    SemiModExp (λ {X} {Y} pY → SemiModExp-pointed {X} {Y} pY)
    𝒞𝟙ty 𝒞unit-pt 𝒞𝟙ty-pt model sort-pt
    public

  open language-syntax Sig using (ctxt; type; _⊢_; first-order; first-order-ctxt)
  open Category.Iso
  open indexed-family._⇒f_ using (transf)

  -- Reading a first-order term's dependency relation back: conjugate the fibre map at an input
  -- through the comparison isomorphisms, then evaluate the resulting linear map on the basis. With
  -- the fibres free, the basis vector at an input position is the selection of that position
  -- alone, so no closure intervenes between the relation and its matrix.
  module readback {Γ : ctxt} {τ : type 0} (Γ-fo : first-order-ctxt Γ) (fo : first-order τ)
                  (t : Γ ⊢ τ) (γ : Setoid.Carrier (𝒞⟦ Γ-fo ⟧ctxt .Fam⟨𝒞⟩μ.idx)) where

    γ𝒟 = ⟦ Γ-fo ⟧ctxt-iso .fwd .Fam⟨𝒟⟩μ.idxf .func γ
    out𝒟 = 𝒟⟦ t ⟧tm .Fam⟨𝒟⟩μ.idxf .func γ𝒟
    out = closed-iso fo .bwd .Fam⟨𝒟⟩μ.idxf .func out𝒟

    src = 𝒞⟦ Γ-fo ⟧ctxt .Fam⟨𝒞⟩μ.fam .Fam⟨𝒞⟩μ.fm γ
    tgt = 𝒞⟦ fo ⟧ty ∅𝒞 .Fam⟨𝒞⟩μ.fam .Fam⟨𝒞⟩μ.fm out

    abstract
      dep : SemiMod._⇒_ (𝔽 src) (𝔽 tgt)
      dep = SemiMod._∘_
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

      -- The presentation matrix: the image of each input position's basis vector.
      dep-mat : matrix.Mat.Matrix S tgt src
      dep-mat q p = SemiMod._⇒_.func dep (M.e p) q

  -- A linear map between free semimodules is the matrix of its values on the basis, so the
  -- realisation is full and faithful and every first-order term's interpretation is the image of a
  -- weighted relation between dimensions.
  module syntactic = definability 𝔽F-faithful 𝔽F-full
