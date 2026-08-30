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
import Data.Product
import Data.List
import prop
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import categories
  using (Category; HasTerminal; IsTerminal; HasCoproducts; HasExponentials; setoid→category)
open import signature using (Signature; Model; PFPC[_,_,_,_])
open import signature.interpretation using (Interpretation; sort-vals-setoid)
open import Data.Sum using (inj₁; inj₂)
open import cmon-enriched using (CMonEnriched)
open import functor using (cones→limits)
import indexed-family
open import indexed-family using (HasSetoidProducts; Fam; _⇒f_; _[_])
import matrix
import fam
import fam-mu-lifting
import fam-exponentials
import matrix-embedding
import matrix-primitives
import language-fo-interpretation
import language-syntax

module ho-model
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (ctrl-weight : Setoid.Carrier A)
  where

open matrix-embedding S public
open lifting-SemiMod using (L; Lmap)
private
  module S = CommutativeSemiring S

open SemiMod._≈m_
open SemiMod._⇒_
open prop-setoid._⇒_ using (func; func-resp-≈)
open prop-setoid._≃m_ using (func-eq)

module Fam⟨𝒞⟩μ = fam-mu-lifting 0ℓ 0ℓ M.cmon M.biproduct 1
module Fam⟨𝒟⟩μ = fam-mu-lifting 0ℓ 0ℓ SemiMod.cmon-enriched SemiMod.biproduct SemiMod.𝕀

private
  module Fam⟨𝒞⟩μ-CP = HasCoproducts Fam⟨𝒞⟩μ.coproducts

ctrl-weight-endo : SemiMod._⇒_ SemiMod.𝕀 SemiMod.𝕀
ctrl-weight-endo = ι1-fwd SemiMod.∘ (mat (matrix.Mat.block S ctrl-weight) SemiMod.∘ ι1-bwd)

𝟙F = HasTerminal.witness (Fam⟨𝒞⟩μ.terminal M.terminal)

𝒞𝟙ty : Fam⟨𝒞⟩μ.Obj
𝒞𝟙ty = Fam⟨𝒞⟩μ.Lf 𝟙F

𝒞Bool = Fam⟨𝒞⟩μ-CP.coprod (Fam⟨𝒞⟩μ.Lf 𝒞𝟙ty) (Fam⟨𝒞⟩μ.Lf 𝒞𝟙ty)

𝒞Bool-root : Fam⟨𝒞⟩μ.Section 𝒞Bool
𝒞Bool-root = Fam⟨𝒞⟩μ.coprod-section (Fam⟨𝒞⟩μ.Lf-root {𝒞𝟙ty}) (Fam⟨𝒞⟩μ.Lf-root {𝒞𝟙ty})

SPmod : HasSetoidProducts 0ℓ 0ℓ SemiMod.cat
SPmod =
  indexed-family.hasSetoidProducts 0ℓ 0ℓ SemiMod.cat
    (λ A → cones→limits (SemiMod.limits (setoid→category A)))

module exp = fam-exponentials 0ℓ 0ℓ SemiMod.cat SemiMod.cmon-enriched SemiMod.biproduct SPmod

SemiModExp : HasExponentials Fam⟨𝒟⟩μ.cat Fam⟨𝒟⟩μ.products
SemiModExp = exp.exponentials

-- The unit section of a function space is zero: an eliminator returning a function attaches
-- control dependence to the root the lifting adjoins alone, matching the operational semantics,
-- where a closure's control positions are its root alone (language-operational.evaluation.ctrl-of).
-- The tuple of the target's section over every argument would instead attach it to every
-- possible result, which no position of a closure stands for.
open CMonEnriched SemiMod.cmon-enriched using (εm; comp-bilinear-ε₂)

exp-section : ∀ {X Y : Fam⟨𝒟⟩μ.Obj} → Fam⟨𝒟⟩μ.Section (exp._⟶_ X Y)
exp-section {X} {Y} .Fam⟨𝒟⟩μ.at f = εm
exp-section {X} {Y} .Fam⟨𝒟⟩μ.at-natural {f₁} {f₂} e =
  comp-bilinear-ε₂ {SemiMod.𝕀} (exp._⟶_ X Y .Fam⟨𝒟⟩μ.fam .Fam⟨𝒟⟩μ.subst {f₁} {f₂} e)

module sig-model (Sig : Signature 0ℓ) (ℐ : Interpretation S Sig) where

  module ℐ = Interpretation ℐ

  boolify : Fam⟨𝒞⟩μ.Mor (matrix-primitives.Fam⟨𝒞⟩-bool S) 𝒞Bool
  boolify =
    Fam⟨𝒞⟩μ-CP.coprod-m
      (Fam⟨𝒞⟩μ.injF {X = 𝒞𝟙ty} Fam⟨𝒞⟩μ.Fam-cat.∘ Fam⟨𝒞⟩μ.injF {X = 𝟙F})
      (Fam⟨𝒞⟩μ.injF {X = 𝒞𝟙ty} Fam⟨𝒞⟩μ.Fam-cat.∘ Fam⟨𝒞⟩μ.injF {X = 𝟙F})

  module prim = matrix-primitives.interp-primitives S Sig ℐ 𝒞Bool boolify

  private
    open prim using (model-over; arg-collect)
    open indexed-family._⇒f_

    d' : ∀ {is} (ψ : Signature.rel Sig is)
         (c : Setoid.Carrier (sort-vals-setoid ℐ.sort-index is)) →
         M.Matrix 1 (ℐ.bases-width is)
    d' ψ c = ℐ.rel-deps ψ .func c

  -- Tests write their dependence into the outcome's root: which branch runs reads the scalars the
  -- test read.
  rel-simple : ∀ is (ψ : Signature.rel Sig is) →
               Fam⟨𝒞⟩μ.Mor
                 Fam⟨𝒞⟩μ.simple[ sort-vals-setoid ℐ.sort-index is , ℐ.bases-width is ]
                 𝒞Bool
  rel-simple is ψ .Fam⟨𝒞⟩μ.idxf = ℐ.rel-pred ψ
  rel-simple is ψ .Fam⟨𝒞⟩μ.famf .transf c = 𝒞Bool-root .Fam⟨𝒞⟩μ.at (ℐ.rel-pred ψ .func c) M.∘ d' ψ c
  rel-simple is ψ .Fam⟨𝒞⟩μ.famf .natural {c} {c'} e =
    M.≈ₘ-trans (M.id-right {M = P' M.∘ d' ψ c'})
    (M.≈ₘ-trans (M.∘-cong (M.≈ₘ-refl {f = P'}) (M.≈ₘ-sym (ℐ.rel-deps ψ .func-resp-≈ e)))
    (M.≈ₘ-trans (M.∘-cong (M.≈ₘ-sym (𝒞Bool-root .Fam⟨𝒞⟩μ.at-natural {x₁ = o} {x₂ = o'} (ℐ.rel-pred ψ .func-resp-≈ e)))
                          (M.≈ₘ-refl {f = d' ψ c}))
                (M.assoc sub (𝒞Bool-root .Fam⟨𝒞⟩μ.at o) (d' ψ c))))
    where
    o  = ℐ.rel-pred ψ .func c
    o' = ℐ.rel-pred ψ .func c'
    P' = 𝒞Bool-root .Fam⟨𝒞⟩μ.at o'
    sub = 𝒞Bool .Fam⟨𝒞⟩μ.fam .Fam⟨𝒞⟩μ.subst {o} {o'} (ℐ.rel-pred ψ .func-resp-≈ e)

  model : Model PFPC[ Fam⟨𝒞⟩μ.cat , Fam⟨𝒞⟩μ.terminal M.terminal , Fam⟨𝒞⟩μ.products , 𝒞Bool ] Sig
  model = record model-over
    { ⟦rel⟧ = λ {is} ψ → (rel-simple is ψ Fam⟨𝒞⟩μ.Fam-cat.∘ arg-collect is) }

module interp (Sig : Signature 0ℓ) (ℐ : Interpretation S Sig) where

  open sig-model Sig ℐ

  𝒞-sort-section : ∀ s → Fam⟨𝒞⟩μ.Section (model .Model.⟦sort⟧ s)
  𝒞-sort-section s = Fam⟨𝒞⟩μ.simple-section (λ _ _ → S.ι)

  open language-fo-interpretation Sig 0ℓ 0ℓ
    M.terminal M.cmon M.biproduct 1
    SemiMod.terminal SemiMod.cmon-enriched SemiMod.biproduct SemiMod.𝕀
    𝔽F 𝔽F-preserve-terminal (λ {m} {n} → 𝔽F-preserve-products {m} {n})
    𝔽-L-iso (λ {P} {Q} f → 𝔽-L-natural {P} {Q} f)
    SemiModExp
    𝒞𝟙ty Fam⟨𝒞⟩μ.injF model
    ctrl-weight-endo (λ {X} {Y} → exp-section {X} {Y}) ι1-bwd
    (Fam⟨𝒞⟩μ.Lf-section (Fam⟨𝒞⟩μ.simple-section (M.terminal .HasTerminal.is-terminal .IsTerminal.to-terminal)))
    𝒞-sort-section
    public

  open language-syntax Sig using (ctxt; type; _⊢_; first-order; first-order-ctxt)
  open Category.Iso
  open indexed-family._⇒f_ using (transf)

  open Fam⟨𝒟⟩μ using (idx; fam; fm; idxf; famf; subst)
  open SemiMod using (Semimodule)
  open Data.Product using (_,_)
  open prop using (_,_)

  bool-elt : ∀ b → Setoid.Carrier A → Semimodule.Carrier (𝒟Bool .fam .fm b)
  bool-elt (inj₁ _) a = a , (λ _ → S.ε)
  bool-elt (inj₂ _) a = a , (λ _ → S.ε)

  bool-elt-cong : ∀ b {a a'} → Setoid._≈_ A a a' →
                  Semimodule._≈_ (𝒟Bool .fam .fm b) (bool-elt b a) (bool-elt b a')
  bool-elt-cong (inj₁ _) e = e , λ _ → S.refl
  bool-elt-cong (inj₂ _) e = e , λ _ → S.refl

  private
    Lmap-elt : ∀ {X Y : Semimodule} (f : SemiMod._⇒_ X Y) (a : Setoid.Carrier A)
               (x : Semimodule.Carrier X) →
               Semimodule._≈_ (L Y) (SemiMod._⇒_.func (Lmap f) (a , x)) (a , SemiMod._⇒_.func f x)
    Lmap-elt {X} {Y} f a x = S.+-runit , Semimodule.+-lunit Y

    module bool-row {n} (D : M.Matrix 1 n) (y : M.Vec n) where
      Ω = Fam⟨F⟩-preserves-bool

      private
        u = app (M.in₁ {1} {1} M.∘ D) y

        branch : ∀ {x₁ x} (e : Setoid._≈_ (𝒟𝟙ty .idx) x₁ x) →
                 Semimodule._≈_ (L (𝔽 1))
                   (SemiMod._⇒_.func (Lmap (𝒟𝟙ty .fam .subst {x₁} {x} e))
                      (SemiMod._⇒_.func (𝔽-L-iso 1 .fwd) u))
                   (app D y Fin.zero , λ _ → S.ε)
        branch {x₁} {x} e =
          Semimodule.trans (L (𝔽 1))
            (Lmap-elt (𝒟𝟙ty .fam .subst {x₁} {x} e) (u Fin.zero) (λ k → u (Fin.suc k)))
            (S.trans (app-∘ (M.in₁ {1} {1}) D y Fin.zero) (app-in₁ {1} {1} (app D y) Fin.zero) ,
             λ k → S.trans (app-congᵥ G (λ j → S.trans (app-∘ (M.in₁ {1} {1}) D y (Fin.suc j))
                                                       (app-in₁ {1} {1} (app D y) (Fin.suc j))) k)
                            (app-ε G k))
          where
          G = 𝒞𝟙ty .Fam⟨𝒞⟩μ.fam .Fam⟨𝒞⟩μ.subst {x₁} {x} e

      core : ∀ i₀ b (e : Setoid._≈_ (𝒟Bool .idx) (Ω .idxf .func i₀) b) →
             Semimodule._≈_ (𝒟Bool .fam .fm b)
               (SemiMod._⇒_.func (𝒟Bool .fam .subst {Ω .idxf .func i₀} {b} e)
                 (SemiMod._⇒_.func (Ω .famf .transf i₀) (app (𝒞Bool-root .Fam⟨𝒞⟩μ.at i₀ M.∘ D) y)))
               (bool-elt b (app D y Fin.zero))
      core (inj₁ _) (inj₁ _) e = branch e
      core (inj₂ _) (inj₂ _) e = branch e

  Args : Data.List.List (Signature.sort Sig) → Fam⟨𝒟⟩μ.Obj
  Args = signature.finite-product (Fam⟨𝒟⟩μ.terminal SemiMod.terminal) Fam⟨𝒟⟩μ.products
           (Model.⟦sort⟧ 𝒟-Sig-model)

  module test {is} (ω : Signature.rel Sig is)
    (p : Setoid.Carrier (Args is .idx)) (z : Semimodule.Carrier (Args is .fam .fm p)) where

    private
      p𝒞 = 𝒟-arg-product is .idxf .func p
      z𝒞 = SemiMod._⇒_.func (𝒟-arg-product is .famf .transf p) z
      C = prim.collect is .Fam⟨𝒞⟩μ.famf .transf p𝒞
      test = Model.⟦rel⟧ 𝒟-Sig-model ω

    args-idx = prim.collect is .Fam⟨𝒞⟩μ.idxf .func p𝒞
    args-vec = app C z𝒞

    test-elt : ∀ b (e : Setoid._≈_ (𝒟Bool .idx) (test .idxf .func p) b) →
               Semimodule._≈_ (𝒟Bool .fam .fm b)
                 (SemiMod._⇒_.func (𝒟Bool .fam .subst {test .idxf .func p} {b} e)
                   (SemiMod._⇒_.func (test .famf .transf p) z))
                 (bool-elt b (app (ℐ.rel-deps ω .func args-idx) args-vec Fin.zero))
    test-elt b e =
      Semimodule.trans (𝒟Bool .fam .fm b)
        (SemiMod._⇒_.func-resp-≈ (𝒟Bool .fam .subst {test .idxf .func p} {b} e)
          (SemiMod._⇒_.func-resp-≈ (bool-row.Ω D args-vec .famf .transf i₀) elt))
        (bool-row.core D args-vec i₀ b e)
      where
      i₀ = ℐ.rel-pred ω .func args-idx
      D = ℐ.rel-deps ω .func args-idx
      P = 𝒞Bool-root .Fam⟨𝒞⟩μ.at i₀
      elt : ∀ k → S._≈_ (app (M.I M.∘ ((P M.∘ D) M.∘ C)) z𝒞 k)
                         (app (P M.∘ D) args-vec k)
      elt k = S.trans (app-∘ M.I ((P M.∘ D) M.∘ C) z𝒞 k)
                (S.trans (app-I (app ((P M.∘ D) M.∘ C) z𝒞) k) (app-∘ (P M.∘ D) C z𝒞 k))

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

      mat-of : M.Matrix tgt src
      mat-of q p = SemiMod._⇒_.func rel (M.e p) q

      presents : mat mat-of SemiMod.≈m rel
      presents = 𝔽F-full rel .prop.∃ₛ.snd
