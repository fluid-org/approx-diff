{-# OPTIONS --prop --postfix-projections --safe #-}

-- Test harness for Boolean dependency analysis over rational data: the derivative coefficient of
-- a value is the zero map when the value is 0 and the identity otherwise, so the Jacobian entries
-- agree with the nonzero entries of the rational Jacobian, up to the chain rule's
-- over-approximation.
module example.dependency where

open import categories using (Category; HasInitial; HasProducts; HasTerminal)
import cmon-enriched
import prop
import semimodule
import sd-semimodule
import matrix
import matrix-embedding-semimod
open import functor using (Functor)
open import Data.List using (List; []; _∷_)
import Data.Nat
open import Data.Nat using (ℕ)
import ho-model-sd-semimod
import semiring-Q
import indexed-family
open import language-operational.algebra using (Algebra; sort-vals)
import language-operational.algebra
open import commutative-semiring using (CommutativeSemiring)
open import signature using (Model)

open import Level using (lift; 0ℓ) public
open import Data.Unit renaming (tt to ·) using () public
open import Data.Product using (_,_) public
open import Data.Sum using (inj₁; inj₂) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl) public
open import Relation.Binary.PropositionalEquality using (sym) renaming (subst to ≡-subst)
open import Relation.Nullary using (yes; no)
open import two renaming (I to ⊤; O to ⊥) using () public
open import Data.Integer using (+_; -[1+_]) public
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _/_) public
open import Data.Rational using () renaming (_≟_ to _≟ℚ_)
open import Data.Nat.Base public using (nonZero)
open import prop-setoid using (Setoid)
open Setoid using (Carrier) public
open import example.signature ℚ using (Sig; sort; number; label; op; lit; add; mult; lbl) public
import example
open import language-syntax Sig hiding (_,_) public
module Ex = example ℚ 0ℚ
open Ex.ex public
open import label using (a; b) public
open import prop using (liftS; LiftS)

-- Model instantiation: Boolean approximations over rational data.
module SDSemiMod-𝟚 = sd-semimodule two.semiring
module SemiMod-𝟚 = semimodule two.semiring
open cmon-enriched.CMonEnriched SemiMod-𝟚.cmon-enriched using (_+m_; εm)

number-width : ℕ
number-width = 1

Approx : Category.obj SDSemiMod-𝟚.cat
Approx = SDSemiMod-𝟚.S^ number-width

approx-unit : Category._⇒_ SDSemiMod-𝟚.cat (HasTerminal.witness SDSemiMod-𝟚.terminal) Approx
approx-unit = HasInitial.from-initial SDSemiMod-𝟚.initial {Approx}
approx-conjunct : Category._⇒_ SDSemiMod-𝟚.cat (HasProducts.prod SDSemiMod-𝟚.products Approx Approx) Approx
approx-conjunct = HasProducts.p₁ SDSemiMod-𝟚.products {Approx} {Approx}
        +m HasProducts.p₂ SDSemiMod-𝟚.products {Approx} {Approx}

private
  open prop-setoid._⇒_

  module Scalars = CommutativeSemiring semiring-Q.semiring

  num-add : prop-setoid._⇒_ (prop-setoid.⊗-setoid semiring-Q.setoid semiring-Q.setoid) semiring-Q.setoid
  num-add .func (x , y) = x Scalars.+ y
  num-add .func-resp-≈ e = Scalars.+-cong (prop.proj₁ e) (prop.proj₂ e)

  num-mult : prop-setoid._⇒_ (prop-setoid.⊗-setoid semiring-Q.setoid semiring-Q.setoid) semiring-Q.setoid
  num-mult .func (x , y) = x Scalars.· y
  num-mult .func-resp-≈ e = Scalars.·-cong (prop.proj₁ e) (prop.proj₂ e)

import example.signature-interpretation
module SI = example.signature-interpretation SDSemiMod-𝟚.cat SDSemiMod-𝟚.products SDSemiMod-𝟚.terminal
  SDSemiMod-𝟚.S^_ (SDSemiMod-𝟚.terminal .HasTerminal.is-terminal) number-width approx-unit approx-conjunct semiring-Q.setoid num-add num-mult
open SI
open SI using (sort-width) public

-- Boolean-collapse derivative coefficient: zero map at 0, identity elsewhere.
private
  coeff-b : ℚ → Category._⇒_ SDSemiMod-𝟚.cat Approx Approx
  coeff-b q with q ≟ℚ 0ℚ
  ... | yes _ = εm
  ... | no _ = Category.id SDSemiMod-𝟚.cat Approx

  coeff-cong-b : ∀ {x y} → Setoid._≈_ semiring-Q.setoid x y → Category._≈_ SemiMod-𝟚.cat (coeff-b x) (coeff-b y)
  coeff-cong-b {x} (liftS refl) = Category.≈-refl SemiMod-𝟚.cat {f = coeff-b x}

module D = Deriv coeff-b coeff-cong-b
open ho-model-sd-semimod.interp-sd two.semiring Sig D.BaseInterp1 public

-- W-trees indexing the fibres of closed μ-types, for writing inputs.
module T = Pm.Tree {n = 0} (λ ())

open indexed-family._⇒f_ public
open SemiMod-𝟚._⇒_ public

-- Value-level algebra, by projection from the model.
module Alg-inst where
  module PA = language-operational.algebra.IndexAlgebra
                SDSemiMod-𝟚.cat SDSemiMod-𝟚.terminal SDSemiMod-𝟚.products Sig

  Alg : Algebra Sig 0ℓ
  Alg = PA.index-algebra D.BaseInterp1

  sort-val : sort → Set
  sort-val = Algebra.sort-val Alg

open Alg-inst using (sort-val) public

private
  module M𝟚 = matrix.Mat two.semiring

bases-width : List sort → ℕ
bases-width = sorts-width sort-width

-- The dependency relation of an operation at the point where it is applied: the fibre component of
-- the operation's interpretation at those values, read off as a matrix by the inverse of the
-- matrix embedding. Nothing is chosen here; the relation is whatever the model already computes.
private
  module MES = matrix-embedding-semimod two.semiring
  module SMc = Category MES.SDSemiMod.SemiMod.cat

  fib : ∀ {is o'} (ω : op is o') (vs : sort-vals sort-val is) → _
  fib {is} ω vs =
    Fam⟨𝒞⟩.Mor.famf (Model.⟦op⟧ D.BaseInterp1 ω) .indexed-family._⇒f_.transf
      (Alg-inst.PA.tuple D.BaseInterp1 is vs)

  -- The approximation of an operation's arguments: the product of the argument approximations.
  args-approx : List sort → Category.obj SDSemiMod-𝟚.cat
  args-approx []       = HasTerminal.witness SDSemiMod-𝟚.terminal
  args-approx (i ∷ is) =
    HasProducts.prod SDSemiMod-𝟚.products (SDSemiMod-𝟚.S^ (sort-width i)) (args-approx is)

  op-fib : ∀ {is o'} (ω : op is o') (vs : sort-vals sort-val is) →
           Category._⇒_ SDSemiMod-𝟚.cat (args-approx is) (SDSemiMod-𝟚.S^ (sort-width o'))
  -- Matching on the operation so that the argument list, and hence both objects, compute.
  op-fib (lit n) vs = fib (lit n) vs
  op-fib add     vs = fib add vs
  op-fib mult    vs = fib mult vs
  op-fib (lbl l) vs = fib (lbl l) vs

  -- The same map on the underlying semimodules, with both objects pinned.
  U-mor : ∀ {is o'} (ω : op is o') (vs : sort-vals sort-val is) →
          SMc._⇒_ (SDSemiMod-𝟚.U .Functor.fobj (args-approx is))
                  (SDSemiMod-𝟚.U .Functor.fobj (SDSemiMod-𝟚.S^ (sort-width o')))
  U-mor {is} {o'} ω vs =
    SDSemiMod-𝟚.U .Functor.fmor {args-approx is} {SDSemiMod-𝟚.S^ (sort-width o')} (op-fib ω vs)

  -- Move the result out of the free object of its width and into the matrix embedding's.
  out : ∀ n → SMc._⇒_ (SDSemiMod-𝟚.U .Functor.fobj (SDSemiMod-𝟚.S^ n)) (MES.X^ n)
  out n = MES.X^≅S^ n .Category.Iso.bwd

op-rel : ∀ {is o'} → op is o' → sort-vals sort-val is →
        Category._⇒_ M𝟚.cat (bases-width is) (sort-width o')
op-rel (lit n) vs = Functor.fmor MES.mor→mat (out 1 SMc.∘ U-mor (lit n) vs)
op-rel add vs     = Functor.fmor MES.mor→mat (out 1 SMc.∘ U-mor add vs)
op-rel mult vs    = Functor.fmor MES.mor→mat (out 1 SMc.∘ U-mor mult vs)
op-rel (lbl l) vs = Functor.fmor MES.mor→mat (out 0 SMc.∘ U-mor (lbl l) vs)
