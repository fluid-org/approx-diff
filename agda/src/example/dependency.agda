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
open import functor using (Functor)
open import Data.List using (List; []; _∷_)
import Data.Nat
open import Data.Nat using (ℕ)
import boolalg-sd-semimodule
import ho-model-boolalg-sd-semimod
import semiring-Q
import indexed-family
open import commutative-semiring using (CommutativeSemiring)

open import Level using (lift; 0ℓ) public
open import Data.Unit renaming (tt to ·) using () public
open import Data.Product using (_,_) public
open import Data.Sum using (inj₁; inj₂) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl) public
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
module BoolAlg-𝟚 = boolalg-sd-semimodule two.semiring two.semiring-boolean
module FO𝟚 = ho-model-boolalg-sd-semimod.FO two.semiring two.semiring-boolean
module SDSemiMod-𝟚 = sd-semimodule two.semiring
module SemiMod-𝟚 = semimodule two.semiring
open cmon-enriched.CMonEnriched SemiMod-𝟚.cmon-enriched using (_+m_; εm)

Approx : Category.obj BoolAlg-𝟚.cat
Approx = BoolAlg-𝟚.𝕀

approx-unit : Category._⇒_ BoolAlg-𝟚.cat (HasTerminal.witness BoolAlg-𝟚.terminal) Approx
approx-unit = HasInitial.from-initial BoolAlg-𝟚.initial {Approx}
approx-conjunct : Category._⇒_ BoolAlg-𝟚.cat (HasProducts.prod BoolAlg-𝟚.products Approx Approx) Approx
approx-conjunct = HasProducts.p₁ BoolAlg-𝟚.products {Approx} {Approx}
        +m HasProducts.p₂ BoolAlg-𝟚.products {Approx} {Approx}

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
module SI = example.signature-interpretation BoolAlg-𝟚.cat BoolAlg-𝟚.products BoolAlg-𝟚.terminal
  Approx approx-unit approx-conjunct semiring-Q.setoid num-add num-mult
open SI
open SI using (sort-fibre) public

-- Boolean-collapse derivative coefficient: zero map at 0, identity elsewhere.
private
  coeff-b : ℚ → Category._⇒_ BoolAlg-𝟚.cat Approx Approx
  coeff-b q with q ≟ℚ 0ℚ
  ... | yes _ = εm
  ... | no _ = Category.id BoolAlg-𝟚.cat Approx

  coeff-cong-b : ∀ {x y} → Setoid._≈_ semiring-Q.setoid x y → Category._≈_ SemiMod-𝟚.cat (coeff-b x) (coeff-b y)
  coeff-cong-b {x} (liftS refl) = Category.≈-refl SemiMod-𝟚.cat {f = coeff-b x}

module D = Deriv coeff-b coeff-cong-b
open ho-model-boolalg-sd-semimod.interp-boolean two.semiring two.semiring-boolean Sig D.BaseInterp1 public

-- W-trees indexing the fibres of closed μ-types, for writing inputs.
module T = Pm.Tree {n = 0} (λ ())

open indexed-family._⇒f_ public
open SemiMod-𝟚._⇒_ public
open BoolAlg-𝟚.SelfDualBooleanAlgebra public using (selfDual)

private
  module M𝟚 = matrix.Mat two.semiring

bases-width : List sort → ℕ
bases-width = sorts-width (λ s → FO𝟚.width (sort-fibre s))

op-rel : ∀ {is o'} → op is o' → Category._⇒_ M𝟚.cat (bases-width is) (FO𝟚.width (sort-fibre o'))
op-rel (lit n)     = λ i ()
op-rel add         = λ i j → two.I
op-rel mult        = λ i j → two.I
op-rel (lbl l)     = λ ()
