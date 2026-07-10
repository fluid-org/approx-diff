{-# OPTIONS --prop --postfix-projections --safe #-}

-- Test harness for the two-valued (Bool) model with the value-carrying base interpretation
-- (BaseInterp1), over the self-dual Boolean algebras as first-order model.
module example.bool where

open import categories using (Category; HasInitial; HasProducts; HasTerminal)
import cmon-enriched
import prop
import semimodule
import boolalg-sd-semimodule
import ho-model-boolalg-sd-semimod
import indexed-family
import galois
import preorder
import nat
open import example.signature nat.ℕ using (Sig; number; label; approx) public
import example

-- Vocabulary re-exported for tests.
open import Level using (lift) public
open import Data.Unit renaming (tt to ·) using () public
open import Data.Product using (_,_) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl) public
open import two renaming (I to ⊤; O to ⊥) using () public
open import nat using (ℕ) public
open import prop-setoid using (Setoid)
open Setoid using (Carrier) public
open import language-syntax Sig hiding (_,_) public   -- _⊢_, types, first-order-data, unit/base/list/_[×]_
module Ex = example nat.ℕ nat.zero
open Ex.ex public                                 -- query, mult-ex, sum, …
open import label using (a; b) public

-- Model instantiation.

module BoolAlg-𝟚 = boolalg-sd-semimodule two.semiring two.semiring-boolean
module SemiMod-𝟚 = semimodule two.semiring
open cmon-enriched.CMonEnriched SemiMod-𝟚.cmon-enriched using (_+m_; εm)

Approx : Category.obj BoolAlg-𝟚.cat
Approx = BoolAlg-𝟚.𝕀

approx-unit : Category._⇒_ BoolAlg-𝟚.cat (HasTerminal.witness BoolAlg-𝟚.terminal) Approx
approx-unit = HasInitial.from-initial BoolAlg-𝟚.initial {Approx}
approx-conjunct : Category._⇒_ BoolAlg-𝟚.cat (HasProducts.prod BoolAlg-𝟚.products Approx Approx) Approx
approx-conjunct = HasProducts.p₁ BoolAlg-𝟚.products {Approx} {Approx}
        +m HasProducts.p₂ BoolAlg-𝟚.products {Approx} {Approx}

open import example.signature-interpretation BoolAlg-𝟚.cat BoolAlg-𝟚.products BoolAlg-𝟚.terminal
  Approx approx-unit approx-conjunct nat.ℕₛ nat.add nat.mult public

-- Boolean-collapse derivative coefficient: zero map vs identity.
private
  coeff-b : ℕ → Category._⇒_ BoolAlg-𝟚.cat Approx Approx
  coeff-b nat.zero     = εm
  coeff-b (nat.succ _) = Category.id BoolAlg-𝟚.cat Approx
  coeff-cong-b : ∀ {x y} → nat._≃_ x y → Category._≈_ SemiMod-𝟚.cat (coeff-b x) (coeff-b y)
  coeff-cong-b {nat.zero}   {nat.zero}   _ = Category.≈-refl SemiMod-𝟚.cat {f = coeff-b nat.zero}
  coeff-cong-b {nat.succ _} {nat.succ _} _ = Category.≈-refl SemiMod-𝟚.cat {f = coeff-b (nat.succ nat.zero)}
  coeff-cong-b {nat.zero}   {nat.succ _} (prop._,_ _ ())
  coeff-cong-b {nat.succ _} {nat.zero}   (prop._,_ () _)

module D = Deriv coeff-b coeff-cong-b
open ho-model-boolalg-sd-semimod.interp-boolean two.semiring two.semiring-boolean Sig D.BaseInterp1 public

open indexed-family._⇒f_ public
open SemiMod-𝟚._⇒_ public
open galois._⇒g_ public
open preorder._=>_ public
