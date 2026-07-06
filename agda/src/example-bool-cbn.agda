{-# OPTIONS --prop --postfix-projections --safe #-}

-- Test harness for the two-valued (Bool) model with the call-by-name base interpretation
-- (BaseInterp0: `number` carries no approximation; demand flows through the `Tag` wrapper), over the
-- self-dual Boolean algebras as first-order model.  As with example-bool, open this and write
-- `to-gal … (mor …) …` slices directly.
module example-bool-cbn where

open import categories using (Category; HasInitial; HasProducts; HasTerminal)
import cmon-enriched
import semimodule
import boolalg-sd-semimodule
import ho-model-boolalg-sd-semimod
import galois
import preorder
import nat
open import example-signature nat.ℕ using (Sig; number; label; approx) public
import example

open import Level using (lift) public
open import Data.Unit renaming (tt to ·) using () public
open import Data.Product using (_,_) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl) public
open import two renaming (I to ⊤; O to ⊥) using () public
open import nat using (ℕ) public
open import prop-setoid using (Setoid)
open Setoid using (Carrier) public
open import language-syntax Sig hiding (_,_) public
module Ex = example nat.ℕ
open Ex.ex public                                 -- cbn-query, Tag, …
open import label using (a; b) public

-- Model instantiation.
module BoolAlg-𝟚 = boolalg-sd-semimodule two.semiring two.semiring-boolean
module SemiMod-𝟚 = semimodule two.semiring
open cmon-enriched.CMonEnriched SemiMod-𝟚.cmon-enriched using (_+m_)

Approx : Category.obj BoolAlg-𝟚.cat
Approx = BoolAlg-𝟚.𝕀

approx-unit : Category._⇒_ BoolAlg-𝟚.cat (HasTerminal.witness BoolAlg-𝟚.terminal) Approx
approx-unit = HasInitial.from-initial BoolAlg-𝟚.initial {Approx}
approx-conjunct : Category._⇒_ BoolAlg-𝟚.cat (HasProducts.prod BoolAlg-𝟚.products Approx Approx) Approx
approx-conjunct = HasProducts.p₁ BoolAlg-𝟚.products {Approx} {Approx}
        +m HasProducts.p₂ BoolAlg-𝟚.products {Approx} {Approx}

open import example-signature-interpretation BoolAlg-𝟚.cat BoolAlg-𝟚.products BoolAlg-𝟚.terminal
  Approx approx-unit approx-conjunct nat.ℕₛ nat.zero-m nat.add nat.mult public
open ho-model-boolalg-sd-semimod.interp-boolean two.semiring two.semiring-boolean Sig BaseInterp0 public

open SemiMod-𝟚._⇒_ public
open galois._⇒g_ public
open preorder._=>_ public

-- `Tag τ = base approx [×] τ` as first-order data.
Tag-ty : ∀ {τ} → first-order-data τ → first-order-data (Tag τ)
Tag-ty d = base approx [×] d
