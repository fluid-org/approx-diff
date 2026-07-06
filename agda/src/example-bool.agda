{-# OPTIONS --prop --postfix-projections --safe #-}

-- Test harness for the two-valued (Bool) model with the value-carrying base interpretation
-- (BaseInterp1), over the self-dual Boolean algebras as first-order model.
module example-bool where

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
open import example-signature nat.ℕ using (Sig; number; label; approx) public
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
module Ex = example nat.ℕ
open Ex.ex public                                 -- query, mult-ex, cbn-query, sum, …
open import label using (a; b) public

-- Model instantiation: Boolean approximations over natural-number data; the derivative
-- coefficient collapses a natural to whether it is nonzero.

module BoolAlg-𝟚 = boolalg-sd-semimodule two.semiring two.semiring-boolean
module SemiMod-𝟚 = semimodule two.semiring
open cmon-enriched.CMonEnriched SemiMod-𝟚.cmon-enriched using (εm)

private
  coeff-b : ℕ → Category._⇒_ BoolAlg-𝟚.cat BoolAlg-𝟚.𝕀 BoolAlg-𝟚.𝕀
  coeff-b nat.zero     = εm
  coeff-b (nat.succ _) = Category.id BoolAlg-𝟚.cat BoolAlg-𝟚.𝕀
  coeff-cong-b : ∀ {x y} → nat._≃_ x y → Category._≈_ SemiMod-𝟚.cat (coeff-b x) (coeff-b y)
  coeff-cong-b {nat.zero}   {nat.zero}   _ = Category.≈-refl SemiMod-𝟚.cat {f = coeff-b nat.zero}
  coeff-cong-b {nat.succ _} {nat.succ _} _ = Category.≈-refl SemiMod-𝟚.cat {f = coeff-b (nat.succ nat.zero)}
  coeff-cong-b {nat.zero}   {nat.succ _} (prop._,_ _ ())
  coeff-cong-b {nat.succ _} {nat.zero}   (prop._,_ () _)

open import example-harness using (module BoolAlg-model-coeff; naturals)
open BoolAlg-model-coeff two.semiring two.semiring-boolean naturals coeff-b coeff-cong-b public
open galois._⇒g_ public
open preorder._=>_ public
