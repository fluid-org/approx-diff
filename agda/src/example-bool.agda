{-# OPTIONS --prop --postfix-projections --safe #-}

-- Test harness for the two-valued (Bool) model with the value-carrying base interpretation
-- (BaseInterp1).  Open this in a test file and write `fwd …` / `bwd …` slices and `≡` checks directly;
-- all the model plumbing lives here and compiles once.
module example-bool where

open import categories using (Category; HasInitial; HasProducts; HasTerminal)
import cmon-enriched as CMon
import prop
import matrix-new
import semimodule
import ho-model-semimod
import galois
import preorder
import indexed-family
open import example-signature using (Sig; number; label; approx) public
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
open example.ex public                                 -- query, mult-ex, cbn-query, sum, …
open import label using (a; b) public

-- Model instantiation.
module HM = ho-model-semimod two.semiring
module FD = matrix-new.Mat two.semiring
module SM = semimodule two.semiring
open CMon.CMonEnriched FD.cmon using (_+m_; εm)
open FD using (_∷_; []) public

unitm : FD._⇒_ 0 1
unitm = HasInitial.from-initial FD.initial {1}
conjunctm : FD._⇒_ (HasProducts.prod FD.products 1 1) 1
conjunctm = HasProducts.p₁ FD.products {1} {1} +m HasProducts.p₂ FD.products {1} {1}

open import example-signature-interpretation FD.cat FD.products FD.terminal 1 unitm conjunctm
  nat.ℕₛ nat.zero-m nat.add nat.mult public

-- Boolean-collapse derivative coefficient: zero map vs identity.
private
  module FDm = Category FD.cat
  coeff-b : ℕ → FD._⇒_ 1 1
  coeff-b nat.zero     = εm
  coeff-b (nat.succ _) = FDm.id 1
  coeff-cong-b : ∀ {x y} → nat._≃_ x y → coeff-b x FDm.≈ coeff-b y
  coeff-cong-b {nat.zero}   {nat.zero}   _ = FDm.≈-refl {f = εm}
  coeff-cong-b {nat.succ _} {nat.succ _} _ = FDm.≈-refl {f = FDm.id 1}
  coeff-cong-b {nat.zero}   {nat.succ _} (prop._,_ _ ())
  coeff-cong-b {nat.succ _} {nat.zero}   (prop._,_ () _)

module D = Deriv coeff-b coeff-cong-b
open HM.interp Sig D.BaseInterp1 public
open HM.interp-sd.bsddl Sig D.BaseInterp1 two.semiring-boolean using (BooleanSDDL; to-gal; ty-bsddl) public

open indexed-family._⇒f_ public
open SM._⇒_ public
open galois._⇒g_ public
open preorder._=>_ public

-- The fibre (linear) map of a term at a given environment.
mor : ∀ {Γ τ} (tm : Γ ⊢ τ) (env : ⟦ Γ ⟧ctxt .idx .Carrier) → _
mor tm env = ⟦ tm ⟧tm .famf .transf env

-- Forward slice: feed an input demand, read the output demand.
fwd : ∀ {Γ τ} (tm : Γ ⊢ τ) (env : ⟦ Γ ⟧ctxt .idx .Carrier) → _
fwd tm env = mor tm env .func

-- Backward slice: `to-gal input output (mor tm env) .right .fun demand`, with input/output the BooleanSDDLs
-- of the term's domain/codomain (built with `ty-bsddl`).  Inlined at the call site so the obj types unify.
