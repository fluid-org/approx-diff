{-# OPTIONS --prop --postfix-projections --safe #-}

-- Test harness for the two-valued (Bool) model with the call-by-name base interpretation
-- (BaseInterp0: `number` carries no approximation; demand flows through the `Tag` wrapper).  As with
-- example-bool, open this and write `to-gal … (mor …) …` slices directly.
module example-bool-cbn where

open import categories using (HasInitial; HasProducts)
import cmon-enriched as CMon
import matrix-new
import semimodule
import ho-model-semimod
import semiring-bool
import galois
import preorder
import indexed-family
open import example-signature using (Sig; number; label; approx) public
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
open example.ex public                                 -- cbn-query, Tag, …
open import label using (a; b) public

module HM = ho-model-semimod semiring-bool.semiring
module FD = matrix-new.Mat semiring-bool.semiring
module SM = semimodule semiring-bool.semiring
open CMon.CMonEnriched FD.cmon using (_+m_)
open FD using (_∷_; []) public

unitm : FD._⇒_ 0 1
unitm = HasInitial.from-initial FD.initial {1}
conjunctm : FD._⇒_ (HasProducts.prod FD.products 1 1) 1
conjunctm = HasProducts.p₁ FD.products {1} {1} +m HasProducts.p₂ FD.products {1} {1}

open import example-signature-interpretation FD.cat FD.products FD.terminal 1 unitm conjunctm public
open HM.interp Sig BaseInterp0 public
open HM.interp-sd.bsddl Sig BaseInterp0 semiring-bool.boolean using (BooleanSDDL; to-gal; ty-bsddl) public

open indexed-family._⇒f_ public
open SM._⇒_ public
open galois._⇒g_ public
open preorder._=>_ public

-- `Tag τ = base approx [×] τ` as first-order data.
Tag-ty : ∀ {τ} → first-order-data τ → first-order-data (Tag τ)
Tag-ty d = base approx [×] d

-- The fibre (linear) map of a term at a given environment.
mor : ∀ {Γ τ} (tm : Γ ⊢ τ) (env : ⟦ Γ ⟧ctxt .idx .Carrier) → _
mor tm env = ⟦ tm ⟧tm .famf .transf env
