{-# OPTIONS --prop --postfix-projections --safe #-}

-- Test harness for the two-valued (Bool) model with the call-by-name base interpretation
-- (BaseInterp0: `number` carries no approximation; demand flows through the `Tag` wrapper), over the
-- self-dual Boolean algebras as first-order model.  As with example-bool, open this and write
-- `to-gal … (mor …) …` slices directly.
module example-bool-cbn where

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

-- Model instantiation: numbers carry trivial fibres (BaseInterp0); dependency is tracked on the
-- value side by the annotations the call-by-name translation threads through the Tag monad.
open import example-harness using (module BoolAlg-model-base; naturals)
open BoolAlg-model-base two.semiring two.semiring-boolean naturals public
open ho-model-boolalg-sd-semimod.interp-boolean two.semiring two.semiring-boolean Sig BaseInterp0 public

open SemiMod._⇒_ public
open galois._⇒g_ public
open preorder._=>_ public

-- `Tag τ = base approx [×] τ` as first-order data.
Tag-ty : ∀ {τ} → first-order-data τ → first-order-data (Tag τ)
Tag-ty d = base approx [×] d
