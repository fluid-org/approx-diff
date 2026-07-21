{-# OPTIONS --prop --postfix-projections --safe #-}

-- Value-level tests of the instrumented runs: widths, erasure, and flattening. Dependence-graph
-- content is asserted only by the dot files, which determine it.
module test.instrument where

open import Data.List using ([]; _∷_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Rational using (ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import example.signature ℚ using (Sig)
open import example.relation using (module Instr)
import example.dependency as Dep
open import example.runs
open Instr using (∅; ents; collapse; instrument-d; unmarked-d)

-- Flattening: collapsing the instrumented relation gives the plain run's relation.
flat-mm : ents (collapse (proj₁ (proj₂ inst-mm)) (proj₂ (proj₂ inst-mm)))
          ≡ ents (proj₁ (proj₂ run-mm))
flat-mm = refl

-- Total width of the doc-marked query's intermediates: three entries and four fold steps.
width-query : proj₁ inst-query-a-marked ≡ 7
width-query = refl

-- Erasure: the unmarked run adds no intermediates.
erasure-query : proj₁ (instrument-d (unmarked-d D-query) ∅) ≡ 0
erasure-query = refl
