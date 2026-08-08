{-# OPTIONS --prop --postfix-projections --safe #-}

-- Value-level tests of the instrumented runs: widths, erasure, and flattening. Dependence-graph
-- content is asserted only by the dot files, which determine it.
module unused.test.instrument where

open import Data.List using ([]; _∷_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Rational using (ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import example.signature ℚ using (Sig)
open import example.relation using (module Instr)
import example.dependency as Dep
open import example.runs
open Instr using (∅; ents; collapse; gwidth; instrument-d; visible-none)

-- Flattening: collapsing the instrumented relation gives the plain run's relation.
flat-mm : ents (collapse (proj₂ inst-mm))
          ≡ ents (proj₁ (proj₂ run-mm))
flat-mm = refl

-- Total width of the fine visible set's intermediates: three entries and four fold steps.
width-query : gwidth (proj₁ inst-query-a-fine) ≡ 7
width-query = refl

-- The run with nothing visible adds no intermediates.
nothing-visible-query : proj₁ (instrument-d (visible-none D-query)) ≡ ∅
nothing-visible-query = refl
