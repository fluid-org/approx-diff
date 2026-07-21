{-# OPTIONS --prop --postfix-projections --safe #-}

-- Value-level tests of the instrumented runs: widths, erasure, flattening, and the small
-- dependence graphs.
module test.instrument where

open import Data.List using ([]; _∷_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Rational using (ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import example.signature ℚ using (Sig)
open import example.relation using (module Instr)
import example.dependency as Dep
open import example.runs
open import language-operational.marking Sig using (unmarked)
open Instr using (∅; emp; ents; collapse; dep-edges; edge-rel)

-- Flattening: collapsing the instrumented relation gives the plain run's relation.
flat-mm : ents (collapse (proj₁ (proj₂ (proj₂ inst-mm))) (proj₂ (proj₂ (proj₂ inst-mm))))
          ≡ ents (proj₁ (proj₂ run-mm))
flat-mm = refl

-- Total width of the doc-marked query's intermediates: three entries and four fold steps.
width-query : proj₁ (proj₂ inst-query-a-marked) ≡ 7
width-query = refl

-- Erasure: the unmarked run adds no intermediates.
erasure-query : proj₁ (proj₂ (Instr.instrument (unmarked _) emp D-query ∅)) ≡ 0
erasure-query = refl

-- The everything-marked graphs.
dep-graph-add-full : dep-edges (proj₁ (proj₂ (proj₂ inst-add-full))) ≡ ((0 , 2) ∷ (1 , 2) ∷ [])
dep-graph-add-full = refl

-- At (x , y) = (1 , 0) the derivative of x * y is [ 0 , 1 ]: the result depends on the second
-- argument only.
dep-graph-mult-full : dep-edges (proj₁ (proj₂ (proj₂ inst-mult-full))) ≡ ((1 , 2) ∷ [])
dep-graph-mult-full = refl

-- Coarse marking: one edge, whose relation names the two consulted positions.
coarse-edges : dep-edges (proj₁ (proj₂ (proj₂ inst-query-a-coarse))) ≡ ((0 , 1) ∷ [])
coarse-edges = refl

coarse-rel : edge-rel (proj₁ (proj₂ (proj₂ inst-query-a-coarse))) 0 1 ≡ ((0 , 0) ∷ (2 , 0) ∷ [])
coarse-rel = refl
