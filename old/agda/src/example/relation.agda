{-# OPTIONS --prop --postfix-projections --safe #-}

-- Instantiation of the logical relation at the example signature: Boolean dependency model over rational
-- data.
module example.relation where

open import Level using (0ℓ)
open import Data.Nat using (ℕ)
open import Data.Rational using (ℚ)
open import categories using (Category)
open import primitives using (Primitives)
import two
import matrix
import language-operational.logical-relation
open import example.signature ℚ using (Sig; sort; number; label; op)
import example.dependency

module Dep = example.dependency

module LR = language-operational.logical-relation Sig Dep.primitives

-- The fundamental property, specialised to this instantiation.
FP : Set
FP = LR.FundamentalProperty

-- Totality, the evaluator and the instrumentation, at the same model.
import language-operational.totality
module Tot = language-operational.totality Sig Dep.primitives

import language-operational.instrument
module Instr = language-operational.instrument Sig Dep.primitives
