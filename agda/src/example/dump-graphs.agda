{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- Writes dot and trace renderings of the harness examples; run from the paper repository root.
module example.dump-graphs where

open import IO
open import IO.Finite using (writeFile)
open import Data.Rational using (ℚ)
open import example.signature ℚ using (Sig)
open import example.relation-boolean using (sort-width; module Alg-inst)
open import example.trace-boolean using (show-op; dep-graph; D-add; D-query)
open import language-operational.trace Sig Alg-inst.Alg sort-width show-op
  using (show-eval; showDot)

main : Main
main = run do
  writeFile "fig/dot/add.dot" (showDot (dep-graph D-add))
  writeFile "fig/dot/query-a.dot" (showDot (dep-graph D-query))
  writeFile "fig/trace/add.trace" (show-eval D-add)
  writeFile "fig/trace/query-a.trace" (show-eval D-query)
