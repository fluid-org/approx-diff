{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- Writes dot and trace renderings of the harness examples; run from the paper repository root.
module example.dump-graphs where

open import IO
open import IO.Finite using (writeFile)
open import Data.Rational using (ℚ)
open import example.signature ℚ using (Sig)
open import example.trace-boolean using (show-op; D-add; D-query)
open import example.instrument-boolean using (dep-edges; inst-query; inst-add-full; inst-query-full)
open import Data.Product using (proj₁; proj₂)
import example.dependency as Dep
open import language-operational.trace Sig Dep.primitives show-op
  using (show-eval; showDotPlain)

main : Main
main = run do
  writeFile "fig/dot/add.dot" (showDotPlain (dep-edges (proj₁ (proj₂ (proj₂ inst-add-full)))))
  writeFile "fig/dot/query-a.dot" (showDotPlain (dep-edges (proj₁ (proj₂ (proj₂ inst-query-full)))))
  writeFile "fig/dot/query-a-marked.dot" (showDotPlain (dep-edges (proj₁ (proj₂ (proj₂ inst-query)))))
  writeFile "fig/trace/add.trace" (show-eval D-add)
  writeFile "fig/trace/query-a.trace" (show-eval D-query)
