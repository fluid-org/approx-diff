{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- Run from the approx-diff repository root.
module example.render.latex where

open import IO
open import IO.Finite using (writeFile)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.String using (String; _++_)
open import Data.Vec using (toList; tabulate)
import matrix
import three
open import semiring-Q using (nonzero)
open import example.runs (nonzero three.semiring) three.semiring three.C
  using (Run; query-run; const-run; length-run; fold0-run; case0-run; tag-run; case-l-run;
         case-r-run; test-run; map-run; adjacent-sums-run; merge-run; filter-run; cond-run; eq-run;
         mult-run; mavg-run; total-run; sum-mul-run; rose-run; score-run; env; model-output; model-of)
open import example.render.grid using (Tok; Mat; Sel; none; sel-tok; grid)
open import example.render.tokens using (val-toks; env-toks)

private
  module M3 = matrix.Mat three.semiring

  rows : ∀ {m n} → M3.Matrix m n → Mat
  rows M = toList (tabulate (λ q → toList (tabulate (M q))))

  in-toks out-toks : Run → List Tok
  in-toks  r = env-toks (env r)
  out-toks r = val-toks 0 (model-output r)

  run-grid : String → Run → Sel → Sel → String
  run-grid name r isel osel = grid name (in-toks r) (out-toks r) (rows (model-of r)) isel osel

  plain : String → Run → String
  plain name r = run-grid name r none none

  fwd : String → Run → ℕ → String
  fwd name r i = run-grid name r (sel-tok (in-toks r) i) none

  bwd : String → Run → ℕ → String
  bwd name r i = run-grid name r none (sel-tok (out-toks r) i)

contents : String
contents =
  plain "query"         query-run   ++
  plain "const"         const-run   ++
  plain "length"        length-run  ++
  plain "fold0"         fold0-run   ++
  plain "case0"         case0-run   ++
  plain "tag"           tag-run     ++
  plain "case-left"     case-l-run  ++
  plain "case-right"    case-r-run  ++
  plain "test"          test-run    ++
  plain "map"           map-run     ++
  plain "adjacent-sums" adjacent-sums-run ++
  plain "filter"        filter-run  ++
  plain "merge"         merge-run   ++
  plain "cond"          cond-run    ++
  plain "eq"            eq-run      ++
  plain "mult"          mult-run    ++
  plain "mavg"          mavg-run    ++
  plain "total"         total-run   ++
  plain "sum-mul"       sum-mul-run ++
  plain "rose"          rose-run    ++
  plain "score"         score-run   ++
  bwd "map (backward slice)"          map-run           2 ++
  fwd "adjacent-sums (forward slice)" adjacent-sums-run 2 ++
  fwd "merge (forward slice)"         merge-run         5

main : Main
main = run (writeFile "test-baselines/matrices.tex" contents)
