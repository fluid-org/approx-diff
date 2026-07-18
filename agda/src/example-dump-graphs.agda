{-# OPTIONS --postfix-projections --prop --guardedness #-}

module example-dump-graphs where

open import IO
open import IO.Finite using (writeFile)
open import example
open import example-mat-model

open import Level using (lift)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₂)
open import every using ([]; _∷_)
import label as L

main : Main
main = run do
  writeFile "fig/dot/add.dot" (showDot (dependence-graph M-add ((lift tt , 2) , 3)))
  writeFile "fig/dot/query-a.dot" (showDot (dependence-graph (query L.a) (lift tt , input)))
  writeFile "fig/trace/add.trace" (show-eval-pretty (proj₂ (proj₂ (eval M-add ((lift tt , 2) , 3)))))
  writeFile "fig/trace/query-a.trace" (show-eval-pretty (proj₂ (proj₂ (eval (query L.a) (lift tt , input)))))
