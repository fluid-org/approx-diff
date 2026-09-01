{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- Run from approx-diff repository root.
module example.render.graph-size where

open import IO
open import Data.List using (List; length; map)
open import Data.Nat using (ℕ)
import Data.Nat.Show as ℕ-Show
open import Data.String using (String; _++_)
open import semiring-Q using (nonzero)
import three
open import signature.example.interpretation (nonzero three.semiring) three.semiring
  using (Sig; interpretation)
open import interaction.graph three.semiring (λ x → three.∨-idem {x})
open import interaction.evaluated Sig three.semiring interpretation three.C (λ x → three.∨-idem {x})
open import example.runs (nonzero three.semiring) three.semiring three.C
  using (Run; map-run; filter-run; env; term)

report : String → Run → String
report name r = name ++ ": FO " ++ ℕ-Show.show (length (FO dependence))
                     ++ ", hidden " ++ ℕ-Show.show (length (fo-hidden dependence)) ++ "\n"
  where open Evaluated (env r) (term r)

main : Main
main = run (putStr (report "map" map-run ++ report "filter" filter-run))
