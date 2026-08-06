{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- Writes the three-weighted map dependence graph as dot: the input and output values as trees,
-- dependence edges across, solid for value flow (d) and dashed for control (c); run from the
-- paper repository root.
module graph-viz.dump-dep-graph where

open import IO
open import IO.Finite using (writeFile)
open import Data.String using (String; _++_)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.List using (List; []; _∷_) renaming (foldr to foldrL; map to mapL)
open import Data.Nat using (ℕ; zero; suc)
import Data.Nat.Show as ℕ-Show
open import Data.Product using (_×_; _,_)
open import Data.Vec using (toList; tabulate)
open import Level using (0ℓ)
import three
import matrix
open import example.rooted-runs-three using (dep-map)

private
  module TM3 = matrix.Mat three.semiring

  -- Position labels for the eleven positions of the three-element number list.
  labels : List String
  labels = "∷" ∷ "pr" ∷ "0" ∷ "∷" ∷ "pr" ∷ "1" ∷ "∷" ∷ "pr" ∷ "2" ∷ "[]" ∷ "()" ∷ []

  out-labels : List String
  out-labels = "∷" ∷ "pr" ∷ "1" ∷ "∷" ∷ "pr" ∷ "2" ∷ "∷" ∷ "pr" ∷ "3" ∷ "[]" ∷ "()" ∷ []

  -- The value tree: parent to child within a list of numbers.
  tree : List (ℕ × ℕ)
  tree = (0 , 1) ∷ (1 , 2) ∷ (1 , 3) ∷ (3 , 4) ∷ (4 , 5) ∷ (4 , 6)
       ∷ (6 , 7) ∷ (7 , 8) ∷ (7 , 9) ∷ (9 , 10) ∷ []

  node : String → ℕ → String → String
  node pre i l =
    "    " ++ pre ++ ℕ-Show.show i ++ " [label=\"" ++ l ++ "\"];\n"

  nodes : String → List String → String
  nodes pre ls = go 0 ls
    where
    go : ℕ → List String → String
    go _ []       = ""
    go i (l ∷ ls) = node pre i l ++ go (suc i) ls

  tree-edges : String → String
  tree-edges pre =
    foldrL (λ e s → edge e ++ s) "" tree
    where
    edge : ℕ × ℕ → String
    edge (i , j) =
      "    " ++ pre ++ ℕ-Show.show i ++ " -> " ++ pre ++ ℕ-Show.show j
      ++ " [color=gray, arrowhead=none];\n"

  dep-edge : three.Three → ℕ → ℕ → String
  dep-edge three.O _ _ = ""
  dep-edge three.D p q =
    "  i" ++ ℕ-Show.show p ++ " -> o" ++ ℕ-Show.show q ++ " [color=black];\n"
  dep-edge three.C p q =
    "  i" ++ ℕ-Show.show p ++ " -> o" ++ ℕ-Show.show q
    ++ " [color=black, style=dashed];\n"

  dep-edges : String
  dep-edges = go 0 (toList (tabulate (λ q → toList (tabulate (dep-map q)))))
    where
    row : ℕ → ℕ → List three.Three → String
    row _ _ []       = ""
    row q p (w ∷ ws) = dep-edge w p q ++ row q (suc p) ws
    go : ℕ → List (List three.Three) → String
    go _ []         = ""
    go q (r ∷ rs) = row q 0 r ++ go (suc q) rs

contents : String
contents =
  "digraph G {\n  rankdir=LR;\n  node [shape=circle, fontsize=11];\n"
  ++ "  subgraph cluster_in {\n    label=\"input\";  color=none;\n"
  ++ nodes "i" labels ++ tree-edges "i" ++ "  }\n"
  ++ "  subgraph cluster_out {\n    label=\"output\"; color=none;\n"
  ++ nodes "o" out-labels ++ tree-edges "o" ++ "  }\n"
  ++ dep-edges
  ++ "}\n"

main : Main
main = run (writeFile "fig/dot/map-three.dot" contents)
