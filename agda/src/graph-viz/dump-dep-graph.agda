{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- Writes the three-weighted map dependence graph as dot, in two views: the full skeleton, and the
-- sugar view with each former merged into its enclosing injection, dependence edges joined by the
-- semiring's addition. Nodes, labels, tree edges and merge classes all come from the value
-- skeleton of the input and output values; run from the paper repository root.
module graph-viz.dump-dep-graph where

open import IO
open import IO.Finite using (writeFile)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_)
open import Data.String using (String; _++_; _==_)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
import Data.Nat.Show as ℕ-Show
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Vec using (toList; tabulate)
open import Level using (0ℓ)
import three
import example.primitives as EP
open import example.rooted-runs-three using (dep-map)
open import graph-viz.dump-slices using (γ-nums-val; δ-out; showC)
open import language-operational.value-skeleton EP.Sig EP.primitives using (Entry; skeleton)
open Entry

private
  Entries : Set
  Entries = List (ℕ × Entry)

  index : ℕ → List Entry → Entries
  index _ []       = []
  index i (e ∷ es) = (i , e) ∷ index (suc i) es

  in-sk out-sk : Entries
  in-sk  = index 0 (skeleton (λ {s} c → showC {s} c) γ-nums-val)
  out-sk = index 0 (skeleton (λ {s} c → showC {s} c) δ-out)

  -- List notation for the body's injections, as in the partial-value renderer.
  sugar : String → String
  sugar l = if l == "inr" then "∷" else if l == "inl" then "[]" else l

  cls-of : Entries → ℕ → ℕ
  cls-of []             i = i
  cls-of ((j , e) ∷ es) i = if i ≡ᵇ j then e .cls else cls-of es i

  node : String → ℕ → String → String
  node pre i l = "    " ++ pre ++ ℕ-Show.show i ++ " [label=\"" ++ l ++ "\"];\n"

  nodes : String → Entries → String
  nodes pre []             = ""
  nodes pre ((i , e) ∷ es) = node pre i (sugar (e .label)) ++ nodes pre es

  nodes-merged : String → Entries → String
  nodes-merged pre []             = ""
  nodes-merged pre ((i , e) ∷ es) =
    (if i ≡ᵇ e .cls then node pre i (sugar (e .label)) else "") ++ nodes-merged pre es

  tree-edge : String → ℕ → ℕ → String
  tree-edge pre i j =
    "    " ++ pre ++ ℕ-Show.show i ++ " -> " ++ pre ++ ℕ-Show.show j
    ++ " [color=gray, arrowhead=none];\n"

  tree-edges : String → Entries → String
  tree-edges pre []             = ""
  tree-edges pre ((i , e) ∷ es) with e .parent
  ... | just p  = tree-edge pre p i ++ tree-edges pre es
  ... | nothing = tree-edges pre es

  member : ℕ × ℕ → List (ℕ × ℕ) → Bool
  member _       []             = false
  member (i , j) ((k , l) ∷ ps) = ((i ≡ᵇ k) ∧ (j ≡ᵇ l)) ∨ member (i , j) ps

  -- Tree edges between classes: self-loops vanish and repeats are dropped.
  merged-tree : Entries → Entries → List (ℕ × ℕ) → List (ℕ × ℕ)
  merged-tree all []             acc = acc
  merged-tree all ((i , e) ∷ es) acc with e .parent
  ... | nothing = merged-tree all es acc
  ... | just p  =
    if ((cls-of all p) ≡ᵇ (e .cls)) ∨ member (cls-of all p , e .cls) acc
    then merged-tree all es acc
    else merged-tree all es ((cls-of all p , e .cls) ∷ acc)

  tree-edges-of : String → List (ℕ × ℕ) → String
  tree-edges-of pre []             = ""
  tree-edges-of pre ((i , j) ∷ ps) = tree-edge pre i j ++ tree-edges-of pre ps

  dep-edge : three.Three → ℕ → ℕ → String
  dep-edge three.O _ _ = ""
  dep-edge three.D p q =
    "  i" ++ ℕ-Show.show p ++ " -> o" ++ ℕ-Show.show q
    ++ " [color=blue, constraint=false];\n"
  dep-edge three.C p q =
    "  i" ++ ℕ-Show.show p ++ " -> o" ++ ℕ-Show.show q
    ++ " [color=black, style=dashed, constraint=false];\n"

  rows : List (List three.Three)
  rows = toList (tabulate (λ q → toList (tabulate (dep-map q))))

  dep-edges : String
  dep-edges = go 0 rows
    where
    row : ℕ → ℕ → List three.Three → String
    row _ _ []       = ""
    row q p (w ∷ ws) = dep-edge w p q ++ row q (suc p) ws
    go : ℕ → List (List three.Three) → String
    go _ []       = ""
    go q (r ∷ rs) = row q 0 r ++ go (suc q) rs

  Edge : Set
  Edge = ℕ × ℕ × three.Three

  -- Insert an edge between classes, joining the weight with any edge already present.
  upd : ℕ → ℕ → three.Three → List Edge → List Edge
  upd p q w [] = (p , q , w) ∷ []
  upd p q w ((p' , q' , w') ∷ es) =
    if (p ≡ᵇ p') ∧ (q ≡ᵇ q')
    then (p' , q' , w three.⊔ w') ∷ es
    else (p' , q' , w') ∷ upd p q w es

  quotient : List Edge
  quotient = go-q 0 rows []
    where
    add : ℕ → ℕ → three.Three → List Edge → List Edge
    add p q three.O acc = acc
    add p q w       acc = upd (cls-of in-sk p) (cls-of out-sk q) w acc
    go-p : ℕ → ℕ → List three.Three → List Edge → List Edge
    go-p q _ []       acc = acc
    go-p q p (w ∷ ws) acc = go-p q (suc p) ws (add p q w acc)
    go-q : ℕ → List (List three.Three) → List Edge → List Edge
    go-q _ []       acc = acc
    go-q q (r ∷ rs) acc = go-q (suc q) rs (go-p q 0 r acc)

  dep-edges-merged : String
  dep-edges-merged = go quotient
    where
    go : List Edge → String
    go []                 = ""
    go ((p , q , w) ∷ es) = dep-edge w p q ++ go es

  graph : String → String → String → String → String → String
  graph in-nodes in-tree out-nodes out-tree deps =
    "digraph G {\n  rankdir=LR;\n  node [shape=circle, fontsize=11];\n"
    ++ "  subgraph cluster_in {\n    label=\"input\";  color=none;\n"
    ++ in-nodes ++ in-tree ++ "  }\n"
    ++ "  subgraph cluster_out {\n    label=\"output\"; color=none;\n"
    ++ out-nodes ++ out-tree ++ "  }\n"
    ++ deps ++ "}\n"

contents : String
contents =
  graph (nodes "i" in-sk) (tree-edges "i" in-sk)
        (nodes "o" out-sk) (tree-edges "o" out-sk)
        dep-edges

contents-sugar : String
contents-sugar =
  graph (nodes-merged "i" in-sk) (tree-edges-of "i" (merged-tree in-sk in-sk []))
        (nodes-merged "o" out-sk) (tree-edges-of "o" (merged-tree out-sk out-sk []))
        dep-edges-merged

main : Main
main = run (writeFile "fig/dot/map-three.dot" contents
            >> writeFile "fig/dot/map-three-sugar.dot" contents-sugar)
