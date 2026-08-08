{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- Merging vertices joins their edges with the semiring's addition, which agrees with composition by
-- distributivity. Run from the approx-diff repository root.
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
open import Data.Rational using (0ℚ; 1ℚ) renaming (_+_ to _+ℚ_)
open import example.runs-three using (dep-map; dep-filter)
open import language-syntax EP.Sig using (base; list) renaming (emp to ∙; _,_ to _▸_)
open import language-operational.evaluation EP.Sig EP.primitives using (Val; Env)
open Val
open Env
open import graph-viz.dump-slices using (γ-nums-val; δ-out; showC)
open import language-operational.list-value EP.Sig EP.primitives using (_∷ᵥ_; nilᵥ)
open import language-operational.annotated-value EP.Sig EP.primitives
  using (Node; walk; walk-env)
open Node

private
  Entries : Set
  Entries = List (ℕ × Node)

  index : ℕ → List Node → Entries
  index _ []       = []
  index i (e ∷ es) = (i , e) ∷ index (suc i) es

  in-sk out-sk : Entries
  in-sk  = index 0 (walk (λ {s} c → showC {s} c) γ-nums-val)
  out-sk = index 0 (walk (λ {s} c → showC {s} c) δ-out)

  -- Membership by numeric equality: the target gates every step without its value reaching the
  -- output, and the kept element's value flows to the one output element.
  numsT = list (base EP.number)

  γ-filter-env : Env (∙ ▸ base EP.number ▸ numsT)
  γ-filter-env = emp · const (1ℚ +ℚ 1ℚ) ·
                 (const 1ℚ ∷ᵥ const (1ℚ +ℚ 1ℚ) ∷ᵥ const ((1ℚ +ℚ 1ℚ) +ℚ 1ℚ) ∷ᵥ nilᵥ)

  δ-filter : Val numsT
  δ-filter = const (1ℚ +ℚ 1ℚ) ∷ᵥ nilᵥ

  filter-in-sk filter-out-sk : Entries
  filter-in-sk  = index 0 (walk-env (λ {s} c → showC {s} c) γ-filter-env)
  filter-out-sk = index 0 (walk (λ {s} c → showC {s} c) δ-filter)

  -- List notation for the body's injections, as in the partial-value renderer.
  sugar : String → String
  sugar l = if l == "inr" then "∷" else if l == "inl" then "[]" else l

  cls-of : Entries → ℕ → ℕ
  cls-of []             i = i
  cls-of ((j , e) ∷ es) i = if i ≡ᵇ j then e .cls else cls-of es i

  node : String → ℕ → String → String
  node pre i l = "    " ++ pre ++ ℕ-Show.show i ++ " [label=\"" ++ l ++ "\"];\n"

  nodes-merged : String → Entries → String
  nodes-merged pre []             = ""
  nodes-merged pre ((i , e) ∷ es) =
    (if i ≡ᵇ e .cls then node pre i (sugar (e .label)) else "") ++ nodes-merged pre es

  tree-edge : String → ℕ → ℕ → String
  tree-edge pre i j =
    "    " ++ pre ++ ℕ-Show.show i ++ " -> " ++ pre ++ ℕ-Show.show j
    ++ " [color=gray, arrowhead=none];\n"

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

  map-rows filter-rows : List (List three.Three)
  map-rows    = toList (tabulate (λ q → toList (tabulate (dep-map q))))
  filter-rows = toList (tabulate (λ q → toList (tabulate (dep-filter q))))

  Edge : Set
  Edge = ℕ × ℕ × three.Three

  -- Insert an edge between classes, joining the weight with any edge already present.
  upd : ℕ → ℕ → three.Three → List Edge → List Edge
  upd p q w [] = (p , q , w) ∷ []
  upd p q w ((p' , q' , w') ∷ es) =
    if (p ≡ᵇ p') ∧ (q ≡ᵇ q')
    then (p' , q' , w three.⊔ w') ∷ es
    else (p' , q' , w') ∷ upd p q w es

  quotient-for : Entries → Entries → List (List three.Three) → List Edge
  quotient-for isk osk rows = go-q 0 rows []
    where
    add : ℕ → ℕ → three.Three → List Edge → List Edge
    add p q three.O acc = acc
    add p q w       acc = upd (cls-of isk p) (cls-of osk q) w acc
    go-p : ℕ → ℕ → List three.Three → List Edge → List Edge
    go-p q _ []       acc = acc
    go-p q p (w ∷ ws) acc = go-p q (suc p) ws (add p q w acc)
    go-q : ℕ → List (List three.Three) → List Edge → List Edge
    go-q _ []       acc = acc
    go-q q (r ∷ rs) acc = go-q (suc q) rs (go-p q 0 r acc)

  merged-dep-edges-for : Entries → Entries → List (List three.Three) → String
  merged-dep-edges-for isk osk rows = go (quotient-for isk osk rows)
    where
    go : List Edge → String
    go []                 = ""
    go ((p , q , w) ∷ es) = dep-edge w p q ++ go es

  reps : Entries → List ℕ
  reps []             = []
  reps ((i , e) ∷ es) = if i ≡ᵇ e .cls then i ∷ reps es else reps es

  last2 : List ℕ → List ℕ
  last2 (i ∷ j ∷ []) = i ∷ j ∷ []
  last2 (_ ∷ is)     = last2 is
  last2 []           = []

  -- The cluster's label sits to the right of the tree, drawn there by invisible edges from the
  -- rightmost two nodes, which centre it between the tree's rows.
  anchor-edges : String → String → List ℕ → String
  anchor-edges pre lab []       = ""
  anchor-edges pre lab (i ∷ is) =
    "    " ++ pre ++ ℕ-Show.show i ++ " -> " ++ lab
    ++ " [style=invis];\n" ++ anchor-edges pre lab is

  cluster : String → String → String → String → List ℕ → String
  cluster name pre ns ts as =
    "  subgraph cluster_" ++ name ++ " {\n    color=none;\n"
    ++ ns ++ ts
    ++ "    " ++ pre ++ "lab [label=\"" ++ name ++ "\", shape=plaintext];\n"
    ++ anchor-edges pre (pre ++ "lab") as
    ++ "  }\n"

  graph : String → String → String → String → List ℕ → List ℕ → String → String
  graph in-nodes in-tree out-nodes out-tree in-as out-as deps =
    "digraph G {\n  rankdir=LR;\n  node [shape=circle, fontsize=11];\n"
    ++ cluster "input"  "i" in-nodes  in-tree  in-as
    ++ cluster "output" "o" out-nodes out-tree out-as
    ++ deps ++ "}\n"

contents-map : String
contents-map =
  graph (nodes-merged "i" in-sk) (tree-edges-of "i" (merged-tree in-sk in-sk []))
        (nodes-merged "o" out-sk) (tree-edges-of "o" (merged-tree out-sk out-sk []))
        (last2 (reps in-sk)) (last2 (reps out-sk))
        (merged-dep-edges-for in-sk out-sk map-rows)

contents-filter : String
contents-filter =
  graph (nodes-merged "i" filter-in-sk)
        (tree-edges-of "i" (merged-tree filter-in-sk filter-in-sk []))
        (nodes-merged "o" filter-out-sk)
        (tree-edges-of "o" (merged-tree filter-out-sk filter-out-sk []))
        (last2 (reps filter-in-sk)) (last2 (reps filter-out-sk))
        (merged-dep-edges-for filter-in-sk filter-out-sk filter-rows)

main : Main
main = run (writeFile "dot/map-three.dot" contents-map
            >> writeFile "dot/filter-three.dot" contents-filter)
