{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- Merging vertices joins their edges with the semiring's addition, which agrees with composition by
-- distributivity. Run from the approx-diff repository root.
module graph-viz.dump-dep-graph where

open import IO
open import IO.Finite using (writeFile)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_)
open import Data.String using (String; _++_; _==_)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤p; tt to ttp)
open import Data.List using (List; []; _∷_) renaming (_++_ to _++L_)
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
open import example.list-value EP.Sig EP.primitives using (_∷ᵥ_; nilᵥ)
open import language-operational.annotated-value EP.Sig EP.primitives
  using (AVal; node; Shape; shape-of; shape-env-of; covers; covers-all; label-of)
open import Data.Unit using (⊤)
open import Data.Nat using (_+_)

private
  numsT = list (base EP.number)

  γ-filter-env : Env (∙ ▸ base EP.number ▸ numsT)
  γ-filter-env = emp · const (1ℚ +ℚ 1ℚ) ·
                 (const 1ℚ ∷ᵥ const (1ℚ +ℚ 1ℚ) ∷ᵥ const ((1ℚ +ℚ 1ℚ) +ℚ 1ℚ) ∷ᵥ nilᵥ)

  δ-filter : Val numsT
  δ-filter = const (1ℚ +ℚ 1ℚ) ∷ᵥ nilᵥ

  in-tree out-tree filter-in-tree filter-out-tree : List (AVal ⊤)
  in-tree         = shape-of (λ {s} c → showC {s} c) γ-nums-val ∷ []
  out-tree        = shape-of (λ {s} c → showC {s} c) δ-out ∷ []
  filter-in-tree  = shape-env-of (λ {s} c → showC {s} c) γ-filter-env
  filter-out-tree = shape-of (λ {s} c → showC {s} c) δ-filter ∷ []

  mutual
    drawn : ℕ → AVal ⊤ → List (ℕ × String)
    drawn off (node sh _ n cs) = (off , label-of sh) ∷ drawn-all (off + n) cs

    drawn-all : ℕ → List (AVal ⊤) → List (ℕ × String)
    drawn-all off []       = []
    drawn-all off (t ∷ ts) = drawn off t ++L drawn-all (off + covers t) ts

  mutual
    kid-edges : ℕ → AVal ⊤ → List (ℕ × ℕ)
    kid-edges off (node _ _ n cs) = links (off + n) cs ++L kid-edges-all (off + n) cs
      where
      links : ℕ → List (AVal ⊤) → List (ℕ × ℕ)
      links o []       = []
      links o (t ∷ ts) = (off , o) ∷ links (o + covers t) ts

    kid-edges-all : ℕ → List (AVal ⊤) → List (ℕ × ℕ)
    kid-edges-all off []       = []
    kid-edges-all off (t ∷ ts) = kid-edges off t ++L kid-edges-all (off + covers t) ts

  mutual
    owner : ℕ → AVal ⊤ → ℕ → ℕ
    owner off (node _ _ n cs) i =
      if in-run off n i then off else owner-all (off + n) cs i
      where
      in-run : ℕ → ℕ → ℕ → Bool
      in-run o zero    j = false
      in-run o (suc k) j = (o ≡ᵇ j) ∨ in-run (suc o) k j

    owner-all : ℕ → List (AVal ⊤) → ℕ → ℕ
    owner-all off []       i = i
    owner-all off (t ∷ ts) i =
      if lt i (off + covers t) then owner off t i else owner-all (off + covers t) ts i
      where
      lt : ℕ → ℕ → Bool
      lt zero    (suc _) = true
      lt _       zero    = false
      lt (suc a) (suc b) = lt a b

  nodes-of : List (AVal ⊤) → List (ℕ × String)
  nodes-of ts = drawn-all 0 ts

  edges-of : List (AVal ⊤) → List (ℕ × ℕ)
  edges-of ts = kid-edges-all 0 ts

  id-of : List (AVal ⊤) → ℕ → ℕ
  id-of ts i = owner-all 0 ts i

  nodes-merged : String → List (ℕ × String) → String
  nodes-merged pre []             = ""
  nodes-merged pre ((i , l) ∷ ns) =
    "    " ++ pre ++ ℕ-Show.show i ++ " [label=\"" ++ l ++ "\"];\n" ++ nodes-merged pre ns

  tree-edges-of : String → List (ℕ × ℕ) → String
  tree-edges-of pre []             = ""
  tree-edges-of pre ((i , j) ∷ ps) =
    "    " ++ pre ++ ℕ-Show.show i ++ " -> " ++ pre ++ ℕ-Show.show j
    ++ " [color=gray, arrowhead=none];\n" ++ tree-edges-of pre ps

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

  quotient-for : List (AVal ⊤) → List (AVal ⊤) → List (List three.Three) → List Edge
  quotient-for isk osk rows = go-q 0 rows []
    where
    add : ℕ → ℕ → three.Three → List Edge → List Edge
    add p q three.O acc = acc
    add p q w       acc = upd (id-of isk p) (id-of osk q) w acc
    go-p : ℕ → ℕ → List three.Three → List Edge → List Edge
    go-p q _ []       acc = acc
    go-p q p (w ∷ ws) acc = go-p q (suc p) ws (add p q w acc)
    go-q : ℕ → List (List three.Three) → List Edge → List Edge
    go-q _ []       acc = acc
    go-q q (r ∷ rs) acc = go-q (suc q) rs (go-p q 0 r acc)

  merged-dep-edges-for : List (AVal ⊤) → List (AVal ⊤) → List (List three.Three) → String
  merged-dep-edges-for isk osk rows = go (quotient-for isk osk rows)
    where
    go : List Edge → String
    go []                 = ""
    go ((p , q , w) ∷ es) = dep-edge w p q ++ go es

  reps : List (ℕ × String) → List ℕ
  reps []            = []
  reps ((i , _) ∷ ns) = i ∷ reps ns

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
  graph (nodes-merged "i" (nodes-of in-tree)) (tree-edges-of "i" (edges-of in-tree))
        (nodes-merged "o" (nodes-of out-tree)) (tree-edges-of "o" (edges-of out-tree))
        (last2 (reps (nodes-of in-tree))) (last2 (reps (nodes-of out-tree)))
        (merged-dep-edges-for in-tree out-tree map-rows)

contents-filter : String
contents-filter =
  graph (nodes-merged "i" (nodes-of filter-in-tree))
        (tree-edges-of "i" (edges-of filter-in-tree))
        (nodes-merged "o" (nodes-of filter-out-tree))
        (tree-edges-of "o" (edges-of filter-out-tree))
        (last2 (reps (nodes-of filter-in-tree))) (last2 (reps (nodes-of filter-out-tree)))
        (merged-dep-edges-for filter-in-tree filter-out-tree filter-rows)

main : Main
main = run (writeFile "dot/map-three.dot" contents-map
            >> writeFile "dot/filter-three.dot" contents-filter)
