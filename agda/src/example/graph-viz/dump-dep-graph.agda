{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- Merging vertices joins their edges with the semiring's addition, which agrees with composition by
-- distributivity. Run from the approx-diff repository root.
module example.graph-viz.dump-dep-graph where

open import IO
open import IO.Finite using (writeFile)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_)
open import Data.String using (String; _++_; _==_)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤p; tt to ttp)
open import Data.List using (List; []; _∷_; concat) renaming (_++_ to _++L_; map to mapL)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
import Data.Nat.Show as ℕ-Show
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec as Vec using (Vec; toList; tabulate)
open import Level using (0ℓ)
import three
open import signature.example.interpretation three.semiring using (Sig; interpretation)
open import example.runs three.semiring three.C using (map-run; filter-run; env; model-output; model-of)
open import example.show three.semiring using (show-const)
open import language-operational.annotated-value Sig three.semiring interpretation three.C
  using (AVal; node; Tag; arity; shape-of; shape-env-of; covers; covers-vec; covers-all;
         label-of; fold; fold-all)
open import Data.Unit using (⊤)
open import Data.Nat using (_+_)

private
  in-tree out-tree filter-in-tree filter-out-tree : List (AVal ⊤)
  in-tree         = shape-env-of (λ {s} c → show-const {s} c) (map-run .env)
  out-tree        = shape-of (λ {s} c → show-const {s} c) (model-output map-run) ∷ []
  filter-in-tree  = shape-env-of (λ {s} c → show-const {s} c) (filter-run .env)
  filter-out-tree = shape-of (λ {s} c → show-const {s} c) (model-output filter-run) ∷ []

  private
    node-entry : ∀ (t : Tag) → ⊤ → ℕ → ℕ → Vec (List (ℕ × String)) (arity t) → List (ℕ × String)
    node-entry sh _ _ off rs = (off , label-of sh) ∷ concat (toList rs)

    node-edges : ∀ (t : Tag) → ⊤ → ℕ → ℕ → Vec (ℕ × List (ℕ × ℕ)) (arity t) → ℕ × List (ℕ × ℕ)
    node-edges _ _ _ off rs =
      off , (mapL (λ r → off , proj₁ r) (toList rs) ++L concat (mapL proj₂ (toList rs)))

  drawn : ℕ → AVal ⊤ → List (ℕ × String)
  drawn = fold node-entry

  drawn-all : ℕ → List (AVal ⊤) → List (ℕ × String)
  drawn-all off ts = concat (fold-all node-entry off ts)

  kid-edges : ℕ → AVal ⊤ → List (ℕ × ℕ)
  kid-edges off t = proj₂ (fold node-edges off t)

  kid-edges-all : ℕ → List (AVal ⊤) → List (ℕ × ℕ)
  kid-edges-all off ts = concat (mapL proj₂ (fold-all node-edges off ts))

  private
    lt : ℕ → ℕ → Bool
    lt zero    (suc _) = true
    lt _       zero    = false
    lt (suc a) (suc b) = lt a b

    in-run : ℕ → ℕ → ℕ → Bool
    in-run o zero    j = false
    in-run o (suc k) j = (o ≡ᵇ j) ∨ in-run (suc o) k j

  mutual
    owner : ℕ → AVal ⊤ → ℕ → ℕ
    owner off (node _ _ n cs) i =
      if in-run off n i then off else owner-vec (off + n) cs i

    owner-vec : ∀ {k} → ℕ → Vec (AVal ⊤) k → ℕ → ℕ
    owner-vec off Vec.[]         i = i
    owner-vec off (t Vec.∷ ts) i =
      if lt i (off + covers t) then owner off t i else owner-vec (off + covers t) ts i

  owner-all : ℕ → List (AVal ⊤) → ℕ → ℕ
  owner-all off []       i = i
  owner-all off (t ∷ ts) i =
    if lt i (off + covers t) then owner off t i else owner-all (off + covers t) ts i

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
  map-rows    = toList (tabulate (λ q → toList (tabulate (model-of map-run q))))
  filter-rows = toList (tabulate (λ q → toList (tabulate (model-of filter-run q))))

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
