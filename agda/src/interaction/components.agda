{-# OPTIONS --prop --postfix-projections --safe #-}

-- Connected components of a graph whose vertices are numbered from zero and whose edges are given
-- as neighbour lists. A vertex leaves the unvisited set when it is queued rather than when it is
-- expanded, so nothing is queued twice. The set is a complete binary tree over the numbers, so a
-- lookup costs the depth rather than the number of vertices.
module interaction.components where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; filterᵇ; length; map; take; upTo)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _<ᵇ_)
open import Data.Product using (_×_; _,_; proj₁)

private
  half : ℕ → ℕ
  half zero          = zero
  half (suc zero)    = zero
  half (suc (suc n)) = suc (half n)

  pow : ℕ → ℕ
  pow zero    = 1
  pow (suc d) = pow d + pow d

  -- Least depth whose complete tree has a leaf for every number below n.
  depth-for : ℕ → ℕ → ℕ
  depth-for zero       n = zero
  depth-for (suc fuel) n = if n <ᵇ 2 then zero else suc (depth-for fuel (half (n + 1)))

  data Numbers : Set where
    num-tip  : ℕ → Numbers
    num-fork : Numbers → Numbers → Numbers

  fill-numbers : ℕ → List ℕ → Numbers × List ℕ
  fill-numbers zero    []       = num-tip 0 , []
  fill-numbers zero    (n ∷ ns) = num-tip n , ns
  fill-numbers (suc d) ns with fill-numbers d ns
  ... | l , ns' with fill-numbers d ns'
  ...   | r , ns'' = num-fork l r , ns''

-- A list read by position, out of range reading zero.
Index : Set
Index = ℕ × Numbers

index : List ℕ → Index
index ns = d , proj₁ (fill-numbers d ns)
  where
  d : ℕ
  d = depth-for (length ns) (length ns)

index-at : Index → ℕ → ℕ
index-at (d , t) p = look-num d p t
  where
  look-num : ℕ → ℕ → Numbers → ℕ
  look-num d       p (num-tip n)    = n
  look-num zero    p (num-fork l r) = 0
  look-num (suc d) p (num-fork l r) =
    if p <ᵇ pow d then look-num d p l else look-num d (p ∸ pow d) r

private
  data Tree : Set where
    tip  : Bool → List ℕ → Tree
    fork : Tree → Tree → Tree

  -- Leaves past the end of the lists are absent, so a number beyond them is never visited.
  fill : ℕ → List (List ℕ) → Tree × List (List ℕ)
  fill zero    []         = tip false [] , []
  fill zero    (ns ∷ nss) = tip true ns , nss
  fill (suc d) nss with fill d nss
  ... | l , nss' with fill d nss'
  ...   | r , nss'' = fork l r , nss''

  look : ℕ → ℕ → Tree → Bool × List ℕ
  look d       p (tip b ns) = b , ns
  look zero    p (fork l r) = false , []
  look (suc d) p (fork l r) = if p <ᵇ pow d then look d p l else look d (p ∸ pow d) r

  clear : ℕ → ℕ → Tree → Tree
  clear d       p (tip _ ns) = tip false ns
  clear zero    p (fork l r) = fork l r
  clear (suc d) p (fork l r) =
    if p <ᵇ pow d then fork (clear d p l) r else fork l (clear d (p ∸ pow d) r)

  push : ℕ → List ℕ → List ℕ → Tree → List ℕ × Tree
  push d []       fr t = fr , t
  push d (q ∷ qs) fr t with look d q t
  ... | true  , _ = push d qs (q ∷ fr) (clear d q t)
  ... | false , _ = push d qs fr t

  -- Fuel bounds the pushes, of which there is at most one per vertex.
  expand : ℕ → ℕ → List ℕ → Tree → List ℕ → List ℕ × Tree
  expand zero    d fr       t acc = acc , t
  expand (suc f) d []       t acc = acc , t
  expand (suc f) d (p ∷ fr) t acc with look d p t
  ... | _ , ns with push d ns fr t
  ...   | fr' , t' = expand f d fr' t' (p ∷ acc)

  from : ℕ → ℕ → List ℕ → Tree → List (List ℕ)
  from f d []       t = []
  from f d (p ∷ ps) t with look d p t
  ... | false , _ = from f d ps t
  ... | true  , _ with expand f d (p ∷ []) (clear d p t) []
  ...   | c , t' = c ∷ from f d ps t'

  data Bins : Set where
    bin  : List ℕ → Bins
    node : Bins → Bins → Bins

  empty-bins : ℕ → Bins
  empty-bins zero    = bin []
  empty-bins (suc d) = node (empty-bins d) (empty-bins d)

  put : ℕ → ℕ → ℕ → Bins → Bins
  put d       p v (bin xs)   = bin (v ∷ xs)
  put zero    p v (node l r) = node l r
  put (suc d) p v (node l r) =
    if p <ᵇ pow d then node (put d p v l) r else node l (put d (p ∸ pow d) v r)

  put-each : ℕ → ℕ → List ℕ → Bins → Bins
  put-each d i []       bs = bs
  put-each d i (j ∷ js) bs = put-each d i js (put d j i bs)

  fill-bins : ℕ → ℕ → List (List ℕ) → Bins → Bins
  fill-bins d i []         bs = bs
  fill-bins d i (ns ∷ nss) bs = fill-bins d (suc i) nss (put-each d i ns bs)

  drain : Bins → List (List ℕ) → List (List ℕ)
  drain (bin xs)   acc = xs ∷ acc
  drain (node l r) acc = drain l (drain r acc)

  zip-append : List (List ℕ) → List (List ℕ) → List (List ℕ)
  zip-append []         _          = []
  zip-append nss        []         = nss
  zip-append (ns ∷ nss) (ms ∷ mss) = (ns ++ ms) ∷ zip-append nss mss

-- Both endpoints of every listed edge, so a traversal can run in either direction. Repeats are
-- harmless: a vertex already queued is no longer in the set.
symmetric : List (List ℕ) → List (List ℕ)
symmetric nss = zip-append nss (drain (fill-bins d 0 nss (empty-bins d)) [])
  where
  d : ℕ
  d = depth-for (length nss) (length nss)

induced : ℕ → List (List ℕ) → List (List ℕ)
induced k nss = map (filterᵇ (λ j → j <ᵇ k)) (take k nss)

components : List (List ℕ) → List (List ℕ)
components nss = from n (depth-for n n) (upTo n) (proj₁ (fill (depth-for n n) nss))
  where
  n : ℕ
  n = length nss
