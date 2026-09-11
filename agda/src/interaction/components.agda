{-# OPTIONS --prop --postfix-projections --safe #-}

-- Connected components of a graph whose vertices are numbered from zero and whose edges are given
-- as neighbour lists. A vertex leaves the unvisited set when it is queued rather than when it is
-- expanded, so nothing is queued twice. The set is a complete binary tree over the numbers, so a
-- lookup costs the depth rather than the number of vertices.
module interaction.components where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; length; upTo)
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

  add-at : ℕ → ℕ → List (List ℕ) → List (List ℕ)
  add-at _       i []          = []
  add-at zero    i (ns ∷ nss)  = (i ∷ ns) ∷ nss
  add-at (suc j) i (ns ∷ nss)  = ns ∷ add-at j i nss

-- Both endpoints of every listed edge, so a traversal can run in either direction. Repeats are
-- harmless: a vertex already queued is no longer in the set.
symmetric : List (List ℕ) → List (List ℕ)
symmetric nss = go 0 nss nss
  where
  add-each : ℕ → List ℕ → List (List ℕ) → List (List ℕ)
  add-each i []       acc = acc
  add-each i (j ∷ js) acc = add-each i js (add-at j i acc)

  go : ℕ → List (List ℕ) → List (List ℕ) → List (List ℕ)
  go i []          acc = acc
  go i (ns ∷ nss') acc = go (suc i) nss' (add-each i ns acc)

components : List (List ℕ) → List (List ℕ)
components nss = from n (depth-for n n) (upTo n) (proj₁ (fill (depth-for n n) nss))
  where
  n : ℕ
  n = length nss
