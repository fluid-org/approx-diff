{-# OPTIONS --prop --postfix-projections --safe #-}

-- Connected components of a graph whose vertices are numbered from zero and whose edges are given
-- as neighbour lists. A vertex leaves the unvisited set when it is queued rather than when it is
-- expanded, so nothing is queued twice. The sets are complete binary trees over the numbers, so a
-- read or a write costs the depth rather than the number of vertices.
module interaction.components where

open import Data.Bool using (Bool; true; false; not; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; concat; filterᵇ; length; map; replicate; take; upTo)
open import Data.Nat using (ℕ; zero; suc; pred; _+_; _∸_; _<ᵇ_; _≡ᵇ_)
open import Data.Nat.Properties using (+-suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; cong to ≡-cong)

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

-- Indexed by depth, so a position always reaches a leaf and no case is left over.
data Tree (A : Set) : ℕ → Set where
  tip  : A → Tree A zero
  fork : ∀ {d} → Tree A d → Tree A d → Tree A (suc d)

private
  fill : {A : Set} (z : A) (d : ℕ) → List A → Tree A d × List A
  fill z zero    []       = tip z , []
  fill z zero    (x ∷ xs) = tip x , xs
  fill z (suc d) xs with fill z d xs
  ... | l , xs' with fill z d xs'
  ...   | r , xs'' = fork l r , xs''

  build : {A : Set} (z : A) (d : ℕ) → List A → Tree A d
  build z d xs = proj₁ (fill z d xs)

  look : {A : Set} {d : ℕ} → ℕ → Tree A d → A
  look         p (tip x)    = x
  look {d = suc d} p (fork l r) = if p <ᵇ pow d then look p l else look (p ∸ pow d) r

  set : {A : Set} {d : ℕ} → ℕ → A → Tree A d → Tree A d
  set         p y (tip _)    = tip y
  set {d = suc d} p y (fork l r) =
    if p <ᵇ pow d then fork (set p y l) r else fork l (set (p ∸ pow d) y r)

  flatten : {A : Set} {d : ℕ} → Tree A d → List A → List A
  flatten (tip x)    acc = x ∷ acc
  flatten (fork l r) acc = flatten l (flatten r acc)

-- A list of numbers read by position, out of range reading zero.
Index : Set
Index = Σ ℕ (Tree ℕ)

index : List ℕ → Index
index ns = d , build 0 d ns
  where
  d : ℕ
  d = depth-for (length ns) (length ns)

index-at : Index → ℕ → ℕ
index-at (d , t) p = look p t

size : {d : ℕ} → Tree Bool d → ℕ
size (tip true)  = 1
size (tip false) = 0
size (fork l r)  = size l + size r

size-clear : {d : ℕ} (t : Tree Bool d) (p : ℕ) → look p t ≡ true →
             suc (size (set p false t)) ≡ size t
size-clear (tip true)  p h = ≡-refl
size-clear {d = suc d} t p h = at t p h
  where
  at : (t' : Tree Bool (suc d)) (p' : ℕ) → look p' t' ≡ true →
       suc (size (set p' false t')) ≡ size t'
  at (fork l r) p' h' with p' <ᵇ pow d
  ... | true  = ≡-cong (_+ size r) (size-clear l p' h')
  ... | false = ≡-trans (≡-sym (+-suc (size l) _))
                        (≡-cong (size l +_) (size-clear r (p' ∸ pow d) h'))

-- What is left to do: a number is either still in the set or already on the frontier, and one
-- leaves the set exactly when it joins the frontier.
measure : {d : ℕ} → List ℕ → Tree Bool d → ℕ
measure fr vs = size vs + length fr

private
  push : {d : ℕ} → Tree (List ℕ) d → List ℕ → List ℕ → Tree Bool d → ℕ →
         List ℕ × Tree Bool d × ℕ
  push ns []       fr vs c = fr , vs , c
  push ns (q ∷ qs) fr vs c =
    if look q vs then push ns qs (q ∷ fr) (set q false vs) (suc c)
    else push ns qs fr vs (suc c)

  push-measure : {d : ℕ} (ns : Tree (List ℕ) d) (qs fr : List ℕ) (vs : Tree Bool d) (c : ℕ) →
                 measure (proj₁ (push ns qs fr vs c)) (proj₁ (proj₂ (push ns qs fr vs c)))
                 ≡ measure fr vs
  push-measure ns []       fr vs c = ≡-refl
  push-measure ns (q ∷ qs) fr vs c with look q vs in eq
  ... | true  = ≡-trans (push-measure ns qs (q ∷ fr) (set q false vs) (suc c))
                        (≡-trans (+-suc (size (set q false vs)) (length fr))
                                 (≡-cong (_+ length fr) (size-clear vs q eq)))
  ... | false = push-measure ns qs fr vs (suc c)

  -- Fuel bounds the pops, of which there is at most one per number ever queued.
  expand : {d : ℕ} → ℕ → Tree (List ℕ) d → List ℕ → Tree Bool d → List ℕ → ℕ →
           List ℕ × Tree Bool d × ℕ
  expand zero    ns fr       vs acc c = acc , vs , c
  expand (suc f) ns []       vs acc c = acc , vs , c
  expand (suc f) ns (p ∷ fr) vs acc c with push ns (look p ns) fr vs c
  ... | fr' , vs' , c' = expand f ns fr' vs' (p ∷ acc) c'

  from : {d : ℕ} → ℕ → Tree (List ℕ) d → List ℕ → Tree Bool d → ℕ → List (List ℕ) × ℕ
  from f ns []       vs c = [] , c
  from f ns (p ∷ ps) vs c =
    if look p vs then opened (expand f ns (p ∷ []) (set p false vs) [] c)
    else from f ns ps vs c
    where
    opened : List ℕ × Tree Bool _ × ℕ → List (List ℕ) × ℕ
    opened (b , vs' , c') = consed b (from f ns ps vs' c')
      where
      consed : List ℕ → List (List ℕ) × ℕ → List (List ℕ) × ℕ
      consed b' (bs , c'') = b' ∷ bs , c''

  zip-append : List (List ℕ) → List (List ℕ) → List (List ℕ)
  zip-append []         _          = []
  zip-append nss        []         = nss
  zip-append (ns ∷ nss) (ms ∷ mss) = (ns ++ ms) ∷ zip-append nss mss

  reversed : (d : ℕ) → List (List ℕ) → Tree (List ℕ) d → Tree (List ℕ) d
  reversed d nss t = go 0 nss t
    where
    put : ℕ → ℕ → Tree (List ℕ) d → Tree (List ℕ) d
    put p v u = set p (v ∷ look p u) u

    put-each : ℕ → List ℕ → Tree (List ℕ) d → Tree (List ℕ) d
    put-each i []       u = u
    put-each i (j ∷ js) u = put-each i js (put j i u)

    go : ℕ → List (List ℕ) → Tree (List ℕ) d → Tree (List ℕ) d
    go i []         u = u
    go i (ms ∷ mss) u = go (suc i) mss (put-each i ms u)

-- Both endpoints of every listed edge, so a traversal can run in either direction. Repeats are
-- harmless: a number already queued is no longer in the set.
symmetric : List (List ℕ) → List (List ℕ)
symmetric nss = zip-append nss (flatten (reversed d nss (build [] d [])) [])
  where
  d : ℕ
  d = depth-for (length nss) (length nss)

induced : ℕ → List (List ℕ) → List (List ℕ)
induced k nss = map (filterᵇ (λ j → j <ᵇ k)) (take k nss)

private
  -- Numbers outside the list are cleared before the traversal starts, so they are neither visited
  -- nor followed.
  drop-rest : {d : ℕ} → ℕ → ℕ → List ℕ → Tree Bool d → Tree Bool d
  drop-rest i zero    ws       vs = vs
  drop-rest i (suc c) []       vs = drop-rest (suc i) c [] (set i false vs)
  drop-rest i (suc c) (w ∷ ws) vs =
    if i ≡ᵇ w then drop-rest (suc i) c ws vs
    else drop-rest (suc i) c (w ∷ ws) (set i false vs)

-- Blocks with the number of neighbours examined.
components-on : List ℕ → List (List ℕ) → List (List ℕ) × ℕ
components-on ws nss =
  from n (build [] d nss) ws (drop-rest 0 n ws (build false d (replicate n true))) 0
  where
  n : ℕ
  n = length nss

  d : ℕ
  d = depth-for n n

components : List (List ℕ) → List (List ℕ) × ℕ
components nss = components-on (upTo (length nss)) nss

private
  mem : ℕ → List ℕ → Bool
  mem i []       = false
  mem i (j ∷ js) = if i ≡ᵇ j then true else mem i js

  nth-list : ℕ → List (List ℕ) → List ℕ
  nth-list _       []        = []
  nth-list zero    (ns ∷ _)  = ns
  nth-list (suc i) (_ ∷ nss) = nth-list i nss

-- The same blocks by the fold the proofs are stated against, with the number of pairs tested.
by-pairs : List (List ℕ) → List ℕ → List (List ℕ) × ℕ
by-pairs nss []       = [] , 0
by-pairs nss (w ∷ ws) = step (by-pairs nss ws)
  where
  ns : List ℕ
  ns = nth-list w nss

  hits : List ℕ → ℕ → Bool × ℕ
  hits []       c = false , c
  hits (q ∷ qs) c = if mem q ns then true , suc c else hits qs (suc c)

  part : List (List ℕ) → ℕ → List (List ℕ) × List (List ℕ) × ℕ
  part []       c = [] , [] , c
  part (b ∷ bs) c = place (hits b c)
    where
    add-hit add-miss : List (List ℕ) × List (List ℕ) × ℕ →
                       List (List ℕ) × List (List ℕ) × ℕ
    add-hit  (hit , miss , c') = b ∷ hit , miss , c'
    add-miss (hit , miss , c') = hit , b ∷ miss , c'

    place : Bool × ℕ → List (List ℕ) × List (List ℕ) × ℕ
    place (true  , c') = add-hit (part bs c')
    place (false , c') = add-miss (part bs c')

  step : List (List ℕ) × ℕ → List (List ℕ) × ℕ
  step (bs , c) = joined (part bs c)
    where
    joined : List (List ℕ) × List (List ℕ) × ℕ → List (List ℕ) × ℕ
    joined (hit , miss , c') = (w ∷ concat hit) ∷ miss , c'

thin : ℕ → ℕ → List ℕ
thin n v = go 0 0 v
  where
  next : ℕ → ℕ
  next c = if suc c ≡ᵇ n then 0 else suc c

  go : ℕ → ℕ → ℕ → List ℕ
  go i c zero    = []
  go i c (suc v) = if c ≡ᵇ 0 then go (suc i) (next c) v else i ∷ go (suc i) (next c) v
