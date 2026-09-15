{-# OPTIONS --prop --postfix-projections --safe #-}

-- Connected components of a graph whose vertices are numbered from zero and whose edges are given
-- as neighbour lists. A vertex leaves the unvisited set when it is queued rather than when it is
-- expanded, so nothing is queued twice. The sets are complete binary trees over the numbers, so a
-- read or a write costs the depth rather than the number of vertices. Walks and the properties
-- asked of a list of components come after the traversal, over any edge relation.
module interaction.components where

open import Data.Bool using (Bool; true; false; not; if_then_else_; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; concat; drop; filterᵇ; length; map; replicate;
                             take; upTo)
open import Data.List.Properties using (drop-drop)
open import Data.Nat using (ℕ; zero; suc; pred; _+_; _∸_; _≤_; _<_; _<ᵇ_; _≡ᵇ_; s≤s; z≤n)
open import Data.Nat.Properties using (+-suc; ≤-pred; ≤-refl; <ᵇ⇒<; <⇒<ᵇ; ≮⇒≥; ∸-cancelʳ-≡;
                                       ∸-monoˡ-<; m+n∸n≡m; n≤0⇒n≡0)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; map₁; map₂)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-concat⁻′)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; ↭-sym)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (∈-resp-↭)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Unary.Any as Any using (Any; any?; here; there)
open import Data.Sum using (inj₁; inj₂)
open import Level using (_⊔_)
open import Relation.Binary.Definitions using (Decidable; DecidableEquality)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (Dec; yes; no; _×-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; cong to ≡-cong)
open import list using (Apart; AllPairs-∈; dec-case; module Partitions)

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

-- The list a tree of depth d stands for: positions below pow d, out of range reading the padding.
nth : {A : Set} → A → ℕ → List A → A
nth z _       []       = z
nth z zero    (x ∷ _)  = x
nth z (suc i) (_ ∷ xs) = nth z i xs

private
  bool-case : {A : Set} (b : Bool) → (b ≡ true → A) → (b ≡ false → A) → A
  bool-case true  t f = t ≡-refl
  bool-case false t f = f ≡-refl

  if-true : {A : Set} {b : Bool} {x y : A} → b ≡ true → (if b then x else y) ≡ x
  if-true ≡-refl = ≡-refl

  if-false : {A : Set} {b : Bool} {x y : A} → b ≡ false → (if b then x else y) ≡ y
  if-false ≡-refl = ≡-refl

  -- A position past the left subtree lands inside the right one.
  right-bound : (d p : ℕ) → p < pow d + pow d → pow d ≤ p → p ∸ pow d < pow d
  right-bound d p lt ge = subst (p ∸ pow d <_) (m+n∸n≡m (pow d) (pow d)) (∸-monoˡ-< lt ge)

  in-left : (d p : ℕ) → (p <ᵇ pow d) ≡ true → p < pow d
  in-left d p e = <ᵇ⇒< p (pow d) (subst T (≡-sym e) tt)

  past-left : (d p : ℕ) → (p <ᵇ pow d) ≡ false → pow d ≤ p
  past-left d p e = ≮⇒≥ (λ lt → subst T e (<⇒<ᵇ lt))

  nth-drop : {A : Set} (z : A) (k p : ℕ) (xs : List A) → k ≤ p →
             nth z (p ∸ k) (drop k xs) ≡ nth z p xs
  nth-drop z zero    p       xs       le       = ≡-refl
  nth-drop z (suc k) p       []       le       = ≡-refl
  nth-drop z (suc k) (suc p) (x ∷ xs) (s≤s le) = nth-drop z k p xs le

  look-set : {A : Set} {d : ℕ} (p : ℕ) (y : A) (t : Tree A d) → look p (set p y t) ≡ y
  look-set p y (tip _)        = ≡-refl
  look-set p y (fork {d} l r) = bool-case (p <ᵇ pow d) left right
    where
    left : (p <ᵇ pow d) ≡ true → look p (set p y (fork l r)) ≡ y
    left e = ≡-trans (≡-cong (look p) (if-true e)) (≡-trans (if-true e) (look-set p y l))

    right : (p <ᵇ pow d) ≡ false → look p (set p y (fork l r)) ≡ y
    right e =
      ≡-trans (≡-cong (look p) (if-false e)) (≡-trans (if-false e) (look-set (p ∸ pow d) y r))

  look-set-≢ : {A : Set} {d : ℕ} (p q : ℕ) (y : A) (t : Tree A d) →
               p < pow d → q < pow d → p ≢ q → look p (set q y t) ≡ look p t
  look-set-≢ p q y (tip _) (s≤s lp) (s≤s lq) ne =
    ⊥-elim (ne (≡-trans (n≤0⇒n≡0 lp) (≡-sym (n≤0⇒n≡0 lq))))
  look-set-≢ p q y (fork {d} l r) lp lq ne = bool-case (q <ᵇ pow d) qleft qright
    where
    qleft : (q <ᵇ pow d) ≡ true → look p (set q y (fork l r)) ≡ look p (fork l r)
    qleft eq = ≡-trans (≡-cong (look p) (if-true eq)) (bool-case (p <ᵇ pow d) same other)
      where
      same : (p <ᵇ pow d) ≡ true → look p (fork (set q y l) r) ≡ look p (fork l r)
      same ep =
        ≡-trans (if-true ep)
                (≡-trans (look-set-≢ p q y l (in-left d p ep) (in-left d q eq) ne) (≡-sym (if-true ep)))

      other : (p <ᵇ pow d) ≡ false → look p (fork (set q y l) r) ≡ look p (fork l r)
      other ep = ≡-trans (if-false ep) (≡-sym (if-false ep))

    qright : (q <ᵇ pow d) ≡ false → look p (set q y (fork l r)) ≡ look p (fork l r)
    qright eq = ≡-trans (≡-cong (look p) (if-false eq)) (bool-case (p <ᵇ pow d) other same)
      where
      other : (p <ᵇ pow d) ≡ true → look p (fork l (set (q ∸ pow d) y r)) ≡ look p (fork l r)
      other ep = ≡-trans (if-true ep) (≡-sym (if-true ep))

      same : (p <ᵇ pow d) ≡ false → look p (fork l (set (q ∸ pow d) y r)) ≡ look p (fork l r)
      same ep =
        ≡-trans (if-false ep)
                (≡-trans (look-set-≢ (p ∸ pow d) (q ∸ pow d) y r
                                     (right-bound d p lp (past-left d p ep))
                                     (right-bound d q lq (past-left d q eq))
                                     (λ e → ne (∸-cancelʳ-≡ (past-left d p ep) (past-left d q eq) e)))
                         (≡-sym (if-false ep)))

  fill-rest : {A : Set} (z : A) (d : ℕ) (xs : List A) → proj₂ (fill z d xs) ≡ drop (pow d) xs
  fill-rest z zero    []       = ≡-refl
  fill-rest z zero    (x ∷ xs) = ≡-refl
  fill-rest z (suc d) xs =
    ≡-trans (fill-rest z d (proj₂ (fill z d xs)))
            (≡-trans (≡-cong (drop (pow d)) (fill-rest z d xs)) (drop-drop (pow d) (pow d) xs))

  look-build : {A : Set} (z : A) (d p : ℕ) (xs : List A) → p < pow d →
               look p (build z d xs) ≡ nth z p xs
  look-build z zero p       []       lt          = ≡-refl
  look-build z zero .0      (x ∷ xs) (s≤s z≤n)   = ≡-refl
  look-build z (suc d) p    xs       lt          = bool-case (p <ᵇ pow d) left right
    where
    left : (p <ᵇ pow d) ≡ true → look p (build z (suc d) xs) ≡ nth z p xs
    left e = ≡-trans (if-true e) (look-build z d p xs (in-left d p e))

    right : (p <ᵇ pow d) ≡ false → look p (build z (suc d) xs) ≡ nth z p xs
    right e =
      ≡-trans (if-false e)
      (≡-trans (≡-cong (λ ys → look (p ∸ pow d) (build z d ys)) (fill-rest z d xs))
      (≡-trans (look-build z d (p ∸ pow d) (drop (pow d) xs)
                           (right-bound d p lt (past-left d p e)))
               (nth-drop z (pow d) p xs (past-left d p e))))

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
  at : (u : Tree Bool (suc d)) (q : ℕ) → look q u ≡ true →
       suc (size (set q false u)) ≡ size u
  at (fork l r) q e with q <ᵇ pow d
  ... | true  = ≡-cong (_+ size r) (size-clear l q e)
  ... | false = ≡-trans (≡-sym (+-suc (size l) _))
                        (≡-cong (size l +_) (size-clear r (q ∸ pow d) e))

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

  -- Each pop takes one off the frontier and pushes only numbers it takes out of the set, so the
  -- measure falls by one and the bound the caller gives is enough.
  expand : {d : ℕ} (f : ℕ) (ns : Tree (List ℕ) d) (fr : List ℕ) (vs : Tree Bool d) →
           measure fr vs ≤ f → List ℕ → ℕ → List ℕ × Tree Bool d × ℕ
  expand f       ns []       vs le acc c = acc , vs , c
  expand zero    ns (p ∷ fr) vs le acc c =
    ⊥-elim (none (subst (_≤ zero) (+-suc (size vs) (length fr)) le))
    where
    none : ∀ {n} → suc n ≤ zero → ⊥
    none ()
  expand (suc f) ns (p ∷ fr) vs le acc c =
    popped (push ns (look p ns) fr vs c) (push-measure ns (look p ns) fr vs c)
    where
    dropped : measure fr vs ≤ f
    dropped = ≤-pred (subst (_≤ suc f) (+-suc (size vs) (length fr)) le)

    popped : (r : List ℕ × Tree Bool _ × ℕ) →
             measure (proj₁ r) (proj₁ (proj₂ r)) ≡ measure fr vs →
             List ℕ × Tree Bool _ × ℕ
    popped (queued , left , seen) e =
      expand f ns queued left (subst (_≤ f) (≡-sym e) dropped) (p ∷ acc) seen

  from : {d : ℕ} → Tree (List ℕ) d → List ℕ → Tree Bool d → ℕ → List (List ℕ) × ℕ
  from ns []       vs c = [] , c
  from ns (p ∷ ps) vs c =
    if look p vs
    then opened (expand (measure (p ∷ []) (set p false vs)) ns (p ∷ []) (set p false vs)
                        ≤-refl [] c)
    else from ns ps vs c
    where
    opened : List ℕ × Tree Bool _ × ℕ → List (List ℕ) × ℕ
    opened (block , left , seen) = map₁ (block ∷_) (from ns ps left seen)

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
  from (build [] d nss) ws (drop-rest 0 n ws (build false d (replicate n true))) 0
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
    place : Bool × ℕ → List (List ℕ) × List (List ℕ) × ℕ
    place (true  , seen) = map₁ (b ∷_) (part bs seen)
    place (false , seen) = map₂ (map₁ (b ∷_)) (part bs seen)

  step : List (List ℕ) × ℕ → List (List ℕ) × ℕ
  step (bs , c) = joined (part bs c)
    where
    joined : List (List ℕ) × List (List ℕ) × ℕ → List (List ℕ) × ℕ
    joined (hit , miss , seen) = (w ∷ concat hit) ∷ miss , seen

thin : ℕ → ℕ → List ℕ
thin n v = go 0 0 v
  where
  next : ℕ → ℕ
  next c = if suc c ≡ᵇ n then 0 else suc c

  go : ℕ → ℕ → ℕ → List ℕ
  go i c zero    = []
  go i c (suc v) = if c ≡ᵇ 0 then go (suc i) (next c) v else i ∷ go (suc i) (next c) v

module Walks {a r} {A : Set a} {Adj : A → A → Set r} (Adj-sym : ∀ {x y} → Adj x y → Adj y x)
             (ws : List A) where

  -- Both ends of every edge taken are listed, so a walk read backwards is a walk.
  data Walk : A → A → Set (a ⊔ r) where
    stop : ∀ {x} → Walk x x
    step : ∀ {x y z} → x ∈ ws → y ∈ ws → Adj x y → Walk y z → Walk x z

  walk-trans : ∀ {x y z} → Walk x y → Walk y z → Walk x z
  walk-trans stop             w = w
  walk-trans (step mx my a v) w = step mx my a (walk-trans v w)

  walk-sym : ∀ {x y} → Walk x y → Walk y x
  walk-sym stop             = stop
  walk-sym (step mx my a w) = walk-trans (walk-sym w) (step my mx (Adj-sym a) stop)

  -- A walk that arrives anywhere else starts at a listed vertex.
  walk-∈ : ∀ {x y} → x ≢ y → Walk x y → x ∈ ws
  walk-∈ ne stop            = ⊥-elim (ne ≡-refl)
  walk-∈ ne (step mx _ _ _) = mx

  module Blocks (bss : List (List A)) (covers : concat bss ↭ ws)
                (disjoint : AllPairs (Apart _≡_) bss) (separated : AllPairs (Apart Adj) bss) where

    private
      block-of : {x : A} → x ∈ ws → Σ (List A) (λ bs → x ∈ bs × bs ∈ bss)
      block-of m = ∈-concat⁻′ bss (∈-resp-↭ (↭-sym covers) m)

    -- An edge leaving a block would join two blocks, so it stays inside.
    edge-in-block : {bs : List A} → bs ∈ bss → ∀ {x y} → x ∈ bs → y ∈ ws → Adj x y → y ∈ bs
    edge-in-block {bs} n {x} {y} mx my a = placed (block-of my)
      where
      placed : Σ (List A) (λ cs → y ∈ cs × cs ∈ bss) → y ∈ bs
      placed (cs , mz , n') with AllPairs-∈ separated n n'
      ... | inj₁ ≡-refl   = mz
      ... | inj₂ (inj₁ k) = ⊥-elim (All.lookup (All.lookup k mx) mz a)
      ... | inj₂ (inj₂ k) = ⊥-elim (All.lookup (All.lookup k mz) mx (Adj-sym a))

    walk-in-block : {bs : List A} → bs ∈ bss → ∀ {x y} → x ∈ bs → Walk x y → y ∈ bs
    walk-in-block n mx stop            = mx
    walk-in-block n mx (step _ my a w) = walk-in-block n (edge-in-block n mx my a) w

    -- Sharing no vertex with the block it cannot leave, a walk never reaches another block.
    apart : AllPairs (Apart Walk) bss
    apart = over (λ m → m) disjoint
      where
      over : {bss' : List (List A)} → (∀ {bs} → bs ∈ bss' → bs ∈ bss) →
             AllPairs (Apart _≡_) bss' → AllPairs (Apart Walk) bss'
      over lift []        = []
      over lift (dz ∷ ds) =
        All.map (λ d → All.tabulate (λ my → All.tabulate (λ mz w →
                  All.lookup (All.lookup d (walk-in-block (lift (here ≡-refl)) my w)) mz ≡-refl)))
                dz
        ∷ over (λ m → lift (there m)) ds

    -- Blocks whose members are joined to each other: sharing a block then decides being joined.
    module Connected (_≟_ : DecidableEquality A) (joined : All (AllPairs Walk) bss) where

      private
        shared : A → A → List A → Set a
        shared x y bs = x ∈ bs × y ∈ bs

        shared? : (x y : A) (bs : List A) → Dec (shared x y bs)
        shared? x y bs = any? (x ≟_) bs ×-dec any? (y ≟_) bs

        found : {x y : A} → Any (shared x y) bss → Walk x y
        found {x} {y} m = pick (All.lookupAny joined m)
          where
          pick : {bs : List A} → AllPairs Walk bs × shared x y bs → Walk x y
          pick (ps , mx , my) with AllPairs-∈ ps mx my
          ... | inj₁ ≡-refl   = stop
          ... | inj₂ (inj₁ w) = w
          ... | inj₂ (inj₂ w) = walk-sym w

        absent : {x y : A} → x ≢ y → ¬ Any (shared x y) bss → ¬ Walk x y
        absent {x} {y} ne k w = k (placed (block-of (walk-∈ ne w)))
          where
          placed : Σ (List A) (λ bs → x ∈ bs × bs ∈ bss) → Any (shared x y) bss
          placed (bs , mx , n) = Any.map (λ { ≡-refl → mx , walk-in-block n mx w }) n

      walk? : Decidable Walk
      walk? x y =
        dec-case (x ≟ y) (λ { ≡-refl → yes stop })
                 (λ ne → dec-case (any? (shared? x y) bss)
                                  (λ m → yes (found m)) (λ k → no (absent ne k)))

      private
        module P = Partitions walk? stop walk-sym

      open P public using (Partition; partitioned; unique)

      partition : All (_≢ []) bss → Partition ws bss
      partition ne = partitioned covers ne joined apart
