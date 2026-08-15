{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_; universal)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
import Data.List.Relation.Unary.All.Properties as AllP
import Data.List.Relation.Unary.AllPairs.Properties as AllPairsP
open import Data.Unit using (⊤; tt)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong)
open import Relation.Nullary.Decidable using (yes; no)
open import basics using (IsStrictOrder)
open import list using (AllPairs-map)

-- The branching of a derivation, and the paths into it. A vertex names a premise, repeatedly, and
-- then either descends or stops at that premise's result.
module interaction.shape where

data Shape : Set where
  node : List Shape → Shape

data Vertex : Shape → Set where
  stop  : ∀ {s ss} → Vertex (node (s ∷ ss))
  down  : ∀ {s ss} → Vertex s → Vertex (node (s ∷ ss))
  next  : ∀ {s ss} → Vertex (node ss) → Vertex (node (s ∷ ss))

down-injective : ∀ {s ss} {u v : Vertex s} → down {ss = ss} u ≡ down v → u ≡ v
down-injective refl = refl

next-injective : ∀ {s ss} {u v : Vertex (node ss)} → next {s = s} u ≡ next v → u ≡ v
next-injective refl = refl

_≟_ : ∀ {s} → DecidableEquality (Vertex s)
stop   ≟ stop   = yes refl
stop   ≟ down v = no λ ()
stop   ≟ next v = no λ ()
down u ≟ stop   = no λ ()
down u ≟ down v with u ≟ v
... | yes e = yes (cong down e)
... | no ¬e = no λ e → ¬e (down-injective e)
down u ≟ next v = no λ ()
next u ≟ stop   = no λ ()
next u ≟ down v = no λ ()
next u ≟ next v with u ≟ v
... | yes e = yes (cong next e)
... | no ¬e = no λ e → ¬e (next-injective e)

-- The vertices of a shape, each premise's result first, then its interior, then the premises after
-- it. This fixes the order in which they are hidden.
mutual
  vertices : (s : Shape) → List (Vertex s)
  vertices (node ss) = vertices-of ss

  vertices-of : (ss : List Shape) → List (Vertex (node ss))
  vertices-of []       = []
  vertices-of (s ∷ ss) = stop ∷ (map down (vertices s) ++ map next (vertices-of ss))

mutual
  distinct : (s : Shape) → AllPairs _≢_ (vertices s)
  distinct (node ss) = distinct-of ss

  distinct-of : (ss : List Shape) → AllPairs _≢_ (vertices-of ss)
  distinct-of []       = []
  distinct-of (s ∷ ss) =
    AllP.++⁺ (AllP.map⁺ (universal (λ _ ()) (vertices s)))
             (AllP.map⁺ (universal (λ _ ()) (vertices-of ss)))
    ∷ AllPairsP.++⁺ (AllPairsP.map⁺ (AllPairs-map (λ h e → h (down-injective e)) (distinct s)))
                    (AllPairsP.map⁺ (AllPairs-map (λ h e → h (next-injective e)) (distinct-of ss)))
                    (AllP.map⁺ (universal (λ _ → AllP.map⁺ (universal (λ _ ()) _)) _))

-- The completion order: a premise's interior before its result, and every premise before those
-- after it.
_<_ : ∀ {s} → Vertex s → Vertex s → Set
stop   < stop   = ⊥
stop   < down _ = ⊥
stop   < next _ = ⊤
down _ < stop   = ⊤
down u < down v = u < v
down _ < next _ = ⊤
next _ < stop   = ⊥
next _ < down _ = ⊥
next u < next v = u < v

<-trans : ∀ {s} (u v w : Vertex s) → u < v → v < w → u < w
<-trans stop     stop     w        () b
<-trans stop     (down _) w        () b
<-trans stop     (next _) stop     a  ()
<-trans stop     (next _) (down _) a  ()
<-trans stop     (next _) (next _) a  b  = tt
<-trans (down _) stop     stop     a  ()
<-trans (down _) stop     (down _) a  ()
<-trans (down _) stop     (next _) a  b  = tt
<-trans (down u) (down v) stop     a  b  = tt
<-trans (down u) (down v) (down w) a  b  = <-trans u v w a b
<-trans (down u) (down v) (next _) a  b  = tt
<-trans (down _) (next _) stop     a  ()
<-trans (down _) (next _) (down _) a  ()
<-trans (down _) (next _) (next _) a  b  = tt
<-trans (next _) stop     w        () b
<-trans (next _) (down _) w        () b
<-trans (next u) (next v) stop     a  ()
<-trans (next u) (next v) (down _) a  ()
<-trans (next u) (next v) (next w) a  b  = <-trans u v w a b

<-asym : ∀ {s} (u v : Vertex s) → u < v → v < u → ⊥
<-asym stop     stop     () b
<-asym stop     (down _) () b
<-asym stop     (next _) a  ()
<-asym (down _) stop     a  ()
<-asym (down u) (down v) a  b = <-asym u v a b
<-asym (down _) (next _) a  ()
<-asym (next _) stop     () b
<-asym (next _) (down _) () b
<-asym (next u) (next v) a  b = <-asym u v a b

<-order : ∀ {s} → IsStrictOrder {A = Vertex s} _<_
<-order .IsStrictOrder.trans = <-trans
<-order .IsStrictOrder.asym = <-asym
