{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_; universal)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
import Data.List.Relation.Unary.All.Properties as AllP
import Data.List.Relation.Unary.AllPairs.Properties as AllPairsP
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Sum.Properties as SumP
open import Data.Unit using (⊤; tt)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary.Decidable using (yes; no)
open import basics using (IsStrictOrder)
open import list using (AllPairs-map)

-- The branching of a derivation, and the paths into it. A vertex names a premise and then either
-- descends into it or stops at its result, so the vertices of a rule are its premises' vertices
-- with each premise's result adjoined.
module interaction.shape where

data Shape : Set where
  node : List Shape → Shape

data Root : Set where
  root : Root

mutual
  Vertex : Shape → Set
  Vertex (node ss) = Vertices ss

  Vertices : List Shape → Set
  Vertices []           = ⊥
  Vertices (s ∷ [])     = Vertex s ⊎ Root
  Vertices (s ∷ t ∷ ss) = (Vertex s ⊎ Root) ⊎ Vertices (t ∷ ss)

root-≟ : DecidableEquality Root
root-≟ root root = yes refl

mutual
  _≟_ : ∀ {s} → DecidableEquality (Vertex s)
  _≟_ {node ss} = _≟s_ {ss}

  _≟s_ : ∀ {ss} → DecidableEquality (Vertices ss)
  _≟s_ {s ∷ []}     = SumP.≡-dec (_≟_ {s}) root-≟
  _≟s_ {s ∷ t ∷ ss} = SumP.≡-dec (SumP.≡-dec (_≟_ {s}) root-≟) (_≟s_ {t ∷ ss})

-- The vertices of a shape, each premise's result first, then its interior, then the premises after
-- it. This fixes the order in which they are hidden.
mutual
  vertices : (s : Shape) → List (Vertex s)
  vertices (node ss) = vertices-of ss

  vertices-of : (ss : List Shape) → List (Vertices ss)
  vertices-of []           = []
  vertices-of (s ∷ [])     = inj₂ root ∷ map inj₁ (vertices s)
  vertices-of (s ∷ t ∷ ss) =
    map inj₁ (inj₂ root ∷ map inj₁ (vertices s)) ++ map inj₂ (vertices-of (t ∷ ss))

private
  sum-distinct : {A B : Set} {xs : List A} {ys : List B} →
                 AllPairs _≢_ xs → AllPairs _≢_ ys →
                 AllPairs _≢_ (map inj₁ xs ++ map inj₂ ys)
  sum-distinct {xs = xs} {ys = ys} dx dy =
    AllPairsP.++⁺ (AllPairsP.map⁺ (AllPairs-map (λ h e → h (SumP.inj₁-injective e)) dx))
                  (AllPairsP.map⁺ (AllPairs-map (λ h e → h (SumP.inj₂-injective e)) dy))
                  (AllP.map⁺ (universal (λ _ → AllP.map⁺ (universal (λ _ ()) ys)) xs))

mutual
  distinct : (s : Shape) → AllPairs _≢_ (vertices s)
  distinct (node ss) = distinct-of ss

  distinct-of : (ss : List Shape) → AllPairs _≢_ (vertices-of ss)
  distinct-of []           = []
  distinct-of (s ∷ [])     =
    AllP.map⁺ (universal (λ _ ()) (vertices s))
    ∷ AllPairsP.map⁺ (AllPairs-map (λ h e → h (SumP.inj₁-injective e)) (distinct s))
  distinct-of (s ∷ t ∷ ss) =
    sum-distinct (AllP.map⁺ (universal (λ _ ()) (vertices s))
                  ∷ AllPairsP.map⁺ (AllPairs-map (λ h e → h (SumP.inj₁-injective e)) (distinct s)))
                 (distinct-of (t ∷ ss))

-- The completion order: a premise's interior before its result, and every premise before those
-- after it. The shape is explicit, since it cannot be recovered from a vertex.
mutual
  lt : (s : Shape) → Vertex s → Vertex s → Set
  lt (node ss) = lts ss

  lts : (ss : List Shape) → Vertices ss → Vertices ss → Set
  lts (s ∷ [])     (inj₁ u)        (inj₁ v)        = lt s u v
  lts (s ∷ [])     (inj₁ _)        (inj₂ _)        = ⊤
  lts (s ∷ [])     (inj₂ _)        _               = ⊥
  lts (s ∷ t ∷ ss) (inj₁ (inj₁ u)) (inj₁ (inj₁ v)) = lt s u v
  lts (s ∷ t ∷ ss) (inj₁ (inj₁ _)) (inj₁ (inj₂ _)) = ⊤
  lts (s ∷ t ∷ ss) (inj₁ (inj₂ _)) (inj₁ _)        = ⊥
  lts (s ∷ t ∷ ss) (inj₁ _)        (inj₂ _)        = ⊤
  lts (s ∷ t ∷ ss) (inj₂ _)        (inj₁ _)        = ⊥
  lts (s ∷ t ∷ ss) (inj₂ u)        (inj₂ v)        = lts (t ∷ ss) u v

mutual
  lt-trans : (s : Shape) (u v w : Vertex s) → lt s u v → lt s v w → lt s u w
  lt-trans (node ss) = lts-trans ss

  lts-trans : (ss : List Shape) (u v w : Vertices ss) → lts ss u v → lts ss v w → lts ss u w
  lts-trans (s ∷ [])     (inj₁ u)        (inj₁ v)        (inj₁ w)        a b = lt-trans s u v w a b
  lts-trans (s ∷ [])     (inj₁ u)        (inj₁ v)        (inj₂ _)        a b = tt
  lts-trans (s ∷ [])     (inj₁ u)        (inj₂ _)        w               a ()
  lts-trans (s ∷ [])     (inj₂ _)        v               w               () b
  lts-trans (s ∷ t ∷ ss) (inj₁ (inj₁ u)) (inj₁ (inj₁ v)) (inj₁ (inj₁ w)) a b = lt-trans s u v w a b
  lts-trans (s ∷ t ∷ ss) (inj₁ (inj₁ u)) (inj₁ (inj₁ v)) (inj₁ (inj₂ _)) a b = tt
  lts-trans (s ∷ t ∷ ss) (inj₁ (inj₁ u)) (inj₁ (inj₁ v)) (inj₂ _)        a b = tt
  lts-trans (s ∷ t ∷ ss) (inj₁ (inj₁ u)) (inj₁ (inj₂ _)) (inj₁ _)        a ()
  lts-trans (s ∷ t ∷ ss) (inj₁ (inj₁ u)) (inj₁ (inj₂ _)) (inj₂ _)        a b = tt
  lts-trans (s ∷ t ∷ ss) (inj₁ (inj₁ u)) (inj₂ _)        (inj₁ _)        a ()
  lts-trans (s ∷ t ∷ ss) (inj₁ (inj₁ u)) (inj₂ _)        (inj₂ _)        a b = tt
  lts-trans (s ∷ t ∷ ss) (inj₁ (inj₂ _)) (inj₁ _)        w               () b
  lts-trans (s ∷ t ∷ ss) (inj₁ (inj₂ _)) (inj₂ _)        (inj₁ _)        a ()
  lts-trans (s ∷ t ∷ ss) (inj₁ (inj₂ _)) (inj₂ _)        (inj₂ _)        a b = tt
  lts-trans (s ∷ t ∷ ss) (inj₂ _)        (inj₁ _)        w               () b
  lts-trans (s ∷ t ∷ ss) (inj₂ _)        (inj₂ _)        (inj₁ _)        a ()
  lts-trans (s ∷ t ∷ ss) (inj₂ u)        (inj₂ v)        (inj₂ w)        a b =
    lts-trans (t ∷ ss) u v w a b

mutual
  lt-asym : (s : Shape) (u v : Vertex s) → lt s u v → lt s v u → ⊥
  lt-asym (node ss) = lts-asym ss

  lts-asym : (ss : List Shape) (u v : Vertices ss) → lts ss u v → lts ss v u → ⊥
  lts-asym (s ∷ [])     (inj₁ u)        (inj₁ v)        a b = lt-asym s u v a b
  lts-asym (s ∷ [])     (inj₁ _)        (inj₂ _)        a ()
  lts-asym (s ∷ [])     (inj₂ _)        v               () b
  lts-asym (s ∷ t ∷ ss) (inj₁ (inj₁ u)) (inj₁ (inj₁ v)) a b = lt-asym s u v a b
  lts-asym (s ∷ t ∷ ss) (inj₁ (inj₁ _)) (inj₁ (inj₂ _)) a ()
  lts-asym (s ∷ t ∷ ss) (inj₁ (inj₁ _)) (inj₂ _)        a ()
  lts-asym (s ∷ t ∷ ss) (inj₁ (inj₂ _)) (inj₁ _)        () b
  lts-asym (s ∷ t ∷ ss) (inj₁ (inj₂ _)) (inj₂ _)        a ()
  lts-asym (s ∷ t ∷ ss) (inj₂ _)        (inj₁ _)        () b
  lts-asym (s ∷ t ∷ ss) (inj₂ u)        (inj₂ v)        a b = lts-asym (t ∷ ss) u v a b

lt-order : (s : Shape) → IsStrictOrder (lt s)
lt-order s .IsStrictOrder.trans = lt-trans s
lt-order s .IsStrictOrder.asym = lt-asym s

lts-order : (ss : List Shape) → IsStrictOrder (lts ss)
lts-order ss .IsStrictOrder.trans = lts-trans ss
lts-order ss .IsStrictOrder.asym = lts-asym ss
