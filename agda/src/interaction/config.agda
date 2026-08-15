{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.Bool as Bool using (Bool; not; _∧_; _∨_; if_then_else_)
open import Data.Bool.ListAction using (any)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; allFin; map; filterᵇ; concat; partitionᵇ; foldr)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import list using (any-tabulate-false)
import matrix
import two

-- Configurations of the interaction: a visible set of vertices together with one hidden region per
-- weakly connected component of the hidden set, each carrying the dependence routed through it as
-- a summary. The visible graph reads the first-order graph at the visible vertices and the
-- summaries elsewhere. The hide move merges the regions adjacent to a vertex and the reveal move
-- splits the region containing one.
module interaction.config where

open import interaction.shape
open import interaction.graph-algebra

private
  module M = matrix.Mat two.semiring

private
  is-I : two.Two → Bool
  is-I two.I = Bool.true
  is-I two.O = Bool.false

nonzero : ∀ {m n} → M.Matrix m n → Bool
nonzero {m} {n} R = any (λ i → any (λ j → is-I (R i j)) (allFin n)) (allFin m)

nonzero-O : ∀ {m n} (R : M.Matrix m n) → nonzero R ≡ Bool.false →
            ∀ i j → R i j ≡ two.O
nonzero-O {m} {n} R h i j
  with R i j
     | any-tabulate-false (λ j' → j') (λ j' → is-I (R i j'))
         (any-tabulate-false (λ i' → i') (λ i' → any (λ j' → is-I (R i' j')) (allFin n)) h i) j
... | two.O | _  = ≡-refl
... | two.I | ()

when : ∀ {m n} → Bool → M.Matrix m n → M.Matrix m n
when Bool.true  R = R
when Bool.false R = M.εₘ

-- A configuration: the visible set, and one pair per hidden region of a set of vertices and a
-- graph. No invariant is imposed; that the pairs are the regions of the hidden set with their
-- summaries is a property the moves preserve.
record Config {Inp : Set} {iw : Inp → ℕ} {n : ℕ} (B : Graph Inp iw n) : Set₁ where
  field
    visible : List (Vertex (Graph.shape B))
    hidden  : List (List (Vertex (Graph.shape B)) × Entries (vw B))

open Config public

module Interaction {Inp : Set} {iw : Inp → ℕ} {n : ℕ} (B : Graph Inp iw n) where

  private
    at : Vertex (Graph.shape B) → V B
    at p = inj₂ (inj₁ p)

    eq : Vertex (Graph.shape B) → Vertex (Graph.shape B) → Bool
    eq p q = ⌊ _≟_ {Graph.shape B} p q ⌋

  member : Vertex (Graph.shape B) → List (Vertex (Graph.shape B)) → Bool
  member p = any (eq p)

  -- Vertices sharing an incident edge, in either direction.
  adjacent : Entries (vw B) → V B → V B → Bool
  adjacent G x y = nonzero (G x y) ∨ nonzero (G y x)

  -- Merge into one region the regions adjacent to a vertex, the hide move's merging specialised to
  -- singletons.
  merge-region : Entries (vw B) → Vertex (Graph.shape B) → List (List (Vertex (Graph.shape B))) →
                 List (List (Vertex (Graph.shape B)))
  merge-region G w rss = (w ∷ concat (proj₁ tp)) ∷ proj₂ tp
    where tp = partitionᵇ (any (λ q → adjacent G (at w) (at q))) rss

  -- The regions of a list of paths: the weakly connected components of the subgraph induced by its
  -- members.
  regions : Entries (vw B) → List (Vertex (Graph.shape B)) → List (List (Vertex (Graph.shape B)))
  regions G []       = []
  regions G (w ∷ ws) = merge-region G w (regions G ws)

  -- The inputs and the root are never hidden, so only an interior vertex can lie in a region.
  member-vertex : V B → List (Vertex (Graph.shape B)) → Bool
  member-vertex (inj₁ _)        C = Bool.false
  member-vertex (inj₂ (inj₁ p)) C = member p C
  member-vertex (inj₂ (inj₂ _)) C = Bool.false

  -- The dependence relations with an endpoint in the given region, zero elsewhere.
  restrict : Entries (vw B) → List (Vertex (Graph.shape B)) → Entries (vw B)
  restrict G C x y = when (member-vertex x C ∨ member-vertex y C) (G x y)

  -- The summary of a hidden region: the dependence routed through it, as relations between the
  -- vertices adjacent to it. Restriction first, so direct edges between boundary vertices are not
  -- carried by the summary.
  summary : List (Vertex (Graph.shape B)) → Entries (vw B)
  summary C = hide-all (vw B) (restrict (fo-graph B) C) (map at C)

  -- The initial configuration: everything hidden, one summary per region of FO.
  initial : Config B
  initial .visible = []
  initial .hidden  = map (λ C → C , summary C) (regions (fo-graph B) (FO B))

  -- The union of a configuration's hidden regions.
  hidden-set : Config B → List (Vertex (Graph.shape B))
  hidden-set K = concat (map proj₁ (K .hidden))

  -- The visible graph: the dependence relations of the first-order graph with neither endpoint
  -- hidden, together with those of the region summaries, parallel contributions summed.
  visible-graph : Config B → Entries (vw B)
  visible-graph K x y =
    foldr M._+ₘ_
          (when (not (member-vertex x hs) ∧ not (member-vertex y hs)) (fo-graph B x y))
          (map (λ CH → proj₂ CH x y) (K .hidden))
    where hs = hidden-set K

  _+G_ : Entries (vw B) → Entries (vw B) → Entries (vw B)
  (G +G H) x y = G x y M.+ₘ H x y

  -- The hide move: remove p from the visible set, merge the regions adjacent to p, and hide p in
  -- the graph assembling p's incident relations in the visible graph with the merged regions'
  -- summaries.
  hide-at : Vertex (Graph.shape B) → Config B → Config B
  hide-at p K .visible = filterᵇ (λ q → not (eq p q)) (K .visible)
  hide-at p K .hidden  =
    (p ∷ concat (map proj₁ (proj₁ tp)) , hide (vw B) assembled (at p)) ∷ proj₂ tp
    where
      tp = partitionᵇ (λ CH → any (λ q → adjacent (fo-graph B) (at p) (at q)) (proj₁ CH))
                      (K .hidden)
      assembled = foldr _+G_ (restrict (visible-graph K) (p ∷ [])) (map proj₂ (proj₁ tp))

  -- Split a stored region at p: recompute regions and summaries with p removed if the region
  -- contains p, and leave it alone otherwise.
  split-region : Vertex (Graph.shape B) → List (Vertex (Graph.shape B)) × Entries (vw B) →
                 List (List (Vertex (Graph.shape B)) × Entries (vw B))
  split-region p (C , H) =
    if member p C
    then map (λ C' → C' , summary C')
             (regions (fo-graph B) (filterᵇ (λ q → not (eq p q)) C))
    else (C , H) ∷ []

  -- The reveal move: return p to the visible set and split the region containing it, recomputing
  -- regions and summaries within that region alone.
  reveal-at : Vertex (Graph.shape B) → Config B → Config B
  reveal-at p K .visible = p ∷ K .visible
  reveal-at p K .hidden  = concat (map (split-region p) (K .hidden))
