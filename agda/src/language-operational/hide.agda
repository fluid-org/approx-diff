{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.Bool using (Bool; not; _∧_; _∨_)
open import Data.Bool.ListAction using (any)
open import Data.List using (List; []; _∷_; allFin; map; filterᵇ; foldl; concat; partitionᵇ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import signature using (Signature)
open import primitives using (Primitives)
import matrix
import two

-- Hiding an intermediate: each remaining entry absorbs the dependence routed through the hidden
-- vertex. Hidden vertices stay in the carrier, so hiding transforms the entry function and the
-- caller tracks which vertices are live; entries at a hidden vertex are stale, never read.
module language-operational.hide {ℓ} (Sig : Signature ℓ) (𝒫 : Primitives two.semiring Sig) where

open Signature Sig
open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.evaluation Sig 𝒫
open import language-operational.path Sig 𝒫
open import language-operational.graph Sig 𝒫

private
  module M = matrix.Mat two.semiring

hide : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} → Graph D → Vertex D → Graph D
hide G r x y = G x y M.+ₘ (G r y M.∘ G x r)

-- Hide a list of vertices, first to last; on acyclic graphs the order is immaterial.
hide-all : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} → Graph D → List (Vertex D) → Graph D
hide-all = foldl hide

-- The first-order dependence graph: the graph of the derivation with every intermediate whose
-- value is not first-order hidden, so that its live vertices are env, the root, and FO D.
fo-graph : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) → Graph D
fo-graph D =
  hide-all (graph D) (map at (filterᵇ (λ p → not (is-ε p) ∧ not (fo-at p)) (paths D)))

private
  nonzero : ∀ {m n} → M.Matrix m n → Bool
  nonzero {m} {n} R = any (λ i → any (λ j → is-I (R i j)) (allFin n)) (allFin m)
    where
      is-I : two.Two → Bool
      is-I two.I = Data.Bool.true
      is-I two.O = Data.Bool.false

-- Vertices sharing an incident edge, in either direction.
adjacent : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} →
           Graph D → Vertex D → Vertex D → Bool
adjacent G x y = nonzero (G x y) ∨ nonzero (G y x)

-- The regions of a list of paths: the weakly connected components of the subgraph induced by its
-- members. Each vertex merges the components it is adjacent to, the hide move's merging specialised
-- to singletons.
regions : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} →
          Graph D → List (Path D) → List (List (Path D))
regions G []       = []
regions G (w ∷ ws) = (w ∷ concat (proj₁ tp)) ∷ proj₂ tp
  where tp = partitionᵇ (any (λ q → adjacent G (at w) (at q))) (regions G ws)

member-vertex : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} →
                Vertex D → List (Path D) → Bool
member-vertex env    C = Data.Bool.false
member-vertex (at p) C = member p C

private
  when : ∀ {m n} → Bool → M.Matrix m n → M.Matrix m n
  when Data.Bool.true  R = R
  when Data.Bool.false R = M.εₘ

-- The entries with an endpoint in the given region, zero elsewhere.
restrict : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} →
           Graph D → List (Path D) → Graph D
restrict G C x y = when (member-vertex x C ∨ member-vertex y C) (G x y)

-- The summary of a hidden region: the dependence routed through it, as entries between the
-- vertices adjacent to it. Restriction first, so direct edges between boundary vertices are not
-- carried by the summary.
summary : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) →
          List (Path D) → Graph D
summary D C = hide-all (restrict (fo-graph D) C) (map at C)

-- A configuration: the visible set, and one pair per hidden region of a set of vertices and a
-- graph. No invariant is imposed; that the pairs are the regions of the hidden set with their
-- summaries is a property the moves preserve.
record Config {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) : Set ℓ where
  field
    visible : List (Path D)
    hidden  : List (List (Path D) × Graph D)

open Config public

-- The initial configuration: everything hidden, one summary per region of FO D.
initial : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) → Config D
initial D .visible = []
initial D .hidden  = map (λ C → C , summary D C) (regions (fo-graph D) (FO D))

-- The union of a configuration's hidden regions.
hidden-set : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} →
             Config D → List (Path D)
hidden-set K = concat (map proj₁ (K .hidden))

-- The visible graph: the entries of the first-order graph with neither endpoint hidden, together
-- with the entries of the region summaries, parallel contributions summed.
visible-graph : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) →
                Config D → Graph D
visible-graph D K x y =
  Data.List.foldr M._+ₘ_
        (when (not (member-vertex x hs) ∧ not (member-vertex y hs)) (fo-graph D x y))
        (map (λ CH → proj₂ CH x y) (K .hidden))
  where hs = hidden-set K
