{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.Bool as Bool using (Bool; not; _∧_; _∨_; if_then_else_)
open import Data.Bool.ListAction using (any)
open import Data.List using (List; []; _∷_; allFin; map; filterᵇ; concat; partitionᵇ; foldr)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl)
open import list using (any-tabulate-false)
open import signature using (Signature)
open import primitives using (Primitives)
import matrix
import two

-- Configurations of the interaction: a visible set of vertices together with one hidden region per
-- weakly connected component of the hidden set, each carrying the dependence routed through it as
-- a summary. The visible graph reads the first-order graph at the visible vertices and the
-- summaries elsewhere. The hide move merges the regions adjacent to a vertex and the reveal move
-- splits the region containing one.
module interaction.config {ℓ} (Sig : Signature ℓ) (𝒫 : Primitives two.semiring Sig) where

open Signature Sig
open Primitives 𝒫
open import language-syntax Sig renaming (_,_ to _▸_) hiding (foldr; if_then_else_)
open import language-operational.evaluation Sig 𝒫
open import interaction.path Sig 𝒫
open import interaction.graph Sig 𝒫
open import interaction.hide Sig 𝒫

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

-- Vertices sharing an incident edge, in either direction.
adjacent : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} →
           Graph D → Vertex D → Vertex D → Bool
adjacent G x y = nonzero (G x y) ∨ nonzero (G y x)

-- Merge into one region the regions adjacent to a vertex, the hide move's merging specialised to
-- singletons.
merge-region : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} →
               Graph D → Path D → List (List (Path D)) → List (List (Path D))
merge-region G w rss = (w ∷ concat (proj₁ tp)) ∷ proj₂ tp
  where tp = partitionᵇ (any (λ q → adjacent G (at w) (at q))) rss

-- The regions of a list of paths: the weakly connected components of the subgraph induced by its
-- members.
regions : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} →
          Graph D → List (Path D) → List (List (Path D))
regions G []       = []
regions G (w ∷ ws) = merge-region G w (regions G ws)

member-vertex : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} →
                Vertex D → List (Path D) → Bool
member-vertex env    C = Bool.false
member-vertex (at p) C = member p C

when : ∀ {m n} → Bool → M.Matrix m n → M.Matrix m n
when Bool.true  R = R
when Bool.false R = M.εₘ

-- The dependence relations with an endpoint in the given region, zero elsewhere.
restrict : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} →
           Graph D → List (Path D) → Graph D
restrict G C x y = when (member-vertex x C ∨ member-vertex y C) (G x y)

-- The summary of a hidden region: the dependence routed through it, as relations between the
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
hidden-set : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} → Config D → List (Path D)
hidden-set K = concat (map proj₁ (K .hidden))

-- The visible graph: the dependence relations of the first-order graph with neither endpoint
-- hidden, together with those of the region summaries, parallel contributions summed.
visible-graph : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) →
                Config D → Graph D
visible-graph D K x y =
  foldr M._+ₘ_
        (when (not (member-vertex x hs) ∧ not (member-vertex y hs)) (fo-graph D x y))
        (map (λ CH → proj₂ CH x y) (K .hidden))
  where hs = hidden-set K

_+G_ : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} →
       Graph D → Graph D → Graph D
(G +G H) x y = G x y M.+ₘ H x y

-- The hide move: remove p from the visible set, merge the regions adjacent to p, and hide p in the
-- graph assembling p's incident relations in the visible graph with the merged regions' summaries.
hide-at : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) →
          Path D → Config D → Config D
hide-at D p K .visible = filterᵇ (λ q → not (eq-path p q)) (K .visible)
hide-at D p K .hidden  = (p ∷ concat (map proj₁ (proj₁ tp)) , hide assembled (at p)) ∷ proj₂ tp
  where
    tp = partitionᵇ (λ CH → any (λ q → adjacent (fo-graph D) (at p) (at q)) (proj₁ CH))
                    (K .hidden)
    assembled = foldr _+G_ (restrict (visible-graph D K) (p ∷ [])) (map proj₂ (proj₁ tp))

-- Split a stored region at p: recompute regions and summaries with p removed if the region
-- contains p, and leave it alone otherwise.
split-region : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) →
               Path D → List (Path D) × Graph D → List (List (Path D) × Graph D)
split-region D p (C , H) =
  if member p C
  then map (λ C' → C' , summary D C')
           (regions (fo-graph D) (filterᵇ (λ q → not (eq-path p q)) C))
  else (C , H) ∷ []

-- The reveal move: return p to the visible set and split the region containing it, recomputing
-- regions and summaries within that region alone.
reveal-at : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) →
            Path D → Config D → Config D
reveal-at D p K .visible = p ∷ K .visible
reveal-at D p K .hidden  = concat (map (split-region D p) (K .hidden))
