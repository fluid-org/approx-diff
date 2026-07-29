{-# OPTIONS --prop --postfix-projections --safe #-}

import Data.Bool as B
open import Data.Bool.ListAction using (any)
open import Data.List using (List; []; _∷_; allFin; map; filterᵇ; foldl; concat; partitionᵇ)
open import Data.Product using (proj₁; proj₂)
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
  hide-all (graph D) (map at (filterᵇ (λ p → B.not (is-ε p) B.∧ B.not (fo-at p)) (paths D)))

private
  nonzero : ∀ {m n} → M.Matrix m n → B.Bool
  nonzero {m} {n} R = any (λ i → any (λ j → is-I (R i j)) (allFin n)) (allFin m)
    where
      is-I : two.Two → B.Bool
      is-I two.I = B.true
      is-I two.O = B.false

-- Vertices sharing an incident edge, in either direction.
adjacent : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} →
           Graph D → Vertex D → Vertex D → B.Bool
adjacent G x y = nonzero (G x y) B.∨ nonzero (G y x)

-- The regions of a list of vertices: the weakly connected components of the subgraph induced by
-- its members. Each vertex merges the components it is adjacent to, the hide move's merging
-- specialised to singletons.
regions : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} →
          Graph D → List (Vertex D) → List (List (Vertex D))
regions G []       = []
regions G (w ∷ ws) = (w ∷ concat (proj₁ tp)) ∷ proj₂ tp
  where tp = partitionᵇ (any (adjacent G w)) (regions G ws)
