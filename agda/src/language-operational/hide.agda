{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.Bool as Bool using (Bool; not; _∧_; _∨_; if_then_else_)
open import Data.Bool.ListAction using (any)
open import Data.List using (List; []; _∷_; allFin; map; filterᵇ; foldl; foldr; concat; partitionᵇ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl)
open import every using (Every; []; _∷_)
open import list using (any-tabulate-false)
open import signature using (Signature)
open import primitives using (Primitives)
import matrix
import two

-- Hiding an intermediate: each remaining entry absorbs the dependence routed through the hidden
-- vertex. Hidden vertices stay in the carrier, so hiding transforms the entry function and the
-- caller tracks which vertices are live; entries at a hidden vertex are stale, never read.
module language-operational.hide {ℓ} (Sig : Signature ℓ) (𝒫 : Primitives two.semiring Sig) where

open Signature Sig
open Primitives 𝒫
open import language-syntax Sig renaming (_,_ to _▸_) hiding (foldr; if_then_else_)
open import type-substitution Sig using (unfold₁)
open import language-operational.evaluation Sig 𝒫
open import language-operational.path Sig 𝒫
open import language-operational.graph Sig 𝒫

private
  module M = matrix.Mat two.semiring

open import categories using (Category)
open Category M.cat using (_⇒_)

hide : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} → Graph D → Vertex D → Graph D
hide G r x y = G x y M.+ₘ (G r y M.∘ G x r)

-- Hide a list of vertices, first to last; on acyclic graphs the order is immaterial.
hide-all : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} → Graph D → List (Vertex D) → Graph D
hide-all = foldl hide

-- The dependence routed through the listed vertices: entries sum the composites along the paths
-- from x to y whose interior vertices form a sublist of ws, taken in list order. When ws ascends
-- in rank this sums exactly the paths through ws, and agrees with hide-all (topological-order).
path-sum : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} →
           Graph D → List (Vertex D) → Graph D
path-sum G []       x y = G x y
path-sum G (r ∷ ws) x y = path-sum G ws x y M.+ₘ (path-sum G ws r y M.∘ G x r)

-- The first-order dependence graph: the graph of the derivation with every intermediate whose
-- value is not first-order hidden, so that its live vertices are env, the root, and FO D.
fo-graph : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) → Graph D
fo-graph D =
  hide-all (graph D) (map at (filterᵇ (λ p → not (is-ε p) ∧ not (fo-at p)) (paths D)))

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
member-vertex env    C = Bool.false
member-vertex (at p) C = member p C

when : ∀ {m n} → Bool → M.Matrix m n → M.Matrix m n
when Bool.true  R = R
when Bool.false R = M.εₘ

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
hidden-set : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} → Config D → List (Path D)
hidden-set K = concat (map proj₁ (K .hidden))

-- The visible graph: the entries of the first-order graph with neither endpoint hidden, together
-- with the entries of the region summaries, parallel contributions summed.
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
-- graph assembling p's incident entries in the visible graph with the merged regions' summaries.
hide-at : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) →
          Path D → Config D → Config D
hide-at D p K .visible = filterᵇ (λ q → not (eq-path p q)) (K .visible)
hide-at D p K .hidden  = (p ∷ concat (map proj₁ (proj₁ tp)) , hide assembled (at p)) ∷ proj₂ tp
  where
    tp = partitionᵇ (λ CH → any (λ q → adjacent (fo-graph D) (at p) (at q)) (proj₁ CH))
                    (K .hidden)
    assembled = foldr _+G_ (restrict (visible-graph D K) (p ∷ [])) (map proj₂ (proj₁ tp))

-- The reveal move: return p to the visible set and split the region containing it, recomputing
-- regions and summaries within that region alone.
reveal-at : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) →
            Path D → Config D → Config D
reveal-at D p K .visible = p ∷ K .visible
reveal-at D p K .hidden  = concat (map step (K .hidden))
  where
    step : List (Path D) × Graph D → List (List (Path D) × Graph D)
    step (C , H) =
      if member p C
      then map (λ C' → C' , summary D C')
               (regions (fo-graph D) (filterᵇ (λ q → not (eq-path p q)) C))
      else (C , H) ∷ []

-- Collapse: hide every path of the derivation and read the remaining dependence from env to the
-- root. Hiding the root itself is a no-op, since the root has no outgoing edges, so the whole
-- enumeration can be hidden.
collapse : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) →
           M.Matrix (width v) (width-env γ)
collapse D = hide-all (graph D) (map at (paths D)) env (at ε)

hide-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
         {D : γ , Ms ⇓s vs [ R ]} → GraphS D → VertexS D → GraphS D
hide-s G r x y = G x y M.+ₘ (G r y M.∘ G x r)

hide-all-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
             {D : γ , Ms ⇓s vs [ R ]} → GraphS D → List (VertexS D) → GraphS D
hide-all-s = foldl hide-s

collapse-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
             (D : γ , Ms ⇓s vs [ R ]) → M.Matrix (bases-width is) (width-env γ)
collapse-s D = hide-all-s (graphS D) (map at (paths-s D)) env (at ε)

hide-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
         {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
         {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
         {D : Map γ s σ' v R v' R'} → GraphM D → VertexM D → GraphM D
hide-m G r x y = G x y M.+ₘ (G r y M.∘ G x r)

hide-all-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
             {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
             {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
             {D : Map γ s σ' v R v' R'} → GraphM D → List (VertexM D) → GraphM D
hide-all-m = foldl hide-m

-- The two collapses of a fold-action graph: the dependence of the result on the environment, and
-- on the input value.
collapse-m-env : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
                 {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
                 {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
                 (D : Map γ s σ' v R v' R') → M.Matrix (width v') (width-env γ)
collapse-m-env D = hide-all-m (graphM D) (map at (paths-m D)) env (at ε)

collapse-m-in : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
                {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
                {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
                (D : Map γ s σ' v R v' R') → M.Matrix (width v') (width v)
collapse-m-in D = hide-all-m (graphM D) (map at (paths-m D)) input (at ε)
