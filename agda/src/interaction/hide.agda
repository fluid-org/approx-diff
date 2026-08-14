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
import interaction.hide-algebra

-- Hiding an intermediate: each remaining dependence relation absorbs the dependence routed
-- through the hidden vertex. Hidden vertices stay in the carrier, so hiding transforms the
-- relations and the caller tracks which vertices are live; relations at a hidden vertex are
-- stale, never read.
module interaction.hide {ℓ} (Sig : Signature ℓ) (𝒫 : Primitives two.semiring Sig) where

open Signature Sig
open Primitives 𝒫
open import language-syntax Sig renaming (_,_ to _▸_) hiding (foldr; if_then_else_)
open import language-operational.type-substitution Sig using (unfold₁)
open import language-operational.evaluation Sig two.semiring 𝒫 two.I
open import interaction.path Sig 𝒫
open import interaction.graph Sig 𝒫

private
  module M = matrix.Mat two.semiring

open import categories using (Category)
open Category M.cat using (_⇒_)

private
  module HA = interaction.hide-algebra

hide : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} → Graph D → Vertex D → Graph D
hide {D = D} = HA.Hide.h (Vertex D) vertex-width

-- Hide a list of vertices, first to last; on acyclic graphs the order is immaterial.
hide-all : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} → Graph D → List (Vertex D) → Graph D
hide-all = foldl hide

-- The first-order dependence graph: the graph of the derivation with every intermediate whose
-- value is not first-order hidden, so that its live vertices are env, the root, and FO D.
fo-graph : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) → Graph D
fo-graph D = hide-all (graph D) (map at (fo-hidden D))


-- Collapse: hide every path of the derivation and read the remaining dependence from env to the
-- root. Hiding the root itself is a no-op, since the root has no outgoing edges, so the whole
-- enumeration can be hidden.
collapse : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) →
           M.Matrix (width v) (width-env γ)
collapse D = hide-all (graph D) (map at (paths D)) env (at ε)

hide-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
         {D : γ , Ms ⇓s vs [ R ]} → GraphS D → VertexS D → GraphS D
hide-s {D = D} = HA.Hide.h (VertexS D) vertex-width-s

hide-all-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
             {D : γ , Ms ⇓s vs [ R ]} → GraphS D → List (VertexS D) → GraphS D
hide-all-s = foldl hide-s

collapse-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
             (D : γ , Ms ⇓s vs [ R ]) → M.Matrix (bases-width is) (width-env γ)
collapse-s D = hide-all-s (graph-s D) (map at (paths-s D)) env (at ε)

hide-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
         {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
         {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
         {D : Map γ s σ' v R v' R'} → GraphM D → VertexM D → GraphM D
hide-m {D = D} = HA.Hide.h (VertexM D) vertex-width-m

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
collapse-m-env D = hide-all-m (graph-m D) (map at (paths-m D)) env (at ε)

collapse-m-in : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
                {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
                {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
                (D : Map γ s σ' v R v' R') → M.Matrix (width v') (width v)
collapse-m-in D = hide-all-m (graph-m D) (map at (paths-m D)) input (at ε)
