{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.Fin using (zero)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import every using (Every; []; _∷_)
open import prop-setoid using () renaming (_⇒_ to _⇒ₛ_)
open import signature using (Signature)
open import primitives using (Primitives)
import matrix
import two

-- Dependence graphs over a derivation: a graph gives for each pair of vertices a dependence
-- relation between their widths, the zero relation meaning no edge. The graph judgement is a
-- function from derivations to graphs, one clause group per rule; unions are pointwise sums
-- realised by a single final zero clause, prefixing is reindexing by path constructors, and
-- rewiring redistributes a premise's env column through the biproduct injections.
module interaction.graph {ℓ} (Sig : Signature ℓ) (𝒫 : Primitives two.semiring Sig) where

open Signature Sig
open Primitives 𝒫
open _⇒ₛ_ using (func)
open import language-syntax Sig renaming (_,_ to _▸_)
open import type-substitution Sig using (unfold₁; unfold₁-inst)
open import language-operational.evaluation Sig 𝒫
open import interaction.path Sig 𝒫

private
  module M = matrix.Mat two.semiring

open import categories using (Category)
open Category M.cat using (_⇒_; _∘_)

data Vertex {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v : Val τ} {R : _} (D : γ , t ⇓ v [ R ]) : Set ℓ where
  env : Vertex D
  at  : Path D → Vertex D

data VertexS {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs} {R : _}
             (D : γ , Ms ⇓s vs [ R ]) : Set ℓ where
  env : VertexS D
  at  : PathS D → VertexS D

-- A fold-action derivation has a second source alongside env: the input value being folded over.
-- The fold rule wires it to the root of its first premise, the way a case branch wires its
-- environment extension to the scrutinee root.
data VertexM {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
             {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
             {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
             (D : Map γ s σ' v R v' R') : Set ℓ where
  env   : VertexM D
  input : VertexM D
  at    : PathM D → VertexM D

vertex-width : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} → Vertex D → ℕ
vertex-width {γ = γ} env = width-env γ
vertex-width (at p)      = width-at p

vertex-width-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
      {D : γ , Ms ⇓s vs [ R ]} → VertexS D → ℕ
vertex-width-s {γ = γ} env = width-env γ
vertex-width-s (at p)      = width-at-s p

vertex-width-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
      {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
      {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
      {D : Map γ s σ' v R v' R'} → VertexM D → ℕ
vertex-width-m {γ = γ} env     = width-env γ
vertex-width-m {v = v} input   = width v
vertex-width-m (at p)          = width-at-m p

Graph : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} → γ , t ⇓ v [ R ] → Set ℓ
Graph D = (x y : Vertex D) → M.Matrix (vertex-width y) (vertex-width x)

GraphS : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R} →
         γ , Ms ⇓s vs [ R ] → Set ℓ
GraphS D = (x y : VertexS D) → M.Matrix (vertex-width-s y) (vertex-width-s x)

GraphM : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
         {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
      {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'} →
         Map γ s σ' v R v' R' → Set ℓ
GraphM D = (x y : VertexM D) → M.Matrix (vertex-width-m y) (vertex-width-m x)

-- Cast a matrix along equalities of its row and column dimensions.
rcast : ∀ {m m' n} → m ≡ m' → M.Matrix m n → M.Matrix m' n
rcast refl R = R

ccast : ∀ {m n n'} → n ≡ n' → M.Matrix m n → M.Matrix m n'
ccast refl R = R

-- The single-edge graph out of a premise's root, read as its dependence relation at each source
-- path: the given relation at the root, zero elsewhere. Defined generically because case-splitting
-- a premise's path type gets stuck when the premise's indices are function-headed (e.g. a scrutinee
-- required to evaluate to inl v).
edge : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} {m} →
       M.Matrix m (width v) → (p : Path D) → M.Matrix m (width-at p)
edge R ε = R
edge R _ = M.εₘ

edge-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
            {D : γ , Ms ⇓s vs [ R ]} {m} →
            M.Matrix m (bases-width is) → (p : PathS D) → M.Matrix m (width-at-s p)
edge-s R ε = R
edge-s R _ = M.εₘ

edge-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
            {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
            {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
            {D : Map γ s σ' v R v' R'} {m} →
            M.Matrix m (width v') → (p : PathM D) → M.Matrix m (width-at-m p)
edge-m R ε = R
edge-m R _ = M.εₘ

mutual
  graph : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) → Graph D
  graph (⇓-var {γ = γ} x) env (at ε) = proj-var x γ

  graph (⇓-inl D) env       (at (inl q)) = graph D env (at q)
  graph (⇓-inl D) (at (inl p)) (at (inl q)) = graph D (at p) (at q)
  graph (⇓-inl D) (at (inl p)) (at ε) = edge (M.in₂ {1}) p

  graph (⇓-inr D) env       (at (inr q)) = graph D env (at q)
  graph (⇓-inr D) (at (inr p)) (at (inr q)) = graph D (at p) (at q)
  graph (⇓-inr D) (at (inr p)) (at ε) = edge (M.in₂ {1}) p

  graph (⇓-case-l D₁ D₂) env (at (case-l₁ q)) = graph D₁ env (at q)
  graph (⇓-case-l D₁ D₂) (at (case-l₁ p)) (at (case-l₁ q)) = graph D₁ (at p) (at q)
  graph (⇓-case-l D₁ D₂) env (at (case-l₂ q)) = graph D₂ env (at q) ∘ M.in₁
  graph (⇓-case-l D₁ D₂) (at (case-l₁ p)) (at (case-l₂ q)) =
    edge (graph D₂ env (at q) ∘ M.in₂ ∘ M.p₂ {1}) p
  graph (⇓-case-l D₁ D₂) (at (case-l₂ p)) (at (case-l₂ q)) = graph D₂ (at p) (at q)
  graph (⇓-case-l D₁ D₂) (at (case-l₂ p)) (at ε) = edge M.I p

  graph (⇓-case-r D₁ D₂) env (at (case-r₁ q)) = graph D₁ env (at q)
  graph (⇓-case-r D₁ D₂) (at (case-r₁ p)) (at (case-r₁ q)) = graph D₁ (at p) (at q)
  graph (⇓-case-r D₁ D₂) env (at (case-r₂ q)) = graph D₂ env (at q) ∘ M.in₁
  graph (⇓-case-r D₁ D₂) (at (case-r₁ p)) (at (case-r₂ q)) =
    edge (graph D₂ env (at q) ∘ M.in₂ ∘ M.p₂ {1}) p
  graph (⇓-case-r D₁ D₂) (at (case-r₂ p)) (at (case-r₂ q)) = graph D₂ (at p) (at q)
  graph (⇓-case-r D₁ D₂) (at (case-r₂ p)) (at ε) = edge M.I p

  graph (⇓-pair D₁ D₂) env (at (pair₁ q)) = graph D₁ env (at q)
  graph (⇓-pair D₁ D₂) (at (pair₁ p)) (at (pair₁ q)) = graph D₁ (at p) (at q)
  graph (⇓-pair D₁ D₂) env (at (pair₂ q)) = graph D₂ env (at q)
  graph (⇓-pair D₁ D₂) (at (pair₂ p)) (at (pair₂ q)) = graph D₂ (at p) (at q)
  graph (⇓-pair D₁ D₂) (at (pair₁ p)) (at ε) = edge (M.in₂ {1} ∘ M.in₁) p
  graph (⇓-pair D₁ D₂) (at (pair₂ p)) (at ε) = edge (M.in₂ {1} ∘ M.in₂) p

  graph (⇓-fst D) env (at (fst q)) = graph D env (at q)
  graph (⇓-fst D) (at (fst p)) (at (fst q)) = graph D (at p) (at q)
  graph (⇓-fst D) (at (fst p)) (at ε) = edge (M.p₁ ∘ M.p₂ {1}) p

  graph (⇓-snd D) env (at (snd q)) = graph D env (at q)
  graph (⇓-snd D) (at (snd p)) (at (snd q)) = graph D (at p) (at q)
  graph (⇓-snd D) (at (snd p)) (at ε) = edge (M.p₂ ∘ M.p₂ {1}) p

  graph ⇓-lam env (at ε) = M.in₂ {1}

  graph (⇓-app D₁ D₂ D₃) env (at (app₁ q)) = graph D₁ env (at q)
  graph (⇓-app D₁ D₂ D₃) (at (app₁ p)) (at (app₁ q)) = graph D₁ (at p) (at q)
  graph (⇓-app D₁ D₂ D₃) env (at (app₂ q)) = graph D₂ env (at q)
  graph (⇓-app D₁ D₂ D₃) (at (app₂ p)) (at (app₂ q)) = graph D₂ (at p) (at q)
  graph (⇓-app D₁ D₂ D₃) (at (app₁ p)) (at (app₃ q)) =
    edge (graph D₃ env (at q) ∘ M.in₁ ∘ M.p₂ {1}) p
  graph (⇓-app D₁ D₂ D₃) (at (app₂ p)) (at (app₃ q)) = edge (graph D₃ env (at q) ∘ M.in₂) p
  graph (⇓-app D₁ D₂ D₃) (at (app₃ p)) (at (app₃ q)) = graph D₃ (at p) (at q)
  graph (⇓-app D₁ D₂ D₃) (at (app₃ p)) (at ε) = edge M.I p

  graph (⇓-bop {ω = ω} {vs = vs} D) env (at (bop q)) = graph-s D env (at q)
  graph (⇓-bop D) (at (bop p)) (at (bop q)) = graph-s D (at p) (at q)
  graph (⇓-bop {ω = ω} {vs = vs} D) (at (bop p)) (at ε) = edge-s (op-deps ω .func vs) p

  graph (⇓-brel D) env (at (brel q)) = graph-s D env (at q)
  graph (⇓-brel D) (at (brel p)) (at (brel q)) = graph-s D (at p) (at q)
  graph (⇓-brel {ω = ω} {vs = vs} D) (at (brel p)) (at ε) =
    edge-s (brel-deps ω vs (rel-pred ω .func vs)) p

  graph (⇓-roll D) env (at (roll q)) = graph D env (at q)
  graph (⇓-roll D) (at (roll p)) (at (roll q)) = graph D (at p) (at q)
  graph (⇓-roll D) (at (roll p)) (at ε) = edge M.I p

  graph (⇓-fold D₁ D₂) env (at (fold₁ q)) = graph D₁ env (at q)
  graph (⇓-fold D₁ D₂) (at (fold₁ p)) (at (fold₁ q)) = graph D₁ (at p) (at q)
  graph (⇓-fold D₁ D₂) env (at (fold₂ q)) = graph-m D₂ env (at q)
  graph (⇓-fold D₁ D₂) (at (fold₁ p)) (at (fold₂ q)) = edge (graph-m D₂ input (at q)) p
  graph (⇓-fold D₁ D₂) (at (fold₂ p)) (at (fold₂ q)) = graph-m D₂ (at p) (at q)
  graph (⇓-fold D₁ D₂) (at (fold₂ p)) (at ε) = edge-m M.I p

  graph D _ _ = M.εₘ

  graph-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
           (D : γ , Ms ⇓s vs [ R ]) → GraphS D
  graph-s (D₁ ∷ D₂) env (at (hd q)) = graph D₁ env (at q)
  graph-s (D₁ ∷ D₂) (at (hd p)) (at (hd q)) = graph D₁ (at p) (at q)
  graph-s (D₁ ∷ D₂) env (at (tl q)) = graph-s D₂ env (at q)
  graph-s (D₁ ∷ D₂) (at (tl p)) (at (tl q)) = graph-s D₂ (at p) (at q)
  graph-s (D₁ ∷ D₂) (at (hd p)) (at ε) = edge M.in₁ p
  graph-s (D₁ ∷ D₂) (at (tl p)) (at ε) = edge-s M.in₂ p
  graph-s D _ _ = M.εₘ

  graph-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
           {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
      {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
           (D : Map γ s σ' v R v' R') → GraphM D
  graph-m (m-rec D₁ D₂) env (at (m-rec₁ q)) = graph-m D₁ env (at q)
  graph-m (m-rec D₁ D₂) input (at (m-rec₁ q)) = graph-m D₁ input (at q)
  graph-m (m-rec D₁ D₂) (at (m-rec₁ p)) (at (m-rec₁ q)) = graph-m D₁ (at p) (at q)
  graph-m (m-rec D₁ D₂) env (at (m-rec₂ q)) = graph D₂ env (at q) ∘ M.in₁
  graph-m (m-rec D₁ D₂) (at (m-rec₁ p)) (at (m-rec₂ q)) = edge-m (graph D₂ env (at q) ∘ M.in₂) p
  graph-m (m-rec D₁ D₂) (at (m-rec₂ p)) (at (m-rec₂ q)) = graph D₂ (at p) (at q)
  graph-m (m-rec D₁ D₂) (at (m-rec₂ p)) (at ε) = edge M.I p

  graph-m m-unit  input (at ε) = M.I
  graph-m m-base  input (at ε) = M.I
  graph-m m-arrow input (at ε) = M.I

  graph-m (m-inl D) env (at (m-inl q)) = graph-m D env (at q)
  graph-m (m-inl D) input (at (m-inl q)) = graph-m D input (at q) ∘ M.p₂ {1}
  graph-m (m-inl D) (at (m-inl p)) (at (m-inl q)) = graph-m D (at p) (at q)
  graph-m (m-inl D) (at (m-inl p)) (at ε) = edge-m (M.in₂ {1}) p
  graph-m (m-inl D) input (at ε) = M.in₁ {1} ∘ M.p₁ {1}

  graph-m (m-inr D) env (at (m-inr q)) = graph-m D env (at q)
  graph-m (m-inr D) input (at (m-inr q)) = graph-m D input (at q) ∘ M.p₂ {1}
  graph-m (m-inr D) (at (m-inr p)) (at (m-inr q)) = graph-m D (at p) (at q)
  graph-m (m-inr D) (at (m-inr p)) (at ε) = edge-m (M.in₂ {1}) p
  graph-m (m-inr D) input (at ε) = M.in₁ {1} ∘ M.p₁ {1}

  graph-m (m-pair D₁ D₂) env (at (m-pair₁ q)) = graph-m D₁ env (at q)
  graph-m (m-pair D₁ D₂) input (at (m-pair₁ q)) = graph-m D₁ input (at q) ∘ M.p₁ ∘ M.p₂ {1}
  graph-m (m-pair D₁ D₂) (at (m-pair₁ p)) (at (m-pair₁ q)) = graph-m D₁ (at p) (at q)
  graph-m (m-pair D₁ D₂) env (at (m-pair₂ q)) = graph-m D₂ env (at q)
  graph-m (m-pair D₁ D₂) input (at (m-pair₂ q)) = graph-m D₂ input (at q) ∘ M.p₂ ∘ M.p₂ {1}
  graph-m (m-pair D₁ D₂) (at (m-pair₂ p)) (at (m-pair₂ q)) = graph-m D₂ (at p) (at q)
  graph-m (m-pair D₁ D₂) (at (m-pair₁ p)) (at ε) = edge-m (M.in₂ {1} ∘ M.in₁) p
  graph-m (m-pair D₁ D₂) (at (m-pair₂ p)) (at ε) = edge-m (M.in₂ {1} ∘ M.in₂) p
  graph-m (m-pair D₁ D₂) input (at ε) = M.in₁ {1} ∘ M.p₁ {1}

  graph-m (m-mu {τ' = τ'} {w = w} D) env (at (m-mu q)) = graph-m D env (at q)
  graph-m (m-mu {τ' = τ'} {w = w} D) input (at (m-mu q)) =
    ccast (sym (width-subst (unfold₁-inst τ' _) w)) (graph-m D input (at q))
  graph-m (m-mu D) (at (m-mu p)) (at (m-mu q)) = graph-m D (at p) (at q)
  graph-m (m-mu {τ' = τ'} {w' = w'} D) (at (m-mu p)) (at ε) =
    edge-m (rcast (sym (width-subst (unfold₁-inst τ' _) w')) M.I) p

  graph-m D _ _ = M.εₘ
