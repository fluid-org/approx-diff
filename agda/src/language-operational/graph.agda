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

-- Dependence graphs over a derivation: a graph is its entry function, giving for each pair of
-- vertices a matrix between their widths, the zero matrix meaning no edge. The graph judgement is a
-- function from derivations to graphs, one clause group per rule; unions are pointwise sums
-- realised by a single final zero clause, prefixing is reindexing by path constructors, and
-- rewiring redistributes a premise's env column through the biproduct injections.
module language-operational.graph {ℓ} (Sig : Signature ℓ) (𝒫 : Primitives two.semiring Sig) where

open Signature Sig
open Primitives 𝒫
open _⇒ₛ_ using (func)
open import language-syntax Sig renaming (_,_ to _▸_)
open import type-substitution Sig using (unfold₁; unfold₁-inst)
open import language-operational.evaluation Sig 𝒫
open import language-operational.path Sig 𝒫

private
  module M = matrix.Mat two.semiring

open import categories using (Category)
open Category M.cat using (_⇒_)

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

-- The single-edge graph out of a premise's root, read as its column of entries at each source
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
  graph (⇓-inl D) (at (inl p)) (at ε) = edge M.I p

  graph (⇓-inr D) env       (at (inr q)) = graph D env (at q)
  graph (⇓-inr D) (at (inr p)) (at (inr q)) = graph D (at p) (at q)
  graph (⇓-inr D) (at (inr p)) (at ε) = edge M.I p

  graph (⇓-case-l D₁ D₂) env (at (case-l₁ q)) = graph D₁ env (at q)
  graph (⇓-case-l D₁ D₂) (at (case-l₁ p)) (at (case-l₁ q)) = graph D₁ (at p) (at q)
  graph (⇓-case-l D₁ D₂) env (at (case-l₂ q)) = graph D₂ env (at q) M.∘ M.in₁
  graph (⇓-case-l D₁ D₂) (at (case-l₁ p)) (at (case-l₂ q)) = edge (graph D₂ env (at q) M.∘ M.in₂) p
  graph (⇓-case-l D₁ D₂) (at (case-l₂ p)) (at (case-l₂ q)) = graph D₂ (at p) (at q)
  graph (⇓-case-l D₁ D₂) (at (case-l₂ p)) (at ε) = edge M.I p

  graph (⇓-case-r D₁ D₂) env (at (case-r₁ q)) = graph D₁ env (at q)
  graph (⇓-case-r D₁ D₂) (at (case-r₁ p)) (at (case-r₁ q)) = graph D₁ (at p) (at q)
  graph (⇓-case-r D₁ D₂) env (at (case-r₂ q)) = graph D₂ env (at q) M.∘ M.in₁
  graph (⇓-case-r D₁ D₂) (at (case-r₁ p)) (at (case-r₂ q)) = edge (graph D₂ env (at q) M.∘ M.in₂) p
  graph (⇓-case-r D₁ D₂) (at (case-r₂ p)) (at (case-r₂ q)) = graph D₂ (at p) (at q)
  graph (⇓-case-r D₁ D₂) (at (case-r₂ p)) (at ε) = edge M.I p

  graph (⇓-pair D₁ D₂) env (at (pair₁ q)) = graph D₁ env (at q)
  graph (⇓-pair D₁ D₂) (at (pair₁ p)) (at (pair₁ q)) = graph D₁ (at p) (at q)
  graph (⇓-pair D₁ D₂) env (at (pair₂ q)) = graph D₂ env (at q)
  graph (⇓-pair D₁ D₂) (at (pair₂ p)) (at (pair₂ q)) = graph D₂ (at p) (at q)
  graph (⇓-pair D₁ D₂) (at (pair₁ p)) (at ε) = edge M.in₁ p
  graph (⇓-pair D₁ D₂) (at (pair₂ p)) (at ε) = edge M.in₂ p

  graph (⇓-fst D) env (at (fst q)) = graph D env (at q)
  graph (⇓-fst D) (at (fst p)) (at (fst q)) = graph D (at p) (at q)
  graph (⇓-fst D) (at (fst p)) (at ε) = edge M.p₁ p

  graph (⇓-snd D) env (at (snd q)) = graph D env (at q)
  graph (⇓-snd D) (at (snd p)) (at (snd q)) = graph D (at p) (at q)
  graph (⇓-snd D) (at (snd p)) (at ε) = edge M.p₂ p

  graph ⇓-lam env (at ε) = M.I

  graph (⇓-app D₁ D₂ D₃) env (at (app₁ q)) = graph D₁ env (at q)
  graph (⇓-app D₁ D₂ D₃) (at (app₁ p)) (at (app₁ q)) = graph D₁ (at p) (at q)
  graph (⇓-app D₁ D₂ D₃) env (at (app₂ q)) = graph D₂ env (at q)
  graph (⇓-app D₁ D₂ D₃) (at (app₂ p)) (at (app₂ q)) = graph D₂ (at p) (at q)
  graph (⇓-app D₁ D₂ D₃) (at (app₁ p)) (at (app₃ q)) = edge (graph D₃ env (at q) M.∘ M.in₁) p
  graph (⇓-app D₁ D₂ D₃) (at (app₂ p)) (at (app₃ q)) = edge (graph D₃ env (at q) M.∘ M.in₂) p
  graph (⇓-app D₁ D₂ D₃) (at (app₃ p)) (at (app₃ q)) = graph D₃ (at p) (at q)
  graph (⇓-app D₁ D₂ D₃) (at (app₃ p)) (at ε) = edge M.I p

  graph (⇓-bop {ω = ω} {vs = vs} D) env (at (bop q)) = graphS D env (at q)
  graph (⇓-bop D) (at (bop p)) (at (bop q)) = graphS D (at p) (at q)
  graph (⇓-bop {ω = ω} {vs = vs} D) (at (bop p)) (at ε) = edge-s (op-deps ω .func vs) p

  graph (⇓-brel D) env (at (brel q)) = graphS D env (at q)
  graph (⇓-brel D) (at (brel p)) (at (brel q)) = graphS D (at p) (at q)

  graph (⇓-roll D) env (at (roll q)) = graph D env (at q)
  graph (⇓-roll D) (at (roll p)) (at (roll q)) = graph D (at p) (at q)
  graph (⇓-roll D) (at (roll p)) (at ε) = edge M.I p

  graph (⇓-fold D₁ D₂) env (at (fold₁ q)) = graph D₁ env (at q)
  graph (⇓-fold D₁ D₂) (at (fold₁ p)) (at (fold₁ q)) = graph D₁ (at p) (at q)
  graph (⇓-fold D₁ D₂) env (at (fold₂ q)) = graphM D₂ env (at q)
  graph (⇓-fold D₁ D₂) (at (fold₁ p)) (at (fold₂ q)) = edge (graphM D₂ input (at q)) p
  graph (⇓-fold D₁ D₂) (at (fold₂ p)) (at (fold₂ q)) = graphM D₂ (at p) (at q)
  graph (⇓-fold D₁ D₂) (at (fold₂ p)) (at ε) = edge-m M.I p

  graph D _ _ = M.εₘ

  graphS : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
           (D : γ , Ms ⇓s vs [ R ]) → GraphS D
  graphS (D₁ ∷ D₂) env (at (hd q)) = graph D₁ env (at q)
  graphS (D₁ ∷ D₂) (at (hd p)) (at (hd q)) = graph D₁ (at p) (at q)
  graphS (D₁ ∷ D₂) env (at (tl q)) = graphS D₂ env (at q)
  graphS (D₁ ∷ D₂) (at (tl p)) (at (tl q)) = graphS D₂ (at p) (at q)
  graphS (D₁ ∷ D₂) (at (hd p)) (at ε) = edge M.in₁ p
  graphS (D₁ ∷ D₂) (at (tl p)) (at ε) = edge-s M.in₂ p
  graphS D _ _ = M.εₘ

  graphM : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
           {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
      {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
           (D : Map γ s σ' v R v' R') → GraphM D
  graphM (m-rec D₁ D₂) env (at (m-rec₁ q)) = graphM D₁ env (at q)
  graphM (m-rec D₁ D₂) input (at (m-rec₁ q)) = graphM D₁ input (at q)
  graphM (m-rec D₁ D₂) (at (m-rec₁ p)) (at (m-rec₁ q)) = graphM D₁ (at p) (at q)
  graphM (m-rec D₁ D₂) env (at (m-rec₂ q)) = graph D₂ env (at q) M.∘ M.in₁
  graphM (m-rec D₁ D₂) (at (m-rec₁ p)) (at (m-rec₂ q)) = edge-m (graph D₂ env (at q) M.∘ M.in₂) p
  graphM (m-rec D₁ D₂) (at (m-rec₂ p)) (at (m-rec₂ q)) = graph D₂ (at p) (at q)
  graphM (m-rec D₁ D₂) (at (m-rec₂ p)) (at ε) = edge M.I p

  graphM m-unit  input (at ε) = M.I
  graphM m-base  input (at ε) = M.I
  graphM m-arrow input (at ε) = M.I

  graphM (m-inl D) env (at (m-inl q)) = graphM D env (at q)
  graphM (m-inl D) input (at (m-inl q)) = graphM D input (at q)
  graphM (m-inl D) (at (m-inl p)) (at (m-inl q)) = graphM D (at p) (at q)
  graphM (m-inl D) (at (m-inl p)) (at ε) = edge-m M.I p

  graphM (m-inr D) env (at (m-inr q)) = graphM D env (at q)
  graphM (m-inr D) input (at (m-inr q)) = graphM D input (at q)
  graphM (m-inr D) (at (m-inr p)) (at (m-inr q)) = graphM D (at p) (at q)
  graphM (m-inr D) (at (m-inr p)) (at ε) = edge-m M.I p

  graphM (m-pair D₁ D₂) env (at (m-pair₁ q)) = graphM D₁ env (at q)
  graphM (m-pair D₁ D₂) input (at (m-pair₁ q)) = graphM D₁ input (at q) M.∘ M.p₁
  graphM (m-pair D₁ D₂) (at (m-pair₁ p)) (at (m-pair₁ q)) = graphM D₁ (at p) (at q)
  graphM (m-pair D₁ D₂) env (at (m-pair₂ q)) = graphM D₂ env (at q)
  graphM (m-pair D₁ D₂) input (at (m-pair₂ q)) = graphM D₂ input (at q) M.∘ M.p₂
  graphM (m-pair D₁ D₂) (at (m-pair₂ p)) (at (m-pair₂ q)) = graphM D₂ (at p) (at q)
  graphM (m-pair D₁ D₂) (at (m-pair₁ p)) (at ε) = edge-m M.in₁ p
  graphM (m-pair D₁ D₂) (at (m-pair₂ p)) (at ε) = edge-m M.in₂ p

  graphM (m-mu {τ' = τ'} {w = w} D) env (at (m-mu q)) = graphM D env (at q)
  graphM (m-mu {τ' = τ'} {w = w} D) input (at (m-mu q)) =
    ccast (sym (width-subst (unfold₁-inst τ' _) w)) (graphM D input (at q))
  graphM (m-mu D) (at (m-mu p)) (at (m-mu q)) = graphM D (at p) (at q)
  graphM (m-mu {τ' = τ'} {w' = w'} D) (at (m-mu p)) (at ε) =
    edge-m (rcast (sym (width-subst (unfold₁-inst τ' _) w')) M.I) p

  graphM D _ _ = M.εₘ
