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

-- Dependence graphs over a derivation (paper, section 3): a graph is its entry function, giving for
-- each pair of vertices a matrix between their widths, the zero matrix meaning no edge. The graph
-- judgement of fig. 9 becomes a function from derivations to graphs, one clause group per rule;
-- unions are pointwise sums realised by a single final zero clause, prefixing is reindexing by path
-- constructors, and rewiring redistributes a premise's env column through the biproduct injections.
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
             (Ds : γ , Ms ⇓s vs [ R ]) : Set ℓ where
  env : VertexS Ds
  at  : PathS Ds → VertexS Ds

-- A fold-action derivation has a second source alongside env: the input value being folded over.
-- The fold rule wires it to the root of its first premise, the way a case branch wires its
-- environment extension to the scrutinee root.
data VertexM {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
             {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
             {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
             (Dm : Map γ s σ' v R v' R') : Set ℓ where
  env   : VertexM Dm
  input : VertexM Dm
  at    : PathM Dm → VertexM Dm

vw : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} → Vertex D → ℕ
vw {γ = γ} env = width-env γ
vw (at p)      = width-at p

vws : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
      {Ds : γ , Ms ⇓s vs [ R ]} → VertexS Ds → ℕ
vws {γ = γ} env = width-env γ
vws (at p)      = width-at-s p

vwm : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
      {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
      {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
      {Dm : Map γ s σ' v R v' R'} → VertexM Dm → ℕ
vwm {γ = γ} env     = width-env γ
vwm {v = v} input   = width v
vwm (at p)          = width-at-m p

Graph : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} → γ , t ⇓ v [ R ] → Set ℓ
Graph D = (x y : Vertex D) → M.Matrix (vw y) (vw x)

GraphS : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R} →
         γ , Ms ⇓s vs [ R ] → Set ℓ
GraphS Ds = (x y : VertexS Ds) → M.Matrix (vws y) (vws x)

GraphM : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
         {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
      {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'} →
         Map γ s σ' v R v' R' → Set ℓ
GraphM Dm = (x y : VertexM Dm) → M.Matrix (vwm y) (vwm x)

-- Cast a matrix along equalities of its row and column dimensions.
rcast : ∀ {m m' n} → m ≡ m' → M.Matrix m n → M.Matrix m' n
rcast refl R = R

ccast : ∀ {m n n'} → n ≡ n' → M.Matrix m n → M.Matrix m n'
ccast refl R = R

-- The given matrix at the root path, zero elsewhere. Defined generically because case-splitting a
-- premise's path type gets stuck when the premise's indices are function-headed (e.g. a scrutinee
-- required to evaluate to inl v).
at-root : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} {m} →
          M.Matrix m (width v) → (p : Path D) → M.Matrix m (width-at p)
at-root R ε = R
at-root R _ = M.εₘ

at-root-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
            {Ds : γ , Ms ⇓s vs [ R ]} {m} →
            M.Matrix m (bases-width is) → (p : PathS Ds) → M.Matrix m (width-at-s p)
at-root-s R ε = R
at-root-s R _ = M.εₘ

at-root-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
            {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
      {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
            {Dm : Map γ s σ' v R v' R'} {m} →
            M.Matrix m (width v') → (p : PathM Dm) → M.Matrix m (width-at-m p)
at-root-m R ε = R
at-root-m R _ = M.εₘ

mutual
  graph : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) → Graph D
  graph (⇓-var {γ = γ} x) env (at ε) = proj-var x γ

  graph (⇓-inl D) env       (at (inl q)) = graph D env (at q)
  graph (⇓-inl D) (at (inl p)) (at (inl q)) = graph D (at p) (at q)
  graph (⇓-inl D) (at (inl p)) (at ε) = at-root M.I p

  graph (⇓-inr D) env       (at (inr q)) = graph D env (at q)
  graph (⇓-inr D) (at (inr p)) (at (inr q)) = graph D (at p) (at q)
  graph (⇓-inr D) (at (inr p)) (at ε) = at-root M.I p

  graph (⇓-case-l Ds D₁) env (at (case-l₁ q)) = graph Ds env (at q)
  graph (⇓-case-l Ds D₁) (at (case-l₁ p)) (at (case-l₁ q)) = graph Ds (at p) (at q)
  graph (⇓-case-l Ds D₁) env (at (case-l₂ q)) = graph D₁ env (at q) M.∘ M.in₁
  graph (⇓-case-l Ds D₁) (at (case-l₁ p)) (at (case-l₂ q)) = at-root (graph D₁ env (at q) M.∘ M.in₂) p
  graph (⇓-case-l Ds D₁) (at (case-l₂ p)) (at (case-l₂ q)) = graph D₁ (at p) (at q)
  graph (⇓-case-l Ds D₁) (at (case-l₂ p)) (at ε) = at-root M.I p

  graph (⇓-case-r Ds D₂) env (at (case-r₁ q)) = graph Ds env (at q)
  graph (⇓-case-r Ds D₂) (at (case-r₁ p)) (at (case-r₁ q)) = graph Ds (at p) (at q)
  graph (⇓-case-r Ds D₂) env (at (case-r₂ q)) = graph D₂ env (at q) M.∘ M.in₁
  graph (⇓-case-r Ds D₂) (at (case-r₁ p)) (at (case-r₂ q)) = at-root (graph D₂ env (at q) M.∘ M.in₂) p
  graph (⇓-case-r Ds D₂) (at (case-r₂ p)) (at (case-r₂ q)) = graph D₂ (at p) (at q)
  graph (⇓-case-r Ds D₂) (at (case-r₂ p)) (at ε) = at-root M.I p

  graph (⇓-pair Ds Dt) env (at (pair₁ q)) = graph Ds env (at q)
  graph (⇓-pair Ds Dt) (at (pair₁ p)) (at (pair₁ q)) = graph Ds (at p) (at q)
  graph (⇓-pair Ds Dt) env (at (pair₂ q)) = graph Dt env (at q)
  graph (⇓-pair Ds Dt) (at (pair₂ p)) (at (pair₂ q)) = graph Dt (at p) (at q)
  graph (⇓-pair Ds Dt) (at (pair₁ p)) (at ε) = at-root M.in₁ p
  graph (⇓-pair Ds Dt) (at (pair₂ p)) (at ε) = at-root M.in₂ p

  graph (⇓-fst D) env (at (fst q)) = graph D env (at q)
  graph (⇓-fst D) (at (fst p)) (at (fst q)) = graph D (at p) (at q)
  graph (⇓-fst D) (at (fst p)) (at ε) = at-root M.p₁ p

  graph (⇓-snd D) env (at (snd q)) = graph D env (at q)
  graph (⇓-snd D) (at (snd p)) (at (snd q)) = graph D (at p) (at q)
  graph (⇓-snd D) (at (snd p)) (at ε) = at-root M.p₂ p

  graph ⇓-lam env (at ε) = M.I

  graph (⇓-app Ds Dt Db) env (at (app₁ q)) = graph Ds env (at q)
  graph (⇓-app Ds Dt Db) (at (app₁ p)) (at (app₁ q)) = graph Ds (at p) (at q)
  graph (⇓-app Ds Dt Db) env (at (app₂ q)) = graph Dt env (at q)
  graph (⇓-app Ds Dt Db) (at (app₂ p)) (at (app₂ q)) = graph Dt (at p) (at q)
  graph (⇓-app Ds Dt Db) (at (app₁ p)) (at (app₃ q)) = at-root (graph Db env (at q) M.∘ M.in₁) p
  graph (⇓-app Ds Dt Db) (at (app₂ p)) (at (app₃ q)) = at-root (graph Db env (at q) M.∘ M.in₂) p
  graph (⇓-app Ds Dt Db) (at (app₃ p)) (at (app₃ q)) = graph Db (at p) (at q)
  graph (⇓-app Ds Dt Db) (at (app₃ p)) (at ε) = at-root M.I p

  graph (⇓-bop {ω = ω} {vs = vs} Ds) env (at (bop q)) = graphS Ds env (at q)
  graph (⇓-bop Ds) (at (bop p)) (at (bop q)) = graphS Ds (at p) (at q)
  graph (⇓-bop {ω = ω} {vs = vs} Ds) (at (bop p)) (at ε) = at-root-s (op-deps ω .func vs) p

  graph (⇓-brel Ds) env (at (brel q)) = graphS Ds env (at q)
  graph (⇓-brel Ds) (at (brel p)) (at (brel q)) = graphS Ds (at p) (at q)

  graph (⇓-roll D) env (at (roll q)) = graph D env (at q)
  graph (⇓-roll D) (at (roll p)) (at (roll q)) = graph D (at p) (at q)
  graph (⇓-roll D) (at (roll p)) (at ε) = at-root M.I p

  graph (⇓-fold Dt Dm) env (at (fold₁ q)) = graph Dt env (at q)
  graph (⇓-fold Dt Dm) (at (fold₁ p)) (at (fold₁ q)) = graph Dt (at p) (at q)
  graph (⇓-fold Dt Dm) env (at (fold₂ q)) = graphM Dm env (at q)
  graph (⇓-fold Dt Dm) (at (fold₁ p)) (at (fold₂ q)) = at-root (graphM Dm input (at q)) p
  graph (⇓-fold Dt Dm) (at (fold₂ p)) (at (fold₂ q)) = graphM Dm (at p) (at q)
  graph (⇓-fold Dt Dm) (at (fold₂ p)) (at ε) = at-root-m M.I p

  graph D _ _ = M.εₘ

  graphS : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
           (Ds : γ , Ms ⇓s vs [ R ]) → GraphS Ds
  graphS (D ∷ Ds) env (at (hd q)) = graph D env (at q)
  graphS (D ∷ Ds) (at (hd p)) (at (hd q)) = graph D (at p) (at q)
  graphS (D ∷ Ds) env (at (tl q)) = graphS Ds env (at q)
  graphS (D ∷ Ds) (at (tl p)) (at (tl q)) = graphS Ds (at p) (at q)
  graphS (D ∷ Ds) (at (hd p)) (at ε) = at-root M.in₁ p
  graphS (D ∷ Ds) (at (tl p)) (at ε) = at-root-s M.in₂ p
  graphS Ds _ _ = M.εₘ

  graphM : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
           {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
      {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
           (Dm : Map γ s σ' v R v' R') → GraphM Dm
  graphM (m-rec Dm De) env (at (m-rec₁ q)) = graphM Dm env (at q)
  graphM (m-rec Dm De) input (at (m-rec₁ q)) = graphM Dm input (at q)
  graphM (m-rec Dm De) (at (m-rec₁ p)) (at (m-rec₁ q)) = graphM Dm (at p) (at q)
  graphM (m-rec Dm De) env (at (m-rec₂ q)) = graph De env (at q) M.∘ M.in₁
  graphM (m-rec Dm De) (at (m-rec₁ p)) (at (m-rec₂ q)) = at-root-m (graph De env (at q) M.∘ M.in₂) p
  graphM (m-rec Dm De) (at (m-rec₂ p)) (at (m-rec₂ q)) = graph De (at p) (at q)
  graphM (m-rec Dm De) (at (m-rec₂ p)) (at ε) = at-root M.I p

  graphM m-unit  input (at ε) = M.I
  graphM m-base  input (at ε) = M.I
  graphM m-arrow input (at ε) = M.I

  graphM (m-inl Dm) env (at (m-inl q)) = graphM Dm env (at q)
  graphM (m-inl Dm) input (at (m-inl q)) = graphM Dm input (at q)
  graphM (m-inl Dm) (at (m-inl p)) (at (m-inl q)) = graphM Dm (at p) (at q)
  graphM (m-inl Dm) (at (m-inl p)) (at ε) = at-root-m M.I p

  graphM (m-inr Dm) env (at (m-inr q)) = graphM Dm env (at q)
  graphM (m-inr Dm) input (at (m-inr q)) = graphM Dm input (at q)
  graphM (m-inr Dm) (at (m-inr p)) (at (m-inr q)) = graphM Dm (at p) (at q)
  graphM (m-inr Dm) (at (m-inr p)) (at ε) = at-root-m M.I p

  graphM (m-pair Dm Dm') env (at (m-pair₁ q)) = graphM Dm env (at q)
  graphM (m-pair Dm Dm') input (at (m-pair₁ q)) = graphM Dm input (at q) M.∘ M.p₁
  graphM (m-pair Dm Dm') (at (m-pair₁ p)) (at (m-pair₁ q)) = graphM Dm (at p) (at q)
  graphM (m-pair Dm Dm') env (at (m-pair₂ q)) = graphM Dm' env (at q)
  graphM (m-pair Dm Dm') input (at (m-pair₂ q)) = graphM Dm' input (at q) M.∘ M.p₂
  graphM (m-pair Dm Dm') (at (m-pair₂ p)) (at (m-pair₂ q)) = graphM Dm' (at p) (at q)
  graphM (m-pair Dm Dm') (at (m-pair₁ p)) (at ε) = at-root-m M.in₁ p
  graphM (m-pair Dm Dm') (at (m-pair₂ p)) (at ε) = at-root-m M.in₂ p

  graphM (m-mu {τ' = τ'} {w = w} Dm) env (at (m-mu q)) = graphM Dm env (at q)
  graphM (m-mu {τ' = τ'} {w = w} Dm) input (at (m-mu q)) =
    ccast (sym (width-subst (unfold₁-inst τ' _) w)) (graphM Dm input (at q))
  graphM (m-mu Dm) (at (m-mu p)) (at (m-mu q)) = graphM Dm (at p) (at q)
  graphM (m-mu {τ' = τ'} {w' = w'} Dm) (at (m-mu p)) (at ε) =
    at-root-m (rcast (sym (width-subst (unfold₁-inst τ' _) w')) M.I) p

  graphM Dm _ _ = M.εₘ
