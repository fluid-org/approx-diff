{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.List using (List) renaming (_∷_ to _∷ₗ_; [] to []ₗ)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Data.Sum using (inj₁; inj₂; [_,_])
open import Level using (0ℓ; _⊔_) renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import signature using (Signature)
open import signature.interpretation using (Interpretation)

-- The value each vertex of a dependence graph produced, its width the vertex's width. A vertex of
-- a rule's shape is, for each premise, either a vertex inside it or that premise's root, so the
-- labelling follows the graph's construction rule by rule.
module interaction.labelling {ℓ} (Sig : Signature ℓ) {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (ℐ : Interpretation S Sig) (ctrl-weight : Setoid.Carrier A)
  (let module S = CommutativeSemiring S) (+-idem : ∀ x → (x S.+ x) S.≈ x) where

open Signature Sig
open Interpretation ℐ
open import Data.List.Relation.Unary.All using () renaming (All to Every)
open import language-syntax Sig hiding (_[_]) renaming (_,_ to _▸_)
open import language-operational.evaluation Sig S ℐ ctrl-weight
open import interaction.graph S +-idem
open import interaction.dependence-graph Sig S ℐ ctrl-weight +-idem
open import matrix-embedding S using (𝔽)

data Node : Set ℓ where
  val  : ∀ {τ : type 0} → Val τ → Node
  vals : ∀ {is} → sort-vals is → Node

node-width : Node → ℕ
node-width (val v)       = width v
node-width (vals {is} _) = bases-width is

record Labelling (s : Shape) (o : Vertex s → SemiMod.Semimodule) : Set (ℓ ⊔ lsuc 0ℓ) where
  field at : (p : Vertex s) → Σ[ x ∈ Node ] 𝔽 (node-width x) ≡ o p

open Labelling public

lab₀ : ∀ {o} → Labelling (node []ₗ) o
lab₀ .at ()

lab₁ : ∀ {s o} {N₀ : SemiMod.Semimodule} → Labelling s o → (x : Node) → 𝔽 (node-width x) ≡ N₀ →
       Labelling (node (s ∷ₗ []ₗ)) [ o , (λ _ → N₀) ]
lab₁ f x e .at (inj₁ p)    = f .at p
lab₁ f x e .at (inj₂ root) = x , e

lab₂ : ∀ {s₁ o₁ s₂ o₂} {N₁ N₂ : SemiMod.Semimodule} →
       Labelling s₁ o₁ → (x₁ : Node) → 𝔽 (node-width x₁) ≡ N₁ →
       Labelling s₂ o₂ → (x₂ : Node) → 𝔽 (node-width x₂) ≡ N₂ →
       Labelling (node (s₁ ∷ₗ s₂ ∷ₗ []ₗ)) [ [ o₁ , (λ _ → N₁) ] , [ o₂ , (λ _ → N₂) ] ]
lab₂ f₁ x₁ e₁ f₂ x₂ e₂ .at (inj₁ (inj₁ p))    = f₁ .at p
lab₂ f₁ x₁ e₁ f₂ x₂ e₂ .at (inj₁ (inj₂ root)) = x₁ , e₁
lab₂ f₁ x₁ e₁ f₂ x₂ e₂ .at (inj₂ (inj₁ p))    = f₂ .at p
lab₂ f₁ x₁ e₁ f₂ x₂ e₂ .at (inj₂ (inj₂ root)) = x₂ , e₂

lab₃ : ∀ {s₁ o₁ s₂ o₂ s₃ o₃} {N₁ N₂ N₃ : SemiMod.Semimodule} →
       Labelling s₁ o₁ → (x₁ : Node) → 𝔽 (node-width x₁) ≡ N₁ →
       Labelling s₂ o₂ → (x₂ : Node) → 𝔽 (node-width x₂) ≡ N₂ →
       Labelling s₃ o₃ → (x₃ : Node) → 𝔽 (node-width x₃) ≡ N₃ →
       Labelling (node (s₁ ∷ₗ s₂ ∷ₗ s₃ ∷ₗ []ₗ))
                 [ [ o₁ , (λ _ → N₁) ] , [ [ o₂ , (λ _ → N₂) ] , [ o₃ , (λ _ → N₃) ] ] ]
lab₃ f₁ x₁ e₁ f₂ x₂ e₂ f₃ x₃ e₃ .at (inj₁ (inj₁ p))           = f₁ .at p
lab₃ f₁ x₁ e₁ f₂ x₂ e₂ f₃ x₃ e₃ .at (inj₁ (inj₂ root))        = x₁ , e₁
lab₃ f₁ x₁ e₁ f₂ x₂ e₂ f₃ x₃ e₃ .at (inj₂ (inj₁ (inj₁ p)))    = f₂ .at p
lab₃ f₁ x₁ e₁ f₂ x₂ e₂ f₃ x₃ e₃ .at (inj₂ (inj₁ (inj₂ root))) = x₂ , e₂
lab₃ f₁ x₁ e₁ f₂ x₂ e₂ f₃ x₃ e₃ .at (inj₂ (inj₂ (inj₁ p)))    = f₃ .at p
lab₃ f₁ x₁ e₁ f₂ x₂ e₂ f₃ x₃ e₃ .at (inj₂ (inj₂ (inj₂ root))) = x₃ , e₃

mutual
  label : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) →
          Labelling (Graph.shape (graph D)) (Graph.object (graph D))
  label (⇓-var x) = lab₀
  label ⇓-unit = lab₀
  label ⇓-lam = lab₀
  label (⇓-inl {v = v} D) = lab₁ (label D) (val v) refl
  label (⇓-inr {v = v} D) = lab₁ (label D) (val v) refl
  label (⇓-case-l {τ₂ = τ₂} {v = v} {u = u} D₁ D₂) =
    lab₂ (label D₁) (val (inl {τ₂ = τ₂} v)) refl (label D₂) (val u) refl
  label (⇓-case-r {τ₁ = τ₁} {v = v} {u = u} D₁ D₂) =
    lab₂ (label D₁) (val (inr {τ₁ = τ₁} v)) refl (label D₂) (val u) refl
  label (⇓-pair {v = v} {u = u} D₁ D₂) =
    lab₂ (label D₁) (val v) refl (label D₂) (val u) refl
  label (⇓-fst {v = v} {u = u} D) = lab₁ (label D) (val (pair v u)) refl
  label (⇓-snd {v = v} {u = u} D) = lab₁ (label D) (val (pair v u)) refl
  label (⇓-app {γ' = γ'} {t' = t'} {v = v} {u = u} D₁ D₂ D₃) =
    lab₃ (label D₁) (val (clo γ' t')) refl (label D₂) (val v) refl (label D₃) (val u) refl
  label (⇓-bop {is = is} {vs = vs} D) = lab₁ (label-s D) (vals {is} vs) refl
  label (⇓-brel {is = is} {vs = vs} D) = lab₁ (label-s D) (vals {is} vs) refl
  label (⇓-roll {v = v} D) = lab₁ (label D) (val v) refl
  label (⇓-fold {v = v} {u = u} D₁ D₂) =
    lab₂ (label D₁) (val v) refl (label-m D₂) (val u) refl

  label-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
            (D : γ , Ms ⇓s vs [ R ]) → Labelling (Graph.shape (graph-s D)) (Graph.object (graph-s D))
  label-s [] = lab₀
  label-s (_∷_ {is = is} {v = v} {vs = vs} D₁ D₂) =
    lab₂ (label D₁) (val (const v)) refl (label-s D₂) (vals {is} vs) refl

  label-m : ∀ {Γ} {γ : Env Γ} {τ₀ σr s σ' v v' F} (D : Map γ {τ₀} {σr} s σ' v v' F) →
            Labelling (Graph.shape (graph-m D)) (Graph.object (graph-m D))
  label-m (m-rec {w' = w'} {u = u} D₁ D₂) =
    lab₂ (label-m D₁) (val w') refl (label D₂) (val u) refl
  label-m m-unit = lab₀
  label-m m-base = lab₀
  label-m m-arrow = lab₀
  label-m (m-inl {v' = v'} D) = lab₁ (label-m D) (val v') refl
  label-m (m-inr {v' = v'} D) = lab₁ (label-m D) (val v') refl
  label-m (m-pair {v' = v'} {u' = u'} D₁ D₂) =
    lab₂ (label-m D₁) (val v') refl (label-m D₂) (val u') refl
  label-m (m-mu {w' = w'} D) = lab₁ (label-m D) (val w') refl
