{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.List using (List) renaming (_∷_ to _∷ₗ_; [] to []ₗ)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Data.Sum using (inj₁; inj₂; [_,_])
open import Level using (0ℓ; _⊔_) renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import prop-setoid using (Setoid) renaming (_⇒_ to _⇒ₛ_)
open import commutative-semiring using (CommutativeSemiring)
open import signature using (Signature)
open import signature.interpretation using (Interpretation)
import sd-semimodule-primitives

-- The value each vertex of a dependence graph produced, its width the vertex's width. A vertex of
-- a rule's derivation is, for each premise, either a vertex inside it or that premise's root, so the
-- labelling follows the graph's construction rule by rule.
module interaction.labelling {ℓ} (Sig : Signature ℓ) {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (ℐ : Interpretation S Sig) (ctrl-weight : Setoid.Carrier A)
  (let module S = CommutativeSemiring S) (+-idem : ∀ x → (x S.+ x) S.≈ x) where

open Signature Sig
open Interpretation ℐ
open _⇒ₛ_ using (func)
open import Data.List.Relation.Unary.All using () renaming (All to Every)
open import language-syntax Sig hiding (_[_]) renaming (_,_ to _▸_)
open import language-operational.evaluation Sig S ℐ ctrl-weight hiding (Derivation)
open import interaction.graph S +-idem
open import interaction.dependence-graph Sig S ℐ ctrl-weight +-idem
open import matrix-embedding S using (𝔽)
open import categories using (Category)
open Category SemiMod.cat using (_⇒_; _∘_)

private
  module SDP = sd-semimodule-primitives S
open SDP.interp-deps Sig ℐ using (op-dep)

data Node : Set ℓ where
  val : ∀ {τ : type 0} → Val τ → Node

node-width : Node → ℕ
node-width (val v) = width v

record Labelling (s : Derivation) (w : Vertex s → ℕ) : Set ℓ where
  field at : (p : Vertex s) → Σ[ x ∈ Node ] node-width x ≡ w p

open Labelling public

lab₀ : ∀ {w} → Labelling (node []ₗ) w
lab₀ .at ()

lab₁ : ∀ {s w} {k : ℕ} → Labelling s w → (x : Node) → node-width x ≡ k →
       Labelling (node (s ∷ₗ []ₗ)) [ w , (λ _ → k) ]
lab₁ f x e .at (inj₁ p)    = f .at p
lab₁ f x e .at (inj₂ output) = x , e

lab₂ : ∀ {s₁ w₁ s₂ w₂} {k₁ k₂ : ℕ} →
       Labelling s₁ w₁ → (x₁ : Node) → node-width x₁ ≡ k₁ →
       Labelling s₂ w₂ → (x₂ : Node) → node-width x₂ ≡ k₂ →
       Labelling (node (s₁ ∷ₗ s₂ ∷ₗ []ₗ)) [ [ w₁ , (λ _ → k₁) ] , [ w₂ , (λ _ → k₂) ] ]
lab₂ f₁ x₁ e₁ f₂ x₂ e₂ .at (inj₁ (inj₁ p))    = f₁ .at p
lab₂ f₁ x₁ e₁ f₂ x₂ e₂ .at (inj₁ (inj₂ output)) = x₁ , e₁
lab₂ f₁ x₁ e₁ f₂ x₂ e₂ .at (inj₂ (inj₁ p))    = f₂ .at p
lab₂ f₁ x₁ e₁ f₂ x₂ e₂ .at (inj₂ (inj₂ output)) = x₂ , e₂

lab₊ : ∀ {s w t ts wts} {k : ℕ} → Labelling s w → (x : Node) → node-width x ≡ k →
       Labelling (node (t ∷ₗ ts)) wts →
       Labelling (node (s ∷ₗ t ∷ₗ ts)) [ [ w , (λ _ → k) ] , wts ]
lab₊ f x e g .at (inj₁ (inj₁ p))    = f .at p
lab₊ f x e g .at (inj₁ (inj₂ output)) = x , e
lab₊ f x e g .at (inj₂ q)           = g .at q

lab₃ : ∀ {s₁ w₁ s₂ w₂ s₃ w₃} {k₁ k₂ k₃ : ℕ} →
       Labelling s₁ w₁ → (x₁ : Node) → node-width x₁ ≡ k₁ →
       Labelling s₂ w₂ → (x₂ : Node) → node-width x₂ ≡ k₂ →
       Labelling s₃ w₃ → (x₃ : Node) → node-width x₃ ≡ k₃ →
       Labelling (node (s₁ ∷ₗ s₂ ∷ₗ s₃ ∷ₗ []ₗ))
                 [ [ w₁ , (λ _ → k₁) ] , [ [ w₂ , (λ _ → k₂) ] , [ w₃ , (λ _ → k₃) ] ] ]
lab₃ f₁ x₁ e₁ f₂ x₂ e₂ f₃ x₃ e₃ .at (inj₁ (inj₁ p))           = f₁ .at p
lab₃ f₁ x₁ e₁ f₂ x₂ e₂ f₃ x₃ e₃ .at (inj₁ (inj₂ output))        = x₁ , e₁
lab₃ f₁ x₁ e₁ f₂ x₂ e₂ f₃ x₃ e₃ .at (inj₂ (inj₁ (inj₁ p)))    = f₂ .at p
lab₃ f₁ x₁ e₁ f₂ x₂ e₂ f₃ x₃ e₃ .at (inj₂ (inj₁ (inj₂ output))) = x₂ , e₂
lab₃ f₁ x₁ e₁ f₂ x₂ e₂ f₃ x₃ e₃ .at (inj₂ (inj₂ (inj₁ p)))    = f₃ .at p
lab₃ f₁ x₁ e₁ f₂ x₂ e₂ f₃ x₃ e₃ .at (inj₂ (inj₂ (inj₂ output))) = x₃ , e₃

mutual
  label : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) →
          Labelling (Graph.D (graph D)) (Graph.width (graph D))
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
  label (⇓-bop {ω = ω} {vs = vs} D) = label-premises D (op-dep ω vs)
  label (⇓-brel {ω = ω} {vs = vs} D) = label-premises D (brel-deps ω vs (rel-pred ω .func vs))
  label (⇓-roll {v = v} D) = lab₁ (label D) (val v) refl
  label (⇓-fold {v = v} {u = u} D₁ D₂) =
    lab₂ (label D₁) (val v) refl (label-m D₂) (val u) refl

  label-premises : ∀ {Γ is n} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
                   (D : γ , Ms ⇓s vs [ R ]) (u : 𝔽 (bases-width is) ⇒ 𝔽 n) →
                   Labelling (node (Ruleₛ.Ds (premises D u))) (Ruleₛ.widths (premises D u))
  label-premises [] u = lab₀
  label-premises (_∷_ {v = v} D₁ []) u = lab₁ (label D₁) (val (const v)) refl
  label-premises (_∷_ {is = is} {v = v} D₁ D₂@(_ ∷ _)) u =
    lab₊ (label D₁) (val (const v)) refl
         (label-premises D₂ (u ∘ in₂ {width (const v)} {bases-width is}))

  label-m : ∀ {Γ} {γ : Env Γ} {τ₀ σr s σ' v v' F} (D : Map γ {τ₀} {σr} s σ' v v' F) →
            Labelling (Graph.D (graph-m D)) (Graph.width (graph-m D))
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
