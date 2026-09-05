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
-- a rule's derivation is, for each premise, either a vertex inside it or that premise's root, so the
-- labelling follows the graph's construction rule by rule.
module interaction.labelling {ℓ} (Sig : Signature ℓ) {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (ℐ : Interpretation S Sig) (ctrl-weight : Setoid.Carrier A)
  (let module S = CommutativeSemiring S) (+-idem : ∀ x → (x S.+ x) S.≈ x) where

open Signature Sig
open import Data.List.Relation.Unary.All using () renaming (All to Every)
open import language-syntax Sig hiding (_[_]) renaming (_,_ to _▸_)
open import language-operational.evaluation Sig S ℐ ctrl-weight hiding (Derivation)
open import interaction.graph S +-idem
open import interaction.dependence-graph Sig S ℐ ctrl-weight +-idem

data Node : Set ℓ where
  val : ∀ {τ : type 0} → Val τ → Node

node-width : Node → ℕ
node-width (val v) = width v

record Labelling (s : Derivation) : Set ℓ where
  field at : (p : Vertex s) → Σ[ x ∈ Node ] node-width x ≡ width-at s p

open Labelling public

lab₀ : ∀ {k b} → Labelling (node k b []ₗ)
lab₀ .at ()

lab₁ : ∀ {k b s} → Labelling s → (x : Node) → node-width x ≡ out-width s →
       Labelling (node k b (s ∷ₗ []ₗ))
lab₁ f x e .at (inj₁ p)    = f .at p
lab₁ f x e .at (inj₂ output) = x , e

lab₂ : ∀ {k b s₁ s₂} →
       Labelling s₁ → (x₁ : Node) → node-width x₁ ≡ out-width s₁ →
       Labelling s₂ → (x₂ : Node) → node-width x₂ ≡ out-width s₂ →
       Labelling (node k b (s₁ ∷ₗ s₂ ∷ₗ []ₗ))
lab₂ f₁ x₁ e₁ f₂ x₂ e₂ .at (inj₁ (inj₁ p))    = f₁ .at p
lab₂ f₁ x₁ e₁ f₂ x₂ e₂ .at (inj₁ (inj₂ output)) = x₁ , e₁
lab₂ f₁ x₁ e₁ f₂ x₂ e₂ .at (inj₂ (inj₁ p))    = f₂ .at p
lab₂ f₁ x₁ e₁ f₂ x₂ e₂ .at (inj₂ (inj₂ output)) = x₂ , e₂

lab₊ : ∀ {k b s t ts} → Labelling s → (x : Node) → node-width x ≡ out-width s →
       Labelling (node k b (t ∷ₗ ts)) →
       Labelling (node k b (s ∷ₗ t ∷ₗ ts))
lab₊ f x e g .at (inj₁ (inj₁ p))    = f .at p
lab₊ f x e g .at (inj₁ (inj₂ output)) = x , e
lab₊ f x e g .at (inj₂ q)           = g .at q

lab₃ : ∀ {k b s₁ s₂ s₃} →
       Labelling s₁ → (x₁ : Node) → node-width x₁ ≡ out-width s₁ →
       Labelling s₂ → (x₂ : Node) → node-width x₂ ≡ out-width s₂ →
       Labelling s₃ → (x₃ : Node) → node-width x₃ ≡ out-width s₃ →
       Labelling (node k b (s₁ ∷ₗ s₂ ∷ₗ s₃ ∷ₗ []ₗ))
lab₃ f₁ x₁ e₁ f₂ x₂ e₂ f₃ x₃ e₃ .at (inj₁ (inj₁ p))           = f₁ .at p
lab₃ f₁ x₁ e₁ f₂ x₂ e₂ f₃ x₃ e₃ .at (inj₁ (inj₂ output))        = x₁ , e₁
lab₃ f₁ x₁ e₁ f₂ x₂ e₂ f₃ x₃ e₃ .at (inj₂ (inj₁ (inj₁ p)))    = f₂ .at p
lab₃ f₁ x₁ e₁ f₂ x₂ e₂ f₃ x₃ e₃ .at (inj₂ (inj₁ (inj₂ output))) = x₂ , e₂
lab₃ f₁ x₁ e₁ f₂ x₂ e₂ f₃ x₃ e₃ .at (inj₂ (inj₂ (inj₁ p)))    = f₃ .at p
lab₃ f₁ x₁ e₁ f₂ x₂ e₂ f₃ x₃ e₃ .at (inj₂ (inj₂ (inj₂ output))) = x₃ , e₃

mutual
  label : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) →
          Labelling (deriv D)
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
  label (⇓-bop D) = label-premises D
  label (⇓-brel D) = label-premises D
  label (⇓-roll {v = v} D) = lab₁ (label D) (val v) refl
  label (⇓-fold {v = v} {u = u} D₁ D₂) =
    lab₂ (label D₁) (val v) refl (label-m D₂) (val u) refl

  label-premises : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
                   (D : γ , Ms ⇓s vs [ R ]) {k b} →
                   Labelling (node k b (derivs D))
  label-premises [] = lab₀
  label-premises (_∷_ {v = v} D₁ []) = lab₁ (label D₁) (val (const v)) refl
  label-premises (_∷_ {v = v} D₁ D₂@(_ ∷ _)) =
    lab₊ (label D₁) (val (const v)) refl (label-premises D₂)

  label-m : ∀ {Γ} {γ : Env Γ} {τ₀ σr s σ' v v' F} (D : Map γ {τ₀} {σr} s σ' v v' F) →
            Labelling (deriv-m D)
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
