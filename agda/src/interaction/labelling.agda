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

record Labelling (D : Derivation) : Set ℓ where
  field at : (p : Path D) → Σ[ x ∈ Node ] node-width x ≡ width-at D p

open Labelling public

lab₀ : ∀ {m k b} (x : Node) → node-width x ≡ k → Labelling (node m k b []ₗ)
lab₀ x e .at ε = x , e
lab₀ x e .at (into () _)

lab₁ : ∀ {m k b D} → Labelling D → (x : Node) → node-width x ≡ k → Labelling (node m k b (D ∷ₗ []ₗ))
lab₁ f x e .at ε             = x , e
lab₁ f x e .at (into here p) = f .at p
lab₁ f x e .at (into (there ()) _)

lab₂ : ∀ {m k b D₁ D₂} → Labelling D₁ → Labelling D₂ → (x : Node) → node-width x ≡ k →
       Labelling (node m k b (D₁ ∷ₗ D₂ ∷ₗ []ₗ))
lab₂ f₁ f₂ x e .at ε                     = x , e
lab₂ f₁ f₂ x e .at (into here p)         = f₁ .at p
lab₂ f₁ f₂ x e .at (into (there here) p) = f₂ .at p
lab₂ f₁ f₂ x e .at (into (there (there ())) _)

lab₊ : ∀ {m k b D D' Ds} → Labelling D → Labelling (node m k b (D' ∷ₗ Ds)) →
       Labelling (node m k b (D ∷ₗ D' ∷ₗ Ds))
lab₊ f g .at ε                  = g .at ε
lab₊ f g .at (into here p)      = f .at p
lab₊ f g .at (into (there i) p) = g .at (into i p)

lab₃ : ∀ {m k b D₁ D₂ D₃} → Labelling D₁ → Labelling D₂ → Labelling D₃ →
       (x : Node) → node-width x ≡ k →
       Labelling (node m k b (D₁ ∷ₗ D₂ ∷ₗ D₃ ∷ₗ []ₗ))
lab₃ f₁ f₂ f₃ x e .at ε                             = x , e
lab₃ f₁ f₂ f₃ x e .at (into here p)                 = f₁ .at p
lab₃ f₁ f₂ f₃ x e .at (into (there here) p)         = f₂ .at p
lab₃ f₁ f₂ f₃ x e .at (into (there (there here)) p) = f₃ .at p
lab₃ f₁ f₂ f₃ x e .at (into (there (there (there ()))) _)

mutual
  label : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) →
          Labelling (deriv D)
  label {v = v} (⇓-var x)         = lab₀ (val v) refl
  label {v = v} ⇓-unit            = lab₀ (val v) refl
  label {v = v} ⇓-lam             = lab₀ (val v) refl
  label {v = v} (⇓-inl D)         = lab₁ (label D) (val v) refl
  label {v = v} (⇓-inr D)         = lab₁ (label D) (val v) refl
  label {v = v} (⇓-case-l D₁ D₂)  = lab₂ (label D₁) (label D₂) (val v) refl
  label {v = v} (⇓-case-r D₁ D₂)  = lab₂ (label D₁) (label D₂) (val v) refl
  label {v = v} (⇓-pair D₁ D₂)    = lab₂ (label D₁) (label D₂) (val v) refl
  label {v = v} (⇓-fst D)         = lab₁ (label D) (val v) refl
  label {v = v} (⇓-snd D)         = lab₁ (label D) (val v) refl
  label {v = v} (⇓-app D₁ D₂ D₃)  = lab₃ (label D₁) (label D₂) (label D₃) (val v) refl
  label {v = v} (⇓-bop D)         = label-premises D (val v) refl
  label {v = v} (⇓-brel D)        = label-premises D (val v) refl
  label {v = v} (⇓-roll D)        = lab₁ (label D) (val v) refl
  label {v = v} (⇓-fold D₁ D₂)    = lab₂ (label D₁) (label-m D₂) (val v) refl

  label-premises : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
                   (D : γ , Ms ⇓s vs [ R ]) {m k b} (x : Node) → node-width x ≡ k →
                   Labelling (node m k b (derivs D))
  label-premises []                 x e = lab₀ x e
  label-premises (D₁ ∷ [])          x e = lab₁ (label D₁) x e
  label-premises (D₁ ∷ D₂@(_ ∷ _))  x e = lab₊ (label D₁) (label-premises D₂ x e)

  label-m : ∀ {Γ} {γ : Env Γ} {τ₀ σr s σ' v v' F} (D : Map γ {τ₀} {σr} s σ' v v' F) →
            Labelling (deriv-m D)
  label-m {v' = v'} (m-rec D₁ D₂)  = lab₂ (label-m D₁) (label D₂) (val v') refl
  label-m {v' = v'} m-unit         = lab₀ (val v') refl
  label-m {v' = v'} m-base         = lab₀ (val v') refl
  label-m {v' = v'} m-arrow        = lab₀ (val v') refl
  label-m {v' = v'} (m-inl D)      = lab₁ (label-m D) (val v') refl
  label-m {v' = v'} (m-inr D)      = lab₁ (label-m D) (val v') refl
  label-m {v' = v'} (m-pair D₁ D₂) = lab₂ (label-m D₁) (label-m D₂) (val v') refl
  label-m {v' = v'} (m-mu D)       = lab₁ (label-m D) (val v') refl
