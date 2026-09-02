{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.Nat using (ℕ; suc)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Data.Product using (proj₁; proj₂)
open import Level using (0ℓ)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import signature using (Signature)
open import signature.interpretation using (Interpretation)

-- A term evaluated at an environment, with the dependence graph and vertex labelling of the
-- resulting derivation.
module interaction.evaluated {ℓ} (Sig : Signature ℓ) {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (ℐ : Interpretation S Sig) (ctrl-weight : Setoid.Carrier A)
  (let module S = CommutativeSemiring S) (+-idem : ∀ x → (x S.+ x) S.≈ x) where

open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.evaluation Sig S ℐ ctrl-weight
open import language-operational.totality Sig S ℐ ctrl-weight using (eval)
open import interaction.graph S +-idem
open import matrix-embedding S using (𝔽)
open import interaction.dependence-graph Sig S ℐ ctrl-weight +-idem
open import interaction.labelling Sig S ℐ ctrl-weight +-idem

module Evaluated {Γ τ} (γ : Env Γ) (t : Γ ⊢ τ) where

  private
    ev : Derivation γ t
    ev = eval t γ

  value : Val τ
  value = proj₁ ev

  derivation : γ , t ⇓ value [ proj₁ (proj₂ ev) ]
  derivation = proj₂ (proj₂ ev)

  dependence : Graph (𝔽 (suc (width-env γ))) (𝔽 (width value))
  dependence = graph derivation

  labels : Labelling (Graph.shape dependence) (Graph.object dependence)
  labels = label derivation

  widths : V dependence → ℕ
  widths (inj₁ _)        = suc (width-env γ)
  widths (inj₂ (inj₁ p)) = node-width (proj₁ (labels .at p))
  widths (inj₂ (inj₂ _)) = width value

  free : ∀ v → vertex-object dependence v ≡ 𝔽 (widths v)
  free (inj₁ _)        = refl
  free (inj₂ (inj₁ p)) = sym (proj₂ (labels .at p))
  free (inj₂ (inj₂ _)) = refl
