{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.Nat using (suc)
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
open import interaction.graph S +-idem hiding (Derivation)
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

  dependence : Graph (suc (width-env γ)) (width value)
  dependence = graph derivation

  labels : Labelling (Graph.D dependence) (Graph.width dependence)
  labels = label derivation
