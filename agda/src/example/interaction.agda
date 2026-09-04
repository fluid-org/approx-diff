{-# OPTIONS --prop --postfix-projections --safe #-}

module example.interaction where

open import Data.Fin using (zero; suc)
open import Data.Nat using (suc)
open import Data.Rational using (ℚ; 1ℚ)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import three

open import signature.example ℚ using (Sig; number)
open import semiring-Q using (nonzero)
import signature.example.interpretation
module Dep = signature.example.interpretation (nonzero three.semiring) three.semiring

open import language-syntax Sig using (_⊢_; zero; base; var; inl; case; emp) renaming (_,_ to _▸_)
open import language-operational.evaluation Sig three.semiring Dep.interpretation three.C
open import interaction.evaluated Sig three.semiring Dep.interpretation three.C (λ x → three.∨-idem {x})
open import interaction.graph three.semiring (λ x → three.∨-idem {x})
open import interaction.dependence-graph Sig three.semiring Dep.interpretation three.C (λ x → three.∨-idem {x})
open import interaction.moves three.semiring (λ x → three.∨-idem {x}) three.≡-of-≈ three.ε?

module rewiring where

  γ₀ : Env (emp ▸ base number)
  γ₀ = emp · const 1ℚ

  t₀ : (emp ▸ base number) ⊢ base number
  t₀ = case (inl (var zero)) (var zero) (var zero)

  open Evaluated γ₀ t₀ using (dependence)

  G : Graph (suc (width-env γ₀)) _
  G = dependence

  open Interaction G

  scrut : Vertex (Graph.shape G)
  scrut = inj₁ (inj₂ root)

  env : V G
  env = inj₁ input

  at : Vertex (Graph.shape G) → V G
  at p = inj₂ (inj₁ p)

  rt : V G
  rt = inj₂ (inj₂ root)

  K₀ : Config G
  K₀ = initial

  K₁ : Config G
  K₁ = reveal-at scrut K₀

  -- Scrutinee revealed: value flow in and out of the revealed vertex.
  reveal-in : entry env (at scrut) (visible-graph K₁ env (at scrut)) (suc zero) (suc zero) ≡ three.D
  reveal-in = refl

  reveal-out : entry (at scrut) rt (visible-graph K₁ (at scrut) rt) zero (suc zero) ≡ three.D
  reveal-out = refl

  reveal-no-direct : entry env rt (visible-graph K₁ env rt) zero (suc zero) ≡ three.O
  reveal-no-direct = refl

  -- The scrutinee's tag position gates the root: control, not value flow.
  reveal-ctrl : entry (at scrut) rt (visible-graph K₁ (at scrut) rt) zero zero ≡ three.C
  reveal-ctrl = refl
