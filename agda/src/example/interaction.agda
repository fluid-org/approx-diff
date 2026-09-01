{-# OPTIONS --prop --postfix-projections --safe #-}

-- Interaction tests over the three-chain: what a Boolean run reports as reached, the three-chain
-- run separates into value flow and control.
module example.interaction where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (suc)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.List.Relation.Unary.All using ([]; _∷_)
import three

open import signature.example ℚ using (Sig; number; add; mult)
open import semiring-Q using (nonzero)
import signature.example.interpretation
module Dep = signature.example.interpretation (nonzero three.semiring) three.semiring

open import language-syntax Sig using (_⊢_; zero; succ; base; var; inl; case; bop; emp) renaming (_,_ to _▸_)
open import language-operational.evaluation Sig three.semiring Dep.interpretation three.C
open import interaction.graph three.semiring (λ x → three.∨-idem {x})
open import interaction.dependence-graph Sig three.semiring Dep.interpretation three.C (λ x → three.∨-idem {x})
open import interaction.moves three.semiring (λ x → three.∨-idem {x}) three.≡-of-≈ three.ε?

module rewiring where

  γ₀ : Env (emp ▸ base number)
  γ₀ = emp · const 1ℚ

  D : γ₀ , case (inl (var zero)) (var zero) (var zero) ⇓ const 1ℚ [ _ ]
  D = ⇓-case-l (⇓-inl (⇓-var zero)) (⇓-var zero)

  G : Graph (suc (width-env γ₀)) _
  G = graph D

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

  -- Everything hidden: the scalar reaches the root as value flow, surviving the control point.
  init-dep : visible-graph K₀ env rt zero (suc zero) ≡ three.D
  init-dep = refl

  -- Scrutinee revealed: value flow in and out of the revealed vertex.
  reveal-in : visible-graph K₁ env (at scrut) (suc zero) (suc zero) ≡ three.D
  reveal-in = refl

  reveal-out : visible-graph K₁ (at scrut) rt zero (suc zero) ≡ three.D
  reveal-out = refl

  reveal-no-direct : visible-graph K₁ env rt zero (suc zero) ≡ three.O
  reveal-no-direct = refl

  -- The scrutinee's tag position gates the root: control, not value flow.
  reveal-ctrl : visible-graph K₁ (at scrut) rt zero zero ≡ three.C
  reveal-ctrl = refl

  collapse-agrees : collapse G zero (suc zero) ≡ three.D
  collapse-agrees = refl

-- An intermediate with a route past it: y · (x + y) at (x, y) = (0, 1). With everything hidden both
-- inputs reach the root. Revealing the sum shows it fed by both inputs and feeding the root, with y
-- still reaching the root without it and x not.
module intermediate where

  γ₀ : Env (emp ▸ base number ▸ base number)
  γ₀ = emp · const 0ℚ · const 1ℚ

  D : γ₀ , bop mult (bop add (var zero ∷ var (succ zero) ∷ []) ∷ var zero ∷ []) ⇓ _ [ _ ]
  D = ⇓-bop (⇓-bop (⇓-var zero ∷ ⇓-var (succ zero) ∷ []) ∷ ⇓-var zero ∷ [])

  G : Graph (suc (width-env γ₀)) _
  G = graph D

  open Interaction G

  sum : Vertex (Graph.shape G)
  sum = inj₁ (inj₁ (inj₂ root))

  env : V G
  env = inj₁ input

  at : Vertex (Graph.shape G) → V G
  at p = inj₂ (inj₁ p)

  rt : V G
  rt = inj₂ (inj₂ root)

  x y : Fin (suc (width-env γ₀))
  x = suc zero
  y = suc (suc zero)

  K₀ : Config G
  K₀ = initial

  K₁ : Config G
  K₁ = reveal-at sum K₀

  hidden-x : visible-graph K₀ env rt zero x ≡ three.D
  hidden-x = refl

  hidden-y : visible-graph K₀ env rt zero y ≡ three.D
  hidden-y = refl

  sum-from-x : visible-graph K₁ env (at sum) zero x ≡ three.D
  sum-from-x = refl

  sum-from-y : visible-graph K₁ env (at sum) zero y ≡ three.D
  sum-from-y = refl

  sum-to-root : visible-graph K₁ (at sum) rt zero zero ≡ three.D
  sum-to-root = refl

  bypass-y : visible-graph K₁ env rt zero y ≡ three.D
  bypass-y = refl

  no-bypass-x : visible-graph K₁ env rt zero x ≡ three.O
  no-bypass-x = refl
