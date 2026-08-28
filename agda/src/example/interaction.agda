{-# OPTIONS --prop --postfix-projections --safe #-}

module example.interaction where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (suc)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.List.Relation.Unary.All using ([]; _∷_)
import two

open import signature.example ℚ using (Sig; number; add; mult)
open import semiring-Q using (nonzero)
import signature.example.interpretation
module Dep = signature.example.interpretation (nonzero two.semiring) two.semiring

open import language-syntax Sig using (_⊢_; zero; succ; base; var; inl; case; bop; emp) renaming (_,_ to _▸_)
open import language-operational.evaluation Sig two.semiring Dep.interpretation two.I
open import interaction.graph two.semiring (λ x → two.∨-idem {x})
open import interaction.dependence-graph Sig two.semiring Dep.interpretation two.I (λ x → two.∨-idem {x})
open import interaction.moves

-- A run with rewiring: case (inl x) of inl x₁ → x₁ | inr y → y. The branch is evaluated under the
-- extended environment, so its env edges are redistributed to env and the scrutinee root, giving the chain
-- env → inl payload → scrutinee root → branch root → root. Initially the three intermediates form one
-- hidden region; revealing the scrutinee root splits it in two, and hiding it again merges them back.
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

  branch : Vertex (Graph.shape G)
  branch = inj₂ (inj₂ root)

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

  K₂ : Config G
  K₂ = hide-at scrut K₁

  -- Everything hidden: the output depends on the input, through the whole chain.
  init-dep : visible-graph K₀ env rt zero (suc zero) ≡ two.I
  init-dep = refl

  -- Scrutinee root revealed: its region splits, dependence routes through the revealed vertex, and
  -- the direct env-to-root entry disappears.
  reveal-in : visible-graph K₁ env (at scrut) (suc zero) (suc zero) ≡ two.I
  reveal-in = refl

  reveal-out : visible-graph K₁ (at scrut) rt zero (suc zero) ≡ two.I
  reveal-out = refl

  reveal-no-direct : visible-graph K₁ env rt zero (suc zero) ≡ two.O
  reveal-no-direct = refl

  -- The rewired env column of the branch is zero: the branch body uses only the bound variable.
  reveal-no-env-branch : fo-graph G env (at branch) zero (suc zero) ≡ two.O
  reveal-no-env-branch = refl

  -- The scrutinee slice of the branch environment carries the dependence instead.
  rewired-scrut-branch : fo-graph G (at scrut) (at branch) zero (suc zero) ≡ two.I
  rewired-scrut-branch = refl

  -- Hidden again: the regions merge back and the initial view returns.
  rehide-dep : visible-graph K₂ env rt zero (suc zero) ≡ two.I
  rehide-dep = refl

  -- Collapsing the whole derivation recovers the run's dependency relation.
  collapse-agrees : collapse G zero (suc zero) ≡ two.I
  collapse-agrees = refl

-- An intermediate with a route past it: y * (x + y) at (x, y) = (0, 1). With everything hidden both inputs
-- reach the root. Revealing the sum shows it fed by both inputs and feeding the root, with y still reaching
-- the root without it and x not.
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

  hidden-x : visible-graph K₀ env rt zero x ≡ two.I
  hidden-x = refl

  hidden-y : visible-graph K₀ env rt zero y ≡ two.I
  hidden-y = refl

  sum-from-x : visible-graph K₁ env (at sum) zero x ≡ two.I
  sum-from-x = refl

  sum-from-y : visible-graph K₁ env (at sum) zero y ≡ two.I
  sum-from-y = refl

  sum-to-root : visible-graph K₁ (at sum) rt zero zero ≡ two.I
  sum-to-root = refl

  bypass-y : visible-graph K₁ env rt zero y ≡ two.I
  bypass-y = refl

  no-bypass-x : visible-graph K₁ env rt zero x ≡ two.O
  no-bypass-x = refl
