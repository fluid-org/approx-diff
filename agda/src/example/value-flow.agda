{-# OPTIONS --prop --postfix-projections --safe #-}

-- Value flow through an intermediate: y * (x + y) at (x, y) = (0, 1). With everything hidden both
-- inputs reach the root. Revealing the sum shows it fed by both inputs and feeding the root, with y
-- reaching the root without it and x not.
module example.value-flow where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (suc)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import every using ([]; _∷_)
import two

open import signature.example ℚ using (Sig; number; add; mult)
import signature.example.interpretation two.semiring as Dep

open import language-syntax Sig using (_⊢_; zero; succ; base; var; bop; emp) renaming (_,_ to _▸_)
open import language-operational.evaluation Sig two.semiring Dep.interpretation two.I
open import interaction.graph
open import interaction.dependence-graph Sig Dep.interpretation
open import interaction.moves

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

init-x : visible-graph K₀ env rt zero x ≡ two.I
init-x = refl

init-y : visible-graph K₀ env rt zero y ≡ two.I
init-y = refl

sum-x : visible-graph K₁ env (at sum) zero x ≡ two.I
sum-x = refl

sum-y : visible-graph K₁ env (at sum) zero y ≡ two.I
sum-y = refl

sum-out : visible-graph K₁ (at sum) rt zero zero ≡ two.I
sum-out = refl

direct-y : visible-graph K₁ env rt zero y ≡ two.I
direct-y = refl

direct-x : visible-graph K₁ env rt zero x ≡ two.O
direct-x = refl
