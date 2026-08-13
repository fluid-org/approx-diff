{-# OPTIONS --prop --postfix-projections --safe #-}

-- Hide and reveal on a run with rewiring: case (inl x) of inl x₁ → x₁ | inr y → y. The branch is
-- evaluated under the extended environment, so its env edges are redistributed to env and the
-- scrutinee root, giving the chain env → inl payload → scrutinee root → branch root → root.
-- Initially the three intermediates form one hidden region; revealing the scrutinee root splits it
-- in two, and hiding it again merges them back.
module interaction.example where

open import Data.Fin using (zero; suc)
open import Data.Rational using (ℚ; 1ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import two

open import example.signature ℚ using (Sig; number)
import example.primitives as Dep

open import language-syntax Sig using (_⊢_; _∋_; zero; base; var; inl; case; ctxt; emp)
  renaming (_,_ to _▸_)
open import language-operational.evaluation Sig Dep.primitives
open import interaction.path Sig Dep.primitives
open import interaction.graph Sig Dep.primitives
open import interaction.hide Sig Dep.primitives
open import interaction.config Sig Dep.primitives

γ₀ : Env (emp ▸ base number)
γ₀ = emp · const 1ℚ

D : γ₀ , case (inl (var zero)) (var zero) (var zero) ⇓ const 1ℚ [ _ ]
D = ⇓-case-l (⇓-inl (⇓-var zero)) (⇓-var zero)

-- The scrutinee root, mid-chain.
scrut : Path D
scrut = case-l₁ ε

K₀ : Config D
K₀ = initial

K₁ : Config D
K₁ = reveal-at scrut K₀

K₂ : Config D
K₂ = hide-at scrut K₁

-- Everything hidden: the output depends on the input, through the whole chain.
init-dep : visible-graph K₀ env (at ε) zero zero ≡ two.I
init-dep = refl

-- Scrutinee root revealed: its region splits, dependence routes through the revealed vertex, and
-- the direct env-to-root entry disappears.
reveal-in : visible-graph K₁ env (at scrut) (suc zero) zero ≡ two.I
reveal-in = refl

reveal-out : visible-graph K₁ (at scrut) (at ε) zero (suc zero) ≡ two.I
reveal-out = refl

reveal-no-direct : visible-graph K₁ env (at ε) zero zero ≡ two.O
reveal-no-direct = refl

-- The rewired env column of the branch is zero: the branch body uses only the bound variable.
reveal-no-env-branch : fo-graph D env (at (case-l₂ ε)) zero zero ≡ two.O
reveal-no-env-branch = refl

-- The scrutinee slice of the branch environment carries the dependence instead.
rewired-scrut-branch : fo-graph D (at scrut) (at (case-l₂ ε)) zero (suc zero) ≡ two.I
rewired-scrut-branch = refl

-- Hidden again: the regions merge back and the initial view returns.
rehide-dep : visible-graph K₂ env (at ε) zero zero ≡ two.I
rehide-dep = refl

-- Collapsing the whole derivation recovers the run's dependency relation.
collapse-agrees : collapse D zero zero ≡ two.I
collapse-agrees = refl
