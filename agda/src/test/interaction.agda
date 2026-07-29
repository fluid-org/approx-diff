{-# OPTIONS --prop --postfix-projections --safe #-}

-- Hide and reveal on a concrete run: a pair of two copies of a rational variable. Initially both
-- components are hidden and the visible graph shows the run's dependence from env to the root;
-- revealing the first component reroutes its half through the revealed vertex, and hiding it again
-- restores the initial view.
module test.interaction where

open import Data.Fin using (zero; suc)
open import Data.Rational using (ℚ; 1ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import two

open import example.signature ℚ using (Sig; number)
import example.dependency as Dep

open import language-syntax Sig using (_⊢_; _∋_; zero; base; var; pair; ctxt; emp)
  renaming (_,_ to _▸_)
open import language-operational.evaluation Sig Dep.primitives
open import language-operational.path Sig Dep.primitives
open import language-operational.graph Sig Dep.primitives
open import language-operational.hide Sig Dep.primitives

open import categories using (HasProducts)
open HasProducts products using () renaming (pair to ⟨_,_⟩)

γ₀ : Env (emp ▸ base number)
γ₀ = emp · const 1ℚ

D : γ₀ , pair (var zero) (var zero) ⇓ pair (const 1ℚ) (const 1ℚ)
      [ ⟨ proj-var zero γ₀ , proj-var zero γ₀ ⟩ ]
D = ⇓-pair (⇓-var zero) (⇓-var zero)

K₀ : Config D
K₀ = initial D

K₁ : Config D
K₁ = reveal-at D (pair₁ ε) K₀

K₂ : Config D
K₂ = hide-at D (pair₁ ε) K₁

-- Everything hidden: both positions of the root depend on the input.
init-fst : visible-graph D K₀ env (at ε) zero zero ≡ two.I
init-fst = refl

init-snd : visible-graph D K₀ env (at ε) (suc zero) zero ≡ two.I
init-snd = refl

-- First component revealed: its dependence routes through the revealed vertex, so the direct
-- env-to-root entry for the first position disappears while the second remains.
reveal-env-vertex : visible-graph D K₁ env (at (pair₁ ε)) zero zero ≡ two.I
reveal-env-vertex = refl

reveal-vertex-root : visible-graph D K₁ (at (pair₁ ε)) (at ε) zero zero ≡ two.I
reveal-vertex-root = refl

reveal-vertex-root' : visible-graph D K₁ (at (pair₁ ε)) (at ε) (suc zero) zero ≡ two.O
reveal-vertex-root' = refl

reveal-fst : visible-graph D K₁ env (at ε) zero zero ≡ two.O
reveal-fst = refl

reveal-snd : visible-graph D K₁ env (at ε) (suc zero) zero ≡ two.I
reveal-snd = refl

-- Hidden again: the initial view returns.
rehide-fst : visible-graph D K₂ env (at ε) zero zero ≡ two.I
rehide-fst = refl

rehide-snd : visible-graph D K₂ env (at ε) (suc zero) zero ≡ two.I
rehide-snd = refl
