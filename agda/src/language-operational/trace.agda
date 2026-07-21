{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (0ℓ)

open import Data.List using (List; []; _∷_; applyUpTo)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_,_; _×_)
open import Data.String using (String; intersperse) renaming (_++_ to _++ˢ_)
import Data.Nat.Show as ℕ-Show
open import prop-setoid using (Setoid)
open import every using (Every; []; _∷_)
import two
open import signature using (Signature)
open import primitives using (Primitives)

-- Rendering of evaluation derivations as traces, and dot rendering of dependence graphs.
module language-operational.trace
  {ℓ} (Sig : Signature ℓ) (𝒫 : Primitives two.semiring Sig)
  (show-op : ∀ {is o} → Signature.op Sig is o → String)
  where

open Signature Sig
open Primitives 𝒫
open prop-setoid._⇒_ using (func)
open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.evaluation Sig 𝒫

var-to-ℕ : ∀ {Γ τ} → Γ ∋ τ → ℕ
var-to-ℕ zero     = zero
var-to-ℕ (succ x) = suc (var-to-ℕ x)

------------------------------------------------------------------------
-- Derivation pretty-printing (ignores the matrix indices).

show-eval  : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} → _,_⇓_[_] γ t v R → String
show-evals : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R} →
             _,_⇓s_[_] γ Ms vs R → List String
show-map   : ∀ {Γ} {γ : Env Γ} {τ₀ σr} {s : Γ ▸ τ₀ [ σr ] ⊢ σr} {σ' v R v' R'} →
             Map γ {τ₀} {σr} s σ' v R v' R' → String

show-eval (⇓-var x)        = "(var " ++ˢ ℕ-Show.show (var-to-ℕ x) ++ˢ ")"
show-eval ⇓-unit           = "unit"
show-eval (⇓-inl t)        = "(inl " ++ˢ show-eval t ++ˢ ")"
show-eval (⇓-inr t)        = "(inr " ++ˢ show-eval t ++ˢ ")"
show-eval (⇓-case-l s b)   = "(case-l " ++ˢ show-eval s ++ˢ " " ++ˢ show-eval b ++ˢ ")"
show-eval (⇓-case-r s b)   = "(case-r " ++ˢ show-eval s ++ˢ " " ++ˢ show-eval b ++ˢ ")"
show-eval (⇓-pair a b)     = "(pair " ++ˢ show-eval a ++ˢ " " ++ˢ show-eval b ++ˢ ")"
show-eval (⇓-fst t)        = "(fst " ++ˢ show-eval t ++ˢ ")"
show-eval (⇓-snd t)        = "(snd " ++ˢ show-eval t ++ˢ ")"
show-eval ⇓-lam            = "lam"
show-eval (⇓-app f a b)    = "(app " ++ˢ show-eval f ++ˢ " " ++ˢ show-eval a ++ˢ " " ++ˢ show-eval b ++ˢ ")"
show-eval (⇓-bop {ω = ω} ts) = "(bop " ++ˢ show-op ω ++ˢ " (" ++ˢ intersperse " " (show-evals ts) ++ˢ "))"
show-eval (⇓-brel ts)      = "(brel (" ++ˢ intersperse " " (show-evals ts) ++ˢ "))"
show-eval (⇓-roll t)       = "(roll " ++ˢ show-eval t ++ˢ ")"
show-eval (⇓-fold t m)     = "(fold " ++ˢ show-eval t ++ˢ " " ++ˢ show-map m ++ˢ ")"

show-evals []       = []
show-evals (t ∷ ts) = show-eval t ∷ show-evals ts

show-map (m-rec m b)    = "(rec " ++ˢ show-map m ++ˢ " " ++ˢ show-eval b ++ˢ ")"
show-map m-unit         = "-"
show-map m-base         = "-"
show-map m-arrow        = "-"
show-map (m-inl m)      = "(inl " ++ˢ show-map m ++ˢ ")"
show-map (m-inr m)      = "(inr " ++ˢ show-map m ++ˢ ")"
show-map (m-pair m₁ m₂) = "(pair " ++ˢ show-map m₁ ++ˢ " " ++ˢ show-map m₂ ++ˢ ")"
show-map (m-mu m)       = "(mu " ++ˢ show-map m ++ˢ ")"

-- Unlabelled rendering, for dependence graphs over intermediates. Every vertex is declared, so
-- isolated ones are rendered.
showDotPlain : ℕ → List (ℕ × ℕ) → String
showDotPlain n es = "digraph G {\n" ++ˢ vertices (applyUpTo (λ i → i) n) ++ˢ go es ++ˢ "}\n"
  where
    vertices : List ℕ → String
    vertices []       = ""
    vertices (i ∷ is) = "  " ++ˢ ℕ-Show.show i ++ˢ ";\n" ++ˢ vertices is
    edge : ℕ × ℕ → String
    edge (i , j) = "  " ++ˢ ℕ-Show.show i ++ˢ " -> " ++ˢ ℕ-Show.show j ++ˢ ";\n"
    go : List (ℕ × ℕ) → String
    go []       = ""
    go (e ∷ es) = edge e ++ˢ go es
