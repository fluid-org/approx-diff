{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (0ℓ)

open import Data.List using (List; []; _∷_)
import Data.Fin
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

-- Values as strings, given a rendering of the constants. Roll is invisible, so inductive values
-- read as their contents; values of list type render bracketed.
module _ (show-const : ∀ {s} → sort-val s → String) where

  mutual
    show-val : ∀ {τ} → Val τ → String
    show-val {μ (unit [+] (_ [×] var Data.Fin.zero))} v = "[" ++ˢ show-list v ++ˢ "]"
    show-val unit       = "()"
    show-val (const c)  = show-const c
    show-val (inl v)    = "inl " ++ˢ show-val v
    show-val (inr v)    = "inr " ++ˢ show-val v
    show-val (pair v u) = "(" ++ˢ show-val v ++ˢ ", " ++ˢ show-val u ++ˢ ")"
    show-val (clo _ _)  = "<closure>"
    show-val (roll v)   = show-val v

    show-list : ∀ {σ} → Val (μ (unit [+] (σ [×] var Data.Fin.zero))) → String
    show-list (roll (inl unit))                       = ""
    show-list (roll (inr (pair v (roll (inl unit))))) = show-val v
    show-list (roll (inr (pair v rest)))              = show-val v ++ˢ ", " ++ˢ show-list rest

-- Rendering for dependence graphs over intermediates: one vertex per label, declared so that
-- isolated vertices are rendered. An edge with a label aggregates a relation bigger than
-- Fin 1 → Fin 1, drawn dotted with the relation as its label.
showDotPlain : List String → List (ℕ × ℕ × String) → String
showDotPlain ls es = "digraph G {\n" ++ˢ vertices 0 ls ++ˢ go es ++ˢ "}\n"
  where
    vertices : ℕ → List String → String
    vertices _ []       = ""
    vertices i (l ∷ ls) =
      "  " ++ˢ ℕ-Show.show i ++ˢ " [label=\"" ++ˢ l ++ˢ "\"];\n" ++ˢ vertices (suc i) ls
    edge : ℕ × ℕ × String → String
    edge (i , j , "") = "  " ++ˢ ℕ-Show.show i ++ˢ " -> " ++ˢ ℕ-Show.show j ++ˢ ";\n"
    edge (i , j , l)  =
      "  " ++ˢ ℕ-Show.show i ++ˢ " -> " ++ˢ ℕ-Show.show j ++ˢ
      " [label=\"" ++ˢ l ++ˢ "\", style=dotted];\n"
    go : List (ℕ × ℕ × String) → String
    go []       = ""
    go (e ∷ es) = edge e ++ˢ go es
