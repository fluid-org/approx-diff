{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (0ℓ)

open import Data.List using (List; []; _∷_)
import Data.Fin
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_,_; _×_)
open import Data.String using (String) renaming (_++_ to _++ˢ_)
import Data.Nat.Show as ℕ-Show
open import prop-setoid using (Setoid)
import two
open import signature using (Signature)
open import primitives using (Primitives)

-- Rendering of values and dependence graphs.
module language-operational.render
  {ℓ} (Sig : Signature ℓ) (𝒫 : Primitives two.semiring Sig)
  where

open Signature Sig
open Primitives 𝒫
open prop-setoid._⇒_ using (func)
open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.evaluation Sig 𝒫

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
    show-val (pair v u) = "(" ++ˢ show-val v ++ˢ ", " ++ˢ show-flat u ++ˢ ")"
    show-val (clo _ _)  = "<closure>"
    show-val (roll v)   = show-val v

    -- Right-nested pairs render as flat tuples, reading (a, b, c) as (a, (b, c)).
    show-flat : ∀ {τ} → Val τ → String
    show-flat (pair v u) = show-val v ++ˢ ", " ++ˢ show-flat u
    show-flat v          = show-val v

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
