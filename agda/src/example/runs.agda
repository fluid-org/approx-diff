{-# OPTIONS --prop --postfix-projections --safe #-}

-- The example terms, their runs, and their markings, shared by the tests and the dot renderer.
module example.runs where

open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _/_; ↥_; ↧ₙ_)
open import Data.Integer using (+_)
open import Data.String using (String)
open import Data.Unit.Polymorphic using (tt)
open import every using ([]; _∷_)
import label as L
import Data.Rational.Show as ℚ-Show
import Data.Integer.Show as ℤ-Show
open import primitives using (Primitives)

open import example.signature ℚ
  using (Sig; sort; number; label; op; lit; add; mult; lbl; rel; equal-label)
open import example.relation using (module Tot; module Instr)
import example.dependency as Dep
open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.evaluation Sig Dep.primitives
  using (Env; emp; _·_; const; pair)
open Instr

show-lbl : L.label → String
show-lbl L.a = "a"
show-lbl L.b = "b"
show-lbl L.c = "c"
show-lbl L.d = "d"

-- Whole rationals render without the denominator; label constants as quoted strings.
show-ℚ : ℚ → String
show-ℚ q with ↧ₙ q
... | 1 = ℤ-Show.show (↥ q)
... | _ = ℚ-Show.show q

show-const : ∀ {s} → Primitives.sort-val Dep.primitives s → String
show-const {number} q = show-ℚ q
show-const {label}  l = "“" Data.String.++ show-lbl l Data.String.++ "”"

------------------------------------------------------------------------
-- Addition of two variables.

M-add : (emp ▸ base number ▸ base number) ⊢ base number
M-add = bop add (var zero ∷ var (succ zero) ∷ [])

run-add = Tot.fundamental M-add (emp · const 0ℚ · const 1ℚ) ((tt , tt) , tt)

D-add = proj₁ (proj₂ (proj₂ run-add))

inst-add-full = instrument-d (marked-all-d D-add) ∅

------------------------------------------------------------------------
-- Multiplication of two variables, at (0, 1). The derivative of x * y is [y, x], so the result
-- depends on x (whose coefficient is y = 1) and not on y (whose coefficient is x = 0).

M-mult : (emp ▸ base number ▸ base number) ⊢ base number
M-mult = bop mult (var zero ∷ var (succ zero) ∷ [])

run-mult = Tot.fundamental M-mult (emp · const 0ℚ · const 1ℚ) ((tt , tt) , tt)

D-mult = proj₁ (proj₂ (proj₂ run-mult))

inst-mult-full = instrument-d (marked-all-d D-mult) ∅

------------------------------------------------------------------------
-- Sum the numbers paired with a given label in a list of (label, number) pairs, fused into a
-- single fold.

elem : type 0
elem = base label [×] base number

query : L.label → emp ⊢ list elem → emp ⊢ base number
query l xs =
  fold (case (var zero)
          (bop (lit 0ℚ) [])
          (if brel equal-label (fst (fst (var zero)) ∷ bop (lbl l) [] ∷ [])
           then bop add (snd (fst (var zero)) ∷ snd (var zero) ∷ [])
           else snd (var zero)))
       xs

entry : ∀ {Γ} → L.label → ℚ → Γ ⊢ elem
entry l q = pair (bop (lbl l) []) (bop (lit q) [])

input : emp ⊢ list elem
input = cons (entry L.a 0ℚ) (cons (entry L.b 1ℚ) (cons (entry L.a 1ℚ) nil))

run-query = Tot.eval (query L.a input)

D-query = proj₂ (proj₂ run-query)

inst-query-a-full = instrument-d (marked-all-d D-query) ∅

------------------------------------------------------------------------
-- Marking each input entry and each fold body result.

inst-query-a-marked =
  instrument-d
    (mark-at (fold₁ ∷ roll ∷ inr ∷ pair₁ ∷ [])
    (mark-at (fold₁ ∷ roll ∷ inr ∷ pair₂ ∷ roll ∷ inr ∷ pair₁ ∷ [])
    (mark-at (fold₁ ∷ roll ∷ inr ∷ pair₂ ∷ roll ∷ inr ∷ pair₂ ∷ roll ∷ inr ∷ pair₁ ∷ [])
    (mark-at (fold₂ ∷ rec₂ ∷ [])
    (mark-at (fold₂ ∷ rec₁ ∷ m-inj ∷ m-pair₂ ∷ rec₂ ∷ [])
    (mark-at (fold₂ ∷ rec₁ ∷ m-inj ∷ m-pair₂ ∷ rec₁ ∷ m-inj ∷ m-pair₂ ∷ rec₂ ∷ [])
    (mark-at (fold₂ ∷ rec₁ ∷ m-inj ∷ m-pair₂ ∷ rec₁ ∷ m-inj ∷ m-pair₂ ∷ rec₁ ∷ m-inj ∷ m-pair₂ ∷ rec₂ ∷ [])
    (unmarked-d D-query))))))))
    ∅

------------------------------------------------------------------------
-- Coarse marking: the input list as a single width-3 intermediate and the query result, with the
-- fold unmarked.

inst-query-a-coarse =
  instrument-d
    (mark-at (fold₁ ∷ [])
    (mark-at []
    (unmarked-d D-query)))
    ∅

------------------------------------------------------------------------
-- Flattening example: y * (x + y) with the sum marked.

t-mm : (emp ▸ base number ▸ base number) ⊢ base number
t-mm = bop mult (bop add (var zero ∷ var (succ zero) ∷ []) ∷ var zero ∷ [])

γ-mm : Env (emp ▸ base number ▸ base number)
γ-mm = emp · const 0ℚ · const 1ℚ

run-mm = Tot.fundamental t-mm γ-mm ((tt , tt) , tt)

D-mm = proj₁ (proj₂ (proj₂ run-mm))

inst-mm = instrument-d (mark-at (bop ∷ hd ∷ []) (unmarked-d D-mm)) ∅

------------------------------------------------------------------------
-- Moving average with window two: adjacent outputs share an input.

half : ℚ
half = + 1 / 2

γ-mavg : Env (emp ▸ base number [×] (base number [×] (base number [×] base number)))
γ-mavg = emp · pair (const 1ℚ) (pair (const (+ 2 / 1)) (pair (const (+ 4 / 1)) (const (+ 8 / 1))))

run-mavg = Tot.fundamental (Dep.mavg half) γ-mavg (tt , tt , tt , tt , tt)

D-mavg = proj₁ (proj₂ (proj₂ run-mavg))

inst-mavg-full = instrument-d (marked-all-d D-mavg) ∅

-- Coarse marking: eta-expanded so the input is evaluated once, giving a single width-4
-- intermediate; the one edge to the output carries the full dependency relation.
mavg-coarse-term : emp ▸ base number [×] (base number [×] (base number [×] base number))
                   ⊢ base number [×] (base number [×] base number)
mavg-coarse-term = app (lam (Dep.mavg-body half (var zero))) (var zero)

run-mavg-coarse = Tot.fundamental mavg-coarse-term γ-mavg (tt , tt , tt , tt , tt)

D-mavg-coarse = proj₁ (proj₂ (proj₂ run-mavg-coarse))

inst-mavg-coarse =
  instrument-d
    (mark-at (app₂ ∷ [])
    (mark-at []
    (unmarked-d D-mavg-coarse)))
    ∅
