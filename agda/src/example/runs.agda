{-# OPTIONS --prop --postfix-projections --safe #-}

-- The example terms, their runs, and their markings, shared by the tests and the artefact
-- renderer.
module example.runs where

open import Data.Fin using (Fin)
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
open import language-operational.marking Sig
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

inst-add-full = Instr.instrument (marked-all M-add) (emp · const · const) D-add ∅

------------------------------------------------------------------------
-- Multiplication of two variables, at (0, 1). The derivative of x * y is [y, x], so the result
-- depends on x (whose coefficient is y = 1) and not on y (whose coefficient is x = 0).

M-mult : (emp ▸ base number ▸ base number) ⊢ base number
M-mult = bop mult (var zero ∷ var (succ zero) ∷ [])

run-mult = Tot.fundamental M-mult (emp · const 0ℚ · const 1ℚ) ((tt , tt) , tt)

D-mult = proj₁ (proj₂ (proj₂ run-mult))

inst-mult-full = Instr.instrument (marked-all M-mult) (emp · const · const) D-mult ∅

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

inst-query-a-full = Instr.instrument (marked-all (query L.a input)) emp D-query ∅

------------------------------------------------------------------------
-- Doc marking: each input entry and the fold body's result.

m-entry : ∀ {Γ} {t : Γ ⊢ elem} → Marked t
m-entry = doc (base label [×] base number) (unmarked _)

m-input : Marked {emp} input
m-input =
  roll (inr (pair m-entry
    (roll (inr (pair m-entry
      (roll (inr (pair m-entry
        (roll (inl unit))))))))))

m-query : Marked (query L.a input)
m-query = fold (doc (base number) (unmarked _)) m-input

inst-query-a-marked = Instr.instrument m-query emp D-query ∅

------------------------------------------------------------------------
-- Coarse marking: the input list as a single width-3 intermediate and the query result, with the
-- fold unmarked.

list-fo : first-order (list elem)
list-fo = μ (unit [+] ((base label [×] base number) [×] var Fin.zero))

m-query-coarse : Marked (query L.a input)
m-query-coarse = doc (base number) (fold (unmarked _) (doc list-fo (unmarked _)))

inst-query-a-coarse = Instr.instrument m-query-coarse emp D-query ∅

------------------------------------------------------------------------
-- Flattening example: y * (x + y) with the sum marked.

t-mm : (emp ▸ base number ▸ base number) ⊢ base number
t-mm = bop mult (bop add (var zero ∷ var (succ zero) ∷ []) ∷ var zero ∷ [])

m-mm : Marked t-mm
m-mm = bop (doc (base number) (unmarked _) ∷ unmarked _ ∷ [])

γ-mm : Env (emp ▸ base number ▸ base number)
γ-mm = emp · const 0ℚ · const 1ℚ

run-mm = Tot.fundamental t-mm γ-mm ((tt , tt) , tt)

inst-mm = Instr.instrument m-mm (emp · const · const)
            (proj₁ (proj₂ (proj₂ run-mm))) ∅

------------------------------------------------------------------------
-- Moving average with window two: adjacent outputs share an input.

half : ℚ
half = + 1 / 2

γ-mavg : Env (emp ▸ base number [×] (base number [×] (base number [×] base number)))
γ-mavg = emp · pair (const 1ℚ) (pair (const (+ 2 / 1)) (pair (const (+ 4 / 1)) (const (+ 8 / 1))))

run-mavg = Tot.fundamental (Dep.mavg half) γ-mavg (tt , tt , tt , tt , tt)

D-mavg = proj₁ (proj₂ (proj₂ run-mavg))

inst-mavg-full =
  Instr.instrument (marked-all (Dep.mavg half))
    (emp · pair const (pair const (pair const const)))
    D-mavg ∅

-- Coarse marking: eta-expanded so the input is evaluated once, giving a single width-4
-- intermediate; the one edge to the output carries the full dependency relation.
mavg-coarse-term : emp ▸ base number [×] (base number [×] (base number [×] base number))
                   ⊢ base number [×] (base number [×] base number)
mavg-coarse-term = app (lam (Dep.mavg-body half (var zero))) (var zero)

m-mavg-coarse : Marked mavg-coarse-term
m-mavg-coarse =
  doc (base number [×] (base number [×] base number))
    (app (lam (unmarked _))
         (doc (base number [×] (base number [×] (base number [×] base number))) (var zero)))

run-mavg-coarse = Tot.fundamental mavg-coarse-term γ-mavg (tt , tt , tt , tt , tt)

inst-mavg-coarse =
  Instr.instrument m-mavg-coarse
    (emp · pair const (pair const (pair const const)))
    (proj₁ (proj₂ (proj₂ run-mavg-coarse))) ∅
