{-# OPTIONS --prop --postfix-projections --safe #-}

-- Traces and dependence graphs at the Boolean model, with golden tests.
module example.trace-boolean where

open import Data.List using (List; []; _∷_; applyUpTo)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ)
open import Data.String using (String)
open import Data.Unit.Polymorphic using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import every using ([]; _∷_)
import label as L
import two

open import example.signature ℚ
  using (Sig; sort; number; label; approx; op; lit; add; mult; lbl;
         approx-unit; approx-mult; rel; equal-label)
open import example.relation-boolean
  using (sort-width; op-mat; module Alg-inst; module Tot; module TotOp)
open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.evaluation Sig Alg-inst.Alg
  using (Env; emp; _·_; const)
open import language-operational.evaluation-mat Sig Alg-inst.Alg two.semiring sort-width
  using (width-env; module WithOpMats)
open WithOpMats op-mat using (_,_⇓_[_])

show-lbl : L.label → String
show-lbl L.a = "a"
show-lbl L.b = "b"
show-lbl L.c = "c"
show-lbl L.d = "d"

show-op : ∀ {is o} → op is o → String
show-op (lit n)     = "lit"
show-op add         = "add"
show-op mult        = "mult"
show-op (lbl l)     = Data.String._++_ "lbl-" (show-lbl l)
show-op approx-unit = "approx-unit"
show-op approx-mult = "approx-mult"

open import language-operational.trace Sig Alg-inst.Alg sort-width show-op

dep-graph : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} →
            γ , t ⇓ v [ R ] → List Edge
dep-graph {γ = γ} D =
  proj₂ (proj₂ (edges D (applyUpTo (λ i → i) (width-env γ)) (width-env γ)))

------------------------------------------------------------------------
-- Addition of two variables.

M-add : (emp ▸ base number ▸ base number) ⊢ base number
M-add = bop add (var zero ∷ var (succ zero) ∷ [])

run-add = TotOp.fundamental M-add (emp · const 0ℚ · const 1ℚ) ((tt , tt) , tt)

D-add = proj₁ (proj₂ (proj₂ run-add))

------------------------------------------------------------------------
-- Sum the numbers paired with a given label in a list of (label, number)
-- pairs, fused into a single fold.

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

run-query = TotOp.eval (query L.a input)

D-query = proj₂ (proj₂ run-query)

------------------------------------------------------------------------
-- Golden tests.

trace-add : show-eval D-add ≡ "(bop add ((var 0) (var 1)))"
trace-add = refl

graph-add : showGraph (dep-graph D-add) ≡
  "(var: 1, 2), (var: 0, 3), (add: 2, 4), (add: 3, 4)"
graph-add = refl

trace-query : show-eval D-query ≡
  "(fold (roll (inr (pair (pair (bop lbl-a ()) (bop lit ())) (roll (inr (pair (pair (bop lbl-b ()) (bop lit ())) (roll (inr (pair (pair (bop lbl-a ()) (bop lit ())) (roll (inl unit))))))))))) (rec (inr (pair (pair - -) (rec (inr (pair (pair - -) (rec (inr (pair (pair - -) (rec (inl -) (case-l (var 0) (bop lit ()))))) (case-r (var 0) (case-l (brel ((fst (fst (var 0))) (bop lbl-a ()))) (bop add ((snd (fst (var 1))) (snd (var 1))))))))) (case-r (var 0) (case-r (brel ((fst (fst (var 0))) (bop lbl-a ()))) (snd (var 1))))))) (case-r (var 0) (case-l (brel ((fst (fst (var 0))) (bop lbl-a ()))) (bop add ((snd (fst (var 1))) (snd (var 1))))))))"
trace-query = refl

graph-query : showGraph (dep-graph D-query) ≡
  "(pair: 0, 1), (pair: 2, 3), (pair: 4, 5), (pair: 5, 6), (inr: 6, 7), (roll: 7, 8), (pair: 3, 9), (pair: 8, 10), (inr: 9, 11), (inr: 10, 12), (roll: 11, 13), (roll: 12, 14), (pair: 1, 15), (pair: 13, 16), (pair: 14, 17), (inr: 15, 18), (inr: 16, 19), (inr: 17, 20), (roll: 18, 21), (roll: 19, 22), (roll: 20, 23), (case-l: 24, 25), (rec: 25, 26), (var: 23, 27), (var: 26, 28), (var: 27, 29), (var: 28, 30), (fst: 29, 31), (var: 27, 32), (var: 28, 33), (fst: 32, 34), (snd: 34, 35), (var: 27, 36), (var: 28, 37), (snd: 37, 38), (add: 35, 39), (add: 38, 39), (case-l: 39, 40), (case-r: 40, 41), (rec: 41, 42), (var: 22, 43), (var: 42, 44), (var: 43, 45), (var: 44, 46), (fst: 45, 47), (var: 43, 48), (var: 44, 49), (snd: 49, 50), (case-r: 50, 51), (case-r: 51, 52), (rec: 52, 53), (var: 21, 54), (var: 53, 55), (var: 54, 56), (var: 55, 57), (fst: 56, 58), (var: 54, 59), (var: 55, 60), (fst: 59, 61), (snd: 61, 62), (var: 54, 63), (var: 55, 64), (snd: 64, 65), (add: 62, 66), (add: 65, 66), (case-l: 66, 67), (case-r: 67, 68), (rec: 68, 69)"
graph-query = refl
