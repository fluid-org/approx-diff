{-# OPTIONS --prop --postfix-projections --safe #-}

-- Traces and dependence graphs at the Boolean model, with golden tests.
module example.trace-boolean where

open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ)
open import Data.String using (String)
open import Data.Unit.Polymorphic using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import every using ([]; _∷_)
import label as L
import two

open import example.signature ℚ
  using (Sig; sort; number; label; op; lit; add; mult; lbl; rel; equal-label)
open import example.relation-boolean
  using (module Tot)
import example.dependency as Dep
open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.evaluation Sig Dep.primitives
  using (Env; emp; _·_; const)

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

open import language-operational.trace Sig Dep.primitives show-op

------------------------------------------------------------------------
-- Addition of two variables.

M-add : (emp ▸ base number ▸ base number) ⊢ base number
M-add = bop add (var zero ∷ var (succ zero) ∷ [])

run-add = Tot.fundamental M-add (emp · const 0ℚ · const 1ℚ) ((tt , tt) , tt)

D-add = proj₁ (proj₂ (proj₂ run-add))

------------------------------------------------------------------------
-- Multiplication of two variables, at (0, 1). The derivative of x * y is [y, x], so the result
-- depends on x (whose coefficient is y = 1) and not on y (whose coefficient is x = 0).

M-mult : (emp ▸ base number ▸ base number) ⊢ base number
M-mult = bop mult (var zero ∷ var (succ zero) ∷ [])

run-mult = Tot.fundamental M-mult (emp · const 0ℚ · const 1ℚ) ((tt , tt) , tt)

D-mult = proj₁ (proj₂ (proj₂ run-mult))

------------------------------------------------------------------------
-- Sum the numbers paired with a given label in a list of (label, number) pairs, fused into a single fold.

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

------------------------------------------------------------------------
-- Golden tests.

trace-add : show-eval D-add ≡ "(bop add ((var 0) (var 1)))"
trace-add = refl

trace-query : show-eval D-query ≡
  "(fold (roll (inr (pair (pair (bop lbl-a ()) (bop lit ())) (roll (inr (pair (pair (bop lbl-b ()) (bop lit ())) (roll (inr (pair (pair (bop lbl-a ()) (bop lit ())) (roll (inl unit))))))))))) (rec (inr (pair (pair - -) (rec (inr (pair (pair - -) (rec (inr (pair (pair - -) (rec (inl -) (case-l (var 0) (bop lit ()))))) (case-r (var 0) (case-l (brel ((fst (fst (var 0))) (bop lbl-a ()))) (bop add ((snd (fst (var 1))) (snd (var 1))))))))) (case-r (var 0) (case-r (brel ((fst (fst (var 0))) (bop lbl-a ()))) (snd (var 1))))))) (case-r (var 0) (case-l (brel ((fst (fst (var 0))) (bop lbl-a ()))) (bop add ((snd (fst (var 1))) (snd (var 1))))))))"
trace-query = refl

