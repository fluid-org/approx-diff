{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (0ℓ)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)

-- The example programs at their inputs, and the model's output and relation of each at the
-- interpretation of the input.
open import Data.Rational using (ℚ)
module example.runs {A : Setoid 0ℓ 0ℓ} (as-weight : ℚ → Setoid.Carrier A) (S : CommutativeSemiring A)
                    (ctrl-weight : Setoid.Carrier A) where

import label
open import Data.Rational using (½; 1ℚ; -_)
import matrix
open import signature.example.interpretation as-weight S using (Sig; interpretation; number)
open import example.programs
open import example.inputs as-weight S ctrl-weight
open import language-syntax Sig using (ctxt; type; first-order-ctxt; first-order; _⊢_; base; unit; _[+]_; _[×]_)
open import language-operational.evaluation Sig S interpretation ctrl-weight using (Val; Env)
open import value-interpretation S ctrl-weight Sig interpretation using (env-idx; idx-val; module model; module interp)
open import categories using (Category)
open Category.Iso using (bwd)
open prop-setoid._⇒_ using (func)

private
  module M = matrix.Mat S

-- A program at an input, with the first-order witnesses of its context and result type.
record Run : Set where
  constructor run
  field
    {Γ}  : ctxt
    {τ}  : type 0
    Γ-fo : first-order-ctxt Γ
    fo   : first-order τ
    term : Γ ⊢ τ
    env  : Env Γ

open Run public

model-input : (r : Run) → Setoid.Carrier (interp.𝒞⟦ r .Γ-fo ⟧ctxt .model.Fam⟨𝒞⟩μ.idx)
model-input r = interp.⟦ r .Γ-fo ⟧ctxt-iso .bwd .model.Fam⟨𝒟⟩μ.idxf .func (env-idx (r .env))

model-output : (r : Run) → Val (r .τ)
model-output r = idx-val (r .fo) (interp.dependency.out (r .Γ-fo) (r .fo) (r .term) (model-input r))

model-of : (r : Run) →
           M.Matrix (interp.dependency.tgt (r .Γ-fo) (r .fo) (r .term) (model-input r))
                    (interp.dependency.src (r .Γ-fo) (r .fo) (r .term) (model-input r))
model-of r = interp.dependency.mat-of (r .Γ-fo) (r .fo) (r .term) (model-input r)

query-run const-run length-run fold0-run case0-run tag-run : Run
query-run  = run query-ctxt-fo (base number) (query label.a) γ-query
const-run  = run query-ctxt-fo (base number) const-term γ-query
length-run = run query-ctxt-fo (base number) length-term γ-query
fold0-run  = run query-ctxt-fo (base number) fold0-term γ-query
case0-run  = run query-ctxt-fo (base number) case0-term γ-query
tag-run    = run query-ctxt-fo (base number) tag-term γ-query

case-l-run case-r-run test-run : Run
case-l-run = run case-ctxt-fo (base number) case-term γ-case-l
case-r-run = run case-ctxt-fo (base number) case-term γ-case-r
test-run   = run test-ctxt-fo (base number) test-term γ-test

mult-run : Run
mult-run = run mult-ctxt-fo (base number) mult-ex γ-mult

score-run : Run
score-run = run score-ctxt-fo (base number) (score (- 1ℚ)) γ-score

mavg-run : Run
mavg-run = run mavg-ctxt-fo (base number [×] (base number [×] base number)) (mavg ½) γ-mavg

total-run sum-mul-run rose-run : Run
total-run   = run total-ctxt-fo (base number) (total label.a) γ-total
sum-mul-run = run sum-mul-ctxt-fo (base number) sum-mul γ-sum-mul
rose-run    = run rose-ctxt-fo (base number) rose-query γ-rose

map-run filter-run cond-run eq-run adjacent-sums-run merge-run : Run
map-run    = run map-ctxt-fo numlist-fo map-term γ-nums
adjacent-sums-run = run map-ctxt-fo numlist-fo adjacent-sums-term γ-adjacent-sums
merge-run  = run merge-ctxt-fo numlist-fo merge-term γ-merge
filter-run = run filter-ctxt-fo numlist-fo filter-term γ-filter
cond-run   = run cond-ctxt-fo (base number) cond-term γ-cond
eq-run     = run eq-ctxt-fo (unit [+] unit) eq-term γ-eq
