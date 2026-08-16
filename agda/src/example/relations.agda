{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (0ℓ)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)

-- The example programs at their inputs, and the model's output and relation of each at the
-- interpretation of the input.
module example.relations {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A) (elim-weight : Setoid.Carrier A) where

import label
import matrix
import ho-model
open import signature.example.interpretation S using (Sig; interpretation; number)
open import example.programs
open import example.inputs S elim-weight
open import language-syntax Sig using (ctxt; type; first-order-ctxt; first-order; _⊢_; base; unit; _[+]_)
open import language-operational.evaluation Sig S interpretation elim-weight using (Val; Env)
open import value-interpretation S elim-weight Sig interpretation using (⟦_⟧env; ⟦_⟧val⁻¹)

module model = ho-model S elim-weight
module interp = model.interp Sig interpretation

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
model-input r = ⟦ r .Γ-fo ⟧env (r .env)

model-output : (r : Run) → Val (r .τ)
model-output r = ⟦ r .fo ⟧val⁻¹ (interp.dependency.out (r .Γ-fo) (r .fo) (r .term) (model-input r))

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

map-run filter-run cond-run eq-run : Run
map-run    = run map-ctxt-fo numlist-fo map-term γ-nums
filter-run = run filter-ctxt-fo numlist-fo filter-term γ-filter
cond-run   = run cond-ctxt-fo (base number) cond-term γ-cond
eq-run     = run eq-ctxt-fo (unit [+] unit) eq-term γ-eq
