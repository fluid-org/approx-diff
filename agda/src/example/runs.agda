{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (0ℓ)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)

open import Data.Rational using (ℚ)
module example.runs {A : Setoid 0ℓ 0ℓ} (as-weight : ℚ → Setoid.Carrier A) (S : CommutativeSemiring A)
                    (ctrl-weight : Setoid.Carrier A) where

open import Data.Rational using (½; 1ℚ; -_)
open import signature.example.interpretation as-weight S using (Sig; interpretation)
open import example.programs
open import example.inputs as-weight S ctrl-weight
open import language-syntax Sig using (ctxt; type; _⊢_)
open import language-operational.evaluation Sig S interpretation ctrl-weight using (Env)

record Run : Set where
  constructor run
  field
    {Γ}  : ctxt
    {τ}  : type 0
    term : Γ ⊢ τ
    env  : Env Γ

open Run public

filter-sum-run const-run length-run fold0-run case0-run tag-run : Run
filter-sum-run  = run (filter-sum "a") γ-query
const-run  = run const-term γ-query
length-run = run length-term γ-query
fold0-run  = run fold0-term γ-query
case0-run  = run case0-term γ-query
tag-run    = run tag-term γ-query

case-l-run case-r-run test-run : Run
case-l-run = run case-term γ-case-l
case-r-run = run case-term γ-case-r
test-run   = run test-term γ-test

mult-run : Run
mult-run = run mult-ex γ-mult

add-mul-run : Run
add-mul-run = run add-mul γ-add-mul

case-inl-run : Run
case-inl-run = run case-inl γ-case-inl

score-run : Run
score-run = run (score (- 1ℚ)) γ-score

mavg-run : Run
mavg-run = run (mavg ½) γ-mavg

total-run sum-mul-run rose-run : Run
total-run   = run (total "a") γ-total
sum-mul-run = run sum-mul γ-sum-mul
rose-run    = run rose-query γ-rose

map-run filter-run cond-run eq-run adjacent-sums-run merge-run : Run
map-run    = run map-term γ-nums
adjacent-sums-run = run adjacent-sums-term γ-adjacent-sums
merge-run  = run merge-term γ-merge
filter-run = run filter-term γ-filter
cond-run   = run cond-term γ-cond
eq-run     = run eq-term γ-eq
