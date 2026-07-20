{-# OPTIONS --prop --postfix-projections --safe #-}

-- Instrumented runs at the Boolean model: golden and flattening tests.
module example.instrument-boolean where

open import Data.Fin using (Fin; splitAt; toℕ)
open import Data.List using (List; []; _∷_; concatMap; allFin)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import every using ([]; _∷_)
import label as L
import two
import matrix

open import example.signature ℚ
  using (Sig; sort; number; label; op; lit; add; mult; lbl; rel; equal-label)
open import example.relation-boolean
  using (module Alg-inst; module Tot; module TotOp;
         module Instr; module InstrOp)
import example.dependency as Dep
open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.evaluation Sig Alg-inst.Alg
  using (Env; emp; _·_; const)
open import language-operational.evaluation-mat Sig Alg-inst.Alg (λ s → Dep.FO𝟚.width (Dep.sort-approx s))
  using (width)
open import language-operational.marking Sig
open import example.trace-boolean using (elem; query; input; D-query)
open Instr

private
  module M𝟚 = matrix.Mat two.semiring

------------------------------------------------------------------------
-- Collapse: eliminate the intermediates from the domain, most recent first.

elim-mat : ∀ (g n w : ℕ) → M𝟚.Matrix w (g + n) → M𝟚.Matrix (g + (n + w)) (g + n)
elim-mat g n w Sm r c with splitAt g r
... | inj₁ a = M𝟚.I (a Data.Fin.↑ˡ n) c
... | inj₂ b with splitAt n b
...   | inj₁ d = M𝟚.I (g Data.Fin.↑ʳ d) c
...   | inj₂ x = Sm x c

collapse : ∀ {g n t} → Seq g n → M𝟚.Matrix t (g + n) → M𝟚.Matrix t g
collapse {g} ∅ A i j = A i (j Data.Fin.↑ˡ 0)
collapse {g} (snoc {n} Φ w Sm) A = collapse Φ (A M𝟚.∘ elim-mat g n (width w) Sm)

------------------------------------------------------------------------
-- Boolean matrices as entry lists, for refl-comparable goldens.

ents : ∀ {m n} → M𝟚.Matrix m n → List (ℕ × ℕ)
ents {m} {n} A =
  concatMap (λ i → concatMap (λ j → keep i j (A i j)) (allFin n)) (allFin m)
  where
    keep : ∀ {m n} → Fin m → Fin n → two.Two → List (ℕ × ℕ)
    keep i j two.I = (toℕ i , toℕ j) ∷ []
    keep i j two.O = []

------------------------------------------------------------------------
-- Flattening on an open term: y * (x + y) with the sum marked.

t-mm : (emp ▸ base number ▸ base number) ⊢ base number
t-mm = bop mult (bop add (var zero ∷ var (succ zero) ∷ []) ∷ var zero ∷ [])

m-mm : Marked t-mm
m-mm = bop (doc (base number) (unmarked _) ∷ unmarked _ ∷ [])

γ-mm : Env (emp ▸ base number ▸ base number)
γ-mm = emp · const 0ℚ · const 1ℚ

run-mm = TotOp.fundamental t-mm γ-mm ((tt , tt) , tt)

inst-mm = InstrOp.instrument m-mm (emp · const · const)
            (proj₁ (proj₂ (proj₂ run-mm))) ∅

flat-mm : ents (collapse (proj₁ (proj₂ (proj₂ inst-mm))) (proj₂ (proj₂ (proj₂ inst-mm))))
          ≡ ents (proj₁ (proj₂ run-mm))
flat-mm = refl

------------------------------------------------------------------------
-- The query example: mark each input entry and the fold body's result.

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

inst-query = InstrOp.instrument m-query emp D-query ∅

-- Total width of the intermediates: three entries and four fold steps.
width-query : proj₁ (proj₂ inst-query) ≡ 7
width-query = refl

-- Erasure: the unmarked run adds no intermediates.
erasure-query : proj₁ (proj₂ (InstrOp.instrument (unmarked _) emp D-query ∅)) ≡ 0
erasure-query = refl
