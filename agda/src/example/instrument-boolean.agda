{-# OPTIONS --prop --postfix-projections --safe #-}

-- Instrumented runs at the Boolean model: golden and flattening tests.
module example.instrument-boolean where

open import Data.Fin using (Fin; splitAt; toℕ)
open import Data.List using (List; []; _∷_; _++_; length; concatMap; allFin)
import Data.Nat
open import Data.Nat using (ℕ; _+_; _∸_; _<ᵇ_)
open import Data.Bool using () renaming (if_then_else_ to ifᵇ_then_else_)
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
  using (module Tot; module Instr)
import example.dependency as Dep
open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.evaluation Sig Dep.primitives
  using (Env; emp; _·_; const; width)
open import language-operational.marking Sig
import label as L
open import example.trace-boolean using (elem; query; input; D-query; M-add; D-add; M-mult; D-mult)
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

run-mm = Tot.fundamental t-mm γ-mm ((tt , tt) , tt)

inst-mm = Instr.instrument m-mm (emp · const · const)
            (proj₁ (proj₂ (proj₂ run-mm))) ∅

flat-mm : ents (collapse (proj₁ (proj₂ (proj₂ inst-mm))) (proj₂ (proj₂ (proj₂ inst-mm))))
          ≡ ents (proj₁ (proj₂ run-mm))
flat-mm = refl

------------------------------------------------------------------------
-- Dependence graph: one vertex per entry of Φ, an edge i → j when the block of S_j at the
-- positions of entry i is non-empty.

private
  -- Index of the entry containing an intermediate position, given the widths of the entries.
  locate : List ℕ → ℕ → ℕ
  locate []       _ = 0
  locate (w ∷ ws) p = ifᵇ p <ᵇ w then 0 else Data.Nat.suc (locate ws (p ∸ w))

  entry-ents : ∀ {g n} → Seq g n → List (ℕ × List (ℕ × ℕ))
  entry-ents ∅             = []
  entry-ents (snoc Φ w Sm) = entry-ents Φ ++ (width w , ents Sm) ∷ []

dep-edges : ∀ {g n} → Seq g n → List (ℕ × ℕ)
dep-edges {g} Φ = go [] (entry-ents Φ)
  where
  edge : List ℕ → ℕ × ℕ → List (ℕ × ℕ)
  edge ws (_ , c) =
    ifᵇ c <ᵇ g then [] else (locate ws (c ∸ g) , length ws) ∷ []

  go : List ℕ → List (ℕ × List (ℕ × ℕ)) → List (ℕ × ℕ)
  go ws []               = []
  go ws ((w , es) ∷ Φe) = concatMap (edge ws) es ++ go (ws ++ w ∷ []) Φe

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

inst-query = Instr.instrument m-query emp D-query ∅

-- Total width of the intermediates: three entries and four fold steps.
width-query : proj₁ (proj₂ inst-query) ≡ 7
width-query = refl

-- The dependence graph of the marked run.
dep-graph-query : dep-edges (proj₁ (proj₂ (proj₂ inst-query))) ≡
  ((2 , 4) ∷ (3 , 4) ∷ (4 , 5) ∷ (0 , 6) ∷ (5 , 6) ∷ [])
dep-graph-query = refl

-- Full evaluation graphs: the everything-marked instance of the same construction.

inst-add-full = Instr.instrument (marked-all M-add) (emp · const · const) D-add ∅

dep-graph-add-full : dep-edges (proj₁ (proj₂ (proj₂ inst-add-full))) ≡ ((0 , 2) ∷ (1 , 2) ∷ [])
dep-graph-add-full = refl

-- At (x , y) = (1 , 0) the derivative of x * y is [ 0 , 1 ]: the result depends on the second
-- argument only.
inst-mult-full = Instr.instrument (marked-all M-mult) (emp · const · const) D-mult ∅

dep-graph-mult-full : dep-edges (proj₁ (proj₂ (proj₂ inst-mult-full))) ≡ ((1 , 2) ∷ [])
dep-graph-mult-full = refl

inst-query-full = Instr.instrument (marked-all (query L.a input)) emp D-query ∅

-- Erasure: the unmarked run adds no intermediates.
erasure-query : proj₁ (proj₂ (Instr.instrument (unmarked _) emp D-query ∅)) ≡ 0
erasure-query = refl
