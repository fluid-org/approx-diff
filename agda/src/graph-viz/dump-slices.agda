{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- Writes the dependency slices as partial values of the input list, one line per output position,
-- compared against a versioned baseline; run from the paper repository root. Rows are read from
-- the same readback matrices as the bit tables and interpreted over the operational value fibre,
-- which agrees with the model fibre positionwise; the fixedness witness comes from spine closure,
-- the identity on these rows, until the row-fixedness of absorbed presentations replaces it.
module graph-viz.dump-slices where

open import IO
open import IO.Finite using (writeFile)
open import Data.String using (String; _++_)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.List using (List; []; _∷_) renaming (foldr to foldrL)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; toℕ)
open import Data.Vec using (Vec; toList; tabulate)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; ↥_; ↧_)
import Data.Integer.Show as ℤ-Show
open import Level using (0ℓ)
import two
import matrix
import label
open import primitives using (Primitives)
import example.primitives as EP
open import example.rooted-runs
  using (dep; dep-const; dep-length; dep-fold0; dep-case0; dep-tag)

open import language-syntax EP.Sig using (type; base; list; _[×]_)
open import language-operational.evaluation EP.Sig EP.primitives using (Val)
open Val
open import language-operational.value-fibre EP.Sig EP.primitives using (pos)
open import language-operational.partial-value EP.Sig EP.primitives using (spine-close; pval)
open import language-operational.render-partial EP.Sig EP.primitives
open Primitives EP.primitives using (sort-val)

private
  module TM = matrix.Mat two.semiring

-- The operational input value mirroring γ-input: three entries, two under the queried label.
elemT : type 0
elemT = base EP.label [×] base EP.number

listT : type 0
listT = list elemT

el : label.label → ℚ → Val elemT
el l n = pair (const l) (const n)

infixr 20 _∷ᵥ_
_∷ᵥ_ : Val elemT → Val listT → Val listT
x ∷ᵥ xs = roll (inr (pair x xs))

nilᵥ : Val listT
nilᵥ = roll (inl unit)

γ-val : Val listT
γ-val = el label.a 0ℚ ∷ᵥ el label.b 1ℚ ∷ᵥ el label.a 1ℚ ∷ᵥ nilᵥ

-- Renderings of the example constants.
show-ℚ : ℚ → String
show-ℚ q = ℤ-Show.show (↥ q) ++ "/" ++ ℤ-Show.show (↧ q)

show-label : label.label → String
show-label label.a = "a"
show-label label.b = "b"
show-label label.c = "c"
show-label label.d = "d"

showC : ∀ {s} → sort-val s → String
showC {EP.number} q = show-ℚ q
showC {EP.label}  l = show-label l

private
  lookupO : List two.Two → ℕ → two.Two
  lookupO []       _       = two.O
  lookupO (b ∷ _)  zero    = b
  lookupO (_ ∷ bs) (suc n) = lookupO bs n

  -- A matrix row, read over the operational fibre through a length-safe lookup; the two layouts
  -- agree positionwise, and a misalignment would surface in the rendered baseline.
  render-row : List two.Two → String
  render-row bits =
    show-pval (λ {s} c → showC {s} c)
      (pval γ-val (spine-close (pos γ-val) (λ i → lookupO bits (toℕ i))))

  slice : ∀ {m n} → TM.Matrix m n → String
  slice {m} M =
    foldrL (λ r s → r ++ "\n" ++ s) ""
      (toList (tabulate {n = m} (λ q → render-row (toList (tabulate (M q))))))

contents : String
contents =
  "list-query\n" ++ slice dep ++
  "const\n" ++ slice dep-const ++
  "length\n" ++ slice dep-length ++
  "fold0\n" ++ slice dep-fold0 ++
  "case0\n" ++ slice dep-case0 ++
  "tag\n" ++ slice dep-tag

main : Main
main = run (writeFile "approx-diff/test-baselines/rooted-slices.txt" contents)
