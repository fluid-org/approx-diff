{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- Writes the rooted dependency tables as text, compared against a versioned baseline; run from the
-- paper repository root. The matrices are the abstract readbacks of example.rooted-dependency,
-- evaluated by the compiled program rather than by the typechecker.
module graph-viz.dump-rooted-tables where

open import IO
open import IO.Finite using (writeFile)
open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_; map) renaming (foldr to foldrL)
open import Data.Vec using (Vec; toList; tabulate)
open import Data.Fin using (Fin)
open import Level using (0ℓ)
import two
import matrix
open import example.rooted-dependency using (dep-l; dep-r)
open import example.rooted-runs using (dep; dep-const; dep-length; dep-fold0; dep-case0; dep-tag)

private
  module TM = matrix.Mat two.semiring

  bit : two.Two → String
  bit two.O = "0"
  bit two.I = "1"

  row : ∀ {n} → Vec two.Two n → String
  row v = foldrL _++_ "" (map bit (toList v))

  rows : ∀ {m n} → Vec (Vec two.Two n) m → String
  rows vs = foldrL (λ r s → r ++ "\n" ++ s) "" (map row (toList vs))

  table : ∀ {m n} → TM.Matrix m n → String
  table M = rows (tabulate (λ i → tabulate (λ j → M i j)))

contents : String
contents =
  "case-left\n"  ++ table dep-l ++
  "case-right\n" ++ table dep-r ++
  "list-query\n" ++ table dep ++
  "const\n" ++ table dep-const ++
  "length\n" ++ table dep-length ++
  "fold0\n" ++ table dep-fold0 ++
  "case0\n" ++ table dep-case0 ++
  "tag\n" ++ table dep-tag

main : Main
main = run (writeFile "approx-diff/test-baselines/rooted-dependency.txt" contents)
