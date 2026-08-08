{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- The layout matches graph-viz.dump-rooted-tables, so the two baselines can be diffed against each
-- other. Run from the approx-diff repository root.
module graph-viz.dump-free-tables where

open import IO
open import IO.Finite using (writeFile)
open import Data.String using (String; _++_)
open import Data.Product using (_×_; _,_)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.List using (List; []; _∷_; map) renaming (foldr to foldrL)
open import Data.Vec using (Vec; toList; tabulate)
open import Data.Fin using (Fin)
open import Level using (0ℓ)
import two
import matrix
open import example.free-dependency using (dep-l; dep-r; dep-test)
open import example.free-runs
  using (dep; dep-const; dep-length; dep-fold0; dep-case0; dep-tag; dep-map; dep-filter)
import three
import example.free-runs-three

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

  module TM3 = matrix.Mat three.semiring

  bit3 : three.Three → String
  bit3 three.O = "0"
  bit3 three.C = "c"
  bit3 three.D = "d"

  table3 : ∀ {m n} → TM3.Matrix m n → String
  table3 M =
    foldrL (λ r s → r ++ "\n" ++ s) ""
      (map (λ v → foldrL _++_ "" (map bit3 (toList v)))
           (toList (tabulate (λ i → tabulate (λ j → M i j)))))

t-case-left t-case-right t-test t-const t-fold0 t-tag t-case0 t-length t-query t-map t-map3
  t-cond3 t-filter t-filter3 t-eq3 : String
t-case-left  = table dep-l
t-case-right = table dep-r
t-test       = table dep-test
t-const      = table dep-const
t-fold0      = table dep-fold0
t-tag        = table dep-tag
t-case0      = table dep-case0
t-length     = table dep-length
t-query      = table dep
t-map        = table dep-map
t-map3       = table3 example.free-runs-three.dep-map
t-cond3      = table3 example.free-runs-three.dep-cond
t-filter     = table dep-filter
t-filter3    = table3 example.free-runs-three.dep-filter
t-eq3        = table3 example.free-runs-three.dep-eq

contents : String
contents =
  "case-left\n"  ++ t-case-left ++
  "case-right\n" ++ t-case-right ++
  "case-test\n" ++ t-test ++
  "list-query\n" ++ t-query ++
  "list-map\n" ++ t-map ++
  "list-map-three\n" ++ t-map3 ++
  "cond-three\n" ++ t-cond3 ++
  "filter\n" ++ t-filter ++
  "filter-three\n" ++ t-filter3 ++
  "eq-three\n" ++ t-eq3 ++
  "const\n" ++ t-const ++
  "length\n" ++ t-length ++
  "fold0\n" ++ t-fold0 ++
  "case0\n" ++ t-case0 ++
  "tag\n" ++ t-tag

main : Main
main = run (writeFile "test-baselines/free-dependency.txt" contents)
