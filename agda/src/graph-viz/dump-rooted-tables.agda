{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- Writes the rooted dependency tables as text, compared against a versioned baseline; run from the
-- paper repository root. The matrices are the abstract readbacks of example.rooted-dependency,
-- evaluated by the compiled program rather than by the typechecker.
module graph-viz.dump-rooted-tables where

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
open import example.rooted-dependency using (dep-l; dep-r; dep-test)
open import example.rooted-runs using (dep; dep-const; dep-length; dep-fold0; dep-case0; dep-tag; dep-map)
import three
import example.rooted-runs-three

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

-- Each table is a top-level definition so the per-example scratch files and the combined baseline
-- share one evaluation; the scratch files are written in order as computed, so their timestamps
-- attribute the evaluation cost per example.
t-case-left t-case-right t-test t-const t-fold0 t-tag t-case0 t-length t-query t-map t-map3 : String
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
t-map3       = table3 example.rooted-runs-three.dep-map

tables : List (String × String)
tables =
  ("case-left"  , t-case-left)
  ∷ ("case-right" , t-case-right)
  ∷ ("case-test"  , t-test)
  ∷ ("const"      , t-const)
  ∷ ("fold0"      , t-fold0)
  ∷ ("tag"        , t-tag)
  ∷ ("case0"      , t-case0)
  ∷ ("length"     , t-length)
  ∷ ("list-query" , t-query)
  ∷ ("list-map"   , t-map)
  ∷ ("list-map-three" , t-map3)
  ∷ []

contents : String
contents =
  "case-left\n"  ++ t-case-left ++
  "case-right\n" ++ t-case-right ++
  "case-test\n" ++ t-test ++
  "list-query\n" ++ t-query ++
  "list-map\n" ++ t-map ++
  "list-map-three\n" ++ t-map3 ++
  "const\n" ++ t-const ++
  "length\n" ++ t-length ++
  "fold0\n" ++ t-fold0 ++
  "case0\n" ++ t-case0 ++
  "tag\n" ++ t-tag

write-each : List (String × String) → IO {0ℓ} ⊤
write-each []             = pure tt
write-each ((n , s) ∷ ts) =
  writeFile ("approx-diff/test-baselines/rooted-" ++ n ++ ".part") s >> write-each ts

main : Main
main =
  run (write-each tables >>
       writeFile "approx-diff/test-baselines/rooted-dependency.txt" contents)
