{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- Profiling target: the length readback alone, over one- and two-element lists, written to
-- scratch files in input order so the timestamps show the growth in evaluation cost with list
-- depth. Compile with GHC profiling and run under +RTS -p to attribute the cost.
module graph-viz.profile-length where

open import IO
open import IO.Finite using (writeFile)
open import Data.String using (String; _++_)
open import Data.Product using (_×_) renaming (_,_ to _,'_)
open import Data.List using (List; []; _∷_; map) renaming (foldr to foldrL)
open import Data.Vec using (Vec; toList; tabulate)
open import Data.Fin using (Fin)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤p; tt to ttp)
open import Level using (0ℓ; lift)
open import Data.Rational using (0ℚ; 1ℚ)
open import prop-setoid using (Setoid)
import label
import two
import matrix
import example.primitives as EP
open import example.rooted-runs
  using (length-term; query-ctxt-fo; module model; module interp)
open import language-syntax EP.Sig using (base)

private
  module TM = matrix.Mat two.semiring
  module T = model.Fam⟨𝒞⟩μ.Tree interp.∅𝒞

  bit : two.Two → String
  bit two.O = "0"
  bit two.I = "1"

  row : ∀ {n} → Vec two.Two n → String
  row v = foldrL _++_ "" (map bit (toList v))

  rows : ∀ {m n} → Vec (Vec two.Two n) m → String
  rows vs = foldrL (λ r s → r ++ "\n" ++ s) "" (map row (toList vs))

  table : ∀ {m n} → TM.Matrix m n → String
  table M = rows (tabulate (λ i → tabulate (λ j → M i j)))

γ1 γ2 : Setoid.Carrier (interp.𝒞⟦ query-ctxt-fo ⟧ctxt .model.Fam⟨𝒞⟩μ.idx)
γ1 =
  lift tt ,'
  T.sup (inj₂ ((label.a ,' 0ℚ) ,'
  T.sup (inj₁ (lift tt))))
γ2 =
  lift tt ,'
  T.sup (inj₂ ((label.a ,' 0ℚ) ,'
  T.sup (inj₂ ((label.b ,' 1ℚ) ,'
  T.sup (inj₁ (lift tt))))))

abstract
  dep1 dep2 : String
  dep1 = table (interp.readback.dep-mat query-ctxt-fo (base EP.number) length-term γ1)
  dep2 = table (interp.readback.dep-mat query-ctxt-fo (base EP.number) length-term γ2)

main : Main
main =
  run (writeFile "/tmp/prof-length-1.txt" dep1 >>
       writeFile "/tmp/prof-length-2.txt" dep2)
