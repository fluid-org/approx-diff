{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- Profiling target: the width-driven single entry (pair-of-pairs payload, depth 2) behind a cheap
-- pair-payload anchor, so the cost-centre profile is dominated by the stage whose growth we are
-- attributing. Compile with GHC profiling and run under +RTS -p.
module graph-viz.probe-prof where

open import IO
open import IO.Finite using (writeFile)
open import Data.String using (String; _++_)
open import Data.Product using (_×_) renaming (_,_ to _,'_)
import Data.Fin as Fin
open Fin using (Fin)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Level using (0ℓ; lift)
open import Data.Rational using (0ℚ; 1ℚ)
open import prop-setoid using (Setoid)
import label
import two
import example.primitives as EP
open import example.rooted-runs using (length-term; query-ctxt-fo; module model; module interp)
open import graph-viz.probe-scaling using (pp-ctxt-fo; len-pp; γpp2; unit-ctxt-fo; len-u; γu3)
open import language-syntax EP.Sig using (base)

private
  module T = model.Fam⟨𝒞⟩μ.Tree interp.∅𝒞

  bit : two.Two → String
  bit two.O = "0"
  bit two.I = "1"

γp2' : Setoid.Carrier (interp.𝒞⟦ query-ctxt-fo ⟧ctxt .model.Fam⟨𝒞⟩μ.idx)
γp2' =
  lift tt ,'
  T.sup (inj₂ ((label.a ,' 0ℚ) ,'
  T.sup (inj₂ ((label.b ,' 1ℚ) ,'
  T.sup (inj₁ (lift tt))))))

abstract
  anchor : String
  anchor = bit (interp.readback.dep-mat query-ctxt-fo (base EP.number) length-term γp2'
                  Fin.zero Fin.zero)

  wide : String
  wide = bit (interp.readback.dep-mat pp-ctxt-fo (base EP.number) len-pp γpp2
                Fin.zero Fin.zero)

  deep : String
  deep = bit (interp.readback.dep-mat unit-ctxt-fo (base EP.number) len-u γu3
                Fin.zero Fin.zero)

main : Main
main =
  run (writeFile "/tmp/prof-anchor.txt" anchor >>
       writeFile "/tmp/prof-wide.txt" wide >>
       writeFile "/tmp/prof-deep.txt" deep)
