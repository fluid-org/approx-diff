{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- Scaling probe for the readback cost: depth against width. The unit-payload list isolates the
-- number of fold layers from the fibre dimension; the pair-of-pairs payload varies the dimension
-- at fixed depth. Stages write scratch files in cost order, so the timestamps attribute the cost
-- even when a later stage is killed.
module graph-viz.probe-scaling where

open import IO
open import IO.Finite using (writeFile)
open import Data.String using (String; _++_)
open import Data.Product using (_×_) renaming (_,_ to _,'_)
open import Data.List using (List; []; _∷_; map) renaming (foldr to foldrL)
open import Data.Vec using (Vec; toList; tabulate)
import Data.Fin as Fin
open Fin using (Fin)
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
open import every using ([]; _∷_)
open import language-syntax EP.Sig
  using (type; base; unit; _[+]_; _[×]_; var; μ; _⊢_; bop; fold; case; snd; zero;
         first-order; first-order-ctxt; emp; _,_)

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

-- Depth axis: list over the unit payload, so each level adds fold layers with minimal width.
unit-ctxt-fo : first-order-ctxt (emp , μ (unit [+] (unit [×] var Fin.zero)))
unit-ctxt-fo = emp , μ (unit [+] (unit [×] var Fin.zero))

len-u : (emp , μ (unit [+] (unit [×] var Fin.zero))) ⊢ base EP.number
len-u =
  fold (case (var zero)
          (bop (EP.lit 0ℚ) [])
          (bop EP.add ((bop (EP.lit 1ℚ) []) ∷ ((snd (var zero)) ∷ []))))
       (var zero)

γu1 γu2 γu3 γu4 : Setoid.Carrier (interp.𝒞⟦ unit-ctxt-fo ⟧ctxt .model.Fam⟨𝒞⟩μ.idx)
γu1 =
  lift tt ,'
  T.sup (inj₂ (lift tt ,'
  T.sup (inj₁ (lift tt))))
γu2 =
  lift tt ,'
  T.sup (inj₂ (lift tt ,'
  T.sup (inj₂ (lift tt ,'
  T.sup (inj₁ (lift tt))))))
γu3 =
  lift tt ,'
  T.sup (inj₂ (lift tt ,'
  T.sup (inj₂ (lift tt ,'
  T.sup (inj₂ (lift tt ,'
  T.sup (inj₁ (lift tt))))))))
γu4 =
  lift tt ,'
  T.sup (inj₂ (lift tt ,'
  T.sup (inj₂ (lift tt ,'
  T.sup (inj₂ (lift tt ,'
  T.sup (inj₂ (lift tt ,'
  T.sup (inj₁ (lift tt))))))))))

-- Width axis: list over a pair-of-pairs payload, doubling the payload width at fixed depth.
ppT : type 1
ppT = (base EP.label [×] base EP.number) [×] (base EP.label [×] base EP.number)

ppList : type 0
ppList = μ (unit [+] (ppT [×] var Fin.zero))

pp-ctxt-fo : first-order-ctxt (emp , ppList)
pp-ctxt-fo =
  emp , μ (unit [+] (((base EP.label [×] base EP.number)
                       [×] (base EP.label [×] base EP.number)) [×] var Fin.zero))

len-pp : (emp , ppList) ⊢ base EP.number
len-pp =
  fold (case (var zero)
          (bop (EP.lit 0ℚ) [])
          (bop EP.add ((bop (EP.lit 1ℚ) []) ∷ ((snd (var zero)) ∷ []))))
       (var zero)

γpp2 : Setoid.Carrier (interp.𝒞⟦ pp-ctxt-fo ⟧ctxt .model.Fam⟨𝒞⟩μ.idx)
γpp2 =
  lift tt ,'
  T.sup (inj₂ (((label.a ,' 0ℚ) ,' (label.b ,' 1ℚ)) ,'
  T.sup (inj₂ (((label.a ,' 1ℚ) ,' (label.b ,' 0ℚ)) ,'
  T.sup (inj₁ (lift tt))))))

-- Anchors: the pair payload at depths 1 and 2, matching profile-length.
γp1 γp2 : Setoid.Carrier (interp.𝒞⟦ query-ctxt-fo ⟧ctxt .model.Fam⟨𝒞⟩μ.idx)
γp1 =
  lift tt ,'
  T.sup (inj₂ ((label.a ,' 0ℚ) ,'
  T.sup (inj₁ (lift tt))))
γp2 =
  lift tt ,'
  T.sup (inj₂ ((label.a ,' 0ℚ) ,'
  T.sup (inj₂ ((label.b ,' 1ℚ) ,'
  T.sup (inj₁ (lift tt))))))

abstract
  u1 u2 u3 u4 : String
  u1 = table (interp.readback.dep-mat unit-ctxt-fo (base EP.number) len-u γu1)
  u2 = table (interp.readback.dep-mat unit-ctxt-fo (base EP.number) len-u γu2)
  u3 = table (interp.readback.dep-mat unit-ctxt-fo (base EP.number) len-u γu3)
  u4 = table (interp.readback.dep-mat unit-ctxt-fo (base EP.number) len-u γu4)

  p1 : String
  p1 = table (interp.readback.dep-mat query-ctxt-fo (base EP.number) length-term γp1)

  p2e : String
  p2e = bit (interp.readback.dep-mat query-ctxt-fo (base EP.number) length-term γp2
               Fin.zero Fin.zero)

  w2e : String
  w2e = bit (interp.readback.dep-mat pp-ctxt-fo (base EP.number) len-pp γpp2
               Fin.zero Fin.zero)

  p2 : String
  p2 = table (interp.readback.dep-mat query-ctxt-fo (base EP.number) length-term γp2)

  w2 : String
  w2 = table (interp.readback.dep-mat pp-ctxt-fo (base EP.number) len-pp γpp2)

main : Main
main =
  run (writeFile "/tmp/probe-u1.txt" u1 >>
       writeFile "/tmp/probe-u2.txt" u2 >>
       writeFile "/tmp/probe-u3.txt" u3 >>
       writeFile "/tmp/probe-p1.txt" p1 >>
       writeFile "/tmp/probe-p2e.txt" p2e >>
       writeFile "/tmp/probe-w2e.txt" w2e >>
       writeFile "/tmp/probe-p2.txt" p2 >>
       writeFile "/tmp/probe-u4.txt" u4 >>
       writeFile "/tmp/probe-w2.txt" w2 >>
       writeFile "/tmp/probe-done.txt" "done")
