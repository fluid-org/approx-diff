{-# OPTIONS --prop --postfix-projections --safe #-}

-- Signed saliency of the 3x3 grid scorer: an integer run with a sign-valued backward derivative.
-- Seeding the score's output gives the signed-attribution map: for each cell, whether increasing
-- it raises (pos), lowers (neg), or has an ambiguous effect (unk) on the score, with zer for a
-- cell the score ignores.
module example.signs-score where

open import example.signs

-- Input grid, laid out row-major as ((r1 , r2) , r3), each row ((c1 , c2) , c3):
--   1 2 1
--   3 5 4
--   1 7 1
gval : ⟦ Grid ⟧ty .idx .Carrier
gval = (((+ 1 , + 2) , + 1) , ((+ 3 , + 5) , + 4)) , ((+ 1 , + 7) , + 1)

-- Grid as first-order data (the Row/Grid synonyms are plain types, so spell it out here).
grid-fo : first-order-data Grid
grid-fo = (((base number [×] base number) [×] base number) [×] ((base number [×] base number) [×] base number))
            [×] ((base number [×] base number) [×] base number)

-- score -1 = 5 - (1+1+1+1) + 3·4 - 5·2 = 3. The saliency: corners lower the score, the mid-edges
-- raise it through their interaction, the centre is ambiguous (its linear and interaction
-- contributions pull in opposite directions), and the bottom-middle cell is ignored.
saliency :
  conjugate (ty (unit [×] grid-fo) (_ , gval))
            (ty (base number) (+ 3))
            (mor (score -[1+ 0 ]) (_ , gval)) .func pos
  ≡ (lift · , ((((neg , neg) , neg) , ((pos , unk) , pos)) , ((neg , zer) , neg)))
saliency = refl
