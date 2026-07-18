{-# OPTIONS --postfix-projections --prop --safe #-}

module example where

open import Level using (lift)
open import Data.Unit using (tt)
open import Data.List using (List; []; _∷_)
open import Data.String using (unlines)
open import Data.Product using (_,_; proj₂)
open import every using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import prop-setoid using (Setoid)
open Setoid using (Carrier)
import label as L

open import example-mat-model

M-add : (emp · base number · base number) ⊢ base number
M-add = bop add (var zero ∷ var (succ zero) ∷ [])

----------------------------------------------------------------------
-- Strictly-FO version of approx-diff's `query`: sum the numbers paired with label l in a list of
-- (label × number) pairs, fused into a single fold (filter + sum in one pass).
query : L.label → emp · list (base label [×] base number) ⊢ base number
query l =
  fold (bop op-zero [])
       (if brel equal-label (fst (var (succ zero)) ∷ bop (lbl l) [] ∷ [])
        then bop add (snd (var (succ zero)) ∷ var zero ∷ [])
        else var zero)
       (var zero)

input : Carrier (⟦ list (base label [×] base number) ⟧ty .idx)
input = (L.a , 0) ∷ (L.b , 1) ∷ (L.a , 1) ∷ []

show-add-graph : showGraph (dependence-graph M-add ((lift tt , 2) , 3)) ≡
  "(var: 1, 2), (var: 0, 3), (add: 2, 4), (add: 3, 4)"
show-add-graph = refl

show-query-a-graph : showGraph (dependence-graph (query L.a) (lift tt , input)) ≡
  "(var: 0, 4), (var: 1, 5), (var: 2, 6), (var: 6, 7), (var: 6, 8), (snd: 8, 9), (var: 3, 10), (add: 9, 11), (add: 10, 11), (case-l: 11, 12), (var: 5, 13), (var: 12, 14), (case-r: 14, 15), (var: 4, 16), (var: 4, 17), (snd: 17, 18), (var: 15, 19), (add: 18, 20), (add: 19, 20), (case-l: 20, 21), (fold: 21, 22)"
show-query-a-graph = refl

show-add-trace : show-eval (proj₂ (proj₂ (eval M-add ((lift tt , 2) , 3)))) ≡ "(bop add ((var 0) (var 1)))"
show-add-trace = refl

show-query-a-trace : show-eval (proj₂ (proj₂ (eval (query L.a) (lift tt , input)))) ≡
  "(fold (bop zero ()) (var 0) ((case-l (brel ((fst (var 1)) (bop lbl-a ()))) (bop add ((snd (var 2)) (var 1)))) (case-r (brel ((fst (var 1)) (bop lbl-a ()))) (var 1)) (case-l (brel ((fst (var 1)) (bop lbl-a ()))) (bop add ((snd (var 2)) (var 1))))))"
show-query-a-trace = refl

show-query-a-trace-pretty : show-eval-pretty (proj₂ (proj₂ (eval (query L.a) (lift tt , input)))) ≡ unlines
  ( "fold"
  ∷ "  bop zero"
  ∷ "  var 0"
  ∷ "  case-l"
  ∷ "    brel"
  ∷ "      fst"
  ∷ "        var 1"
  ∷ "      bop lbl-a"
  ∷ "    bop add"
  ∷ "      snd"
  ∷ "        var 2"
  ∷ "      var 1"
  ∷ "  case-r"
  ∷ "    brel"
  ∷ "      fst"
  ∷ "        var 1"
  ∷ "      bop lbl-a"
  ∷ "    var 1"
  ∷ "  case-l"
  ∷ "    brel"
  ∷ "      fst"
  ∷ "        var 1"
  ∷ "      bop lbl-a"
  ∷ "    bop add"
  ∷ "      snd"
  ∷ "        var 2"
  ∷ "      var 1"
  ∷ [])
show-query-a-trace-pretty = refl
