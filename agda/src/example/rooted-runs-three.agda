{-# OPTIONS --prop --postfix-projections --safe #-}

-- The map readback weighted in the three-chain: eliminations charge at C, value flow carries D.
module example.rooted-runs-three where

import Data.Fin as Fin
open import prop-setoid using (Setoid)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ) renaming (_+_ to _+ℚ_)
open import Data.Product using () renaming (_,_ to _,'_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Level using (lift)
import three
import matrix
import example.primitives-over
import ho-model-roots-order-idempotent
open import example.rooted-runs using (map-term; filter-term)

module EP3 = example.primitives-over three.semiring

module model = ho-model-roots-order-idempotent three.semiring
  (λ {x} → three.∨-idem {x}) (λ {x} → three.∧-idem {x}) (λ {x} → three.⊤-add-top {x}) three.C
module interp = model.rooted-interp EP3.Sig EP3.primitives

open import language-syntax EP3.Sig
  using (base; list; unit; _[+]_; _[×]_; var; μ; first-order; first-order-ctxt; emp; _,_;
         _⊢_; if_then_else_; brel; bop; zero; succ)
open import every using ([]; _∷_)

numlist-fo : first-order (list (base EP3.number))
numlist-fo = μ (unit [+] (base EP3.number [×] var Fin.zero))

map-ctxt-fo : first-order-ctxt (emp , list (base EP3.number))
map-ctxt-fo = emp , numlist-fo

γ-nums : Setoid.Carrier (interp.𝒞⟦ map-ctxt-fo ⟧ctxt .model.Fam⟨𝒞⟩μ.idx)
γ-nums =
  lift tt ,'
  T'.sup (inj₂ (0ℚ ,' T'.sup (inj₂ (1ℚ ,' T'.sup (inj₂ ((1ℚ +ℚ 1ℚ) ,'
  T'.sup (inj₁ (lift tt))))))))
  where module T' = model.Fam⟨𝒞⟩μ.Tree interp.∅𝒞

-- Data and control interacting through a numeric test: x reaches the output only through the
-- equality, so its composite weight is C; y flows into the branch body at D.
cond-ctxt-fo : first-order-ctxt (emp , base EP3.number , base EP3.number)
cond-ctxt-fo = emp , base EP3.number , base EP3.number

cond-term : (emp , base EP3.number , base EP3.number) ⊢ base EP3.number
cond-term =
  if brel EP3.equal-number ((var (succ zero)) ∷ ((bop (EP3.lit 0ℚ) []) ∷ []))
  then bop EP3.add ((var zero) ∷ ((bop (EP3.lit 1ℚ) []) ∷ []))
  else var zero

γ-cond : Setoid.Carrier (interp.𝒞⟦ cond-ctxt-fo ⟧ctxt .model.Fam⟨𝒞⟩μ.idx)
γ-cond = (lift tt ,' 0ℚ) ,' 1ℚ

abstract
  dep-cond : matrix.Mat.Matrix three.semiring 1 2
  dep-cond = interp.readback.dep-mat cond-ctxt-fo (base EP3.number) cond-term γ-cond

-- The test's own outcome: the compared numbers reach the boolean at full weight, and only a
-- consumer of that boolean turns the dependence into control.
eq-ctxt-fo : first-order-ctxt (emp , base EP3.number)
eq-ctxt-fo = emp , first-order.base EP3.number

eq-term : (emp , base EP3.number) ⊢ (unit [+] unit)
eq-term = brel EP3.equal-number ((var zero) ∷ ((bop (EP3.lit 0ℚ) []) ∷ []))

γ-eq : Setoid.Carrier (interp.𝒞⟦ eq-ctxt-fo ⟧ctxt .model.Fam⟨𝒞⟩μ.idx)
γ-eq = lift tt ,' 0ℚ

abstract
  dep-eq : matrix.Mat.Matrix three.semiring 2 1
  dep-eq = interp.readback.dep-mat eq-ctxt-fo (first-order.unit [+] first-order.unit)
                                   eq-term γ-eq

filter-ctxt-fo : first-order-ctxt (emp , base EP3.number , list (base EP3.number))
filter-ctxt-fo = (emp , first-order.base EP3.number) , numlist-fo

γ-filter : Setoid.Carrier (interp.𝒞⟦ filter-ctxt-fo ⟧ctxt .model.Fam⟨𝒞⟩μ.idx)
γ-filter =
  ((lift tt ,' (1ℚ +ℚ 1ℚ)) ,'
   T'.sup (inj₂ (1ℚ ,' T'.sup (inj₂ ((1ℚ +ℚ 1ℚ) ,' T'.sup (inj₂ (((1ℚ +ℚ 1ℚ) +ℚ 1ℚ) ,'
   T'.sup (inj₁ (lift tt)))))))))
  where module T' = model.Fam⟨𝒞⟩μ.Tree interp.∅𝒞

abstract
  dep-filter : matrix.Mat.Matrix three.semiring
                 (model.OI.Pos.dim (interp.𝒞⟦ numlist-fo ⟧ty interp.∅𝒞 .model.Fam⟨𝒞⟩μ.fam
                                      .model.Fam⟨𝒞⟩μ.fm
                                      (interp.readback.out filter-ctxt-fo numlist-fo
                                                           filter-term γ-filter)))
                 (model.OI.Pos.dim (interp.𝒞⟦ filter-ctxt-fo ⟧ctxt .model.Fam⟨𝒞⟩μ.fam
                                      .model.Fam⟨𝒞⟩μ.fm γ-filter))
  dep-filter = interp.readback.dep-mat filter-ctxt-fo numlist-fo filter-term γ-filter

abstract
  dep-map : matrix.Mat.Matrix three.semiring
              (model.OI.Pos.dim (interp.𝒞⟦ numlist-fo ⟧ty interp.∅𝒞 .model.Fam⟨𝒞⟩μ.fam
                                   .model.Fam⟨𝒞⟩μ.fm
                                   (interp.readback.out map-ctxt-fo numlist-fo
                                                        map-term γ-nums)))
              (model.OI.Pos.dim (interp.𝒞⟦ map-ctxt-fo ⟧ctxt .model.Fam⟨𝒞⟩μ.fam
                                   .model.Fam⟨𝒞⟩μ.fm γ-nums))
  dep-map = interp.readback.dep-mat map-ctxt-fo numlist-fo map-term γ-nums
