{-# OPTIONS --prop --postfix-projections --safe #-}

-- The readbacks weighted in the three-chain: eliminations charge at C, value flow carries D.
module example.runs-three where

open import prop-setoid using (Setoid)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ) renaming (_+_ to _+ℚ_)
open import Data.Product using () renaming (_,_ to _,'_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Level using (lift)
import three
import matrix
import example.primitives-over
import ho-model-roots-free
open import example.list-terms
  using (numlist-fo; map-ctxt-fo; map-term; filter-ctxt-fo; filter-term;
         cond-ctxt-fo; cond-term; eq-ctxt-fo; eq-term)

module EP3 = example.primitives-over three.semiring

module model = ho-model-roots-free three.semiring three.C
module interp = model.rooted-interp EP3.Sig EP3.primitives

open import language-syntax EP3.Sig using (base; unit; _[+]_; first-order)

γ-nums : Setoid.Carrier (interp.𝒞⟦ map-ctxt-fo ⟧ctxt .model.Fam⟨𝒞⟩μ.idx)
γ-nums =
  lift tt ,'
  T'.sup (inj₂ (0ℚ ,' T'.sup (inj₂ (1ℚ ,' T'.sup (inj₂ ((1ℚ +ℚ 1ℚ) ,'
  T'.sup (inj₁ (lift tt))))))))
  where module T' = model.Fam⟨𝒞⟩μ.Tree interp.∅𝒞

γ-cond : Setoid.Carrier (interp.𝒞⟦ cond-ctxt-fo ⟧ctxt .model.Fam⟨𝒞⟩μ.idx)
γ-cond = (lift tt ,' 0ℚ) ,' 1ℚ

abstract
  dep-cond : matrix.Mat.Matrix three.semiring 1 2
  dep-cond = interp.readback.dep-mat cond-ctxt-fo (base EP3.number) cond-term γ-cond

γ-eq : Setoid.Carrier (interp.𝒞⟦ eq-ctxt-fo ⟧ctxt .model.Fam⟨𝒞⟩μ.idx)
γ-eq = lift tt ,' 0ℚ

abstract
  dep-eq : matrix.Mat.Matrix three.semiring 2 1
  dep-eq = interp.readback.dep-mat eq-ctxt-fo (first-order.unit [+] first-order.unit)
                                   eq-term γ-eq

γ-filter : Setoid.Carrier (interp.𝒞⟦ filter-ctxt-fo ⟧ctxt .model.Fam⟨𝒞⟩μ.idx)
γ-filter =
  ((lift tt ,' (1ℚ +ℚ 1ℚ)) ,'
   T'.sup (inj₂ (1ℚ ,' T'.sup (inj₂ ((1ℚ +ℚ 1ℚ) ,' T'.sup (inj₂ (((1ℚ +ℚ 1ℚ) +ℚ 1ℚ) ,'
   T'.sup (inj₁ (lift tt)))))))))
  where module T' = model.Fam⟨𝒞⟩μ.Tree interp.∅𝒞

abstract
  dep-filter : matrix.Mat.Matrix three.semiring
                 (interp.readback.tgt filter-ctxt-fo numlist-fo filter-term γ-filter)
                 (interp.readback.src filter-ctxt-fo numlist-fo filter-term γ-filter)
  dep-filter = interp.readback.dep-mat filter-ctxt-fo numlist-fo filter-term γ-filter

abstract
  dep-map : matrix.Mat.Matrix three.semiring
              (interp.readback.tgt map-ctxt-fo numlist-fo map-term γ-nums)
              (interp.readback.src map-ctxt-fo numlist-fo map-term γ-nums)
  dep-map = interp.readback.dep-mat map-ctxt-fo numlist-fo map-term γ-nums
