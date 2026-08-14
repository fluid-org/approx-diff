{-# OPTIONS --prop --postfix-projections --safe #-}

-- Dependency matrices weighted in the three-chain: consuming a former is recorded at C, value
-- flow at D.
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
import ho-model
open import example.list-terms
  using (numlist-fo; map-ctxt-fo; map-term; filter-ctxt-fo; filter-term;
         cond-ctxt-fo; cond-term; eq-ctxt-fo; eq-term)

module EP3 = example.primitives-over three.semiring

module model = ho-model three.semiring three.C
module interp = model.interp EP3.Sig EP3.primitives

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
  dep-cond = interp.dependency.mat-of cond-ctxt-fo (base EP3.number) cond-term γ-cond

γ-eq : Setoid.Carrier (interp.𝒞⟦ eq-ctxt-fo ⟧ctxt .model.Fam⟨𝒞⟩μ.idx)
γ-eq = lift tt ,' 0ℚ

abstract
  dep-eq : matrix.Mat.Matrix three.semiring 2 1
  dep-eq = interp.dependency.mat-of eq-ctxt-fo (first-order.unit [+] first-order.unit)
                                   eq-term γ-eq

γ-filter : Setoid.Carrier (interp.𝒞⟦ filter-ctxt-fo ⟧ctxt .model.Fam⟨𝒞⟩μ.idx)
γ-filter =
  ((lift tt ,' (1ℚ +ℚ 1ℚ)) ,'
   T'.sup (inj₂ (1ℚ ,' T'.sup (inj₂ ((1ℚ +ℚ 1ℚ) ,' T'.sup (inj₂ (((1ℚ +ℚ 1ℚ) +ℚ 1ℚ) ,'
   T'.sup (inj₁ (lift tt)))))))))
  where module T' = model.Fam⟨𝒞⟩μ.Tree interp.∅𝒞

abstract
  dep-filter : matrix.Mat.Matrix three.semiring
                 (interp.dependency.tgt filter-ctxt-fo numlist-fo filter-term γ-filter)
                 (interp.dependency.src filter-ctxt-fo numlist-fo filter-term γ-filter)
  dep-filter = interp.dependency.mat-of filter-ctxt-fo numlist-fo filter-term γ-filter

abstract
  dep-map : matrix.Mat.Matrix three.semiring
              (interp.dependency.tgt map-ctxt-fo numlist-fo map-term γ-nums)
              (interp.dependency.src map-ctxt-fo numlist-fo map-term γ-nums)
  dep-map = interp.dependency.mat-of map-ctxt-fo numlist-fo map-term γ-nums
