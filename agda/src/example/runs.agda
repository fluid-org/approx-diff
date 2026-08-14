{-# OPTIONS --prop --postfix-projections --safe #-}

-- The example terms' dependency matrices over the Booleans: with no order on positions a matrix
-- is the fibre map evaluated on the basis, and a fibre's dimension is the object itself.
module example.runs where

open import prop-setoid using (Setoid)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ) renaming (_+_ to _+ℚ_)
open import Data.Product using () renaming (_,_ to _,'_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Level using (lift)
import label
import two
import example
import example.primitives as EP
import matrix
import ho-model
open import example.list-terms
  using (query-ctxt-fo; const-term; length-term; fold0-term; case0-term; tag-term;
         numlist-fo; map-ctxt-fo; map-term; filter-ctxt-fo; filter-term)

module Ex = example ℚ 0ℚ
open Ex.ex using (query)

module model = ho-model two.semiring two.I
module interp = model.interp EP.Sig EP.primitives

open import language-syntax EP.Sig using (base)

private
  module T = model.Fam⟨𝒞⟩μ.Tree interp.∅𝒞

-- Three entries, two under the queried label.
γ-input : Setoid.Carrier (interp.𝒞⟦ query-ctxt-fo ⟧ctxt .model.Fam⟨𝒞⟩μ.idx)
γ-input =
  lift tt ,'
  T.sup (inj₂ ((label.a ,' 0ℚ) ,'
  T.sup (inj₂ ((label.b ,' 1ℚ) ,'
  T.sup (inj₂ ((label.a ,' 1ℚ) ,'
  T.sup (inj₁ (lift tt))))))))

abstract
  dep-const : matrix.Mat.Matrix two.semiring
                (interp.dependency.tgt query-ctxt-fo (base EP.number) const-term γ-input)
                (interp.dependency.src query-ctxt-fo (base EP.number) const-term γ-input)
  dep-const = interp.dependency.mat-of query-ctxt-fo (base EP.number) const-term γ-input

abstract
  dep-length : matrix.Mat.Matrix two.semiring
                 (interp.dependency.tgt query-ctxt-fo (base EP.number) length-term γ-input)
                 (interp.dependency.src query-ctxt-fo (base EP.number) length-term γ-input)
  dep-length = interp.dependency.mat-of query-ctxt-fo (base EP.number) length-term γ-input

abstract
  dep-fold0 : matrix.Mat.Matrix two.semiring
                (interp.dependency.tgt query-ctxt-fo (base EP.number) fold0-term γ-input)
                (interp.dependency.src query-ctxt-fo (base EP.number) fold0-term γ-input)
  dep-fold0 = interp.dependency.mat-of query-ctxt-fo (base EP.number) fold0-term γ-input

abstract
  dep-case0 : matrix.Mat.Matrix two.semiring
                (interp.dependency.tgt query-ctxt-fo (base EP.number) case0-term γ-input)
                (interp.dependency.src query-ctxt-fo (base EP.number) case0-term γ-input)
  dep-case0 = interp.dependency.mat-of query-ctxt-fo (base EP.number) case0-term γ-input

abstract
  dep-tag : matrix.Mat.Matrix two.semiring
              (interp.dependency.tgt query-ctxt-fo (base EP.number) tag-term γ-input)
              (interp.dependency.src query-ctxt-fo (base EP.number) tag-term γ-input)
  dep-tag = interp.dependency.mat-of query-ctxt-fo (base EP.number) tag-term γ-input

γ-nums : Setoid.Carrier (interp.𝒞⟦ map-ctxt-fo ⟧ctxt .model.Fam⟨𝒞⟩μ.idx)
γ-nums =
  lift tt ,'
  T'.sup (inj₂ (0ℚ ,' T'.sup (inj₂ (1ℚ ,' T'.sup (inj₂ ((1ℚ +ℚ 1ℚ) ,'
  T'.sup (inj₁ (lift tt))))))))
  where module T' = model.Fam⟨𝒞⟩μ.Tree interp.∅𝒞

γ-filter : Setoid.Carrier (interp.𝒞⟦ filter-ctxt-fo ⟧ctxt .model.Fam⟨𝒞⟩μ.idx)
γ-filter =
  ((lift tt ,' (1ℚ +ℚ 1ℚ)) ,'
   T'.sup (inj₂ (1ℚ ,' T'.sup (inj₂ ((1ℚ +ℚ 1ℚ) ,' T'.sup (inj₂ (((1ℚ +ℚ 1ℚ) +ℚ 1ℚ) ,'
   T'.sup (inj₁ (lift tt)))))))))
  where module T' = model.Fam⟨𝒞⟩μ.Tree interp.∅𝒞

abstract
  dep-filter : matrix.Mat.Matrix two.semiring
                 (interp.dependency.tgt filter-ctxt-fo numlist-fo filter-term γ-filter)
                 (interp.dependency.src filter-ctxt-fo numlist-fo filter-term γ-filter)
  dep-filter = interp.dependency.mat-of filter-ctxt-fo numlist-fo filter-term γ-filter

abstract
  dep-map : matrix.Mat.Matrix two.semiring
              (interp.dependency.tgt map-ctxt-fo numlist-fo map-term γ-nums)
              (interp.dependency.src map-ctxt-fo numlist-fo map-term γ-nums)
  dep-map = interp.dependency.mat-of map-ctxt-fo numlist-fo map-term γ-nums

-- One output row, the result number's scalar, against the input list's positions.
abstract
  dep : matrix.Mat.Matrix two.semiring
          (interp.dependency.tgt query-ctxt-fo (base EP.number) (query label.a) γ-input)
          (interp.dependency.src query-ctxt-fo (base EP.number) (query label.a) γ-input)
  dep = interp.dependency.mat-of query-ctxt-fo (base EP.number) (query label.a) γ-input
