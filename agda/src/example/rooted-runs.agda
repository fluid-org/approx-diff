{-# OPTIONS --prop --postfix-projections --safe #-}

-- Readbacks over a three-element list, at the rooted model with roots as isolated positions.
-- Expected: const and fold0 all-zero (nothing examined); case0 and tag the sum-cell roots the
-- fold examines and nothing else, the two agreeing because a fold's case charges each examined
-- tag whatever the branches return; length additionally the pair roots its snd eliminates; the
-- label-filtered query the cell roots, the labels, and the values whose label matches. Payload
-- columns light up only when a branch reads them, which is the distinction the dominated model
-- collapsed.
module example.rooted-runs where

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
import ho-model-roots-order-idempotent
open import example.list-terms
  using (query-ctxt-fo; const-term; length-term; fold0-term; case0-term; tag-term;
         numlist-fo; map-ctxt-fo; map-term; filter-ctxt-fo; filter-term)

module Ex = example ℚ 0ℚ
open Ex.ex using (query)

module model = ho-model-roots-order-idempotent two.semiring
  (λ {x} → two.∨-idem {x}) (λ {x} → two.∧-idem {x}) (λ {x} → two.⊤-add-top {x}) two.I
module interp = model.rooted-interp EP.Sig EP.primitives

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
                (model.OI.Pos.dim (interp.𝒞⟦ base EP.number ⟧ty interp.∅𝒞 .model.Fam⟨𝒞⟩μ.fam
                                     .model.Fam⟨𝒞⟩μ.fm
                                     (interp.readback.out query-ctxt-fo (base EP.number)
                                                          const-term γ-input)))
                (model.OI.Pos.dim (interp.𝒞⟦ query-ctxt-fo ⟧ctxt .model.Fam⟨𝒞⟩μ.fam
                                     .model.Fam⟨𝒞⟩μ.fm γ-input))
  dep-const = interp.readback.dep-mat query-ctxt-fo (base EP.number) const-term γ-input

abstract
  dep-length : matrix.Mat.Matrix two.semiring
                 (model.OI.Pos.dim (interp.𝒞⟦ base EP.number ⟧ty interp.∅𝒞 .model.Fam⟨𝒞⟩μ.fam
                                      .model.Fam⟨𝒞⟩μ.fm
                                      (interp.readback.out query-ctxt-fo (base EP.number)
                                                           length-term γ-input)))
                 (model.OI.Pos.dim (interp.𝒞⟦ query-ctxt-fo ⟧ctxt .model.Fam⟨𝒞⟩μ.fam
                                      .model.Fam⟨𝒞⟩μ.fm γ-input))
  dep-length = interp.readback.dep-mat query-ctxt-fo (base EP.number) length-term γ-input

abstract
  dep-fold0 : matrix.Mat.Matrix two.semiring
                (model.OI.Pos.dim (interp.𝒞⟦ base EP.number ⟧ty interp.∅𝒞 .model.Fam⟨𝒞⟩μ.fam
                                     .model.Fam⟨𝒞⟩μ.fm
                                     (interp.readback.out query-ctxt-fo (base EP.number)
                                                          fold0-term γ-input)))
                (model.OI.Pos.dim (interp.𝒞⟦ query-ctxt-fo ⟧ctxt .model.Fam⟨𝒞⟩μ.fam
                                     .model.Fam⟨𝒞⟩μ.fm γ-input))
  dep-fold0 = interp.readback.dep-mat query-ctxt-fo (base EP.number) fold0-term γ-input

abstract
  dep-case0 : matrix.Mat.Matrix two.semiring
                (model.OI.Pos.dim (interp.𝒞⟦ base EP.number ⟧ty interp.∅𝒞 .model.Fam⟨𝒞⟩μ.fam
                                     .model.Fam⟨𝒞⟩μ.fm
                                     (interp.readback.out query-ctxt-fo (base EP.number)
                                                          case0-term γ-input)))
                (model.OI.Pos.dim (interp.𝒞⟦ query-ctxt-fo ⟧ctxt .model.Fam⟨𝒞⟩μ.fam
                                     .model.Fam⟨𝒞⟩μ.fm γ-input))
  dep-case0 = interp.readback.dep-mat query-ctxt-fo (base EP.number) case0-term γ-input

abstract
  dep-tag : matrix.Mat.Matrix two.semiring
              (model.OI.Pos.dim (interp.𝒞⟦ base EP.number ⟧ty interp.∅𝒞 .model.Fam⟨𝒞⟩μ.fam
                                   .model.Fam⟨𝒞⟩μ.fm
                                   (interp.readback.out query-ctxt-fo (base EP.number)
                                                        tag-term γ-input)))
              (model.OI.Pos.dim (interp.𝒞⟦ query-ctxt-fo ⟧ctxt .model.Fam⟨𝒞⟩μ.fam
                                   .model.Fam⟨𝒞⟩μ.fm γ-input))
  dep-tag = interp.readback.dep-mat query-ctxt-fo (base EP.number) tag-term γ-input

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
                 (model.OI.Pos.dim (interp.𝒞⟦ numlist-fo ⟧ty interp.∅𝒞 .model.Fam⟨𝒞⟩μ.fam
                                      .model.Fam⟨𝒞⟩μ.fm
                                      (interp.readback.out filter-ctxt-fo numlist-fo
                                                           filter-term γ-filter)))
                 (model.OI.Pos.dim (interp.𝒞⟦ filter-ctxt-fo ⟧ctxt .model.Fam⟨𝒞⟩μ.fam
                                      .model.Fam⟨𝒞⟩μ.fm γ-filter))
  dep-filter = interp.readback.dep-mat filter-ctxt-fo numlist-fo filter-term γ-filter

abstract
  dep-map : matrix.Mat.Matrix two.semiring
              (model.OI.Pos.dim (interp.𝒞⟦ numlist-fo ⟧ty interp.∅𝒞 .model.Fam⟨𝒞⟩μ.fam
                                   .model.Fam⟨𝒞⟩μ.fm
                                   (interp.readback.out map-ctxt-fo numlist-fo
                                                        map-term γ-nums)))
              (model.OI.Pos.dim (interp.𝒞⟦ map-ctxt-fo ⟧ctxt .model.Fam⟨𝒞⟩μ.fam
                                   .model.Fam⟨𝒞⟩μ.fm γ-nums))
  dep-map = interp.readback.dep-mat map-ctxt-fo numlist-fo map-term γ-nums

-- One output row, the result number's scalar, against the input list's positions.
abstract
  dep : matrix.Mat.Matrix two.semiring
          (model.OI.Pos.dim (interp.𝒞⟦ base EP.number ⟧ty interp.∅𝒞 .model.Fam⟨𝒞⟩μ.fam
                               .model.Fam⟨𝒞⟩μ.fm
                               (interp.readback.out query-ctxt-fo (base EP.number)
                                                    (query label.a) γ-input)))
          (model.OI.Pos.dim (interp.𝒞⟦ query-ctxt-fo ⟧ctxt .model.Fam⟨𝒞⟩μ.fam
                               .model.Fam⟨𝒞⟩μ.fm γ-input))
  dep = interp.readback.dep-mat query-ctxt-fo (base EP.number) (query label.a) γ-input
