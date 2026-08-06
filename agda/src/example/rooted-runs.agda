{-# OPTIONS --prop --postfix-projections --safe #-}

-- Readbacks over a three-element list, at the rooted model with roots as isolated positions.
-- Expected: const and fold0 all-zero (nothing examined); case0 and tag the sum-cell roots the
-- fold examines and nothing else, the two agreeing because a fold's case charges each examined
-- tag whatever the branches return; length additionally the pair roots its snd eliminates; the
-- label-filtered query the cell roots, the labels, and the values whose label matches. Payload
-- columns light up only when a branch reads them, which is the distinction the dominated model
-- collapsed.
module example.rooted-runs where

import Data.Fin as Fin
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
open import every using ([]; _∷_)
import ho-model-roots-order-idempotent

module Ex = example ℚ 0ℚ
open Ex.ex using (query)

module model = ho-model-roots-order-idempotent two.semiring
  (λ {x} → two.∨-idem {x}) (λ {x} → two.∧-idem {x}) (λ {x} → two.⊤-add-top {x})
module interp = model.rooted-interp EP.Sig EP.primitives

open import language-syntax EP.Sig
  using (base; list; unit; _[+]_; _[×]_; var; μ; _⊢_; bop; fold; case; snd; fst; pair;
         from_collect_; return; zero; first-order; first-order-ctxt; emp; _,_; first-order)

query-ctxt-fo : first-order-ctxt (emp , list (base EP.label [×] base EP.number))
query-ctxt-fo = emp , μ (unit [+] ((base EP.label [×] base EP.number) [×] var Fin.zero))

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

-- A term that ignores its input: every column must be zero.
const-term : (emp , list (base EP.label [×] base EP.number)) ⊢ base EP.number
const-term = bop (EP.lit 0ℚ) []

abstract
  dep-const : matrix.Mat.Matrix two.semiring
                (model.OI.Pos.dim (interp.𝒞⟦ base EP.number ⟧ty interp.∅𝒞 .model.Fam⟨𝒞⟩μ.fam
                                     .model.Fam⟨𝒞⟩μ.fm
                                     (interp.readback.out query-ctxt-fo (base EP.number)
                                                          const-term γ-input)))
                (model.OI.Pos.dim (interp.𝒞⟦ query-ctxt-fo ⟧ctxt .model.Fam⟨𝒞⟩μ.fam
                                     .model.Fam⟨𝒞⟩μ.fm γ-input))
  dep-const = interp.readback.dep-mat query-ctxt-fo (base EP.number) const-term γ-input

-- Length: fold ignoring the element, so only the cons cells should register.
length-term : (emp , list (base EP.label [×] base EP.number)) ⊢ base EP.number
length-term =
  fold (case (var zero)
          (bop (EP.lit 0ℚ) [])
          (bop EP.add ((bop (EP.lit 1ℚ) []) ∷ ((snd (var zero)) ∷ []))))
       (var zero)

abstract
  dep-length : matrix.Mat.Matrix two.semiring
                 (model.OI.Pos.dim (interp.𝒞⟦ base EP.number ⟧ty interp.∅𝒞 .model.Fam⟨𝒞⟩μ.fam
                                      .model.Fam⟨𝒞⟩μ.fm
                                      (interp.readback.out query-ctxt-fo (base EP.number)
                                                           length-term γ-input)))
                 (model.OI.Pos.dim (interp.𝒞⟦ query-ctxt-fo ⟧ctxt .model.Fam⟨𝒞⟩μ.fam
                                      .model.Fam⟨𝒞⟩μ.fm γ-input))
  dep-length = interp.readback.dep-mat query-ctxt-fo (base EP.number) length-term γ-input

-- A fold whose body reads nothing: separates the fold itself from what its body consults.
fold0-term : (emp , list (base EP.label [×] base EP.number)) ⊢ base EP.number
fold0-term = fold (bop (EP.lit 0ℚ) []) (var zero)

abstract
  dep-fold0 : matrix.Mat.Matrix two.semiring
                (model.OI.Pos.dim (interp.𝒞⟦ base EP.number ⟧ty interp.∅𝒞 .model.Fam⟨𝒞⟩μ.fam
                                     .model.Fam⟨𝒞⟩μ.fm
                                     (interp.readback.out query-ctxt-fo (base EP.number)
                                                          fold0-term γ-input)))
                (model.OI.Pos.dim (interp.𝒞⟦ query-ctxt-fo ⟧ctxt .model.Fam⟨𝒞⟩μ.fam
                                     .model.Fam⟨𝒞⟩μ.fm γ-input))
  dep-fold0 = interp.readback.dep-mat query-ctxt-fo (base EP.number) fold0-term γ-input

-- Matches the unfolding but returns a constant either way: separates matching from reading.
case0-term : (emp , list (base EP.label [×] base EP.number)) ⊢ base EP.number
case0-term = fold (case (var zero) (bop (EP.lit 0ℚ) []) (bop (EP.lit 0ℚ) [])) (var zero)

abstract
  dep-case0 : matrix.Mat.Matrix two.semiring
                (model.OI.Pos.dim (interp.𝒞⟦ base EP.number ⟧ty interp.∅𝒞 .model.Fam⟨𝒞⟩μ.fam
                                     .model.Fam⟨𝒞⟩μ.fm
                                     (interp.readback.out query-ctxt-fo (base EP.number)
                                                          case0-term γ-input)))
                (model.OI.Pos.dim (interp.𝒞⟦ query-ctxt-fo ⟧ctxt .model.Fam⟨𝒞⟩μ.fam
                                     .model.Fam⟨𝒞⟩μ.fm γ-input))
  dep-case0 = interp.readback.dep-mat query-ctxt-fo (base EP.number) case0-term γ-input

-- Zero for nil, one for cons: should register the outermost tag and nothing else.
tag-term : (emp , list (base EP.label [×] base EP.number)) ⊢ base EP.number
tag-term = fold (case (var zero) (bop (EP.lit 0ℚ) []) (bop (EP.lit 1ℚ) [])) (var zero)

abstract
  dep-tag : matrix.Mat.Matrix two.semiring
              (model.OI.Pos.dim (interp.𝒞⟦ base EP.number ⟧ty interp.∅𝒞 .model.Fam⟨𝒞⟩μ.fam
                                   .model.Fam⟨𝒞⟩μ.fm
                                   (interp.readback.out query-ctxt-fo (base EP.number)
                                                        tag-term γ-input)))
              (model.OI.Pos.dim (interp.𝒞⟦ query-ctxt-fo ⟧ctxt .model.Fam⟨𝒞⟩μ.fam
                                   .model.Fam⟨𝒞⟩μ.fm γ-input))
  dep-tag = interp.readback.dep-mat query-ctxt-fo (base EP.number) tag-term γ-input

-- Expected: each output cell records the input spine above it and its own scalar, nothing later.
numlist-fo : first-order (list (base EP.number))
numlist-fo = μ (unit [+] (base EP.number [×] var Fin.zero))

map-ctxt-fo : first-order-ctxt (emp , list (base EP.number))
map-ctxt-fo = emp , numlist-fo

γ-nums : Setoid.Carrier (interp.𝒞⟦ map-ctxt-fo ⟧ctxt .model.Fam⟨𝒞⟩μ.idx)
γ-nums =
  lift tt ,'
  T'.sup (inj₂ (0ℚ ,' T'.sup (inj₂ (1ℚ ,' T'.sup (inj₂ ((1ℚ +ℚ 1ℚ) ,'
  T'.sup (inj₁ (lift tt))))))))
  where module T' = model.Fam⟨𝒞⟩μ.Tree interp.∅𝒞

map-term : (emp , list (base EP.number)) ⊢ list (base EP.number)
map-term =
  from var zero collect
    return (bop EP.add ((bop (EP.lit 1ℚ) []) ∷ ((var zero) ∷ [])))

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
