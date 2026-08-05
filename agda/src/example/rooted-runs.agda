{-# OPTIONS --prop --postfix-projections --safe #-}

-- Readbacks over a three-element list, at the rooted model. FOUR OF THE SIX BASELINE ROWS ARE
-- WRONG, and are committed so the defect is recorded rather than hidden.
--
-- Correct: const and fold0, both all-zero. Neither applies an elimination form to the list.
--
-- Wrong: case0, tag, length and the label-filtered query all come out saturated. case0 is the
-- sharpest, since its value is one constant whatever the input, so every column should be zero.
-- Expected instead: case0 all-zero; tag the outermost cell root only; length the cons cell roots
-- only; the query the cell roots, the labels, and the values whose label matches.
--
-- Cause: the constructors go through injF, which gives a cell no root of its own and derives one
-- as the support of its contents. Elimination reads that derived root, so examining a node counts
-- as depending on everything beneath it. Domination itself is the wanted prefix closure; the fault
-- is deriving the root rather than taking it as separate data, as assembleF does.
module example.rooted-runs where

import Data.Fin as Fin
open import prop-setoid using (Setoid)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ)
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
import ho-model-rooted-order-idempotent

module Ex = example ℚ 0ℚ
open Ex.ex using (query)

module model = ho-model-rooted-order-idempotent two.semiring
  (λ {x} → two.∨-idem {x}) (λ {x} → two.∧-idem {x}) (λ {x} → two.⊤-add-top {x})
module interp = model.rooted-interp EP.Sig EP.primitives

open import language-syntax EP.Sig
  using (base; list; unit; _[+]_; _[×]_; var; μ; _⊢_; bop; fold; case; snd; zero; first-order; first-order-ctxt; emp; _,_)

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
