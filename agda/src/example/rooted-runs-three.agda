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
open import example.rooted-runs using (map-term)

module EP3 = example.primitives-over three.semiring

module model = ho-model-roots-order-idempotent three.semiring
  (λ {x} → three.∨-idem {x}) (λ {x} → three.∧-idem {x}) (λ {x} → three.⊤-add-top {x}) three.C
module interp = model.rooted-interp EP3.Sig EP3.primitives

open import language-syntax EP3.Sig
  using (base; list; unit; _[+]_; _[×]_; var; μ; first-order; first-order-ctxt; emp; _,_)

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

abstract
  dep-map : matrix.Mat.Matrix three.semiring
              (model.OI.Pos.dim (interp.𝒞⟦ numlist-fo ⟧ty interp.∅𝒞 .model.Fam⟨𝒞⟩μ.fam
                                   .model.Fam⟨𝒞⟩μ.fm
                                   (interp.readback.out map-ctxt-fo numlist-fo
                                                        map-term γ-nums)))
              (model.OI.Pos.dim (interp.𝒞⟦ map-ctxt-fo ⟧ctxt .model.Fam⟨𝒞⟩μ.fam
                                   .model.Fam⟨𝒞⟩μ.fm γ-nums))
  dep-map = interp.readback.dep-mat map-ctxt-fo numlist-fo map-term γ-nums
