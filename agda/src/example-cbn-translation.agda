{-# OPTIONS --prop --postfix-projections --safe #-}

-- Backward analysis using CBN lifting. Currently a work-in-progress: the
-- CBN translation uses cbn-coerce, which generates O(|P|) syntactic
-- bind/pure boilerplate per roll/fold-μ. With the W-form interpretation,
-- evaluating the resulting terms (for the tests below) times out
-- (>4min, ≥14GB RSS) on a 3-element input. Tests retained as a TODO.

module example-cbn-translation where

open import Level using (0ℓ; lift)
open import Data.Unit renaming (tt to ·) using ()
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₂)
open import signature
import language-syntax
import label
import galois

open import example-signature

module L = language-syntax Sig

import indexed-family
import join-semilattice-category
import join-semilattice
import preorder
import prop-setoid

open prop-setoid.Setoid

open import two renaming (I to ⊤; O to ⊥)
open import polynomial-functor using (inF)

open L hiding (_,_)

import example

module backward-cbn where
  open import ho-model
  open import example-signature-interpretation galois.cat galois.products galois.terminal galois.TWO galois.unit galois.conjunct
  open Galois.interp Sig BaseInterp0
  open example.ex using (Tag)
  open example.ex.cbn-Tag using (cbn-query)

  input : ⟦ Tag (list (Tag (Tag (base label) [×] Tag (base number)))) ⟧ty .idx .Carrier
  input = _ ,
          inF (inj₂ ((_ , (_ , label.a) , (_ , 0)) ,
          inF (inj₂ ((_ , (_ , label.b) , (_ , 1)) ,
          inF (inj₂ ((_ , (_ , label.a) , (_ , 1)) ,
          inF (inj₁ (lift ·))))))))

  bwd-slice : label.label → _
  bwd-slice l = ⟦ cbn-query l ⟧tm .famf .transf (_ , input) .proj₂ .*→* .func .fun (⊤ , ·) .proj₂
    where
      open indexed-family._⇒f_
      open join-semilattice-category._⇒_
      open join-semilattice._=>_
      open preorder._=>_

  -- TODO: tests below — reconstructed structure for the W-form result:
  --     (⊤ , ((⊤ , (⊤ , ·) , (⊤ , ·)) ,
  --           ((⊤ , (⊤ , ·) , (⊥ , ·)) ,
  --            ((⊤ , (⊤ , ·) , (⊤ , ·)) ,
  --             ·))))
  -- ...but enabling them makes typechecking timeout. Blocked on design
  -- rework: eliminating cbn-coerce requires the pointed-types redesign
  -- (sums-as-Mon-wrapped + polynomial-approx + force primitive), which
  -- is a coordinated overhaul. See conversation log 2026-05-19.
  -- test1 : bwd-slice label.a ≡ ... ; test1 = ≡-refl
  -- test2 : bwd-slice label.b ≡ ... ; test2 = ≡-refl
