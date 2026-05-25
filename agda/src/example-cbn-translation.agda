{-# OPTIONS --prop --postfix-projections --safe #-}

-- Backward analysis using CBN lifting.

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
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl)

open L hiding (_,_)

import example
open example.ex using (Tag; Tag-monad; query)

open import cbn-translation Sig Tag-monad

cbn-query : label.label → emp , Tag (list (Tag (Tag (base label) [×] Tag (base number)))) ⊢ Tag (base number)
cbn-query l = ⟪ query l ⟫tm

module backward-cbn where
  open import ho-model
  open import example-signature-interpretation galois.cat galois.products galois.terminal galois.TWO galois.unit galois.conjunct
  open Galois.interp Sig BaseInterp0

  -- μ-list representation
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

  -- Slices will also need adjusting to μ-list format, but currently cbn-translation doesn't compile.
  test1 : bwd-slice label.a ≡ (⊤ , (⊤ , (⊤ , ·) , ⊤ , ·) , (⊤ , (⊤ , ·) , ⊥ , ·) , (⊤ , (⊤ , ·) , ⊤ , ·) , ·)
  test1 = ≡-refl

  test2 : bwd-slice label.b ≡ (⊤ , (⊤ , (⊤ , ·) , ⊥ , ·) , (⊤ , (⊤ , ·) , ⊤ , ·) , (⊤ , (⊤ , ·) , ⊥ , ·) , ·)
  test2 = ≡-refl
