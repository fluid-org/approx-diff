{-# OPTIONS --prop --postfix-projections --safe #-}

-- Backward and forward analyses of the list example for the language with general
-- recursive types, with two-valued (Bool) approximation.

module example-bools-2 where

open import Level using (0ℓ; lift)
open import every using (Every; []; _∷_)
open import signature
import language-syntax-2
import label
import galois
import conjugate

open import example-signature

module L = language-syntax-2 Sig

import indexed-family
import join-semilattice-category
import join-semilattice
import preorder
import prop-setoid

open import two renaming (I to ⊤; O to ⊥)
open import Data.Unit renaming (tt to ·; ⊤ to Unit) using ()
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; _×_; proj₁; proj₂)

open prop-setoid.Setoid

open L hiding (_,_)

import example-2

open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl)

-- Backward analysis (Galois).
module backward where
  open import ho-model
  open import example-signature-interpretation galois.cat galois.products galois.terminal galois.TWO galois.unit galois.conjunct
  open Galois.interp-2 Sig BaseInterp1
  open indexed-family._⇒f_
  open join-semilattice-category._⇒_
  open join-semilattice._=>_
  open preorder._=>_

  module T = Galois.Fam⟨𝒟⟩-μ.Tree {n = 0} (λ ())

  input : ⟦ list (base label [×] base number) ⟧ty (λ ()) .idx .Carrier
  input = T.sup (inj₂ ((label.a , 0) , T.sup (inj₂ ((label.b , 1) , T.sup (inj₂ ((label.a , 1) , T.sup (inj₁ (lift ·))))))))

  bwd-slice : label.label → _
  bwd-slice l = ⟦ example-2.ex.query l ⟧tm .famf .transf (_ , input) .proj₂ .*→* .func .fun ⊤ .proj₂

  -- Querying for the 'a' label uses the 1st and 3rd numbers
  test1 : bwd-slice label.a ≡ ((· , ⊤) , (· , ⊥) , (· , ⊤) , _)
  test1 = ≡-refl

  -- Querying for the 'b' label uses the 2nd number
  test2 : bwd-slice label.b ≡ ((· , ⊥) , (· , ⊤) , (· , ⊥) , _)
  test2 = ≡-refl

-- Forward analysis (Conjugate).
module forward where
  open import ho-model
  open import example-signature-interpretation conjugate.cat conjugate.products conjugate.terminal conjugate.TWO conjugate.unit conjugate.conjunct
  open Conjugate.interp-2 Sig BaseInterp1

  module T = Conjugate.Fam⟨𝒟⟩-μ.Tree {n = 0} (λ ())

  input : ⟦ list (base label [×] base number) ⟧ty (λ ()) .idx .Carrier
  input = T.sup (inj₂ ((label.a , 0) , T.sup (inj₂ ((label.b , 1) , T.sup (inj₂ ((label.a , 1) , T.sup (inj₁ (lift ·))))))))

  fwd-slice : _ → _
  fwd-slice supply = ⟦ example-2.ex.query label.a ⟧tm .famf .transf (_ , input) .proj₁ .*→* .func .fun (· , supply)
    where
      open indexed-family._⇒f_
      open join-semilattice-category._⇒_
      open join-semilattice._=>_
      open preorder._=>_

  -- Output depends on 1st label (would be ⊥ in the Galois example)
  test-1 : fwd-slice ((· , ⊤) , (· , ⊥) , (· , ⊥) , _) ≡ ⊤
  test-1 = ≡-refl

  -- Output doesn't depend on 2nd label
  test-2 : fwd-slice ((· , ⊥) , (· , ⊤) , (· , ⊥) , _) ≡ ⊥
  test-2 = ≡-refl

  -- Output depends on 3rd label (would be ⊥ in the Galois example)
  test-3 : fwd-slice ((· , ⊥) , (· , ⊥) , (· , ⊤) , _) ≡ ⊤
  test-3 = ≡-refl
