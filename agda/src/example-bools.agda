{-# OPTIONS --prop --postfix-projections --safe #-}

-- Examples with Two-valued (Bool) approximation.

module example-bools where

open import Level using (0ℓ; lift)
open import Data.List using (List; []; _∷_)
open import every using (Every; []; _∷_)
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

open import two renaming (I to ⊤; O to ⊥)
import semiring-bool
open import Data.Unit renaming (tt to ·; ⊤ to Unit) using ()
open import Data.Product using (_,_; _×_; proj₁; proj₂)

open prop-setoid.Setoid

open L hiding (_,_)

import example

open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl)

-- Backward analysis (Galois). Example (2) in Section 4.3.
module backward where
  import ho-model-galois
  open import example-signature-interpretation galois.cat galois.products galois.terminal galois.TWO galois.unit galois.conjunct
  open ho-model-galois.interp Sig BaseInterp1

  input : ⟦ list (base label [×] base number) ⟧ty .idx .Carrier
  input = 3 , (label.a , 0) , (label.b , 1) , (label.a , 1) , _

  bwd-slice : label.label → _
  bwd-slice l = ⟦ example.ex.query l ⟧tm .famf .transf (_ , input) .proj₂ .*→* .func .fun ⊤ .proj₂
    where
      open indexed-family._⇒f_
      open join-semilattice-category._⇒_
      open join-semilattice._=>_
      open preorder._=>_

  -- Querying for the 'a' label uses the 1st and 3rd numbers
  test1 : bwd-slice label.a ≡ ((· , ⊤) , (· , ⊥) , (· , ⊤) , _)
  test1 = ≡-refl

  -- Querying for the 'b' label uses the 2nd number
  test2 : bwd-slice label.b ≡ ((· , ⊥) , (· , ⊤) , (· , ⊥) , _)
  test2 = ≡-refl

-- Backward analysis using CBN lifting.
module backward-cbn where
  import ho-model-galois
  open import example-signature-interpretation galois.cat galois.products galois.terminal galois.TWO galois.unit galois.conjunct
  open ho-model-galois.interp Sig BaseInterp0
  open example.ex using (Tag; cbn-query)

  input : ⟦ Tag (list (Tag (Tag (base label) [×] Tag (base number)))) ⟧ty .idx .Carrier
  input = _ , 3 , (_ , (_ , label.a) , (_ , 0)) , (_ , (_ , label.b) , (_ , 1)) , (_ , (_ , label.a) , (_ , 1)) , _

  bwd-slice : label.label → _
  bwd-slice l = ⟦ example.ex.cbn-query l ⟧tm .famf .transf (_ , input) .proj₂ .*→* .func .fun (⊤ , ·) .proj₂
    where
      open indexed-family._⇒f_
      open join-semilattice-category._⇒_
      open join-semilattice._=>_
      open preorder._=>_

  test1 : bwd-slice label.a ≡ (⊤ , (⊤ , (⊤ , ·) , ⊤ , ·) , (⊤ , (⊤ , ·) , ⊥ , ·) , (⊤ , (⊤ , ·) , ⊤ , ·) , ·)
  test1 = ≡-refl

  test2 : bwd-slice label.b ≡ (⊤ , (⊤ , (⊤ , ·) , ⊥ , ·) , (⊤ , (⊤ , ·) , ⊤ , ·) , (⊤ , (⊤ , ·) , ⊥ , ·) , ·)
  test2 = ≡-refl

-- Forward analysis (matrix-new), embedded into SemiMod.
module forward where
  open import categories using (Category; HasTerminal; HasInitial; IsInitial; IsTerminal; HasProducts)

  import cmon-enriched as CMon
  import matrix-new
  import semimodule
  import ho-model-matrix-new

  module HM = ho-model-matrix-new semiring-bool.semiring
  module FD = matrix-new.Mat semiring-bool.semiring
  module SM = semimodule semiring-bool.semiring
  open CMon.CMonEnriched FD.cmon using (_+m_)

  unitm : FD._⇒_ 0 1
  unitm = HasInitial.from-initial FD.initial {1}

  conjunctm : FD._⇒_ (HasProducts.prod FD.products 1 1) 1
  conjunctm = HasProducts.p₁ FD.products {1} {1} +m HasProducts.p₂ FD.products {1} {1}

  open import example-signature-interpretation FD.cat FD.products FD.terminal 1 unitm conjunctm
  open HM.interp Sig BaseInterp1

  input : ⟦ list (base label [×] base number) ⟧ty .idx .Carrier
  input = 3 , (label.a , 0) , (label.b , 1) , (label.a , 1) , _

  open indexed-family._⇒f_
  open SM._⇒_
  open FD using (_∷_; [])

  fwd-slice : _ → _
  fwd-slice n = ⟦ example.ex.query label.a ⟧tm .famf .transf (_ , input) .func n

  -- Output depends on the 1st and 3rd numbers (those with label a), not the 2nd.
  test-1 : fwd-slice (lift · , ([] , (⊤ ∷ [])) , ([] , (⊥ ∷ [])) , ([] , (⊥ ∷ [])) , _) ≡ (⊤ ∷ [])
  test-1 = ≡-refl

  test-2 : fwd-slice (lift · , ([] , (⊥ ∷ [])) , ([] , (⊤ ∷ [])) , ([] , (⊥ ∷ [])) , _) ≡ (⊥ ∷ [])
  test-2 = ≡-refl

  test-3 : fwd-slice (lift · , ([] , (⊥ ∷ [])) , ([] , (⊥ ∷ [])) , ([] , (⊤ ∷ [])) , _) ≡ (⊤ ∷ [])
  test-3 = ≡-refl

-- Backward analysis (Galois) via to-gal on the matrix-new model, replacing ho-model-galois.
module backward-mat where
  open import categories using (Category; HasTerminal; HasInitial; IsInitial; IsTerminal; HasProducts)
  import cmon-enriched as CMon
  import matrix-new
  import ho-model-matrix-new
  import nat
  import galois
  import preorder
  import indexed-family

  module HM = ho-model-matrix-new semiring-bool.semiring
  module FD = matrix-new.Mat semiring-bool.semiring
  open CMon.CMonEnriched FD.cmon using (_+m_)
  open FD using (_∷_; [])

  unitm : FD._⇒_ 0 1
  unitm = HasInitial.from-initial FD.initial {1}

  conjunctm : FD._⇒_ (HasProducts.prod FD.products 1 1) 1
  conjunctm = HasProducts.p₁ FD.products {1} {1} +m HasProducts.p₂ FD.products {1} {1}

  open import example-signature-interpretation FD.cat FD.products FD.terminal 1 unitm conjunctm
  open HM.interp Sig BaseInterp1

  open HM.interp-sd.ty-bsddl-mod Sig BaseInterp1 semiring-bool.boolean
    using (BooleanSDDL; to-gal; 𝟘b; ⊕b; ty-bsddl)

  input : ⟦ list (base label [×] base number) ⟧ty .idx .Carrier
  input = 3 , (label.a , 0) , (label.b , 1) , (label.a , 1) , _

  input-ty : first-order-data (list (base label [×] base number))
  input-ty = list (base label [×] base number)

  open indexed-family._⇒f_
  open galois._⇒g_
  open preorder._=>_

  -- Galois backward slice: the upper adjoint of the query morphism, applied to full output demand.
  bwd-slice : label.label → _
  bwd-slice l =
    to-gal (⊕b 𝟘b (ty-bsddl input-ty input)) (ty-bsddl (base number) nat.zero)
           (⟦ example.ex.query l ⟧tm .famf .transf (_ , input)) .right .fun (⊥ ∷ [])

  -- Galois backward slice. Querying 'a' needs the 1st and 3rd numbers; querying 'b' needs the 2nd.
  test1 : bwd-slice label.a ≡ (lift · , ([] , ⊥ ∷ []) , ([] , ⊤ ∷ []) , ([] , ⊥ ∷ []) , _)
  test1 = ≡-refl

  test2 : bwd-slice label.b ≡ (lift · , ([] , ⊤ ∷ []) , ([] , ⊥ ∷ []) , ([] , ⊤ ∷ []) , _)
  test2 = ≡-refl
