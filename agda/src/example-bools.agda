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
-- WIP: blocked on Agda higher-order unification — the complement laws `x · ¬ x` don't let Agda solve the
-- implicit {x} when the witnesses propagate through the BooleanSDDL constructors (⊓/⊔ aren't injective).
-- Fix: make complement-∧/∨ take x explicitly in semimodule.agda's BooleanSDDL record + constructors.
{-
module backward-mat where
  open import categories using (Category; HasTerminal; HasInitial; IsInitial; IsTerminal; HasProducts)
  import cmon-enriched as CMon
  import matrix-new
  import semimodule
  import ho-model-matrix-new
  import nat
  import galois
  import preorder
  import indexed-family
  open import prop using (tt) renaming (_,_ to _,p_)

  module HM = ho-model-matrix-new semiring-bool.semiring
  module FD = matrix-new.Mat semiring-bool.semiring
  module SM = semimodule semiring-bool.semiring
  open CMon.CMonEnriched FD.cmon using (_+m_)
  open FD using (_∷_; [])

  unitm : FD._⇒_ 0 1
  unitm = HasInitial.from-initial FD.initial {1}
  conjunctm : FD._⇒_ (HasProducts.prod FD.products 1 1) 1
  conjunctm = HasProducts.p₁ FD.products {1} {1} +m HasProducts.p₂ FD.products {1} {1}

  open import example-signature-interpretation FD.cat FD.products FD.terminal 1 unitm conjunctm
  open HM.interp Sig BaseInterp1

  -- S = 2 is a Boolean lattice; every witness is an antisymmetric (tt , tt) pair.
  ⊤-add-top : ∀ {x} → SM.S._≈_ (SM.S._+_ SM.S.ι x) SM.S.ι
  ⊤-add-top = tt ,p tt
  ∧-idem : ∀ {x} → SM.S._≈_ (SM.S._·_ x x) x
  ∧-idem {⊥} = tt ,p tt
  ∧-idem {⊤} = tt ,p tt

  open SM using (𝕀)
  open SM.JoinSemilattices ⊤-add-top using (BooleanSDDL; to-gal) renaming (_≤_ to _≤m_)
  open SM.JoinSemilattices.DistribLattices ⊤-add-top ∧-idem using (𝟘-bsddl; ⊕-bsddl)

  compl-∧ : ∀ {x} → _≤m_ 𝕀 (SM.S._·_ x (¬ x)) SM.S.ε
  compl-∧ {⊥} = tt ,p tt
  compl-∧ {⊤} = tt ,p tt
  compl-∨ : ∀ {x} → _≤m_ 𝕀 SM.S.ι (SM.S._+_ x (¬ x))
  compl-∨ {⊥} = tt ,p tt
  compl-∨ {⊤} = tt ,p tt

  module TB = HM.interp-sd.ty-bsddl-mod Sig BaseInterp1 ∧-idem ⊤-add-top ¬ compl-∧ compl-∨

  input : ⟦ list (base label [×] base number) ⟧ty .idx .Carrier
  input = 3 , (label.a , 0) , (label.b , 1) , (label.a , 1) , _

  input-fod : first-order-data (list (base label [×] base number))
  input-fod = list (base label [×] base number)

  inputBSDDL : BooleanSDDL
  inputBSDDL = ⊕-bsddl ¬ compl-∧ compl-∨
                 (𝟘-bsddl ¬ compl-∧ compl-∨)
                 (TB.ty-bsddl input-fod input)

  outputBSDDL : BooleanSDDL
  outputBSDDL = TB.ty-bsddl (base number) nat.zero

  open indexed-family._⇒f_

  bwd-slice : label.label → _
  bwd-slice l =
    to-gal inputBSDDL outputBSDDL (⟦ example.ex.query l ⟧tm .famf .transf (_ , input)) .right .fun (⊤ ∷ [])
    where
      open galois._⇒g_
      open preorder._=>_
-}
