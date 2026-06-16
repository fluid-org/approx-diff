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
import conjugate

open import example-signature

module L = language-syntax Sig

import indexed-family
import join-semilattice-category
import join-semilattice
import preorder
import prop-setoid

open import two renaming (I to ⊤; O to ⊥)
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

-- Forward analysis (Conjugate).
module forward where
  import ho-model-conjugate
  open import example-signature-interpretation conjugate.cat conjugate.products conjugate.terminal conjugate.TWO conjugate.unit conjugate.conjunct
  open ho-model-conjugate.interp Sig BaseInterp1

  input : ⟦ list (base label [×] base number) ⟧ty .idx .Carrier
  input = 3 , (label.a , 0) , (label.b , 1) , (label.a , 1) , _

  -- bwd-slice behaves the same as in the Galois examples, but fwd-slice does not
  fwd-slice : _ → _
  fwd-slice supply = ⟦ example.ex.query label.a ⟧tm .famf .transf (_ , input) .proj₁ .*→* .func .fun (· , supply)
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

-- Matrix model variant.
module forward-matrix where
  open import categories using (Category; HasTerminal; HasInitial; IsInitial; IsTerminal; HasProducts)

  import join-semilattice-category as SemiLat
  import cmon-enriched as CMon
  open CMon.CMonEnriched SemiLat.cmon-enriched using (_+m_)
  open CMon using (biproducts→products)

  import ho-model-matrix
  open ho-model-matrix

  private
    module MatRep = Category cat

    products : HasProducts cat
    products = biproducts→products cmon biproduct

  unitm : MatRep._⇒_ 0 1
  unitm = HasInitial.from-initial initial {1}

  conjunctm : MatRep._⇒_ (HasProducts.prod products 1 1) 1
  conjunctm = HasProducts.p₁ products {1} {1} +m HasProducts.p₂ products {1} {1}

  open import example-signature-interpretation cat products terminal 1 unitm conjunctm
  open ho-model-matrix.interp Sig BaseInterp1

  input : ⟦ list (base label [×] base number) ⟧ty .idx .Carrier
  input = 3 , (label.a , 0) , (label.b , 1) , (label.a , 1) , _

  open indexed-family._⇒f_
  open SemiLat._⇒_
  open join-semilattice._=>_
  open preorder._=>_

  -- Reproduce the conjugate example (fwd direction only) via the matrix model.
  fwd-slice : _ → _
  fwd-slice n = ⟦ example.ex.query label.a ⟧tm .famf .transf (_ , input) .*→* .func .fun n

  -- Output depends on 1st label (would be ⊥ in the Galois example)
  test-1 : fwd-slice (· , (· , ⊤ , ·) , (· , ⊥ , ·) , (· , ⊥ , ·) , _) ≡ (⊤ , ·)
  test-1 = ≡-refl

  -- Output doesn't depend on 2nd label
  test-2 : fwd-slice (· , (· , ⊥ , ·) , (· , ⊤ , ·) , (· , ⊥ , ·) , _) ≡ (⊥ , ·)
  test-2 = ≡-refl

  -- Output depends on 3rd label (would be ⊥ in the Galois example)
  test-3 : fwd-slice (· , (· , ⊥ , ·) , (· , ⊥ , ·) , (· , ⊤ , ·) , _) ≡ (⊤ , ·)
  test-3 = ≡-refl

module forward-fdsemimod where
  open import categories using (Category; HasTerminal; HasInitial; IsInitial; IsTerminal; HasProducts)

  import cmon-enriched as CMon
  import fd-semimodule
  import semimodule
  import ho-model-fd-semimod

  module FD = fd-semimodule.FDSemiMod two.semiring
  module SM = semimodule.SemiMod two.semiring
  open CMon.CMonEnriched FD.cmon using (_+m_)

  unitm : FD._⇒_ 0 1
  unitm = HasInitial.from-initial FD.initial {1}

  conjunctm : FD._⇒_ (HasProducts.prod FD.products 1 1) 1
  conjunctm = HasProducts.p₁ FD.products {1} {1} +m HasProducts.p₂ FD.products {1} {1}

  open import example-signature-interpretation FD.cat FD.products FD.terminal 1 unitm conjunctm
  open ho-model-fd-semimod.interp Sig BaseInterp1

  input : ⟦ list (base label [×] base number) ⟧ty .idx .Carrier
  input = 3 , (label.a , 0) , (label.b , 1) , (label.a , 1) , _

  open indexed-family._⇒f_
  open SM._⇒_

  fwd-slice : _ → _
  fwd-slice n = ⟦ example.ex.query label.a ⟧tm .famf .transf (_ , input) .func n

  -- Slice values are SemiMod carriers: each sort's slice is a Vec (Fin dim → Two),
  -- list/ctxt units are lifted.  The shape below typechecks (domain accepted); the
  -- ≡-refl reduction currently times out — a performance issue to resume tomorrow.
  -- test-1 : fwd-slice (lift · , ((λ _ → ⊤) , (λ _ → ⊥)) , ((λ _ → ⊥) , (λ _ → ⊥)) , ((λ _ → ⊥) , (λ _ → ⊥)) , _) ≡ (λ _ → ⊤)
  -- test-1 = ≡-refl

-- Forward analysis via the Data.Vec model (FDSemiMod₂).  Same setup as
-- forward-fdsemimod; slice values are now Data.Vec, not functions.
module forward-fdsemimod-2 where
  open import categories using (Category; HasTerminal; HasInitial; IsInitial; IsTerminal; HasProducts)

  import cmon-enriched as CMon
  import fd-semimodule-2
  import semimodule
  import ho-model-fd-semimod-2

  module FD = fd-semimodule-2.FDSemiMod₂ two.semiring
  module SM = semimodule.SemiMod two.semiring
  open CMon.CMonEnriched FD.cmon using (_+m_)

  unitm : FD._⇒_ 0 1
  unitm = HasInitial.from-initial FD.initial {1}

  conjunctm : FD._⇒_ (HasProducts.prod FD.products 1 1) 1
  conjunctm = HasProducts.p₁ FD.products {1} {1} +m HasProducts.p₂ FD.products {1} {1}

  open import example-signature-interpretation FD.cat FD.products FD.terminal 1 unitm conjunctm
  open ho-model-fd-semimod-2.interp Sig BaseInterp1

  input : ⟦ list (base label [×] base number) ⟧ty .idx .Carrier
  input = 3 , (label.a , 0) , (label.b , 1) , (label.a , 1) , _

  open indexed-family._⇒f_
  open SM._⇒_

  fwd-slice : _ → _
  fwd-slice n = ⟦ example.ex.query label.a ⟧tm .famf .transf (_ , input) .func n

  -- For interactive testing: slice values are Data.Vec now (a Vec 1 leaf is
  -- `x ∷ []`), units still lifted.  e.g. (uncomment and normalise in VSCode):
  -- test-1 : fwd-slice (lift · , ((⊤ ∷ []) , (⊥ ∷ [])) , ((⊥ ∷ []) , (⊥ ∷ [])) , ((⊥ ∷ []) , (⊥ ∷ [])) , _) ≡ (⊤ ∷ [])
  -- test-1 = ≡-refl
