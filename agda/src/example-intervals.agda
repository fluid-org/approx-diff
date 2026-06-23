{-# OPTIONS --prop --postfix-projections --safe #-}

-- Examples with rational-interval approximation.

module example-intervals where

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
open import Data.Unit renaming (tt to ·; ⊤ to Unit) using ()
open import Data.Product using (_,_; _×_; proj₁; proj₂)

open prop-setoid.Setoid

open L hiding (_,_)

import example

open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl)

-- Backward analysis (Galois). Example (3) in Section 4.3.
module backward where
  open import ho-model
  open import example-signature-interpretation galois.cat galois.products galois.terminal galois.TWO galois.unit galois.conjunct
  open import prop-setoid using (idS)
    renaming (𝟙 to 𝟙ₛ; const to constₛ)
  open import approx-numbers using (module Galois)
  open import categories using (Category; HasProducts; HasTerminal)

  BaseInterp : Model PFPC[ cat , terminal , products , 𝟚 ] Sig
  BaseInterp .Model.⟦sort⟧ number = Galois.ℚ-intv
  BaseInterp .Model.⟦sort⟧ label = simple[ label.Label , galois.𝟙 ]
  BaseInterp .Model.⟦sort⟧ approx = simple[ 𝟙ₛ , galois.TWO ]
  BaseInterp .Model.⟦op⟧ zero = Galois.zero-mor
  BaseInterp .Model.⟦op⟧ add = Galois.add-mor C.∘ binary2
  BaseInterp .Model.⟦op⟧ (lbl l) = simplef[ constₛ _ l , galois.cat .Category.id _ ]
  BaseInterp .Model.⟦rel⟧ equal-label = predicate label.equal-label C.∘ binary
  BaseInterp .Model.⟦op⟧ approx-unit = simplef[ idS _ , galois.unit ]
  BaseInterp .Model.⟦op⟧ approx-mult = simplef[ prop-setoid.to-𝟙 , galois.conjunct ] C.∘ binary

  import ho-model-galois
  open ho-model-galois.interp Sig BaseInterp
  open import Data.Nat hiding (_/_)
  open import Data.Rational renaming (_≤_ to _≤ℚ_; show to ℚ-show)
  open import Data.Integer hiding (_/_; show; -_)
  open import preorder using (bottom; <_>; LCarrier)
  open import approx-numbers using (Intv)
  open import prop using (liftS)
  open import Data.Product using (Σ) renaming (_×_ to _×ₜ_)

  input : ⟦ list (base label [×] base number) ⟧ty .idx .Carrier
  input = 3 , (label.a , 0ℚ) , (label.b , 1ℚ) , (label.a , 1ℚ) , _

  open Intv

  interval : Intv 1ℚ
  interval .lower = + 9 / 10
  interval .upper = + 11 / 10
  interval .l≤q = liftS (*≤* (+≤+ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))
  interval .q≤u = liftS (*≤* (+≤+ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))))

  open import Data.Maybe

  extract-interval : ∀ {q} → LCarrier (Intv q) → Maybe (ℚ ×ₜ ℚ)
  extract-interval bottom = nothing
  extract-interval < x > = just (x .lower , x .upper)

  bwd-slice : _
  bwd-slice = ⟦ example.ex.query label.a ⟧tm .famf .transf (_ , input) .proj₂ .*→* .func .fun < interval > .proj₂
    where
      open indexed-family._⇒f_
      open join-semilattice-category._⇒_
      open join-semilattice._=>_
      open preorder._=>_

  -- Normalising 'bwd-slice' doesn't seem to work, possibly due to
  -- the use of records and/or the proofs attached to them. We have to
  -- project out the relevant bits individually and test them:

  test1 : extract-interval (bwd-slice .proj₁ .proj₂) ≡ just (- (+ 1 / 10) , + 1 / 10)
  test1 = ≡-refl

  test2 : extract-interval (bwd-slice .proj₂ .proj₁ .proj₂) ≡ nothing
  test2 = ≡-refl

  test3 : extract-interval (bwd-slice .proj₂ .proj₂ .proj₁ .proj₂) ≡ just (+ 9 / 10 , + 11 / 10)
  test3 = ≡-refl

-- Forward analysis: the meet-preserving (upper-adjoint) Galois map add⁎, which unions the shifted input bounds.
module forward where
  open import approx-numbers using (module Galois; Intv)
  open import Data.Rational
  import Data.Rational.Properties
  open import preorder using (bottom; <_>; LCarrier)
  open import prop using (liftS)
  open import Data.Nat hiding (_/_)
  open import Data.Integer hiding (_/_; show; -_)
  open import Data.Maybe
  open import Data.Product using (Σ) renaming (_×_ to _×ₜ_)

  open Intv

  intv1 : Intv 1ℚ
  intv1 .lower = + 4 / 5
  intv1 .upper = + 3 / 2
  intv1 .l≤q = liftS (*≤* (+≤+ (s≤s (s≤s (s≤s (s≤s z≤n))))))
  intv1 .q≤u = liftS (*≤* (+≤+ (s≤s (s≤s z≤n))))

  intv0 : Intv 0ℚ
  intv0 .lower = - (+ 1 / 2)
  intv0 .upper = 0ℚ
  intv0 .l≤q = liftS (*≤* -≤+)
  intv0 .q≤u = liftS Data.Rational.Properties.≤-refl

  extract-interval : ∀ {q} → LCarrier (Intv q) → Maybe (ℚ ×ₜ ℚ)
  extract-interval bottom = nothing
  extract-interval < x > = just (x .lower , x .upper)

  -- [-1/2, 0] around 0 added to [4/5, 3/2] around 1: add⁎ unions the shifted bounds, giving [1/2, 3/2] around 1.
  fwd-add⁎ : _
  fwd-add⁎ = Galois.add-interval 0ℚ 1ℚ .galois._⇒g_.right .preorder._=>_.fun
    (< intv0 > , < intv1 >)

  test-add⁎ : extract-interval fwd-add⁎ ≡ just (+ 1 / 2 , + 3 / 2)
  test-add⁎ = ≡-refl
