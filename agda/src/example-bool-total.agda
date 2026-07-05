{-# OPTIONS --prop --postfix-projections --safe #-}

-- Boolean dependency analysis of the weighted-sum query from the introduction, with rational
-- numbers as the underlying data. Where the rational derivative of the price entry cancels to 0,
-- the Boolean analysis reports ⊤, because disjunction can't cancel.
module example-bool-total where

open import categories using (Category; HasInitial; HasProducts; HasTerminal)
import cmon-enriched
import prop
import semimodule
import sd-semimodule
import boolalg-sd-semimodule
import ho-model-boolalg-sd-semimod
import semiring-Q
import indexed-family
open import commutative-semiring using (CommutativeSemiring)

open import Level using (lift; 0ℓ)
open import Data.Unit renaming (tt to ·) using ()
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)
open import two renaming (I to ⊤; O to ⊥) using ()
open import Data.Integer using (+_; -[1+_])
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _/_; _≟_)
open import prop-setoid using (Setoid)
open Setoid using (Carrier)
open import example-signature ℚ using (Sig; number; label; approx)
import example
open import language-syntax Sig hiding (_,_)
module Ex = example ℚ
open Ex.ex using (total)
open import label using (a; b)
open import prop using (liftS; LiftS)

-- Model instantiation: Boolean approximations over rational data.
module BoolAlg-𝟚 = boolalg-sd-semimodule two.semiring two.semiring-boolean
module SDSemiMod-𝟚 = sd-semimodule two.semiring
module SemiMod-𝟚 = semimodule two.semiring
open cmon-enriched.CMonEnriched SemiMod-𝟚.cmon-enriched using (_+m_; εm)

Approxm : Category.obj BoolAlg-𝟚.cat
Approxm = BoolAlg-𝟚.𝕀

unitm : Category._⇒_ BoolAlg-𝟚.cat (HasTerminal.witness BoolAlg-𝟚.terminal) Approxm
unitm = HasInitial.from-initial BoolAlg-𝟚.initial {Approxm}
conjunctm : Category._⇒_ BoolAlg-𝟚.cat (HasProducts.prod BoolAlg-𝟚.products Approxm Approxm) Approxm
conjunctm = HasProducts.p₁ BoolAlg-𝟚.products {Approxm} {Approxm}
        +m HasProducts.p₂ BoolAlg-𝟚.products {Approxm} {Approxm}

private
  num-zero : prop-setoid._⇒_ (prop-setoid.𝟙 {0ℓ} {0ℓ}) semiring-Q.setoid
  num-zero = record { func = λ _ → 0ℚ ; func-resp-≈ = λ _ → prop-setoid.Setoid.refl semiring-Q.setoid }

  module Scalars = CommutativeSemiring semiring-Q.semiring

  num-add : prop-setoid._⇒_ (prop-setoid.⊗-setoid semiring-Q.setoid semiring-Q.setoid) semiring-Q.setoid
  num-add = record { func = λ (x , y) → Scalars._+_ x y
                   ; func-resp-≈ = λ e → Scalars.+-cong (prop.proj₁ e) (prop.proj₂ e) }

  num-mult : prop-setoid._⇒_ (prop-setoid.⊗-setoid semiring-Q.setoid semiring-Q.setoid) semiring-Q.setoid
  num-mult = record { func = λ (x , y) → Scalars._·_ x y
                    ; func-resp-≈ = λ e → Scalars.·-cong (prop.proj₁ e) (prop.proj₂ e) }

open import example-signature-interpretation BoolAlg-𝟚.cat BoolAlg-𝟚.products BoolAlg-𝟚.terminal
  Approxm unitm conjunctm semiring-Q.setoid num-zero num-add num-mult

-- Boolean-collapse derivative coefficient: zero map at 0, identity elsewhere.
private
  coeff-b : ℚ → Category._⇒_ BoolAlg-𝟚.cat Approxm Approxm
  coeff-b q with q ≟ 0ℚ
  ... | yes _ = εm
  ... | no _ = Category.id BoolAlg-𝟚.cat Approxm

  coeff-cong-b : ∀ {x y} → Setoid._≈_ semiring-Q.setoid x y → Category._≈_ SemiMod-𝟚.cat (coeff-b x) (coeff-b y)
  coeff-cong-b {x} (liftS refl) = Category.≈-refl SemiMod-𝟚.cat {f = coeff-b x}

module D = Deriv coeff-b coeff-cong-b
open ho-model-boolalg-sd-semimod.interp-boolean two.semiring two.semiring-boolean Sig D.BaseInterp1

open indexed-family._⇒f_
open SemiMod-𝟚._⇒_
open BoolAlg-𝟚.SelfDualBooleanAlgebra using (selfDual)

input : ⟦ (list (base label [×] base number)) [×] (base number [×] base number) ⟧ty .idx .Carrier
input = (3 , (a , + 3 / 1) , (b , 1ℚ) , (a , -[1+ 2 ] / 1) , _) , (+ 2 / 1 , + 5 / 1)

input-ty : first-order-data ((list (base label [×] base number)) [×] (base number [×] base number))
input-ty = list (base label [×] base number) [×] (base number [×] base number)

-- ∂₂/∂q₁ = ⊤: the output may depend on the first quantity.
test-q₁ : fwd (total a) (_ , input)
            (lift · , ((lift · , ⊤) , (lift · , ⊥) , (lift · , ⊥) , _) , (⊥ , ⊥))
          ≡ ⊤
test-q₁ = refl

-- ∂₂/∂(price a) = ⊤, although the rational derivative is 0, because disjunction can't cancel.
test-price-a : fwd (total a) (_ , input)
                 (lift · , ((lift · , ⊥) , (lift · , ⊥) , (lift · , ⊥) , _) , (⊤ , ⊥))
               ≡ ⊤
test-price-a = refl

-- ∂₂/∂q₂ = ⊥: the b-labelled row is not consulted.
test-q₂ : fwd (total a) (_ , input)
            (lift · , ((lift · , ⊥) , (lift · , ⊤) , (lift · , ⊥) , _) , (⊥ , ⊥))
          ≡ ⊥
test-q₂ = refl

-- The backward derivative applied to the selected output: the inputs the output may depend on,
-- (1 0 1 1 0), still including the cancelled price a.
test-bwd : SDSemiMod-𝟚.conjugate (selfDual (ty (unit [×] input-ty) (_ , input)))
             (selfDual (ty (base number) 0ℚ))
             (mor (total a) (_ , input)) .func ⊤
           ≡ (lift · , ((lift · , ⊤) , (lift · , ⊥) , (lift · , ⊤) , lift ·) , (⊤ , ⊥))
test-bwd = refl
