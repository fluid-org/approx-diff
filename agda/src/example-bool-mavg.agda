{-# OPTIONS --prop --postfix-projections --safe #-}

-- Boolean dependency analysis of the moving-average example: adjacent outputs share an input,
-- and composing the backward and forward derivatives sends a selection of outputs to the outputs
-- related to it by a shared dependency, as in the cognacy analyses of linked visualisations.
module example-bool-mavg where

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
open Ex.ex using (mavg)
open import label using (a; b)
open import prop using (liftS; LiftS)

-- Model instantiation: Boolean approximations over rational data.
module BoolAlg-𝟚 = boolalg-sd-semimodule two.semiring two.semiring-boolean
module SDSemiMod-𝟚 = sd-semimodule two.semiring
module SemiMod-𝟚 = semimodule two.semiring
open cmon-enriched.CMonEnriched SemiMod-𝟚.cmon-enriched using (_+m_; εm)

Approx : Category.obj BoolAlg-𝟚.cat
Approx = BoolAlg-𝟚.𝕀

approx-unit : Category._⇒_ BoolAlg-𝟚.cat (HasTerminal.witness BoolAlg-𝟚.terminal) Approx
approx-unit = HasInitial.from-initial BoolAlg-𝟚.initial {Approx}
approx-conjunct : Category._⇒_ BoolAlg-𝟚.cat (HasProducts.prod BoolAlg-𝟚.products Approx Approx) Approx
approx-conjunct = HasProducts.p₁ BoolAlg-𝟚.products {Approx} {Approx}
        +m HasProducts.p₂ BoolAlg-𝟚.products {Approx} {Approx}

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
  Approx approx-unit approx-conjunct semiring-Q.setoid num-zero num-add num-mult

-- Boolean-collapse derivative coefficient: zero map at 0, identity elsewhere.
private
  coeff-b : ℚ → Category._⇒_ BoolAlg-𝟚.cat Approx Approx
  coeff-b q with q ≟ 0ℚ
  ... | yes _ = εm
  ... | no _ = Category.id BoolAlg-𝟚.cat Approx

  coeff-cong-b : ∀ {x y} → Setoid._≈_ semiring-Q.setoid x y → Category._≈_ SemiMod-𝟚.cat (coeff-b x) (coeff-b y)
  coeff-cong-b {x} (liftS refl) = Category.≈-refl SemiMod-𝟚.cat {f = coeff-b x}

module D = Deriv coeff-b coeff-cong-b
open ho-model-boolalg-sd-semimod.interp-boolean two.semiring two.semiring-boolean Sig D.BaseInterp1

open indexed-family._⇒f_
open SemiMod-𝟚._⇒_
open BoolAlg-𝟚.SelfDualBooleanAlgebra using (selfDual)

half : ℚ
half = + 1 / 2

input : ⟦ ((base number [×] base number) [×] base number) [×] base number ⟧ty .idx .Carrier
input = ((1ℚ , + 2 / 1) , + 4 / 1) , + 8 / 1

input-ty : first-order-data (((base number [×] base number) [×] base number) [×] base number)
input-ty = ((base number [×] base number) [×] base number) [×] base number

output-ty : first-order-data ((base number [×] base number) [×] base number)
output-ty = (base number [×] base number) [×] base number

-- The first input reaches only the first output ...
test-fwd-first : fwd (mavg half) (_ , input) (lift · , (((⊤ , ⊥) , ⊥) , ⊥))
                 ≡ ((⊤ , ⊥) , ⊥)
test-fwd-first = refl

-- ... and a shared input reaches both adjacent outputs.
test-fwd-shared : fwd (mavg half) (_ , input) (lift · , (((⊥ , ⊤) , ⊥) , ⊥))
                  ≡ ((⊤ , ⊤) , ⊥)
test-fwd-shared = refl

-- Backward derivative of the full output: every input is used.
test-bwd : SDSemiMod-𝟚.conjugate (selfDual (ty (unit [×] input-ty) (_ , input)))
             (selfDual (ty output-ty ((+ 3 / 2 , + 3 / 1) , + 6 / 1)))
             (mor (mavg half) (_ , input)) .func ((⊤ , ⊤) , ⊤)
           ≡ (lift · , (((⊤ , ⊤) , ⊤) , ⊤))
test-bwd = refl

-- Related outputs: backwards from the first output and forwards again. The second output shares
-- an input with the first; the third shares nothing and stays ⊥.
test-related : fwd (mavg half) (_ , input)
                 (SDSemiMod-𝟚.conjugate (selfDual (ty (unit [×] input-ty) (_ , input)))
                    (selfDual (ty output-ty ((+ 3 / 2 , + 3 / 1) , + 6 / 1)))
                    (mor (mavg half) (_ , input)) .func ((⊤ , ⊥) , ⊥))
               ≡ ((⊤ , ⊤) , ⊥)
test-related = refl
