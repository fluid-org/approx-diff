{-# OPTIONS --prop --postfix-projections --safe #-}

-- Linear provenance polynomials for the weighted-sum query, at the free commutative semiring on
-- the input positions (numbered 0-4, in input order; 5 selects the output). Seeding each position
-- with its variable, the forward derivative returns the polynomial x0 + x2 + 2·x3, and evaluating
-- it at the all-ones valuation recovers the counting analysis. Setoid equality of polynomials is
-- the equational theory, so the tests compare renderings under the unverified normaliser.
module example-free-total where

open import categories using (Category; HasInitial; HasProducts; HasTerminal)
import cmon-enriched
import prop
import semimodule
import sd-semimodule
import ho-model-sd-semimod
import semiring-free
import semiring-N
import semiring-Q
import indexed-family
open import commutative-semiring using (CommutativeSemiring)

open import Level using (lift; 0ℓ)
open import Data.Unit renaming (tt to ·) using ()
open import Data.Product using (_,_)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ)
open import Data.String using (String) renaming (_++_ to _++s_)
import Data.Nat.Show
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Integer using (+_; -[1+_])
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _/_)
open import prop-setoid using (Setoid)
open Setoid using (Carrier)
open import example-signature ℚ using (Sig; number; label; approx)
import example
module Ex = example ℚ
open Ex.ex using (total)
open import language-syntax Sig hiding (_,_)
open import label using (a; b)
open import prop using (liftS)

module FS = semiring-free ℕ
open FS using (Poly; var)
open FS.Normalise (λ n → n) (λ n → "x" ++s Data.Nat.Show.show n) using (pretty)

-- Model instantiation: polynomial approximations over rational data.
module SDSemiMod-Free = sd-semimodule FS.semiring
module SemiMod-Free = semimodule FS.semiring
open cmon-enriched.CMonEnriched SemiMod-Free.cmon-enriched using (_+m_)

Approxm : Category.obj SDSemiMod-Free.cat
Approxm = SDSemiMod-Free.𝕀

unitm : Category._⇒_ SDSemiMod-Free.cat (HasTerminal.witness SDSemiMod-Free.terminal) Approxm
unitm = HasInitial.from-initial SDSemiMod-Free.initial {Approxm}
conjunctm : Category._⇒_ SDSemiMod-Free.cat (HasProducts.prod SDSemiMod-Free.products Approxm Approxm) Approxm
conjunctm = HasProducts.p₁ SDSemiMod-Free.products {Approxm} {Approxm}
        +m HasProducts.p₂ SDSemiMod-Free.products {Approxm} {Approxm}

private
  module Num = CommutativeSemiring semiring-Q.semiring

  num-zero : prop-setoid._⇒_ (prop-setoid.𝟙 {0ℓ} {0ℓ}) semiring-Q.setoid
  num-zero = record { func = λ _ → 0ℚ ; func-resp-≈ = λ _ → Num.refl }

  num-add : prop-setoid._⇒_ (prop-setoid.⊗-setoid semiring-Q.setoid semiring-Q.setoid) semiring-Q.setoid
  num-add = record { func = λ (x , y) → Num._+_ x y
                   ; func-resp-≈ = λ e → Num.+-cong (prop.proj₁ e) (prop.proj₂ e) }

  num-mult : prop-setoid._⇒_ (prop-setoid.⊗-setoid semiring-Q.setoid semiring-Q.setoid) semiring-Q.setoid
  num-mult = record { func = λ (x , y) → Num._·_ x y
                    ; func-resp-≈ = λ e → Num.·-cong (prop.proj₁ e) (prop.proj₂ e) }

open import example-signature-interpretation SDSemiMod-Free.cat SDSemiMod-Free.products SDSemiMod-Free.terminal
  Approxm unitm conjunctm semiring-Q.setoid num-zero num-add num-mult

-- Unit coefficients: every argument of every operation counts as one use.
private
  unit-c : ℚ → ℚ → Category._⇒_ SDSemiMod-Free.cat Approxm Approxm
  unit-c _ _ = Category.id SDSemiMod-Free.cat Approxm

  unit-c-cong : ∀ {x x' y y'} → Setoid._≈_ semiring-Q.setoid x x' → Setoid._≈_ semiring-Q.setoid y y' →
                Category._≈_ SemiMod-Free.cat (unit-c x y) (unit-c x' y')
  unit-c-cong _ _ = Category.≈-refl SemiMod-Free.cat {f = unit-c 0ℚ 0ℚ}

module D = BinDeriv unit-c unit-c unit-c unit-c unit-c-cong unit-c-cong unit-c-cong unit-c-cong
open ho-model-sd-semimod.interp-sd FS.semiring Sig D.BaseInterp1
open SDSemiMod-Free using (conjugate)

open indexed-family._⇒f_
open SemiMod-Free._⇒_

-- The run of the introduction, with each perturbable position seeded by its variable.
input : ⟦ (list (base label [×] base number)) [×] (base number [×] base number) ⟧ty .idx .Carrier
input = (3 , (a , + 3 / 1) , (b , 1ℚ) , (a , -[1+ 2 ] / 1) , _) , (+ 2 / 1 , + 5 / 1)

input-ty : first-order-data ((list (base label [×] base number)) [×] (base number [×] base number))
input-ty = list (base label [×] base number) [×] (base number [×] base number)

fwd-poly : Poly
fwd-poly = fwd (total a) (_ , input)
             (lift · , ((lift · , var 0) , (lift · , var 1) , (lift · , var 2) , _) , (var 3 , var 4))

-- The output's linear provenance polynomial: each selected quantity once, the queried price twice.
test-fwd : pretty fwd-poly ≡ "x0 + x2 + 2·x3"
test-fwd = refl

-- Evaluating the polynomial at the all-ones valuation recovers the counting analysis.
test-eval-counting : FS.Eval.eval semiring-N.semiring (λ _ → 1) fwd-poly ≡ 4
test-eval-counting = refl

bwd-polys : List Poly
bwd-polys =
  let (_ , ((_ , p₁) , (_ , p₂) , (_ , p₃) , _) , (ppa , ppb)) =
        conjugate (ty (unit [×] input-ty) (_ , input)) (ty (base number) 0ℚ)
          (mor (total a) (_ , input)) .func (var 5)
  in p₁ ∷ p₂ ∷ p₃ ∷ ppa ∷ ppb ∷ []

-- Backwards, with the output selected symbolically: the transpose distributes the output variable
-- to the used positions, twice to the price.
test-bwd : map pretty bwd-polys ≡ "x5" ∷ "0" ∷ "x5" ∷ "2·x5" ∷ "0" ∷ []
test-bwd = refl
