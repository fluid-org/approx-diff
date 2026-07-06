{-# OPTIONS --prop --postfix-projections --safe #-}

-- Shared setup for the example harnesses over the self-dual semimodules: the approximation
-- object's monoid structure, the interpretation of numbers, and the model instantiation,
-- parameterised by the scalar semiring and the derivative coefficients.
module example-harness where

open import Level using (lift; 0ℓ)
open import categories using (Category; HasInitial; HasProducts; HasTerminal)
import cmon-enriched
import prop
import semimodule
import sd-semimodule
import ho-model-sd-semimod
import semiring-Q
import nat
import boolalg-sd-semimodule
import ho-model-boolalg-sd-semimod
import indexed-family
open import commutative-semiring using (CommutativeSemiring; BooleanAlgebra)
open import Data.Product using (_,_)
open import Data.Rational using (ℚ; 0ℚ)
open import prop-setoid using (Setoid)

-- What a number is: a carrier setoid with zero, addition and multiplication on it.
record Numbers : Set₁ where
  field
    Numₛ : Setoid 0ℓ 0ℓ
    num-zero : prop-setoid._⇒_ (prop-setoid.𝟙 {0ℓ} {0ℓ}) Numₛ
    num-add  : prop-setoid._⇒_ (prop-setoid.⊗-setoid Numₛ Numₛ) Numₛ
    num-mult : prop-setoid._⇒_ (prop-setoid.⊗-setoid Numₛ Numₛ) Numₛ

rationals : Numbers
rationals .Numbers.Numₛ = semiring-Q.setoid
rationals .Numbers.num-zero = record { func = λ _ → 0ℚ ; func-resp-≈ = λ _ → Num.refl }
  where module Num = CommutativeSemiring semiring-Q.semiring
rationals .Numbers.num-add =
  record { func = λ (x , y) → Num._+_ x y
         ; func-resp-≈ = λ e → Num.+-cong (prop.proj₁ e) (prop.proj₂ e) }
  where module Num = CommutativeSemiring semiring-Q.semiring
rationals .Numbers.num-mult =
  record { func = λ (x , y) → Num._·_ x y
         ; func-resp-≈ = λ e → Num.·-cong (prop.proj₁ e) (prop.proj₂ e) }
  where module Num = CommutativeSemiring semiring-Q.semiring

naturals : Numbers
naturals .Numbers.Numₛ = nat.ℕₛ
naturals .Numbers.num-zero = nat.zero-m
naturals .Numbers.num-add = nat.add
naturals .Numbers.num-mult = nat.mult

-- Harness over SDSemiMod(S) with rational data, parameterised by the approximation object and the
-- derivative coefficients of the binary arithmetic primitives.
module SDSemiMod-model {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (Approx : Category.obj (sd-semimodule.cat S))
  (D : Numbers) (open Numbers D)
  (add-c₁ add-c₂ mult-c₁ mult-c₂ : Setoid.Carrier Numₛ → Setoid.Carrier Numₛ →
                                   Category._⇒_ (sd-semimodule.cat S) Approx Approx)
  (add-c₁-cong : ∀ {x x' y y'} → Setoid._≈_ Numₛ x x' → Setoid._≈_ Numₛ y y' →
                 Category._≈_ (semimodule.cat S) (add-c₁ x y) (add-c₁ x' y'))
  (add-c₂-cong : ∀ {x x' y y'} → Setoid._≈_ Numₛ x x' → Setoid._≈_ Numₛ y y' →
                 Category._≈_ (semimodule.cat S) (add-c₂ x y) (add-c₂ x' y'))
  (mult-c₁-cong : ∀ {x x' y y'} → Setoid._≈_ Numₛ x x' → Setoid._≈_ Numₛ y y' →
                  Category._≈_ (semimodule.cat S) (mult-c₁ x y) (mult-c₁ x' y'))
  (mult-c₂-cong : ∀ {x x' y y'} → Setoid._≈_ Numₛ x x' → Setoid._≈_ Numₛ y y' →
                  Category._≈_ (semimodule.cat S) (mult-c₂ x y) (mult-c₂ x' y'))
  where

  module SDSemiMod = sd-semimodule S
  module SemiMod = semimodule S
  open cmon-enriched.CMonEnriched SemiMod.cmon-enriched using (_+m_)

  open import example-signature (Setoid.Carrier Numₛ) using (Sig)

  approx-unit : Category._⇒_ SDSemiMod.cat (HasTerminal.witness SDSemiMod.terminal) Approx
  approx-unit = HasInitial.from-initial SDSemiMod.initial {Approx}

  approx-conjunct : Category._⇒_ SDSemiMod.cat (HasProducts.prod SDSemiMod.products Approx Approx) Approx
  approx-conjunct = HasProducts.p₁ SDSemiMod.products {Approx} {Approx} +m
                    HasProducts.p₂ SDSemiMod.products {Approx} {Approx}

  open import example-signature-interpretation SDSemiMod.cat SDSemiMod.products SDSemiMod.terminal
    Approx approx-unit approx-conjunct Numₛ num-zero num-add num-mult public

  module D = BinDeriv add-c₁ add-c₂ mult-c₁ mult-c₂ add-c₁-cong add-c₂-cong mult-c₁-cong mult-c₂-cong
  open ho-model-sd-semimod.interp-sd S Sig D.BaseInterp1 public
  open SDSemiMod public using (conjugate)

  open indexed-family._⇒f_ public
  open SemiMod._⇒_ public

-- The common special case: every argument of every operation has the identity coefficient, and
-- the approximation object is the scalars.
module SDSemiMod-model-unit {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (D : Numbers) (open Numbers D) where
  private
    unit-c : Setoid.Carrier Numₛ → Setoid.Carrier Numₛ →
             Category._⇒_ (sd-semimodule.cat S) (sd-semimodule.𝕀 S) (sd-semimodule.𝕀 S)
    unit-c _ _ = Category.id (sd-semimodule.cat S) (sd-semimodule.𝕀 S)

    unit-c-cong : ∀ {x x' y y'} → Setoid._≈_ Numₛ x x' → Setoid._≈_ Numₛ y y' →
                  Category._≈_ (semimodule.cat S) (unit-c x y) (unit-c x' y')
    unit-c-cong {x} {_} {y} _ _ = Category.≈-refl (semimodule.cat S) {f = unit-c x y}

  open SDSemiMod-model S (sd-semimodule.𝕀 S) D unit-c unit-c unit-c unit-c
    unit-c-cong unit-c-cong unit-c-cong unit-c-cong public

-- The AD-style case: addition has identity coefficients and multiplication's coefficient at v is
-- a chosen linear map, in practice multiplication-by-v.
module SDSemiMod-model-scalar {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (D : Numbers) (open Numbers D)
  (coeff : Setoid.Carrier Numₛ → Category._⇒_ (sd-semimodule.cat S) (sd-semimodule.𝕀 S) (sd-semimodule.𝕀 S))
  (coeff-cong : ∀ {x y} → Setoid._≈_ Numₛ x y →
                Category._≈_ (semimodule.cat S) (coeff x) (coeff y))
  where

  private
    unit-c : Setoid.Carrier Numₛ → Setoid.Carrier Numₛ →
             Category._⇒_ (sd-semimodule.cat S) (sd-semimodule.𝕀 S) (sd-semimodule.𝕀 S)
    unit-c _ _ = Category.id (sd-semimodule.cat S) (sd-semimodule.𝕀 S)

    unit-c-cong : ∀ {x x' y y'} → Setoid._≈_ Numₛ x x' → Setoid._≈_ Numₛ y y' →
                  Category._≈_ (semimodule.cat S) (unit-c x y) (unit-c x' y')
    unit-c-cong {x} {_} {y} _ _ = Category.≈-refl (semimodule.cat S) {f = unit-c x y}

  open SDSemiMod-model S (sd-semimodule.𝕀 S) D unit-c unit-c (λ _ y → coeff y) (λ x _ → coeff x)
    unit-c-cong unit-c-cong (λ _ e₂ → coeff-cong e₂) (λ e₁ _ → coeff-cong e₁) public

-- Base layer for harnesses over the self-dual Boolean algebras.
module BoolAlg-model-base {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (S-boolean : BooleanAlgebra S)
  (N : Numbers) (open Numbers N)
  where

  module BoolAlg = boolalg-sd-semimodule S S-boolean
  module SemiMod = semimodule S
  open cmon-enriched.CMonEnriched SemiMod.cmon-enriched using (_+m_)

  open import example-signature (Setoid.Carrier Numₛ) using (Sig)

  Approx : Category.obj BoolAlg.cat
  Approx = BoolAlg.𝕀

  approx-unit : Category._⇒_ BoolAlg.cat (HasTerminal.witness BoolAlg.terminal) Approx
  approx-unit = HasInitial.from-initial BoolAlg.initial {Approx}

  approx-conjunct : Category._⇒_ BoolAlg.cat (HasProducts.prod BoolAlg.products Approx Approx) Approx
  approx-conjunct = HasProducts.p₁ BoolAlg.products {Approx} {Approx}
                +m HasProducts.p₂ BoolAlg.products {Approx} {Approx}

  open import example-signature-interpretation BoolAlg.cat BoolAlg.products BoolAlg.terminal
    Approx approx-unit approx-conjunct Numₛ num-zero num-add num-mult public

-- The value-carrying case, with a single coefficient function: the derivative of multiplication
-- at (x, y) has coefficient (coeff y, coeff x), and addition has identity coefficients.
module BoolAlg-model-coeff {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (S-boolean : BooleanAlgebra S)
  (N : Numbers) (open Numbers N)
  (coeff : Setoid.Carrier Numₛ →
           Category._⇒_ (boolalg-sd-semimodule.cat S S-boolean) (boolalg-sd-semimodule.𝕀 S S-boolean)
                        (boolalg-sd-semimodule.𝕀 S S-boolean))
  (coeff-cong : ∀ {x y} → Setoid._≈_ Numₛ x y →
                Category._≈_ (semimodule.cat S) (coeff x) (coeff y))
  where

  open BoolAlg-model-base S S-boolean N public
  open import example-signature (Setoid.Carrier Numₛ) using (Sig)
  module D = Deriv coeff coeff-cong
  open ho-model-boolalg-sd-semimod.interp-boolean S S-boolean Sig D.BaseInterp1 public

  open indexed-family._⇒f_ public
  open SemiMod._⇒_ public

-- The zero-testing coefficients over rational data: the derivative of an operation reads an
-- argument exactly when the corresponding coefficient of the rational derivative is nonzero.
module BoolAlg-model-nonzero {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (S-boolean : BooleanAlgebra S)
  where

  private
    open import Data.Rational using (_≟_)
    open import Relation.Nullary using (yes; no)
    open import prop using (liftS)
    open import Relation.Binary.PropositionalEquality using (refl)
    open cmon-enriched.CMonEnriched (semimodule.cmon-enriched S) using (εm)

    coeff-b : ℚ → Category._⇒_ (boolalg-sd-semimodule.cat S S-boolean)
                               (boolalg-sd-semimodule.𝕀 S S-boolean) (boolalg-sd-semimodule.𝕀 S S-boolean)
    coeff-b q with q ≟ 0ℚ
    ... | yes _ = εm
    ... | no _ = Category.id (boolalg-sd-semimodule.cat S S-boolean) (boolalg-sd-semimodule.𝕀 S S-boolean)

    coeff-cong-b : ∀ {x y} → Setoid._≈_ semiring-Q.setoid x y →
                   Category._≈_ (semimodule.cat S) (coeff-b x) (coeff-b y)
    coeff-cong-b {x} (liftS refl) = Category.≈-refl (semimodule.cat S) {f = coeff-b x}

  open BoolAlg-model-coeff S S-boolean rationals coeff-b coeff-cong-b public
