{-# OPTIONS --prop --postfix-projections --safe #-}

-- Test harness for qualitative (signed) dependency analysis over integer data: values run over ℤ,
-- and a program's fibre map is its Jacobian of signs, the direction (up, down, or ambiguous) in
-- which each output depends on each input. The derivative coefficient of a run value is its sign,
-- so the analysis sees only the sign of the data it abstracts.
module example.signs where

open import categories using (Category; HasInitial; HasProducts; HasTerminal)
import cmon-enriched
import prop
import semimodule
import sd-semimodule
import ho-model-sd-semimod
import indexed-family
import semiring-sign

open import Level using (lift; 0ℓ) public
open import Data.Unit renaming (tt to ·) using () public
open import Data.Product using (_,_) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong₂) public
open import prop using (liftS; LiftS) public
open semiring-sign using (Sign; zer; pos; neg; unk) public
open import Data.Integer using (ℤ; +_; -[1+_]) public
open import Data.Nat.Base using (zero; suc)
import Data.Integer
open import prop-setoid using (Setoid; IsEquivalence)
open Setoid using (Carrier) public
open import commutative-semiring using (CommutativeSemiring)
open import example.signature ℤ using (Sig; number; label; approx) public
import example
open import language-syntax Sig hiding (_,_) public
module Ex = example ℤ (+ 0)
open Ex.ex public

-- Model instantiation: sign approximations over integer data.

module SDSemiMod-S = sd-semimodule semiring-sign.semiring
module SemiMod-S = semimodule semiring-sign.semiring
module Scalars = CommutativeSemiring semiring-sign.semiring
open cmon-enriched.CMonEnriched SemiMod-S.cmon-enriched using (_+m_)

Approx : Category.obj SDSemiMod-S.cat
Approx = SDSemiMod-S.𝕀

approx-unit : Category._⇒_ SDSemiMod-S.cat (HasTerminal.witness SDSemiMod-S.terminal) Approx
approx-unit = HasInitial.from-initial SDSemiMod-S.initial {Approx}
approx-conjunct : Category._⇒_ SDSemiMod-S.cat (HasProducts.prod SDSemiMod-S.products Approx Approx) Approx
approx-conjunct = HasProducts.p₁ SDSemiMod-S.products {Approx} {Approx}
        +m HasProducts.p₂ SDSemiMod-S.products {Approx} {Approx}

ℤ-setoid : Setoid 0ℓ 0ℓ
ℤ-setoid .Setoid.Carrier = ℤ
ℤ-setoid .Setoid._≈_ a b = LiftS 0ℓ (a ≡ b)
ℤ-setoid .Setoid.isEquivalence .IsEquivalence.refl = liftS refl
ℤ-setoid .Setoid.isEquivalence .IsEquivalence.sym (liftS e) = liftS (sym e)
ℤ-setoid .Setoid.isEquivalence .IsEquivalence.trans (liftS e₁) (liftS e₂) = liftS (trans e₁ e₂)

-- The sign of a run value, the abstraction the analysis works at.
sgn : ℤ → Sign
sgn (+ zero)  = zer
sgn (+ suc n) = pos
sgn -[1+ n ]  = neg

private
  open prop-setoid._⇒_
  open prop-setoid._≃m_
  open SemiMod-S._≈m_ using (*≈*)

  cong₂-ℤ : (f : ℤ → ℤ → ℤ) {x x' y y' : ℤ} →
            LiftS 0ℓ (x ≡ x') → LiftS 0ℓ (y ≡ y') → LiftS 0ℓ (f x y ≡ f x' y')
  cong₂-ℤ f (liftS e₁) (liftS e₂) = liftS (cong₂ f e₁ e₂)

  num-add : prop-setoid._⇒_ (prop-setoid.⊗-setoid ℤ-setoid ℤ-setoid) ℤ-setoid
  num-add .func (x , y) = Data.Integer._+_ x y
  num-add .func-resp-≈ e = cong₂-ℤ Data.Integer._+_ (prop.proj₁ e) (prop.proj₂ e)

  num-mult : prop-setoid._⇒_ (prop-setoid.⊗-setoid ℤ-setoid ℤ-setoid) ℤ-setoid
  num-mult .func (x , y) = Data.Integer._*_ x y
  num-mult .func-resp-≈ e = cong₂-ℤ Data.Integer._*_ (prop.proj₁ e) (prop.proj₂ e)

  -- Multiplication by c as a linear endomorphism of the scalars.
  scalar : Sign → Category._⇒_ SDSemiMod-S.cat Approx Approx
  scalar c .SemiMod-S._⇒_.*→* .func x = c Scalars.· x
  scalar c .SemiMod-S._⇒_.*→* .func-resp-≈ e = Scalars.·-cong (Scalars.refl {c}) e
  scalar c .SemiMod-S._⇒_.preserve-ze = Scalars.ε-annihilᵣ {c}
  scalar c .SemiMod-S._⇒_.preserve-+ {x} {y} = Scalars.·-+-distribₗ {c} {x} {y}
  scalar c .SemiMod-S._⇒_.preserve-· {s} {x} =
    Scalars.trans (Scalars.sym (Scalars.·-assoc {c} {s} {x}))
      (Scalars.trans (Scalars.·-cong (Scalars.·-comm {c} {s}) Scalars.refl) (Scalars.·-assoc {s} {c} {x}))

  -- Derivative coefficient of a run value: multiplication by its sign.
  coeff : ℤ → Category._⇒_ SDSemiMod-S.cat Approx Approx
  coeff z = scalar (sgn z)

  coeff-cong : ∀ {x y} → Setoid._≈_ ℤ-setoid x y → Category._≈_ SemiMod-S.cat (coeff x) (coeff y)
  coeff-cong {x} (liftS refl) = Category.≈-refl SemiMod-S.cat {f = coeff x}

open import example.signature-interpretation SDSemiMod-S.cat SDSemiMod-S.products SDSemiMod-S.terminal
  Approx approx-unit approx-conjunct ℤ-setoid num-add num-mult public
module D = Deriv coeff coeff-cong
open ho-model-sd-semimod.interp-sd semiring-sign.semiring Sig D.BaseInterp1 public
open SDSemiMod-S public using (conjugate)

open indexed-family._⇒f_ public
open SemiMod-S._⇒_ public
