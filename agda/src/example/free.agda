{-# OPTIONS --prop --postfix-projections --safe #-}

-- Test harness for the free commutative semiring on ℕ-numbered input positions: rational data,
-- unit coefficients, so fibre values are linear provenance polynomials. Setoid equality of
-- polynomials is the equational theory, so tests compare renderings under the unverified
-- normaliser.
module example.free where

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

open import Level using (lift; 0ℓ) public
open import Data.Unit renaming (tt to ·) using () public
open import Data.Product using (_,_) public
open import Data.List using (List; []; _∷_; map) public
open import Data.Nat using (ℕ) public
open import Data.Nat.Base public using (nonZero)
open import Data.String using (String) renaming (_++_ to _++s_) public
import Data.Nat.Show
open import Relation.Binary.PropositionalEquality using (_≡_; refl) public
open import Data.Integer using (+_; -[1+_]) public
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _/_) public
open import prop-setoid using (Setoid)
open Setoid using (Carrier) public
open import example.signature ℚ using (Sig; number; label; approx) public
import example
module Ex = example ℚ 0ℚ
open Ex.ex public
open import language-syntax Sig hiding (_,_) public
open import label using (a; b) public
open import prop using (liftS)

module Free = semiring-free ℕ
open Free public using (Poly; var)
open Free.Normalise (λ n → n) (λ n → "x" ++s Data.Nat.Show.show n) public using (pretty)

-- Model instantiation: polynomial approximations over rational data.
module SDSemiMod-Free = sd-semimodule Free.semiring
module SemiMod-Free = semimodule Free.semiring
open cmon-enriched.CMonEnriched SemiMod-Free.cmon-enriched using (_+m_)

Approx : Category.obj SDSemiMod-Free.cat
Approx = SDSemiMod-Free.𝕀

approx-unit : Category._⇒_ SDSemiMod-Free.cat (HasTerminal.witness SDSemiMod-Free.terminal) Approx
approx-unit = HasInitial.from-initial SDSemiMod-Free.initial {Approx}

approx-conjunct : Category._⇒_ SDSemiMod-Free.cat (HasProducts.prod SDSemiMod-Free.products Approx Approx) Approx
approx-conjunct = HasProducts.p₁ SDSemiMod-Free.products {Approx} {Approx} +m
            HasProducts.p₂ SDSemiMod-Free.products {Approx} {Approx}

private
  module Num = CommutativeSemiring semiring-Q.semiring
  open prop-setoid._⇒_

  num-add : prop-setoid._⇒_ (prop-setoid.⊗-setoid semiring-Q.setoid semiring-Q.setoid) semiring-Q.setoid
  num-add .func (x , y) = x Num.+ y
  num-add .func-resp-≈ e = Num.+-cong (prop.proj₁ e) (prop.proj₂ e)

  num-mult : prop-setoid._⇒_ (prop-setoid.⊗-setoid semiring-Q.setoid semiring-Q.setoid) semiring-Q.setoid
  num-mult .func (x , y) = x Num.· y
  num-mult .func-resp-≈ e = Num.·-cong (prop.proj₁ e) (prop.proj₂ e)

open import example.signature-interpretation SDSemiMod-Free.cat SDSemiMod-Free.products SDSemiMod-Free.terminal
  Approx approx-unit approx-conjunct semiring-Q.setoid num-add num-mult

-- Unit coefficients: every argument of every operation counts as one use.
private
  unit-c : ℚ → ℚ → Category._⇒_ SDSemiMod-Free.cat Approx Approx
  unit-c _ _ = Category.id SDSemiMod-Free.cat Approx

  unit-c-cong : ∀ {x x' y y'} → Setoid._≈_ semiring-Q.setoid x x' → Setoid._≈_ semiring-Q.setoid y y' →
                Category._≈_ SemiMod-Free.cat (unit-c x y) (unit-c x' y')
  unit-c-cong _ _ = Category.≈-refl SemiMod-Free.cat {f = unit-c 0ℚ 0ℚ}

module D = BinDeriv unit-c unit-c unit-c unit-c unit-c-cong unit-c-cong unit-c-cong unit-c-cong
open ho-model-sd-semimod.interp-sd Free.semiring Sig D.BaseInterp1 public
open SDSemiMod-Free public using (conjugate)

open indexed-family._⇒f_ public
open SemiMod-Free._⇒_ public

