{-# OPTIONS --prop --postfix-projections --safe #-}

-- Test harness for the rationals (AD) model: a number carries one scalar position, and the
-- dependency relation of an operation at given arguments is its Jacobian there, with rational
-- entries.
module example.rationals where

open import categories using (Category)
import prop
import matrix
import cmon-enriched
import Data.Nat
import semimodule
import sd-semimodule
import ho-model-sd-semimod
import indexed-family
import semiring-Q
import label
open import primitives using (Primitives)
open Primitives using (sort-index; sort-width; op-fun; op-deps; rel-pred)
open import commutative-semiring using (CommutativeSemiring)

open import Level using (lift; 0ℓ) public
open import Data.Unit renaming (tt to ·) using () public
open import Data.Product using (_,_) public
open import Data.Sum using (inj₁; inj₂) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl) public
open import prop using (liftS) public
open import Data.Rational using (ℚ; 0ℚ; 1ℚ) public
open import prop-setoid using (Setoid; IsEquivalence)
open Setoid using (Carrier) public
open import example.signature ℚ
  using (Sig; sort; number; label; op; rel; lit; add; mult; lbl; equal-label) public
import example
open import language-syntax Sig hiding (_,_) public
module Ex = example ℚ 0ℚ
open Ex.ex public

private
  module Mℚ = matrix.Mat semiring-Q.semiring
  module BCℚ = cmon-enriched.Biproduct
  module Scalars = CommutativeSemiring semiring-Q.semiring
  open prop-setoid._⇒_

  -- Copairing of blocks in Mat, and a scalar as a 1-by-1 block.
  _∥_ : ∀ {m n k} → Category._⇒_ Mℚ.cat m k → Category._⇒_ Mℚ.cat n k → Category._⇒_ Mℚ.cat (m Data.Nat.+ n) k
  _∥_ {m} {n} f g = BCℚ.copair (Mℚ.biproduct m n) f g

  blk : ℚ → Category._⇒_ Mℚ.cat 1 1
  blk c _ _ = c

private
  -- The Jacobian of multiplication: [ ∂/∂x , ∂/∂y ] = [ y , x ].
  mult-jac : ℚ → ℚ → Category._⇒_ Mℚ.cat 2 1
  mult-jac x y = blk y ∥ blk x

  mult-jac-resp : ∀ {x x' y y'} →
                  Setoid._≈_ semiring-Q.setoid x x' → Setoid._≈_ semiring-Q.setoid y y' →
                  Category._≈_ Mℚ.cat (mult-jac x y) (mult-jac x' y')
  mult-jac-resp {x} {_} {y} (liftS refl) (liftS refl) = Category.≈-refl Mℚ.cat {f = mult-jac x y}

primitives : Primitives semiring-Q.semiring Sig
primitives .sort-index number = semiring-Q.setoid
primitives .sort-index label  = label.Label
primitives .sort-width number = 1
primitives .sort-width label  = 0
primitives .op-fun (lit n) .func _ = n
primitives .op-fun add .func (x , y , _) = x Scalars.+ y
primitives .op-fun mult .func (x , y , _) = x Scalars.· y
primitives .op-fun (lbl l) .func _ = l
primitives .op-fun (lit n) .func-resp-≈ _ = liftS refl
primitives .op-fun add .func-resp-≈ e =
  Scalars.+-cong (prop.proj₁ e) (prop.proj₁ (prop.proj₂ e))
primitives .op-fun mult .func-resp-≈ e =
  Scalars.·-cong (prop.proj₁ e) (prop.proj₁ (prop.proj₂ e))
primitives .op-fun (lbl l) .func-resp-≈ _ =
  Setoid.isEquivalence label.Label .IsEquivalence.refl
primitives .op-deps (lit n) .func _ = Mℚ.εₘ
primitives .op-deps add .func _ = Mℚ.I ∥ Mℚ.I
primitives .op-deps mult .func (x , y , _) = mult-jac x y
primitives .op-deps (lbl l) .func _ = Mℚ.εₘ
primitives .op-deps (lit n) .func-resp-≈ _ = Category.≈-refl Mℚ.cat {f = Mℚ.εₘ}
primitives .op-deps add .func-resp-≈ _ = Category.≈-refl Mℚ.cat {f = Mℚ.I ∥ Mℚ.I}
primitives .op-deps mult .func-resp-≈ e =
  mult-jac-resp (prop.proj₁ e) (prop.proj₁ (prop.proj₂ e))
primitives .op-deps (lbl l) .func-resp-≈ _ = Category.≈-refl Mℚ.cat {f = Mℚ.εₘ}
primitives .rel-pred equal-label .func (l₁ , l₂ , _) = label.equal-label .func (l₁ , l₂)
primitives .rel-pred equal-label .func-resp-≈ e =
  label.equal-label .func-resp-≈ (prop.proj₁ e prop., prop.proj₁ (prop.proj₂ e))

-- The model determined by the primitives, and the interpretation of the language over it.
module HM = ho-model-sd-semimod semiring-Q.semiring
module PI = HM.interp-primitives Sig primitives
open HM.interp-sd Sig PI.model public
open HM.SDSemiMod public using (conjugate)

-- W-trees indexing the fibres of closed μ-types, for writing inputs.
module T = Pm.Tree {n = 0} (λ ())

module SemiMod-ℚ = semimodule semiring-Q.semiring
open indexed-family._⇒f_ public
open SemiMod-ℚ._⇒_ public
