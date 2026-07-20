{-# OPTIONS --prop --postfix-projections --safe #-}

-- Forward and backward analysis of the example query in the perturbation-bound model: a number is
-- approximated in two dimensions (left and right perturbation bound), and the dependency relations
-- are min-plus matrices. Addition propagates bounds unchanged; multiplication admits no
-- min-plus-linear bound, recorded by the constantly-∞ matrix.
module example.intervals where

open import categories using (Category)
import prop
import matrix
import semimodule
import sd-semimodule
import ho-model-sd-semimod
import semiring-Q-tropical-add
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
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _/_) public
open import Data.Nat.Base public using (nonZero)
open import Data.Integer.Base public using (nonNeg)
open import Data.Integer using (+_; -[1+_]) public
open import prop using (liftS)
open import prop-setoid using (Setoid; IsEquivalence)
open Setoid using (Carrier) public
open import example.signature ℚ
  using (Sig; sort; number; label; op; rel; lit; add; mult; lbl; equal-label) public
import example
open import language-syntax Sig hiding (_,_) public
module Ex = example ℚ 0ℚ
open Ex.ex public
open import label using (a; b) public
open semiring-Q-tropical-add public using (∞; fin)

private
  open matrix.Mat semiring-Q-tropical-add.semiring using (_∥_; block)
  module Mℚ∞ = matrix.Mat semiring-Q-tropical-add.semiring
  module Num = CommutativeSemiring semiring-Q.semiring
  open prop-setoid._⇒_

private
  -- Addition passes each argument's bounds through unchanged: the block matrix [ I₂ , I₂ ].
  add-deps : Category._⇒_ Mℚ∞.cat 4 2
  add-deps = Mℚ∞.I ∥ Mℚ∞.I

primitives : Primitives semiring-Q-tropical-add.semiring Sig
primitives .sort-index number = semiring-Q.setoid
primitives .sort-index label  = label.Label
primitives .sort-width number = 2
primitives .sort-width label  = 0
primitives .op-fun (lit n) .func _ = n
primitives .op-fun add .func (x , y , _) = x Num.+ y
primitives .op-fun mult .func (x , y , _) = x Num.· y
primitives .op-fun (lbl l) .func _ = l
primitives .op-fun (lit n) .func-resp-≈ _ = liftS refl
primitives .op-fun add .func-resp-≈ e =
  Num.+-cong (prop.proj₁ e) (prop.proj₁ (prop.proj₂ e))
primitives .op-fun mult .func-resp-≈ e =
  Num.·-cong (prop.proj₁ e) (prop.proj₁ (prop.proj₂ e))
primitives .op-fun (lbl l) .func-resp-≈ _ =
  Setoid.isEquivalence label.Label .IsEquivalence.refl
primitives .op-deps (lit n) .func _ = Mℚ∞.εₘ
primitives .op-deps add .func _ = add-deps
primitives .op-deps mult .func _ = Mℚ∞.εₘ
primitives .op-deps (lbl l) .func _ = Mℚ∞.εₘ
primitives .op-deps (lit n) .func-resp-≈ _ = Category.≈-refl Mℚ∞.cat {f = Mℚ∞.εₘ}
primitives .op-deps add .func-resp-≈ _ = Category.≈-refl Mℚ∞.cat {f = add-deps}
primitives .op-deps mult .func-resp-≈ _ = Category.≈-refl Mℚ∞.cat {f = Mℚ∞.εₘ}
primitives .op-deps (lbl l) .func-resp-≈ _ = Category.≈-refl Mℚ∞.cat {f = Mℚ∞.εₘ}
primitives .rel-pred equal-label .func (l₁ , l₂ , _) = label.equal-label .func (l₁ , l₂)
primitives .rel-pred equal-label .func-resp-≈ e =
  label.equal-label .func-resp-≈ (prop.proj₁ e prop., prop.proj₁ (prop.proj₂ e))

-- The model determined by the primitives, and the interpretation of the language over it.
module HM = ho-model-sd-semimod semiring-Q-tropical-add.semiring
module PI = HM.interp-primitives Sig primitives
open HM.interp-sd Sig PI.model public
open HM.SDSemiMod public using (conjugate)

-- W-trees indexing the fibres of closed μ-types, for writing inputs.
module T = Pm.Tree {n = 0} (λ ())

module SemiMod-ℚ∞ = semimodule semiring-Q-tropical-add.semiring
open SemiMod-ℚ∞._⇒_ public
