{-# OPTIONS --prop --postfix-projections --safe #-}

-- Test harness for Boolean dependency analysis over rational data: a number carries one scalar
-- position, and the dependency relation of an operation at given arguments is the Boolean collapse
-- of the rational Jacobian there, ⊥ where an entry is 0 and ⊤ elsewhere.
module example.dependency where

open import categories using (Category)
import prop
import matrix
import semimodule
import ho-model-sd-semimod
import semiring-Q
import indexed-family
open import primitives using (Primitives)
open Primitives using (sort-index; sort-width; op-fun; op-rel; rel-pred)
open import commutative-semiring using (CommutativeSemiring)

open import Level using (lift; 0ℓ) public
open import Data.Nat using (ℕ)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Unit renaming (tt to ·) using () public
open import Data.Product using (_,_) public
open import Data.Sum using (inj₁; inj₂) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl) public
open import Relation.Nullary using (yes; no)
open import two renaming (I to ⊤; O to ⊥) using () public
open import Data.Integer using (+_; -[1+_]) public
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _/_) public
open import Data.Rational using () renaming (_≟_ to _≟ℚ_)
open import Data.Nat.Base public using (nonZero)
open import prop-setoid using (Setoid; IsEquivalence)
open Setoid using (Carrier) public
open import example.signature ℚ using (Sig; sort; number; label; op; rel; lit; add; mult; lbl; equal-label) public
import example
open import language-syntax Sig hiding (_,_) public
module Ex = example ℚ 0ℚ
open Ex.ex public
open import label using (a; b) public
open import prop using (liftS; LiftS)

private
  module M𝟚 = matrix.Mat two.semiring
  module Scalars = CommutativeSemiring semiring-Q.semiring
  open prop-setoid._⇒_

-- Boolean collapse of a rational: ⊥ at 0, ⊤ elsewhere.
collapse : ℚ → two.Two
collapse q with q ≟ℚ 0ℚ
... | yes _ = ⊥
... | no _  = ⊤

private
  -- The Boolean collapse of the Jacobian of multiplication: [ ∂/∂x , ∂/∂y ] = [ y , x ].
  mult-rel : ℚ → ℚ → Category._⇒_ M𝟚.cat 2 1
  mult-rel x y _ fzero    = collapse y
  mult-rel x y _ (fsuc _) = collapse x

  mult-rel-resp : ∀ {x x' y y'} →
                  Setoid._≈_ semiring-Q.setoid x x' → Setoid._≈_ semiring-Q.setoid y y' →
                  Category._≈_ M𝟚.cat (mult-rel x y) (mult-rel x' y')
  mult-rel-resp {x} {_} {y} (liftS refl) (liftS refl) = Category.≈-refl M𝟚.cat {f = mult-rel x y}

primitives : Primitives two.semiring Sig
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
primitives .op-rel (lit n) .func _ = λ _ ()
primitives .op-rel add .func _ = λ _ _ → ⊤
primitives .op-rel mult .func (x , y , _) = mult-rel x y
primitives .op-rel (lbl l) .func _ = λ ()
primitives .op-rel (lit n) .func-resp-≈ _ = Category.≈-refl M𝟚.cat {f = λ _ ()}
primitives .op-rel add .func-resp-≈ _ = Category.≈-refl M𝟚.cat {f = λ _ _ → ⊤}
primitives .op-rel mult .func-resp-≈ e =
  mult-rel-resp (prop.proj₁ e) (prop.proj₁ (prop.proj₂ e))
primitives .op-rel (lbl l) .func-resp-≈ _ = Category.≈-refl M𝟚.cat {f = λ ()}
primitives .rel-pred equal-label .func (l₁ , l₂ , _) = label.equal-label .func (l₁ , l₂)
primitives .rel-pred equal-label .func-resp-≈ e =
  label.equal-label .func-resp-≈ (prop.proj₁ e prop., prop.proj₁ (prop.proj₂ e))

sort-val : sort → Set
sort-val = Primitives.sort-val primitives

-- The model determined by the primitives, and the interpretation of the language over it.
module HM = ho-model-sd-semimod two.semiring
module PI = HM.interp-primitives Sig primitives
open HM.interp-sd Sig PI.model public

-- W-trees indexing the fibres of closed μ-types, for writing inputs.
module T = Pm.Tree {n = 0} (λ ())

module SemiMod-𝟚 = semimodule two.semiring
open indexed-family._⇒f_ public
open SemiMod-𝟚._⇒_ public
