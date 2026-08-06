{-# OPTIONS --prop --postfix-projections --safe #-}

-- Boolean dependency analysis over rational data: a number carries one scalar position, and the
-- dependency relation of an operation at given arguments is the Boolean collapse of the rational
-- Jacobian there, ⊥ where an entry is 0 and ⊤ elsewhere. Model-free: harnesses for any framework
-- instantiate their model at this signature and these primitives.
module example.primitives where

import prop
import matrix
import semiring-Q
open import primitives using (Primitives)
import example.values as V
open Primitives using (sort-index; sort-width; op-fun; op-deps; rel-pred; rel-deps)

open import categories using (Category)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (refl)
open import Data.Product using (_,_)
open import two renaming (I to ⊤; O to ⊥) using () public
open import Data.Rational using (ℚ; 0ℚ)
open import Data.Rational using () renaming (_≟_ to _≟ℚ_)
open import prop-setoid using (Setoid)
open import prop using (liftS)
open import example.signature ℚ using (Sig; sort; number; label; op; rel; lit; add; mult; lbl; equal-label; equal-number) public

private
  open matrix.Mat two.semiring using (_∥_; block)
  module M𝟚 = matrix.Mat two.semiring
  open prop-setoid._⇒_

-- Boolean collapse of a rational: ⊥ at 0, ⊤ elsewhere.
collapse : ℚ → two.Two
collapse q with q ≟ℚ 0ℚ
... | yes _ = ⊥
... | no _  = ⊤

private
  -- The Boolean collapse of the Jacobian of multiplication: [ ∂/∂x , ∂/∂y ] = [ y , x ].
  mult-rel : ℚ → ℚ → Category._⇒_ M𝟚.cat 2 1
  mult-rel x y = block (collapse y) ∥ block (collapse x)

  mult-rel-resp : ∀ {x x' y y'} →
                  Setoid._≈_ semiring-Q.setoid x x' → Setoid._≈_ semiring-Q.setoid y y' →
                  Category._≈_ M𝟚.cat (mult-rel x y) (mult-rel x' y')
  mult-rel-resp {x} {_} {y} (liftS refl) (liftS refl) = Category.≈-refl M𝟚.cat {f = mult-rel x y}

primitives : Primitives two.semiring Sig
primitives .sort-index = V.sort-index
primitives .sort-width number = 1
primitives .sort-width label  = 0
primitives .op-fun = V.op-fun
primitives .rel-pred = V.rel-pred
primitives .op-deps (lit n) .func _ = M𝟚.εₘ
primitives .op-deps add .func _ = M𝟚.I ∥ M𝟚.I
primitives .op-deps mult .func (x , y , _) = mult-rel x y
primitives .op-deps (lbl l) .func _ = M𝟚.εₘ
primitives .op-deps (lit n) .func-resp-≈ _ = Category.≈-refl M𝟚.cat {f = M𝟚.εₘ}
primitives .op-deps add .func-resp-≈ _ = Category.≈-refl M𝟚.cat {f = M𝟚.I ∥ M𝟚.I}
primitives .op-deps mult .func-resp-≈ e =
  mult-rel-resp (prop.proj₁ e) (prop.proj₁ (prop.proj₂ e))
primitives .op-deps (lbl l) .func-resp-≈ _ = Category.≈-refl M𝟚.cat {f = M𝟚.εₘ}
primitives .rel-deps equal-label .func _ = M𝟚.εₘ
primitives .rel-deps equal-label .func-resp-≈ _ = Category.≈-refl M𝟚.cat {f = M𝟚.εₘ}
primitives .rel-deps equal-number .func _ = M𝟚.I ∥ M𝟚.I
primitives .rel-deps equal-number .func-resp-≈ _ = Category.≈-refl M𝟚.cat {f = M𝟚.I ∥ M𝟚.I}

sort-val : sort → Set
sort-val = Primitives.sort-val primitives
