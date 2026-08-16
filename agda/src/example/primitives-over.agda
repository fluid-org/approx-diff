{-# OPTIONS --prop --postfix-projections --safe #-}

-- Dependency analysis over rational data, weighted in any commutative semiring: a number carries
-- one scalar position, and the dependency relation of an operation at given arguments is the
-- collapse of the rational Jacobian there, ε where an entry is 0 and ι elsewhere.
open import Level using (0ℓ)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)

module example.primitives-over {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A) where

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
open import Data.Rational using (ℚ; 0ℚ) renaming (_≟_ to _≟ℚ_)
open import prop using (liftS)
open import signature.example ℚ
  using (Sig; sort; number; label; op; rel; lit; add; mult; lbl; equal-label; equal-number)
  public

private
  module Sc = CommutativeSemiring S
  open matrix.Mat S using (_∥_; block)
  module MS = matrix.Mat S
  open prop-setoid._⇒_

-- Collapse of a rational: ε at 0, ι elsewhere.
collapse : ℚ → Setoid.Carrier A
collapse q with q ≟ℚ 0ℚ
... | yes _ = Sc.ε
... | no _  = Sc.ι

private
  -- The collapse of the Jacobian of multiplication: [ ∂/∂x , ∂/∂y ] = [ y , x ].
  mult-rel : ℚ → ℚ → Category._⇒_ MS.cat 2 1
  mult-rel x y = block (collapse y) ∥ block (collapse x)

  mult-rel-resp : ∀ {x x' y y'} →
                  Setoid._≈_ semiring-Q.setoid x x' → Setoid._≈_ semiring-Q.setoid y y' →
                  Category._≈_ MS.cat (mult-rel x y) (mult-rel x' y')
  mult-rel-resp {x} {_} {y} (liftS refl) (liftS refl) = Category.≈-refl MS.cat {f = mult-rel x y}

primitives : Primitives S Sig
primitives .sort-index = V.sort-index
primitives .sort-width number = 1
primitives .sort-width label  = 0
primitives .op-fun = V.op-fun
primitives .rel-pred = V.rel-pred
primitives .op-deps (lit n) .func _ = MS.εₘ
primitives .op-deps add .func _ = MS.I ∥ MS.I
primitives .op-deps mult .func (x , y , _) = mult-rel x y
primitives .op-deps (lbl l) .func _ = MS.εₘ
primitives .op-deps (lit n) .func-resp-≈ _ = Category.≈-refl MS.cat {f = MS.εₘ}
primitives .op-deps add .func-resp-≈ _ = Category.≈-refl MS.cat {f = MS.I ∥ MS.I}
primitives .op-deps mult .func-resp-≈ e =
  mult-rel-resp (prop.proj₁ e) (prop.proj₁ (prop.proj₂ e))
primitives .op-deps (lbl l) .func-resp-≈ _ = Category.≈-refl MS.cat {f = MS.εₘ}
primitives .rel-deps equal-label .func _ = MS.εₘ
primitives .rel-deps equal-label .func-resp-≈ _ = Category.≈-refl MS.cat {f = MS.εₘ}
primitives .rel-deps equal-number .func _ = MS.I ∥ MS.I
primitives .rel-deps equal-number .func-resp-≈ _ = Category.≈-refl MS.cat {f = MS.I ∥ MS.I}

sort-val : sort → Set
sort-val = Primitives.sort-val primitives
