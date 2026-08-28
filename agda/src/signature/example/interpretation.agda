{-# OPTIONS --prop --postfix-projections --safe #-}

-- The example signature over rational data, weighted in any commutative semiring: a number is a
-- rational carrying one scalar position, a label carries none, and the dependency relation of an
-- operation at given arguments is its rational Jacobian there, read as weights.
open import Level using (0ℓ)
open import prop-setoid using (Setoid; IsEquivalence; +-setoid; 𝟙)
open import commutative-semiring using (CommutativeSemiring)

open import Data.Rational using (ℚ)
module signature.example.interpretation {A : Setoid 0ℓ 0ℓ} (as-weight : ℚ → Setoid.Carrier A)
                                        (S : CommutativeSemiring A) where

import prop
import matrix
import semiring-Q
import label
open import signature.interpretation using (Interpretation)
open Interpretation using (sort-index; sort-width; op-fun; op-deps; rel-pred; rel-deps)

open import categories using (Category)
open import Relation.Binary.PropositionalEquality using (refl)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import prop using (liftS)
open import Data.Rational using (0ℚ) renaming (_≟_ to _≟ℚ_)
open import Relation.Nullary using (yes; no)
open import signature.example ℚ
  using (Sig; sort; number; label; op; rel; lit; add; mult; lbl; equal-label; equal-number)
  public

private
  module Scalars = CommutativeSemiring semiring-Q.semiring
  open matrix.Mat S using (_∥_; block)
  module MS = matrix.Mat S
  open Category MS.cat using (_⇒_; _≈_; ≈-refl)
  open prop-setoid._⇒_

private
  -- The Jacobian of multiplication: [ ∂/∂x , ∂/∂y ] = [ y , x ].
  mult-rel : ℚ → ℚ → 2 ⇒ 1
  mult-rel x y = block (as-weight y) ∥ block (as-weight x)

  mult-rel-resp : ∀ {x x' y y'} →
                  Setoid._≈_ semiring-Q.setoid x x' → Setoid._≈_ semiring-Q.setoid y y' →
                  mult-rel x y ≈ mult-rel x' y'
  mult-rel-resp {x} {_} {y} (liftS refl) (liftS refl) = ≈-refl {f = mult-rel x y}

  eq-out : ℚ → ℚ → Setoid.Carrier (+-setoid (𝟙 {0ℓ} {0ℓ}) 𝟙)
  eq-out x y with x ≟ℚ y
  ... | yes _ = inj₁ _
  ... | no  _ = inj₂ _

interpretation : Interpretation S Sig
interpretation .sort-index number = semiring-Q.setoid
interpretation .sort-index label  = label.Label
interpretation .sort-width number = 1
interpretation .sort-width label  = 0
interpretation .op-fun (lit n) .func _ = n
interpretation .op-fun add .func (x , y , _) = x Scalars.+ y
interpretation .op-fun mult .func (x , y , _) = x Scalars.· y
interpretation .op-fun (lbl l) .func _ = l
interpretation .op-fun (lit n) .func-resp-≈ _ = liftS refl
interpretation .op-fun add .func-resp-≈ e = Scalars.+-cong (prop.proj₁ e) (prop.proj₁ (prop.proj₂ e))
interpretation .op-fun mult .func-resp-≈ e = Scalars.·-cong (prop.proj₁ e) (prop.proj₁ (prop.proj₂ e))
interpretation .op-fun (lbl l) .func-resp-≈ _ = Setoid.isEquivalence label.Label .IsEquivalence.refl
interpretation .op-deps (lit n) .func _ = MS.εₘ
interpretation .op-deps add .func _ = MS.I ∥ MS.I
interpretation .op-deps mult .func (x , y , _) = mult-rel x y
interpretation .op-deps (lbl l) .func _ = MS.εₘ
interpretation .op-deps (lit n) .func-resp-≈ _ = ≈-refl {f = MS.εₘ}
interpretation .op-deps add .func-resp-≈ _ = ≈-refl {f = MS.I ∥ MS.I}
interpretation .op-deps mult .func-resp-≈ e = mult-rel-resp (prop.proj₁ e) (prop.proj₁ (prop.proj₂ e))
interpretation .op-deps (lbl l) .func-resp-≈ _ = ≈-refl {f = MS.εₘ}
interpretation .rel-pred equal-label .func (l₁ , l₂ , _) = label.equal-label .func (l₁ , l₂)
interpretation .rel-pred equal-label .func-resp-≈ e =
  label.equal-label .func-resp-≈ (prop.proj₁ e prop., prop.proj₁ (prop.proj₂ e))
interpretation .rel-pred equal-number .func (x , y , _) = eq-out x y
interpretation .rel-pred equal-number .func-resp-≈ {x , y , _} {x' , y' , _}
  (liftS refl prop., (liftS refl prop., _)) =
  Setoid.isEquivalence (+-setoid (𝟙 {0ℓ} {0ℓ}) 𝟙) .IsEquivalence.refl {eq-out x y}
interpretation .rel-deps equal-label .func _ = MS.εₘ
interpretation .rel-deps equal-label .func-resp-≈ _ = ≈-refl {f = MS.εₘ}
interpretation .rel-deps equal-number .func _ = MS.I ∥ MS.I
interpretation .rel-deps equal-number .func-resp-≈ _ = ≈-refl {f = MS.I ∥ MS.I}

sort-val : sort → Set
sort-val = Interpretation.sort-val interpretation
