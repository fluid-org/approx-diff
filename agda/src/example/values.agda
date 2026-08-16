{-# OPTIONS --prop --postfix-projections --safe #-}

-- The setoid-side data of the example primitives, shared by the models: rational constants and
-- operations, labels, and label equality. The models differ only in their widths and dependency
-- relations.
module example.values where

open import Level using (0ℓ)
import prop
open import prop-setoid using (Setoid; IsEquivalence; +-setoid; 𝟙)
open import primitives using (sort-vals-setoid)
open import commutative-semiring using (CommutativeSemiring)
open import Data.Rational using (ℚ) renaming (_≟_ to _≟ℚ_)
open import Relation.Nullary using (yes; no)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)
open import prop using (liftS)
import semiring-Q
import label
open import signature.example ℚ
  using (sort; number; label; op; rel; lit; add; mult; lbl; equal-label; equal-number)

private
  module Scalars = CommutativeSemiring semiring-Q.semiring
  open prop-setoid._⇒_

sort-index : sort → Setoid 0ℓ 0ℓ
sort-index number = semiring-Q.setoid
sort-index label  = label.Label

op-fun : ∀ {is o} (ω : op is o) → prop-setoid._⇒_ (sort-vals-setoid sort-index is) (sort-index o)
op-fun (lit n) .func _ = n
op-fun add .func (x , y , _) = x Scalars.+ y
op-fun mult .func (x , y , _) = x Scalars.· y
op-fun (lbl l) .func _ = l
op-fun (lit n) .func-resp-≈ _ = liftS refl
op-fun add .func-resp-≈ e = Scalars.+-cong (prop.proj₁ e) (prop.proj₁ (prop.proj₂ e))
op-fun mult .func-resp-≈ e = Scalars.·-cong (prop.proj₁ e) (prop.proj₁ (prop.proj₂ e))
op-fun (lbl l) .func-resp-≈ _ = Setoid.isEquivalence label.Label .IsEquivalence.refl

private
  eq-out : ℚ → ℚ → Setoid.Carrier (+-setoid (𝟙 {0ℓ} {0ℓ}) 𝟙)
  eq-out x y with x ≟ℚ y
  ... | yes _ = inj₁ _
  ... | no  _ = inj₂ _

rel-pred : ∀ {is} (ψ : rel is) →
           prop-setoid._⇒_ (sort-vals-setoid sort-index is) (+-setoid (𝟙 {0ℓ} {0ℓ}) 𝟙)
rel-pred equal-label .func (l₁ , l₂ , _) = label.equal-label .func (l₁ , l₂)
rel-pred equal-label .func-resp-≈ e =
  label.equal-label .func-resp-≈ (prop.proj₁ e prop., prop.proj₁ (prop.proj₂ e))
rel-pred equal-number .func (x , y , _) = eq-out x y
rel-pred equal-number .func-resp-≈ {x , y , _} {x' , y' , _}
  (liftS refl prop., (liftS refl prop., _)) =
  Setoid.isEquivalence (+-setoid (𝟙 {0ℓ} {0ℓ}) 𝟙) .IsEquivalence.refl {eq-out x y}
