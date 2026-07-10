{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- Category-free shape layer of the Fam μ-type construction. Sorts and trees
-- are built from index sets alone: the construction is parameterised by the
-- index setoids of the kinding environment, and constants enter as their index
-- setoids, so the layer mentions no category. The fibre layer over a specific
-- category is built separately on top.
------------------------------------------------------------------------------

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Nat using (ℕ; suc)
import Data.Fin as Fin
open Fin using (Fin)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_) renaming (_×_ to _×T_)
open import prop using (_∧_; _,_; ⊥)
open import prop-setoid using (Setoid; IsEquivalence)
import setoid-cat
import polynomial-functor-2

module fam-mu-types-2.shape (os es : Level) where

open Setoid using (Carrier; isEquivalence) renaming (_≈_ to _≈s_)
open IsEquivalence

-- Index-erased polynomials: constants are index setoids.
𝒮 = setoid-cat.SetoidCat os (os ⊔ es)
Poly = polynomial-functor-2.Poly 𝒮
open polynomial-functor-2.Poly
open polynomial-functor-2 using (extend)

-- A sort is an index-erased μ-body together with a resolution of its free
-- variables to parameters or other sorts.
data Sort (n : ℕ) : Set (lsuc os ⊔ lsuc es) where
  mkSort : ∀ {k} → Poly (suc k) → (Fin k → Fin n ⊎ Sort n) → Sort n

-- The body environment of a μ-binder: slot 0 is the binder's own sort, the rest
-- are the ambient parameters.
η₀ : ∀ {n} → Poly (suc n) → Fin (suc n) → Fin n ⊎ Sort n
η₀ P = extend (λ i → inj₁ i) (inj₂ (mkSort P (λ i → inj₁ i)))

module Tree {n} (ι : Fin n → Setoid os (os ⊔ es)) where
  mutual
    data W {k} (Q : Poly (suc k)) (ρ : Fin k → Fin n ⊎ Sort n) : Set os where
      sup : ⟦ Q ⟧shape (extend ρ (inj₂ (mkSort Q ρ))) → W Q ρ

    ⟦_⟧shape : ∀ {k} → Poly k → (Fin k → Fin n ⊎ Sort n) → Set os
    ⟦ const S ⟧shape η = S .Carrier
    ⟦ var j   ⟧shape η = El (η j)
    ⟦ P + Q   ⟧shape η = ⟦ P ⟧shape η ⊎ ⟦ Q ⟧shape η
    ⟦ P × Q   ⟧shape η = ⟦ P ⟧shape η ×T ⟦ Q ⟧shape η
    ⟦ μ Q'    ⟧shape η = W Q' η

    El : Fin n ⊎ Sort n → Set os
    El (inj₁ p)            = ι p .Carrier
    El (inj₂ (mkSort Q ρ)) = W Q ρ

  mutual
    W-≈ : ∀ {k} {Q : Poly (suc k)} {ρ : Fin k → Fin n ⊎ Sort n} → W Q ρ → W Q ρ → Prop (os ⊔ es)
    W-≈ {Q = Q} {ρ = ρ} (sup x) (sup y) = shape≈ Q (extend ρ (inj₂ (mkSort Q ρ))) x y

    shape≈ : ∀ {j} (Q : Poly j) (η : Fin j → Fin n ⊎ Sort n) →
             ⟦ Q ⟧shape η → ⟦ Q ⟧shape η → Prop (os ⊔ es)
    shape≈ (const S) η x y = _≈s_ S x y
    shape≈ (var j)   η x y = elEq (η j) x y
    shape≈ (P + Q) η (inj₁ x) (inj₁ y) = shape≈ P η x y
    shape≈ (P + Q) η (inj₁ _) (inj₂ _) = ⊥
    shape≈ (P + Q) η (inj₂ _) (inj₁ _) = ⊥
    shape≈ (P + Q) η (inj₂ x) (inj₂ y) = shape≈ Q η x y
    shape≈ (P × Q) η (x₁ , x₂) (y₁ , y₂) = shape≈ P η x₁ y₁ ∧ shape≈ Q η x₂ y₂
    shape≈ (μ Q') η x y = W-≈ x y

    elEq : (r : Fin n ⊎ Sort n) → El r → El r → Prop (os ⊔ es)
    elEq (inj₁ p)            x y = _≈s_ (ι p) x y
    elEq (inj₂ (mkSort Q ρ)) x y = W-≈ x y

  mutual
    W-≈-refl : ∀ {k} {Q : Poly (suc k)} {ρ} (x : W Q ρ) → W-≈ x x
    W-≈-refl {Q = Q} {ρ = ρ} (sup x) = shape≈-refl Q (extend ρ (inj₂ (mkSort Q ρ))) x

    shape≈-refl : ∀ {j} (Q : Poly j) (η : Fin j → Fin n ⊎ Sort n) (x : ⟦ Q ⟧shape η) → shape≈ Q η x x
    shape≈-refl (const S) η x = S .isEquivalence .refl
    shape≈-refl (var j)   η x = elEq-refl (η j) x
    shape≈-refl (P + Q) η (inj₁ x) = shape≈-refl P η x
    shape≈-refl (P + Q) η (inj₂ y) = shape≈-refl Q η y
    shape≈-refl (P × Q) η (x₁ , x₂) = shape≈-refl P η x₁ , shape≈-refl Q η x₂
    shape≈-refl (μ Q') η x = W-≈-refl x

    elEq-refl : (r : Fin n ⊎ Sort n) (x : El r) → elEq r x x
    elEq-refl (inj₁ p)            x = ι p .isEquivalence .refl
    elEq-refl (inj₂ (mkSort Q ρ)) x = W-≈-refl x

  mutual
    W-≈-sym : ∀ {k} {Q : Poly (suc k)} {ρ} {x y : W Q ρ} → W-≈ x y → W-≈ y x
    W-≈-sym {Q = Q} {ρ = ρ} {sup x} {sup y} p = shape≈-sym Q (extend ρ (inj₂ (mkSort Q ρ))) p

    shape≈-sym : ∀ {j} (Q : Poly j) (η : Fin j → Fin n ⊎ Sort n) {x y : ⟦ Q ⟧shape η} →
                 shape≈ Q η x y → shape≈ Q η y x
    shape≈-sym (const S) η p = S .isEquivalence .sym p
    shape≈-sym (var j)   η p = elEq-sym (η j) p
    shape≈-sym (P + Q) η {inj₁ _} {inj₁ _} p = shape≈-sym P η p
    shape≈-sym (P + Q) η {inj₂ _} {inj₂ _} p = shape≈-sym Q η p
    shape≈-sym (P × Q) η {_ , _} {_ , _} (p₁ , p₂) = shape≈-sym P η p₁ , shape≈-sym Q η p₂
    shape≈-sym (μ Q') η {x} {y} p = W-≈-sym {x = x} {y = y} p

    elEq-sym : (r : Fin n ⊎ Sort n) {x y : El r} → elEq r x y → elEq r y x
    elEq-sym (inj₁ p)            e = ι p .isEquivalence .sym e
    elEq-sym (inj₂ (mkSort Q ρ)) {x} {y} e = W-≈-sym {x = x} {y = y} e

  mutual
    W-≈-trans : ∀ {k} {Q : Poly (suc k)} {ρ} {x y z : W Q ρ} → W-≈ x y → W-≈ y z → W-≈ x z
    W-≈-trans {Q = Q} {ρ = ρ} {sup x} {sup y} {sup z} p q = shape≈-trans Q (extend ρ (inj₂ (mkSort Q ρ))) p q

    shape≈-trans : ∀ {j} (Q : Poly j) (η : Fin j → Fin n ⊎ Sort n) {x y z : ⟦ Q ⟧shape η} →
                   shape≈ Q η x y → shape≈ Q η y z → shape≈ Q η x z
    shape≈-trans (const S) η p q = S .isEquivalence .trans p q
    shape≈-trans (var j)   η p q = elEq-trans (η j) p q
    shape≈-trans (P + Q) η {inj₁ _} {inj₁ _} {inj₁ _} p q = shape≈-trans P η p q
    shape≈-trans (P + Q) η {inj₂ _} {inj₂ _} {inj₂ _} p q = shape≈-trans Q η p q
    shape≈-trans (P × Q) η {_ , _} {_ , _} {_ , _} (p₁ , p₂) (q₁ , q₂) =
      shape≈-trans P η p₁ q₁ , shape≈-trans Q η p₂ q₂
    shape≈-trans (μ Q') η {x} {y} {z} p q = W-≈-trans {x = x} {y = y} {z = z} p q

    elEq-trans : (r : Fin n ⊎ Sort n) {x y z : El r} → elEq r x y → elEq r y z → elEq r x z
    elEq-trans (inj₁ p)            e f = ι p .isEquivalence .trans e f
    elEq-trans (inj₂ (mkSort Q ρ)) {x} {y} {z} e f = W-≈-trans {x = x} {y = y} {z = z} e f

  -- The carrier setoid of the μ-type at sort (Q , ρ).
  WSetoid : ∀ {k} (Q : Poly (suc k)) (ρ : Fin k → Fin n ⊎ Sort n) → Setoid os (os ⊔ es)
  WSetoid Q ρ .Carrier = W Q ρ
  WSetoid Q ρ ._≈s_ = W-≈
  WSetoid Q ρ .isEquivalence .refl {x} = W-≈-refl x
  WSetoid Q ρ .isEquivalence .sym {x} {y} = W-≈-sym {x = x} {y = y}
  WSetoid Q ρ .isEquivalence .trans {x} {y} {z} = W-≈-trans {x = x} {y = y} {z = z}
