{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (0ℓ; suc; _⊔_)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; _+_)
import Data.Product as Product
open import Data.Unit.Polymorphic using (⊤)
open import categories using (Category)
open import commutative-semiring using (CommutativeSemiring)
import prop
open import prop-setoid using (Setoid; ⊗-setoid; +-setoid; 𝟙; ⊤-isEquivalence)
open import signature using (Signature)
import matrix

-- The primitives of a signature, as assumed by the operational semantics: for each sort a setoid
-- of constants and a width, and for each operation a function on constants together with a dependency
-- relation at each tuple of constants.
module primitives where

-- The setoid of tuples of constants.
sort-vals-setoid : ∀ {ℓ} {sort : Set ℓ} (sort-index : sort → Setoid 0ℓ 0ℓ) → List sort → Setoid 0ℓ 0ℓ
sort-vals-setoid si [] .Setoid.Carrier = ⊤
sort-vals-setoid si [] .Setoid._≈_ _ _ = prop.⊤
sort-vals-setoid si [] .Setoid.isEquivalence = ⊤-isEquivalence
sort-vals-setoid si (σ ∷ σs) = ⊗-setoid (si σ) (sort-vals-setoid si σs)

sorts-width : ∀ {ℓ} {A : Set ℓ} → (A → ℕ) → List A → ℕ
sorts-width w []       = 0
sorts-width w (s ∷ ss) = w s + sorts-width w ss

record Primitives {ℓ} {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A) (Sig : Signature ℓ)
                  : Set (ℓ ⊔ suc 0ℓ) where
  open Signature Sig
  field
    sort-index : sort → Setoid 0ℓ 0ℓ
    sort-width : sort → ℕ

  sort-val : sort → Set
  sort-val s = Setoid.Carrier (sort-index s)

  sort-vals : List sort → Set
  sort-vals is = Setoid.Carrier (sort-vals-setoid sort-index is)

  bases-width : List sort → ℕ
  bases-width = sorts-width sort-width

  field
    op-fun   : ∀ {is o} → op is o →
               prop-setoid._⇒_ (sort-vals-setoid sort-index is) (sort-index o)
    op-deps   : ∀ {is o'} → op is o' →
               prop-setoid._⇒_ (sort-vals-setoid sort-index is)
                 (Category.hom-setoid (matrix.Mat.cat S) (bases-width is) (sort-width o'))
    rel-pred : ∀ {is} → rel is →
               prop-setoid._⇒_ (sort-vals-setoid sort-index is) (+-setoid (𝟙 {0ℓ} {0ℓ}) 𝟙)
