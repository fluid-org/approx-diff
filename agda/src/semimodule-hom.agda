{-# OPTIONS --postfix-projections --prop --safe #-}

-- Matrices presented as morphisms between free semimodules, with entry access and
-- transpose recovered through the embedding. Wiring composes as functions; sums
-- appear only where the semantics sums.
open import Level using (0ℓ)
open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import Data.Fin using (Fin)
open import prop-setoid using (Setoid)
open import prop using (∃ₛ)
open import commutative-semiring using (CommutativeSemiring)
open import categories using (Category)
open import cmon-enriched using (CMonEnriched; Biproduct)
import matrix
import semimodule
import matrix-embedding

module semimodule-hom {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A) where

open Setoid A using (Carrier)
module M = matrix.Mat S
module SM = semimodule S
open SM using (Semimodule)
open matrix-embedding S using (𝔽; mat; app-e; 𝔽-biproduct; 𝔽F-full; 𝔽F-faithful; mat-cong; mat-comp; mat-I; mat-ε; mat-+)

private
  module C = Category SM.cat
  module CM = CMonEnriched SM.cmon-enriched

Hom : ℕ → ℕ → Set
Hom m n = SM._⇒_ (𝔽 n) (𝔽 m)

infix 4 _≈ₕ_
_≈ₕ_ : ∀ {m n} → Hom m n → Hom m n → Prop 0ℓ
_≈ₕ_ = SM._≈m_

I : ∀ {n} → Hom n n
I {n} = SM.id (𝔽 n)

εₕ : ∀ {m n} → Hom m n
εₕ {m} {n} = CM.εm {𝔽 n} {𝔽 m}

infixl 21 _∘_
_∘_ : ∀ {m n k} → Hom m n → Hom n k → Hom m k
f ∘ g = SM._∘_ f g

infixl 21 _+ₕ_
_+ₕ_ : ∀ {m n} → Hom m n → Hom m n → Hom m n
f +ₕ g = CM._+m_ f g

-- Entry access and the round trip with matrices.
entry : ∀ {m n} → Hom m n → Fin m → Fin n → Carrier
entry f i j = f .SM._⇒_.func (M.e j) i

to-matrix : ∀ {m n} → Hom m n → M.Matrix m n
to-matrix = entry

of-matrix : ∀ {m n} → M.Matrix m n → Hom m n
of-matrix = mat

to-of : ∀ {m n} (R : M.Matrix m n) → M._≈ₘ_ (to-matrix (of-matrix R)) R
to-of R i j = app-e R j i

of-to : ∀ {m n} (f : Hom m n) → of-matrix (to-matrix f) ≈ₕ f
of-to f = 𝔽F-full f .∃ₛ.snd

infixl 22 _ᵀ
_ᵀ : ∀ {m n} → Hom m n → Hom n m
f ᵀ = of-matrix (M._ᵀ (to-matrix f))

-- Biproduct wiring on dimensions.
p₁ : ∀ {m n} → Hom m (m +ℕ n)
p₁ {m} {n} = 𝔽-biproduct m n .Biproduct.p₁

p₂ : ∀ {m n} → Hom n (m +ℕ n)
p₂ {m} {n} = 𝔽-biproduct m n .Biproduct.p₂

in₁ : ∀ {m n} → Hom (m +ℕ n) m
in₁ {m} {n} = 𝔽-biproduct m n .Biproduct.in₁

in₂ : ∀ {m n} → Hom (m +ℕ n) n
in₂ {m} {n} = 𝔽-biproduct m n .Biproduct.in₂

⟨_,_⟩ : ∀ {m x y} → Hom x m → Hom y m → Hom (x +ℕ y) m
⟨ f , g ⟩ = (in₁ ∘ f) +ₕ (in₂ ∘ g)

infixl 20 _∥_
_∥_ : ∀ {k m n} → Hom k m → Hom k n → Hom k (m +ℕ n)
f ∥ g = (f ∘ p₁) +ₕ (g ∘ p₂)

infixl 20 _⊕_
_⊕_ : ∀ {m n x y} → Hom m x → Hom n y → Hom (m +ℕ n) (x +ℕ y)
f ⊕ g = (in₁ ∘ (f ∘ p₁)) +ₕ (in₂ ∘ (g ∘ p₂))
