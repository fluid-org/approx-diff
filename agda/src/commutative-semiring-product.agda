{-# OPTIONS --prop --postfix-projections --safe #-}

module commutative-semiring-product where

open import Level using (_⊔_)
open import Data.Product using (_,_; proj₁; proj₂)
open import prop using (_,_)
open import prop-setoid using (Setoid; ⊗-setoid)
open import commutative-monoid using (CommutativeMonoid)
open import commutative-semiring using (CommutativeSemiring)

open CommutativeMonoid
open CommutativeSemiring

private
  -- The pair is built from projections, so a component of a sum is computed only as far as that
  -- factor's sum needs.
  _⊗M_ : ∀ {o e} {A B : Setoid o e} → CommutativeMonoid A → CommutativeMonoid B →
         CommutativeMonoid (⊗-setoid A B)
  (X ⊗M Y) .ε = X .ε , Y .ε
  (X ⊗M Y) ._+_ p q = X ._+_ (proj₁ p) (proj₁ q) , Y ._+_ (proj₂ p) (proj₂ q)
  (X ⊗M Y) .+-cong (e₁ , e₂) (e₁' , e₂') = X .+-cong e₁ e₁' , Y .+-cong e₂ e₂'
  (X ⊗M Y) .+-lunit = X .+-lunit , Y .+-lunit
  (X ⊗M Y) .+-assoc = X .+-assoc , Y .+-assoc
  (X ⊗M Y) .+-comm = X .+-comm , Y .+-comm

_⊗S_ : ∀ {o e} {A B : Setoid o e} → CommutativeSemiring A → CommutativeSemiring B →
       CommutativeSemiring (⊗-setoid A B)
(S ⊗S T) .additive = S .additive ⊗M T .additive
(S ⊗S T) .multiplicative = S .multiplicative ⊗M T .multiplicative
(S ⊗S T) .·-+-distribₗ = S .·-+-distribₗ , T .·-+-distribₗ
(S ⊗S T) .ε-annihilₗ = S .ε-annihilₗ , T .ε-annihilₗ
