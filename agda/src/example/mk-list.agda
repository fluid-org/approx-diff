{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (0ℓ)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import signature using (Signature)
open import primitives using (Primitives)

module example.mk-list {ℓ} (Sig : Signature ℓ) {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (𝒫 : Primitives S Sig) (elim-weight : Setoid.Carrier A) where

open import language-syntax Sig using (type; list; sub-ren-id)
open import language-operational.evaluation Sig S 𝒫 elim-weight using (Val)
open Val

infixr 20 _∷ᵥ_

nilᵥ : ∀ {τ : type 0} → Val (list τ)
nilᵥ = roll (inl unit)

_∷ᵥ_ : ∀ {τ : type 0} → Val τ → Val (list τ) → Val (list τ)
_∷ᵥ_ {τ} x xs = roll (inr (pair (subst Val (sym (sub-ren-id τ (λ ()))) x) xs))

fromList : ∀ {τ : type 0} → List (Val τ) → Val (list τ)
fromList []       = nilᵥ
fromList (x ∷ xs) = x ∷ᵥ fromList xs
