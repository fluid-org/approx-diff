{-# OPTIONS --prop --postfix-projections --safe #-}

-- List values at the list encoding of the syntax: a cons is an injection over a pair of head and
-- tail, under a roll. Shared by the example dumps so a list value is built one way.
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (subst; sym)
import two
open import signature using (Signature)
open import primitives using (Primitives)

module example.list-value {ℓ} (Sig : Signature ℓ)
  (𝒫 : Primitives two.semiring Sig) where

open import language-syntax Sig using (type; list; sub-ren-id)
open import language-operational.evaluation Sig two.semiring 𝒫 two.I using (Val)
open Val

infixr 20 _∷ᵥ_

nilᵥ : ∀ {τ : type 0} → Val (list τ)
nilᵥ = roll (inl unit)

_∷ᵥ_ : ∀ {τ : type 0} → Val τ → Val (list τ) → Val (list τ)
_∷ᵥ_ {τ} x xs = roll (inr (pair (subst Val (sym (sub-ren-id τ (λ ()))) x) xs))

fromList : ∀ {τ : type 0} → List (Val τ) → Val (list τ)
fromList []       = nilᵥ
fromList (x ∷ xs) = x ∷ᵥ fromList xs
