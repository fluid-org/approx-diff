{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (suc; _⊔_)
open import Data.List using (List; []; _∷_)
import Data.Product as Product
import Data.Sum as Sum
open import Data.Unit.Polymorphic using (⊤)
open import signature using (Signature)

-- Value-level interpretation of a signature: per-sort value types and per-op/rel
-- functions. Used by the operational semantics, independently of any categorical model.
module signature-algebra where

-- Per-sort value tuple for a list of sorts, given a value type per sort.
sort-vals : ∀ {ℓ ℓ'} {sort : Set ℓ} (sort-val : sort → Set ℓ') → List sort → Set ℓ'
sort-vals sv []       = ⊤
sort-vals sv (σ ∷ σs) = sv σ Product.× sort-vals sv σs

record Algebra {ℓ} (Sig : Signature ℓ) ℓ' : Set (ℓ ⊔ suc ℓ') where
  open Signature Sig
  field
    sort-val : sort → Set ℓ'
    op-fun   : ∀ {is o} → op is o → sort-vals sort-val is → sort-val o
    rel-pred : ∀ {is}   → rel is  → sort-vals sort-val is → ⊤ {ℓ'} Sum.⊎ ⊤ {ℓ'}
