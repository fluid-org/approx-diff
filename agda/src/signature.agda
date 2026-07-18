{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (suc; _⊔_)
open import Data.List using (List; []; _∷_; _++_)
import Data.Product as Product
import Data.Sum as Sum
open import Data.String using (String)
open import Data.Unit.Polymorphic using (⊤)
open import categories using (Category; HasTerminal; HasProducts)

module signature where

record Signature ℓ : Set (suc ℓ) where
  field
    sort    : Set ℓ
    op      : List sort → sort → Set ℓ
    rel     : List sort → Set ℓ
    show-op : ∀ {is o} → op is o → String

-- Per-sort value tuple for a list of sorts, given a value type per sort.
sort-vals : ∀ {ℓ ℓ'} {sort : Set ℓ} (sort-val : sort → Set ℓ') → List sort → Set ℓ'
sort-vals sv []       = ⊤
sort-vals sv (σ ∷ σs) = sv σ Product.× sort-vals sv σs

-- Set-theoretic interpretation of a signature: per-sort value types and per-op/rel functions.
record Algebra {ℓ} (Sig : Signature ℓ) ℓ' : Set (ℓ ⊔ suc ℓ') where
  open Signature Sig
  field
    sort-val : sort → Set ℓ'
    op-fun   : ∀ {is o} → op is o → sort-vals sort-val is → sort-val o
    rel-pred : ∀ {is}   → rel is  → sort-vals sort-val is → ⊤ {ℓ'} Sum.⊎ ⊤ {ℓ'}


-- Finite-product categories.
record FPCat o m e : Set (suc (o ⊔ m ⊔ e)) where
  constructor FPC[_,_,_]
  field
    cat      : Category o m e
    terminal : HasTerminal cat
    products : HasProducts cat

  open Category cat public
  open HasTerminal terminal renaming (witness to 𝟙) public
  open HasProducts products renaming (pair to ⟨_,_⟩; prod to _×_) public

  list→product : ∀ {ℓ} {A : Set ℓ} → (A → obj) → List A → obj
  list→product i []       = 𝟙
  list→product i (x ∷ xs) = i x × list→product i xs

-- Models of signatures live in finite product (FIXME: monoidal?)
-- categories with a specified object of truth values.
record PointedFPCat o m e : Set (suc (o ⊔ m ⊔ e)) where
  constructor PFPC[_,_]
  field
    fpcat : FPCat o m e
    Ω     : FPCat.obj fpcat

  open FPCat fpcat public

record Model {ℓ o m e} (𝒞 : PointedFPCat o m e) (Sig : Signature ℓ) : Set (ℓ ⊔ o ⊔ m) where
  open PointedFPCat 𝒞
  open Signature Sig
  field
    ⟦sort⟧     : sort → obj
    ⟦op⟧       : ∀ {i o} → op i o → list→product ⟦sort⟧ i ⇒ ⟦sort⟧ o
    ⟦rel⟧      : ∀ {i} → rel i → list→product ⟦sort⟧ i ⇒ Ω
