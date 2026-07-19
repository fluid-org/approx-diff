{-# OPTIONS --postfix-projections --prop --safe #-}

open import Level using (0ℓ)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
import label
import prop-setoid

-- Value-level interpretation of the example signature.
module example.algebra
  (Num : Set) (add-fun mult-fun : Num → Num → Num)
  (Approx : Set) (approx-unit-val : Approx) (approx-mult-val : Approx → Approx → Approx)
  where

open import signature using (Signature)
open import language-operational.algebra using (Algebra; sort-vals)
open import example.signature Num

sort-val : sort → Set
sort-val number = Num
sort-val label  = label.label
sort-val approx = Approx

op-fun : ∀ {is o} → op is o → sort-vals sort-val is → sort-val o
op-fun (lit n)     _           = n
op-fun add         (n , m , _) = add-fun n m
op-fun mult        (n , m , _) = mult-fun n m
op-fun (lbl l)     _           = l
op-fun approx-unit _           = approx-unit-val
op-fun approx-mult (a , b , _) = approx-mult-val a b

rel-pred : ∀ {is} → rel is → sort-vals sort-val is → ⊤ {0ℓ} ⊎ ⊤ {0ℓ}
rel-pred equal-label (l₁ , l₂ , _) = label.equal-label .prop-setoid._⇒_.func (l₁ , l₂)

Alg : Algebra Sig 0ℓ
Alg .Algebra.sort-val = sort-val
Alg .Algebra.op-fun   = op-fun
Alg .Algebra.rel-pred = rel-pred
