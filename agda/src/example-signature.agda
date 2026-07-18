{-# OPTIONS --postfix-projections --prop --safe #-}

module example-signature where

open import Level using (0ℓ)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.String using (String; _++_)
import signature
open signature using (Signature; Algebra)

import label
import prop-setoid

data sort : Set where
  number label : sort

sort-val : sort → Set
sort-val number = ℕ
sort-val label  = label.label

data op : List sort → sort → Set where
  zero : op [] number
  add  : op (number ∷ number ∷ []) number
  mult : op (number ∷ number ∷ []) number
  lbl  : label.label → op [] label

data rel : List sort → Set where
  equal-label : rel (label ∷ label ∷ [])

show-label : label.label → String
show-label label.a = "a"
show-label label.b = "b"
show-label label.c = "c"
show-label label.d = "d"

op-fun : ∀ {is o} → op is o → signature.sort-vals sort-val is → sort-val o
op-fun zero    _              = 0
op-fun add     (n , m , _)    = n + m
op-fun mult    (n , m , _)    = n * m
op-fun (lbl l) _              = l

rel-pred : ∀ {is} → rel is → signature.sort-vals sort-val is → ⊤ {0ℓ} ⊎ ⊤ {0ℓ}
rel-pred equal-label (l₁ , l₂ , _) = label.equal-label .prop-setoid._⇒_.func (l₁ , l₂)

show-op : ∀ {is o} → op is o → String
show-op zero    = "zero"
show-op add     = "add"
show-op mult    = "mult"
show-op (lbl x) = "lbl-" ++ show-label x

Sig : Signature 0ℓ
Sig .Signature.sort    = sort
Sig .Signature.op      = op
Sig .Signature.rel     = rel
Sig .Signature.show-op = show-op

Alg : Algebra Sig 0ℓ
Alg .Algebra.sort-val = sort-val
Alg .Algebra.op-fun   = op-fun
Alg .Algebra.rel-pred = rel-pred
