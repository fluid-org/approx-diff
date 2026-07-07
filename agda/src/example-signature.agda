{-# OPTIONS --postfix-projections --prop --safe #-}

-- Parameterised by the set of numeric literals, which the intended models take as the carrier of
-- the `number` sort.
module example-signature (Num : Set) where

open import Level using (0ℓ)
open import signature using (Signature)
open import Data.List using (List; []; _∷_)
import label

data sort : Set where
  number label approx : sort

data op : List sort → sort → Set where
  lit  : Num → op [] number
  add  : op (number ∷ number ∷ []) number
  mult : op (number ∷ number ∷ []) number
  lbl  : label.label → op [] label
  approx-unit : op [] approx
  approx-mult : op (approx ∷ approx ∷ []) approx

data rel : List sort → Set where
  equal-label : rel (label ∷ label ∷ [])

Sig : Signature 0ℓ
Sig .Signature.sort = sort
Sig .Signature.op = op
Sig .Signature.rel = rel
