{-# OPTIONS --postfix-projections --prop --safe #-}

-- Parameterised by the set of numeric literals, which the intended models take as the carrier of
-- the `number` sort.
module signature.example (Num : Set) where

open import Level using (0ℓ)
open import signature using (Signature)
open import Data.List using (List; []; _∷_)
open import Data.String using (String)

data sort : Set where
  number string : sort

data op : List sort → sort → Set where
  lit  : Num → op [] number
  add  : op (number ∷ number ∷ []) number
  mult : op (number ∷ number ∷ []) number
  str  : String → op [] string

data rel : List sort → Set where
  equal-string : rel (string ∷ string ∷ [])
  equal-number : rel (number ∷ number ∷ [])
  less-number : rel (number ∷ number ∷ [])

Sig : Signature 0ℓ
Sig .Signature.sort = sort
Sig .Signature.op = op
Sig .Signature.rel = rel
