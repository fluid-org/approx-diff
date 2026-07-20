{-# OPTIONS --prop --postfix-projections --safe #-}

module example (Num : Set) (num-zero : Num) where

open import Level using (0ℓ; lift)
import Data.Fin as Fin
open import Data.List using (List; []; _∷_)
open import every using (Every; []; _∷_)
open import Relation.Binary.PropositionalEquality using (refl)
open import signature
import language-syntax
import label

open import example.signature Num

module L = language-syntax Sig

-- example query. Given `List (label [×] nat)`, add up all the
-- elements labelled with a specific label:
--
--   sum [ snd e | e <- xs, equal-label 'a' (fst e) ]
--
--   sum (concatMap x (e. if equal-label 'a' (fst e) then return (snd e) else nil))
--
--   sum = foldr (lit num-zero) (add (var zero) (var (succ zero)))

module ex where
  open L

  `_ : ∀ {Γ} → label.label → Γ ⊢ base label
  ` l = bop (lbl l) []

  _≟_ : ∀ {Γ} → Γ ⊢ base label → Γ ⊢ base label → Γ ⊢ bool
  M ≟ N = brel equal-label (M ∷ N ∷ [])

  sum : ∀ {Γ} → Γ ⊢ list (base number) [→] base number
  sum = lam (foldr (bop (lit num-zero) []) (bop add (var zero ∷ var (succ zero) ∷ [])) (var zero))

  some-eq : ∀ {Γ} → Γ ⊢ base label [→] list (base label) [→] bool
  some-eq = lam (lam
    (foldr false
      (if (brel equal-label (var (succ zero) ∷ var (succ (succ (succ zero))) ∷ []))
       then true else (var zero))
      (var zero)))

  query : label.label → emp , list (base label [×] base number) ⊢ base number
  query l =
    app sum
      (from var zero collect
      when fst (var zero) ≟ (` l) ；
      return (snd (var zero)))

  -- Price-weighted sum of the quantities with a given label; the per-label prices are a further
  -- pair of inputs.
  total : label.label →
          emp , (list (base label [×] base number)) [×] (base number [×] base number) ⊢ base number
  total l = app sum
                (from fst (var zero) collect
                 when fst (var zero) ≟ (` l) ；
                 return (bop mult (price l ∷ snd (var zero) ∷ [])))
    where
      price : label.label →
              (emp , (list (base label [×] base number)) [×] (base number [×] base number))
                , (base label [×] base number) ⊢ base number
      price label.a = fst (snd (var (succ zero)))
      price _       = snd (snd (var (succ zero)))

  -- Moving average with window two over four inputs; adjacent outputs share an input, and
  -- non-adjacent outputs share none. h is the constant 1/2, supplied as a literal.
  mavg : Num → emp , ((base number [×] base number) [×] base number) [×] base number
             ⊢ (base number [×] base number) [×] base number
  mavg h = pair (pair (avg (fst (fst (fst (var zero)))) (snd (fst (fst (var zero)))))
                      (avg (snd (fst (fst (var zero)))) (snd (fst (var zero)))))
                (avg (snd (fst (var zero))) (snd (var zero)))
    where
      avg : ∀ {Γ} → Γ ⊢ base number → Γ ⊢ base number → Γ ⊢ base number
      avg x y = bop mult (bop (lit h) [] ∷ bop add (x ∷ y ∷ []) ∷ [])

  -- 3x3 grid scorer for the signed-saliency reading: a centre-surround linear filter (centre
  -- positive, corners negative) plus two adjacent-cell interaction products. Unlike the linear
  -- mavg, the products make the Jacobian, and hence the saliency, depend on the input. `neg` is
  -- the -1 weight literal; positive weights are implicit. The bottom-middle cell is absent from
  -- the score, so masked.
  Row Grid : type 0
  Row  = (base number [×] base number) [×] base number
  Grid = (Row [×] Row) [×] Row

  score : Num → emp , Grid ⊢ base number
  score neg =
    plus (plus x5 (minus (plus (plus x1 x3) (plus x7 x9))))
         (plus (times x4 x6) (minus (times x5 x2)))
    where
      plus times : ∀ {Γ} → Γ ⊢ base number → Γ ⊢ base number → Γ ⊢ base number
      plus  a b = bop add  (a ∷ b ∷ [])
      times a b = bop mult (a ∷ b ∷ [])
      minus : ∀ {Γ} → Γ ⊢ base number → Γ ⊢ base number
      minus a = bop mult (bop (lit neg) [] ∷ a ∷ [])
      g : emp , Grid ⊢ Grid
      g = var zero
      r1 r2 r3 : emp , Grid ⊢ Row
      r1 = fst (fst g)
      r2 = snd (fst g)
      r3 = snd g
      x1 x2 x3 x4 x5 x6 x7 x9 : emp , Grid ⊢ base number
      x1 = fst (fst r1)
      x2 = snd (fst r1)
      x3 = snd r1
      x4 = fst (fst r2)
      x5 = snd (fst r2)
      x6 = snd r2
      x7 = fst (fst r3)
      x9 = snd r3

  -- Product of two numbers.
  mult-ex : emp , base number [×] base number ⊢ base number
  mult-ex = bop mult (fst (var zero) ∷ snd (var zero) ∷ [])

  -- Sum of a list of numbers, multiplied by another number.
  sum-mul : emp , list (base number) [×] base number ⊢ base number
  sum-mul = bop mult (app sum (fst (var zero)) ∷ snd (var zero) ∷ [])

  -- Rose trees of numbers: a nested recursive type (the children list is itself
  -- a μ-type mentioning the outer recursion variable).
  rose : type 0
  rose = μ (base number [×] μ (unit [+] (var (Fin.suc Fin.zero) [×] var Fin.zero)))

  node : ∀ {Γ} → Γ ⊢ base number → Γ ⊢ list rose → Γ ⊢ rose
  node n ts = roll (pair n ts)

  -- Sum of all numbers in a rose tree: the fold's recursion crosses the inner
  -- list μ, so the children arrive as a list of subtree sums.
  rose-sum : ∀ {Γ} → Γ ⊢ rose [→] base number
  rose-sum = lam (fold (bop add (fst (var zero) ∷ app sum (snd (var zero)) ∷ [])) (var zero))

  rose-query : emp , rose ⊢ base number
  rose-query = app rose-sum (var zero)
