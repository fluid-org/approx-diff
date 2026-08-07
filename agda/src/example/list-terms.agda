{-# OPTIONS --prop --postfix-projections --safe #-}

-- The terms the dependency readbacks run at, and the first-order witnesses of their contexts.
-- Syntax only, so that the models these are read back in are compared on the same programs.
module example.list-terms where

import Data.Fin as Fin
open import Data.Rational using (ℚ; 0ℚ; 1ℚ)
open import every using ([]; _∷_)
open import example.signature ℚ using (Sig; number; label; lit; add; equal-number)
open import language-syntax Sig
  using (base; list; unit; _[+]_; _[×]_; var; μ; _⊢_; bop; fold; case; snd; pair;
         from_collect_; return; zero; succ; when_；_; brel; if_then_else_;
         first-order; first-order-ctxt; emp; _,_)

query-ctxt-fo : first-order-ctxt (emp , list (base label [×] base number))
query-ctxt-fo = emp , μ (unit [+] ((base label [×] base number) [×] var Fin.zero))

-- A term that ignores its input: every column must be zero.
const-term : (emp , list (base label [×] base number)) ⊢ base number
const-term = bop (lit 0ℚ) []

-- Length: fold ignoring the element, so only the cons cells should register.
length-term : (emp , list (base label [×] base number)) ⊢ base number
length-term =
  fold (case (var zero)
          (bop (lit 0ℚ) [])
          (bop add ((bop (lit 1ℚ) []) ∷ ((snd (var zero)) ∷ []))))
       (var zero)

-- A fold whose body reads nothing: separates the fold itself from what its body consults.
fold0-term : (emp , list (base label [×] base number)) ⊢ base number
fold0-term = fold (bop (lit 0ℚ) []) (var zero)

-- Matches the unfolding but returns a constant either way: separates matching from reading.
case0-term : (emp , list (base label [×] base number)) ⊢ base number
case0-term = fold (case (var zero) (bop (lit 0ℚ) []) (bop (lit 0ℚ) [])) (var zero)

-- Zero for nil, one for cons: should register the outermost tag and nothing else.
tag-term : (emp , list (base label [×] base number)) ⊢ base number
tag-term = fold (case (var zero) (bop (lit 0ℚ) []) (bop (lit 1ℚ) [])) (var zero)

numlist-fo : first-order (list (base number))
numlist-fo = μ (unit [+] (base number [×] var Fin.zero))

map-ctxt-fo : first-order-ctxt (emp , list (base number))
map-ctxt-fo = emp , numlist-fo

-- Expected: each output cell records the input spine above it and its own scalar, nothing later.
map-term : (emp , list (base number)) ⊢ list (base number)
map-term =
  from var zero collect
    return (bop add ((bop (lit 1ℚ) []) ∷ ((var zero) ∷ [])))

-- Membership by numeric equality: the target is compared with each element, so it gates every step
-- without its value reaching the output.
filter-ctxt-fo : first-order-ctxt (emp , base number , list (base number))
filter-ctxt-fo = (emp , first-order.base number) , numlist-fo

filter-term : (emp , base number , list (base number)) ⊢ list (base number)
filter-term =
  from var zero collect
    (when brel equal-number ((var zero) ∷ ((var (succ (succ zero))) ∷ []))
     ； return (var zero))

-- Data and control interacting through a numeric test: the tested number reaches the output only
-- through the equality, the other reaches it as value flow.
cond-ctxt-fo : first-order-ctxt (emp , base number , base number)
cond-ctxt-fo = emp , base number , base number

cond-term : (emp , base number , base number) ⊢ base number
cond-term =
  if brel equal-number ((var (succ zero)) ∷ ((bop (lit 0ℚ) []) ∷ []))
  then bop add ((var zero) ∷ ((bop (lit 1ℚ) []) ∷ []))
  else var zero

-- The test's own outcome: the compared numbers reach the boolean directly, and only a consumer of
-- that boolean turns the dependence into control.
eq-ctxt-fo : first-order-ctxt (emp , base number)
eq-ctxt-fo = emp , first-order.base number

eq-term : (emp , base number) ⊢ (unit [+] unit)
eq-term = brel equal-number ((var zero) ∷ ((bop (lit 0ℚ) []) ∷ []))
