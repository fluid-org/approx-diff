{-# OPTIONS --prop --postfix-projections --safe #-}

-- Syntax only: every model and the operational semantics read the same terms.
module example.programs where

import Data.Fin as Fin
open import Data.Rational using (ℚ; 0ℚ; 1ℚ)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.String using (String)
open import signature.example ℚ
open import language-syntax Sig

`_ : ∀ {Γ} → String → Γ ⊢ base string
` s = bop (str s) []

_≟_ : ∀ {Γ} → Γ ⊢ base string → Γ ⊢ base string → Γ ⊢ bool
M ≟ N = brel equal-string (M ∷ N ∷ [])

sum : ∀ {Γ} → Γ ⊢ list (base number) [→] base number
sum = lam (foldr (bop (lit 0ℚ) []) (bop add (var zero ∷ var (succ zero) ∷ [])) (var zero))

------------------------------------------------------------------------------
-- Programs over a list of labelled numbers.

-- The running example: add up the numbers carrying a given label,
--   sum [ snd e | e <- xs, equal-label l (fst e) ].
query : String → emp , list (base string [×] base number) ⊢ base number
query l =
  app sum
    (from var zero collect
    when fst (var zero) ≟ (` l) ；
    return (snd (var zero)))

-- Ignores its input: every column must be zero.
const-term : (emp , list (base string [×] base number)) ⊢ base number
const-term = bop (lit 0ℚ) []

-- Length: a fold ignoring the element, so only the cons cells should register.
length-term : (emp , list (base string [×] base number)) ⊢ base number
length-term =
  fold (case (var zero)
          (bop (lit 0ℚ) [])
          (bop add ((bop (lit 1ℚ) []) ∷ ((snd (var zero)) ∷ []))))
       (var zero)

-- A fold whose body reads nothing: separates the fold itself from what its body consults.
fold0-term : (emp , list (base string [×] base number)) ⊢ base number
fold0-term = fold (bop (lit 0ℚ) []) (var zero)

-- Matches the unfolding but returns a constant either way: separates matching from reading.
case0-term : (emp , list (base string [×] base number)) ⊢ base number
case0-term = fold (case (var zero) (bop (lit 0ℚ) []) (bop (lit 0ℚ) [])) (var zero)

-- Zero for nil, one for cons: should register the outermost tag and nothing else.
tag-term : (emp , list (base string [×] base number)) ⊢ base number
tag-term = fold (case (var zero) (bop (lit 0ℚ) []) (bop (lit 1ℚ) [])) (var zero)

-- Price-weighted sum of the quantities with a given label; the per-label prices are a further
-- pair of inputs.
total : String →
        emp , (list (base string [×] base number)) [×] (base number [×] base number) ⊢ base number
total l = app sum
              (from fst (var zero) collect
               when fst (var zero) ≟ (` l) ；
               return (bop mult (price l ∷ snd (var zero) ∷ [])))
  where
    price : String →
            (emp , (list (base string [×] base number)) [×] (base number [×] base number))
              , (base string [×] base number) ⊢ base number
    price "a" = fst (snd (var (succ zero)))
    price _       = snd (snd (var (succ zero)))

------------------------------------------------------------------------------
-- Programs over a list of numbers.

-- Each output cell should record the input spine above it and its own scalar, nothing later.
map-term : (emp , list (base number)) ⊢ list (base number)
map-term =
  from var zero collect
    return (bop add ((bop (lit 1ℚ) []) ∷ ((var zero) ∷ [])))

-- Membership by numeric equality: the target is compared with each element, so it gates every step
-- without its value reaching the output.
filter-term : (emp , base number , list (base number)) ⊢ list (base number)
filter-term =
  from var zero collect
    (when brel equal-number ((var zero) ∷ ((var (succ (succ zero))) ∷ []))
     ； return (var zero))

-- Adjacent-pair sums; the fold pairs each suffix's head with its sums so far, so a step can reach the
-- next element.
adjacent-sums-term : (emp , list (base number)) ⊢ list (base number)
adjacent-sums-term = snd (foldr (pair (inl unit) nil) body (var zero))
  where
  body : (emp , list (base number)) , base number
         , ((unit [+] base number) [×] list (base number))
         ⊢ (unit [+] base number) [×] list (base number)
  body = pair (inr (var (succ zero)))
              (case (fst (var zero))
                    nil
                    (cons (bop add (var (succ (succ zero)) ∷ var zero ∷ []))
                          (snd (var (succ zero)))))

-- Merge two sorted lists.
merge-term : (emp , list (base number) [×] list (base number)) ⊢ list (base number)
merge-term =
  app (foldr (lam (var zero)) step (fst (var zero))) (snd (var zero))
  where
  step : ((emp , list (base number) [×] list (base number)) , base number)
         , (list (base number) [→] list (base number))
         ⊢ list (base number) [→] list (base number)
  step = lam (snd (foldr
    (pair nil (cons (var (succ (succ zero))) (app (var (succ zero)) nil)))
    (pair (cons (var (succ zero)) (fst (var zero)))
          (if brel less-number (var (succ zero) ∷ var (succ (succ (succ (succ zero)))) ∷ [])
           then cons (var (succ zero)) (snd (var zero))
           else cons (var (succ (succ (succ (succ zero)))))
                     (app (var (succ (succ (succ zero)))) (cons (var (succ zero)) (fst (var zero))))))
    (var zero)))

sum-mul : emp , list (base number) [×] base number ⊢ base number
sum-mul = bop mult (app sum (fst (var zero)) ∷ snd (var zero) ∷ [])

------------------------------------------------------------------------------
-- Programs over numbers and booleans.

-- Data and control interacting through a numeric test: the tested number reaches the output only
-- through the equality, the other reaches it as value flow.
cond-term : (emp , base number , base number) ⊢ base number
cond-term =
  if brel equal-number ((var (succ zero)) ∷ ((bop (lit 0ℚ) []) ∷ []))
  then bop add ((var zero) ∷ ((bop (lit 1ℚ) []) ∷ []))
  else var zero

-- The test's own outcome: the compared numbers reach the boolean directly, and only a consumer of
-- that boolean turns the dependence into control.
eq-term : (emp , base number) ⊢ (unit [+] unit)
eq-term = brel equal-number ((var zero) ∷ ((bop (lit 0ℚ) []) ∷ []))

-- Control dependence through a test: matching on a numeric equality must depend on the scalar the
-- test read, through the root of the test's boolean.
test-term : (emp , base number) ⊢ base number
test-term =
  case (brel equal-number (var zero ∷ (bop (lit 0ℚ) [] ∷ [])))
       (bop (lit 1ℚ) []) (bop (lit 0ℚ) [])

-- A case on a boolean input: one branch reads the number, the other a constant.
case-ctxt : ctxt
case-ctxt = (emp , base number) , (unit [+] unit)

case-term : case-ctxt ⊢ base number
case-term = case (var zero) (var (succ (succ zero))) (bop (lit 0ℚ) [])

mult-ex : emp , base number [×] base number ⊢ base number
mult-ex = bop mult (fst (var zero) ∷ snd (var zero) ∷ [])

-- y · (x + y): the sum an intermediate with a route past it through y.
add-mul : emp , base number , base number ⊢ base number
add-mul = bop mult (bop add (var zero ∷ var (succ zero) ∷ []) ∷ var zero ∷ [])

-- Moving average with window two over four inputs; adjacent outputs share an input, and
-- non-adjacent outputs share none. h is the constant 1/2, supplied as a literal.
mavg-body : ∀ {Γ} → ℚ → Γ ⊢ base number [×] (base number [×] (base number [×] base number))
          → Γ ⊢ base number [×] (base number [×] base number)
mavg-body h v = pair (avg x₁ x₂) (pair (avg x₂ x₃) (avg x₃ x₄))
  where
    avg : ∀ {Γ} → Γ ⊢ base number → Γ ⊢ base number → Γ ⊢ base number
    avg x y = bop mult (bop (lit h) [] ∷ bop add (x ∷ y ∷ []) ∷ [])
    x₁ = fst v
    x₂ = fst (snd v)
    x₃ = fst (snd (snd v))
    x₄ = snd (snd (snd v))

mavg : ℚ → emp , base number [×] (base number [×] (base number [×] base number))
           ⊢ base number [×] (base number [×] base number)
mavg h = mavg-body h (var zero)

-- 3x3 grid scorer for the signed-saliency reading: a centre-surround linear filter (centre
-- positive, corners negative) plus two adjacent-cell interaction products. Unlike the linear
-- mavg, the products make the Jacobian, and hence the saliency, depend on the input. `neg` is
-- the -1 weight literal; positive weights are implicit. The bottom-middle cell is absent from
-- the score, so masked.
Row Grid : type 0
Row  = base number [×] (base number [×] base number)
Grid = Row [×] (Row [×] Row)

score : ℚ → emp , Grid ⊢ base number
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
    r1 = fst g
    r2 = fst (snd g)
    r3 = snd (snd g)
    x1 x2 x3 x4 x5 x6 x7 x9 : emp , Grid ⊢ base number
    x1 = fst r1
    x2 = fst (snd r1)
    x3 = snd (snd r1)
    x4 = fst r2
    x5 = fst (snd r2)
    x6 = snd (snd r2)
    x7 = fst r3
    x9 = snd (snd r3)

------------------------------------------------------------------------------
-- Rose trees of numbers: a nested recursive type, the children list itself a μ-type mentioning
-- the outer recursion variable.

rose : type 0
rose = μ (base number [×] μ (unit [+] (var (Fin.suc Fin.zero) [×] var Fin.zero)))

node : ∀ {Γ} → Γ ⊢ base number → Γ ⊢ list rose → Γ ⊢ rose
node n ts = roll (pair n ts)

-- Sum of all numbers in a rose tree: the fold's recursion crosses the inner list μ, so the
-- children arrive as a list of subtree sums.
rose-sum : ∀ {Γ} → Γ ⊢ rose [→] base number
rose-sum = lam (fold (bop add (fst (var zero) ∷ app sum (snd (var zero)) ∷ [])) (var zero))

rose-query : emp , rose ⊢ base number
rose-query = app rose-sum (var zero)
