{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- The model's output and relation of each example program at its input, the relation as slices in
-- annotated-value form: the input environment annotated with the relation's row at each output
-- position. Run from the approx-diff repository root.
module example.render.relations where

open import IO
open import IO.Finite using (writeFile)
open import Data.String using (String; _++_)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
import Data.Nat.Show as ℕ-Show
open import Data.Vec using (toList; tabulate)
import Data.Vec as Vec
open import Level using (0ℓ)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
import matrix
import three
import semiring-sign as sign
open import Data.Product using (_×_; _,_)
open import Data.Rational using (ℚ)
open import commutative-semiring-product using (_⊗S_)
open import semiring-Q using (nonzero)
import example.render.constants
import signature.example.interpretation
import example.runs
import language-operational.evaluation
import example.render.annotated-value as AV

-- Rendering over a semiring, given how a scalar is shown after a position.
module render {A : Setoid 0ℓ 0ℓ} (as-weight : ℚ → Setoid.Carrier A) (S : CommutativeSemiring A)
              (ctrl-weight : Setoid.Carrier A) (suffix : Setoid.Carrier A → String) where

  open CommutativeSemiring S using (ι; ε)
  open signature.example.interpretation as-weight S using (Sig; interpretation)
  open language-operational.evaluation Sig S interpretation ctrl-weight using (Val; Env)
  open AV Sig S interpretation ctrl-weight using (AVal; node; Tag)
  open AV.annotate Sig S interpretation ctrl-weight S using (row→aval; row→avals)
  open example.render.constants as-weight S using (show-const)

  private
    module M = matrix.Mat S
    Scalar = Setoid.Carrier A

    show-c : ℕ → String → Scalar → String
    show-c zero    l a = l
    show-c (suc _) l a = l ++ suffix a

    show-aval : AVal Scalar → String
    show-kids : ∀ {k} → Vec.Vec (AVal Scalar) k → String

    show-aval (node Tag.unit      a _ _)  = "()" ++ suffix a
    show-aval (node (Tag.const l) a n _)  = show-c n l a
    show-aval (node Tag.inl       a _ cs) = "inl" ++ suffix a ++ " " ++ show-kids cs
    show-aval (node Tag.inr       a _ cs) = "inr" ++ suffix a ++ " " ++ show-kids cs
    show-aval (node (Tag.clo _)   a _ _)  = "<closure>" ++ suffix a
    show-aval (node Tag.nil       a _ _)  = "[]" ++ suffix a
    show-aval (node Tag.pair      a _ (p Vec.∷ q Vec.∷ Vec.[])) =
      "(" ++ show-aval p ++ ", " ++ show-aval q ++ ")" ++ suffix a
    show-aval (node Tag.cons      a _ (h Vec.∷ t Vec.∷ Vec.[])) =
      show-aval h ++ " ∷" ++ suffix a ++ " " ++ show-aval t

    show-kids Vec.[]       = ""
    show-kids (t Vec.∷ _) = show-aval t

    show-env : List (AVal Scalar) → String
    show-env []       = ""
    show-env (c ∷ []) = show-aval c
    show-env (c ∷ cs) = show-aval c ++ "; " ++ show-env cs

    at : List Scalar → ℕ → Scalar
    at []       _       = ε
    at (a ∷ _)  zero    = a
    at (_ ∷ as) (suc n) = at as n

    rows : ∀ {m n} → M.Matrix m n → List (List Scalar)
    rows M = toList (tabulate (λ q → toList (tabulate (M q))))

    lines : List String → String
    lines []       = ""
    lines (l ∷ ls) = l ++ "\n" ++ lines ls

  show-run : ∀ {Γ τ} → String → Env Γ → Val τ → ∀ {m n} → M.Matrix m n → String
  show-run name γ v R =
    lines (name ∷
           ("  in  " ++ show-env (row→avals (λ {s} c → show-const {s} c) (λ _ → ι) γ)) ∷
           ("  out " ++ show-aval (row→aval (λ {s} c → show-const {s} c) (λ _ → ι) v)) ∷ [])
    ++ go 0 (rows R)
    where
    go : ℕ → List (List Scalar) → String
    go q []       = ""
    go q (r ∷ rs) =
      "  " ++ ℕ-Show.show q ++ "   " ++ show-env (row→avals (λ {s} c → show-const {s} c) (at r) γ) ++ "\n"
      ++ go (suc q) rs

  show-composite : ∀ {τ} → String → Val τ → ∀ {m n} → M.Matrix m n → String
  show-composite name v R = name ++ "\n" ++ go 0 (rows R)
    where
    go : ℕ → List (List Scalar) → String
    go q []       = ""
    go q (r ∷ rs) =
      "  " ++ ℕ-Show.show q ++ "   " ++ show-aval (row→aval (λ {s} c → show-const {s} c) (at r) v) ++ "\n"
      ++ go (suc q) rs

private
  suffix3 : three.Three → String
  suffix3 three.D = ""
  suffix3 three.C = "ᶜ"
  suffix3 three.O = "⊥"

  suffix-sign : sign.Sign → String
  suffix-sign sign.pos = ""
  suffix-sign sign.neg = "⁻"
  suffix-sign sign.unk = "?"
  suffix-sign sign.zer = "⊥"

  -- A sign paired with the three-chain: the sign of a position's effect, and whether the position
  -- is reached as value flow or through a control point.
  suffix-signed : sign.Sign × three.Three → String
  suffix-signed (s , three.O) = "⊥"
  suffix-signed (s , k)       = suffix-sign s ++ suffix3 k

  signed-weight : ℚ → sign.Sign × three.Three
  signed-weight q = sign.sign-of q , nonzero three.semiring q

  module chain where
    open render (nonzero three.semiring) three.semiring three.C suffix3
    open example.runs (nonzero three.semiring) three.semiring three.C
    module M3 = matrix.Mat three.semiring

    entry : String → Run → String
    entry name r = show-run name (env r) (model-output r) (model-of r)

    related : String → Run → String
    related name r = show-composite name (model-output r) (model-of r M3.∘ (model-of r M3.ᵀ))

    forward : String → Run → String
    forward name r = show-composite name (model-output r) (model-of r M3.ᵀ)

    contents : String
    contents =
      entry "query"      query-run  ++
      entry "const"      const-run  ++
      entry "length"     length-run ++
      entry "fold0"      fold0-run  ++
      entry "case0"      case0-run  ++
      entry "tag"        tag-run    ++
      entry "case-left"  case-l-run ++
      entry "case-right" case-r-run ++
      entry "test"       test-run   ++
      entry "map"        map-run    ++
      entry "filter"     filter-run ++
      entry "cond"       cond-run   ++
      entry "eq"         eq-run     ++
      entry "mult"       mult-run   ++
      entry "mavg"       mavg-run   ++
      entry "total"      total-run   ++
      entry "sum-mul"    sum-mul-run ++
      entry "rose"       rose-run    ++
      related "mavg-related" mavg-run ++
      forward "map-forward"    map-run    ++
      forward "filter-forward" filter-run ++
      forward "query-forward"  query-run

  module signed where
    open render signed-weight (sign.semiring ⊗S three.semiring) (sign.unk , three.C) suffix-signed
    open example.runs signed-weight (sign.semiring ⊗S three.semiring) (sign.unk , three.C)

    entry : String → Run → String
    entry name r = show-run name (env r) (model-output r) (model-of r)

    contents : String
    contents = entry "score" score-run

contents : String
contents = chain.contents ++ signed.contents

main : Main
main = run (writeFile "test-baselines/relations.txt" contents)
