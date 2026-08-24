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
import two
import three
import semiring-sign as sign
open import Data.Product using (_×_; _,_)
open import Data.Rational using (ℚ)
open import commutative-semiring-product using (_⊗S_)
open import signature.example.collapse using (nonzero)
import example.render.constants
import signature.example.interpretation
import example.runs
import language-operational.evaluation
import example.render.annotated-value as AV

-- Rendering over a semiring, given how a scalar is shown after a position.
module over {A : Setoid 0ℓ 0ℓ} (collapse : ℚ → Setoid.Carrier A) (S : CommutativeSemiring A)
              (ctrl-weight : Setoid.Carrier A) (suffix : Setoid.Carrier A → String) where

  open CommutativeSemiring S using (ι; ε)
  open signature.example.interpretation collapse S using (Sig; interpretation)
  open language-operational.evaluation Sig S interpretation ctrl-weight using (Val; Env)
  open AV Sig S interpretation ctrl-weight using (AVal; node; Tag)
  open AV.annotate Sig S interpretation ctrl-weight S using (row→aval; row→avals)
  open example.render.constants collapse S using (show-const)

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

  show-composite : ∀ {τ} → String → Val τ → ∀ {m} → M.Matrix m m → String
  show-composite name v R = name ++ "\n" ++ go 0 (rows R)
    where
    go : ℕ → List (List Scalar) → String
    go q []       = ""
    go q (r ∷ rs) =
      "  " ++ ℕ-Show.show q ++ "   " ++ show-aval (row→aval (λ {s} c → show-const {s} c) (at r) v) ++ "\n"
      ++ go (suc q) rs

private
  suffix2 : two.Two → String
  suffix2 two.I = ""
  suffix2 two.O = "⊥"

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

  collapse-signed : ℚ → sign.Sign × three.Three
  collapse-signed q = sign.sign-of q , nonzero three.semiring q

  module R2 = over (nonzero two.semiring) two.semiring two.I suffix2
  module R3 = over (nonzero three.semiring) three.semiring three.C suffix3
  module RS = over collapse-signed (sign.semiring ⊗S three.semiring) (sign.unk , three.C) suffix-signed
  module E2 = example.runs (nonzero two.semiring) two.semiring two.I
  module E3 = example.runs (nonzero three.semiring) three.semiring three.C
  module ES = example.runs collapse-signed (sign.semiring ⊗S three.semiring) (sign.unk , three.C)

  sign-run : String → ES.Run → String
  sign-run name r = RS.show-run name (ES.env r) (ES.model-output r) (ES.model-of r)

  two-run : String → E2.Run → String
  two-run name r = R2.show-run name (E2.env r) (E2.model-output r) (E2.model-of r)

  module M3 = matrix.Mat three.semiring

  three-related : String → E3.Run → String
  three-related name r = R3.show-composite name (E3.model-output r) (E3.model-of r M3.∘ (E3.model-of r M3.ᵀ))

  three-run : String → E3.Run → String
  three-run name r = R3.show-run name (E3.env r) (E3.model-output r) (E3.model-of r)

-- The Booleans for the programs whose point is which positions are read; the three-chain, which
-- separates consumption from value flow, for those whose point is that distinction; signs paired
-- with the three-chain for the saliency reading of the grid scorer.
contents : String
contents =
  two-run   "query"      E2.query-run  ++
  two-run   "const"      E2.const-run  ++
  two-run   "length"     E2.length-run ++
  two-run   "fold0"      E2.fold0-run  ++
  two-run   "case0"      E2.case0-run  ++
  two-run   "tag"        E2.tag-run    ++
  two-run   "case-left"  E2.case-l-run ++
  two-run   "case-right" E2.case-r-run ++
  two-run   "test"       E2.test-run   ++
  three-run "map"        E3.map-run    ++
  three-run "filter"     E3.filter-run ++
  three-run "cond"       E3.cond-run   ++
  three-run "eq"         E3.eq-run     ++
  three-run "mult"       E3.mult-run   ++
  three-run "mavg"       E3.mavg-run   ++
  three-related "mavg-related" E3.mavg-run ++
  sign-run  "score"      ES.score-run

main : Main
main = run (writeFile "test-baselines/relations.txt" contents)
