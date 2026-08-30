{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- Slices as LaTeX: a selection on one side of a run and the weights it induces on the other,
-- each side the value with positions wrapped in \posD/\posC/\posO by weight. Run from the
-- approx-diff repository root.
module example.render.latex where

open import IO
open import IO.Finite using (writeFile)
open import Data.Bool using (if_then_else_)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
import Data.Vec as Vec
open import Data.Vec using (toList; tabulate)
open import Data.String using (String; _++_)
import matrix
import three
open import semiring-Q using (nonzero)
open import signature.example.interpretation (nonzero three.semiring) three.semiring
  using (Sig; interpretation)
open import example.runs (nonzero three.semiring) three.semiring three.C
  using (Run; map-run; filter-run; query-run; env; model-output; model-of)
open import example.render.constants (nonzero three.semiring) three.semiring using (show-const)
import example.render.annotated-value as AV
open AV Sig three.semiring interpretation three.C using (AVal; node; Tag)
open AV.annotate Sig three.semiring interpretation three.C three.semiring
  using (row→aval; row→avals)

private
  module M3 = matrix.Mat three.semiring

  cmd : three.Three → String → String
  cmd three.D s = "\\posD{" ++ s ++ "}"
  cmd three.C s = "\\posC{" ++ s ++ "}"
  cmd three.O s = "\\posO{" ++ s ++ "}"

  tex-aval : AVal three.Three → String
  tex-kids : ∀ {k} → Vec.Vec (AVal three.Three) k → String

  tex-aval (node Tag.unit      a _ _)  = cmd a "()"
  tex-aval (node (Tag.const l) a _ _)  = cmd a l
  tex-aval (node Tag.inl       a _ cs) = cmd a "\\mathsf{inl}\\," ++ tex-kids cs
  tex-aval (node Tag.inr       a _ cs) = cmd a "\\mathsf{inr}\\," ++ tex-kids cs
  tex-aval (node (Tag.clo _)   a _ _)  = cmd a "\\lambda"
  tex-aval (node Tag.nil       a _ _)  = cmd a "[\\,]"
  tex-aval (node Tag.pair      a _ (p Vec.∷ q Vec.∷ Vec.[])) =
    cmd a "(" ++ tex-aval p ++ cmd a ",\\," ++ tex-aval q ++ cmd a ")"
  tex-aval (node Tag.cons      a _ (h Vec.∷ t Vec.∷ Vec.[])) =
    tex-aval h ++ " " ++ cmd a "\\cons" ++ " " ++ tex-aval t

  tex-kids Vec.[]      = ""
  tex-kids (t Vec.∷ _) = tex-aval t

  tex-env : List (AVal three.Three) → String
  tex-env []       = ""
  tex-env (c ∷ []) = tex-aval c
  tex-env (c ∷ cs) = tex-aval c ++ ";\\ " ++ tex-env cs

  at : List three.Three → ℕ → three.Three
  at []       _       = three.O
  at (a ∷ _)  zero    = a
  at (_ ∷ as) (suc n) = at as n

  nth : ℕ → List (List three.Three) → List three.Three
  nth _       []       = []
  nth zero    (r ∷ _)  = r
  nth (suc n) (_ ∷ rs) = nth n rs

  rows : ∀ {m n} → M3.Matrix m n → List (List three.Three)
  rows M = toList (tabulate (λ q → toList (tabulate (M q))))

  δ : ℕ → ℕ → three.Three
  δ p i = if i ≡ᵇ p then three.D else three.O

  show : ∀ {s} → _ → String
  show {s} c = show-const {s} c

  tex-out : Run → (ℕ → three.Three) → String
  tex-out r f = tex-aval (row→aval (λ {s} c → show {s} c) f (model-output r))

  tex-in : Run → (ℕ → three.Three) → String
  tex-in r f = tex-env (row→avals (λ {s} c → show {s} c) f (env r))

  backward : String → Run → ℕ → String
  backward name r q =
    "\\slice{" ++ name ++ "}{" ++ tex-out r (δ q) ++ "}{" ++ tex-in r (at (nth q (rows (model-of r)))) ++ "}\n"

  forward : String → Run → ℕ → String
  forward name r p =
    "\\slice{" ++ name ++ "}{" ++ tex-in r (δ p) ++ "}{" ++ tex-out r (at (nth p (rows (model-of r M3.ᵀ)))) ++ "}\n"

contents : String
contents =
  backward "map, backward, second output element"  map-run    5 ++
  forward  "map, forward, second input element"    map-run    5 ++
  forward  "filter, forward, comparison target"    filter-run 0 ++
  backward "query, backward, the sum"              query-run  0

main : Main
main = run (writeFile "latex-preview/slices.tex" contents)
