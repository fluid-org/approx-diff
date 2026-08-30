{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- A constructor's positions have identical matrix rows, so one line per constructor suffices,
-- selected at its first position. Run from the approx-diff repository root.
module example.render.latex where

open import IO
open import IO.Finite using (writeFile)
open import Data.Bool using (if_then_else_)
open import Data.List using (List; []; _∷_; concat; map)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
import Data.Nat.Show as ℕ-Show
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤)
import Data.Vec as Vec
open import Data.Vec using (toList; tabulate)
open import Data.String using (String; _++_; _==_)
import matrix
import three
open import semiring-Q using (nonzero)
open import signature.example.interpretation (nonzero three.semiring) three.semiring
  using (Sig; interpretation)
open import example.runs (nonzero three.semiring) three.semiring three.C
  using (Run; query-run; const-run; length-run; fold0-run; case0-run; tag-run; case-l-run;
         case-r-run; test-run; map-run; filter-run; cond-run; eq-run; mult-run; mavg-run;
         total-run; sum-mul-run; rose-run; env; model-output; model-of)
open import example.render.constants (nonzero three.semiring) three.semiring using (show-const)
import example.render.annotated-value as AV
open AV Sig three.semiring interpretation three.C
  using (AVal; node; Tag; arity; label-of; fold-all; shape-of; shape-env-of)
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

  shw : ∀ {s} → _ → String
  shw {s} c = show-const {s} c

  tex-out : Run → (ℕ → three.Three) → String
  tex-out r f = tex-aval (row→aval (λ {s} c → shw {s} c) f (model-output r))

  tex-in : Run → (ℕ → three.Three) → String
  tex-in r f = tex-env (row→avals (λ {s} c → shw {s} c) f (env r))

  node-entry : ∀ (t : Tag) → ⊤ → ℕ → ℕ → Vec.Vec (List (ℕ × String)) (arity t) → List (ℕ × String)
  node-entry t _ zero    off rs = concat (toList rs)
  node-entry t _ (suc _) off rs = (off , label-of t) ∷ concat (toList rs)

  reps-of : List (AVal ⊤) → List (ℕ × String)
  reps-of ts = concat (fold-all node-entry 0 ts)

  tex-label : String → String
  tex-label l = if l == "∷" then "$\\cons$" else l

  bslice fslice : Run → ℕ × String → String
  bslice r (q , l) =
    "\\slice{$\\leftarrow$ " ++ ℕ-Show.show q ++ " (" ++ tex-label l ++ ")}{"
    ++ tex-out r (δ q) ++ "}{" ++ tex-in r (at (nth q (rows (model-of r)))) ++ "}\n"
  fslice r (p , l) =
    "\\slice{$\\rightarrow$ " ++ ℕ-Show.show p ++ " (" ++ tex-label l ++ ")}{"
    ++ tex-in r (δ p) ++ "}{" ++ tex-out r (at (nth p (rows (model-of r M3.ᵀ)))) ++ "}\n"

  cat : List String → String
  cat []       = ""
  cat (s ∷ ss) = s ++ cat ss

  catalogue : String → Run → String
  catalogue name r =
    "\\run{" ++ name ++ "}\n"
    ++ cat (map (bslice r) (reps-of (shape-of (λ {s} c → shw {s} c) (model-output r) ∷ [])))
    ++ cat (map (fslice r) (reps-of (shape-env-of (λ {s} c → shw {s} c) (env r))))

contents : String
contents =
  catalogue "query"      query-run   ++
  catalogue "const"      const-run   ++
  catalogue "length"     length-run  ++
  catalogue "fold0"      fold0-run   ++
  catalogue "case0"      case0-run   ++
  catalogue "tag"        tag-run     ++
  catalogue "case-left"  case-l-run  ++
  catalogue "case-right" case-r-run  ++
  catalogue "test"       test-run    ++
  catalogue "map"        map-run     ++
  catalogue "filter"     filter-run  ++
  catalogue "cond"       cond-run    ++
  catalogue "eq"         eq-run      ++
  catalogue "mult"       mult-run    ++
  catalogue "mavg"       mavg-run    ++
  catalogue "total"      total-run   ++
  catalogue "sum-mul"    sum-mul-run ++
  catalogue "rose"       rose-run

main : Main
main = run (writeFile "latex-preview/slices.tex" contents)
