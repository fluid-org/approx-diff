{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- Run from the approx-diff repository root.
module example.render.latex where

open import IO
open import IO.Finite using (writeFile)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤)
import Data.Vec as Vec
open import Data.Vec using (toList; tabulate)
open import Data.String using (String; _++_)
import matrix
import three
open import semiring-Q using (nonzero)
open import signature.example.interpretation (nonzero three.semiring) three.semiring
  using (Sig; interpretation)
open import example.runs (nonzero three.semiring) three.semiring three.C
  using (Run; query-run; const-run; length-run; fold0-run; case0-run; tag-run; case-l-run;
         case-r-run; test-run; map-run; adjacent-sums-run; filter-run; cond-run; eq-run; mult-run; mavg-run;
         total-run; sum-mul-run; rose-run; score-run; env; model-output; model-of)
open import example.render.constants (nonzero three.semiring) three.semiring using (show-const)
import example.render.annotated-value as AV
open AV Sig three.semiring interpretation three.C
  using (AVal; node; Tag; width; shape-of; shape-env-of)
open AV.annotate Sig three.semiring interpretation three.C three.semiring
  using (block-sum)

private
  module M3 = matrix.Mat three.semiring

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

  shw : ∀ {s} → _ → String
  shw {s} c = show-const {s} c

  cat : List String → String
  cat []       = ""
  cat (s ∷ ss) = s ++ cat ss

  appL : {A : Set} → List A → List A → List A
  appL []       ys = ys
  appL (x ∷ xs) ys = x ∷ appL xs ys

  tokens : ℕ → AVal ⊤ → List (String × ℕ × ℕ)
  tokens-snd : ℕ → AVal ⊤ → List (String × ℕ × ℕ)
  tokens-vec : ∀ {k} → ℕ → Vec.Vec (AVal ⊤) k → List (String × ℕ × ℕ)

  tokens off (node Tag.unit      _ n _)  = ("()" , n , off) ∷ []
  tokens off (node (Tag.const l) _ n _)  = (l , n , off) ∷ []
  tokens off (node Tag.inl       _ n cs) = ("\\mathsf{inl}\\," , n , off) ∷ tokens-vec (off + n) cs
  tokens off (node Tag.inr       _ n cs) = ("\\mathsf{inr}\\," , n , off) ∷ tokens-vec (off + n) cs
  tokens off (node (Tag.clo _)   _ n _)  = ("\\lambda" , n , off) ∷ []
  tokens off (node Tag.nil       _ n _)  = ("[\\,]" , n , off) ∷ []
  tokens off (node Tag.pair      _ n (p Vec.∷ q Vec.∷ Vec.[])) =
    ("(" , 0 , 0) ∷ appL (tokens (off + n) p)
      (("," , n , off) ∷ appL (tokens-snd (off + n + width p) q) ((")" , 0 , 0) ∷ []))
  tokens off (node Tag.cons      _ n (h Vec.∷ t Vec.∷ Vec.[])) =
    appL (tokens (off + n) h) (("\\cons" , n , off) ∷ tokens (off + n + width h) t)

  tokens-snd off (node Tag.pair _ n (p Vec.∷ q Vec.∷ Vec.[])) =
    appL (tokens (off + n) p) (("," , n , off) ∷ tokens-snd (off + n + width p) q)
  tokens-snd off t = tokens off t

  tokens-vec off Vec.[]      = []
  tokens-vec off (t Vec.∷ _) = tokens off t

  tokens-env : ℕ → List (AVal ⊤) → List (String × ℕ × ℕ)
  tokens-env _   []       = []
  tokens-env off (c ∷ []) = tokens off c
  tokens-env off (c ∷ cs) = appL (tokens off c) ((";" , 0 , 0) ∷ tokens-env (off + width c) cs)

  crep : ℕ → String
  crep zero    = ""
  crep (suc k) = "c" ++ crep k

  mark : three.Three → String
  mark three.D = "\\posD{\\bullet}"
  mark three.C = "\\posC{\\circ}"
  mark three.O = ""

  mcell : List (List three.Three) → ℕ × ℕ → String × ℕ × ℕ → String
  mcell rs (rn , roff) (_ , cn , coff) =
    " & \\gcell{$" ++ mark (block-sum (λ q p → at (nth q rs) p) roff rn coff cn) ++ "$}"

  mrow : List (List three.Three) → List (String × ℕ × ℕ) → String × ℕ × ℕ → String
  mrow rs ctoks (l , rn , roff) =
    "$" ++ l ++ "$" ++ cat (map (mcell rs (rn , roff)) ctoks) ++ " \\\\\n"

  mhead : String × ℕ × ℕ → String
  mhead (l , _ , _) = " & $" ++ l ++ "$"

  count : List (String × ℕ × ℕ) → ℕ
  count []       = 0
  count (_ ∷ ts) = suc (count ts)

  frame : String → String → String → String → String
  frame name spec header body =
    "\\run{" ++ name ++ "}\n{\\scriptsize\\setlength{\\tabcolsep}{1.5pt}%\n\\begin{tabular}{l"
    ++ spec ++ "}\n" ++ header ++ " \\\\\n" ++ body ++ "\\end{tabular}}\n"

  in-tokens out-tokens : Run → List (String × ℕ × ℕ)
  in-tokens  r = tokens-env 0 (shape-env-of (λ {s} c → shw {s} c) (env r))
  out-tokens r = tokens 0 (shape-of (λ {s} c → shw {s} c) (model-output r))

  grid : String → Run → String
  grid name r =
    frame name (crep (count itoks)) (cat (map mhead itoks))
          (cat (map (mrow (rows (model-of r)) itoks) otoks))
    where
    itoks = in-tokens r
    otoks = out-tokens r

contents : String
contents =
  grid "query"       query-run ++
  grid "const"       const-run ++
  grid "length"      length-run ++
  grid "fold0"       fold0-run ++
  grid "case0"       case0-run ++
  grid "tag"         tag-run ++
  grid "case-left"   case-l-run ++
  grid "case-right"  case-r-run ++
  grid "test"        test-run ++
  grid "map"         map-run ++
  grid "adjacent-sums"      adjacent-sums-run ++
  grid "filter"      filter-run ++
  grid "cond"        cond-run ++
  grid "eq"          eq-run ++
  grid "mult"        mult-run ++
  grid "mavg"        mavg-run ++
  grid "total"       total-run ++
  grid "sum-mul"     sum-mul-run ++
  grid "rose"        rose-run ++
  grid "score"       score-run

main : Main
main = run (writeFile "test-baselines/slices.tex" contents)
