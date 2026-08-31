{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- Run from the approx-diff repository root.
module example.render.latex where

open import IO
open import IO.Finite using (writeFile)
open import Data.Bool using (Bool; false; true; _∨_; if_then_else_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _≡ᵇ_)
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
         case-r-run; test-run; map-run; adjacent-sums-run; merge-run; filter-run; cond-run; eq-run; mult-run; mavg-run;
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

  sel? : Maybe ℕ → ℕ → Bool
  sel? nothing  _ = false
  sel? (just k) i = k ≡ᵇ i

  band : Bool → String
  band false = ""
  band true  = "\\cellcolor{blue!10}"

  tok-of : Maybe ℕ → List (String × ℕ × ℕ) → Maybe (ℕ × ℕ)
  tok-of nothing  _  = nothing
  tok-of (just k) ts = just (pick k ts)
    where
    pick : ℕ → List (String × ℕ × ℕ) → ℕ × ℕ
    pick _       []                 = 0 , 0
    pick zero    ((_ , n , o) ∷ _)  = n , o
    pick (suc k) (_ ∷ ts)           = pick k ts

  reach? : List (List three.Three) → Maybe (ℕ × ℕ) → ℕ → ℕ → three.Three
  reach? rs nothing        _  _    = three.O
  reach? rs (just (n , o)) rn roff = block-sum (λ q p → at (nth q rs) p) roff rn o n

  label-cell : Bool → three.Three → String → String
  label-cell true  _       l = "\\cellcolor{blue!25}$" ++ l ++ "$"
  label-cell false three.O l = "$" ++ l ++ "$"
  label-cell false three.D l = "\\cellcolor{blue!10}$" ++ l ++ "$"
  label-cell false three.C l = "\\cellcolor{blue!10}$\\posC{" ++ l ++ "}$"

  cells-go : List (List three.Three) → ℕ → ℕ → Bool → Maybe ℕ → ℕ → List (String × ℕ × ℕ) → String
  cells-go rs rn roff rsel csel i [] = ""
  cells-go rs rn roff rsel csel i ((_ , cn , coff) ∷ cts) =
    (if i ≡ᵇ zero then "" else " & ") ++ band (rsel ∨ sel? csel i) ++ "\\gcell{$"
    ++ mark (block-sum (λ q p → at (nth q rs) p) roff rn coff cn) ++ "$}"
    ++ cells-go rs rn roff rsel csel (suc i) cts

  heads-go : List (List three.Three) → Maybe (ℕ × ℕ) → Maybe ℕ → ℕ → List (String × ℕ × ℕ) → String
  heads-go rs hrTok hc i [] = ""
  heads-go rs hrTok hc i ((l , cn , coff) ∷ ts) =
    (if i ≡ᵇ zero then "" else " & ") ++ label-cell (sel? hc i) (reach? rs hrTok cn coff) l
    ++ heads-go rs hrTok hc (suc i) ts

  count : List (String × ℕ × ℕ) → ℕ
  count []       = 0
  count (_ ∷ ts) = suc (count ts)

  in-tokens out-tokens : Run → List (String × ℕ × ℕ)
  in-tokens  r = tokens-env 0 (shape-env-of (λ {s} c → shw {s} c) (env r))
  out-tokens r = tokens 0 (shape-of (λ {s} c → shw {s} c) (model-output r))

  rows-go : List (List three.Three) → List (String × ℕ × ℕ) → Maybe ℕ → Maybe ℕ → Maybe (ℕ × ℕ)
                → ℕ → List (String × ℕ × ℕ) → String
  rows-go rs ctoks hr hc hcTok i [] = ""
  rows-go rs ctoks hr hc hcTok i ((l , rn , roff) ∷ rts) =
    cells-go rs rn roff (sel? hr i) hc 0 ctoks ++ " & "
    ++ label-cell (sel? hr i) (reach? rs hcTok rn roff) l ++ " \\\\\n"
    ++ rows-go rs ctoks hr hc hcTok (suc i) rts

  hgrid : String → Run → Maybe ℕ → Maybe ℕ → String
  hgrid name r hr hc =
    "\\run{" ++ name ++ "}\n{\\scriptsize\\setlength{\\tabcolsep}{1.5pt}%\n\\begin{tabular}{"
    ++ crep (count itoks) ++ "|l}\n" ++ heads-go rs (tok-of hr otoks) hc 0 itoks ++ " & \\\\ \\hline\n"
    ++ rows-go rs itoks hr hc (tok-of hc itoks) 0 otoks ++ "\\end{tabular}}\n"
    where
    itoks = in-tokens r
    otoks = out-tokens r
    rs = rows (model-of r)

  grid : String → Run → String
  grid name r = hgrid name r nothing nothing

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
  grid "merge"       merge-run  ++
  grid "cond"        cond-run ++
  grid "eq"          eq-run ++
  grid "mult"        mult-run ++
  grid "mavg"        mavg-run ++
  grid "total"       total-run ++
  grid "sum-mul"     sum-mul-run ++
  grid "rose"        rose-run ++
  grid "score"       score-run   ++
  hgrid "map (backward slice)"          map-run           (just 2) nothing ++
  hgrid "adjacent-sums (forward slice)" adjacent-sums-run nothing (just 2) ++
  hgrid "merge (forward slice)"         merge-run         nothing (just 5)

main : Main
main = run (writeFile "test-baselines/slices.tex" contents)
