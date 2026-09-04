{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- Matrices as LaTeX tables: one column per input constructor, one row per output constructor, each
-- entry the sum over those constructors' positions. A selection is a weight vector on either axis,
-- so the result of one table's slice can be the selection of the next.
module example.render.grid where

open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.String using (String; _++_)
import three
open three using (Three; O; C; D; _⊓_; _⊔_)

-- A label, the number of positions it covers, and the offset where they start.
Label : Set
Label = String × ℕ × ℕ

Sel : Set
Sel = ℕ → Three

Mat : Set
Mat = List (List Three)

none : Sel
none _ = O

private
  at : List Three → ℕ → Three
  at []       _       = O
  at (a ∷ _)  zero    = a
  at (_ ∷ as) (suc n) = at as n

  nth : ℕ → Mat → List Three
  nth _       []       = []
  nth zero    (r ∷ _)  = r
  nth (suc n) (_ ∷ rs) = nth n rs

  entry : Mat → ℕ → ℕ → Three
  entry M q p = at (nth q M) p

  span : (ℕ → Three) → ℕ → ℕ → Three
  span f o zero    = O
  span f o (suc k) = f o ⊔ span f (suc o) k

  width-of : List Label → ℕ
  width-of []                 = 0
  width-of ((_ , n , _) ∷ ts) = n + width-of ts

  sel-of : Sel → Label → Three
  sel-of s (_ , n , o) = span s o n

  block : Mat → Label → Label → Three
  block M (_ , qn , qo) (_ , pn , po) = span (λ q → span (entry M q) po pn) qo qn

  reach-in : Mat → ℕ → Sel → Label → Three
  reach-in M h osel (_ , pn , po) = span (λ p → span (λ q → osel q ⊓ entry M q p) 0 h) po pn

  reach-out : Mat → ℕ → Sel → Label → Three
  reach-out M w isel (_ , qn , qo) = span (λ q → span (λ p → isel p ⊓ entry M q p) 0 w) qo qn

  mark : Three → String
  mark D = "\\posD{\\bullet}"
  mark C = "\\posC{\\circ}"
  mark O = ""

  band : Three → String
  band O = ""
  band _ = "\\cellcolor{blue!10}"

  label-cell : Three → Three → String → String
  label-cell O O l = "$" ++ l ++ "$"
  label-cell O D l = "\\cellcolor{blue!10}$" ++ l ++ "$"
  label-cell O C l = "\\cellcolor{blue!10}$\\posC{" ++ l ++ "}$"
  label-cell _ _ l = "\\cellcolor{blue!25}$" ++ l ++ "$"

  crep : ℕ → String
  crep zero    = ""
  crep (suc k) = "c" ++ crep k

  cat : List String → String
  cat []       = ""
  cat (s ∷ ss) = s ++ cat ss

  amp : List String → String
  amp []           = ""
  amp (x ∷ [])     = x
  amp (x ∷ y ∷ xs) = x ++ " & " ++ amp (y ∷ xs)

  cell : Mat → Sel → Sel → Label → Label → String
  cell M isel osel t u =
    band (sel-of osel t ⊔ sel-of isel u) ++ "\\gcell{$" ++ mark (block M t u) ++ "$}"

  row-of : Mat → ℕ → List Label → Sel → Sel → Label → String
  row-of M w ilabels isel osel t =
    amp (map (cell M isel osel t) ilabels) ++ " & "
    ++ label-cell (sel-of osel t) (reach-out M w isel t) (proj₁ t) ++ " \\\\\n"

-- The positions of the token at the given index, selected at full weight.
sel-label : List Label → ℕ → Sel
sel-label []                 _       _ = O
sel-label ((_ , n , o) ∷ _)  zero    p = span (λ i → if-eq i p) o n
  where
  if-eq : ℕ → ℕ → Three
  if-eq zero    zero    = D
  if-eq (suc i) (suc j) = if-eq i j
  if-eq _       _       = O
sel-label (_ ∷ ts)           (suc k) p = sel-label ts k p

grid : String → List Label → List Label → Mat → Sel → Sel → String
grid name ilabels olabels M isel osel =
  "\\run{" ++ name ++ "}\n{\\scriptsize\\setlength{\\tabcolsep}{1.5pt}%\n\\begin{tabular}{"
  ++ crep (count ilabels) ++ "|l}\n"
  ++ amp (map (λ t → label-cell (sel-of isel t) (reach-in M h osel t) (proj₁ t)) ilabels)
  ++ " & \\\\ \\hline\n"
  ++ cat (map (row-of M w ilabels isel osel) olabels)
  ++ "\\end{tabular}}\n"
  where
  w = width-of ilabels
  h = width-of olabels
  count : List Label → ℕ
  count []       = 0
  count (_ ∷ ts) = suc (count ts)
