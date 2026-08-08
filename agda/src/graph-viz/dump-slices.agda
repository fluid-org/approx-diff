{-# OPTIONS --prop --postfix-projections --guardedness #-}

module graph-viz.dump-slices where

open import IO
open import IO.Finite using (writeFile)
open import Data.String using (String; _++_)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.List using (List; []; _∷_) renaming (foldr to foldrL)
open import Data.Nat using (ℕ; zero; suc)
import Data.Integer as ℤ
import Data.Fin as Fin
open import Data.Vec using (Vec; toList; tabulate)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; ↥_; ↧_) renaming (_+_ to _+ℚ_)
import Data.Integer.Show as ℤ-Show
open import Level using (0ℓ)
import two
import matrix
import free-realise
import label
open import primitives using (Primitives)
import example.primitives as EP
open import example.runs
  using (dep; dep-const; dep-length; dep-fold0; dep-case0; dep-tag; dep-map)

open import language-syntax EP.Sig using (type; base; list; unit; μ; var; _[×]_; _[+]_; sub-ren-id)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import language-operational.evaluation EP.Sig EP.primitives using (Val)
open Val
open import language-operational.annotated-value EP.Sig EP.primitives
  using (AVal; node; Shape; shape-of)
import language-operational.annotated-value as AV
open AV.annotate EP.Sig EP.primitives two.semiring using (row→aval; aval→row)
open import language-operational.list-value EP.Sig EP.primitives using (_∷ᵥ_; nilᵥ)
open Primitives EP.primitives using (sort-val; sort-width)

private
  module TM = matrix.Mat two.semiring
  module FR = free-realise two.semiring (λ {x} → two.⊤-add-top {x})

elemT : type 0
elemT = base EP.label [×] base EP.number

listT : type 0
listT = list elemT

el : label.label → ℚ → Val elemT
el l n = pair (const l) (const n)

γ-val : Val listT
γ-val = el label.a 0ℚ ∷ᵥ el label.b 1ℚ ∷ᵥ el label.a 1ℚ ∷ᵥ nilᵥ

show-ℚ : ℚ → String
show-ℚ q with ↧ q
... | ℤ.+ (suc zero) = ℤ-Show.show (↥ q)
... | d              = ℤ-Show.show (↥ q) ++ "/" ++ ℤ-Show.show d

show-label : label.label → String
show-label label.a = "a"
show-label label.b = "b"
show-label label.c = "c"
show-label label.d = "d"

showC : ∀ {s} → sort-val s → String
showC {EP.number} q = show-ℚ q
showC {EP.label}  l = show-label l

private
  mark : two.Two → String
  mark two.I = ""
  mark two.O = "⊥"

  show-c : ℕ → String → two.Two → String
  show-c zero    l a = "_"
  show-c (suc _) l a = l ++ mark a

  mutual
    show-aval : AVal two.Two → String
    show-aval (node Shape.unit      a _ _)  = "()" ++ mark a
    show-aval (node (Shape.const l) a n _)  = show-c n l a
    show-aval (node Shape.inl       a _ cs) = "inl" ++ mark a ++ " " ++ show-kids cs
    show-aval (node Shape.inr       a _ cs) = "inr" ++ mark a ++ " " ++ show-kids cs
    show-aval (node Shape.clo       a _ _)  = "<closure>" ++ mark a
    show-aval (node Shape.nil       a _ _)  = "[]" ++ mark a
    show-aval (node Shape.pair      a _ (p ∷ q ∷ _)) =
      "(" ++ show-aval p ++ ", " ++ show-aval q ++ ")" ++ mark a
    show-aval (node Shape.pair      a _ _)  = "?"
    show-aval (node Shape.cons      a _ (h ∷ t ∷ _)) =
      show-aval h ++ " ∷" ++ mark a ++ " " ++ show-aval t
    show-aval (node Shape.cons      a _ _)  = "?"

    show-kids : List (AVal two.Two) → String
    show-kids []      = ""
    show-kids (t ∷ _) = show-aval t

  lookupO : List two.Two → ℕ → two.Two
  lookupO []       _       = two.O
  lookupO (b ∷ _)  zero    = b
  lookupO (_ ∷ bs) (suc n) = lookupO bs n

  render-row : ∀ {τ} (v : Val τ) → List two.Two → String
  render-row v bits = show-aval (row→aval (λ {s} c → showC {s} c) (lookupO bits) v)

  slice-over : ∀ {τ} (v : Val τ) {m n} → TM.Matrix m n → String
  slice-over v {m} M =
    foldrL (λ r s → r ++ "\n" ++ s) ""
      (toList (tabulate {n = m} (λ q → render-row v (toList (tabulate (M q))))))

  slice : ∀ {m n} → TM.Matrix m n → String
  slice = slice-over γ-val

numlistT : type 0
numlistT = list (base EP.number)

γ-nums-val : Val numlistT
γ-nums-val = const 0ℚ ∷ᵥ const 1ℚ ∷ᵥ const (1ℚ +ℚ 1ℚ) ∷ᵥ nilᵥ

δ-out : Val numlistT
δ-out = const (0ℚ +ℚ 1ℚ) ∷ᵥ const (1ℚ +ℚ 1ℚ) ∷ᵥ const ((1ℚ +ℚ 1ℚ) +ℚ 1ℚ) ∷ᵥ nilᵥ

private
  vec-of : ∀ {n} → List two.Two → TM.Vec n
  vec-of bs i = lookupO bs (Fin.toℕ i)

  bits-of : ∀ n → TM.Vec n → List two.Two
  bits-of n w = toList (tabulate {n = n} w)

  consumes : ∀ {m n} → TM.Matrix m n → TM.Vec m → TM.Vec n
  consumes M = FR.app (M TM.ᵀ)

  erases : ∀ {m n} → TM.Matrix m n → TM.Vec n → TM.Vec m
  erases M = FR.app M

  consᵃ : two.Two → AVal two.Two → AVal two.Two → AVal two.Two
  consᵃ a h t = node Shape.cons a 2 (h ∷ t ∷ [])

  nilᵃ : two.Two → AVal two.Two
  nilᵃ a = node Shape.nil a 2 []

  numᵃ : ℚ → two.Two → AVal two.Two
  numᵃ q a = node (Shape.const (show-ℚ q)) a 1 []

  cell1-sel : AVal two.Two
  cell1-sel =
    consᵃ two.I (numᵃ 0ℚ two.O)
      (consᵃ two.O (numᵃ 1ℚ two.O)
        (consᵃ two.O (numᵃ (1ℚ +ℚ 1ℚ) two.O) (nilᵃ two.O)))

  out-cell2-sel : AVal two.Two
  out-cell2-sel =
    consᵃ two.O (numᵃ (0ℚ +ℚ 1ℚ) two.O)
      (consᵃ two.I (numᵃ (1ℚ +ℚ 1ℚ) two.O)
        (consᵃ two.O (numᵃ ((1ℚ +ℚ 1ℚ) +ℚ 1ℚ) two.O) (nilᵃ two.O)))

  sel-of : ∀ {n} → AVal two.Two → TM.Vec n
  sel-of p i = aval→row p (Fin.toℕ i)

  fwd-bits : ∀ {m n} → TM.Matrix m n → TM.Vec n → List two.Two
  fwd-bits {m} M sel = bits-of m (erases M sel)

  bwd-bits : ∀ {m n} → TM.Matrix m n → TM.Vec m → List two.Two
  bwd-bits {m} {n} M outsel = bits-of n (consumes M outsel)

  render-fwd : ∀ {m n} → TM.Matrix m n → TM.Vec n → String
  render-fwd M sel = render-row δ-out (fwd-bits M sel)

  render-in : List two.Two → String
  render-in bits = render-row γ-nums-val bits

  render-out : List two.Two → String
  render-out bits = render-row δ-out bits

contents : String
contents =
  "list-query\n" ++ slice dep ++
  "const\n" ++ slice dep-const ++
  "length\n" ++ slice dep-length ++
  "fold0\n" ++ slice dep-fold0 ++
  "case0\n" ++ slice dep-case0 ++
  "tag\n" ++ slice dep-tag ++
  "map-backward\n" ++ slice-over γ-nums-val dep-map ++
  "map-erase-cell1\n" ++ render-fwd dep-map (sel-of cell1-sel) ++ "\n" ++
  "map-query-cell2\n" ++
    show-aval out-cell2-sel ++ "\n" ++
    render-in (bwd-bits dep-map (sel-of out-cell2-sel)) ++ "\n" ++
    render-out (fwd-bits dep-map (vec-of (bwd-bits dep-map (sel-of out-cell2-sel)))) ++ "\n"

main : Main
main = run (writeFile "test-baselines/slices.txt" contents)
