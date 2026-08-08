{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- Rows are the readback matrices of the dependency tables, presented over the operational values
-- as annotated values: each position carries its own scalar, top by default and ⊥ where a position
-- is dropped. A token with two positions (a list cell's tag and pair, nil's tag and unit) carries
-- both marks in that order, · holding a top slot when only one is dropped. Run from the
-- approx-diff repository root.
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
import label
open import primitives using (Primitives)
import example.primitives as EP
open import example.runs
  using (dep; dep-const; dep-length; dep-fold0; dep-case0; dep-tag; dep-map)

open import language-syntax EP.Sig using (type; base; list; unit; μ; var; _[×]_; _[+]_)
open import language-operational.evaluation EP.Sig EP.primitives using (Val)
open Val
import language-operational.annotated-value
module AV = language-operational.annotated-value EP.Sig EP.primitives
open AV.annotate two.semiring
  using (AVal; unit*; const*; inl*; inr*; pair*; clo*; roll*; aval)
open import language-operational.list-value EP.Sig EP.primitives using (_∷ᵥ_; nilᵥ)
open Primitives EP.primitives using (sort-val; sort-width)

private
  module TM = matrix.Mat two.semiring

-- The operational input value mirroring γ-input: three entries, two under the queried label.
elemT : type 0
elemT = base EP.label [×] base EP.number

listT : type 0
listT = list elemT

el : label.label → ℚ → Val elemT
el l n = pair (const l) (const n)

γ-val : Val listT
γ-val = el label.a 0ℚ ∷ᵥ el label.b 1ℚ ∷ᵥ el label.a 1ℚ ∷ᵥ nilᵥ

-- Renderings of the example constants.
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

  mark2 : two.Two → two.Two → String
  mark2 two.I two.I = ""
  mark2 two.I two.O = "·⊥"
  mark2 two.O two.I = "⊥·"
  mark2 two.O two.O = "⊥⊥"

  marks : ∀ {n} → TM.Vec n → String
  marks {zero}  w = ""
  marks {suc n} w = mark (w Fin.zero) ++ marks {n} (λ i → w (Fin.suc i))

  -- A constant of width zero has no positions and nothing to select, so it renders as absent.
  show-c : (n : ℕ) → String → TM.Vec n → String
  show-c zero    s w = "_"
  show-c (suc n) s w = s ++ marks w

  mutual
    show-aval : ∀ {τ} {v : Val τ} → AVal v → String
    show-aval {μ (unit [+] (_ [×] var Fin.zero))} p = show-alist p
    show-aval (unit* a)                  = "()" ++ mark a
    show-aval (const* {s = s} {c = c} w) = show-c (sort-width s) (showC {s} c) w
    show-aval (inl* a p)                 = "inl" ++ mark a ++ " " ++ show-aval p
    show-aval (inr* a p)                 = "inr" ++ mark a ++ " " ++ show-aval p
    show-aval (pair* a p q)              =
      "(" ++ show-aval p ++ ", " ++ show-aval q ++ ")" ++ mark a
    show-aval (clo* a ρ)                 = "<closure>" ++ mark a
    show-aval (roll* p)                  = show-aval p

    show-alist : ∀ {σ} {v : Val (μ (unit [+] (σ [×] var Fin.zero)))} → AVal v → String
    show-alist (roll* (inl* a (unit* b)))     = "[]" ++ mark2 a b
    show-alist (roll* (inr* a (pair* b h t))) =
      show-aval h ++ " ∷" ++ mark2 a b ++ " " ++ show-alist t

  lookupO : List two.Two → ℕ → two.Two
  lookupO []       _       = two.O
  lookupO (b ∷ _)  zero    = b
  lookupO (_ ∷ bs) (suc n) = lookupO bs n

  -- A matrix row, read over the operational value through a length-safe lookup; the two layouts
  -- agree positionwise, and a misalignment would surface in the rendered baseline.
  render-row : ∀ {τ} (v : Val τ) → List two.Two → String
  render-row v bits = show-aval (aval v (lookupO bits))

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
  and2 or2 not2 : two.Two → two.Two → two.Two
  and2 two.I b = b
  and2 two.O _ = two.O
  or2 two.O b = b
  or2 two.I _ = two.I
  not2 two.I _ = two.O
  not2 two.O _ = two.I

  -- Row containment: every consumed position of the row is available in the selection.
  contained : List two.Two → List two.Two → two.Two
  contained []       _        = two.I
  contained (r ∷ rs) []       = and2 (not2 r two.O) (contained rs [])
  contained (r ∷ rs) (b ∷ bs) = and2 (or2 (not2 r two.O) b) (contained rs bs)

  -- The forward slice of an input selection: the output positions whose whole row it contains,
  -- rendered over the output value.
  meets : List two.Two → List two.Two → two.Two
  meets []       _        = two.O
  meets (_ ∷ _)  []       = two.O
  meets (r ∷ rs) (b ∷ bs) = or2 (and2 r b) (meets rs bs)

  fwd-bits : ∀ {m n} → TM.Matrix m n → List two.Two → List two.Two
  fwd-bits {m} M sel = toList (tabulate {n = m} (λ q → meets (toList (tabulate (M q))) sel))

  render-fwd : ∀ {m n} → TM.Matrix m n → List two.Two → String
  render-fwd M sel = render-row δ-out (fwd-bits M sel)

  -- The first input cons cell, without its element.
  cell1-sel : List two.Two
  cell1-sel = two.I ∷ two.I ∷ two.O ∷ two.O ∷ two.O ∷ two.O ∷ two.O ∷ two.O
            ∷ two.O ∷ two.O ∷ two.O ∷ []

  out-cell2-sel : List two.Two
  out-cell2-sel = two.O ∷ two.O ∷ two.O ∷ two.I ∷ two.I ∷ two.O ∷ two.O ∷ two.O
                ∷ two.O ∷ two.O ∷ two.O ∷ []

  -- The backward slice of an output selection: the join of the selected positions' rows.
  bwd-bits : ∀ {m n} → TM.Matrix m n → List two.Two → List two.Two
  bwd-bits {m} M outsel =
    foldrL orL (toList (tabulate {n = m} (λ _ → two.O)))
      (zipsel (toList (tabulate {n = m} (λ q → toList (tabulate (M q))))) outsel)
    where
    orL : List two.Two → List two.Two → List two.Two
    orL []       ys       = ys
    orL xs       []       = xs
    orL (x ∷ xs) (y ∷ ys) = or2 x y ∷ orL xs ys
    zipsel : List (List two.Two) → List two.Two → List (List two.Two)
    zipsel []         _              = []
    zipsel (_ ∷ rs)   []             = []
    zipsel (r ∷ rs)   (two.I ∷ bs)   = r ∷ zipsel rs bs
    zipsel (r ∷ rs)   (two.O ∷ bs)   = zipsel rs bs

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
  "map-forward-cell1\n" ++ render-fwd dep-map cell1-sel ++ "\n" ++
  "map-roundtrip-cell2\n" ++
    render-out out-cell2-sel ++ "\n" ++
    render-in (bwd-bits dep-map out-cell2-sel) ++ "\n" ++
    render-out (fwd-bits dep-map (bwd-bits dep-map out-cell2-sel)) ++ "\n"

main : Main
main = run (writeFile "test-baselines/slices.txt" contents)
