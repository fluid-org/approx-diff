{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- Writes the dependency slices as partial values of the input list, one line per output position,
-- compared against a versioned baseline; run from the paper repository root. Rows are read from
-- the same readback matrices as the bit tables and interpreted over the operational value fibre,
-- which agrees with the model fibre positionwise; the fixedness witness comes from spine closure,
-- the identity on these rows, until the row-fixedness of absorbed presentations replaces it.
module graph-viz.dump-slices where

open import IO
open import IO.Finite using (writeFile)
open import Data.String using (String; _++_)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.List using (List; []; _∷_) renaming (foldr to foldrL)
open import Data.Nat using (ℕ; zero; suc)
import Data.Integer as ℤ
open import Data.Fin using (Fin; toℕ)
open import Data.Vec using (Vec; toList; tabulate)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; ↥_; ↧_) renaming (_+_ to _+ℚ_)
import Data.Integer.Show as ℤ-Show
open import Level using (0ℓ)
import two
import matrix
import label
open import primitives using (Primitives)
import example.primitives as EP
open import example.rooted-runs
  using (dep; dep-const; dep-length; dep-fold0; dep-case0; dep-tag; dep-map)

open import language-syntax EP.Sig using (type; base; list; _[×]_)
open import language-operational.evaluation EP.Sig EP.primitives using (Val)
open Val
open import language-operational.value-fibre EP.Sig EP.primitives using (pos)
open import language-operational.partial-value EP.Sig EP.primitives using (spine-close; pval)
open import language-operational.render-partial EP.Sig EP.primitives
open Primitives EP.primitives using (sort-val)

private
  module TM = matrix.Mat two.semiring

-- The operational input value mirroring γ-input: three entries, two under the queried label.
elemT : type 0
elemT = base EP.label [×] base EP.number

listT : type 0
listT = list elemT

el : label.label → ℚ → Val elemT
el l n = pair (const l) (const n)

infixr 20 _∷ᵥ_
_∷ᵥ_ : Val elemT → Val listT → Val listT
x ∷ᵥ xs = roll (inr (pair x xs))

nilᵥ : Val listT
nilᵥ = roll (inl unit)

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
  lookupO : List two.Two → ℕ → two.Two
  lookupO []       _       = two.O
  lookupO (b ∷ _)  zero    = b
  lookupO (_ ∷ bs) (suc n) = lookupO bs n

  -- A matrix row, read over the operational fibre through a length-safe lookup; the two layouts
  -- agree positionwise, and a misalignment would surface in the rendered baseline.
  render-row : ∀ {τ} (v : Val τ) → List two.Two → String
  render-row v bits =
    show-pval (λ {s} c → showC {s} c)
      (pval v (spine-close (pos v) (λ i → lookupO bits (toℕ i))))

  slice-over : ∀ {τ} (v : Val τ) {m n} → TM.Matrix m n → String
  slice-over v {m} M =
    foldrL (λ r s → r ++ "\n" ++ s) ""
      (toList (tabulate {n = m} (λ q → render-row v (toList (tabulate (M q))))))

  slice : ∀ {m n} → TM.Matrix m n → String
  slice = slice-over γ-val

numlistT : type 0
numlistT = list (base EP.number)

infixr 20 _∷ⁿ_
_∷ⁿ_ : Val (base EP.number) → Val numlistT → Val numlistT
x ∷ⁿ xs = roll (inr (pair x xs))

nilⁿ : Val numlistT
nilⁿ = roll (inl unit)

γ-nums-val : Val numlistT
γ-nums-val = const 0ℚ ∷ⁿ const 1ℚ ∷ⁿ const (1ℚ +ℚ 1ℚ) ∷ⁿ nilⁿ

δ-out : Val numlistT
δ-out = const (0ℚ +ℚ 1ℚ) ∷ⁿ const (1ℚ +ℚ 1ℚ) ∷ⁿ const ((1ℚ +ℚ 1ℚ) +ℚ 1ℚ) ∷ⁿ nilⁿ

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
  render-fwd {m} M sel =
    show-pval (λ {s} c → showC {s} c)
      (pval δ-out (spine-close (pos δ-out) (λ i → lookupO (fwd-bits M sel) (toℕ i))))

  -- The first input cons cell, without its element.
  cell1-sel : List two.Two
  cell1-sel = two.I ∷ two.I ∷ two.O ∷ two.O ∷ two.O ∷ two.O ∷ two.O ∷ two.O
            ∷ two.O ∷ two.O ∷ two.O ∷ []

  -- Output element 2 as a selection: its scalar and the spine above it.
  out-elem2-sel : List two.Two
  out-elem2-sel = two.I ∷ two.I ∷ two.O ∷ two.I ∷ two.I ∷ two.I ∷ two.O ∷ two.O
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
  "map-roundtrip-elem2\n" ++
    render-out out-elem2-sel ++ "\n" ++
    render-in (bwd-bits dep-map out-elem2-sel) ++ "\n" ++
    render-out (fwd-bits dep-map (bwd-bits dep-map out-elem2-sel)) ++ "\n" 

main : Main
main = run (writeFile "approx-diff/test-baselines/rooted-slices.txt" contents)
