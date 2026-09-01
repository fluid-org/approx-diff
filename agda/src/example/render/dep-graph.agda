{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- Run from approx-diff repository root.
module example.render.dep-graph where

open import IO
open import IO.Finite using (writeFile)
open import Data.List using (List; []; _∷_; map; concat; foldl; length; applyUpTo)
  renaming (_++_ to _++L_)
open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _+_)
import Data.Nat.Show as ℕ-Show
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; _++_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using (toList; tabulate)
import matrix
import three
open three using (Three; O; C; D; _⊔_; _⊓_)
open import semiring-Q using (nonzero)
open import signature.interpretation using (Interpretation)
open import signature.example.interpretation (nonzero three.semiring) three.semiring
  using (Sig; interpretation; sort-val)
open Interpretation interpretation using (sort-vals)
open import example.render.constants (nonzero three.semiring) three.semiring using (show-const)
open import language-operational.evaluation Sig three.semiring interpretation three.C
  using (Env)
open import interaction.graph three.semiring (λ x → three.∨-idem {x})
open import interaction.labelling Sig three.semiring interpretation three.C (λ x → three.∨-idem {x})
open import interaction.evaluated Sig three.semiring interpretation three.C (λ x → three.∨-idem {x})
open import example.runs (nonzero three.semiring) three.semiring three.C
  using (Run; map-run; filter-run; env; term)
open import example.render.tokens using (show-val; show-env)

private
  module M3 = matrix.Mat three.semiring

  -- Blocks materialised as lists so hide steps share entries; function-typed
  -- relations recompute each entry through every enclosing hide step.
  LL : Set
  LL = List (List Three)

  nth : ∀ {a} {A : Set a} → A → List A → ℕ → A
  nth d []       _       = d
  nth d (x ∷ xs) zero    = x
  nth d (x ∷ xs) (suc i) = nth d xs i

  ll-at : LL → ℕ → ℕ → Three
  ll-at rows p q = nth O (nth [] rows p) q

  ll-of : ∀ {m n} → M3.Matrix m n → LL
  ll-of M = toList (tabulate λ p → toList (tabulate λ q → M p q))

  mat-ll : ℕ → ℕ → (ℕ → ℕ → Three) → LL
  mat-ll m n b = applyUpTo (λ p → applyUpTo (b p) n) m

  mul : ℕ → (ℕ → ℕ → Three) → (ℕ → ℕ → Three) → ℕ → ℕ → Three
  mul zero    b c p q = O
  mul (suc s) b c p q = (b p s ⊓ c s q) ⊔ mul s b c p q

  join-list : List Three → Three
  join-list []       = O
  join-list (t ∷ ts) = t ⊔ join-list ts

  ll-join : LL → Three
  ll-join rows = join-list (concat rows)

  Tbl : Set
  Tbl = List (List LL)

  at-t : Tbl → ℕ → ℕ → LL
  at-t T x y = nth [] (nth [] T x) y

  any-three : List Three → Bool
  any-three []       = false
  any-three (O ∷ ts) = any-three ts
  any-three (t ∷ ts) = true

  ll-any : LL → Bool
  ll-any []           = false
  ll-any (row ∷ rows) = if any-three row then true else ll-any rows

  blk-hide : ℕ → ℕ → ℕ → LL → LL → LL → LL
  blk-hide m n k base row col = mat-ll m n (λ p q → ll-at base p q ⊔ mul k (ll-at row) (ll-at col) p q)

  -- Values must flow through applied arguments: module- and where-level definitions
  -- compile to functions of enclosing parameters, re-running per reference.
  hide-tbl : List ℕ → ℕ → Tbl → ℕ → Tbl
  hide-tbl ws N T r =
    go (applyUpTo (λ x → ll-any (at-t T x r)) N) (applyUpTo (λ y → ll-any (at-t T r y)) N)
    where
    go : List Bool → List Bool → Tbl
    go preds succs = applyUpTo (λ x → applyUpTo (λ y →
      if nth false preds x ∧ nth false succs y
      then blk-hide (nth 0 ws y) (nth 0 ws x) (nth 0 ws r) (at-t T x y) (at-t T r y) (at-t T x r)
      else at-t T x y) N) N

  number : ∀ {a} {A : Set a} → ℕ → List A → List (ℕ × A)
  number _ []       = []
  number i (x ∷ xs) = (i , x) ∷ number (suc i) xs

  edge-line : ℕ → ℕ → Three → String
  edge-line i j D = "  n" ++ ℕ-Show.show i ++ " -> n" ++ ℕ-Show.show j ++ " [color=blue];\n"
  edge-line i j C = "  n" ++ ℕ-Show.show i ++ " -> n" ++ ℕ-Show.show j ++ " [style=dashed];\n"
  edge-line i j O = ""

  txt-sort-vals : ∀ {is} → sort-vals is → String
  txt-sort-vals {[]}     _        = "()"
  txt-sort-vals {i ∷ is} (v , vs) = show-const {i} v ++ " " ++ txt-sort-vals {is} vs

  node-text : Node → String
  node-text (val v)        = show-val v
  node-text (vals {is} vs) = txt-sort-vals {is} vs

module render-run (r : Run) where

  open Evaluated (env r) (term r)

  dot : String
  dot = go dependence labels
    where
    go : ∀ {m n} (G : Graph m n) → Labelling (Graph.shape G) (Graph.width G) → String
    go G lab = emit (foldl (hide-tbl ws N) T₀ hid-ix)
      where
      fo-vs : List (V G)
      fo-vs = map (λ p → inj₂ (inj₁ p)) (FO G)

      hid-vs : List (V G)
      hid-vs = map (λ p → inj₂ (inj₁ p)) (fo-hidden G)

      all-vs : List (V G)
      all-vs = (inj₁ input ∷ []) ++L fo-vs ++L hid-vs ++L (inj₂ (inj₂ root) ∷ [])

      nf : ℕ
      nf = length fo-vs

      N : ℕ
      N = length all-vs

      ws : List ℕ
      ws = map (vertex-width G) all-vs

      hid-ix : List ℕ
      hid-ix = applyUpTo (λ i → suc (nf + i)) (length hid-vs)

      T₀ : Tbl
      T₀ = map (λ x → map (λ y → ll-of (gr G x y)) all-vs) all-vs

      ivs : List (ℕ × V G)
      ivs = (zero , inj₁ input) ∷ number 1 fo-vs ++L
            ((suc (nf + length hid-vs) , inj₂ (inj₂ root)) ∷ [])

      label-of : V G → String
      label-of (inj₁ input)        = show-env (env r)
      label-of (inj₂ (inj₂ root))  = show-val value
      label-of (inj₂ (inj₁ p))     = node-text (proj₁ (lab .at p))

      node-line : ℕ × V G → String
      node-line (i , x) = "  n" ++ ℕ-Show.show i ++ " [shape=box, fontsize=11, label=\"" ++ label-of x ++ "\"];\n"

      edges-from : Tbl → ℕ × V G → String
      edges-from T (i , x) = walk ivs
        where
        walk : List (ℕ × V G) → String
        walk []             = ""
        walk ((j , y) ∷ zs) = edge-line i j (ll-join (at-t T i j)) ++ walk zs

      cat : List String → String
      cat []       = ""
      cat (s ∷ ss) = s ++ cat ss

      emit : Tbl → String
      emit T = "digraph G {\n  rankdir=LR;\n" ++ cat (map node-line ivs) ++
               cat (map (edges-from T) ivs) ++ "}\n"

main : Main
main = run (writeFile "dot/map-three.dot" (render-run.dot map-run) >>
            writeFile "dot/filter-three.dot" (render-run.dot filter-run))
