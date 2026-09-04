{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- Run from approx-diff repository root.
module example.render.dep-graph where

open import IO
open import IO.Finite using (writeFile; putStrLn)
open import Data.List using (List; []; _∷_; map; concat; foldl; filterᵇ)
  renaming (_++_ to _++L_)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Bool using (Bool; true; false; not; if_then_else_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Nat using (ℕ; suc)
import Data.Nat.Show as ℕ-Show
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ)
open import Data.String using (String; _++_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using (toList; tabulate)
import matrix
import three
open three using (Three; O; C; D)
open import semiring-Q using (nonzero)
open import signature.interpretation using (Interpretation)
open import signature.example ℚ using (add; mult) renaming (number to number-sort)
open import signature.example.interpretation (nonzero three.semiring) three.semiring
  using (Sig; interpretation; sort-val)
open Interpretation interpretation using (sort-vals)
open import example.render.constants (nonzero three.semiring) three.semiring using (show-const)
open import language-syntax Sig using (_⊢_; var; zero; succ; base; bop; emp) renaming (_,_ to _▸_)
open import language-operational.evaluation Sig three.semiring interpretation three.C
  using (Env; emp; _·_; const)
open import interaction.graph three.semiring (λ x → three.∨-idem {x})
open import interaction.labelling Sig three.semiring interpretation three.C (λ x → three.∨-idem {x})
open import interaction.evaluated Sig three.semiring interpretation three.C (λ x → three.∨-idem {x})
open import interaction.moves three.semiring (λ x → three.∨-idem {x}) three.≡-of-≈ three.ε?
open import example.runs (nonzero three.semiring) three.semiring three.C
  using (Run; map-run; filter-run; env; term)
open import example.render.value-labels (nonzero three.semiring) three.semiring three.C
  using (show-val; show-env)

private
  module M3 = matrix.Mat three.semiring

  LL : Set
  LL = List (List Three)

  ll-of : ∀ {m n} → M3.Matrix m n → LL
  ll-of M = toList (tabulate λ p → toList (tabulate λ q → M p q))

  join-list : List Three → Three
  join-list []       = O
  join-list (t ∷ ts) = t three.⊔ join-list ts

  ll-join : LL → Three
  ll-join rows = join-list (concat rows)

  any-three : List Three → Bool
  any-three []       = false
  any-three (O ∷ ts) = any-three ts
  any-three (t ∷ ts) = true

  ll-any : LL → Bool
  ll-any []           = false
  ll-any (row ∷ rows) = if any-three row then true else ll-any rows

  Edge : Set
  Edge = ℕ × ℕ × LL

  keep : ℕ → ℕ → LL → List Edge
  keep i j B = if ll-any B then (i , j , B) ∷ [] else []

  enumerate : ∀ {a} {A : Set a} → ℕ → List A → List (ℕ × A)
  enumerate _ []       = []
  enumerate i (x ∷ xs) = (i , x) ∷ enumerate (suc i) xs

  edge-line : ℕ → ℕ → Three → String
  edge-line i j D = "  n" ++ ℕ-Show.show i ++ " -> n" ++ ℕ-Show.show j ++ " [color=blue];\n"
  edge-line i j C = "  n" ++ ℕ-Show.show i ++ " -> n" ++ ℕ-Show.show j ++ " [style=dashed];\n"
  edge-line i j O = ""

  edge-lines : List Edge → String
  edge-lines []                 = ""
  edge-lines ((i , j , B) ∷ es) = edge-line i j (ll-join B) ++ edge-lines es

  txt-sort-vals : ∀ {is} → sort-vals is → String
  txt-sort-vals {[]}     _        = "()"
  txt-sort-vals {i ∷ is} (v , vs) = show-const {i} v ++ " " ++ txt-sort-vals {is} vs

  node-text : Node → String
  node-text (val v)        = show-val v
  node-text (vals {is} vs) = txt-sort-vals {is} vs

  cat : List String → String
  cat []       = ""
  cat (s ∷ ss) = s ++ cat ss

-- The visible graph of a configuration: the environment, the visible intermediates, and the root,
-- with each edge the reduced relation between two of them after hiding the rest, computed by one
-- traversal of the raw graph in evaluation order.
module render-eval {Γ τ} (γ : Env Γ) (t : Γ ⊢ τ) where

  open Evaluated γ t public
  open Interaction dependence widths free public

  private
    label-of : V dependence → String
    label-of (inj₁ input)       = show-env γ
    label-of (inj₂ (inj₂ root)) = show-val value
    label-of (inj₂ (inj₁ p))    = node-text (proj₁ (labels .at p))

    node-line : ℕ × V dependence → String
    node-line (i , x) = "  n" ++ ℕ-Show.show i ++ " [shape=box, fontsize=11, label=\"" ++ label-of x ++ "\"];\n"

  visible-edge : V dependence → V dependence → List (V dependence) → LL
  visible-edge a b hid = ll-of (hide-in-evaluation-order dependence widths free hid a b)

  dot-at : Config dependence → String
  dot-at K = "digraph G {\n  rankdir=LR;\n" ++ cat (map node-line nvs) ++ edge-lines (rows nvs) ++ "}\n"
    where
    nvs : List (ℕ × V dependence)
    nvs = enumerate 0 ((inj₁ input ∷ []) ++L map (λ p → inj₂ (inj₁ p)) (K .visible) ++L (inj₂ (inj₂ root) ∷ []))

    hid : List (V dependence)
    hid = map (λ p → inj₂ (inj₁ p))
              (filterᵇ (λ q → not ⌊ q ∈? K .visible ⌋) (vertices (Graph.shape dependence)))

    rows : List (ℕ × V dependence) → List Edge
    rows []             = []
    rows ((i , x) ∷ is) = cols nvs ++L rows is
      where
      cols : List (ℕ × V dependence) → List Edge
      cols []             = []
      cols ((j , y) ∷ js) = keep i j (visible-edge x y hid) ++L cols js

  full : Config dependence
  full = foldl (λ K p → reveal-at p K) initial (FO dependence)

  dot : String
  dot = dot-at full

private
  module map-fig    = render-eval (env map-run) (term map-run)
  module filter-fig = render-eval (env filter-run) (term filter-run)

-- y · (x + y) at (x, y) = (0, 1), with only the sum revealed: the two-way factorisation of the
-- dependence relation through one intermediate.
private
  γ-int : Env ((emp ▸ base number-sort) ▸ base number-sort)
  γ-int = emp · const 0ℚ · const 1ℚ

  t-int : ((emp ▸ base number-sort) ▸ base number-sort) ⊢ base number-sort
  t-int = bop mult (bop add (var zero ∷ var (succ zero) ∷ []) ∷ var zero ∷ [])

  module int-fig = render-eval γ-int t-int

  sum-vertex : Vertex (Graph.shape int-fig.dependence)
  sum-vertex = inj₁ (inj₁ (inj₂ root))

  int-dot : String
  int-dot = int-fig.dot-at (int-fig.reveal-at sum-vertex int-fig.initial)

main : Main
main = run (writeFile "dot/intermediate-three.dot" int-dot >>
            writeFile "dot/filter-three.dot" (filter-fig.dot-at filter-fig.initial) >>
            writeFile "dot/map-three.dot" (map-fig.dot-at map-fig.initial))
