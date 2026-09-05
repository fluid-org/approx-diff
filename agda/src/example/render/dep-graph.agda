{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- Run from approx-diff repository root.
module example.render.dep-graph where

open import IO
open import IO.Finite using (writeFile; putStrLn)
open import Data.List using (List; []; _∷_; map; concat; foldl; filterᵇ; length)
  renaming (_++_ to _++L_)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Bool using (Bool; true; false; not; if_then_else_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc)
import Data.Nat.Show as ℕ-Show
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ)
open import Data.String using (String; _++_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using (toList; tabulate)
import matrix
import three
open three using (Three)
open import semiring-Q using (nonzero)
open import signature.example ℚ using (add; mult) renaming (number to number-sort)
open import signature.example.interpretation (nonzero three.semiring) three.semiring
  using (Sig; interpretation)
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

  join-list : List Three → Three
  join-list []       = three.O
  join-list (t ∷ ts) = t three.⊔ join-list ts

  table-join : M3.Table → Three
  table-join rows = join-list (concat rows)

  any-three : List Three → Bool
  any-three []             = false
  any-three (three.O ∷ ts) = any-three ts
  any-three (t ∷ ts)       = true

  table-any : M3.Table → Bool
  table-any []           = false
  table-any (row ∷ rows) = if any-three row then true else table-any rows

  Edge : Set
  Edge = ℕ × ℕ × M3.Table

  keep : ℕ → ℕ → M3.Table → List Edge
  keep i j B = if table-any B then (i , j , B) ∷ [] else []

  enumerate : ∀ {a} {A : Set a} → ℕ → List A → List (ℕ × A)
  enumerate _ []       = []
  enumerate i (x ∷ xs) = (i , x) ∷ enumerate (suc i) xs

  edge-line : ℕ → ℕ → Three → String
  edge-line i j three.D = "  n" ++ ℕ-Show.show i ++ " -> n" ++ ℕ-Show.show j ++ " [color=blue];\n"
  edge-line i j three.C = "  n" ++ ℕ-Show.show i ++ " -> n" ++ ℕ-Show.show j ++ " [style=dashed];\n"
  edge-line i j three.O = ""

  edge-lines : List Edge → String
  edge-lines []                 = ""
  edge-lines ((i , j , B) ∷ es) = edge-line i j (table-join B) ++ edge-lines es

  node-text : Node → String
  node-text (val v) = show-val v

  cat : List String → String
  cat []       = ""
  cat (s ∷ ss) = s ++ cat ss

-- The visible graph of a configuration: the environment, the visible intermediates, and the root,
-- with each edge the reduced relation between two of them after hiding the rest, computed by one
-- traversal of the raw graph in evaluation order.
module render-eval {Γ τ} (γ : Env Γ) (t : Γ ⊢ τ) where

  open Evaluated γ t public

  first-order = first-order-edges dependence (λ _ x → x)
  summarise   = tabulated-summary dependence (λ _ x → x) first-order

  open Interaction dependence first-order public

  private
    label-of : V dependence → String
    label-of (inj₁ input) = show-env γ
    label-of (inj₂ p)     = node-text (proj₁ (labels .at p))

    node-line : ℕ × ℕ × V dependence → String
    node-line (i , _ , x) = "  n" ++ ℕ-Show.show i ++ " [shape=box, fontsize=11, label=\"" ++ label-of x ++ "\"];\n"

    T : Tabulation
    T = tabulation dependence three.ε? (λ _ x → x)

  dot-at : Config dependence → String
  dot-at K = "digraph G {\n  rankdir=LR;\n" ++ cat (map node-line nvs) ++ edge-lines (rows nvs) ++ "}\n"
    where
    endpoints : List (ℕ × V dependence)
    endpoints = (0 , inj₁ input) ∷ map (λ p → index-of dependence (inj₂ p) , inj₂ p) (K .visible)
                ++L ((suc (length (vertices D)) , inj₂ ε) ∷ [])

    nvs : List (ℕ × ℕ × V dependence)
    nvs = enumerate 0 endpoints

    hid : List ℕ
    hid = map proj₁ (filterᵇ (λ iq → not ⌊ proj₂ iq ∈? K .visible ⌋) (enumerate 1 (vertices D)))

    H : Tabulation
    H = TabulatedHide.hide-graph T (λ _ x → x) three.ε? hid

    visible-edge : ℕ → ℕ → M3.Table
    visible-edge a b = go (position H a) (position H b)
      where
      go : Maybe ℕ → Maybe ℕ → M3.Table
      go (just p) (just q) = read-table H p q
      go _        _        = []

    rows : List (ℕ × ℕ × V dependence) → List Edge
    rows []                 = []
    rows ((i , gx , x) ∷ is) = cols nvs ++L rows is
      where
      cols : List (ℕ × ℕ × V dependence) → List Edge
      cols []                 = []
      cols ((j , gy , y) ∷ js) = keep i j (visible-edge gx gy) ++L cols js

  full : Config dependence
  full = foldl (λ K p → reveal-at summarise p K) (initial summarise) (FO dependence)

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

  sum-vertex : Path int-fig.D
  sum-vertex = into here ε

  int-dot : String
  int-dot = int-fig.dot-at (int-fig.reveal-at int-fig.summarise sum-vertex
              (int-fig.initial int-fig.summarise))

main : Main
main = run (writeFile "dot/intermediate-three.dot" int-dot >>
            writeFile "dot/filter-three.dot"
              (filter-fig.dot-at (filter-fig.initial filter-fig.summarise)) >>
            writeFile "dot/map-three.dot"
              (map-fig.dot-at (map-fig.initial map-fig.summarise)))
