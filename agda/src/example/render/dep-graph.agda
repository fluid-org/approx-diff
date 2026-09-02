{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- Run from approx-diff repository root.
module example.render.dep-graph where

open import IO
open import IO.Finite using (writeFile)
open import Data.List using (List; []; _∷_; map; concat; foldl; length; applyUpTo)
  renaming (_++_ to _++L_)
open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _+_; _≡ᵇ_)
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
open import interaction.moves three.semiring (λ x → three.∨-idem {x}) three.≡-of-≈ three.ε?
open import matrix-embedding three.semiring using (𝔽)
open import Relation.Binary.PropositionalEquality using (_≡_)
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

  any-three : List Three → Bool
  any-three []       = false
  any-three (O ∷ ts) = any-three ts
  any-three (t ∷ ts) = true

  ll-any : LL → Bool
  ll-any []           = false
  ll-any (row ∷ rows) = if any-three row then true else ll-any rows

  zip-⊔ : List Three → List Three → List Three
  zip-⊔ []       ys       = ys
  zip-⊔ xs       []       = xs
  zip-⊔ (x ∷ xs) (y ∷ ys) = (x ⊔ y) ∷ zip-⊔ xs ys

  ll-add : LL → LL → LL
  ll-add []       rs'        = rs'
  ll-add rs       []         = rs
  ll-add (r ∷ rs) (r' ∷ rs') = zip-⊔ r r' ∷ ll-add rs rs'

  Edge : Set
  Edge = ℕ × ℕ × LL

  keep : ℕ → ℕ → LL → List Edge
  keep i j B = if ll-any B then (i , j , B) ∷ [] else []

  upsert : ℕ → ℕ → LL → List Edge → List Edge
  upsert x y B [] = (x , y , B) ∷ []
  upsert x y B ((x' , y' , B') ∷ es) =
    if (x ≡ᵇ x') ∧ (y ≡ᵇ y')
    then (x' , y' , ll-add B B') ∷ es
    else (x' , y' , B') ∷ upsert x y B es

  merge : List Edge → List Edge → List Edge
  merge []                 es = es
  merge ((x , y , B) ∷ ns) es = merge ns (upsert x y B es)

  part : ℕ → List Edge → List Edge × List Edge × List Edge
  part r [] = [] , [] , []
  part r ((x , y , B) ∷ es) with part r es
  ... | ins , outs , rest =
    if y ≡ᵇ r then (((x , y , B) ∷ ins) , outs , rest)
    else if x ≡ᵇ r then (ins , ((x , y , B) ∷ outs) , rest)
    else (ins , outs , ((x , y , B) ∷ rest))

  compose-edges : (ℕ → ℕ) → ℕ → List Edge → List Edge → List Edge
  compose-edges wd r ins outs = concat (map (λ ie → map (mk ie) outs) ins)
    where
    mk : Edge → Edge → Edge
    mk (x , _ , Bxr) (_ , y , Bry) =
      x , y , mat-ll (wd y) (wd x) (mul (wd r) (ll-at Bry) (ll-at Bxr))

  elim : (ℕ → ℕ) → List Edge → ℕ → List Edge
  elim wd es r with part r es
  ... | ins , outs , rest = merge (compose-edges wd r ins outs) rest


  number : ∀ {a} {A : Set a} → ℕ → List A → List (ℕ × A)
  number _ []       = []
  number i (x ∷ xs) = (i , x) ∷ number (suc i) xs

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

module render-run (r : Run) where

  open Evaluated (env r) (term r)

  dot : String
  dot = go dependence labels widths free
    where
    go : ∀ {X Y} (G : Graph X Y) → Labelling (Graph.shape G) (Graph.object G) →
         (wdv : V G → ℕ) → (∀ v → vertex-object G v ≡ 𝔽 (wdv v)) → String
    go G lab wdv freev = emit (foldl (elim wdf) edges₀ hid-ix)
      where
      open Interaction G wdv freev using (entry)

      fo-vs : List (V G)
      fo-vs = map (λ p → inj₂ (inj₁ p)) (FO G)

      hid-vs : List (V G)
      hid-vs = map (λ p → inj₂ (inj₁ p)) (fo-hidden G)

      all-vs : List (V G)
      all-vs = (inj₁ input ∷ []) ++L fo-vs ++L hid-vs ++L (inj₂ (inj₂ root) ∷ [])

      nf : ℕ
      nf = length fo-vs

      ws : List ℕ
      ws = map wdv all-vs

      wdf : ℕ → ℕ
      wdf i = nth 0 ws i

      hid-ix : List ℕ
      hid-ix = applyUpTo (λ i → suc (nf + i)) (length hid-vs)

      rows : List (ℕ × V G) → List Edge
      rows []             = []
      rows ((i , x) ∷ is) = cols (number 0 all-vs) ++L rows is
        where
        cols : List (ℕ × V G) → List Edge
        cols []             = []
        cols ((j , y) ∷ js) = keep i j (ll-of (entry x y (gr G x y))) ++L cols js

      edges₀ : List Edge
      edges₀ = rows (number 0 all-vs)

      ivs : List (ℕ × V G)
      ivs = (zero , inj₁ input) ∷ number 1 fo-vs ++L
            ((suc (nf + length hid-vs) , inj₂ (inj₂ root)) ∷ [])

      label-of : V G → String
      label-of (inj₁ input)        = show-env (env r)
      label-of (inj₂ (inj₂ root))  = show-val value
      label-of (inj₂ (inj₁ p))     = node-text (proj₁ (lab .at p))

      node-line : ℕ × V G → String
      node-line (i , x) = "  n" ++ ℕ-Show.show i ++ " [shape=box, fontsize=11, label=\"" ++ label-of x ++ "\"];\n"

      cat : List String → String
      cat []       = ""
      cat (s ∷ ss) = s ++ cat ss

      emit : List Edge → String
      emit es = "digraph G {\n  rankdir=LR;\n" ++ cat (map node-line ivs) ++
                edge-lines es ++ "}\n"

main : Main
main = run (writeFile "dot/map-three.dot" (render-run.dot map-run) >>
            writeFile "dot/filter-three.dot" (render-run.dot filter-run))
