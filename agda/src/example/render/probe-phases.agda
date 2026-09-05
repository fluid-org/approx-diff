{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- Phase timings for the filter-sum stage-table pipeline: trace markers on stderr bracket each read, so
-- the gaps between marker arrival times give the phase costs. Run from approx-diff repository root.
module example.render.probe-phases where

open import IO
open import IO.Finite using (putStrLn)
open import Data.Bool using (not)
open import Data.List using (List; []; _∷_; map; length; concat; filterᵇ; upTo)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Nat using (ℕ; suc; _≡ᵇ_)
import Data.Nat.Show as ℕ-Show
open import Data.String using (String; _++_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using (toList; tabulate)
import matrix
import three
open three using (Three)
open import semiring-Q using (nonzero)
open import signature.example.interpretation (nonzero three.semiring) three.semiring
  using (Sig; interpretation)
open import interaction.graph three.semiring (λ x → three.∨-idem {x})
open import interaction.evaluated Sig three.semiring interpretation three.C (λ x → three.∨-idem {x})
open import interaction.moves three.semiring (λ x → three.∨-idem {x}) three.≡-of-≈ three.ε?
  using (module Interaction; tabulated-summary; first-order-tables; tabulated-first-order; Tables)
open import example.runs (nonzero three.semiring) three.semiring three.C
  using (filter-sum-run; env; term)

{-# FOREIGN GHC import qualified Debug.Trace #-}
{-# FOREIGN GHC import qualified Data.Text #-}
postulate trace : {A : Set} → String → A → A
{-# COMPILE GHC trace = \_ s x -> Debug.Trace.trace (Data.Text.unpack s) x #-}

private
  module M3 = matrix.Mat three.semiring

  show3 : Three → String
  show3 three.O = "O"
  show3 three.C = "C"
  show3 three.D = "D"

  join-list : List Three → Three
  join-list []       = three.O
  join-list (t ∷ ts) = t three.⊔ join-list ts

  join : ∀ {m n} → M3.Matrix m n → Three
  join M = join-list (concat (toList (tabulate λ i → toList (tabulate λ j → M i j))))

  open Evaluated (env filter-sum-run) (term filter-sum-run)

  ts : Tables dependence
  ts = first-order-tables dependence (λ _ x → x)

  fo = tabulated-first-order dependence (λ _ x → x) ts

  open Interaction dependence fo using (entry)

  env-v root-v filtered-v : V dependence
  env-v      = inj₁ input
  root-v     = inj₂ ε
  filtered-v = inj₂ (into (there here) ε)

  mk : String → Three → String → String
  mk k v r = trace ("phase " ++ k) (show3 v ++ " " ++ r)

  T5 : Tabulation
  T5 = tabulation dependence three.ε? trace

  interior-indices : List ℕ
  interior-indices = map suc (upTo (length (vertices D)))

  root-index : ℕ
  root-index = suc (length (vertices D))

  join-table : M3.Table → Three
  join-table t = join-list (concat t)

  filtered-index : ℕ
  filtered-index = index-of dependence filtered-v

  full-hide partial-hide : Tabulation
  full-hide    = TabulatedHide.hide-graph T5 trace three.ε? interior-indices
  partial-hide = TabulatedHide.hide-graph T5 trace three.ε?
                   (filterᵇ (λ i → not (i ≡ᵇ filtered-index)) interior-indices)

  ask : Tabulation → ℕ → Three
  ask H v with position H 0 | position H v
  ... | just p | just q = join-table (read-table H p q)
  ... | _      | _      = three.O

  ts8 : Tables dependence
  ts8 = first-order-tables dependence trace

  fo8 = tabulated-first-order dependence trace ts8

  module I8 = Interaction dependence fo8

  consult : List (V dependence × V dependence) → Three
  consult []             = three.O
  consult ((x , y) ∷ es) = join (I8.entry x y (fo8 x y)) three.⊔ consult es

  out : String
  out =
    trace ("phase 0: FO " ++ ℕ-Show.show (length (FO dependence))
           ++ ", hidden " ++ ℕ-Show.show (length (fo-hidden dependence)))
      (mk "5: full hide, edge to root" (ask full-hide root-index)
        (mk "6: partial hide, edge to filtered vertex" (ask partial-hide filtered-index)
          (mk "7: same partial hide, edge to root" (ask partial-hide root-index)
            (mk "8: first-order graph, two edges" (consult ((env-v , root-v) ∷ (env-v , filtered-v) ∷ []))
              (mk "9: same two edges, reversed" (consult ((env-v , filtered-v) ∷ (env-v , root-v) ∷ []))
                "end")))))

main : Main
main = run (putStrLn out)
