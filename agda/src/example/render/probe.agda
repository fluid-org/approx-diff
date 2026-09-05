{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- Cost probes for hide-in-evaluation-order, reporting through the trace postulate on stderr so a
-- killed run loses nothing. Scale survey across examples, then scaling curve on merge prefixes.
-- Run from approx-diff repository root.
module example.render.probe where

open import IO
open import IO.Finite using (putStrLn)
open import Data.List using (List; []; _∷_; map; length; concat; upTo)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _⊔_)
import Data.Nat.Show as ℕ-Show
open import Data.String using (String; _++_)
open import Data.Sum using (inj₁; inj₂)
import matrix
import three
open three using (Three)
open import semiring-Q using (nonzero)
open import signature.example.interpretation (nonzero three.semiring) three.semiring
  using (Sig; interpretation)
open import interaction.graph three.semiring (λ x → three.∨-idem {x})
open import interaction.evaluated Sig three.semiring interpretation three.C (λ x → three.∨-idem {x})
open import example.runs (nonzero three.semiring) three.semiring three.C
  using (Run; filter-sum-run; map-run; filter-run; merge-run; env; term)

{-# FOREIGN GHC import qualified Debug.Trace #-}
{-# FOREIGN GHC import qualified Data.Text #-}
postulate trace : {A : Set} → String → A → A
{-# COMPILE GHC trace = \_ s x -> Debug.Trace.trace (Data.Text.unpack s) x #-}

private
  module M3 = matrix.Mat three.semiring

  show : ℕ → String
  show = ℕ-Show.show

  show3 : Three → String
  show3 three.O = "O"
  show3 three.C = "C"
  show3 three.D = "D"

  join-list : List Three → Three
  join-list []       = three.O
  join-list (t ∷ ts) = t three.⊔ join-list ts

  sum : List ℕ → ℕ
  sum []       = 0
  sum (n ∷ ns) = n + sum ns

  max : List ℕ → ℕ
  max []       = 0
  max (n ∷ ns) = n ⊔ max ns

  count : (ℕ → ℕ) → List ℕ → ℕ
  count f ns = sum (map f ns)

  is0 is1 is2 big : ℕ → ℕ
  is0 zero = 1
  is0 _    = 0
  is1 (suc zero) = 1
  is1 _          = 0
  is2 (suc (suc zero)) = 1
  is2 _                = 0
  big (suc (suc (suc _))) = 1
  big _                   = 0

  module scale (name : String) (r : Run) where
    open Evaluated (env r) (term r)

    hid : List (V dependence)
    hid = map inj₂ (vertices D)

    ws : List ℕ
    ws = map (vertex-width dependence) hid

    line : String
    line = name ++ ": " ++ show (length hid) ++ " vertices, width sum " ++ show (sum ws)
           ++ ", max " ++ show (max ws)
           ++ ", widths 0/1/2/3+: " ++ show (count is0 ws) ++ "/" ++ show (count is1 ws)
           ++ "/" ++ show (count is2 ws) ++ "/" ++ show (count big ws)

  module bench where
    open Evaluated (env merge-run) (term merge-run)

    T : Tabulation
    T = tabulation dependence three.ε? trace

    root-index : ℕ
    root-index = suc (length (vertices D))

    join-table : M3.Table → Three
    join-table t = join-list (concat t)

    at : ℕ → String
    at k = show3 (join-table (TabulatedHide.hide-table T (λ _ x → x) (map suc (upTo k)) 0 root-index))

  survey : String
  survey = scale.line "filter-sum" filter-sum-run ++ "\n" ++ scale.line "map" map-run ++ "\n"
           ++ scale.line "filter" filter-run ++ "\n" ++ scale.line "merge" merge-run

  curve : List ℕ → ℕ
  curve []       = 0
  curve (k ∷ ks) = trace ("k=" ++ show k ++ " -> " ++ bench.at k) (curve ks)

main : Main
main = run (putStrLn (trace survey (show (curve (5 ∷ [])))))
