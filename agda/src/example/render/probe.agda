{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- Cost probe for hide-in-evaluation-order: scale numbers for one example, then the traced
-- computation with tick marks on stderr. Run from approx-diff repository root.
module example.render.probe where

open import IO
open import IO.Finite using (putStrLn)
open import Data.List using (List; []; _∷_; map; length; concat)
open import Data.Nat using (ℕ; _+_; _*_)
import Data.Nat.Show as ℕ-Show
open import Data.String using (String; _++_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using (toList; tabulate)
import matrix
import three
open three using (Three; O; C; D)
open import semiring-Q using (nonzero)
open import signature.example.interpretation (nonzero three.semiring) three.semiring
  using (Sig; interpretation)
open import interaction.graph three.semiring (λ x → three.∨-idem {x})
open import interaction.evaluated Sig three.semiring interpretation three.C (λ x → three.∨-idem {x})
open import example.runs (nonzero three.semiring) three.semiring three.C
  using (Run; merge-run; env; term)

{-# FOREIGN GHC import qualified Debug.Trace #-}
{-# FOREIGN GHC import qualified Data.Text #-}
postulate trace : {A : Set} → String → A → A
{-# COMPILE GHC trace = \_ s x -> Debug.Trace.trace (Data.Text.unpack s) x #-}

private
  module M3 = matrix.Mat three.semiring

  show3 : Three → String
  show3 O = "O"
  show3 C = "C"
  show3 D = "D"

  join-list : List Three → Three
  join-list []       = O
  join-list (t ∷ ts) = t three.⊔ join-list ts

  join : ∀ {m n} → M3.Matrix m n → Three
  join M = join-list (concat (toList (tabulate λ i → toList (tabulate λ j → M i j))))

  sum : List ℕ → ℕ
  sum []       = 0
  sum (n ∷ ns) = n + sum ns

  -- Basis reads over ordered pairs: each pair (u, v) with u before v costs wd u * wd v.
  volume : List ℕ → ℕ
  volume []       = 0
  volume (w ∷ ws) = w * sum ws + volume ws

  module pm where
    open Evaluated (env merge-run) (term merge-run) public

    hid : List (V dependence)
    hid = map (λ v → inj₂ (inj₁ v)) (vertices (Graph.shape dependence))

main : Main
main = run (putStrLn ("vertices: " ++ ℕ-Show.show (length pm.hid)) >>
            putStrLn ("total width: " ++ ℕ-Show.show (sum ws)) >>
            putStrLn ("pair read volume: " ++ ℕ-Show.show (volume ws)) >>
            putStrLn ("result: " ++ show3 (join R)))
  where
  ws : List ℕ
  ws = map pm.widths pm.hid

  R = Instrumented.hide-in-evaluation-order pm.dependence pm.widths pm.free trace
        pm.hid (inj₁ input) (inj₂ (inj₂ root))
