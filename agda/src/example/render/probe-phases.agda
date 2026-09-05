{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- Phase timings for the filter-sum stage-table pipeline: trace markers on stderr bracket each read, so
-- the gaps between marker arrival times give the phase costs. Run from approx-diff repository root.
module example.render.probe-phases where

open import IO
open import IO.Finite using (putStrLn)
open import Data.List using (List; []; _∷_; map; length; concat)
open import Data.Nat using (ℕ)
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
  show3 O = "O"
  show3 C = "C"
  show3 D = "D"

  join-list : List Three → Three
  join-list []       = O
  join-list (t ∷ ts) = t three.⊔ join-list ts

  join : ∀ {m n} → M3.Matrix m n → Three
  join M = join-list (concat (toList (tabulate λ i → toList (tabulate λ j → M i j))))

  open Evaluated (env filter-sum-run) (term filter-sum-run)

  ts : Tables dependence
  ts = first-order-tables dependence

  fo = tabulated-first-order dependence ts

  open Interaction dependence fo using (entry)

  env-v root-v filtered-v : V dependence
  env-v      = inj₁ input
  root-v     = inj₂ ε
  filtered-v = inj₂ (into (there here) ε)

  mk : String → Three → String → String
  mk k v r = trace ("phase " ++ k) (show3 v ++ " " ++ r)

  out : String
  out =
    trace ("phase 0: FO " ++ ℕ-Show.show (length (FO dependence))
           ++ ", hidden " ++ ℕ-Show.show (length (fo-hidden dependence)))
      (mk "1: fo env->root" (join (entry env-v root-v (fo env-v root-v)))
        (mk "2: fo env->root repeat" (join (entry env-v root-v (fo env-v root-v)))
          (mk "3: fo filtered->root" (join (entry filtered-v root-v (fo filtered-v root-v)))
            (mk "4: region summary env->root"
              (join (entry env-v root-v (tabulated-summary dependence fo (FO dependence) env-v root-v)))
              "end"))))

main : Main
main = run (putStrLn out)
