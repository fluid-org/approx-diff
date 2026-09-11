{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- Cost probes for the hiding pass, reporting through the trace postulate on stderr so a
-- killed run loses nothing. Scale survey across examples, then scaling curve on merge prefixes.
-- Run from approx-diff repository root.
module example.render.probe where

open import IO
open import IO.Finite using (putStrLn)
open import Data.List using (List; []; _∷_; map; length; concat; take; upTo)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _⊔_)
open import Data.Product using (_×_; _,_; proj₂)
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
open import interaction.moves three.semiring (λ x → three.∨-idem {x}) three.≡-of-≈ three.ε?
  using (module Interaction; first-order-graph)
open import interaction.components
  using (by-pairs; components; components-on; induced; symmetric; thin)
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
           ++ ", inputs width " ++ show (vertex-width dependence (inj₁ input))
           ++ ", max " ++ show (max ws)
           ++ ", widths 0/1/2/3+: " ++ show (count is0 ws) ++ "/" ++ show (count is1 ws)
           ++ "/" ++ show (count is2 ws) ++ "/" ++ show (count big ws)

  -- Strict in both arguments, so joining forces every entry.
  join! : Three → Three → Three
  join! three.O y       = y
  join! three.C three.O = three.C
  join! three.C three.C = three.C
  join! three.C three.D = three.D
  join! three.D three.O = three.D
  join! three.D three.C = three.D
  join! three.D three.D = three.D

  join-weights : List (ℕ × Three) → Three
  join-weights []            = three.O
  join-weights ((_ , w) ∷ ws) = join! w (join-weights ws)

  join-positions : List (List (ℕ × Three)) → Three
  join-positions []       = three.O
  join-positions (P ∷ Ps) = join! (join-weights P) (join-positions Ps)

  module bench (r : Run) where
    open Evaluated (env r) (term r)

    all-positions : ℕ → String
    all-positions k =
      show3 (hide-graph-reachability dependence three.ε? trace (map suc (upTo k))
               (λ a c → join! a (join-positions (proj₂ c))) three.O)

    fo-positions : List ℕ
    fo-positions = map (λ p → suc (path-position D p)) (fo-hidden dependence)

    fo-count : String
    fo-count = show (length fo-positions)

    fo-reachability : String
    fo-reachability =
      show3 (hide-graph-reachability dependence three.ε? trace fo-positions
               (λ a c → join! a (join-positions (proj₂ c))) three.O)

  -- Every adjacency question the fold asks reads a stored edge, so the position-edge marks between
  -- one prefix's begin line and its result count the questions. A prefix repeated in the curve is
  -- timed a second time against whatever the first left built.
  module region-fold (r : Run) where
    open Evaluated (env r) (term r)

    private
      first-order = first-order-graph dependence (λ _ x → x)
      rels = dep-rels-of dependence three.ε? trace
      adjacent = adjacent-at dependence three.≡-of-≈ three.ε? trace
      module I = Interaction dependence (rels first-order) (adjacent first-order)

    sizes : ℕ → String
    sizes k = show (length blocks) ++ " regions over " ++ show (sum (map length blocks)) ++ " hidden"
      where blocks = I.regions (take k (FO dependence))

    traversed : ℕ → String
    traversed k =
      show (length cc) ++ " components over " ++ show (sum (map length cc)) ++ " visible, "
      ++ show (sum (map length ss)) ++ " endpoints"
      where
      ss = induced k (symmetric (graph-sources dependence first-order))
      cc = components ss

    split : ℕ → String
    split n =
      show (length cc) ++ " components, " ++ show (length bb) ++ " blocks over "
      ++ show (sum (map length cc)) ++ " and " ++ show (sum (map length bb)) ++ " of "
      ++ show (length ws) ++ " kept"
      where
      ss = symmetric (graph-sources dependence first-order)
      ws = thin n (length ss)
      cc = components-on ws ss
      bb = by-pairs ss ws

  survey : String
  survey = scale.line "filter-sum" filter-sum-run ++ "\n" ++ scale.line "map" map-run ++ "\n"
           ++ scale.line "filter" filter-run ++ "\n" ++ scale.line "merge" merge-run

  -- The result threads through the continuation, so unused-argument erasure cannot drop the
  -- chain ahead of it.
  curve : String → (ℕ → String) → List ℕ → ℕ → ℕ
  curve name f []       r = r
  curve name f (k ∷ ks) r =
    trace ("begin " ++ name ++ " k=" ++ show k)
          (trace (name ++ " k=" ++ show k ++ " -> " ++ f k) (curve name f ks r))

  module benchM = bench merge-run
  module region-foldM = region-fold filter-run

  prefixes : List ℕ
  prefixes = 800 ∷ 3936 ∷ []

  point : String → String → ℕ → ℕ
  point name v r = trace ("begin " ++ name) (trace (name ++ " -> " ++ v) r)

main : Main
main =
  run (putStrLn (trace survey
        (show (curve "split" region-foldM.split (2 ∷ 3 ∷ 4 ∷ 6 ∷ 10 ∷ []) 0))))
