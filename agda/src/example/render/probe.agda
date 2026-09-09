{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- Cost probes for the hiding pass, reporting through the trace postulate on stderr so a
-- killed run loses nothing. Scale survey across examples, then scaling curve on merge prefixes.
-- Run from approx-diff repository root.
module example.render.probe where

open import IO
open import IO.Finite using (putStrLn)
open import Data.List using (List; []; _∷_; map; length; concat; upTo)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _⊔_)
open import Data.Product using (_×_; _,_)
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

  module bench (r : Run) where
    open Evaluated (env r) (term r)

    T : Tabulation
    T = tabulation dependence three.ε? trace

    join-table : M3.Table → Three
    join-table t = join-list (concat t)

    join-slot : Maybe M3.Table → Three
    join-slot nothing  = three.O
    join-slot (just t) = join-table t

    -- Strict in both arguments, so joining forces every slot.
    join! : Three → Three → Three
    join! three.O y       = y
    join! three.C three.O = three.C
    join! three.C three.C = three.C
    join! three.C three.D = three.D
    join! three.D three.O = three.D
    join! three.D three.C = three.D
    join! three.D three.D = three.D

    join-row : List (Maybe M3.Table) → Three
    join-row []       = three.O
    join-row (s ∷ ss) = join! (join-slot s) (join-row ss)

    join-store : List (List (Maybe M3.Table)) → Three
    join-store []         = three.O
    join-store (row ∷ rs) = join! (join-row row) (join-store rs)

    ask-all : Tabulation → Three
    ask-all H = join-store (H .edges)

    Tₛ : Tabulation
    Tₛ = sparse-tabulation dependence three.ε? trace

    T𝓌 : Tabulation
    T𝓌 = stepwise-tabulation dependence three.ε? trace

    all-old all-blocks all-sparse all-listed all-stepwise all-functional : ℕ → String
    join-entries : List (ℕ × M3.Table) → Three
    join-entries []             = three.O
    join-entries ((_ , t) ∷ es) = join! (join-table t) (join-entries es)

    all-functional k =
      show3 (hide-graph-fold dependence three.ε? trace (map suc (upTo k))
               (λ a c → join! a (join-entries c)) three.O)
    all-old k    = show3 (ask-all (Tabulated.hide-graph T trace three.ε? (map suc (upTo k))))
    all-blocks k = show3 (ask-all (Tabulated.hide-graph-blocks T trace three.ε? (map suc (upTo k))))
    all-sparse k = show3 (join-store (Tabulated.hide-graph-sparse T trace three.ε? (map suc (upTo k))))
    all-listed k = show3 (join-store (Tabulated.hide-graph-sparse Tₛ trace three.ε? (map suc (upTo k))))
    all-stepwise k =
      show3 (join-store (Tabulated.hide-graph-sparse T𝓌 trace three.ε? (map suc (upTo k))))

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

  module benchF = bench filter-sum-run

  prefixes : List ℕ
  prefixes = 5 ∷ 25 ∷ 100 ∷ 194 ∷ []

main : Main
main = run (putStrLn (trace survey (show (curve "functional" benchF.all-functional prefixes 0))))
