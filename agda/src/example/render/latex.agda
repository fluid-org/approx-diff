{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- Run from approx-diff repository root.
module example.render.latex where

open import IO
open import IO.Finite using (writeFile)
open import Data.Fin using (suc)
open import Data.List using (List; []; _∷_; map; foldr)
open import Data.Nat using (ℕ)
import Data.Nat as Nat
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Rational using (ℚ)
open import Data.String using (String; _++_)
open import Data.Vec using (toList; tabulate)
import example.render.value-labels
import example.runs
import interaction.evaluated
import interaction.graph
import matrix
import semiring-sign as sign
import signature.example.interpretation
import three
open import semiring-Q using (nonzero)
open import commutative-semiring-product using (_⊗S_; ⊗-idem)
open import signature.example.interpretation (nonzero three.semiring) three.semiring
  using (Sig; interpretation)
open import interaction.graph three.semiring (λ x → three.∨-idem {x})
open import interaction.evaluated Sig three.semiring interpretation three.C (λ x → three.∨-idem {x})
open import example.runs (nonzero three.semiring) three.semiring three.C
  using (Run; query-run; const-run; length-run; fold0-run; case0-run; tag-run; case-l-run;
         case-r-run; test-run; map-run; adjacent-sums-run; filter-run; cond-run; eq-run;
         mult-run; mavg-run; total-run; sum-mul-run; rose-run; score-run; env; term; model-output)
open import example.render.table using (Label; Mat; SignedMat; Sel; none; sel-label; table; signed-table)
open import example.render.value-labels (nonzero three.semiring) three.semiring three.C
  using (val-labels; env-labels)

private
  module M3 = matrix.Mat three.semiring

  rows : ∀ {m n} → M3.Matrix m n → Mat
  rows M = toList (tabulate (λ q → toList (tabulate (M q))))

  in-labels out-labels : Run → List Label
  in-labels  r = env-labels (env r)
  out-labels r = val-labels 0 (model-output r)

  -- The dependence matrix of a run's degenerate configuration: every intermediate hidden, in
  -- evaluation order, with the control column of the environment vertex dropped.
  op-rows : Run → Mat
  op-rows r = drop-ctrl (hide-in-evaluation-order dependence widths free
                           (map (λ v → inj₂ (inj₁ v)) (vertices (Graph.shape dependence)))
                           (inj₁ input) (inj₂ (inj₂ root)))
    where
    open Evaluated (env r) (term r)

    -- Argument taken as a value so its internal table is computed once, not per entry read.
    drop-ctrl : ∀ {m n} → M3.Matrix m (Nat.suc n) → Mat
    drop-ctrl R = rows (λ q p → R q (suc p))

  -- Which outputs are related through some shared input.
  related : String → Run → String
  related name r = table name (out-labels r) (out-labels r) (go (hide-in-evaluation-order dependence widths free
                     (map (λ v → inj₂ (inj₁ v)) (vertices (Graph.shape dependence)))
                     (inj₁ input) (inj₂ (inj₂ root)))) none none
    where
    open Evaluated (env r) (term r)

    go : ∀ {m n} → M3.Matrix m (Nat.suc n) → Mat
    go {m} {n} R = rows (drop M3.∘ (drop M3.ᵀ))
      where
      drop : M3.Matrix m n
      drop q p = R q (suc p)

  run-table : String → Run → Sel → Sel → String
  run-table name r isel osel = table name (in-labels r) (out-labels r) (op-rows r) isel osel

  plain : String → Run → String
  plain name r = run-table name r none none

  fwd : String → Run → ℕ → String
  fwd name r i = run-table name r (sel-label (in-labels r) i) none

  bwd : String → Run → ℕ → String
  bwd name r i = run-table name r none (sel-label (out-labels r) i)

  module signed where
    private
      signed-weight : ℚ → sign.Sign × three.Three
      signed-weight q = sign.sign-of q , nonzero three.semiring q

      module runs = example.runs signed-weight (sign.semiring ⊗S three.semiring) (sign.unk , three.C)
      module graph = interaction.graph (sign.semiring ⊗S three.semiring)
                       (⊗-idem sign.semiring three.semiring sign.+ˢ-idem (λ x → three.∨-idem {x}))
      module sig-interp = signature.example.interpretation signed-weight
                            (sign.semiring ⊗S three.semiring)
      module evaluated = interaction.evaluated sig-interp.Sig (sign.semiring ⊗S three.semiring)
                           sig-interp.interpretation (sign.unk , three.C)
                           (⊗-idem sign.semiring three.semiring sign.+ˢ-idem (λ x → three.∨-idem {x}))
      module axes = example.render.value-labels signed-weight (sign.semiring ⊗S three.semiring)
                      (sign.unk , three.C)
      module mat = matrix.Mat (sign.semiring ⊗S three.semiring)

      open evaluated.Evaluated (runs.env runs.score-run) (runs.term runs.score-run)
        using (dependence; widths; free)

      score-rows : SignedMat
      score-rows = drop-ctrl (graph.hide-in-evaluation-order dependence widths free
                     (map (λ v → inj₂ (inj₁ v)) (graph.vertices (graph.Graph.shape dependence)))
                     (inj₁ graph.input) (inj₂ (inj₂ graph.root)))
        where
        drop-ctrl : ∀ {m n} → mat.Matrix m (Nat.suc n) → SignedMat
        drop-ctrl R = toList (tabulate (λ q → toList (tabulate (λ p → R q (suc p)))))

    fragment : String
    fragment = signed-table "score (signed)" (axes.env-labels (runs.env runs.score-run))
              (axes.val-labels 0 (runs.model-output runs.score-run)) score-rows

tables : List (String × String)
tables =
  ("query"         , plain "query"         query-run)   ∷
  ("const"         , plain "const"         const-run)   ∷
  ("length"        , plain "length"        length-run)  ∷
  ("fold0"         , plain "fold0"         fold0-run)   ∷
  ("case0"         , plain "case0"         case0-run)   ∷
  ("tag"           , plain "tag"           tag-run)     ∷
  ("case-left"     , plain "case-left"     case-l-run)  ∷
  ("case-right"    , plain "case-right"    case-r-run)  ∷
  ("test"          , plain "test"          test-run)    ∷
  ("map"           , plain "map"           map-run)     ∷
  ("adjacent-sums" , plain "adjacent-sums" adjacent-sums-run) ∷
  ("filter"        , plain "filter"        filter-run)  ∷
  ("cond"          , plain "cond"          cond-run)    ∷
  ("eq"            , plain "eq"            eq-run)      ∷
  ("mult"          , plain "mult"          mult-run)    ∷
  ("mavg"          , plain "mavg"          mavg-run)    ∷
  ("total"         , plain "total"         total-run)   ∷
  ("sum-mul"       , plain "sum-mul"       sum-mul-run) ∷
  ("rose"          , plain "rose"          rose-run)    ∷
  ("score"         , plain "score"         score-run)   ∷
  ("map-backward"        , bwd "map (backward slice)"          map-run           2) ∷
  ("adjacent-sums-forward" , fwd "adjacent-sums (forward slice)" adjacent-sums-run 2) ∷
  ("mavg-related"          , related "mavg (related outputs)"          mavg-run) ∷
  ("adjacent-sums-related" , related "adjacent-sums (related outputs)" adjacent-sums-run) ∷
  ("score-signed"          , signed.fragment) ∷ []
  -- merge and merge-forward disabled: hide-in-evaluation-order diverges on merge's graph (#48
  -- closure width growth); restore once that subtask lands.

main : Main
main = run (foldr (λ t io → writeFile ("test-baselines/matrices/" ++ proj₁ t ++ ".tex") (proj₂ t) >> io)
                  (pure tt) tables)
