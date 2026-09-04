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
         mult-run; mavg-run; total-run; sum-mul-run; rose-run; score-run; env; term)
open import example.render.table using (Label; Mat; SignedMat; none; sel-label; table; signed-table)
open import example.render.value-labels (nonzero three.semiring) three.semiring three.C
  using (val-labels; env-labels)

private
  module M3 = matrix.Mat three.semiring

  rows : ∀ {m n} → M3.Matrix m n → Mat
  rows M = toList (tabulate (λ q → toList (tabulate (M q))))

  module render (r : Run) where
    private
      open Evaluated (env r) (term r)

      i-labels o-labels : List Label
      i-labels = env-labels (env r)
      o-labels = val-labels 0 value

      -- Dependence matrix of the degenerate configuration.
      R = hide-in-evaluation-order dependence widths free
            (map (λ v → inj₂ (inj₁ v)) (vertices (Graph.shape dependence)))
            (inj₁ input) (inj₂ (inj₂ root))

      -- Control column of the environment vertex dropped.
      drop-ctrl : ∀ {m n} → M3.Matrix m (Nat.suc n) → M3.Matrix m n
      drop-ctrl M q p = M q (suc p)

    plain : String → String
    plain name = table name i-labels o-labels (rows (drop-ctrl R)) none none

    fwd bwd : String → ℕ → String
    fwd name i = table name i-labels o-labels (rows (drop-ctrl R)) (sel-label i-labels i) none
    bwd name i = table name i-labels o-labels (rows (drop-ctrl R)) none (sel-label o-labels i)

    related-outputs : String → String
    related-outputs name = table name o-labels o-labels (rows (D M3.∘ (D M3.ᵀ))) none none
      where D = drop-ctrl R

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
        using (dependence; widths; free; value)

      score-rows : SignedMat
      score-rows = drop-ctrl (graph.hide-in-evaluation-order dependence widths free
                     (map (λ v → inj₂ (inj₁ v)) (graph.vertices (graph.Graph.shape dependence)))
                     (inj₁ graph.input) (inj₂ (inj₂ graph.root)))
        where
        drop-ctrl : ∀ {m n} → mat.Matrix m (Nat.suc n) → SignedMat
        drop-ctrl R = toList (tabulate (λ q → toList (tabulate (λ p → R q (suc p)))))

    fragment : String
    fragment = signed-table "score (signed)" (axes.env-labels (runs.env runs.score-run))
              (axes.val-labels 0 value) score-rows

tables : List (String × String)
tables =
  ("query"         , render.plain query-run         "query")      ∷
  ("const"         , render.plain const-run         "const")      ∷
  ("length"        , render.plain length-run        "length")     ∷
  ("fold0"         , render.plain fold0-run         "fold0")      ∷
  ("case0"         , render.plain case0-run         "case0")      ∷
  ("tag"           , render.plain tag-run           "tag")        ∷
  ("case-left"     , render.plain case-l-run        "case-left")  ∷
  ("case-right"    , render.plain case-r-run        "case-right") ∷
  ("test"          , render.plain test-run          "test")       ∷
  ("map"           , render.plain map-run           "map")        ∷
  ("adjacent-sums" , render.plain adjacent-sums-run "adjacent-sums") ∷
  ("filter"        , render.plain filter-run        "filter")     ∷
  ("cond"          , render.plain cond-run          "cond")       ∷
  ("eq"            , render.plain eq-run            "eq")         ∷
  ("mult"          , render.plain mult-run          "mult")       ∷
  ("mavg"          , render.plain mavg-run          "mavg")       ∷
  ("total"         , render.plain total-run         "total")      ∷
  ("sum-mul"       , render.plain sum-mul-run       "sum-mul")    ∷
  ("rose"          , render.plain rose-run          "rose")       ∷
  ("score"         , render.plain score-run         "score")      ∷
  ("map-backward"        , render.bwd map-run "map (backward slice)" 2) ∷
  ("adjacent-sums-forward" , render.fwd adjacent-sums-run "adjacent-sums (forward slice)" 2) ∷
  ("mavg-related"          , render.related-outputs mavg-run "mavg (related outputs)") ∷
  ("adjacent-sums-related" , render.related-outputs adjacent-sums-run "adjacent-sums (related outputs)") ∷
  ("score-signed"          , signed.fragment) ∷ []
  -- merge and merge-forward disabled: hide-in-evaluation-order diverges on merge's graph (#48
  -- closure width growth); restore once that subtask lands.

main : Main
main = run (foldr (λ t io → writeFile ("test-baselines/matrices/" ++ proj₁ t ++ ".tex") (proj₂ t) >> io)
                  (pure tt) tables)
