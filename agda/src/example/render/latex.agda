{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- Run from approx-diff repository root.
module example.render.latex where

open import IO
open import IO.Finite using (writeFile)
open import Data.Fin using (suc)
open import Data.List using (List; []; _∷_; map; foldr; concat) renaming (_++_ to _++ₗ_)
open import Data.Nat using (ℕ)
import Data.Nat as Nat
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Rational using (ℚ)
open import Data.String using (String; _++_)
open import Data.Vec using (toList; tabulate)
open import Relation.Nullary using (yes; no)
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
open import interaction.labelling Sig three.semiring interpretation three.C (λ x → three.∨-idem {x})
  using (Node; val; at)
open import interaction.moves three.semiring (λ x → three.∨-idem {x}) three.≡-of-≈ three.ε?
  using (module Interaction; Config; visible; NonZero?; tabulated-summary;
         Tables; first-order-tables; tabulated-first-order)
open import example.runs (nonzero three.semiring) three.semiring three.C
  using (Run; filter-sum-run; const-run; length-run; fold0-run; case0-run; tag-run; case-l-run;
         case-r-run; test-run; map-run; adjacent-sums-run; filter-run; cond-run; eq-run;
         mult-run; add-mul-run; case-inl-run; mavg-run; total-run; sum-mul-run; rose-run; score-run; env; term)
open import example.render.table using (Label; none; sel-label; table; signed-table)
open import example.render.value-labels (nonzero three.semiring) three.semiring three.C
  using (val-labels; env-labels)

private
  module M3 = matrix.Mat three.semiring

  node-labels : ℕ → Node → List Label
  node-labels off (val v) = val-labels off v

  module render (r : Run) where
    private
      open Evaluated (env r) (term r)

      i-labels o-labels : List Label
      i-labels = env-labels (env r)
      o-labels = val-labels 0 value

      -- Dependence matrix of the degenerate configuration.
      R = hide-in-evaluation-order dependence (map inj₂ (vertices D)) (inj₁ input) (inj₂ ε)

      -- Control column of the environment vertex dropped.
      drop-ctrl : ∀ {m n} → M3.Matrix m (Nat.suc n) → M3.Matrix m n
      drop-ctrl M q p = M q (suc p)

      open Interaction dependence (fo-graph dependence) using (entry)

      wd : V dependence → ℕ
      wd = vertex-width dependence

      vertex-labels : V dependence → List Label
      vertex-labels (inj₁ _) = i-labels
      vertex-labels (inj₂ p) = node-labels 0 (proj₁ (labels .at p))

      -- Width of a vertex as presented: the environment loses its control column.
      pwd : V dependence → ℕ
      pwd (inj₁ _) = Nat.pred (wd (inj₁ input))
      pwd (inj₂ v) = wd (inj₂ v)

      presented : (u v : V dependence) → M3.Matrix (wd v) (wd u) → M3.Matrix (wd v) (pwd u)
      presented (inj₁ input) _ M = drop-ctrl M
      presented (inj₂ _)     _ M = M

    plain : String → String
    plain name = table name i-labels o-labels (M3.to-table (drop-ctrl R)) none none

    fwd bwd : String → ℕ → String
    fwd name i = table name i-labels o-labels (M3.to-table (drop-ctrl R)) (sel-label i-labels i) none
    bwd name i = table name i-labels o-labels (M3.to-table (drop-ctrl R)) none (sel-label o-labels i)

    related-outputs : String → String
    related-outputs name = table name o-labels o-labels (M3.to-table (rows M3.∘ (rows M3.ᵀ))) none none
      where rows = drop-ctrl R

    -- One table per nonzero visible-graph edge between the environment, the revealed vertices
    -- and the root.
    tables : List (Path D) → (V dependence → String) → String →
             List (String × String)
    tables ps nm name = from-store (first-order-tables dependence)
      where
      from-store : Tables dependence → List (String × String)
      from-store ts = at-config (foldr (I.reveal-at summarise) (I.initial summarise) ps)
        where
        first-order = tabulated-first-order dependence ts
        summarise = tabulated-summary dependence first-order
        module I = Interaction dependence first-order
        at-config : Config dependence → List (String × String)
        at-config K = concat (map (λ u → concat (map (edge u) endpoints)) endpoints)
          where
          endpoints : List (V dependence)
          endpoints = inj₁ input ∷ (map inj₂ (K .visible) ++ₗ (inj₂ ε ∷ []))
          edge : V dependence → V dependence → List (String × String)
          edge u v = emit (presented u v (entry u v (I.visible-graph K u v)))
            where
            emit : M3.Matrix (wd v) (pwd u) → List (String × String)
            emit M with NonZero? M
            ... | no  _ = []
            ... | yes _ =
              (name ++ "-" ++ nm u ++ "-" ++ nm v ,
               table (name ++ " (" ++ nm u ++ " to " ++ nm v ++ ")") (vertex-labels u) (vertex-labels v)
                     (M3.to-table M) none none) ∷ []

  filter-sum-graph = Evaluated.dependence (env filter-sum-run) (term filter-sum-run)

  -- Root of the application's argument premise: the filtered list between the comprehension and sum.
  filtered-vertex : Path (Evaluated.D (env filter-sum-run) (term filter-sum-run))
  filtered-vertex = into (there here) ε

  filter-sum-name : V filter-sum-graph → String
  filter-sum-name (inj₁ _)          = "env"
  filter-sum-name (inj₂ ε)          = "root"
  filter-sum-name (inj₂ (into _ _)) = "filtered"

  add-mul-graph = Evaluated.dependence (env add-mul-run) (term add-mul-run)

  sum-vertex : Path (Evaluated.D (env add-mul-run) (term add-mul-run))
  sum-vertex = into here ε

  add-mul-name : V add-mul-graph → String
  add-mul-name (inj₁ _)          = "env"
  add-mul-name (inj₂ ε)          = "root"
  add-mul-name (inj₂ (into _ _)) = "sum"

  case-inl-graph = Evaluated.dependence (env case-inl-run) (term case-inl-run)

  scrutinee-vertex : Path (Evaluated.D (env case-inl-run) (term case-inl-run))
  scrutinee-vertex = into here ε

  case-inl-name : V case-inl-graph → String
  case-inl-name (inj₁ _)          = "env"
  case-inl-name (inj₂ ε)          = "root"
  case-inl-name (inj₂ (into _ _)) = "scrutinee"

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
        using (D; dependence; value)

      score-rows : mat.Table
      score-rows = drop-ctrl (graph.hide-in-evaluation-order dependence
                     (map inj₂ (graph.vertices D))
                     (inj₁ graph.input) (inj₂ graph.ε))
        where
        drop-ctrl : ∀ {m n} → mat.Matrix m (Nat.suc n) → mat.Table
        drop-ctrl R = toList (tabulate (λ q → toList (tabulate (λ p → R q (suc p)))))

    fragment : String
    fragment = signed-table "score (signed)" (axes.env-labels (runs.env runs.score-run))
              (axes.val-labels 0 value) score-rows

all-tables : List (String × String)
all-tables =
  ("filter-sum"    , render.plain filter-sum-run    "filter-sum") ∷
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
  ("add-mul"               , render.plain add-mul-run     "add-mul")  ∷
  ("case-inl"              , render.plain case-inl-run    "case-inl") ∷
  ("score-signed"          , signed.fragment) ∷ []
  -- filter-sum stage tables disabled: revealing the filtered list is slow until hide produces
  -- graphs (#69); reinstate then.
  ++ₗ render.tables add-mul-run (sum-vertex ∷ []) add-mul-name "add-mul"
  ++ₗ render.tables case-inl-run (scrutinee-vertex ∷ []) case-inl-name "case-inl"
  -- merge and merge-forward disabled: hide-in-evaluation-order diverges on merge's graph (#48
  -- closure width growth); restore once that subtask lands.

main : Main
main = run (foldr (λ t io → writeFile ("test-baselines/matrices/" ++ proj₁ t ++ ".tex") (proj₂ t) >> io)
                  (pure tt) all-tables)
