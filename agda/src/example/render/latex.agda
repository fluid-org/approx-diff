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
  using (Node; val; vals; at)
open import interaction.moves three.semiring (λ x → three.∨-idem {x}) three.≡-of-≈ three.ε?
  using (module Interaction; Config; visible; NonZero?)
open import example.runs (nonzero three.semiring) three.semiring three.C
  using (Run; query-run; const-run; length-run; fold0-run; case0-run; tag-run; case-l-run;
         case-r-run; test-run; map-run; adjacent-sums-run; filter-run; cond-run; eq-run;
         mult-run; add-mul-run; case-inl-run; mavg-run; total-run; sum-mul-run; rose-run; score-run; env; term)
open import example.render.table using (Label; Mat; SignedMat; none; sel-label; table; signed-table)
open import example.render.value-labels (nonzero three.semiring) three.semiring three.C
  using (val-labels; env-labels; vals-labels)

private
  module M3 = matrix.Mat three.semiring

  rows : ∀ {m n} → M3.Matrix m n → Mat
  rows M = toList (tabulate (λ q → toList (tabulate (M q))))

  node-labels : ℕ → Node → List Label
  node-labels off (val v)        = val-labels off v
  node-labels off (vals {is} vs) = vals-labels {is} off vs

  module render (r : Run) where
    private
      open Evaluated (env r) (term r)

      i-labels o-labels : List Label
      i-labels = env-labels (env r)
      o-labels = val-labels 0 value

      -- Dependence matrix of the degenerate configuration.
      R = hide-in-evaluation-order dependence
            (map (λ v → inj₂ (inj₁ v)) (vertices (Graph.shape dependence)))
            (inj₁ input) (inj₂ (inj₂ root))

      -- Control column of the environment vertex dropped.
      drop-ctrl : ∀ {m n} → M3.Matrix m (Nat.suc n) → M3.Matrix m n
      drop-ctrl M q p = M q (suc p)

      open Interaction dependence using (entry; initial; reveal-at; visible-graph)

      wd : V dependence → ℕ
      wd = vertex-width dependence

      vertex-labels : V dependence → List Label
      vertex-labels (inj₁ _)        = i-labels
      vertex-labels (inj₂ (inj₁ p)) = node-labels 0 (proj₁ (labels .at p))
      vertex-labels (inj₂ (inj₂ _)) = o-labels

      -- Width of a vertex as presented: the environment loses its control column.
      pwd : V dependence → ℕ
      pwd (inj₁ _) = Nat.pred (wd (inj₁ input))
      pwd (inj₂ v) = wd (inj₂ v)

      presented : (u v : V dependence) → M3.Matrix (wd v) (wd u) → M3.Matrix (wd v) (pwd u)
      presented (inj₁ input) _ M = drop-ctrl M
      presented (inj₂ _)     _ M = M

    plain : String → String
    plain name = table name i-labels o-labels (rows (drop-ctrl R)) none none

    fwd bwd : String → ℕ → String
    fwd name i = table name i-labels o-labels (rows (drop-ctrl R)) (sel-label i-labels i) none
    bwd name i = table name i-labels o-labels (rows (drop-ctrl R)) none (sel-label o-labels i)

    related-outputs : String → String
    related-outputs name = table name o-labels o-labels (rows (D M3.∘ (D M3.ᵀ))) none none
      where D = drop-ctrl R

    -- One table per nonzero visible-graph edge between the environment, the revealed vertices
    -- and the root.
    tables : List (Vertex (Graph.shape dependence)) → (V dependence → String) → String →
             List (String × String)
    tables ps nm name = concat (map (λ u → concat (map (edge u) endpoints)) endpoints)
      where
      K : Config dependence
      K = foldr reveal-at initial ps
      endpoints : List (V dependence)
      endpoints = inj₁ input ∷ (map (λ p → inj₂ (inj₁ p)) (K .visible) ++ₗ (inj₂ (inj₂ root) ∷ []))
      edge : V dependence → V dependence → List (String × String)
      edge u v = go (presented u v (entry u v (visible-graph K u v)))
        where
        go : M3.Matrix (wd v) (pwd u) → List (String × String)
        go M with NonZero? M
        ... | no  _ = []
        ... | yes _ =
          (name ++ "-" ++ nm u ++ "-" ++ nm v ,
           table (name ++ " (" ++ nm u ++ " to " ++ nm v ++ ")") (vertex-labels u) (vertex-labels v)
                 (rows M) none none) ∷ []

  add-mul-graph = Evaluated.dependence (env add-mul-run) (term add-mul-run)

  sum-vertex : Vertex (Graph.shape add-mul-graph)
  sum-vertex = inj₁ (inj₁ (inj₂ root))

  add-mul-name : V add-mul-graph → String
  add-mul-name (inj₁ _)        = "env"
  add-mul-name (inj₂ (inj₁ _)) = "sum"
  add-mul-name (inj₂ (inj₂ _)) = "root"

  case-inl-graph = Evaluated.dependence (env case-inl-run) (term case-inl-run)

  scrutinee-vertex : Vertex (Graph.shape case-inl-graph)
  scrutinee-vertex = inj₁ (inj₂ root)

  case-inl-name : V case-inl-graph → String
  case-inl-name (inj₁ _)        = "env"
  case-inl-name (inj₂ (inj₁ _)) = "scrutinee"
  case-inl-name (inj₂ (inj₂ _)) = "root"

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
        using (dependence; value)

      score-rows : SignedMat
      score-rows = drop-ctrl (graph.hide-in-evaluation-order dependence
                     (map (λ v → inj₂ (inj₁ v)) (graph.vertices (graph.Graph.shape dependence)))
                     (inj₁ graph.input) (inj₂ (inj₂ graph.root)))
        where
        drop-ctrl : ∀ {m n} → mat.Matrix m (Nat.suc n) → SignedMat
        drop-ctrl R = toList (tabulate (λ q → toList (tabulate (λ p → R q (suc p)))))

    fragment : String
    fragment = signed-table "score (signed)" (axes.env-labels (runs.env runs.score-run))
              (axes.val-labels 0 value) score-rows

all-tables : List (String × String)
all-tables =
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
  ("add-mul"               , render.plain add-mul-run     "add-mul")  ∷
  ("case-inl"              , render.plain case-inl-run    "case-inl") ∷
  ("score-signed"          , signed.fragment) ∷ []
  ++ₗ render.tables add-mul-run (sum-vertex ∷ []) add-mul-name "add-mul"
  ++ₗ render.tables case-inl-run (scrutinee-vertex ∷ []) case-inl-name "case-inl"
  -- merge and merge-forward disabled: hide-in-evaluation-order diverges on merge's graph (#48
  -- closure width growth); restore once that subtask lands.

main : Main
main = run (foldr (λ t io → writeFile ("test-baselines/matrices/" ++ proj₁ t ++ ".tex") (proj₂ t) >> io)
                  (pure tt) all-tables)
