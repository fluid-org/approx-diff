{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- Run from approx-diff repository root.
module example.render.gen-latex where

open import IO
open import IO.Finite using (writeFile)
open import Data.Fin using (suc)
open import Data.List using (List; []; _∷_; map; mapMaybe; foldr; concat; length; upTo)
  renaming (_++_ to _++ₗ_)
open import Data.Maybe using (Maybe; just; nothing)
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
import interaction.moves
import matrix
import semiring-sign as sign
import signature.example.interpretation
import three
open import semiring-Q using (nonzero)
open import commutative-semiring-product using (_⊗S_; ⊗-idem; ⊗-ε?; ⊗-≡-of-≈)
open import signature.example.interpretation (nonzero three.semiring) three.semiring
  using (Sig; interpretation)
open import interaction.graph three.semiring (λ x → three.∨-idem {x})
open import interaction.evaluated Sig three.semiring interpretation three.C (λ x → three.∨-idem {x})
open import interaction.labelling Sig three.semiring interpretation three.C (λ x → three.∨-idem {x})
  using (Node; val; at)
open import interaction.moves three.semiring (λ x → three.∨-idem {x}) three.≡-of-≈ three.ε?
  using (module Interaction; Config; visible; NonZero?; fo-graph-edges; region-summary)
open import example.runs (nonzero three.semiring) three.semiring three.C
  using (Run; filter-sum-run; const-run; length-run; fold0-run; case0-run; tag-run; case-l-run;
         case-r-run; test-run; map-run; adjacent-sums-run; filter-run; cond-run; eq-run;
         mult-run; add-mul-run; case-inl-run; mavg-run; total-run; sum-mul-run; rose-run; score-run; env; term)
open import example.render.table using (Label; Sel; none; sel-label; table; signed-table)
open import example.render.value-labels (nonzero three.semiring) three.semiring three.C
  using (val-labels; env-labels)

private
  module M3 = matrix.Mat three.semiring

  node-labels : ℕ → Node → List Label
  node-labels off (val v) = val-labels off v

  data Presentation : Set where
    matrices : Maybe ℕ → Maybe ℕ → Presentation
    related  : Presentation

  -- A test: a run, the vertices to reveal (each a name and premise positions), and how to present
  -- the resulting visible graph. Emitted under key/<u>-<v> for each visible edge.
  record Test : Set where
    field
      key     : String
      title   : String
      the-run : Run
      reveals : List (String × List ℕ)
      present : Presentation

  module render (r : Run) where
    open Evaluated (env r) (term r) public using (D; dependence)
    private
      open Evaluated (env r) (term r) hiding (D; dependence)

      i-labels o-labels : List Label
      i-labels = env-labels (env r)
      o-labels = val-labels 0 value

      fo-tables = fo-graph-edges dependence (λ _ x → x)
      fo-of : Edges dependence → DepRels (vertex-object dependence)
      fo-of tabs x y = table-morphism dependence x y (edge-at dependence three.ε? (λ _ z → z) tabs x y)
      fo = fo-of fo-tables
      summarise = region-summary dependence (λ _ x → x)
      module I = Interaction dependence fo

      -- Dependence matrix of the degenerate configuration.
      R = degenerate fo-tables
        where
        degenerate : Edges dependence → M3.Matrix (vertex-width dependence (inj₂ ε))
                                                  (vertex-width dependence (inj₁ input))
        degenerate tabs =
          M3.look {vertex-width dependence (inj₂ ε)} {vertex-width dependence (inj₁ input)}
            (J.visible-table tabs (J.initial summarise) (inj₁ input) (inj₂ ε))
          where module J = Interaction dependence (fo-of tabs)

      -- Control column of the environment vertex dropped.
      drop-ctrl : ∀ {m n} → M3.Matrix m (Nat.suc n) → M3.Matrix m n
      drop-ctrl M q p = M q (suc p)

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

    -- One table per edge of the visible graph after the reveals, between the environment, the
    -- revealed vertices and the root.
    emit : String → String → List (String × List ℕ) → Presentation → List (String × String)
    emit key title reveals (matrices si so) = shared fo-tables
      where
      resolve : String × List ℕ → Maybe (String × Path D)
      resolve (s , ks) with path-at D ks
      ... | just p  = just (s , p)
      ... | nothing = nothing

      named : List (String × Path D)
      named = mapMaybe resolve reveals

      K : Config dependence
      K = foldr (I.reveal-at summarise) (I.initial summarise) (map proj₂ named)

      endpoints : List (String × V dependence)
      endpoints = ("env" , inj₁ input) ∷
                  (map (λ sp → proj₁ sp , inj₂ (proj₂ sp)) named ++ₗ (("root" , inj₂ ε) ∷ []))

      sel-here : List Label → Maybe ℕ → Sel
      sel-here ls nothing  = none
      sel-here ls (just i) = sel-label ls i

      at-env : V dependence → Sel
      at-env (inj₁ _) = sel-here i-labels si
      at-env _        = none

      at-root : V dependence → Sel
      at-root (inj₂ ε) = sel-here o-labels so
      at-root _        = none

      -- An edge whose weight lies only in the dropped control column presents as an all-zero
      -- table; suppressed.
      edge-entry : (String × V dependence) × (String × V dependence) × M3.Table →
                   Maybe (String × String)
      edge-entry ((nu , u) , (nv , v) , t) with presented u v (M3.look {wd v} {wd u} t)
      ... | M with NonZero? M
      ...   | no  _ = nothing
      ...   | yes _ = just
        (key ++ "/" ++ nu ++ "-" ++ nv ,
         table (title ++ " (" ++ nu ++ " to " ++ nv ++ ")") (vertex-labels u) (vertex-labels v)
               (M3.to-table M) (at-env u) (at-root v))

      shared : Edges dependence → List (String × String)
      shared tabs = with-config (foldr (J.reveal-at summarise) (J.initial summarise) (map proj₂ named))
        where
        module J = Interaction dependence (fo-of tabs)

        with-config : Config dependence → List (String × String)
        with-config K' = mapMaybe edge-entry (J.visible-edges tabs K' endpoints)

    emit key title reveals related = from-rows (M3.to-table (drop-ctrl R))
      where
      from-rows : M3.Table → List (String × String)
      from-rows t = product (M3.look {vertex-width dependence (inj₂ ε)} {Nat.pred (wd (inj₁ input))} t)
        where
        product : M3.Matrix (vertex-width dependence (inj₂ ε)) (Nat.pred (wd (inj₁ input))) →
                  List (String × String)
        product rows =
          (key ++ "/root-root" ,
           table title o-labels o-labels (M3.to-table (rows M3.∘ (rows M3.ᵀ))) none none) ∷ []

  mk : String → String → Run → List (String × List ℕ) → Presentation → Test
  mk k ti r rs pr .Test.key     = k
  mk k ti r rs pr .Test.title   = ti
  mk k ti r rs pr .Test.the-run = r
  mk k ti r rs pr .Test.reveals = rs
  mk k ti r rs pr .Test.present = pr

  plain : String → Run → Test
  plain name r = mk name name r [] (matrices nothing nothing)

  emit-test : Test → List (String × String)
  emit-test T = render.emit (Test.the-run T) (Test.key T) (Test.title T) (Test.reveals T) (Test.present T)

  tests : List Test
  tests =
    plain "filter-sum" filter-sum-run ∷
    plain "const" const-run ∷
    plain "length" length-run ∷
    plain "fold0" fold0-run ∷
    plain "case0" case0-run ∷
    plain "tag" tag-run ∷
    plain "case-left" case-l-run ∷
    plain "case-right" case-r-run ∷
    plain "test" test-run ∷
    plain "map" map-run ∷
    plain "adjacent-sums" adjacent-sums-run ∷
    plain "filter" filter-run ∷
    plain "cond" cond-run ∷
    plain "eq" eq-run ∷
    plain "mult" mult-run ∷
    plain "mavg" mavg-run ∷
    plain "total" total-run ∷
    plain "sum-mul" sum-mul-run ∷
    plain "rose" rose-run ∷
    plain "score" score-run ∷
    plain "add-mul" add-mul-run ∷
    plain "case-inl" case-inl-run ∷
    mk "map-backward" "map (backward slice)" map-run [] (matrices nothing (just 2)) ∷
    mk "adjacent-sums-forward" "adjacent-sums (forward slice)" adjacent-sums-run [] (matrices (just 2) nothing) ∷
    mk "mavg-related" "mavg (related outputs)" mavg-run [] related ∷
    mk "adjacent-sums-related" "adjacent-sums (related outputs)" adjacent-sums-run [] related ∷
    -- Root of the application's argument premise: the filtered list between the comprehension and sum.
    mk "filter-sum-filtered" "filter-sum" filter-sum-run (("filtered" , 1 ∷ []) ∷ []) (matrices nothing nothing) ∷
    mk "add-mul-sum" "add-mul" add-mul-run (("sum" , 0 ∷ []) ∷ []) (matrices nothing nothing) ∷
    mk "case-inl-scrutinee" "case-inl" case-inl-run (("scrutinee" , 0 ∷ []) ∷ []) (matrices nothing nothing) ∷ []

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

      signed-ε? = ⊗-ε? sign.semiring three.semiring sign.ε? three.ε?
      module mat = matrix.Mat (sign.semiring ⊗S three.semiring)

      open evaluated.Evaluated (runs.env runs.score-run) (runs.term runs.score-run)
        using (D; dependence; value)

      module smoves = interaction.moves (sign.semiring ⊗S three.semiring)
                        (⊗-idem sign.semiring three.semiring sign.+ˢ-idem (λ x → three.∨-idem {x}))
                        (⊗-≡-of-≈ sign.semiring three.semiring sign.≡-of-≈ three.≡-of-≈)
                        signed-ε?

      fo-tables = smoves.fo-graph-edges dependence (λ _ x → x)
      fo-of : graph.Edges dependence → graph.DepRels (graph.vertex-object dependence)
      fo-of tabs x y = graph.table-morphism dependence x y
                         (graph.edge-at dependence signed-ε? (λ _ z → z) tabs x y)
      summarise = smoves.region-summary dependence (λ _ x → x)

      score-rows : mat.Table
      score-rows = rows fo-tables
        where
        drop-ctrl : ∀ {m n} → mat.Matrix m (Nat.suc n) → mat.Table
        drop-ctrl R = toList (tabulate (λ q → toList (tabulate (λ p → R q (suc p)))))

        rows : graph.Edges dependence → mat.Table
        rows tabs = drop-ctrl (mat.look {graph.vertex-width dependence (inj₂ graph.ε)}
                                        {graph.vertex-width dependence (inj₁ graph.input)}
                      (J.visible-table tabs (J.initial summarise)
                                       (inj₁ graph.input) (inj₂ graph.ε)))
          where module J = smoves.Interaction dependence (fo-of tabs)

    fragment : String
    fragment = signed-table "score (signed)" (axes.env-labels (runs.env runs.score-run))
              (axes.val-labels 0 value) score-rows

all-tables : List (String × String)
all-tables =
  concat (map emit-test tests) ++ₗ (("score-signed/env-root" , signed.fragment) ∷ [])
  -- merge and merge-forward omitted: fo-tabulation does not complete on merge's graph.

main : Main
main = run (foldr (λ t io → writeFile ("test-baselines/matrices/" ++ proj₁ t ++ ".tex") (proj₂ t) >> io)
                  (pure tt) all-tables)
