{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.Bool as Bool using (Bool; not; _∧_; _∨_; if_then_else_)
open import Data.Bool.ListAction using (any)
open import Data.Bool.Properties using (∨-comm; ∨-identityʳ; ∧-comm)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; allFin; length; map; filterᵇ; concat; partitionᵇ; foldr)
open import Data.List.Properties using (++-identityʳ; concat-++; concat-map; foldl-++; length-map; map-++; map-∘)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
  using (map⁺; shift; ++⁺; drop-∷; Any-resp-↭; ↭-length)
open import Data.List.Relation.Binary.Pointwise using ([]; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_; universal) renaming (map to All-map)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_) renaming (map to AllPairs-map)
open import Data.List.Relation.Unary.Any using (Any) renaming (map to Any-map)
open import Data.Nat using (ℕ; _≤_; z≤n; s≤s)
open import Data.Nat.ListAction using (sum)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst; subst₂)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; cong to ≡-cong; cong₂ to ≡-cong₂)
open import Relation.Nullary.Decidable using (⌊_⌋; yes; no)
import Data.List.Relation.Binary.Permutation.Homogeneous as H
import Data.List.Relation.Binary.Permutation.Propositional as ↭
open ↭ using (_↭_; ↭-refl; ↭-sym; ↭-trans; ↭-reflexive)
import Data.List.Relation.Unary.All.Properties as AllP
import Data.List.Relation.Unary.AllPairs.Properties as AllPairsP
import Data.List.Relation.Unary.Any.Properties as AnyPr
import matrix
import two
open import list

-- Configurations of the interaction: a visible set of vertices together with one hidden region per
-- weakly connected component of the hidden set, each carrying the dependence routed through it as
-- a summary. The visible graph reads the first-order graph at the visible vertices and the
-- summaries elsewhere. The hide move merges the regions adjacent to a vertex and the reveal move
-- splits the region containing one. The moves preserve the invariant that the stored regions are
-- the regions of the hidden set with their summaries, and are mutually inverse.
module interaction.moves where

open import interaction.graph two.semiring (λ x → two.∨-idem {x})
import commutative-semiring
open import prop using (Prf; ⟪_⟫) renaming (_∧_ to _∧ₚ_; _,_ to _,ₚ_; proj₁ to proj₁ₚ; proj₂ to proj₂ₚ)

private
  module M = matrix.Mat two.semiring
  module S = commutative-semiring.CommutativeSemiring two.semiring

  ⊥ₚ-elim : ∀ {A : Set} → prop.⊥ {0ℓ} → A
  ⊥ₚ-elim ()

  ≈-of-≡ₛ : ∀ {x y : two.Two} → x ≡ y → x S.≈ y
  ≈-of-≡ₛ ≡-refl = S.refl

  ≡-of-≈ₛ : ∀ {x y : two.Two} → x S.≈ y → x ≡ y
  ≡-of-≈ₛ {two.O} {two.O} _ = ≡-refl
  ≡-of-≈ₛ {two.I} {two.I} _ = ≡-refl
  ≡-of-≈ₛ {two.O} {two.I} e = ⊥ₚ-elim (proj₂ₚ e)
  ≡-of-≈ₛ {two.I} {two.O} e = ⊥ₚ-elim (proj₁ₚ e)

private
  is-I : two.Two → Bool
  is-I two.I = Bool.true
  is-I two.O = Bool.false

nonzero : ∀ {m n} → M.Matrix m n → Bool
nonzero {m} {n} R = any (λ i → any (λ j → is-I (R i j)) (allFin n)) (allFin m)

nonzero-O : ∀ {m n} (R : M.Matrix m n) → nonzero R ≡ Bool.false →
            ∀ i j → R i j ≡ two.O
nonzero-O {m} {n} R h i j
  with R i j
     | any-tabulate-false (λ j' → j') (λ j' → is-I (R i j'))
         (any-tabulate-false (λ i' → i') (λ i' → any (λ j' → is-I (R i' j')) (allFin n)) h i) j
... | two.O | _  = ≡-refl
... | two.I | ()

when : ∀ {m n} → Bool → M.Matrix m n → M.Matrix m n
when Bool.true  R = R
when Bool.false R = M.εₘ

-- A configuration: the visible set, and one pair per hidden region of a set of vertices and a
-- graph. No invariant is imposed; that the pairs are the regions of the hidden set with their
-- summaries is a property the moves preserve.
record Config {m n : ℕ} (B : Graph m n) : Set₁ where
  field
    visible : List (Vertex (Graph.shape B))
    hidden  : List (List (Vertex (Graph.shape B)) × Relation (vertex-width B))

open Config public

module Interaction {m n : ℕ} (B : Graph m n) where

  private
    at : Vertex (Graph.shape B) → V B
    at p = inj₂ (inj₁ p)

    eq : Vertex (Graph.shape B) → Vertex (Graph.shape B) → Bool
    eq p q = ⌊ _≟_ {Graph.shape B} p q ⌋

  member : Vertex (Graph.shape B) → List (Vertex (Graph.shape B)) → Bool
  member p = any (eq p)

  adjacent : Relation (vertex-width B) → V B → V B → Bool
  adjacent G x y = nonzero (G x y) ∨ nonzero (G y x)

  merge-region : Relation (vertex-width B) → Vertex (Graph.shape B) → List (List (Vertex (Graph.shape B))) →
                 List (List (Vertex (Graph.shape B)))
  merge-region G w rss = (w ∷ concat (proj₁ tp)) ∷ proj₂ tp
    where tp = partitionᵇ (any (λ q → adjacent G (at w) (at q))) rss

  regions : Relation (vertex-width B) → List (Vertex (Graph.shape B)) → List (List (Vertex (Graph.shape B)))
  regions G []       = []
  regions G (w ∷ ws) = merge-region G w (regions G ws)

  -- The inputs and the root are never hidden, so only an interior vertex can lie in a region.
  member-vertex : V B → List (Vertex (Graph.shape B)) → Bool
  member-vertex (inj₁ _)        C = Bool.false
  member-vertex (inj₂ (inj₁ p)) C = member p C
  member-vertex (inj₂ (inj₂ _)) C = Bool.false

  restrict : Relation (vertex-width B) → List (Vertex (Graph.shape B)) → Relation (vertex-width B)
  restrict G C x y = when (member-vertex x C ∨ member-vertex y C) (G x y)

  -- The summary of a hidden region: the dependence routed through it, as relations between the
  -- vertices adjacent to it. Restriction first, so direct edges between boundary vertices are not
  -- carried by the summary.
  summary : List (Vertex (Graph.shape B)) → Relation (vertex-width B)
  summary C = hide-all (vertex-width B) (restrict (fo-graph B) C) (map at C)

  initial : Config B
  initial .visible = []
  initial .hidden  = map (λ C → C , summary C) (regions (fo-graph B) (FO B))

  hidden-set : Config B → List (Vertex (Graph.shape B))
  hidden-set K = concat (map proj₁ (K .hidden))

  member-hidden : ∀ p (K : Config B) {b} → member p (hidden-set K) ≡ b →
                  any (λ CH → member p (proj₁ CH)) (K .hidden) ≡ b
  member-hidden p K hp =
    ≡-trans (≡-sym (any-map (λ C → member p C) proj₁ (K .hidden)))
            (≡-trans (≡-sym (any-concat (eq p) (map proj₁ (K .hidden)))) hp)

  visible-graph : Config B → Relation (vertex-width B)
  visible-graph K x y =
    foldr M._+ₘ_
          (when (not (member-vertex x hs) ∧ not (member-vertex y hs)) (fo-graph B x y))
          (map (λ CH → proj₂ CH x y) (K .hidden))
    where hs = hidden-set K

  _+G_ : Relation (vertex-width B) → Relation (vertex-width B) → Relation (vertex-width B)
  (G +G H) x y = G x y M.+ₘ H x y

  hide-at : Vertex (Graph.shape B) → Config B → Config B
  hide-at p K .visible = filterᵇ (λ q → not (eq p q)) (K .visible)
  hide-at p K .hidden  =
    (p ∷ concat (map proj₁ (proj₁ tp)) , hide (vertex-width B) assembled (at p)) ∷ proj₂ tp
    where
      tp = partitionᵇ (λ CH → any (λ q → adjacent (fo-graph B) (at p) (at q)) (proj₁ CH))
                      (K .hidden)
      assembled = foldr _+G_ (restrict (visible-graph K) (p ∷ [])) (map proj₂ (proj₁ tp))

  split-region : Vertex (Graph.shape B) → List (Vertex (Graph.shape B)) × Relation (vertex-width B) →
                 List (List (Vertex (Graph.shape B)) × Relation (vertex-width B))
  split-region p (C , H) =
    if member p C
    then map (λ C' → C' , summary C')
             (regions (fo-graph B) (filterᵇ (λ q → not (eq p q)) C))
    else (C , H) ∷ []

  reveal-at : Vertex (Graph.shape B) → Config B → Config B
  reveal-at p K .visible = p ∷ K .visible
  reveal-at p K .hidden  = concat (map (split-region p) (K .hidden))

private

  when-O : ∀ (b : Bool) {m n} (R : M.Matrix m n) (i : Fin m) (j : Fin n) →
           (b ≡ Bool.true → R i j ≡ two.O) → when b R i j ≡ two.O
  when-O Bool.false R i j h = ≡-refl
  when-O Bool.true  R i j h = h ≡-refl

  when-sub : ∀ (b₁ b₂ : Bool) {m n} (R : M.Matrix m n) (i : Fin m) (j : Fin n) →
             (b₁ ≡ Bool.true → b₂ ≡ Bool.true) →
             (when b₁ R i j two.⊔ when b₂ R i j) ≡ when b₂ R i j
  when-sub Bool.false b₂ R i j imp = ≡-refl
  when-sub Bool.true  b₂ R i j imp with b₂ | imp ≡-refl
  ... | Bool.true | _ = two.⊔-idem

  when-I : ∀ (b : Bool) {m n} (R : M.Matrix m n) (i : Fin m) (j : Fin n) →
           when b R i j ≡ two.I → (b ≡ Bool.true) × (R i j ≡ two.I)
  when-I Bool.true  R i j h = ≡-refl , h

  ∧-intro : ∀ {a b : Bool} → a ≡ Bool.true → b ≡ Bool.true → (a Bool.∧ b) ≡ Bool.true
  ∧-intro e₁ e₂ = ≡-cong₂ Bool._∧_ e₁ e₂

  not-false : ∀ {b : Bool} → b ≡ Bool.false → Bool.not b ≡ Bool.true
  not-false e = ≡-cong Bool.not e

  or-introl : ∀ (a b : Bool) → a ≡ Bool.true → (a ∨ b) ≡ Bool.true
  or-introl a b e = ≡-cong (_∨ b) e

  or-intror : ∀ (a b : Bool) → b ≡ Bool.true → (a ∨ b) ≡ Bool.true
  or-intror a b e = ≡-trans (≡-cong (a ∨_) e) (∨-true a)

  foldr-entryₘ : ∀ {m n} (B : M.Matrix m n) (Rs : List (M.Matrix m n)) (i : Fin m) (j : Fin n) →
                 foldr M._+ₘ_ B Rs i j ≡ foldr two._⊔_ (B i j) (map (λ R' → R' i j) Rs)
  foldr-entryₘ B []        i j = ≡-refl
  foldr-entryₘ B (R' ∷ Rs) i j = ≡-cong (R' i j two.⊔_) (foldr-entryₘ B Rs i j)

module _ {m n : ℕ} (𝒢 : Graph m n) where

  open Graph 𝒢 using (shape)

  Path : Set
  Path = Vertex shape
  open Interaction 𝒢

  private
    module HA = Hide (V 𝒢) (vertex-width 𝒢)

    at : Path → V 𝒢
    at p = inj₂ (inj₁ p)

    eq-path : Path → Path → Bool
    eq-path p q = ⌊ _≟_ {shape} p q ⌋

    eq-path-refl : ∀ (p : Path) → eq-path p p ≡ Bool.true
    eq-path-refl p with _≟_ {shape} p p
    ... | yes _  = ≡-refl
    ... | no ¬e  = ⊥-elim (¬e ≡-refl)

    eq-path-≡ : ∀ {p q : Path} → eq-path p q ≡ Bool.true → p ≡ q
    eq-path-≡ {p} {q} h with _≟_ {shape} p q
    ... | yes e = e

    ≢-eq-false : ∀ {p q : Path} → p ≢ q → eq-path p q ≡ Bool.false
    ≢-eq-false {p} {q} ¬e with _≟_ {shape} p q
    ... | no _  = ≡-refl
    ... | yes e = ⊥-elim (¬e e)

    eq-path-false-sym : ∀ {p q : Path} → eq-path p q ≡ Bool.false → eq-path q p ≡ Bool.false
    eq-path-false-sym {p} {q} h with _≟_ {shape} q p
    ... | no _  = ≡-refl
    ... | yes e with _≟_ {shape} p q
    ...   | no ¬e = ⊥-elim (¬e (≡-sym e))

  member-perm : (q : Path) {C C' : List (Path)} → C ↭ C' → member q C ≡ member q C'
  member-perm q = any-perm (eq-path q)

  restrict-forward : {G : Relation (vertex-width 𝒢)} (C : List (Path)) → Fwd 𝒢 G → Fwd 𝒢 (restrict G C)
  restrict-forward C fwd x y i j with member-vertex x C ∨ member-vertex y C
  ... | Bool.true  = fwd x y i j
  ... | Bool.false = inj₂ ⟪ S.refl {two.O} ⟫

  adjacent-sym : (G : Relation (vertex-width 𝒢)) (x y : V 𝒢) → adjacent G x y ≡ adjacent G y x
  adjacent-sym G x y = ∨-comm (nonzero (G x y)) (nonzero (G y x))

  Apart : Relation (vertex-width 𝒢) → List (Path) → List (Path) → Set
  Apart G C C' = any (λ q → any (λ q' → adjacent G (at q) (at q')) C') C ≡ Bool.false

  apart-sym : (G : Relation (vertex-width 𝒢)) {C C' : List (Path)} → Apart G C C' → Apart G C' C
  apart-sym G {C} {C'} h =
    ≡-trans (any-comm (λ q q' → adjacent G (at q) (at q')) C' C)
    (≡-trans (any-cong (λ q → any-cong (λ q' → adjacent-sym G (at q') (at q)) C') C) h)

  merge-separated : (G : Relation (vertex-width 𝒢)) (w : Path) {rs : List (List (Path))} →
                    AllPairs (Apart G) rs →
                    let tp = partitionᵇ (any (λ q → adjacent G (at w) (at q))) rs in
                    AllPairs (Apart G) ((w ∷ concat (proj₁ tp)) ∷ proj₂ tp)
  merge-separated G w {rs} sep = apart-w ∷ proj₁ (proj₂ pa)
    where
    f = any (λ q → adjacent G (at w) (at q))
    pa = partition-AllPairs {S = Apart G} f (λ {C} {C'} → apart-sym G {C} {C'}) sep
    tp = partitionᵇ f rs
    apart-w : All (Apart G (w ∷ concat (proj₁ tp))) (proj₂ tp)
    apart-w =
      All-zip (λ {C'} hf hc →
                ≡-cong₂ _∨_ hf
                  (≡-trans (any-concat (λ q → any (λ q' → adjacent G (at q) (at q')) C') (proj₁ tp))
                           (any-false hc)))
              (part₂-false f rs) (proj₂ (proj₂ pa))

  regions-separated : (G : Relation (vertex-width 𝒢)) (ws : List (Path)) → AllPairs (Apart G) (regions G ws)
  regions-separated G []       = []
  regions-separated G (w ∷ ws) = merge-separated G w (regions-separated G ws)

  record Summarised (K : Config 𝒢) : Set where
    field
      partition : (K .visible ++ hidden-set K) ↭ FO 𝒢
      canonical : map proj₁ (K .hidden) ↭↭ regions (fo-graph 𝒢) (hidden-set K)
      summaries : All (λ CH → ∀ x y (i : Fin (vertex-width 𝒢 y)) (j : Fin (vertex-width 𝒢 x)) →
                              proj₂ CH x y i j ≡ summary (proj₁ CH) x y i j)
                      (K .hidden)

  open Summarised public

  separated : {K : Config 𝒢} → Summarised K → AllPairs (Apart (fo-graph 𝒢)) (map proj₁ (K .hidden))
  separated {K} S =
    perm-AllPairs (λ {C} {C'} → apart-sym (fo-graph 𝒢) {C} {C'})
                  (λ {C} {C'} {C''} → resp C C' C'')
                  (H.sym ↭-sym (S .canonical))
                  (regions-separated (fo-graph 𝒢) (hidden-set K))
    where
    resp : (C C' C'' : List (Path)) → C ↭ C' → Apart (fo-graph 𝒢) C C'' →
           Apart (fo-graph 𝒢) C' C''
    resp C C' C'' r ap =
      ≡-trans (≡-sym (any-perm (λ q → any (λ q' → adjacent (fo-graph 𝒢) (at q) (at q')) C'') r)) ap

  regions-concat : (G : Relation (vertex-width 𝒢)) (ws : List (Path)) → concat (regions G ws) ↭ ws
  regions-concat G []       = ↭.refl
  regions-concat G (w ∷ ws) =
    ↭.prep w (↭-trans (↭-reflexive (concat-++ (proj₁ tp) (proj₂ tp)))
             (↭-trans (concat-resp (↭↭-of-↭ (partition-↭ _ (regions G ws))))
                      (regions-concat G ws)))
    where tp = partitionᵇ (any (λ q → adjacent G (at w) (at q))) (regions G ws)

  adj-p : Path → List (Path) × Relation (vertex-width 𝒢) → Bool
  adj-p p CH = any (λ q → adjacent (fo-graph 𝒢) (at p) (at q)) (proj₁ CH)

  hide-at-hidden-set : (p : Path) (K : Config 𝒢) →
                       hidden-set (hide-at p K) ↭ (p ∷ hidden-set K)
  hide-at-hidden-set p K =
    ↭.prep p
      (↭-trans (↭-reflexive (concat-++ (map proj₁ (proj₁ tp)) (map proj₁ (proj₂ tp))))
      (↭-trans (↭-reflexive (≡-cong concat (≡-sym (map-++ proj₁ (proj₁ tp) (proj₂ tp)))))
               (concat-resp (↭↭-of-↭ (map⁺ proj₁ (partition-↭ _ (K .hidden)))))))
    where tp = partitionᵇ (adj-p p) (K .hidden)

  private
    mv-mono : {C E : List (Path)} →
              (∀ q → member q C ≡ Bool.true → member q E ≡ Bool.true) →
              ∀ z → member-vertex z C ≡ Bool.true → member-vertex z E ≡ Bool.true
    mv-mono mono (inj₁ _)        ()
    mv-mono mono (inj₂ (inj₂ _)) ()
    mv-mono mono (inj₂ (inj₁ q)) h = mono q h

  restrict-sub : (G : Relation (vertex-width 𝒢)) {C E : List (Path)} →
                 (∀ q → member q C ≡ Bool.true → member q E ≡ Bool.true) →
                 ∀ x y (i : Fin (vertex-width 𝒢 y)) (j : Fin (vertex-width 𝒢 x)) →
                 (restrict G C x y i j two.⊔ restrict G E x y i j) ≡ restrict G E x y i j
  restrict-sub G {C} {E} mono x y i j =
    when-sub (member-vertex x C ∨ member-vertex y C) (member-vertex x E ∨ member-vertex y E)
             (G x y) i j imp
    where
    imp : (member-vertex x C ∨ member-vertex y C) ≡ Bool.true →
          (member-vertex x E ∨ member-vertex y E) ≡ Bool.true
    imp h with ∨-true-inv (member-vertex x C) (member-vertex y C) h
    ... | inj₁ hx = ≡-cong (_∨ member-vertex y E) (mv-mono mono x hx)
    ... | inj₂ hy = ≡-trans (≡-cong (member-vertex x E ∨_) (mv-mono mono y hy))
                            (∨-true (member-vertex x E))

  restrict-agree : (G : Relation (vertex-width 𝒢)) {C E : List (Path)} →
                   (∀ q → member q C ≡ Bool.true → member q E ≡ Bool.true) →
                   All (λ r → Prf (((z : V 𝒢) (i : Fin (vertex-width 𝒢 z)) (j : Fin (vertex-width 𝒢 r)) →
                                    restrict G E r z i j S.≈ restrict G C r z i j)
                               ∧ₚ ((z : V 𝒢) (i : Fin (vertex-width 𝒢 r)) (j : Fin (vertex-width 𝒢 z)) →
                                    restrict G E z r i j S.≈ restrict G C z r i j)))
                       (map at C)
  restrict-agree G {C} {E} mono =
    AllP.map⁺ (All-map (λ {q} hq → ⟪
      (λ z i j → ≈-of-≡ₛ (
        ≡-trans (≡-cong (λ b → when (b ∨ member-vertex z E) (G (at q) z) i j) (mono q hq))
                (≡-sym (≡-cong (λ b → when (b ∨ member-vertex z C) (G (at q) z) i j) hq)))) ,ₚ
      (λ z i j → ≈-of-≡ₛ (
        ≡-trans (≡-cong (λ b → when (member-vertex z E ∨ b) (G z (at q)) i j) (mono q hq))
        (≡-trans (≡-cong (λ b → when b (G z (at q)) i j) (∨-true (member-vertex z E)))
        (≡-sym (≡-trans (≡-cong (λ b → when (member-vertex z C ∨ b) (G z (at q)) i j) hq)
                        (≡-cong (λ b → when b (G z (at q)) i j) (∨-true (member-vertex z C)))))))) ⟫)
      (any-self eq-path-refl C))

  localise : {C E : List (Path)} →
             (∀ q → member q C ≡ Bool.true → member q E ≡ Bool.true) →
             ∀ x y (i : Fin (vertex-width 𝒢 y)) (j : Fin (vertex-width 𝒢 x)) →
             hide-all (vertex-width 𝒢) (restrict (fo-graph 𝒢) E) (map at C) x y i j ≡
             (restrict (fo-graph 𝒢) E x y i j two.⊔ summary C x y i j)
  localise {C = C} {E = E} mono x y i j =
    ≡-of-≈ₛ (HA.agree-add {G = restrict (fo-graph 𝒢) C} {G' = restrict (fo-graph 𝒢) E} (map at C)
               (λ x' y' i' j' → ≈-of-≡ₛ (restrict-sub (fo-graph 𝒢) mono x' y' i' j'))
               (restrict-agree (fo-graph 𝒢) mono)
               x y i j)

  summary-zero : {C : List (Path)} (q : Path) →
                 member q C ≡ Bool.false →
                 any (λ q' → adjacent (fo-graph 𝒢) (at q) (at q')) C ≡ Bool.false →
                 (((z : V 𝒢) (i : Fin (vertex-width 𝒢 z)) (j : Fin (vertex-width 𝒢 (at q))) →
                   summary C (at q) z i j ≡ two.O) ×
                  ((z : V 𝒢) (i : Fin (vertex-width 𝒢 (at q))) (j : Fin (vertex-width 𝒢 z)) →
                   summary C z (at q) i j ≡ two.O))
  summary-zero {C = C} q hm hadj =
    (λ z i j → ≡-of-≈ₛ (proj₁ₚ zf z i j)) , (λ z i j → ≡-of-≈ₛ (proj₂ₚ zf z i j))
    where
    adjs : All (λ q' → adjacent (fo-graph 𝒢) (at q) (at q') ≡ Bool.false) C
    adjs = any-false-All _ C hadj

    entry-row : ∀ z → member-vertex z C ≡ Bool.true →
                ∀ i j → fo-graph 𝒢 (at q) z i j ≡ two.O
    entry-row (inj₁ _)        ()
    entry-row (inj₂ (inj₂ _)) ()
    entry-row (inj₂ (inj₁ q')) hz i j =
      nonzero-O (fo-graph 𝒢 (at q) (at q'))
                (proj₁ (∨-false (nonzero (fo-graph 𝒢 (at q) (at q')))
                                (nonzero (fo-graph 𝒢 (at q') (at q)))
                                (member-All {eq = eq-path} eq-path-≡ {x = q'} adjs hz))) i j

    entry-col : ∀ z → member-vertex z C ≡ Bool.true →
                ∀ i j → fo-graph 𝒢 z (at q) i j ≡ two.O
    entry-col (inj₁ _)        ()
    entry-col (inj₂ (inj₂ _)) ()
    entry-col (inj₂ (inj₁ q')) hz i j =
      nonzero-O (fo-graph 𝒢 (at q') (at q))
                (proj₂ (∨-false (nonzero (fo-graph 𝒢 (at q) (at q')))
                                (nonzero (fo-graph 𝒢 (at q') (at q)))
                                (member-All {eq = eq-path} eq-path-≡ {x = q'} adjs hz))) i j

    base-row : (z : V 𝒢) (i : Fin (vertex-width 𝒢 z)) (j : Fin (vertex-width 𝒢 (at q))) →
               restrict (fo-graph 𝒢) C (at q) z i j ≡ two.O
    base-row z i j =
      ≡-trans (≡-cong (λ b → when (b ∨ member-vertex z C) (fo-graph 𝒢 (at q) z) i j) hm)
              (when-O (member-vertex z C) (fo-graph 𝒢 (at q) z) i j (λ hz → entry-row z hz i j))

    base-col : (z : V 𝒢) (i : Fin (vertex-width 𝒢 (at q))) (j : Fin (vertex-width 𝒢 z)) →
               restrict (fo-graph 𝒢) C z (at q) i j ≡ two.O
    base-col z i j =
      ≡-trans (≡-cong (λ b → when (member-vertex z C ∨ b) (fo-graph 𝒢 z (at q)) i j) hm)
      (≡-trans (≡-cong (λ b → when b (fo-graph 𝒢 z (at q)) i j) (∨-identityʳ (member-vertex z C)))
               (when-O (member-vertex z C) (fo-graph 𝒢 z (at q)) i j (λ hz → entry-col z hz i j)))

    zf = HA.zero-fold (map at C) (at q)
           ((λ z i j → ≈-of-≡ₛ (base-row z i j)) ,ₚ (λ z i j → ≈-of-≡ₛ (base-col z i j)))

  assemble : {E : List (Path)} (Cs : List (List (Path))) →
             All (λ C → ∀ q → member q C ≡ Bool.true → member q E ≡ Bool.true) Cs →
             AllPairs (λ C C' → Apart (fo-graph 𝒢) C' C
                              × (any (λ q → member q C) C' ≡ Bool.false)) Cs →
             ∀ x y (i : Fin (vertex-width 𝒢 y)) (j : Fin (vertex-width 𝒢 x)) →
             hide-all (vertex-width 𝒢) (restrict (fo-graph 𝒢) E) (map at (concat Cs)) x y i j ≡
             foldr two._⊔_ (restrict (fo-graph 𝒢) E x y i j)
                           (map (λ C → summary C x y i j) Cs)
  assemble []       []             []              x y i j = ≡-refl
  assemble {E = E} (C ∷ Cs) (mono ∷ monos) (shead ∷ stail) x y i j =
    ≡-trans (≡-cong (λ ws → hide-all (vertex-width 𝒢) R-E ws x y i j) (map-++ at C (concat Cs)))
    (≡-trans (≡-cong (λ H → H x y i j) (foldl-++ (hide (vertex-width 𝒢)) R-E (map at C) (map at (concat Cs))))
    (≡-trans (≡-of-≈ₛ (HA.fold-cong (map at (concat Cs)) (λ x' y' i' j' → ≈-of-≡ₛ (localise {C = C} mono x' y' i' j')) x y i j))
    (≡-trans (≡-of-≈ₛ (HA.add-inert {G = R-E} {T = summary C} (map at (concat Cs)) inert' x y i j))
    (≡-trans (≡-cong (two._⊔ summary C x y i j) (assemble Cs monos stail x y i j))
             (two.⊔-comm _ (summary C x y i j))))))
    where
    R-E = restrict (fo-graph 𝒢) E
    inert' = AllP.map⁺ (AllP.concat⁺ (All-map
              (λ {C'} (ap , ds) →
                All-zip (λ {q} ha hm → let (l , r) = summary-zero {C = C} q hm ha in
                                       ⟪ ((λ z i j → ≈-of-≡ₛ (l z i j)) ,ₚ (λ z i j → ≈-of-≡ₛ (r z i j))) ⟫)
                        (any-false-All _ C' ap) (any-false-All _ C' ds))
              shead))

  private
    foldr-entry : (B : Relation (vertex-width 𝒢)) (Gs : List (Relation (vertex-width 𝒢))) →
                  ∀ x y (i : Fin (vertex-width 𝒢 y)) (j : Fin (vertex-width 𝒢 x)) →
                  foldr _+G_ B Gs x y i j ≡
                  foldr two._⊔_ (B x y i j) (map (λ H → H x y i j) Gs)
    foldr-entry B []       x y i j = ≡-refl
    foldr-entry B (H ∷ Gs) x y i j = ≡-cong (H x y i j two.⊔_) (foldr-entry B Gs x y i j)

  blocks-⊆ : (Css : List (List (Path))) →
             All (λ C → ∀ q → member q C ≡ Bool.true → member q (concat Css) ≡ Bool.true) Css
  blocks-⊆ []         = []
  blocks-⊆ (C ∷ Css) =
    (λ q h → ≡-trans (any-++ (eq-path q) C (concat Css)) (≡-cong (_∨ member q (concat Css)) h)) ∷
    All-map (λ {C'} g q h →
              ≡-trans (any-++ (eq-path q) C (concat Css))
              (≡-trans (≡-cong (member q C ∨_) (g q h)) (∨-true (member q C))))
            (blocks-⊆ Css)

  summary-snoc : (p : Path) (C : List (Path)) →
                 ∀ x y (i : Fin (vertex-width 𝒢 y)) (j : Fin (vertex-width 𝒢 x)) →
                 summary (p ∷ C) x y i j ≡
                 hide (vertex-width 𝒢) (hide-all (vertex-width 𝒢) (restrict (fo-graph 𝒢) (p ∷ C)) (map at C)) (at p) x y i j
  summary-snoc p C x y i j =
    ≡-trans (≡-of-≈ₛ (hide-all-perm 𝒢 (restrict-forward (p ∷ C) (fo-forward 𝒢)) perm x y i j))
            (≡-cong (λ H → H x y i j)
                    (foldl-++ (hide (vertex-width 𝒢)) (restrict (fo-graph 𝒢) (p ∷ C)) (map at C) (at p ∷ [])))
    where
    perm : (at p ∷ map at C) ↭ (map at C ++ (at p ∷ []))
    perm = ↭-sym (↭-trans (shift (at p) (map at C) [])
                          (↭-reflexive (≡-cong (at p ∷_) (++-identityʳ (map at C)))))

  Distinct : List (Path) → List (Path) → Set
  Distinct C C' = (any (λ q → member q C) C' ≡ Bool.false) × (any (λ q → member q C') C ≡ Bool.false)

  private
    block-of : (q : Path) (Css : List (List (Path))) →
               member q (concat Css) ≡ Bool.true → Any (λ C → member q C ≡ Bool.true) Css
    block-of q Css h =
      any-Any (λ C → member q C) Css (≡-trans (≡-sym (any-concat (eq-path q) Css)) h)

  private
    visible-entry : (K : Config 𝒢) →
                    ∀ x y (i : Fin (vertex-width 𝒢 y)) (j : Fin (vertex-width 𝒢 x)) →
                    visible-graph K x y i j ≡
                    foldr two._⊔_
                          (when (Bool.not (member-vertex x (hidden-set K)) Bool.∧
                                 Bool.not (member-vertex y (hidden-set K)))
                                (fo-graph 𝒢 x y) i j)
                          (map (λ CH → proj₂ CH x y i j) (K .hidden))
    visible-entry K x y i j =
      ≡-trans (foldr-entryₘ _ (map (λ CH → proj₂ CH x y) (K .hidden)) i j)
              (≡-cong (foldr two._⊔_ _)
                      (≡-sym (map-∘ {g = λ R' → R' i j} {f = λ CH → proj₂ CH x y} (K .hidden))))

  merged-summary : (p : Path) (K : Config 𝒢) → Summarised K →
                   member p (hidden-set K) ≡ Bool.false →
                   AllPairs Distinct (map proj₁ (K .hidden)) →
                   let tp = partitionᵇ (adj-p p) (K .hidden) in
                   ∀ x y (i : Fin (vertex-width 𝒢 y)) (j : Fin (vertex-width 𝒢 x)) →
                   hide (vertex-width 𝒢) (foldr _+G_ (restrict (visible-graph K) (p ∷ []))
                                    (map proj₂ (proj₁ tp)))
                        (at p) x y i j
                   ≡ summary (p ∷ concat (map proj₁ (proj₁ tp))) x y i j
  merged-summary p K S hp dist x y i j =
    ≡-trans (≡-of-≈ₛ (HA.h-cong (at p) (λ x' y' i' j' → ≈-of-≡ₛ (core x' y' i' j')) x y i j))
            (≡-sym (summary-snoc p (concat Ms) x y i j))
    where
    G  = fo-graph 𝒢
    tp = partitionᵇ (adj-p p) (K .hidden)
    Ms = map proj₁ (proj₁ tp)
    C* = p ∷ concat Ms
    B = restrict (visible-graph K) (p ∷ [])

    sums-at : ∀ x' y' (i' : Fin (vertex-width 𝒢 y')) (j' : Fin (vertex-width 𝒢 x')) → List two.Two
    sums-at x' y' i' j' = map (λ C → summary C x' y' i' j') Ms

    base-agree : ∀ x' y' (i' : Fin (vertex-width 𝒢 y')) (j' : Fin (vertex-width 𝒢 x')) →
                 (B x' y' i' j' two.⊔ foldr two._⊔_ two.O (sums-at x' y' i' j'))
                 ≡ (restrict G C* x' y' i' j' two.⊔ foldr two._⊔_ two.O (sums-at x' y' i' j'))
    base-agree x' y' i' j' =
      two.I-antisym
        (λ h → [ fwd-B x' y' i' j' , two.⊔-I-inr _ ]′
                 (two.⊔-I (B x' y' i' j') (foldr two._⊔_ two.O (sums-at x' y' i' j')) h))
        (λ h → [ bwd-B x' y' i' j' , two.⊔-I-inr _ ]′
                 (two.⊔-I (restrict G C* x' y' i' j') (foldr two._⊔_ two.O (sums-at x' y' i' j')) h))
      where
      u-adj : All (λ CH → adj-p p CH ≡ Bool.false) (proj₂ tp)
      u-adj = part₂-false (adj-p p) (K .hidden)

      u-szero : All (λ CH →
                  (((z : V 𝒢) (i' : Fin (vertex-width 𝒢 z)) (j' : Fin (vertex-width 𝒢 (at p))) →
                    summary (proj₁ CH) (at p) z i' j' ≡ two.O)
                 × ((z : V 𝒢) (i' : Fin (vertex-width 𝒢 (at p))) (j' : Fin (vertex-width 𝒢 z)) →
                    summary (proj₁ CH) z (at p) i' j' ≡ two.O))) (proj₂ tp)
      u-szero = All-zip (λ {CH} hadj hm → summary-zero {C = proj₁ CH} p hm hadj) u-adj
                  (proj₂ (partition-All (adj-p p) (any-false-All _ (K .hidden)
                    (member-hidden p K hp))))

      edge-O : ∀ {C : List (Path)} → any (λ q → adjacent G (at p) (at q)) C ≡ Bool.false →
               ∀ q' → member q' C ≡ Bool.true →
               ((∀ i' j' → G (at p) (at q') i' j' ≡ two.O) × (∀ i' j' → G (at q') (at p) i' j' ≡ two.O))
      edge-O {C} hadj q' hq =
        (λ i' j' → nonzero-O (G (at p) (at q')) (proj₁ spl) i' j') ,
        (λ i' j' → nonzero-O (G (at q') (at p)) (proj₂ spl) i' j')
        where
        spl = ∨-false (nonzero (G (at p) (at q'))) (nonzero (G (at q') (at p)))
                      (member-All {eq = eq-path} eq-path-≡ {x = q'} (any-false-All _ C hadj) hq)

      hid-split : ∀ q → member q (hidden-set K) ≡ Bool.true →
                  Any (λ CH → member q (proj₁ CH) ≡ Bool.true) (proj₁ tp)
                  ⊎ Any (λ CH → member q (proj₁ CH) ≡ Bool.true) (proj₂ tp)
      hid-split q h
        with ∨-true-inv (any (λ CH → member q (proj₁ CH)) (proj₁ tp))
                        (any (λ CH → member q (proj₁ CH)) (proj₂ tp))
                        (≡-trans (≡-sym (any-++ (λ CH → member q (proj₁ CH)) (proj₁ tp) (proj₂ tp)))
                         (≡-trans (any-perm (λ CH → member q (proj₁ CH))
                                            (partition-↭ (adj-p p) (K .hidden)))
                          (≡-trans (≡-sym (any-map (λ C → member q C) proj₁ (K .hidden)))
                                   (≡-trans (≡-sym (any-concat (eq-path q) (map proj₁ (K .hidden)))) h))))
      ... | inj₁ e = inj₁ (any-Any _ (proj₁ tp) e)
      ... | inj₂ e = inj₂ (any-Any _ (proj₂ tp) e)

      summary-I : ∀ (C : List (Path)) x' y' (i' : Fin (vertex-width 𝒢 y')) (j' : Fin (vertex-width 𝒢 x')) →
             (member-vertex x' C ∨ member-vertex y' C) ≡ Bool.true →
             G x' y' i' j' ≡ two.I → summary C x' y' i' j' ≡ two.I
      summary-I C x' y' i' j' gd ge =
        ≡-trans (≡-of-≈ₛ (HA.increasing (map at C) x' y' i' j'))
                (≡-cong (two._⊔ hide-all (vertex-width 𝒢) (restrict G C) (map at C) x' y' i' j')
                        (≡-trans (≡-cong (λ b → when b (G x' y') i' j') gd) ge))

      sums-I : ∀ x' y' (i' : Fin (vertex-width 𝒢 y')) (j' : Fin (vertex-width 𝒢 x')) (b : two.Two) →
            Any (λ C → summary C x' y' i' j' ≡ two.I) Ms →
            foldr two._⊔_ b (map (λ C → summary C x' y' i' j') Ms) ≡ two.I
      sums-I x' y' i' j' b a = two.foldr-⊔-at b (AnyPr.map⁺ a)

      mv-p-≡ : ∀ z → member-vertex z (p ∷ []) ≡ Bool.true → z ≡ at p
      mv-p-≡ (inj₁ _)        ()
      mv-p-≡ (inj₂ (inj₂ _)) ()
      mv-p-≡ (inj₂ (inj₁ q)) h with ∨-true-inv (eq-path q p) Bool.false h
      ... | inj₁ e = ≡-cong at (eq-path-≡ e)
      ... | inj₂ ()

      pguard-≡ : ∀ x' y' → (member-vertex x' (p ∷ []) ∨ member-vertex y' (p ∷ [])) ≡ Bool.true →
                 (x' ≡ at p) ⊎ (y' ≡ at p)
      pguard-≡ x' y' h with ∨-true-inv (member-vertex x' (p ∷ [])) (member-vertex y' (p ∷ [])) h
      ... | inj₁ e = inj₁ (mv-p-≡ x' e)
      ... | inj₂ e = inj₂ (mv-p-≡ y' e)

      p∈C* : member p C* ≡ Bool.true
      p∈C* = or-introl (eq-path p p) (member p (concat Ms)) (eq-path-refl p)

      vis-or : ∀ x' y' (i' : Fin (vertex-width 𝒢 y')) (j' : Fin (vertex-width 𝒢 x')) →
               (x' ≡ at p) ⊎ (y' ≡ at p) → G x' y' i' j' ≡ two.I →
               restrict G C* x' y' i' j' ≡ two.I
      vis-or .(at p) y' i' j' (inj₁ ≡-refl) ge =
        ≡-trans (≡-cong (λ b → when b (G (at p) y') i' j')
                        (or-introl (member p C*) (member-vertex y' C*) p∈C*)) ge
      vis-or x' .(at p) i' j' (inj₂ ≡-refl) ge =
        ≡-trans (≡-cong (λ b → when b (G x' (at p)) i' j')
                        (or-intror (member-vertex x' C*) (member p C*) p∈C*)) ge

      stored-or : ∀ x' y' (i' : Fin (vertex-width 𝒢 y')) (j' : Fin (vertex-width 𝒢 x')) →
                  (x' ≡ at p) ⊎ (y' ≡ at p) →
                  (Any (λ CH → summary (proj₁ CH) x' y' i' j' ≡ two.I) (proj₁ tp)
                   ⊎ Any (λ CH → summary (proj₁ CH) x' y' i' j' ≡ two.I) (proj₂ tp)) →
                  (restrict G C* x' y' i' j' two.⊔ foldr two._⊔_ two.O (sums-at x' y' i' j')) ≡ two.I
      stored-or x'      y' i' j' _             (inj₁ aM) =
        two.⊔-I-inr _ (sums-I x' y' i' j' two.O (AnyPr.map⁺ aM))
      stored-or .(at p) y' i' j' (inj₁ ≡-refl) (inj₂ aU) =
        Any-contra (λ { (sI , (zr , _)) → two.O≢I (≡-trans (≡-sym (zr y' i' j')) sI) })
                   (Any-All aU u-szero)
      stored-or x' .(at p) i' j' (inj₂ ≡-refl) (inj₂ aU) =
        Any-contra (λ { (sI , (_ , zc)) → two.O≢I (≡-trans (≡-sym (zc x' i' j')) sI) })
                   (Any-All aU u-szero)

      fwd-B : ∀ x' y' (i' : Fin (vertex-width 𝒢 y')) (j' : Fin (vertex-width 𝒢 x')) →
              B x' y' i' j' ≡ two.I →
              (restrict G C* x' y' i' j' two.⊔ foldr two._⊔_ two.O (sums-at x' y' i' j')) ≡ two.I
      fwd-B x' y' i' j' h with when-I (member-vertex x' (p ∷ []) ∨ member-vertex y' (p ∷ []))
                                      (visible-graph K x' y') i' j' h
      ... | (pgt , ve)
        with two.foldr-⊔-I (when (Bool.not (member-vertex x' (hidden-set K)) Bool.∧
                                   Bool.not (member-vertex y' (hidden-set K)))
                             (G x' y') i' j')
                       (map (λ CH → proj₂ CH x' y' i' j') (K .hidden))
                       (≡-trans (≡-sym (visible-entry K x' y' i' j')) ve)
      ...   | inj₁ vb =
        two.⊔-I-inl (vis-or x' y' i' j' (pguard-≡ x' y' pgt)
                            (proj₂ (when-I (Bool.not (member-vertex x' (hidden-set K)) Bool.∧
                                            Bool.not (member-vertex y' (hidden-set K)))
                                       (G x' y') i' j' vb)))
      ...   | inj₂ aS =
        stored-or x' y' i' j' (pguard-≡ x' y' pgt)
          (AnyPr.++⁻ (proj₁ tp) (Any-resp-↭ (↭-sym (partition-↭ (adj-p p) (K .hidden)))
            (Any-map (λ (eI , inv) → ≡-trans (≡-sym (inv x' y' i' j')) eI)
                     (Any-All (AnyPr.map⁻ aS) (S .summaries)))))

      B-visible-x : ∀ y' (i' : Fin (vertex-width 𝒢 y')) (j' : Fin (vertex-width 𝒢 (at p))) →
                     member-vertex y' (hidden-set K) ≡ Bool.false → G (at p) y' i' j' ≡ two.I →
                     B (at p) y' i' j' ≡ two.I
      B-visible-x y' i' j' hy ge =
        ≡-trans (≡-cong (λ b → when b (visible-graph K (at p) y') i' j')
                        (or-introl (member p (p ∷ [])) (member-vertex y' (p ∷ []))
                                   (≡-cong (_∨ Bool.false) (eq-path-refl p))))
        (≡-trans (visible-entry K (at p) y' i' j')
                 (two.foldr-⊔-here (map (λ CH → proj₂ CH (at p) y' i' j') (K .hidden))
                   (≡-trans (≡-cong (λ b → when b (G (at p) y') i' j')
                                    (∧-intro (not-false hp) (not-false hy)))
                            ge)))

      B-visible-y : ∀ x' (i' : Fin (vertex-width 𝒢 (at p))) (j' : Fin (vertex-width 𝒢 x')) →
                     member-vertex x' (hidden-set K) ≡ Bool.false → G x' (at p) i' j' ≡ two.I →
                     B x' (at p) i' j' ≡ two.I
      B-visible-y x' i' j' hx ge =
        ≡-trans (≡-cong (λ b → when b (visible-graph K x' (at p)) i' j')
                        (or-intror (member-vertex x' (p ∷ [])) (member p (p ∷ []))
                                   (≡-cong (_∨ Bool.false) (eq-path-refl p))))
        (≡-trans (visible-entry K x' (at p) i' j')
                 (two.foldr-⊔-here (map (λ CH → proj₂ CH x' (at p) i' j') (K .hidden))
                   (≡-trans (≡-cong (λ b → when b (G x' (at p)) i' j')
                                    (∧-intro (not-false hx) (not-false hp)))
                            ge)))

      bwd-px : ∀ y' (i' : Fin (vertex-width 𝒢 y')) (j' : Fin (vertex-width 𝒢 (at p))) →
               G (at p) y' i' j' ≡ two.I →
               (B (at p) y' i' j' two.⊔ foldr two._⊔_ two.O (sums-at (at p) y' i' j')) ≡ two.I
      bwd-px (inj₁ i) i' j' ge = two.⊔-I-inl (B-visible-x (inj₁ i) i' j' ≡-refl ge)
      bwd-px (inj₂ (inj₂ r)) i' j' ge = two.⊔-I-inl (B-visible-x (inj₂ (inj₂ r)) i' j' ≡-refl ge)
      bwd-px (inj₂ (inj₁ qy)) i' j' ge =
        bool-case (member qy (hidden-set K))
          (λ hy → [ (λ aM → two.⊔-I-inr _ (sums-I (at p) (at qy) i' j' two.O
                      (AnyPr.map⁺ (Any-map (λ {CH} mem →
                        summary-I (proj₁ CH) (at p) (at qy) i' j'
                             (or-intror (member p (proj₁ CH)) (member qy (proj₁ CH)) mem) ge) aM))))
                  , (λ aU → Any-contra
                              (λ { {CH} (mem , adj) →
                                   two.O≢I (≡-trans (≡-sym (proj₁ (edge-O {C = proj₁ CH} adj qy mem) i' j'))
                                           ge) })
                              (Any-All aU u-adj)) ]′ (hid-split qy hy))
          (λ hy → two.⊔-I-inl (B-visible-x (at qy) i' j' hy ge))

      bwd-py : ∀ x' (i' : Fin (vertex-width 𝒢 (at p))) (j' : Fin (vertex-width 𝒢 x')) →
               G x' (at p) i' j' ≡ two.I →
               (B x' (at p) i' j' two.⊔ foldr two._⊔_ two.O (sums-at x' (at p) i' j')) ≡ two.I
      bwd-py (inj₁ i) i' j' ge = two.⊔-I-inl (B-visible-y (inj₁ i) i' j' ≡-refl ge)
      bwd-py (inj₂ (inj₂ r)) i' j' ge = two.⊔-I-inl (B-visible-y (inj₂ (inj₂ r)) i' j' ≡-refl ge)
      bwd-py (inj₂ (inj₁ qx)) i' j' ge =
        bool-case (member qx (hidden-set K))
          (λ hx → [ (λ aM → two.⊔-I-inr _ (sums-I (at qx) (at p) i' j' two.O
                      (AnyPr.map⁺ (Any-map (λ {CH} mem →
                        summary-I (proj₁ CH) (at qx) (at p) i' j'
                             (or-introl (member qx (proj₁ CH)) (member p (proj₁ CH)) mem) ge) aM))))
                  , (λ aU → Any-contra
                              (λ { {CH} (mem , adj) →
                                   two.O≢I (≡-trans (≡-sym (proj₂ (edge-O {C = proj₁ CH} adj qx mem) i' j'))
                                           ge) })
                              (Any-All aU u-adj)) ]′ (hid-split qx hx))
          (λ hx → two.⊔-I-inl (B-visible-y (at qx) i' j' hx ge))

      bwd-l : ∀ x' y' (i' : Fin (vertex-width 𝒢 y')) (j' : Fin (vertex-width 𝒢 x')) →
              G x' y' i' j' ≡ two.I → member-vertex x' C* ≡ Bool.true →
              (B x' y' i' j' two.⊔ foldr two._⊔_ two.O (sums-at x' y' i' j')) ≡ two.I
      bwd-l (inj₁ _) y' i' j' ge ()
      bwd-l (inj₂ (inj₂ _)) y' i' j' ge ()
      bwd-l (inj₂ (inj₁ qx)) y' i' j' ge hx with ∨-true-inv (eq-path qx p) (member qx (concat Ms)) hx
      ... | inj₂ m =
        two.⊔-I-inr _
          (sums-I (at qx) y' i' j' two.O
               (Any-map (λ {C} mem →
                           summary-I C (at qx) y' i' j' (or-introl (member qx C) (member-vertex y' C) mem) ge)
                        (block-of qx Ms m)))
      ... | inj₁ ep with eq-path-≡ {p = qx} {q = p} ep
      ...   | ≡-refl = bwd-px y' i' j' ge

      bwd-r : ∀ x' y' (i' : Fin (vertex-width 𝒢 y')) (j' : Fin (vertex-width 𝒢 x')) →
              G x' y' i' j' ≡ two.I → member-vertex y' C* ≡ Bool.true →
              (B x' y' i' j' two.⊔ foldr two._⊔_ two.O (sums-at x' y' i' j')) ≡ two.I
      bwd-r x' (inj₁ _) i' j' ge ()
      bwd-r x' (inj₂ (inj₂ _)) i' j' ge ()
      bwd-r x' (inj₂ (inj₁ qy)) i' j' ge hy with ∨-true-inv (eq-path qy p) (member qy (concat Ms)) hy
      ... | inj₂ m =
        two.⊔-I-inr _
          (sums-I x' (at qy) i' j' two.O
               (Any-map (λ {C} mem →
                           summary-I C x' (at qy) i' j' (or-intror (member-vertex x' C) (member qy C) mem) ge)
                        (block-of qy Ms m)))
      ... | inj₁ ep with eq-path-≡ {p = qy} {q = p} ep
      ...   | ≡-refl = bwd-py x' i' j' ge

      bwd-B : ∀ x' y' (i' : Fin (vertex-width 𝒢 y')) (j' : Fin (vertex-width 𝒢 x')) →
              restrict G C* x' y' i' j' ≡ two.I →
              (B x' y' i' j' two.⊔ foldr two._⊔_ two.O (sums-at x' y' i' j')) ≡ two.I
      bwd-B x' y' i' j' h with when-I (member-vertex x' C* ∨ member-vertex y' C*) (G x' y') i' j' h
      ... | (gd , ge) with ∨-true-inv (member-vertex x' C*) (member-vertex y' C*) gd
      ...   | inj₁ hx = bwd-l x' y' i' j' ge hx
      ...   | inj₂ hy = bwd-r x' y' i' j' ge hy

    base-swap : ∀ x' y' (i' : Fin (vertex-width 𝒢 y')) (j' : Fin (vertex-width 𝒢 x')) →
                foldr two._⊔_ (B x' y' i' j') (sums-at x' y' i' j') ≡
                foldr two._⊔_ (restrict G C* x' y' i' j') (sums-at x' y' i' j')
    base-swap x' y' i' j' =
      ≡-trans (two.foldr-⊔-base (B x' y' i' j') (sums-at x' y' i' j'))
      (≡-trans (base-agree x' y' i' j')
               (≡-sym (two.foldr-⊔-base (restrict G C* x' y' i' j') (sums-at x' y' i' j'))))

    maps≡ : ∀ x' y' (i' : Fin (vertex-width 𝒢 y')) (j' : Fin (vertex-width 𝒢 x')) →
            map (λ H → H x' y' i' j') (map proj₂ (proj₁ tp)) ≡ sums-at x' y' i' j'
    maps≡ x' y' i' j' =
      ≡-trans (≡-sym (map-∘ {g = λ H → H x' y' i' j'} {f = proj₂} (proj₁ tp)))
      (≡-trans (map-All-cong (All-map (λ inv → inv x' y' i' j')
                                      (proj₁ (partition-All (adj-p p) (S .summaries)))))
               (map-∘ {g = λ C → summary C x' y' i' j'} {f = proj₁} (proj₁ tp)))

    monosC* : All (λ C → ∀ q → member q C ≡ Bool.true → member q C* ≡ Bool.true) Ms
    monosC* = All-map (λ g q h → or-intror (eq-path q p) (member q (concat Ms)) (g q h)) (blocks-⊆ Ms)

    sepsMs : AllPairs (λ C C' → Apart G C' C × (any (λ q → member q C) C' ≡ Bool.false)) Ms
    sepsMs =
      AllPairs-map (λ {C} {C'} (ap , d) → (apart-sym G {C} {C'} ap , proj₁ d))
        (subst (AllPairs (λ C C' → Apart G C C' × Distinct C C'))
               (map-partition₁ proj₁ (λ C → any (λ q → adjacent G (at p) (at q)) C) (K .hidden))
               (proj₁ (partition-AllPairs {S = λ C C' → Apart G C C' × Distinct C C'}
                        (λ C → any (λ q → adjacent G (at p) (at q)) C)
                        (λ {C} {C'} (ap , (d₁ , d₂)) → (apart-sym G {C} {C'} ap , (d₂ , d₁)))
                        (AllPairs-zip (separated S) dist))))

    core : ∀ x' y' (i' : Fin (vertex-width 𝒢 y')) (j' : Fin (vertex-width 𝒢 x')) →
           foldr _+G_ B (map proj₂ (proj₁ tp)) x' y' i' j' ≡
           hide-all (vertex-width 𝒢) (restrict G C*) (map at (concat Ms)) x' y' i' j'
    core x' y' i' j' =
      ≡-trans (foldr-entry B (map proj₂ (proj₁ tp)) x' y' i' j')
      (≡-trans (≡-cong (foldr two._⊔_ (B x' y' i' j')) (maps≡ x' y' i' j'))
      (≡-trans (base-swap x' y' i' j')
               (≡-sym (assemble {E = C*} Ms monosC* sepsMs x' y' i' j'))))

  FO-distinct : AllPairs (λ q q' → eq-path q q' ≡ Bool.false) (FO 𝒢)
  FO-distinct =
    filter-AllPairs (Graph.fo 𝒢) (AllPairs-map ≢-eq-false (distinct (Graph.shape 𝒢)))

  private
    partition-distinct : (K : Config 𝒢) → (K .visible ++ hidden-set K) ↭ FO 𝒢 →
                         AllPairs (λ q q' → eq-path q q' ≡ Bool.false)
                                  (K .visible ++ hidden-set K)
    partition-distinct K part =
      AllPairs-perm (λ {q} {q'} h → eq-path-false-sym {p = q} {q = q'} h)
                    (↭-sym part) (FO-distinct)

    concat-distinct : (Css : List (List (Path))) →
                      AllPairs (λ q q' → eq-path q q' ≡ Bool.false) (concat Css) →
                      AllPairs Distinct Css
    concat-distinct []        ps = []
    concat-distinct (C ∷ Css) ps with AllPairs-++⁻ C (concat Css) ps
    ... | (_ , aCss , cross) =
      All-map
        (λ {C'} a →
          any-false (All-map (λ {q'} aq' →
                                any-false (All-map (λ {q} hb → eq-path-false-sym {p = q} {q = q'} hb)
                                                   aq'))
                             (AllP.All-swap a)) ,
          any-false (All-map (λ {q} aq → any-false aq) a))
        (AllP.All-swap (All-map AllP.concat⁻ cross))
      ∷ concat-distinct Css aCss

    visible-not-hidden : (K : Config 𝒢) → Summarised K → ∀ {p} →
                         member p (K .visible) ≡ Bool.true →
                         member p (hidden-set K) ≡ Bool.false
    visible-not-hidden K S {p} pv =
      any-false (member-All {eq = eq-path} eq-path-≡ {x = p}
                  (proj₂ (proj₂ (AllPairs-++⁻ (K .visible) (hidden-set K)
                                              (partition-distinct K (S .partition)))))
                  pv)

  summarised-distinct : (K : Config 𝒢) → Summarised K →
                        AllPairs Distinct (map proj₁ (K .hidden))
  summarised-distinct K S =
    concat-distinct (map proj₁ (K .hidden))
      (proj₁ (proj₂ (AllPairs-++⁻ (K .visible) (hidden-set K)
                                  (partition-distinct K (S .partition)))))

  hide-at-partition : (p : Path) (K : Config 𝒢) → Summarised K →
                      member p (K .visible) ≡ Bool.true →
                      (hide-at p K .visible ++ hidden-set (hide-at p K)) ↭ FO 𝒢
  hide-at-partition p K S pv =
    ↭-trans (++⁺ ↭-refl (hide-at-hidden-set p K))
    (↭-trans (shift p (hide-at p K .visible) (hidden-set K))
    (↭-trans (++⁺ (filter-out-↭ {eq = eq-path} (λ {q} {q'} e → eq-path-≡ {p = q} {q = q'} e)
                    (proj₁ (AllPairs-++⁻ (K .visible) (hidden-set K)
                                         (partition-distinct K (S .partition))))
                    pv)
                  ↭-refl)
             (S .partition)))

  hide-at-summaries : (p : Path) (K : Config 𝒢) (S : Summarised K) →
                      member p (K .visible) ≡ Bool.true →
                      All (λ CH → ∀ x y (i : Fin (vertex-width 𝒢 y)) (j : Fin (vertex-width 𝒢 x)) →
                                  proj₂ CH x y i j ≡ summary (proj₁ CH) x y i j)
                          (hide-at p K .hidden)
  hide-at-summaries p K S pv =
    merged-summary p K S (visible-not-hidden K S {p = p} pv) (summarised-distinct K S) ∷
    proj₂ (partition-All (adj-p p) (S .summaries))

  Apart-mono : {G : Relation (vertex-width 𝒢)} {C₁ C₂ C₁' C₂' : List (Path)} →
               (∀ q → member q C₁ ≡ Bool.true → member q C₁' ≡ Bool.true) →
               (∀ q → member q C₂ ≡ Bool.true → member q C₂' ≡ Bool.true) →
               Apart G C₁' C₂' → Apart G C₁ C₂
  Apart-mono {G = G} {C₁ = C₁} {C₂} {C₁'} {C₂'} m₁ m₂ ap =
    any-false (All-map
      (λ {q} mq → any-false (All-map
        (λ {q'} mq' →
          member-All {eq = eq-path} eq-path-≡ {x = q'}
            (member-All {eq = eq-path} eq-path-≡ {x = q}
               (All-map (λ h → any-false-All _ C₂' h) (any-false-All _ C₁' ap)) (m₁ q mq))
            (m₂ q' mq'))
        (any-self eq-path-refl C₂)))
      (any-self eq-path-refl C₁))

  private
    split-none : (p : Path)
                 {CHs : List (List (Path) × Relation (vertex-width 𝒢))} →
                 All (λ CH → member p (proj₁ CH) ≡ Bool.false) CHs →
                 concat (map (split-region p) CHs) ≡ CHs
    split-none p []                     = ≡-refl
    split-none p (_∷_ {C , H} h hs) rewrite h = ≡-cong ((C , H) ∷_) (split-none p hs)

  reveal-set : (p : Path)
               (CHs : List (List (Path) × Relation (vertex-width 𝒢))) →
               AllPairs (λ q q' → eq-path q q' ≡ Bool.false) (concat (map proj₁ CHs)) →
               any (λ CH → member p (proj₁ CH)) CHs ≡ Bool.true →
               (p ∷ concat (map proj₁ (concat (map (split-region p) CHs))))
               ↭ concat (map proj₁ CHs)
  reveal-set p ((C , H) ∷ CHs) ps h
    with AllPairs-++⁻ C (concat (map proj₁ CHs)) ps
  ... | (aC , aRest , cross) with member p C in e
  ...   | Bool.false =
    ↭-trans (↭-sym (shift p C (concat (map proj₁ (concat (map (split-region p) CHs))))))
            (++⁺ ↭-refl (reveal-set p CHs aRest h))
  ...   | Bool.true  =
    ↭-trans (↭-reflexive (≡-cong (λ z → p ∷ concat z) (map-++ proj₁ X Z)))
    (↭-trans (↭-reflexive (≡-cong (p ∷_) (≡-sym (concat-++ (map proj₁ X) (map proj₁ Z)))))
    (↭-trans (↭-reflexive (≡-cong₂ (λ u v → p ∷ (concat u ++ concat (map proj₁ v)))
                                   (map-proj₁-pair summary Regs)
                                   (split-none p no-p-tail)))
             (++⁺ head-perm ↭-refl)))
    where
    C∖p  = filterᵇ (λ q → Bool.not (eq-path p q)) C
    Regs = regions (fo-graph 𝒢) C∖p
    X    = map (λ C' → C' , summary C') Regs
    Z    = concat (map (split-region p) CHs)

    no-p-tail : All (λ CH → member p (proj₁ CH) ≡ Bool.false) CHs
    no-p-tail =
      any-false-All _ CHs
        (≡-trans (≡-sym (any-map (λ C' → member p C') proj₁ CHs))
          (≡-trans (≡-sym (any-concat (eq-path p) (map proj₁ CHs)))
                   (any-false (member-All {eq = eq-path} eq-path-≡ {x = p} cross e))))

    head-perm : (p ∷ concat Regs) ↭ C
    head-perm =
      ↭-trans (↭.prep p (regions-concat (fo-graph 𝒢) C∖p))
              (filter-out-↭ {eq = eq-path} (λ {q} {q'} e' → eq-path-≡ {p = q} {q = q'} e')
                            aC e)

  private
    split-summaries : (p : Path)
                      (CH : List (Path) × Relation (vertex-width 𝒢)) →
                      (∀ x y (i : Fin (vertex-width 𝒢 y)) (j : Fin (vertex-width 𝒢 x)) →
                       proj₂ CH x y i j ≡ summary (proj₁ CH) x y i j) →
                      All (λ CH' → ∀ x y (i : Fin (vertex-width 𝒢 y)) (j : Fin (vertex-width 𝒢 x)) →
                                   proj₂ CH' x y i j ≡ summary (proj₁ CH') x y i j)
                          (split-region p CH)
    split-summaries p (C , H) old with member p C
    ... | Bool.false = old ∷ []
    ... | Bool.true  =
      AllP.map⁺ (universal (λ C' x y i j → ≡-refl)
                           (regions (fo-graph 𝒢) (filterᵇ (λ q → Bool.not (eq-path p q)) C)))

  reveal-at-partition : (p : Path) (K : Config 𝒢) → Summarised K →
                        member p (hidden-set K) ≡ Bool.true →
                        (reveal-at p K .visible ++ hidden-set (reveal-at p K)) ↭ FO 𝒢
  reveal-at-partition p K S hp =
    ↭-trans (↭-sym (shift p (K .visible) (hidden-set (reveal-at p K))))
    (↭-trans (++⁺ ↭-refl
                (reveal-set p (K .hidden)
                   (proj₁ (proj₂ (AllPairs-++⁻ (K .visible) (hidden-set K)
                                               (partition-distinct K (S .partition)))))
                   (member-hidden p K hp)))
             (S .partition))

  reveal-at-summaries : (p : Path) (K : Config 𝒢) (S : Summarised K) →
                        member p (hidden-set K) ≡ Bool.true →
                        All (λ CH → ∀ x y (i : Fin (vertex-width 𝒢 y)) (j : Fin (vertex-width 𝒢 x)) →
                                    proj₂ CH x y i j ≡ summary (proj₁ CH) x y i j)
                            (reveal-at p K .hidden)
  reveal-at-summaries p K S hp =
    AllP.concat⁺ (AllP.map⁺ (All-map (λ {CH} old → split-summaries p CH old) (S .summaries)))

  private
  visible-graph-summary : (K : Config 𝒢) → Summarised K →
                          ∀ x y (i : Fin (vertex-width 𝒢 y)) (j : Fin (vertex-width 𝒢 x)) →
                          member-vertex x (hidden-set K) ≡ Bool.false →
                          member-vertex y (hidden-set K) ≡ Bool.false →
                          visible-graph K x y i j ≡
                          (fo-graph 𝒢 x y i j two.⊔ summary (hidden-set K) x y i j)
  visible-graph-summary K S x y i j hx hy =
    ≡-trans (visible-entry K x y i j)
    (≡-trans (two.foldr-⊔-base _ (map (λ CH → proj₂ CH x y i j) (K .hidden)))
             (≡-cong₂ two._⊔_ base-eq Σ-eq))
    where
    G  = fo-graph 𝒢
    Cs = map proj₁ (K .hidden)

    base-eq : when (Bool.not (member-vertex x (hidden-set K)) Bool.∧
                    Bool.not (member-vertex y (hidden-set K))) (G x y) i j
              ≡ G x y i j
    base-eq = ≡-cong (λ b → when b (G x y) i j) (∧-intro (not-false hx) (not-false hy))

    stored-eq : map (λ CH → proj₂ CH x y i j) (K .hidden) ≡ map (λ C → summary C x y i j) Cs
    stored-eq = ≡-trans (map-All-cong (All-map (λ inv → inv x y i j) (S .summaries)))
                        (map-∘ {g = λ C → summary C x y i j} {f = proj₁} (K .hidden))

    seps : AllPairs (λ C C' → Apart G C' C × (any (λ q → member q C) C' ≡ Bool.false)) Cs
    seps = AllPairs-map (λ {C} {C'} (ap , d) → (apart-sym G {C} {C'} ap , proj₁ d))
                        (AllPairs-zip (separated S) (summarised-distinct K S))

    restrict-O : restrict G (hidden-set K) x y i j ≡ two.O
    restrict-O = ≡-cong (λ b → when b (G x y) i j) (≡-cong₂ _∨_ hx hy)

    Σ-eq : foldr two._⊔_ two.O (map (λ CH → proj₂ CH x y i j) (K .hidden))
           ≡ summary (hidden-set K) x y i j
    Σ-eq =
      ≡-trans (≡-cong (foldr two._⊔_ two.O) stored-eq)
      (≡-sym (≡-trans (assemble {E = hidden-set K} Cs (blocks-⊆ Cs) seps x y i j)
             (≡-trans (two.foldr-⊔-base (restrict G (hidden-set K) x y i j)
                                        (map (λ C → summary C x y i j) Cs))
                      (≡-cong (two._⊔ foldr two._⊔_ two.O (map (λ C → summary C x y i j) Cs))
                              restrict-O))))

  hide-reveal-visible : (p : Path) (K : Config 𝒢) → Summarised K →
                        member p (K .visible) ≡ Bool.true →
                        reveal-at p (hide-at p K) .visible ↭ K .visible
  hide-reveal-visible p K S pv =
    filter-out-↭ {eq = eq-path} (λ {q} {q'} e → eq-path-≡ {p = q} {q = q'} e)
                 (proj₁ (AllPairs-++⁻ (K .visible) (hidden-set K)
                                      (partition-distinct K (S .partition))))
                 pv

  hide-reveal-hidden-set : (p : Path) (K : Config 𝒢) → Summarised K →
                           member p (K .visible) ≡ Bool.true →
                           hidden-set (reveal-at p (hide-at p K)) ↭ hidden-set K
  hide-reveal-hidden-set p K S pv =
    drop-∷ (↭-trans (reveal-set p (hide-at p K .hidden)
                      (proj₁ (proj₂ (AllPairs-++⁻ (hide-at p K .visible)
                                                  (hidden-set (hide-at p K))
                                                  (partition-distinct (hide-at p K)
                                                    (hide-at-partition p K S pv)))))
                      (or-introl _ _ (or-introl (eq-path p p) _ (eq-path-refl p))))
                    (hide-at-hidden-set p K))

  private
    hidden-not-visible : (K : Config 𝒢) → Summarised K → ∀ {p} →
                         member p (hidden-set K) ≡ Bool.true →
                         member p (K .visible) ≡ Bool.false
    hidden-not-visible K S {p} hp =
      any-false (All-map
        (λ {q} cr → eq-path-false-sym {p = q} {q = p}
                      (member-All {eq = eq-path} eq-path-≡ {x = p} cr hp))
        (proj₂ (proj₂ (AllPairs-++⁻ (K .visible) (hidden-set K) (partition-distinct K (S .partition))))))

  reveal-hide-visible : (p : Path) (K : Config 𝒢) → Summarised K →
                        member p (hidden-set K) ≡ Bool.true →
                        hide-at p (reveal-at p K) .visible ≡ K .visible
  reveal-hide-visible p K S hp =
    ≡-trans (filter-head-false (K .visible) (≡-cong Bool.not (eq-path-refl p)))
            (filter-all-true (All-map (λ h → ≡-cong Bool.not h)
               (any-false-All _ (K .visible) (hidden-not-visible K S {p = p} hp))))

  reveal-hide-hidden-set : (p : Path) (K : Config 𝒢) → Summarised K →
                           member p (hidden-set K) ≡ Bool.true →
                           hidden-set (hide-at p (reveal-at p K)) ↭ hidden-set K
  reveal-hide-hidden-set p K S hp =
    ↭-trans (hide-at-hidden-set p (reveal-at p K))
            (reveal-set p (K .hidden)
               (proj₁ (proj₂ (AllPairs-++⁻ (K .visible) (hidden-set K)
                                           (partition-distinct K (S .partition)))))
               (member-hidden p K hp))

  private
    restrict-≤ : (G : Relation (vertex-width 𝒢)) (C : List (Path)) →
                 ∀ x y (i : Fin (vertex-width 𝒢 y)) (j : Fin (vertex-width 𝒢 x)) →
                 (restrict G C x y i j two.⊔ G x y i j) ≡ G x y i j
    restrict-≤ G C x y i j with member-vertex x C ∨ member-vertex y C
    ... | Bool.true  = two.⊔-idem
    ... | Bool.false = ≡-refl

    restrict-hidden-agree : (G : Relation (vertex-width 𝒢)) (C : List (Path)) →
                            All (λ r → Prf (((z : V 𝒢) (i : Fin (vertex-width 𝒢 z)) (j : Fin (vertex-width 𝒢 r)) →
                                             G r z i j S.≈ restrict G C r z i j)
                                        ∧ₚ ((z : V 𝒢) (i : Fin (vertex-width 𝒢 r)) (j : Fin (vertex-width 𝒢 z)) →
                                             G z r i j S.≈ restrict G C z r i j)))
                                (map at C)
    restrict-hidden-agree G C =
      AllP.map⁺ (All-map (λ {q} hq → ⟪
        (λ z i j → ≈-of-≡ₛ (≡-sym (≡-cong (λ b → when b (G (at q) z) i j)
                                          (or-introl (member q C) (member-vertex z C) hq)))) ,ₚ
        (λ z i j → ≈-of-≡ₛ (≡-sym (≡-cong (λ b → when b (G z (at q)) i j)
                                          (or-intror (member-vertex z C) (member q C) hq)))) ⟫)
        (any-self eq-path-refl C))

  summaries-assemble : (K : Config 𝒢) → Summarised K →
                       ∀ x y (i : Fin (vertex-width 𝒢 y)) (j : Fin (vertex-width 𝒢 x)) →
                       member-vertex x (hidden-set K) ≡ Bool.false →
                       member-vertex y (hidden-set K) ≡ Bool.false →
                       visible-graph K x y i j ≡
                       hide-all (vertex-width 𝒢) (fo-graph 𝒢) (map at (hidden-set K)) x y i j
  summaries-assemble K S x y i j hx hy =
    ≡-trans (visible-graph-summary K S x y i j hx hy)
            (≡-sym (≡-of-≈ₛ (HA.agree-add {G = restrict (fo-graph 𝒢) (hidden-set K)} {G' = fo-graph 𝒢}
                      (map at (hidden-set K))
                      (λ x' y' i' j' → ≈-of-≡ₛ (restrict-≤ (fo-graph 𝒢) (hidden-set K) x' y' i' j'))
                      (restrict-hidden-agree (fo-graph 𝒢) (hidden-set K))
                      x y i j)))

  record _≈_ (K K' : Config 𝒢) : Set where
    field
      visible-≈ : K .visible ↭ K' .visible
      hidden-≈  : hidden-set K ↭ hidden-set K'

  open _≈_ public

  hide-reveal : (p : Path) (K : Config 𝒢) → Summarised K →
                member p (K .visible) ≡ Bool.true →
                reveal-at p (hide-at p K) ≈ K
  hide-reveal p K S pv .visible-≈ = hide-reveal-visible p K S pv
  hide-reveal p K S pv .hidden-≈  = hide-reveal-hidden-set p K S pv

  reveal-hide : (p : Path) (K : Config 𝒢) → Summarised K →
                member p (hidden-set K) ≡ Bool.true →
                hide-at p (reveal-at p K) ≈ K
  reveal-hide p K S hp .visible-≈ = ↭-reflexive (reveal-hide-visible p K S hp)
  reveal-hide p K S hp .hidden-≈  = reveal-hide-hidden-set p K S hp

  merge-region-resp : (G : Relation (vertex-width 𝒢)) (w : Vertex shape) {rss rss' : List (List (Vertex shape))} →
                      rss ↭↭ rss' → merge-region G w rss ↭↭ merge-region G w rss'
  merge-region-resp G w {rss} {rss'} p =
    H.prep (↭.prep w (concat-resp (proj₁ tp-p))) (proj₂ tp-p)
    where
    tp-p = partition-permᴿ (any (λ q → adjacent G (at w) (at q)))
                           (λ {C} {C'} pc → any-perm (λ q → adjacent G (at w) (at q)) pc)
                           p

  private
    adj : (G : Relation (vertex-width 𝒢)) (w : Vertex shape) → List (Vertex shape) → Bool
    adj G w C = any (λ q → adjacent G (at w) (at q)) C

    merge-region-filter : (G : Relation (vertex-width 𝒢)) (w : Vertex shape) (rss : List (List (Vertex shape))) →
                          merge-region G w rss ≡
                          ((w ∷ concat (filterᵇ (adj G w) rss)) ∷
                           filterᵇ (λ C → not (adj G w C)) rss)
    merge-region-filter G w rss =
      ≡-cong (λ u → (w ∷ concat (proj₁ u)) ∷ proj₂ u) (partition-filter (adj G w) rss)

  merge-region-comm : (G : Relation (vertex-width 𝒢)) (w w' : Vertex shape) (rss : List (List (Vertex shape))) →
                      merge-region G w (merge-region G w' rss) ↭↭
                      merge-region G w' (merge-region G w rss)
  merge-region-comm G w w' rss =
    subst₂ _↭↭_
      (≡-sym (≡-trans (≡-cong (merge-region G w) (merge-region-filter G w' rss))
                      (merge-region-filter G w ((w' ∷ concat F') ∷ N'))))
      (≡-sym (≡-trans (≡-cong (merge-region G w') (merge-region-filter G w rss))
                      (merge-region-filter G w' ((w ∷ concat F) ∷ N))))
      (bool-case b true-branch false-branch)
    where
    A  = adj G w
    A' = adj G w'
    F  = filterᵇ A rss
    F' = filterᵇ A' rss
    N  = filterᵇ (λ C → not (A C)) rss
    N' = filterᵇ (λ C → not (A' C)) rss

    b  = A (w' ∷ concat F')

    beq : b ≡ A' (w ∷ concat F)
    beq =
      ≡-cong₂ _∨_ (adjacent-sym G (at w) (at w'))
        (≡-trans (any-concat (λ q → adjacent G (at w) (at q)) F')
        (≡-trans (any-filterᵇ-∧ A A' rss)
        (≡-trans (any-cong (λ C → ∧-comm (A' C) (A C)) rss)
        (≡-sym (≡-trans (any-concat (λ q → adjacent G (at w') (at q)) F)
                        (any-filterᵇ-∧ A' A rss))))))

    Goal : Set
    Goal = ((w ∷ concat (filterᵇ A ((w' ∷ concat F') ∷ N'))) ∷
            filterᵇ (λ C → not (A C)) ((w' ∷ concat F') ∷ N'))
           ↭↭
           ((w' ∷ concat (filterᵇ A' ((w ∷ concat F) ∷ N))) ∷
            filterᵇ (λ C → not (A' C)) ((w ∷ concat F) ∷ N))

    untouched : filterᵇ (λ C → not (A C)) N' ↭↭ filterᵇ (λ C → not (A' C)) N
    untouched = subst (λ z → filterᵇ (λ C → not (A C)) N' ↭↭ z)
                      (filter-comm (λ C → not (A C)) (λ C → not (A' C)) rss)
                      ↭↭-refl

    true-branch : b ≡ Bool.true → Goal
    true-branch eb =
      subst₂ _↭↭_
        (≡-sym (≡-cong₂ (λ u v → (w ∷ concat u) ∷ v)
                  (filter-head-true {f = A} {x = w' ∷ concat F'} N' eb)
                  (filter-head-false {x = w' ∷ concat F'} N' (≡-cong not eb))))
        (≡-sym (≡-cong₂ (λ u v → (w' ∷ concat u) ∷ v)
                  (filter-head-true {f = A'} {x = w ∷ concat F} N (≡-trans (≡-sym beq) eb))
                  (filter-head-false {x = w ∷ concat F} N
                                     (≡-cong not (≡-trans (≡-sym beq) eb)))))
        (H.prep
          (↭.swap w w'
            (↭-trans (↭-reflexive (concat-++ F' (filterᵇ A N')))
            (↭-trans (concat-resp (↭↭-of-↭ (filter-exchange A A' rss)))
                     (↭-reflexive (≡-sym (concat-++ F (filterᵇ A' N)))))))
          untouched)

    false-branch : b ≡ Bool.false → Goal
    false-branch eb =
      subst₂ _↭↭_
        (≡-sym (≡-cong₂ (λ u v → (w ∷ concat u) ∷ v)
                  (filter-head-false {f = A} {x = w' ∷ concat F'} N' eb)
                  (filter-head-true {x = w' ∷ concat F'} N' (≡-cong not eb))))
        (≡-sym (≡-cong₂ (λ u v → (w' ∷ concat u) ∷ v)
                  (filter-head-false {f = A'} {x = w ∷ concat F} N (≡-trans (≡-sym beq) eb))
                  (filter-head-true {x = w ∷ concat F} N
                                    (≡-cong not (≡-trans (≡-sym beq) eb)))))
        (H.swap
          (↭-reflexive (≡-cong (λ z → w ∷ concat z) (filter-avoid A A' rss hb)))
          (↭-reflexive (≡-cong (λ z → w' ∷ concat z) (≡-sym (filter-avoid A' A rss hb'))))
          untouched)
      where
      hb : any (λ C → A' C ∧ A C) rss ≡ Bool.false
      hb = ≡-trans (≡-sym (≡-trans (any-concat (λ q → adjacent G (at w) (at q)) F')
                                   (any-filterᵇ-∧ A A' rss)))
                   (proj₂ (∨-false (adjacent G (at w) (at w'))
                                   (any (λ q → adjacent G (at w) (at q)) (concat F')) eb))

      hb' : any (λ C → A C ∧ A' C) rss ≡ Bool.false
      hb' = ≡-trans (any-cong (λ C → ∧-comm (A C) (A' C)) rss) hb

  regions-perm : (G : Relation (vertex-width 𝒢)) {ws ws' : List (Vertex shape)} → ws ↭ ws' →
                 regions G ws ↭↭ regions G ws'
  regions-perm G ↭.refl         = ↭↭-refl
  regions-perm G (↭.prep w p)   = merge-region-resp G w (regions-perm G p)
  regions-perm G (↭.swap {xs = ws₁} {ys = ws₂} w w' p) =
    H.trans (merge-region-resp G w (merge-region-resp G w' (regions-perm G p)))
            (merge-region-comm G w w' (regions G ws₂))
  regions-perm G (↭.trans p q)  = H.trans (regions-perm G p) (regions-perm G q)

  private
    stored≡ : map proj₁ (initial .hidden) ≡ regions (fo-graph 𝒢) (FO 𝒢)
    stored≡ = map-proj₁-pair summary (regions (fo-graph 𝒢) (FO 𝒢))

  initial-summarised : Summarised (initial)
  initial-summarised .partition =
    subst (λ z → concat z ↭ FO 𝒢) (≡-sym stored≡) (regions-concat (fo-graph 𝒢) (FO 𝒢))
  initial-summarised .canonical =
    subst (λ z → z ↭↭ regions (fo-graph 𝒢) (concat z))
          (≡-sym stored≡)
          (regions-perm (fo-graph 𝒢) (↭-sym (regions-concat (fo-graph 𝒢) (FO 𝒢))))
  initial-summarised .summaries =
    AllP.map⁺ (universal (λ C x y i j → ≡-refl) (regions (fo-graph 𝒢) (FO 𝒢)))

  hide-at-summarised : (p : Vertex shape) (K : Config 𝒢) (S : Summarised K) →
                       member p (K .visible) ≡ Bool.true →
                       Summarised (hide-at p K)
  hide-at-summarised p K S pv .partition = hide-at-partition p K S pv
  hide-at-summarised p K S pv .canonical =
    subst (λ z → z ↭↭ regions (fo-graph 𝒢) (hidden-set (hide-at p K)))
          lhs-eq
          (H.trans (merge-region-resp (fo-graph 𝒢) p (S .canonical))
                   (H.sym ↭-sym (regions-perm (fo-graph 𝒢) (hide-at-hidden-set p K))))
    where
    lhs-eq : merge-region (fo-graph 𝒢) p (map proj₁ (K .hidden)) ≡
             map proj₁ (hide-at p K .hidden)
    lhs-eq = ≡-cong₂ (λ u v → (p ∷ concat u) ∷ v)
               (map-partition₁ proj₁ (adj (fo-graph 𝒢) p) (K .hidden))
               (map-partition₂ proj₁ (adj (fo-graph 𝒢) p) (K .hidden))
  hide-at-summarised p K S pv .summaries = hide-at-summaries p K S pv

  private
    ↭↭-of-≡ : {xss yss : List (List (Vertex shape))} → xss ≡ yss → xss ↭↭ yss
    ↭↭-of-≡ ≡-refl = ↭↭-refl

    regions-⊆ : (G : Relation (vertex-width 𝒢)) (ws : List (Vertex shape)) →
                All (λ C → ∀ q → member q C ≡ Bool.true → member q ws ≡ Bool.true)
                    (regions G ws)
    regions-⊆ G ws =
      All-map (λ {C} inc q h → ≡-trans (≡-sym (member-perm q (regions-concat G ws))) (inc q h))
              (blocks-⊆ (regions G ws))

    merge-region-inert : (G : Relation (vertex-width 𝒢)) (w : Vertex shape) (X Y : List (List (Vertex shape))) →
                         All (λ C → adj G w C ≡ Bool.false) Y →
                         merge-region G w (X ++ Y) ≡ merge-region G w X ++ Y
    merge-region-inert G w X Y h =
      ≡-trans (merge-region-filter G w (X ++ Y))
      (≡-trans (≡-cong₂ (λ u v → (w ∷ concat u) ∷ v)
                 (≡-trans (filter-++ (adj G w) X Y)
                 (≡-trans (≡-cong (filterᵇ (adj G w) X ++_) (filter-none h))
                          (++-identityʳ (filterᵇ (adj G w) X))))
                 (≡-trans (filter-++ (λ C → not (adj G w C)) X Y)
                          (≡-cong (filterᵇ (λ C → not (adj G w C)) X ++_)
                                  (filter-all-true (All-map (λ e → ≡-cong not e) h)))))
               (≡-cong (_++ Y) (≡-sym (merge-region-filter G w X))))

  regions-apart : (G : Relation (vertex-width 𝒢)) (B rest : List (Vertex shape)) → Apart G B rest →
                  regions G (B ++ rest) ↭↭ (regions G B ++ regions G rest)
  regions-apart G []      rest ap = ↭↭-refl
  regions-apart G (b ∷ B) rest ap with ∨-false (any (λ q' → adjacent G (at b) (at q')) rest)
                                             (any (λ q → any (λ q' → adjacent G (at q) (at q')) rest) B)
                                             ap
  ... | (hb , hB) =
    H.trans (merge-region-resp G b (regions-apart G B rest hB))
            (↭↭-of-≡ (merge-region-inert G b (regions G B) (regions G rest)
              (All-map (λ {C} inc →
                 any-false (All-map (λ {q} mq →
                              member-All {eq = eq-path} eq-path-≡ {x = q}
                                (any-false-All _ rest hb) (inc q mq))
                            (any-self eq-path-refl C)))
                (regions-⊆ G rest))))

  private
    apart-concat : {G : Relation (vertex-width 𝒢)} {C : List (Vertex shape)} {Cs : List (List (Vertex shape))} →
                   All (Apart G C) Cs → Apart G C (concat Cs)
    apart-concat {G = G} {C} {Cs} aps =
      ≡-trans (any-cong (λ q → any-concat (λ q' → adjacent G (at q) (at q')) Cs) C)
      (≡-trans (any-comm (λ q C' → any (λ q' → adjacent G (at q) (at q')) C') C Cs)
               (any-false aps))

    regions-nonempty : (G : Relation (vertex-width 𝒢)) (ws : List (Vertex shape)) →
                       All (λ C → 1 ≤ length C) (regions G ws)
    regions-nonempty G []       = []
    regions-nonempty G (w ∷ ws) =
      s≤s z≤n ∷ proj₂ (partition-All (adj G w) (regions-nonempty G ws))

  regions-apart-concat : {G : Relation (vertex-width 𝒢)} {Cs : List (List (Vertex shape))} →
                         AllPairs (Apart G) Cs →
                         regions G (concat Cs) ↭↭ concat (map (regions G) Cs)
  regions-apart-concat {G = G}           []                    = ↭↭-refl
  regions-apart-concat {G = G} {C ∷ Cs} (aps ∷ pairs) =
    H.trans (regions-apart G C (concat Cs) (apart-concat {G = G} {C = C} {Cs = Cs} aps))
            (↭↭-++⁺ ↭↭-refl (regions-apart-concat pairs))

  blocks-one-region : (K : Config 𝒢) → Summarised K →
                      All (λ C → regions (fo-graph 𝒢) C ↭↭ (C ∷ []))
                          (map proj₁ (K .hidden))
  blocks-one-region K S = All-map (λ {C} e → one {C} e) lens1
    where
    G  = fo-graph 𝒢
    Cs = map proj₁ (K .hidden)

    perm2 : Cs ↭↭ concat (map (regions G) Cs)
    perm2 = H.trans (S .canonical) (regions-apart-concat (separated S))

    nonempty : All (λ C → 1 ≤ length C) Cs
    nonempty = perm-All (λ {C} {C'} pc h → subst (1 ≤_) (↭-length pc) h)
                        (H.sym ↭-sym (S .canonical))
                        (regions-nonempty G (hidden-set K))

    len-regions : ∀ (C : List (Vertex shape)) → 1 ≤ length C → 1 ≤ length (regions G C)
    len-regions (q ∷ C') _ = s≤s z≤n

    atleast : All (λ C → 1 ≤ length (regions G C)) Cs
    atleast = All-map (λ {C} h → len-regions C h) nonempty

    lens-eq : sum (map (λ C → length (regions G C)) Cs) ≡
              length (map (λ C → length (regions G C)) Cs)
    lens-eq =
      ≡-trans (≡-cong sum (map-∘ {g = length} {f = regions G} Cs))
      (≡-trans (≡-sym (length-concat (map (regions G) Cs)))
      (≡-trans (≡-sym (perm-length perm2))
               (≡-sym (length-map (λ C → length (regions G C)) Cs))))

    lens1 : All (λ C → length (regions G C) ≡ 1) Cs
    lens1 = AllP.map⁻ (sum-ones (AllP.map⁺ atleast) lens-eq)

    one : ∀ {C : List (Vertex shape)} → length (regions G C) ≡ 1 → regions G C ↭↭ (C ∷ [])
    one {C} e with singleton (regions G C) e
    ... | (C₀ , eq) =
      subst (_↭↭ (C ∷ [])) (≡-sym eq)
            (H.prep (↭-trans (↭-reflexive (≡-sym (++-identityʳ C₀)))
                             (subst (λ z → concat z ↭ C) eq (regions-concat G C)))
                    (H.refl []))

  reveal-at-summarised : (p : Vertex shape) (K : Config 𝒢) (S : Summarised K) →
                         member p (hidden-set K) ≡ Bool.true →
                         Summarised (reveal-at p K)
  reveal-at-summarised p K S hp .partition = reveal-at-partition p K S hp
  reveal-at-summarised p K S hp .summaries = reveal-at-summaries p K S hp
  reveal-at-summarised p K S hp .canonical =
    subst (λ z → z ↭↭ regions G (hidden-set (reveal-at p K)))
          (≡-trans (≡-cong concat (map-∘ {g = map proj₁} {f = split-region p} (K .hidden)))
                   (concat-map {f = proj₁} (map (split-region p) (K .hidden))))
          (H.trans blocks-part
          (H.trans (↭↭-of-≡ (≡-cong concat maps-eq))
          (H.trans (H.sym ↭.↭-sym (regions-apart-concat {G = G} apart-filtered))
          (H.trans (↭↭-of-≡ (≡-cong (regions G) (≡-sym (filter-concat notp Cs))))
                   (H.sym ↭.↭-sym (regions-perm G hrev))))))
    where
    G    = fo-graph 𝒢
    Cs   = map proj₁ (K .hidden)
    notp = λ q → not (eq-path p q)

    distinct-hs : AllPairs (λ q q' → eq-path q q' ≡ Bool.false) (hidden-set K)
    distinct-hs = proj₁ (proj₂ (AllPairs-++⁻ (K .visible) (hidden-set K) (partition-distinct K (S .partition))))

    hrev : hidden-set (reveal-at p K) ↭ filterᵇ notp (hidden-set K)
    hrev = drop-∷
      (↭-trans (reveal-set p (K .hidden) distinct-hs
                  (≡-trans (≡-sym (any-map (λ C → member p C) proj₁ (K .hidden)))
                           (≡-trans (≡-sym (any-concat (eq-path p) Cs)) hp)))
               (↭.↭-sym (filter-out-↭ {eq = eq-path}
                          (λ {q} {q'} e → eq-path-≡ {p = q} {q = q'} e)
                          distinct-hs hp)))

    apart-filtered : AllPairs (Apart G) (map (filterᵇ notp) Cs)
    apart-filtered =
      AllPairsP.map⁺
        (AllPairs-map (λ {C} {C'} ap →
                         Apart-mono {G = G} {C₁ = filterᵇ notp C} {C₂ = filterᵇ notp C'}
                                    {C₁' = C} {C₂' = C'}
                                    (λ q h → any-filterᵇ (eq-path q) notp C h)
                                    (λ q h → any-filterᵇ (eq-path q) notp C' h)
                                    ap)
                      (separated S))

    maps-eq : map (λ CH → regions G (filterᵇ notp (proj₁ CH))) (K .hidden) ≡
              map (regions G) (map (filterᵇ notp) Cs)
    maps-eq =
      ≡-trans (map-∘ {g = λ C → regions G (filterᵇ notp C)} {f = proj₁} (K .hidden))
              (map-∘ {g = regions G} {f = filterᵇ notp} Cs)

    split : ∀ C (H' : Relation (vertex-width 𝒢)) {b} → member p C ≡ b →
            split-region p (C , H') ≡
            (if b then map (λ C' → C' , summary C') (regions G (filterᵇ notp C)) else (C , H') ∷ [])
    split C H' e =
      ≡-cong (λ b → if b then map (λ C' → C' , summary C') (regions G (filterᵇ notp C)) else (C , H') ∷ []) e

    per-block : ∀ CH → regions G (proj₁ CH) ↭↭ (proj₁ CH ∷ []) →
                map proj₁ (split-region p CH) ↭↭ regions G (filterᵇ notp (proj₁ CH))
    per-block (C , H') one =
      bool-case (member p C)
        (λ e → ↭↭-of-≡ (≡-trans (≡-cong (map proj₁) (split C H' e))
                                (map-proj₁-pair summary (regions G (filterᵇ notp C)))))
        (λ e → subst₂ _↭↭_
                 (≡-sym (≡-cong (map proj₁) (split C H' e)))
                 (≡-sym (≡-cong (regions G)
                          (filter-all-true (All-map (λ h → ≡-cong not h)
                                                    (any-false-All _ C e)))))
                 (H.sym ↭.↭-sym one))

    blocks-part : concat (map (λ CH → map proj₁ (split-region p CH)) (K .hidden)) ↭↭
                  concat (map (λ CH → regions G (filterᵇ notp (proj₁ CH))) (K .hidden))
    blocks-part =
      concat-↭↭ (All-map (λ {CH} one → per-block CH one)
                         (AllP.map⁻ (blocks-one-region K S)))
