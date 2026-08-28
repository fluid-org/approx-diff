{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.Bool as Bool using (Bool; not; _∧_; _∨_; if_then_else_)
open import Data.Bool.ListAction using (any)
open import Data.Bool.Properties using (∨-comm; ∨-identityʳ; ∧-comm; T?)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; allFin; length; map; filter; filterᵇ; concat;
                            partitionᵇ; foldr)
import Data.List as L
open import Data.List.Properties
  using (++-identityʳ; concat-++; concat-map; foldl-++; length-map; map-++; map-∘;
         filter-all; filter-reject)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
  using (map⁺; shift; ++⁺; drop-∷; All-resp-↭; Any-resp-↭; ↭-length; ∈-resp-↭)
open import Data.List.Relation.Binary.Pointwise using ([]; _∷_)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-concat⁻; ∈-concat⁺′; ∈-map⁺; ∈-filter⁻)
open import Data.List.Relation.Unary.All using (All; []; _∷_; universal)
  renaming (map to All-map; tabulate to All-tabulate; lookup to All-lookup)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_) renaming (map to AllPairs-map)
open import Data.List.Relation.Unary.Any using (Any; any?; here; there; tail)
  renaming (map to Any-map)
open import Data.Nat using (ℕ; _≤_; z≤n; s≤s)
open import Data.Nat.ListAction using (sum)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst; subst₂)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; cong to ≡-cong; cong₂ to ≡-cong₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (⌊_⌋; Dec; does; yes; no; ¬?; _⊎-dec_; _×-dec_; toWitness; toWitnessFalse; isYes≗does;
         dec-true; dec-false)
import Data.List.Relation.Binary.Permutation.Homogeneous as H
import Data.List.Relation.Binary.Permutation.Propositional as ↭
open ↭ using (_↭_; ↭-refl; ↭-sym; ↭-trans; ↭-reflexive)
import Data.List.Relation.Unary.All.Properties as AllP
import Data.List.Relation.Unary.AllPairs.Properties as AllPairsP
import Data.List.Relation.Unary.Any.Properties as AnyPr
import Data.Fin.Properties as FinP
import Data.List.Membership.DecPropositional as DecMem
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

NonZero : ∀ {m n} → M.Matrix m n → Set
NonZero {m} {n} R = Σ (Fin m) λ i → Σ (Fin n) λ j → R i j ≡ two.I

NonZero? : ∀ {m n} (R : M.Matrix m n) → Dec (NonZero R)
NonZero? R = FinP.any? (λ i → FinP.any? (λ j → is-I? (R i j)))
  where
  is-I? : (t : two.Two) → Dec (t ≡ two.I)
  is-I? two.O = no (λ ())
  is-I? two.I = yes ≡-refl

¬T-false : ∀ {b : Bool} → ¬ (Bool.T b) → b ≡ Bool.false
¬T-false {Bool.false} h = ≡-refl
¬T-false {Bool.true}  h = ⊥-elim (h _)

does-false : ∀ {p} {P : Set p} (d : Dec P) → does d ≡ Bool.false → ¬ P
does-false d e =
  toWitnessFalse (subst (λ b → Bool.T (Bool.not b)) (≡-sym (≡-trans (isYes≗does d) e)) _)

NonZero-O : ∀ {m n} (R : M.Matrix m n) → ¬ NonZero R → ∀ i j → R i j ≡ two.O
NonZero-O R h i j with R i j in e
... | two.O = ≡-refl
... | two.I = ⊥-elim (h (i , j , e))

when : ∀ {p} {P : Set p} {m n} → Dec P → M.Matrix m n → M.Matrix m n
when (yes _) R = R
when (no _)  R = M.εₘ

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

  open DecMem (_≟_ {Graph.shape B}) public using (_∈_; _∉_; _∈?_)

  _≢?_ : (p q : Vertex (Graph.shape B)) → Dec (p ≢ q)
  p ≢? q = ¬? (_≟_ {Graph.shape B} p q)

  Adjacent : Relation (vertex-width B) → V B → V B → Set
  Adjacent G x y = NonZero (G x y) ⊎ NonZero (G y x)

  Adjacent? : (G : Relation (vertex-width B)) (x y : V B) → Dec (Adjacent G x y)
  Adjacent? G x y = NonZero? (G x y) ⊎-dec NonZero? (G y x)

  adjacent : Relation (vertex-width B) → V B → V B → Bool
  adjacent G x y = does (Adjacent? G x y)

  ¬adjacent-All : (G : Relation (vertex-width B)) (x : V B) (C : List (Vertex (Graph.shape B))) →
                  any (λ q → adjacent G x (at q)) C ≡ Bool.false →
                  All (λ q → ¬ Adjacent G x (at q)) C
  ¬adjacent-All G x C h =
    All-map (λ {q} e → does-false (Adjacent? G x (at q)) e) (any-false-All _ C h)

  ¬adjacent-any : (G : Relation (vertex-width B)) (x : V B) (C : List (Vertex (Graph.shape B))) →
                  All (λ q → ¬ Adjacent G x (at q)) C →
                  any (λ q → adjacent G x (at q)) C ≡ Bool.false
  ¬adjacent-any G x C h = any-false (All-map (λ {q} k → dec-false (Adjacent? G x (at q)) k) h)

  adjacent-O : (G : Relation (vertex-width B)) (x y : V B) → ¬ Adjacent G x y →
               (∀ i j → G x y i j ≡ two.O) × (∀ i j → G y x i j ≡ two.O)
  adjacent-O G x y h =
    (λ i j → NonZero-O (G x y) (λ k → h (inj₁ k)) i j) ,
    (λ i j → NonZero-O (G y x) (λ k → h (inj₂ k)) i j)

  merge-region : Relation (vertex-width B) → Vertex (Graph.shape B) → List (List (Vertex (Graph.shape B))) →
                 List (List (Vertex (Graph.shape B)))
  merge-region G w rss = (w ∷ concat (proj₁ tp)) ∷ proj₂ tp
    where tp = partitionᵇ (any (λ q → adjacent G (at w) (at q))) rss

  regions : Relation (vertex-width B) → List (Vertex (Graph.shape B)) → List (List (Vertex (Graph.shape B)))
  regions G []       = []
  regions G (w ∷ ws) = merge-region G w (regions G ws)

  -- The inputs and the root are never hidden, so only an interior vertex can lie in a region.
  VertexIn : V B → List (Vertex (Graph.shape B)) → Set
  VertexIn (inj₁ _)        C = ⊥
  VertexIn (inj₂ (inj₁ p)) C = p ∈ C
  VertexIn (inj₂ (inj₂ _)) C = ⊥

  _∈ᵥ?_ : (z : V B) (C : List (Vertex (Graph.shape B))) → Dec (VertexIn z C)
  inj₁ _        ∈ᵥ? C = no (λ ())
  inj₂ (inj₁ p) ∈ᵥ? C = p ∈? C
  inj₂ (inj₂ _) ∈ᵥ? C = no (λ ())

  Adj-p : Vertex (Graph.shape B) → List (Vertex (Graph.shape B)) × Relation (vertex-width B) → Set
  Adj-p p CH = Any (λ q → Adjacent (fo-graph B) (at p) (at q)) (proj₁ CH)

  adj-p? : (p : Vertex (Graph.shape B))
           (CH : List (Vertex (Graph.shape B)) × Relation (vertex-width B)) → Dec (Adj-p p CH)
  adj-p? p CH = any? (λ q → Adjacent? (fo-graph B) (at p) (at q)) (proj₁ CH)

  restrict : Relation (vertex-width B) → List (Vertex (Graph.shape B)) → Relation (vertex-width B)
  restrict G C x y = when (x ∈ᵥ? C ⊎-dec y ∈ᵥ? C) (G x y)

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

  hidden-∈ : ∀ {p} (K : Config B) → p ∈ hidden-set K → Any (λ CH → p ∈ proj₁ CH) (K .hidden)
  hidden-∈ K h = AnyPr.map⁻ (∈-concat⁻ (map proj₁ (K .hidden)) h)

  hidden-∉ : ∀ {p} (K : Config B) → p ∉ hidden-set K → All (λ CH → p ∉ proj₁ CH) (K .hidden)
  hidden-∉ K h = All-tabulate (λ m k → h (∈-concat⁺′ k (∈-map⁺ proj₁ m)))

  visible-graph : Config B → Relation (vertex-width B)
  visible-graph K x y =
    foldr M._+ₘ_
          (when (¬? (x ∈ᵥ? hs) ×-dec ¬? (y ∈ᵥ? hs)) (fo-graph B x y))
          (map (λ CH → proj₂ CH x y) (K .hidden))
    where hs = hidden-set K

  _+G_ : Relation (vertex-width B) → Relation (vertex-width B) → Relation (vertex-width B)
  (G +G H) x y = G x y M.+ₘ H x y

  hide-at : Vertex (Graph.shape B) → Config B → Config B
  hide-at p K .visible = filter (p ≢?_) (K .visible)
  hide-at p K .hidden  =
    (p ∷ concat (map proj₁ (proj₁ tp)) , hide (vertex-width B) assembled (at p)) ∷ proj₂ tp
    where
      tp = L.partition (adj-p? p) (K .hidden)
      assembled = foldr _+G_ (restrict (visible-graph K) (p ∷ [])) (map proj₂ (proj₁ tp))

  split-region : Vertex (Graph.shape B) → List (Vertex (Graph.shape B)) × Relation (vertex-width B) →
                 List (List (Vertex (Graph.shape B)) × Relation (vertex-width B))
  split-region p (C , H) with p ∈? C
  ... | yes _ = map (λ C' → C' , summary C') (regions (fo-graph B) (filter (p ≢?_) C))
  ... | no  _ = (C , H) ∷ []

  split-region-∈ : ∀ p C (H : Relation (vertex-width B)) → p ∈ C →
                   split-region p (C , H) ≡
                   map (λ C' → C' , summary C') (regions (fo-graph B) (filter (p ≢?_) C))
  split-region-∈ p C H h with p ∈? C
  ... | yes _ = ≡-refl
  ... | no ¬k = ⊥-elim (¬k h)

  split-region-∉ : ∀ p C (H : Relation (vertex-width B)) → p ∉ C →
                   split-region p (C , H) ≡ (C , H) ∷ []
  split-region-∉ p C H h with p ∈? C
  ... | yes k = ⊥-elim (h k)
  ... | no  _ = ≡-refl

  reveal-at : Vertex (Graph.shape B) → Config B → Config B
  reveal-at p K .visible = p ∷ K .visible
  reveal-at p K .hidden  = concat (map (split-region p) (K .hidden))

private

  when-yes : ∀ {p} {P : Set p} (d : Dec P) → P →
             ∀ {m n} (R : M.Matrix m n) (i : Fin m) (j : Fin n) → when d R i j ≡ R i j
  when-yes (yes _)  h R i j = ≡-refl
  when-yes (no  ¬h) h R i j = ⊥-elim (¬h h)

  when-O : ∀ {p} {P : Set p} (d : Dec P) {m n} (R : M.Matrix m n) (i : Fin m) (j : Fin n) →
           (P → R i j ≡ two.O) → when d R i j ≡ two.O
  when-O (no  _) R i j h = ≡-refl
  when-O (yes k) R i j h = h k

  when-sub : ∀ {p q} {P : Set p} {Q : Set q} (d₁ : Dec P) (d₂ : Dec Q)
             {m n} (R : M.Matrix m n) (i : Fin m) (j : Fin n) → (P → Q) →
             (when d₁ R i j two.⊔ when d₂ R i j) ≡ when d₂ R i j
  when-sub (no  _) d₂        R i j imp = ≡-refl
  when-sub (yes k) (yes _)   R i j imp = two.⊔-idem
  when-sub (yes k) (no  ¬k') R i j imp = ⊥-elim (¬k' (imp k))

  when-I : ∀ {p} {P : Set p} (d : Dec P) {m n} (R : M.Matrix m n) (i : Fin m) (j : Fin n) →
           when d R i j ≡ two.I → P × (R i j ≡ two.I)
  when-I (yes k) R i j h = k , h

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


  restrict-forward : {G : Relation (vertex-width 𝒢)} (C : List (Path)) → Fwd 𝒢 G → Fwd 𝒢 (restrict G C)
  restrict-forward {G} C fwd x y i j with x ∈ᵥ? C ⊎-dec y ∈ᵥ? C
  ... | yes _ = fwd x y i j
  ... | no  _ = inj₂ ⟪ S.refl {two.O} ⟫

  adjacent-sym : (G : Relation (vertex-width 𝒢)) (x y : V 𝒢) → adjacent G x y ≡ adjacent G y x
  adjacent-sym G x y = ∨-comm (does (NonZero? (G x y))) (does (NonZero? (G y x)))

  Apart : Relation (vertex-width 𝒢) → List (Path) → List (Path) → Set
  Apart G C C' = All (λ q → All (λ q' → ¬ Adjacent G (at q) (at q')) C') C

  apart-sym : (G : Relation (vertex-width 𝒢)) {C C' : List (Path)} → Apart G C C' → Apart G C' C
  apart-sym G h =
    All-tabulate (λ m' → All-tabulate (λ m a → All-lookup (All-lookup h m) m' ([ inj₂ , inj₁ ]′ a)))

  merge-separated : (G : Relation (vertex-width 𝒢)) (w : Path) {rs : List (List (Path))} →
                    AllPairs (Apart G) rs →
                    let tp = partitionᵇ (any (λ q → adjacent G (at w) (at q))) rs in
                    AllPairs (Apart G) ((w ∷ concat (proj₁ tp)) ∷ proj₂ tp)
  merge-separated G w {rs} sep = apart-w ∷ proj₁ (proj₂ pa)
    where
    f? = λ C → T? (any (λ q → adjacent G (at w) (at q)) C)
    pa = partition-AllPairs {S = Apart G} f? (λ {C} {C'} → apart-sym G {C} {C'}) sep
    tp = L.partition f? rs
    apart-w : All (Apart G (w ∷ concat (proj₁ tp))) (proj₂ tp)
    apart-w =
      All-zip (λ {C'} hf hc → ¬adjacent-All G (at w) C' (¬T-false hf) ∷ AllP.concat⁺ hc)
              (part₂-¬ f? rs) (proj₂ (proj₂ pa))

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
    resp C C' C'' r ap = All-resp-↭ r ap

  regions-concat : (G : Relation (vertex-width 𝒢)) (ws : List (Path)) → concat (regions G ws) ↭ ws
  regions-concat G []       = ↭.refl
  regions-concat G (w ∷ ws) =
    ↭.prep w (↭-trans (↭-reflexive (concat-++ (proj₁ tp) (proj₂ tp)))
             (↭-trans (concat-resp (↭↭-of-↭ (partition-↭ _ (regions G ws))))
                      (regions-concat G ws)))
    where tp = partitionᵇ (any (λ q → adjacent G (at w) (at q))) (regions G ws)

  hide-at-hidden-set : (p : Path) (K : Config 𝒢) →
                       hidden-set (hide-at p K) ↭ (p ∷ hidden-set K)
  hide-at-hidden-set p K =
    ↭.prep p
      (↭-trans (↭-reflexive (concat-++ (map proj₁ (proj₁ tp)) (map proj₁ (proj₂ tp))))
      (↭-trans (↭-reflexive (≡-cong concat (≡-sym (map-++ proj₁ (proj₁ tp) (proj₂ tp)))))
               (concat-resp (↭↭-of-↭ (map⁺ proj₁ (partition-↭ _ (K .hidden)))))))
    where tp = L.partition (adj-p? p) (K .hidden)

  private
    mv-mono : {C E : List (Path)} → C ⊆ E → ∀ {z} → VertexIn z C → VertexIn z E
    mv-mono mono {inj₂ (inj₁ q)} h = mono h

  restrict-sub : (G : Relation (vertex-width 𝒢)) {C E : List (Path)} → C ⊆ E →
                 ∀ x y (i : Fin (vertex-width 𝒢 y)) (j : Fin (vertex-width 𝒢 x)) →
                 (restrict G C x y i j two.⊔ restrict G E x y i j) ≡ restrict G E x y i j
  restrict-sub G {C} {E} mono x y i j =
    when-sub (x ∈ᵥ? C ⊎-dec y ∈ᵥ? C) (x ∈ᵥ? E ⊎-dec y ∈ᵥ? E) (G x y) i j
             [ (λ hx → inj₁ (mv-mono mono hx)) , (λ hy → inj₂ (mv-mono mono hy)) ]′

  restrict-agree : (G : Relation (vertex-width 𝒢)) {C E : List (Path)} → C ⊆ E →
                   All (λ r → Prf (((z : V 𝒢) (i : Fin (vertex-width 𝒢 z)) (j : Fin (vertex-width 𝒢 r)) →
                                    restrict G E r z i j S.≈ restrict G C r z i j)
                               ∧ₚ ((z : V 𝒢) (i : Fin (vertex-width 𝒢 r)) (j : Fin (vertex-width 𝒢 z)) →
                                    restrict G E z r i j S.≈ restrict G C z r i j)))
                       (map at C)
  restrict-agree G {C} {E} mono =
    AllP.map⁺ (All-map (λ {q} h → ⟪
      (λ z i j → ≈-of-≡ₛ (≡-trans (when-yes (at q ∈ᵥ? E ⊎-dec z ∈ᵥ? E) (inj₁ (mono h)) (G (at q) z) i j)
                                  (≡-sym (when-yes (at q ∈ᵥ? C ⊎-dec z ∈ᵥ? C) (inj₁ h) (G (at q) z) i j)))) ,ₚ
      (λ z i j → ≈-of-≡ₛ (≡-trans (when-yes (z ∈ᵥ? E ⊎-dec at q ∈ᵥ? E) (inj₂ (mono h)) (G z (at q)) i j)
                                  (≡-sym (when-yes (z ∈ᵥ? C ⊎-dec at q ∈ᵥ? C) (inj₂ h) (G z (at q)) i j)))) ⟫)
      (All-tabulate (λ h → h)))

  localise : {C E : List (Path)} → C ⊆ E →
             ∀ x y (i : Fin (vertex-width 𝒢 y)) (j : Fin (vertex-width 𝒢 x)) →
             hide-all (vertex-width 𝒢) (restrict (fo-graph 𝒢) E) (map at C) x y i j ≡
             (restrict (fo-graph 𝒢) E x y i j two.⊔ summary C x y i j)
  localise {C = C} {E = E} mono x y i j =
    ≡-of-≈ₛ (HA.agree-add {G = restrict (fo-graph 𝒢) C} {G' = restrict (fo-graph 𝒢) E} (map at C)
               (λ x' y' i' j' → ≈-of-≡ₛ (restrict-sub (fo-graph 𝒢) mono x' y' i' j'))
               (restrict-agree (fo-graph 𝒢) mono)
               x y i j)

  summary-zero : {C : List (Path)} (q : Path) → q ∉ C →
                 All (λ q' → ¬ Adjacent (fo-graph 𝒢) (at q) (at q')) C →
                 (((z : V 𝒢) (i : Fin (vertex-width 𝒢 z)) (j : Fin (vertex-width 𝒢 (at q))) →
                   summary C (at q) z i j ≡ two.O) ×
                  ((z : V 𝒢) (i : Fin (vertex-width 𝒢 (at q))) (j : Fin (vertex-width 𝒢 z)) →
                   summary C z (at q) i j ≡ two.O))
  summary-zero {C = C} q hm hadj =
    (λ z i j → ≡-of-≈ₛ (proj₁ₚ zf z i j)) , (λ z i j → ≡-of-≈ₛ (proj₂ₚ zf z i j))
    where
    entry-row : ∀ {z} → VertexIn z C → ∀ i j → fo-graph 𝒢 (at q) z i j ≡ two.O
    entry-row {inj₂ (inj₁ q')} hz i j =
      proj₁ (adjacent-O (fo-graph 𝒢) (at q) (at q') (All-lookup hadj hz)) i j

    entry-col : ∀ {z} → VertexIn z C → ∀ i j → fo-graph 𝒢 z (at q) i j ≡ two.O
    entry-col {inj₂ (inj₁ q')} hz i j =
      proj₂ (adjacent-O (fo-graph 𝒢) (at q) (at q') (All-lookup hadj hz)) i j

    base-row : (z : V 𝒢) (i : Fin (vertex-width 𝒢 z)) (j : Fin (vertex-width 𝒢 (at q))) →
               restrict (fo-graph 𝒢) C (at q) z i j ≡ two.O
    base-row z i j =
      when-O (at q ∈ᵥ? C ⊎-dec z ∈ᵥ? C) (fo-graph 𝒢 (at q) z) i j
             [ (λ h → ⊥-elim (hm h)) , (λ hz → entry-row hz i j) ]′

    base-col : (z : V 𝒢) (i : Fin (vertex-width 𝒢 (at q))) (j : Fin (vertex-width 𝒢 z)) →
               restrict (fo-graph 𝒢) C z (at q) i j ≡ two.O
    base-col z i j =
      when-O (z ∈ᵥ? C ⊎-dec at q ∈ᵥ? C) (fo-graph 𝒢 z (at q)) i j
             [ (λ hz → entry-col hz i j) , (λ h → ⊥-elim (hm h)) ]′

    zf = HA.zero-fold (map at C) (at q)
           ((λ z i j → ≈-of-≡ₛ (base-row z i j)) ,ₚ (λ z i j → ≈-of-≡ₛ (base-col z i j)))

  Distinct : List (Path) → List (Path) → Set
  Distinct C C' = All (_∉ C) C'

  distinct-sym : {C C' : List (Path)} → Distinct C C' → Distinct C' C
  distinct-sym d = All-tabulate (λ m k → All-lookup d k m)

  assemble : {E : List (Path)} (Cs : List (List (Path))) →
             All (_⊆ E) Cs →
             AllPairs (λ C C' → Apart (fo-graph 𝒢) C' C × Distinct C C') Cs →
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
                All-zip (λ {q} ha hm →
                          let (l , r) = summary-zero {C = C} q hm ha in
                                       ⟪ ((λ z i j → ≈-of-≡ₛ (l z i j)) ,ₚ (λ z i j → ≈-of-≡ₛ (r z i j))) ⟫)
                        ap ds)
              shead))

  private
    foldr-entry : (B : Relation (vertex-width 𝒢)) (Gs : List (Relation (vertex-width 𝒢))) →
                  ∀ x y (i : Fin (vertex-width 𝒢 y)) (j : Fin (vertex-width 𝒢 x)) →
                  foldr _+G_ B Gs x y i j ≡
                  foldr two._⊔_ (B x y i j) (map (λ H → H x y i j) Gs)
    foldr-entry B []       x y i j = ≡-refl
    foldr-entry B (H ∷ Gs) x y i j = ≡-cong (H x y i j two.⊔_) (foldr-entry B Gs x y i j)

  blocks-⊆ : (Css : List (List (Path))) → All (_⊆ concat Css) Css
  blocks-⊆ []        = []
  blocks-⊆ (C ∷ Css) = ∈-++⁺ˡ ∷ All-map (λ g {_} h → ∈-++⁺ʳ C (g h)) (blocks-⊆ Css)

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

  private
    visible-entry : (K : Config 𝒢) →
                    ∀ x y (i : Fin (vertex-width 𝒢 y)) (j : Fin (vertex-width 𝒢 x)) →
                    visible-graph K x y i j ≡
                    foldr two._⊔_
                          (when (¬? (x ∈ᵥ? hidden-set K) ×-dec ¬? (y ∈ᵥ? hidden-set K))
                                (fo-graph 𝒢 x y) i j)
                          (map (λ CH → proj₂ CH x y i j) (K .hidden))
    visible-entry K x y i j =
      ≡-trans (foldr-entryₘ _ (map (λ CH → proj₂ CH x y) (K .hidden)) i j)
              (≡-cong (foldr two._⊔_ _)
                      (≡-sym (map-∘ {g = λ R' → R' i j} {f = λ CH → proj₂ CH x y} (K .hidden))))

  merged-summary : (p : Path) (K : Config 𝒢) → Summarised K →
                   p ∉ hidden-set K →
                   AllPairs Distinct (map proj₁ (K .hidden)) →
                   let tp = L.partition (adj-p? p) (K .hidden) in
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
    tp = L.partition (adj-p? p) (K .hidden)
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
      u-adj : All (λ CH → ¬ Adj-p p CH) (proj₂ tp)
      u-adj = part₂-¬ (adj-p? p) (K .hidden)

      u-szero : All (λ CH →
                  (((z : V 𝒢) (i' : Fin (vertex-width 𝒢 z)) (j' : Fin (vertex-width 𝒢 (at p))) →
                    summary (proj₁ CH) (at p) z i' j' ≡ two.O)
                 × ((z : V 𝒢) (i' : Fin (vertex-width 𝒢 (at p))) (j' : Fin (vertex-width 𝒢 z)) →
                    summary (proj₁ CH) z (at p) i' j' ≡ two.O))) (proj₂ tp)
      u-szero = All-zip (λ {CH} hadj hm →
                          summary-zero {C = proj₁ CH} p hm (AllP.¬Any⇒All¬ (proj₁ CH) hadj))
                        u-adj
                  (proj₂ (partition-All (adj-p? p) (hidden-∉ K hp)))

      edge-O : ∀ {C : List (Path)} → All (λ q → ¬ Adjacent G (at p) (at q)) C →
               ∀ q' → q' ∈ C →
               ((∀ i' j' → G (at p) (at q') i' j' ≡ two.O) × (∀ i' j' → G (at q') (at p) i' j' ≡ two.O))
      edge-O {C} hadj q' hq =
        adjacent-O G (at p) (at q') (All-lookup hadj hq)

      hid-split : ∀ {q} → q ∈ hidden-set K →
                  Any (λ CH → q ∈ proj₁ CH) (proj₁ tp) ⊎ Any (λ CH → q ∈ proj₁ CH) (proj₂ tp)
      hid-split h =
        AnyPr.++⁻ (proj₁ tp) (Any-resp-↭ (↭-sym (partition-↭ (adj-p? p) (K .hidden))) (hidden-∈ K h))

      summary-I : ∀ (C : List (Path)) x' y' (i' : Fin (vertex-width 𝒢 y')) (j' : Fin (vertex-width 𝒢 x')) →
             VertexIn x' C ⊎ VertexIn y' C →
             G x' y' i' j' ≡ two.I → summary C x' y' i' j' ≡ two.I
      summary-I C x' y' i' j' gd ge =
        ≡-trans (≡-of-≈ₛ (HA.increasing (map at C) x' y' i' j'))
                (≡-cong (two._⊔ hide-all (vertex-width 𝒢) (restrict G C) (map at C) x' y' i' j')
                        (≡-trans (when-yes (x' ∈ᵥ? C ⊎-dec y' ∈ᵥ? C) gd (G x' y') i' j') ge))

      sums-I : ∀ x' y' (i' : Fin (vertex-width 𝒢 y')) (j' : Fin (vertex-width 𝒢 x')) (b : two.Two) →
            Any (λ C → summary C x' y' i' j' ≡ two.I) Ms →
            foldr two._⊔_ b (map (λ C → summary C x' y' i' j') Ms) ≡ two.I
      sums-I x' y' i' j' b a = two.foldr-⊔-at b (AnyPr.map⁺ a)

      mv-p-≡ : ∀ {z} → VertexIn z (p ∷ []) → z ≡ at p
      mv-p-≡ {inj₂ (inj₁ q)} (here ≡-refl) = ≡-refl

      pguard-≡ : ∀ x' y' → VertexIn x' (p ∷ []) ⊎ VertexIn y' (p ∷ []) →
                 (x' ≡ at p) ⊎ (y' ≡ at p)
      pguard-≡ x' y' = [ (λ e → inj₁ (mv-p-≡ e)) , (λ e → inj₂ (mv-p-≡ e)) ]′

      p∈C* : VertexIn (at p) C*
      p∈C* = here ≡-refl

      vis-or : ∀ x' y' (i' : Fin (vertex-width 𝒢 y')) (j' : Fin (vertex-width 𝒢 x')) →
               (x' ≡ at p) ⊎ (y' ≡ at p) → G x' y' i' j' ≡ two.I →
               restrict G C* x' y' i' j' ≡ two.I
      vis-or .(at p) y' i' j' (inj₁ ≡-refl) ge =
        ≡-trans (when-yes (at p ∈ᵥ? C* ⊎-dec y' ∈ᵥ? C*) (inj₁ p∈C*) (G (at p) y') i' j') ge
      vis-or x' .(at p) i' j' (inj₂ ≡-refl) ge =
        ≡-trans (when-yes (x' ∈ᵥ? C* ⊎-dec at p ∈ᵥ? C*) (inj₂ p∈C*) (G x' (at p)) i' j') ge

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
      fwd-B x' y' i' j' h
        with when-I (x' ∈ᵥ? (p ∷ []) ⊎-dec y' ∈ᵥ? (p ∷ [])) (visible-graph K x' y') i' j' h
      ... | (pgt , ve)
        with two.foldr-⊔-I (when (¬? (x' ∈ᵥ? hidden-set K) ×-dec ¬? (y' ∈ᵥ? hidden-set K))
                             (G x' y') i' j')
                       (map (λ CH → proj₂ CH x' y' i' j') (K .hidden))
                       (≡-trans (≡-sym (visible-entry K x' y' i' j')) ve)
      ...   | inj₁ vb =
        two.⊔-I-inl (vis-or x' y' i' j' (pguard-≡ x' y' pgt)
                            (proj₂ (when-I (¬? (x' ∈ᵥ? hidden-set K) ×-dec ¬? (y' ∈ᵥ? hidden-set K))
                                       (G x' y') i' j' vb)))
      ...   | inj₂ aS =
        stored-or x' y' i' j' (pguard-≡ x' y' pgt)
          (AnyPr.++⁻ (proj₁ tp) (Any-resp-↭ (↭-sym (partition-↭ (adj-p? p) (K .hidden)))
            (Any-map (λ (eI , inv) → ≡-trans (≡-sym (inv x' y' i' j')) eI)
                     (Any-All (AnyPr.map⁻ aS) (S .summaries)))))

      B-visible-x : ∀ y' (i' : Fin (vertex-width 𝒢 y')) (j' : Fin (vertex-width 𝒢 (at p))) →
                     ¬ VertexIn y' (hidden-set K) → G (at p) y' i' j' ≡ two.I →
                     B (at p) y' i' j' ≡ two.I
      B-visible-x y' i' j' hy ge =
        ≡-trans (when-yes (at p ∈ᵥ? (p ∷ []) ⊎-dec y' ∈ᵥ? (p ∷ [])) (inj₁ (here ≡-refl))
                          (visible-graph K (at p) y') i' j')
        (≡-trans (visible-entry K (at p) y' i' j')
                 (two.foldr-⊔-here (map (λ CH → proj₂ CH (at p) y' i' j') (K .hidden))
                   (≡-trans (when-yes (¬? (at p ∈ᵥ? hidden-set K) ×-dec ¬? (y' ∈ᵥ? hidden-set K))
                                      (hp , hy) (G (at p) y') i' j') ge)))

      B-visible-y : ∀ x' (i' : Fin (vertex-width 𝒢 (at p))) (j' : Fin (vertex-width 𝒢 x')) →
                     ¬ VertexIn x' (hidden-set K) → G x' (at p) i' j' ≡ two.I →
                     B x' (at p) i' j' ≡ two.I
      B-visible-y x' i' j' hx ge =
        ≡-trans (when-yes (x' ∈ᵥ? (p ∷ []) ⊎-dec at p ∈ᵥ? (p ∷ [])) (inj₂ (here ≡-refl))
                          (visible-graph K x' (at p)) i' j')
        (≡-trans (visible-entry K x' (at p) i' j')
                 (two.foldr-⊔-here (map (λ CH → proj₂ CH x' (at p) i' j') (K .hidden))
                   (≡-trans (when-yes (¬? (x' ∈ᵥ? hidden-set K) ×-dec ¬? (at p ∈ᵥ? hidden-set K))
                                      (hx , hp) (G x' (at p)) i' j') ge)))

      bwd-px : ∀ y' (i' : Fin (vertex-width 𝒢 y')) (j' : Fin (vertex-width 𝒢 (at p))) →
               G (at p) y' i' j' ≡ two.I →
               (B (at p) y' i' j' two.⊔ foldr two._⊔_ two.O (sums-at (at p) y' i' j')) ≡ two.I
      bwd-px (inj₁ i) i' j' ge = two.⊔-I-inl (B-visible-x (inj₁ i) i' j' (λ ()) ge)
      bwd-px (inj₂ (inj₂ r)) i' j' ge = two.⊔-I-inl (B-visible-x (inj₂ (inj₂ r)) i' j' (λ ()) ge)
      bwd-px (inj₂ (inj₁ qy)) i' j' ge =
        dec-case (qy ∈? hidden-set K)
          (λ hy → [ (λ aM → two.⊔-I-inr _ (sums-I (at p) (at qy) i' j' two.O
                      (AnyPr.map⁺ (Any-map (λ {CH} mem →
                        summary-I (proj₁ CH) (at p) (at qy) i' j'
                             (inj₂ mem) ge) aM))))
                  , (λ aU → Any-contra
                              (λ { {CH} (mem , adj) →
                                   two.O≢I (≡-trans (≡-sym (proj₁ (edge-O {C = proj₁ CH} (AllP.¬Any⇒All¬ (proj₁ CH) adj) qy mem) i' j'))
                                           ge) })
                              (Any-All aU u-adj)) ]′ (hid-split hy))
          (λ hy → two.⊔-I-inl (B-visible-x (at qy) i' j' hy ge))

      bwd-py : ∀ x' (i' : Fin (vertex-width 𝒢 (at p))) (j' : Fin (vertex-width 𝒢 x')) →
               G x' (at p) i' j' ≡ two.I →
               (B x' (at p) i' j' two.⊔ foldr two._⊔_ two.O (sums-at x' (at p) i' j')) ≡ two.I
      bwd-py (inj₁ i) i' j' ge = two.⊔-I-inl (B-visible-y (inj₁ i) i' j' (λ ()) ge)
      bwd-py (inj₂ (inj₂ r)) i' j' ge = two.⊔-I-inl (B-visible-y (inj₂ (inj₂ r)) i' j' (λ ()) ge)
      bwd-py (inj₂ (inj₁ qx)) i' j' ge =
        dec-case (qx ∈? hidden-set K)
          (λ hx → [ (λ aM → two.⊔-I-inr _ (sums-I (at qx) (at p) i' j' two.O
                      (AnyPr.map⁺ (Any-map (λ {CH} mem →
                        summary-I (proj₁ CH) (at qx) (at p) i' j'
                             (inj₁ mem) ge) aM))))
                  , (λ aU → Any-contra
                              (λ { {CH} (mem , adj) →
                                   two.O≢I (≡-trans (≡-sym (proj₂ (edge-O {C = proj₁ CH} (AllP.¬Any⇒All¬ (proj₁ CH) adj) qx mem) i' j'))
                                           ge) })
                              (Any-All aU u-adj)) ]′ (hid-split hx))
          (λ hx → two.⊔-I-inl (B-visible-y (at qx) i' j' hx ge))

      bwd-l : ∀ x' y' (i' : Fin (vertex-width 𝒢 y')) (j' : Fin (vertex-width 𝒢 x')) →
              G x' y' i' j' ≡ two.I → VertexIn x' C* →
              (B x' y' i' j' two.⊔ foldr two._⊔_ two.O (sums-at x' y' i' j')) ≡ two.I
      bwd-l (inj₂ (inj₁ qx)) y' i' j' ge (here ≡-refl) = bwd-px y' i' j' ge
      bwd-l (inj₂ (inj₁ qx)) y' i' j' ge (there m) =
        two.⊔-I-inr _
          (sums-I (at qx) y' i' j' two.O
               (Any-map (λ {C} mem → summary-I C (at qx) y' i' j' (inj₁ mem) ge)
                        (∈-concat⁻ Ms m)))

      bwd-r : ∀ x' y' (i' : Fin (vertex-width 𝒢 y')) (j' : Fin (vertex-width 𝒢 x')) →
              G x' y' i' j' ≡ two.I → VertexIn y' C* →
              (B x' y' i' j' two.⊔ foldr two._⊔_ two.O (sums-at x' y' i' j')) ≡ two.I
      bwd-r x' (inj₂ (inj₁ qy)) i' j' ge (here ≡-refl) = bwd-py x' i' j' ge
      bwd-r x' (inj₂ (inj₁ qy)) i' j' ge (there m) =
        two.⊔-I-inr _
          (sums-I x' (at qy) i' j' two.O
               (Any-map (λ {C} mem → summary-I C x' (at qy) i' j' (inj₂ mem) ge)
                        (∈-concat⁻ Ms m)))

      bwd-B : ∀ x' y' (i' : Fin (vertex-width 𝒢 y')) (j' : Fin (vertex-width 𝒢 x')) →
              restrict G C* x' y' i' j' ≡ two.I →
              (B x' y' i' j' two.⊔ foldr two._⊔_ two.O (sums-at x' y' i' j')) ≡ two.I
      bwd-B x' y' i' j' h with when-I (x' ∈ᵥ? C* ⊎-dec y' ∈ᵥ? C*) (G x' y') i' j' h
      ... | (inj₁ hx , ge) = bwd-l x' y' i' j' ge hx
      ... | (inj₂ hy , ge) = bwd-r x' y' i' j' ge hy

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
                                      (proj₁ (partition-All (adj-p? p) (S .summaries)))))
               (map-∘ {g = λ C → summary C x' y' i' j'} {f = proj₁} (proj₁ tp)))

    monosC* : All (_⊆ C*) Ms
    monosC* = All-map (λ g {_} h → there (g h)) (blocks-⊆ Ms)

    sepsMs : AllPairs (λ C C' → Apart G C' C × Distinct C C') Ms
    sepsMs =
      AllPairs-map (λ {C} {C'} (ap , d) → (apart-sym G {C} {C'} ap , d))
        (subst (AllPairs (λ C C' → Apart G C C' × Distinct C C'))
               (map-partition₁ proj₁ (λ C → any? (λ q → Adjacent? G (at p) (at q)) C) (K .hidden))
               (proj₁ (partition-AllPairs {S = λ C C' → Apart G C C' × Distinct C C'}
                        (λ C → any? (λ q → Adjacent? G (at p) (at q)) C)
                        (λ {C} {C'} (ap , d) → (apart-sym G {C} {C'} ap , distinct-sym d))
                        (AllPairs-zip (separated S) dist))))

    core : ∀ x' y' (i' : Fin (vertex-width 𝒢 y')) (j' : Fin (vertex-width 𝒢 x')) →
           foldr _+G_ B (map proj₂ (proj₁ tp)) x' y' i' j' ≡
           hide-all (vertex-width 𝒢) (restrict G C*) (map at (concat Ms)) x' y' i' j'
    core x' y' i' j' =
      ≡-trans (foldr-entry B (map proj₂ (proj₁ tp)) x' y' i' j')
      (≡-trans (≡-cong (foldr two._⊔_ (B x' y' i' j')) (maps≡ x' y' i' j'))
      (≡-trans (base-swap x' y' i' j')
               (≡-sym (assemble {E = C*} Ms monosC* sepsMs x' y' i' j'))))

  FO-distinct : AllPairs _≢_ (FO 𝒢)
  FO-distinct = AllPairsP.filter⁺ (λ q → T? (Graph.fo 𝒢 q)) (distinct (Graph.shape 𝒢))

  private
    partition-distinct : (K : Config 𝒢) → (K .visible ++ hidden-set K) ↭ FO 𝒢 →
                         AllPairs _≢_ (K .visible ++ hidden-set K)
    partition-distinct K part =
      AllPairs-perm (λ h e → h (≡-sym e)) (↭-sym part) FO-distinct

    concat-distinct : (Css : List (List (Path))) →
                      AllPairs _≢_ (concat Css) → AllPairs Distinct Css
    concat-distinct []        ps = []
    concat-distinct (C ∷ Css) ps with AllPairs-++⁻ C (concat Css) ps
    ... | (_ , aCss , cross) =
      All-map (λ a → All-tabulate (λ m' m → All-lookup (All-lookup a m) m' ≡-refl))
              (AllP.All-swap (All-map AllP.concat⁻ cross))
      ∷ concat-distinct Css aCss

    visible-not-hidden : (K : Config 𝒢) → Summarised K → ∀ {p} →
                         p ∈ K .visible →
                         p ∉ hidden-set K
    visible-not-hidden K S {p} pv k =
      All-lookup (All-lookup (proj₂ (proj₂ (AllPairs-++⁻ (K .visible) (hidden-set K)
                                              (partition-distinct K (S .partition)))))
                             pv)
                 k ≡-refl

  summarised-distinct : (K : Config 𝒢) → Summarised K →
                        AllPairs Distinct (map proj₁ (K .hidden))
  summarised-distinct K S =
    concat-distinct (map proj₁ (K .hidden))
      (proj₁ (proj₂ (AllPairs-++⁻ (K .visible) (hidden-set K)
                                  (partition-distinct K (S .partition)))))

  hide-at-partition : (p : Path) (K : Config 𝒢) → Summarised K →
                      p ∈ K .visible →
                      (hide-at p K .visible ++ hidden-set (hide-at p K)) ↭ FO 𝒢
  hide-at-partition p K S pv =
    ↭-trans (++⁺ ↭-refl (hide-at-hidden-set p K))
    (↭-trans (shift p (hide-at p K .visible) (hidden-set K))
    (↭-trans (++⁺ (filter-out-↭ (_≟_ {shape})
                    (proj₁ (AllPairs-++⁻ (K .visible) (hidden-set K)
                                         (partition-distinct K (S .partition))))
                    pv)
                  ↭-refl)
             (S .partition)))

  hide-at-summaries : (p : Path) (K : Config 𝒢) (S : Summarised K) →
                      p ∈ K .visible →
                      All (λ CH → ∀ x y (i : Fin (vertex-width 𝒢 y)) (j : Fin (vertex-width 𝒢 x)) →
                                  proj₂ CH x y i j ≡ summary (proj₁ CH) x y i j)
                          (hide-at p K .hidden)
  hide-at-summaries p K S pv =
    merged-summary p K S (visible-not-hidden K S {p = p} pv) (summarised-distinct K S) ∷
    proj₂ (partition-All (adj-p? p) (S .summaries))

  Apart-mono : {G : Relation (vertex-width 𝒢)} {C₁ C₂ C₁' C₂' : List (Path)} →
               C₁ ⊆ C₁' → C₂ ⊆ C₂' → Apart G C₁' C₂' → Apart G C₁ C₂
  Apart-mono m₁ m₂ ap =
    All-tabulate (λ h → All-tabulate (λ h' → All-lookup (All-lookup ap (m₁ h)) (m₂ h')))

  private
    split-none : (p : Path)
                 {CHs : List (List (Path) × Relation (vertex-width 𝒢))} →
                 All (λ CH → p ∉ proj₁ CH) CHs →
                 concat (map (split-region p) CHs) ≡ CHs
    split-none p []                     = ≡-refl
    split-none p (_∷_ {C , H} h hs) rewrite split-region-∉ p C H h =
      ≡-cong ((C , H) ∷_) (split-none p hs)

  reveal-set : (p : Path)
               (CHs : List (List (Path) × Relation (vertex-width 𝒢))) →
               AllPairs _≢_ (concat (map proj₁ CHs)) →
               Any (λ CH → p ∈ proj₁ CH) CHs →
               (p ∷ concat (map proj₁ (concat (map (split-region p) CHs))))
               ↭ concat (map proj₁ CHs)
  reveal-set p ((C , H) ∷ CHs) ps h
    with AllPairs-++⁻ C (concat (map proj₁ CHs)) ps
  ... | (aC , aRest , cross) with p ∈? C
  ...   | no ¬m =
    ↭-trans (↭-sym (shift p C (concat (map proj₁ (concat (map (split-region p) CHs))))))
            (++⁺ ↭-refl (reveal-set p CHs aRest (tail ¬m h)))
  ...   | yes m =
    ↭-trans (↭-reflexive (≡-cong (λ z → p ∷ concat z) (map-++ proj₁ X Z)))
    (↭-trans (↭-reflexive (≡-cong (p ∷_) (≡-sym (concat-++ (map proj₁ X) (map proj₁ Z)))))
    (↭-trans (↭-reflexive (≡-cong₂ (λ u v → p ∷ (concat u ++ concat (map proj₁ v)))
                                   (map-proj₁-pair summary Regs)
                                   (split-none p no-p-tail)))
             (++⁺ head-perm ↭-refl)))
    where
    C∖p  = filter (p ≢?_) C
    Regs = regions (fo-graph 𝒢) C∖p
    X    = map (λ C' → C' , summary C') Regs
    Z    = concat (map (split-region p) CHs)

    no-p-tail : All (λ CH → p ∉ proj₁ CH) CHs
    no-p-tail =
      All-tabulate (λ mCH k →
        All-lookup (All-lookup cross m) (∈-concat⁺′ k (∈-map⁺ proj₁ mCH)) ≡-refl)

    head-perm : (p ∷ concat Regs) ↭ C
    head-perm =
      ↭-trans (↭.prep p (regions-concat (fo-graph 𝒢) C∖p))
              (filter-out-↭ (_≟_ {shape}) aC m)

  private
    split-summaries : (p : Path)
                      (CH : List (Path) × Relation (vertex-width 𝒢)) →
                      (∀ x y (i : Fin (vertex-width 𝒢 y)) (j : Fin (vertex-width 𝒢 x)) →
                       proj₂ CH x y i j ≡ summary (proj₁ CH) x y i j) →
                      All (λ CH' → ∀ x y (i : Fin (vertex-width 𝒢 y)) (j : Fin (vertex-width 𝒢 x)) →
                                   proj₂ CH' x y i j ≡ summary (proj₁ CH') x y i j)
                          (split-region p CH)
    split-summaries p (C , H) old with p ∈? C
    ... | no  _ = old ∷ []
    ... | yes _ =
      AllP.map⁺ (universal (λ C' x y i j → ≡-refl)
                           (regions (fo-graph 𝒢) (filter (p ≢?_) C)))

  reveal-at-partition : (p : Path) (K : Config 𝒢) → Summarised K →
                        p ∈ hidden-set K →
                        (reveal-at p K .visible ++ hidden-set (reveal-at p K)) ↭ FO 𝒢
  reveal-at-partition p K S hp =
    ↭-trans (↭-sym (shift p (K .visible) (hidden-set (reveal-at p K))))
    (↭-trans (++⁺ ↭-refl
                (reveal-set p (K .hidden)
                   (proj₁ (proj₂ (AllPairs-++⁻ (K .visible) (hidden-set K)
                                               (partition-distinct K (S .partition)))))
                   (hidden-∈ K hp)))
             (S .partition))

  reveal-at-summaries : (p : Path) (K : Config 𝒢) (S : Summarised K) →
                        p ∈ hidden-set K →
                        All (λ CH → ∀ x y (i : Fin (vertex-width 𝒢 y)) (j : Fin (vertex-width 𝒢 x)) →
                                    proj₂ CH x y i j ≡ summary (proj₁ CH) x y i j)
                            (reveal-at p K .hidden)
  reveal-at-summaries p K S hp =
    AllP.concat⁺ (AllP.map⁺ (All-map (λ {CH} old → split-summaries p CH old) (S .summaries)))

  private
  visible-graph-summary : (K : Config 𝒢) → Summarised K →
                          ∀ x y (i : Fin (vertex-width 𝒢 y)) (j : Fin (vertex-width 𝒢 x)) →
                          ¬ VertexIn x (hidden-set K) → ¬ VertexIn y (hidden-set K) →
                          visible-graph K x y i j ≡
                          (fo-graph 𝒢 x y i j two.⊔ summary (hidden-set K) x y i j)
  visible-graph-summary K S x y i j hx hy =
    ≡-trans (visible-entry K x y i j)
    (≡-trans (two.foldr-⊔-base _ (map (λ CH → proj₂ CH x y i j) (K .hidden)))
             (≡-cong₂ two._⊔_ base-eq Σ-eq))
    where
    G  = fo-graph 𝒢
    Cs = map proj₁ (K .hidden)

    base-eq : when (¬? (x ∈ᵥ? hidden-set K) ×-dec ¬? (y ∈ᵥ? hidden-set K)) (G x y) i j ≡ G x y i j
    base-eq = when-yes (¬? (x ∈ᵥ? hidden-set K) ×-dec ¬? (y ∈ᵥ? hidden-set K)) (hx , hy) (G x y) i j

    stored-eq : map (λ CH → proj₂ CH x y i j) (K .hidden) ≡ map (λ C → summary C x y i j) Cs
    stored-eq = ≡-trans (map-All-cong (All-map (λ inv → inv x y i j) (S .summaries)))
                        (map-∘ {g = λ C → summary C x y i j} {f = proj₁} (K .hidden))

    seps : AllPairs (λ C C' → Apart G C' C × Distinct C C') Cs
    seps = AllPairs-map (λ {C} {C'} (ap , d) → (apart-sym G {C} {C'} ap , d))
                        (AllPairs-zip (separated S) (summarised-distinct K S))

    restrict-O : restrict G (hidden-set K) x y i j ≡ two.O
    restrict-O = when-O (x ∈ᵥ? hidden-set K ⊎-dec y ∈ᵥ? hidden-set K) (G x y) i j
                        [ (λ h → ⊥-elim (hx h)) , (λ h → ⊥-elim (hy h)) ]′

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
                        p ∈ K .visible →
                        reveal-at p (hide-at p K) .visible ↭ K .visible
  hide-reveal-visible p K S pv =
    filter-out-↭ (_≟_ {shape})
                 (proj₁ (AllPairs-++⁻ (K .visible) (hidden-set K)
                                      (partition-distinct K (S .partition))))
                 pv

  hide-reveal-hidden-set : (p : Path) (K : Config 𝒢) → Summarised K →
                           p ∈ K .visible →
                           hidden-set (reveal-at p (hide-at p K)) ↭ hidden-set K
  hide-reveal-hidden-set p K S pv =
    drop-∷ (↭-trans (reveal-set p (hide-at p K .hidden)
                      (proj₁ (proj₂ (AllPairs-++⁻ (hide-at p K .visible)
                                                  (hidden-set (hide-at p K))
                                                  (partition-distinct (hide-at p K)
                                                    (hide-at-partition p K S pv)))))
                      (here (here ≡-refl)))
                    (hide-at-hidden-set p K))

  private
    hidden-not-visible : (K : Config 𝒢) → Summarised K → ∀ {p} →
                         p ∈ hidden-set K →
                         p ∉ K .visible
    hidden-not-visible K S {p} hp k =
      All-lookup (All-lookup (proj₂ (proj₂ (AllPairs-++⁻ (K .visible) (hidden-set K)
                                              (partition-distinct K (S .partition)))))
                             k)
                 hp ≡-refl

  reveal-hide-visible : (p : Path) (K : Config 𝒢) → Summarised K →
                        p ∈ hidden-set K →
                        hide-at p (reveal-at p K) .visible ≡ K .visible
  reveal-hide-visible p K S hp =
    ≡-trans (filter-reject (p ≢?_) (λ k → k ≡-refl))
            (filter-all (p ≢?_)
              (All-tabulate (λ {q} m e →
                 hidden-not-visible K S {p = p} hp (subst (_∈ K .visible) (≡-sym e) m))))

  reveal-hide-hidden-set : (p : Path) (K : Config 𝒢) → Summarised K →
                           p ∈ hidden-set K →
                           hidden-set (hide-at p (reveal-at p K)) ↭ hidden-set K
  reveal-hide-hidden-set p K S hp =
    ↭-trans (hide-at-hidden-set p (reveal-at p K))
            (reveal-set p (K .hidden)
               (proj₁ (proj₂ (AllPairs-++⁻ (K .visible) (hidden-set K)
                                           (partition-distinct K (S .partition)))))
               (hidden-∈ K hp))

  private
    restrict-≤ : (G : Relation (vertex-width 𝒢)) (C : List (Path)) →
                 ∀ x y (i : Fin (vertex-width 𝒢 y)) (j : Fin (vertex-width 𝒢 x)) →
                 (restrict G C x y i j two.⊔ G x y i j) ≡ G x y i j
    restrict-≤ G C x y i j with x ∈ᵥ? C ⊎-dec y ∈ᵥ? C
    ... | yes _ = two.⊔-idem
    ... | no  _ = ≡-refl

    restrict-hidden-agree : (G : Relation (vertex-width 𝒢)) (C : List (Path)) →
                            All (λ r → Prf (((z : V 𝒢) (i : Fin (vertex-width 𝒢 z)) (j : Fin (vertex-width 𝒢 r)) →
                                             G r z i j S.≈ restrict G C r z i j)
                                        ∧ₚ ((z : V 𝒢) (i : Fin (vertex-width 𝒢 r)) (j : Fin (vertex-width 𝒢 z)) →
                                             G z r i j S.≈ restrict G C z r i j)))
                                (map at C)
    restrict-hidden-agree G C =
      AllP.map⁺ (All-map (λ {q} h → ⟪
        (λ z i j → ≈-of-≡ₛ (≡-sym (when-yes (at q ∈ᵥ? C ⊎-dec z ∈ᵥ? C) (inj₁ h) (G (at q) z) i j))) ,ₚ
        (λ z i j → ≈-of-≡ₛ (≡-sym (when-yes (z ∈ᵥ? C ⊎-dec at q ∈ᵥ? C) (inj₂ h) (G z (at q)) i j))) ⟫)
        (All-tabulate (λ h → h)))

  summaries-assemble : (K : Config 𝒢) → Summarised K →
                       ∀ x y (i : Fin (vertex-width 𝒢 y)) (j : Fin (vertex-width 𝒢 x)) →
                       ¬ VertexIn x (hidden-set K) → ¬ VertexIn y (hidden-set K) →
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
                p ∈ K .visible →
                reveal-at p (hide-at p K) ≈ K
  hide-reveal p K S pv .visible-≈ = hide-reveal-visible p K S pv
  hide-reveal p K S pv .hidden-≈  = hide-reveal-hidden-set p K S pv

  reveal-hide : (p : Path) (K : Config 𝒢) → Summarised K →
                p ∈ hidden-set K →
                hide-at p (reveal-at p K) ≈ K
  reveal-hide p K S hp .visible-≈ = ↭-reflexive (reveal-hide-visible p K S hp)
  reveal-hide p K S hp .hidden-≈  = reveal-hide-hidden-set p K S hp

  merge-region-resp : (G : Relation (vertex-width 𝒢)) (w : Vertex shape) {rss rss' : List (List (Vertex shape))} →
                      rss ↭↭ rss' → merge-region G w rss ↭↭ merge-region G w rss'
  merge-region-resp G w {rss} {rss'} p =
    H.prep (↭.prep w (concat-resp (proj₁ tp-p))) (proj₂ tp-p)
    where
    A? = λ C → T? (any (λ q → adjacent G (at w) (at q)) C)
    tp-p = partition-permᴿ A? (λ pc → subst Bool.T (any-perm _ pc))
                              (λ pc → subst Bool.T (≡-sym (any-perm _ pc))) p

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
                       p ∈ K .visible →
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
    lhs-eq =
      ≡-trans (≡-cong₂ (λ u v → (p ∷ concat u) ∷ v)
                 (map-partition₁ proj₁ A? (K .hidden)) (map-partition₂ proj₁ A? (K .hidden)))
              (≡-cong (λ u → (p ∷ concat (map proj₁ (proj₁ u))) ∷ map proj₁ (proj₂ u))
                      (partition-cong (λ CH → A? (proj₁ CH)) (adj-p? p) agree (K .hidden)))
      where
      A? = λ C → T? (adj (fo-graph 𝒢) p C)
      agree = λ CH → ≡-trans (does-T? _)
                             (≡-sym (does-any? (λ q → Adjacent? (fo-graph 𝒢) (at p) (at q))
                                               (proj₁ CH)))
  hide-at-summarised p K S pv .summaries = hide-at-summaries p K S pv

  private
    ↭↭-of-≡ : {xss yss : List (List (Vertex shape))} → xss ≡ yss → xss ↭↭ yss
    ↭↭-of-≡ ≡-refl = ↭↭-refl

    regions-⊆ : (G : Relation (vertex-width 𝒢)) (ws : List (Vertex shape)) →
                All (_⊆ ws) (regions G ws)
    regions-⊆ G ws =
      All-map (λ inc {_} h → ∈-resp-↭ (regions-concat G ws) (inc h)) (blocks-⊆ (regions G ws))

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
  regions-apart G (b ∷ B) rest (hb ∷ hB) =
    H.trans (merge-region-resp G b (regions-apart G B rest hB))
            (↭↭-of-≡ (merge-region-inert G b (regions G B) (regions G rest)
              (All-map (λ {C} inc →
                 ¬adjacent-any G (at b) C (All-tabulate (λ h → All-lookup hb (inc h))))
                (regions-⊆ G rest))))

  private
    apart-concat : {G : Relation (vertex-width 𝒢)} {C : List (Vertex shape)} {Cs : List (List (Vertex shape))} →
                   All (Apart G C) Cs → Apart G C (concat Cs)
    apart-concat aps = All-tabulate (λ m → AllP.concat⁺ (All-map (λ ap → All-lookup ap m) aps))

    regions-nonempty : (G : Relation (vertex-width 𝒢)) (ws : List (Vertex shape)) →
                       All (λ C → 1 ≤ length C) (regions G ws)
    regions-nonempty G []       = []
    regions-nonempty G (w ∷ ws) =
      s≤s z≤n ∷ proj₂ (partition-All (λ C → T? (adj G w C)) (regions-nonempty G ws))

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
                         p ∈ hidden-set K →
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
    notp = p ≢?_

    distinct-hs : AllPairs _≢_ (hidden-set K)
    distinct-hs = proj₁ (proj₂ (AllPairs-++⁻ (K .visible) (hidden-set K) (partition-distinct K (S .partition))))

    hrev : hidden-set (reveal-at p K) ↭ filter notp (hidden-set K)
    hrev = drop-∷
      (↭-trans (reveal-set p (K .hidden) distinct-hs (hidden-∈ K hp))
               (↭.↭-sym (filter-out-↭ (_≟_ {shape}) distinct-hs hp)))

    apart-filtered : AllPairs (Apart G) (map (filter notp) Cs)
    apart-filtered =
      AllPairsP.map⁺
        (AllPairs-map (λ {C} {C'} ap →
                         Apart-mono {G = G} {C₁ = filter notp C} {C₂ = filter notp C'}
                                    {C₁' = C} {C₂' = C'}
                                    (λ h → proj₁ (∈-filter⁻ notp h))
                                    (λ h → proj₁ (∈-filter⁻ notp h))
                                    ap)
                      (separated S))

    maps-eq : map (λ CH → regions G (filter notp (proj₁ CH))) (K .hidden) ≡
              map (regions G) (map (filter notp) Cs)
    maps-eq =
      ≡-trans (map-∘ {g = λ C → regions G (filter notp C)} {f = proj₁} (K .hidden))
              (map-∘ {g = regions G} {f = filter notp} Cs)

    per-block : ∀ CH → regions G (proj₁ CH) ↭↭ (proj₁ CH ∷ []) →
                map proj₁ (split-region p CH) ↭↭ regions G (filter notp (proj₁ CH))
    per-block (C , H') one =
      dec-case (p ∈? C)
        (λ k → ↭↭-of-≡ (≡-trans (≡-cong (map proj₁) (split-region-∈ p C H' k))
                                (map-proj₁-pair summary (regions G (filter notp C)))))
        (λ ¬k → subst₂ _↭↭_
                  (≡-sym (≡-cong (map proj₁) (split-region-∉ p C H' ¬k)))
                  (≡-sym (≡-cong (regions G)
                           (filter-all (p ≢?_)
                             (All-tabulate (λ {q} m e' → ¬k (subst (_∈ C) (≡-sym e') m))))))
                  (H.sym ↭.↭-sym one))

    blocks-part : concat (map (λ CH → map proj₁ (split-region p CH)) (K .hidden)) ↭↭
                  concat (map (λ CH → regions G (filter notp (proj₁ CH))) (K .hidden))
    blocks-part =
      concat-↭↭ (All-map (λ {CH} one → per-block CH one)
                         (AllP.map⁻ (blocks-one-region K S)))
