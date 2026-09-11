{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.Bool.Properties using (T?)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; allFin; length; map; mapMaybe; filter; filterᵇ; concat; foldr)
import Data.List as L
open import Data.List.Properties
  using (++-identityʳ; concat-++; concat-map; foldl-++; length-map; map-++; map-∘;
         filter-all; filter-accept; filter-reject; filter-none; filter-++; partition-defn)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
  using (map⁺; shift; ++⁺; drop-∷; All-resp-↭; Any-resp-↭; ↭-length; ∈-resp-↭)
open import Data.List.Relation.Binary.Pointwise using ([]; _∷_)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ₚ_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-concat⁻; ∈-concat⁺′; ∈-map⁺; ∈-map⁻; ∈-filter⁻)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
  renaming (map to All-map; tabulate to All-tabulate; lookup to All-lookup)
open import Data.List.Relation.Unary.AllPairs as AllPairs using (AllPairs; []; _∷_)
  renaming (map to AllPairs-map)
open import Data.List.Relation.Unary.Any using (Any; any?; here; there; tail) renaming (map to Any-map)
open import Data.Bool using (Bool; true; false; not; _∨_; if_then_else_)
open import Data.Bool.ListAction using (any)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s; _≡ᵇ_)
open import Data.Nat.ListAction using (sum)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Sum.Properties using (inj₂-injective)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst; subst₂)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; cong to ≡-cong; cong₂ to ≡-cong₂)
open import Relation.Nullary using (¬_)
open import Relation.Unary.Properties using (∁?)
open import Relation.Nullary.Decidable using (Dec; yes; no; ¬?; ⌊_⌋; _⊎-dec_; _×-dec_)
import Data.List.Relation.Binary.Permutation.Homogeneous as H
import Data.List.Relation.Binary.Permutation.Propositional as ↭
open ↭ using (_↭_; ↭-refl; ↭-sym; ↭-trans; ↭-reflexive)
import Data.List.Relation.Unary.All.Properties as AllP
import Data.List.Relation.Unary.Linked.Properties as LinkedP
import Data.List.Sort.Base as SortBase
import Data.List.Sort.MergeSort as MergeSort
import Relation.Binary.Properties.StrictTotalOrder as StrictTotalOrderP
import Data.List.Relation.Unary.AllPairs.Properties as AllPairsP
import Data.List.Relation.Unary.Any.Properties as AnyPr
import Data.Fin.Properties as FinP
import Data.List.Membership.DecPropositional as DecMem
import matrix
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import list
open import basics using (IsStrictOrder)
import prop.set-elim as set-elim

-- Configurations of the interaction: a visible set of vertices together with one hidden region per
-- weakly connected component of the hidden set, each carrying the dependence routed through it as
-- a summary. The visible graph reads the first-order graph at the visible vertices and the
-- summaries elsewhere. The hide move merges the regions adjacent to a vertex and the reveal move
-- splits the region containing one. The moves preserve the invariant that the stored pairs are
-- the view of the visible set, and are mutually inverse. Adjacency is
-- decided through a width witness exhibiting each vertex object as a free semimodule, by reading
-- an edge's matrix off basis vectors.
module interaction.moves {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (let module S = CommutativeSemiring S)
  (+-idem : ∀ x → (x S.+ x) S.≈ x)
  (≡-of-≈ : ∀ {x y} → x S.≈ y → x ≡ y)
  (ε? : (x : S.Carrier) → Dec (x ≡ S.ε)) where

open import interaction.graph S +-idem renaming (restrict to restrict-tables)
open import matrix-embedding S using (𝔽; mat; mat-cong; mat-ε; mat-+; 𝔽F-full)
open import prop using (Prf; ⟪_⟫; ∃ₛ) renaming (_∧_ to _∧ₚ_; _,_ to _,ₚ_; proj₁ to proj₁ₚ; proj₂ to proj₂ₚ)
open import categories using (Category)
open Category SemiMod.cat using (_⇒_; _∘_; _≈_; ≈-refl; ≈-sym; ≈-trans; ≡-to-≈)

private
  module M = matrix.Mat S

  ≈-of-≡ : ∀ {x y} → x ≡ y → x S.≈ y
  ≈-of-≡ ≡-refl = S.refl

  foldr-base : ∀ {P Q : SemiMod.Semimodule} (b : P ⇒ Q) (ts : List (P ⇒ Q)) →
               foldr _+ₘ_ b ts ≈ (b +ₘ foldr _+ₘ_ εₘ ts)
  foldr-base b []       = ≈-sym (+ₘ-runit b)
  foldr-base b (t ∷ ts) = ≈-trans (+ₘ-cong ≈-refl (foldr-base b ts)) (+ₘ-swap-mid t b (foldr _+ₘ_ εₘ ts))

  foldr-map-≈ : ∀ {a} {A' : Set a} {P Q : SemiMod.Semimodule} (b : P ⇒ Q)
                (f g : A' → P ⇒ Q) (xs : List A') →
                All (λ x → Prf (f x ≈ g x)) xs →
                foldr _+ₘ_ b (map f xs) ≈ foldr _+ₘ_ b (map g xs)
  foldr-map-≈ b f g []       []            = ≈-refl
  foldr-map-≈ b f g (x ∷ xs) (⟪ e ⟫ ∷ es) = +ₘ-cong e (foldr-map-≈ b f g xs es)

NonZero : ∀ {m n} → M.Matrix m n → Set
NonZero {m} {n} R = Σ (Fin m) λ i → Σ (Fin n) λ j → ¬ (R i j ≡ S.ε)

NonZero? : ∀ {m n} (R : M.Matrix m n) → Dec (NonZero R)
NonZero? R = FinP.any? (λ i → FinP.any? (λ j → ¬? (ε? (R i j))))

NonZero-O : ∀ {m n} (R : M.Matrix m n) → ¬ NonZero R → ∀ i j → R i j ≡ S.ε
NonZero-O R h i j = dec-case (ε? (R i j)) (λ e → e) (λ ne → ⊥-elim (h (i , j , ne)))

when : ∀ {p} {P : Set p} {X Y : SemiMod.Semimodule} → Dec P → X ⇒ Y → X ⇒ Y
when (yes _) f = f
when (no _)  f = εₘ

private
  when-yes : ∀ {p} {P : Set p} (d : Dec P) → P →
             ∀ {X Y : SemiMod.Semimodule} (f : X ⇒ Y) → when d f ≈ f
  when-yes (yes _)  h f = ≈-refl
  when-yes (no  ¬h) h f = set-elim.⊥-elim (¬h h)

  when-O : ∀ {p} {P : Set p} (d : Dec P) {X Y : SemiMod.Semimodule} (f : X ⇒ Y) →
           (P → f ≈ εₘ) → when d f ≈ εₘ
  when-O (no  _) f h = ≈-refl
  when-O (yes k) f h = h k

  when-sub : ∀ {p q} {P : Set p} {Q : Set q} (d₁ : Dec P) (d₂ : Dec Q)
             {X Y : SemiMod.Semimodule} (f : X ⇒ Y) → (P → Q) →
             (when d₁ f +ₘ when d₂ f) ≈ when d₂ f
  when-sub (no  _) d₂        f imp = +ₘ-lunit (when d₂ f)
  when-sub (yes k) (yes _)   f imp = +ₘ-idem f
  when-sub (yes k) (no  ¬k') f imp = set-elim.⊥-elim (¬k' (imp k))

-- A configuration: the visible set, and one pair per hidden region of a set of vertices and a
-- graph. No invariant is imposed; that the pairs are the view of the visible set is a property
-- the moves preserve.

idt : {A : Set} → String → A → A
idt _ x = x

-- The summaries of a list of regions, computed together, keyed by those regions.
record Summary {m : ℕ} {D : Derivation} (𝒢 : FullGraph m D) : Set where
  field
    regions-to : List (List (Path D)) → List (List (Path D) × Graph 𝒢)
    keys       : ∀ Cs → map proj₁ (regions-to Cs) ≡ Cs

open Summary public using (regions-to; keys)

record Config {m : ℕ} {D : Derivation} (𝒢 : FullGraph m D) : Set₁ where
  field
    visible : List (Path D)
    summaries : List (List (Path D) × Graph 𝒢)

open Config public

module Interaction {m : ℕ} {D : Derivation} (𝒢 : FullGraph m D)
                   (fo-labels : DepRels (vertex-object 𝒢)) where

  private
    wd : V 𝒢 → ℕ
    wd = vertex-width 𝒢

  private
    at : Path D → V 𝒢
    at p = inj₂ p

  open DecMem (_≟_ {D}) public using (_∈_; _∉_; _∈?_)

  _≢?_ : (p q : Path D) → Dec (p ≢ q)
  p ≢? q = ¬? (_≟_ {D} p q)

  entry : ∀ (x y : V 𝒢) → (vertex-object 𝒢 x ⇒ vertex-object 𝒢 y) → M.Matrix (wd y) (wd x)
  entry x y f = ∃ₛ.fst (𝔽F-full f)

  entry-ε : ∀ (x y : V 𝒢) (f : vertex-object 𝒢 x ⇒ vertex-object 𝒢 y) →
            (∀ i j → entry x y f i j ≡ S.ε) → f ≈ εₘ
  entry-ε x y f h =
    ≈-trans (≈-sym (∃ₛ.snd (𝔽F-full f)))
    (≈-trans (mat-cong (λ i j → ≈-of-≡ (h i j))) mat-ε)

  Adjacent : DepRels (vertex-object 𝒢) → V 𝒢 → V 𝒢 → Set
  Adjacent G x y = NonZero (entry x y (G x y)) ⊎ NonZero (entry y x (G y x))

  Adjacent? : (G : DepRels (vertex-object 𝒢)) (x y : V 𝒢) → Dec (Adjacent G x y)
  Adjacent? G x y = NonZero? (entry x y (G x y)) ⊎-dec NonZero? (entry y x (G y x))

  AdjacentIn : DepRels (vertex-object 𝒢) → Path D → List (Path D) → Set
  AdjacentIn G p C = Any (λ q → Adjacent G (at p) (at q)) C

  adjacent-in? : (G : DepRels (vertex-object 𝒢)) (p : Path D)
                 (C : List (Path D)) → Dec (AdjacentIn G p C)
  adjacent-in? G p C = any? (λ q → Adjacent? G (at p) (at q)) C

  adjacent-O : (G : DepRels (vertex-object 𝒢)) (x y : V 𝒢) → ¬ Adjacent G x y →
               Prf ((G x y ≈ εₘ) ∧ₚ (G y x ≈ εₘ))
  adjacent-O G x y h =
    ⟪ entry-ε x y (G x y) (NonZero-O (entry x y (G x y)) (λ k → h (inj₁ k))) ,ₚ
      entry-ε y x (G y x) (NonZero-O (entry y x (G y x)) (λ k → h (inj₂ k))) ⟫

  merge-region : DepRels (vertex-object 𝒢) → Path D → List (List (Path D)) →
                 List (List (Path D))
  merge-region G w rss = (w ∷ concat (proj₁ tp)) ∷ proj₂ tp
    where tp = L.partition (adjacent-in? G w) rss

  regions : DepRels (vertex-object 𝒢) → List (Path D) → List (List (Path D))
  regions G []       = []
  regions G (w ∷ ws) = merge-region G w (regions G ws)

  -- The inputs and the root are never hidden, so only an interior vertex can lie in a region.
  VertexIn : V 𝒢 → List (Path D) → Set
  VertexIn (inj₁ _) C = ⊥
  VertexIn (inj₂ p) C = p ∈ C

  _∈ᵥ?_ : (z : V 𝒢) (C : List (Path D)) → Dec (VertexIn z C)
  inj₁ _        ∈ᵥ? C = no (λ ())
  inj₂ p ∈ᵥ? C = p ∈? C

  Adj-p : Path D → List (Path D) × Graph 𝒢 → Set
  Adj-p p CH = AdjacentIn fo-labels p (proj₁ CH)

  adj-p? : (p : Path D) (CH : List (Path D) × Graph 𝒢) → Dec (Adj-p p CH)
  adj-p? p CH = adjacent-in? fo-labels p (proj₁ CH)

  restrict : DepRels (vertex-object 𝒢) → List (Path D) → DepRels (vertex-object 𝒢)
  restrict G C x y = when (x ∈ᵥ? C ⊎-dec y ∈ᵥ? C) (G x y)

  -- The summary of a hidden region: the dependence routed through it, as relations between the
  -- vertices adjacent to it. Restriction first, so direct edges between boundary vertices are not
  -- carried by the summary.
  summary : List (Path D) → DepRels (vertex-object 𝒢)
  summary C = hide-all (vertex-object 𝒢) (restrict fo-labels C) (map at C)

  initial : Summary 𝒢 → Config 𝒢
  initial summarise .visible = []
  initial summarise .summaries  = summarise .regions-to (regions fo-labels (FO 𝒢))

  hidden-set : Config 𝒢 → List (Path D)
  hidden-set K = concat (map proj₁ (K .summaries))

  hidden-∈ : ∀ {p} (K : Config 𝒢) → p ∈ hidden-set K → Any (λ CH → p ∈ proj₁ CH) (K .summaries)
  hidden-∈ K h = AnyPr.map⁻ (∈-concat⁻ (map proj₁ (K .summaries)) h)

  hidden-∉ : ∀ {p} (K : Config 𝒢) → p ∉ hidden-set K → All (λ CH → p ∉ proj₁ CH) (K .summaries)
  hidden-∉ K h = All-tabulate (λ m k → h (∈-concat⁺′ k (∈-map⁺ proj₁ m)))

  visible-graph : Config 𝒢 → DepRels (vertex-object 𝒢)
  visible-graph K x y =
    foldr _+ₘ_
          (when (¬? (x ∈ᵥ? hs) ×-dec ¬? (y ∈ᵥ? hs)) (fo-labels x y))
          (map (λ CH → table-morphism 𝒢 x y (edge-at 𝒢 ε? idt (proj₂ CH) x y)) (K .summaries))
    where hs = hidden-set K

  edge-table : Graph 𝒢 → (x y : V 𝒢) → M.Table
  edge-table E x y with edge-at 𝒢 ε? idt E x y
  ... | just t  = t
  ... | nothing = zero-table (vertex-width 𝒢 y) (vertex-width 𝒢 x)

  -- F must be the graph fo-labels reads.
  visible-table : Graph 𝒢 → Config 𝒢 → (x y : V 𝒢) → M.Table
  visible-table F K x y =
    foldr (add-table (vertex-width 𝒢 y) (vertex-width 𝒢 x))
          (if ⌊ ¬? (x ∈ᵥ? hidden-set K) ×-dec ¬? (y ∈ᵥ? hidden-set K) ⌋
           then edge-table F x y
           else zero-table (vertex-width 𝒢 y) (vertex-width 𝒢 x))
          (map (λ CH → edge-table (proj₂ CH) x y) (K .summaries))

  -- The edges of the visible graph among labelled endpoints: the ordered pairs whose dependence
  -- matrix is nonzero, with the matrix.
  visible-edges : {A : Set} → Graph 𝒢 → Config 𝒢 → List (A × V 𝒢) →
                  List ((A × V 𝒢) × (A × V 𝒢) × M.Table)
  visible-edges {A} F K us = concat (map (λ u → mapMaybe (edge u) us) us)
    where
    edge : A × V 𝒢 → A × V 𝒢 → Maybe ((A × V 𝒢) × (A × V 𝒢) × M.Table)
    edge u v with visible-table F K (proj₂ u) (proj₂ v)
    ... | t with NonZero? (M.look {vertex-width 𝒢 (proj₂ v)} {vertex-width 𝒢 (proj₂ u)} t)
    ...   | yes _ = just (u , v , t)
    ...   | no  _ = nothing

  edge-table-rep : (E : Graph 𝒢) (x y : V 𝒢) →
                   mat (M.look {vertex-width 𝒢 y} {vertex-width 𝒢 x} (edge-table E x y))
                   ≈ table-morphism 𝒢 x y (edge-at 𝒢 ε? idt E x y)
  edge-table-rep E x y with edge-at 𝒢 ε? idt E x y
  ... | just t  = ≈-refl
  ... | nothing = zero-table-morphism 𝒢 x y (vertex-width 𝒢 y) (vertex-width 𝒢 x)

  -- The rendered table computes the matrix of the visible graph, provided F stores the graph
  -- fo-labels reads.
  visible-table-rep : (F : Graph 𝒢) →
                      ((x' y' : V 𝒢) → table-morphism 𝒢 x' y' (edge-at 𝒢 ε? idt F x' y') ≈ fo-labels x' y') →
                      (K : Config 𝒢) (x y : V 𝒢) →
                      mat (M.look {vertex-width 𝒢 y} {vertex-width 𝒢 x} (visible-table F K x y))
                      ≈ visible-graph K x y
  visible-table-rep F F-reads K x y = fold-rep (K .summaries)
    where
    both? = ¬? (x ∈ᵥ? hidden-set K) ×-dec ¬? (y ∈ᵥ? hidden-set K)
    base' = if ⌊ both? ⌋ then edge-table F x y
            else zero-table (vertex-width 𝒢 y) (vertex-width 𝒢 x)

    base-rep : mat (M.look {vertex-width 𝒢 y} {vertex-width 𝒢 x} base')
               ≈ when both? (fo-labels x y)
    base-rep with ¬? (x ∈ᵥ? hidden-set K) ×-dec ¬? (y ∈ᵥ? hidden-set K)
    ... | yes _ = ≈-trans (edge-table-rep F x y) (F-reads x y)
    ... | no  _ = zero-table-morphism 𝒢 x y (vertex-width 𝒢 y) (vertex-width 𝒢 x)

    fold-rep : (CHs : List (List (Path D) × Graph 𝒢)) →
               mat (M.look {vertex-width 𝒢 y} {vertex-width 𝒢 x}
                    (foldr (add-table (vertex-width 𝒢 y) (vertex-width 𝒢 x)) base'
                           (map (λ CH → edge-table (proj₂ CH) x y) CHs)))
               ≈ foldr _+ₘ_ (when both? (fo-labels x y))
                            (map (λ CH → table-morphism 𝒢 x y (edge-at 𝒢 ε? idt (proj₂ CH) x y)) CHs)
    fold-rep []         = base-rep
    fold-rep (CH ∷ CHs) =
      ≈-trans (mat-cong (λ i j → ≈-of-≡
                (look-add (edge-table (proj₂ CH) x y)
                          (foldr (add-table (vertex-width 𝒢 y) (vertex-width 𝒢 x)) base'
                                 (map (λ CH' → edge-table (proj₂ CH') x y) CHs))
                          i j)))
      (≈-trans (mat-+ (M.look (edge-table (proj₂ CH) x y))
                      (M.look (foldr (add-table (vertex-width 𝒢 y) (vertex-width 𝒢 x)) base'
                                     (map (λ CH' → edge-table (proj₂ CH') x y) CHs))))
               (+ₘ-cong (edge-table-rep (proj₂ CH) x y) (fold-rep CHs)))

  hide-at : Summary 𝒢 → Path D → Config 𝒢 → Config 𝒢
  hide-at summarise p K .visible = filter (p ≢?_) (K .visible)
  hide-at summarise p K .summaries  = summarise .regions-to (C ∷ []) ++ proj₂ tp
    where
      tp = L.partition (adj-p? p) (K .summaries)
      C  = p ∷ concat (map proj₁ (proj₁ tp))

  split-region : Summary 𝒢 → Path D →
                 List (Path D) × Graph 𝒢 → List (List (Path D) × Graph 𝒢)
  split-region summarise p (C , H) with p ∈? C
  ... | yes _ = summarise .regions-to (regions fo-labels (filter (p ≢?_) C))
  ... | no  _ = (C , H) ∷ []

  split-region-∈ : ∀ (summarise : Summary 𝒢) p C (H : Graph 𝒢) → p ∈ C →
                   split-region summarise p (C , H) ≡
                   summarise .regions-to (regions fo-labels (filter (p ≢?_) C))
  split-region-∈ summarise p C H h with p ∈? C
  ... | yes _ = ≡-refl
  ... | no ¬k = ⊥-elim (¬k h)

  split-region-∉ : ∀ (summarise : Summary 𝒢) p C (H : Graph 𝒢) → p ∉ C →
                   split-region summarise p (C , H) ≡ (C , H) ∷ []
  split-region-∉ summarise p C H h with p ∈? C
  ... | yes k = ⊥-elim (h k)
  ... | no  _ = ≡-refl

  reveal-at : Summary 𝒢 → Path D → Config 𝒢 → Config 𝒢
  reveal-at summarise p K .visible = p ∷ K .visible
  reveal-at summarise p K .summaries  = concat (map (split-region summarise p) (K .summaries))

module _ {m : ℕ} {D : Derivation} (𝒢 : FullGraph m D) where

  open Interaction 𝒢 (fo-graph 𝒢)

  private
    module Hide-𝒢 = Hide (V 𝒢) (vertex-object 𝒢)

    at : Path D → V 𝒢
    at p = inj₂ p

  restrict-forward : {G : DepRels (vertex-object 𝒢)} (C : List (Path D)) → Fwd 𝒢 G → Fwd 𝒢 (restrict G C)
  restrict-forward {G} C fwd x y with x ∈ᵥ? C ⊎-dec y ∈ᵥ? C
  ... | yes _ = fwd x y
  ... | no  _ = inj₂ ⟪ ≈-refl ⟫

  private
    module Vertex≤ = StrictTotalOrderP (vertex-order D)
    module MS = MergeSort Vertex≤.decTotalOrder
    open SortBase.SortingAlgorithm MS.mergeSort using (sort; sort-↭; sort-↗)
    open IsStrictOrder (lt-order D) using (asym; irrefl)

  private
    fo-hid : List (V 𝒢)
    fo-hid = map at (sort (fo-hidden 𝒢))

  fo-tabulation : (tick : {A : Set} → String → A → A) → DepTables
  fo-tabulation tick =
    Tabulated.hide-graph (dep-tables 𝒢 ε? tick) tick ε? (map (index-of 𝒢) fo-hid)

  fo-edges : (tick : {A : Set} → String → A → A) → DepRels (vertex-object 𝒢)
  fo-edges tick = dep-rel-at 𝒢 (fo-tabulation tick)

  positions : List (Path D) → List ℕ
  positions = map (λ p → suc (path-position D p))

  first-order-graph : (tick : {A : Set} → String → A → A) → Graph 𝒢
  first-order-graph tick = hide-graph-position-edges 𝒢 ε? tick (positions (fo-hidden 𝒢))

  at-index : List (Graph 𝒢) → ℕ → Graph 𝒢
  at-index []       _       = columns [] []
  at-index (E ∷ _)  zero    = E
  at-index (_ ∷ Es) (suc i) = at-index Es i

  with-regions : ℕ → List (List (Path D)) → (ℕ → Graph 𝒢) → List (List (Path D) × Graph 𝒢)
  with-regions i []       f = []
  with-regions i (C ∷ Cs) f = (C , f i) ∷ with-regions (suc i) Cs f

  with-regions-keys : (i : ℕ) (Cs : List (List (Path D))) (f : ℕ → Graph 𝒢) →
                      map proj₁ (with-regions i Cs f) ≡ Cs
  with-regions-keys i []       f = ≡-refl
  with-regions-keys i (C ∷ Cs) f = ≡-cong (C ∷_) (with-regions-keys (suc i) Cs f)

  -- The first-order set and every region are hidden together, and the paths kept for a region are
  -- those through it, which is what restricting to it before hiding leaves.
  region-summary : (tick : {A : Set} → String → A → A) → Summary 𝒢
  region-summary tick .regions-to Cs =
    with-regions 0 Cs (at-index (hide-graph-position-summaries 𝒢 ε? tick
                                   (positions (fo-hidden 𝒢) ++ concat (map positions Cs))
                                   (map positions Cs)))
  region-summary tick .keys Cs = with-regions-keys 0 Cs _

  -- The region is sorted into evaluation order so that every nonzero edge among its vertices runs
  -- forward; restricting before hiding keeps direct boundary edges out of the summary.
  tabulated-one : (tick : {A : Set} → String → A → A) → DepTables → List (Path D) → Graph 𝒢
  tabulated-one tick F C =
    tabulated (Tabulated.hide-graph (restrict-tables region F) tick ε? region)
    where
    region : List ℕ
    region = map (λ p → index-of 𝒢 (at p)) (sort C)

  tabulated-pairs : (tick : {A : Set} → String → A → A) → DepTables →
                    List (List (Path D)) → List (List (Path D) × Graph 𝒢)
  tabulated-pairs tick F []       = []
  tabulated-pairs tick F (C ∷ Cs) = (C , tabulated-one tick F C) ∷ tabulated-pairs tick F Cs

  tabulated-keys : (tick : {A : Set} → String → A → A) (F : DepTables)
                   (Cs : List (List (Path D))) → map proj₁ (tabulated-pairs tick F Cs) ≡ Cs
  tabulated-keys tick F []       = ≡-refl
  tabulated-keys tick F (C ∷ Cs) = ≡-cong (C ∷_) (tabulated-keys tick F Cs)

  tabulated-summary : (tick : {A : Set} → String → A → A) → DepTables → Summary 𝒢
  tabulated-summary tick F .regions-to Cs = tabulated-pairs tick F Cs
  tabulated-summary tick F .keys       Cs = tabulated-keys tick F Cs

  adjacent-sym : (G : DepRels (vertex-object 𝒢)) {x y : V 𝒢} → Adjacent G x y → Adjacent G y x
  adjacent-sym G = [ inj₂ , inj₁ ]′

  Apart : DepRels (vertex-object 𝒢) → List (Path D) → List (Path D) → Set
  Apart G C C' = All (λ q → All (λ q' → ¬ Adjacent G (at q) (at q')) C') C

  apart-sym : (G : DepRels (vertex-object 𝒢)) {C C' : List (Path D)} → Apart G C C' → Apart G C' C
  apart-sym G h =
    All-tabulate (λ m' → All-tabulate (λ m a → All-lookup (All-lookup h m) m' (adjacent-sym G a)))

  merge-separated : (G : DepRels (vertex-object 𝒢)) (w : Path D) {rs : List (List (Path D))} →
                    AllPairs (Apart G) rs →
                    let tp = L.partition (adjacent-in? G w) rs in
                    AllPairs (Apart G) ((w ∷ concat (proj₁ tp)) ∷ proj₂ tp)
  merge-separated G w {rs} sep = apart-w ∷ proj₁ (proj₂ pa)
    where
    pa = partition-AllPairs {S = Apart G} (adjacent-in? G w) (λ {C} {C'} → apart-sym G {C} {C'}) sep
    tp = L.partition (adjacent-in? G w) rs
    apart-w : All (Apart G (w ∷ concat (proj₁ tp))) (proj₂ tp)
    apart-w =
      All.zipWith (λ {C'} (hf , hc) → AllP.¬Any⇒All¬ C' hf ∷ AllP.concat⁺ hc)
                  (part₂-¬ (adjacent-in? G w) rs , proj₂ (proj₂ pa))

  regions-separated : (G : DepRels (vertex-object 𝒢)) (ws : List (Path D)) → AllPairs (Apart G) (regions G ws)
  regions-separated G []       = []
  regions-separated G (w ∷ ws) = merge-separated G w (regions-separated G ws)

  -- A region's stored summary reads back as the specified summary between vertices outside the
  -- region and outside the first-order-hidden set, the pairs a view can expose.
  Summarises : List (Path D) × Graph 𝒢 → Set
  Summarises CH =
    ∀ x y → ¬ VertexIn x (fo-hidden 𝒢) → ¬ VertexIn y (fo-hidden 𝒢) →
    ¬ VertexIn x (proj₁ CH) → ¬ VertexIn y (proj₁ CH) →
    Prf (table-morphism 𝒢 x y (edge-at 𝒢 ε? idt (proj₂ CH) x y) ≈ summary (proj₁ CH) x y)

  Agrees : Summary 𝒢 → Set
  Agrees summarise = ∀ Cs → All (_⊆ FO 𝒢) Cs → All (AllPairs _≢_) Cs →
                     All Summarises (summarise .regions-to Cs)

  record Summarised (K : Config 𝒢) : Set where
    field
      partition : (K .visible ++ hidden-set K) ↭ FO 𝒢
      canonical : map proj₁ (K .summaries) ↭↭ regions (fo-graph 𝒢) (hidden-set K)
      summaries : All Summarises (K .summaries)

  open Summarised public

  separated : {K : Config 𝒢} → Summarised K → AllPairs (Apart (fo-graph 𝒢)) (map proj₁ (K .summaries))
  separated {K} S =
    perm-AllPairs (λ {C} {C'} → apart-sym (fo-graph 𝒢) {C} {C'})
                  (λ {C} {C'} {C''} → resp C C' C'')
                  (H.sym ↭-sym (S .canonical))
                  (regions-separated (fo-graph 𝒢) (hidden-set K))
    where
    resp : (C C' C'' : List (Path D)) → C ↭ C' → Apart (fo-graph 𝒢) C C'' →
           Apart (fo-graph 𝒢) C' C''
    resp C C' C'' r ap = All-resp-↭ r ap

  regions-concat : (G : DepRels (vertex-object 𝒢)) (ws : List (Path D)) → concat (regions G ws) ↭ ws
  regions-concat G []       = ↭.refl
  regions-concat G (w ∷ ws) =
    ↭.prep w (↭-trans (↭-reflexive (concat-++ (proj₁ tp) (proj₂ tp)))
             (↭-trans (concat-resp (↭↭-of-↭ (partition-↭ _ (regions G ws))))
                      (regions-concat G ws)))
    where tp = L.partition (adjacent-in? G w) (regions G ws)

  hide-at-hidden-set : (summarise : Summary 𝒢) (p : Path D) (K : Config 𝒢) →
                       hidden-set (hide-at summarise p K) ↭ (p ∷ hidden-set K)
  hide-at-hidden-split : (summarise : Summary 𝒢) (p : Path D) (K : Config 𝒢) →
                         hidden-set (hide-at summarise p K)
                         ≡ (p ∷ concat (map proj₁ (proj₁ (L.partition (adj-p? p) (K .summaries)))))
                           ++ concat (map proj₁ (proj₂ (L.partition (adj-p? p) (K .summaries))))
  hide-at-hidden-split summarise p K = ≡-cong concat keyed
    where
    tp = L.partition (adj-p? p) (K .summaries)
    C  = p ∷ concat (map proj₁ (proj₁ tp))

    keyed : map proj₁ (summarise .regions-to (C ∷ []) ++ proj₂ tp)
            ≡ (C ∷ []) ++ map proj₁ (proj₂ tp)
    keyed = ≡-trans (map-++ proj₁ (summarise .regions-to (C ∷ [])) (proj₂ tp))
                    (≡-cong (_++ map proj₁ (proj₂ tp)) (summarise .keys (C ∷ [])))

  hide-at-hidden-set summarise p K =
    subst (λ l → l ↭ (p ∷ hidden-set K)) (≡-sym (hide-at-hidden-split summarise p K)) merged
    where
    tp = L.partition (adj-p? p) (K .summaries)
    C  = p ∷ concat (map proj₁ (proj₁ tp))

    merged : (C ++ concat (map proj₁ (proj₂ tp))) ↭ (p ∷ hidden-set K)
    merged =
      ↭.prep p
        (↭-trans (↭-reflexive (concat-++ (map proj₁ (proj₁ tp)) (map proj₁ (proj₂ tp))))
        (↭-trans (↭-reflexive (≡-cong concat (≡-sym (map-++ proj₁ (proj₁ tp) (proj₂ tp)))))
                 (concat-resp (↭↭-of-↭ (map⁺ proj₁ (partition-↭ _ (K .summaries)))))))

  private
    mv-mono : {C E : List (Path D)} → C ⊆ E → ∀ {z} → VertexIn z C → VertexIn z E
    mv-mono mono {inj₂ q} h = mono h

  restrict-sub : (G : DepRels (vertex-object 𝒢)) {C E : List (Path D)} → C ⊆ E →
                 ∀ x y → (restrict G C x y +ₘ restrict G E x y) ≈ restrict G E x y
  restrict-sub G {C} {E} mono x y =
    when-sub (x ∈ᵥ? C ⊎-dec y ∈ᵥ? C) (x ∈ᵥ? E ⊎-dec y ∈ᵥ? E) (G x y)
             [ (λ hx → inj₁ (mv-mono mono hx)) , (λ hy → inj₂ (mv-mono mono hy)) ]′

  restrict-agree : (G : DepRels (vertex-object 𝒢)) {C E : List (Path D)} → C ⊆ E →
                   All (λ r → Prf (((z : V 𝒢) → restrict G E r z ≈ restrict G C r z)
                               ∧ₚ ((z : V 𝒢) → restrict G E z r ≈ restrict G C z r)))
                       (map at C)
  restrict-agree G {C} {E} mono =
    AllP.map⁺ (All-map (λ {q} h → ⟪
      (λ z → ≈-trans (when-yes (at q ∈ᵥ? E ⊎-dec z ∈ᵥ? E) (inj₁ (mono h)) (G (at q) z))
                     (≈-sym (when-yes (at q ∈ᵥ? C ⊎-dec z ∈ᵥ? C) (inj₁ h) (G (at q) z)))) ,ₚ
      (λ z → ≈-trans (when-yes (z ∈ᵥ? E ⊎-dec at q ∈ᵥ? E) (inj₂ (mono h)) (G z (at q)))
                     (≈-sym (when-yes (z ∈ᵥ? C ⊎-dec at q ∈ᵥ? C) (inj₂ h) (G z (at q))))) ⟫)
      (All-tabulate (λ h → h)))

  localise : {C E : List (Path D)} → C ⊆ E →
             ∀ x y →
             hide-all (vertex-object 𝒢) (restrict (fo-graph 𝒢) E) (map at C) x y ≈
             (restrict (fo-graph 𝒢) E x y +ₘ summary C x y)
  localise {C = C} {E = E} mono x y =
    Hide-𝒢.agree-add {G = restrict (fo-graph 𝒢) C} {G' = restrict (fo-graph 𝒢) E} (map at C)
      (λ x' y' → restrict-sub (fo-graph 𝒢) mono x' y')
      (restrict-agree (fo-graph 𝒢) mono)
      x y

  summary-zero : {C : List (Path D)} (q : Path D) → q ∉ C →
                 All (λ q' → ¬ Adjacent (fo-graph 𝒢) (at q) (at q')) C →
                 Prf (((z : V 𝒢) → summary C (at q) z ≈ εₘ)
                   ∧ₚ ((z : V 𝒢) → summary C z (at q) ≈ εₘ))
  summary-zero {C = C} q hm hadj =
    ⟪ Hide-𝒢.zero-fold {G = restrict (fo-graph 𝒢) C} (map at C) (at q) (base-row ,ₚ base-col) ⟫
    where
    entry-row : ∀ {z} → VertexIn z C → fo-graph 𝒢 (at q) z ≈ εₘ
    entry-row {inj₂ q'} hz =
      proj₁ₚ (Prf.prf (adjacent-O (fo-graph 𝒢) (at q) (at q') (All-lookup hadj hz)))

    entry-col : ∀ {z} → VertexIn z C → fo-graph 𝒢 z (at q) ≈ εₘ
    entry-col {inj₂ q'} hz =
      proj₂ₚ (Prf.prf (adjacent-O (fo-graph 𝒢) (at q) (at q') (All-lookup hadj hz)))

    base-row : (z : V 𝒢) → restrict (fo-graph 𝒢) C (at q) z ≈ εₘ
    base-row z =
      when-O (at q ∈ᵥ? C ⊎-dec z ∈ᵥ? C) (fo-graph 𝒢 (at q) z)
             (set-elim.⊎-case (λ h → set-elim.⊥-elim (hm h)) (λ hz → entry-row hz))

    base-col : (z : V 𝒢) → restrict (fo-graph 𝒢) C z (at q) ≈ εₘ
    base-col z =
      when-O (z ∈ᵥ? C ⊎-dec at q ∈ᵥ? C) (fo-graph 𝒢 z (at q))
             (set-elim.⊎-case (λ hz → entry-col hz) (λ h → set-elim.⊥-elim (hm h)))

  Distinct : List (Path D) → List (Path D) → Set
  Distinct C C' = All (_∉ C) C'

  distinct-sym : {C C' : List (Path D)} → Distinct C C' → Distinct C' C
  distinct-sym d = All-tabulate (λ m k → All-lookup d k m)

  assemble : {E : List (Path D)} (Cs : List (List (Path D))) →
             All (_⊆ E) Cs →
             AllPairs (λ C C' → Apart (fo-graph 𝒢) C' C × Distinct C C') Cs →
             ∀ x y →
             hide-all (vertex-object 𝒢) (restrict (fo-graph 𝒢) E) (map at (concat Cs)) x y ≈
             foldr _+ₘ_ (restrict (fo-graph 𝒢) E x y) (map (λ C → summary C x y) Cs)
  assemble []       []             []              x y = ≈-refl
  assemble {E = E} (C ∷ Cs) (mono ∷ monos) (shead ∷ stail) x y =
    ≈-trans (≡-to-≈ (≡-cong (λ ws → hide-all (vertex-object 𝒢) R-E ws x y) (map-++ at C (concat Cs))))
    (≈-trans (≡-to-≈ (≡-cong (λ H → H x y) (foldl-++ (hide (vertex-object 𝒢)) R-E (map at C) (map at (concat Cs)))))
    (≈-trans (Hide-𝒢.fold-cong (map at (concat Cs)) (λ x' y' → localise {C = C} mono x' y') x y)
    (≈-trans (Hide-𝒢.add-inert {G = R-E} {T = summary C} (map at (concat Cs)) inert' x y)
    (≈-trans (+ₘ-cong (assemble Cs monos stail x y) ≈-refl)
             +ₘ-comm))))
    where
    R-E = restrict (fo-graph 𝒢) E
    inert' = AllP.map⁺ (AllP.concat⁺ (All-map
              (λ {C'} (ap , ds) →
                All.zipWith (λ {q} (ha , hm) → summary-zero {C = C} q hm ha) (ap , ds))
              shead))

  blocks-⊆ : (Css : List (List (Path D))) → All (_⊆ concat Css) Css
  blocks-⊆ []        = []
  blocks-⊆ (C ∷ Css) = ∈-++⁺ˡ ∷ All-map (λ g {_} h → ∈-++⁺ʳ C (g h)) (blocks-⊆ Css)

  private
    regions-⊆ : (G : DepRels (vertex-object 𝒢)) (ws : List (Path D)) → All (_⊆ ws) (regions G ws)
    regions-⊆ G ws = All-map (λ inc {_} h → ∈-resp-↭ (regions-concat G ws) (inc h)) (blocks-⊆ (regions G ws))

  FO-distinct : AllPairs _≢_ (FO 𝒢)
  FO-distinct = AllPairsP.filter⁺ (λ q → T? (fo-at D q)) (distinct D)

  private
    partition-distinct : (K : Config 𝒢) → (K .visible ++ hidden-set K) ↭ FO 𝒢 →
                         AllPairs _≢_ (K .visible ++ hidden-set K)
    partition-distinct K part =
      AllPairs-perm (λ h e → h (≡-sym e)) (↭-sym part) FO-distinct

    concat-distinct : (Css : List (List (Path D))) → AllPairs _≢_ (concat Css) → AllPairs Distinct Css
    concat-distinct []        ps = []
    concat-distinct (C ∷ Css) ps with AllPairs-++⁻ C (concat Css) ps
    ... | (_ , aCss , cross) =
      All-map (λ a → All-tabulate (λ m' m → All-lookup (All-lookup a m) m' ≡-refl))
              (AllP.All-swap (All-map AllP.concat⁻ cross))
      ∷ concat-distinct Css aCss

    blocks-distinct : (Css : List (List (Path D))) → AllPairs _≢_ (concat Css) → All (AllPairs _≢_) Css
    blocks-distinct []        _  = []
    blocks-distinct (C ∷ Css) ps with AllPairs-++⁻ C (concat Css) ps
    ... | (aC , aCss , _) = aC ∷ blocks-distinct Css aCss

    regions-distinct : (G : DepRels (vertex-object 𝒢)) (ws : List (Path D)) → AllPairs _≢_ ws →
                       All (AllPairs _≢_) (regions G ws)
    regions-distinct G ws dist =
      blocks-distinct (regions G ws)
                      (AllPairs-perm (λ h e → h (≡-sym e)) (↭-sym (regions-concat G ws)) dist)

    visible-hidden-split : (K : Config 𝒢) → Summarised K →
                           AllPairs _≢_ (K .visible) × AllPairs _≢_ (hidden-set K) ×
                             All (λ p → All (p ≢_) (hidden-set K)) (K .visible)
    visible-hidden-split K S = AllPairs-++⁻ (K .visible) (hidden-set K) (partition-distinct K (S .partition))

  summarised-distinct : (K : Config 𝒢) → Summarised K → AllPairs Distinct (map proj₁ (K .summaries))
  summarised-distinct K S =
    concat-distinct (map proj₁ (K .summaries))
      (proj₁ (proj₂ (visible-hidden-split K S)))

  hide-at-partition : (summarise : Summary 𝒢) (p : Path D) (K : Config 𝒢) → Summarised K →
                      p ∈ K .visible →
                      (hide-at summarise p K .visible ++ hidden-set (hide-at summarise p K)) ↭ FO 𝒢
  hide-at-partition summarise p K S pv =
    ↭-trans (++⁺ ↭-refl (hide-at-hidden-set summarise p K))
    (↭-trans (shift p (hide-at summarise p K .visible) (hidden-set K))
    (↭-trans (++⁺ (filter-out-↭ (_≟_ {D})
                    (proj₁ (visible-hidden-split K S))
                    pv)
                  ↭-refl)
             (S .partition)))

  hide-at-summaries : (summarise : Summary 𝒢) → Agrees summarise →
                      (p : Path D) (K : Config 𝒢) (S : Summarised K) → p ∈ K .visible →
                      All Summarises (hide-at summarise p K .summaries)
  hide-at-summaries summarise agrees p K S pv =
    AllP.++⁺ (agrees (C' ∷ []) (C'-mono ∷ []) (C'-distinct ∷ []))
             (proj₂ (partition-All (adj-p? p) (S .summaries)))
    where
    C' = p ∷ concat (map proj₁ (proj₁ (L.partition (adj-p? p) (K .summaries))))

    C'-mono : C' ⊆ FO 𝒢
    C'-mono {q} h
      with ∈-resp-↭ (hide-at-hidden-set summarise p K)
             (subst (λ l → q ∈ l) (≡-sym (hide-at-hidden-split summarise p K)) (∈-++⁺ˡ h))
    ... | here ≡-refl = ∈-resp-↭ (S .partition) (∈-++⁺ˡ pv)
    ... | there k     = ∈-resp-↭ (S .partition) (∈-++⁺ʳ (K .visible) k)

    C'-distinct : AllPairs _≢_ C'
    C'-distinct =
      proj₁ (AllPairs-++⁻ C' (concat (map proj₁ (proj₂ (L.partition (adj-p? p) (K .summaries)))))
              (subst (AllPairs _≢_) (hide-at-hidden-split summarise p K)
                (proj₁ (proj₂ (AllPairs-++⁻ (hide-at summarise p K .visible)
                                            (hidden-set (hide-at summarise p K))
                                            (partition-distinct (hide-at summarise p K)
                                              (hide-at-partition summarise p K S pv)))))))

  Apart-mono : {G : DepRels (vertex-object 𝒢)} {C₁ C₂ C₁' C₂' : List (Path D)} →
               C₁ ⊆ C₁' → C₂ ⊆ C₂' → Apart G C₁' C₂' → Apart G C₁ C₂
  Apart-mono m₁ m₂ ap = All-tabulate (λ h → All-tabulate (λ h' → All-lookup (All-lookup ap (m₁ h)) (m₂ h')))

  private
    split-none : (summarise : Summary 𝒢) (p : Path D)
                 {CHs : List (List (Path D) × Graph 𝒢)} →
                 All (λ CH → p ∉ proj₁ CH) CHs →
                 concat (map (split-region summarise p) CHs) ≡ CHs
    split-none summarise p []                     = ≡-refl
    split-none summarise p (_∷_ {C , H} h hs) rewrite split-region-∉ summarise p C H h =
      ≡-cong ((C , H) ∷_) (split-none summarise p hs)

  reveal-set : (summarise : Summary 𝒢) (p : Path D)
               (CHs : List (List (Path D) × Graph 𝒢)) →
               AllPairs _≢_ (concat (map proj₁ CHs)) →
               Any (λ CH → p ∈ proj₁ CH) CHs →
               (p ∷ concat (map proj₁ (concat (map (split-region summarise p) CHs))))
               ↭ concat (map proj₁ CHs)
  reveal-set summarise p ((C , H) ∷ CHs) ps h with AllPairs-++⁻ C (concat (map proj₁ CHs)) ps
  ... | (aC , aRest , cross) with p ∈? C
  ...   | no ¬m =
    ↭-trans (↭-sym (shift p C (concat (map proj₁ (concat (map (split-region summarise p) CHs))))))
            (++⁺ ↭-refl (reveal-set summarise p CHs aRest (tail ¬m h)))
  ...   | yes m =
    ↭-trans (↭-reflexive (≡-cong (λ z → p ∷ concat z) (map-++ proj₁ Xs Zs)))
    (↭-trans (↭-reflexive (≡-cong (p ∷_) (≡-sym (concat-++ (map proj₁ Xs) (map proj₁ Zs)))))
    (↭-trans (↭-reflexive (≡-cong₂ (λ u v → p ∷ (concat u ++ concat (map proj₁ v)))
                                   (summarise .keys Regs)
                                   (split-none summarise p no-p-tail)))
             (++⁺ head-perm ↭-refl)))
    where
    C∖p  = filter (p ≢?_) C
    Regs = regions (fo-graph 𝒢) C∖p
    Xs   = summarise .regions-to Regs
    Zs   = concat (map (split-region summarise p) CHs)

    no-p-tail : All (λ CH → p ∉ proj₁ CH) CHs
    no-p-tail =
      All-tabulate (λ mCH k →
        All-lookup (All-lookup cross m) (∈-concat⁺′ k (∈-map⁺ proj₁ mCH)) ≡-refl)

    head-perm : (p ∷ concat Regs) ↭ C
    head-perm = ↭-trans (↭.prep p (regions-concat (fo-graph 𝒢) C∖p)) (filter-out-↭ (_≟_ {D}) aC m)

  private
    split-summaries : (summarise : Summary 𝒢) → Agrees summarise → (p : Path D)
                      (CH : List (Path D) × Graph 𝒢) →
                      proj₁ CH ⊆ FO 𝒢 → AllPairs _≢_ (proj₁ CH) → Summarises CH →
                      All Summarises (split-region summarise p CH)
    split-summaries summarise agrees p (C , H) mono dist old with p ∈? C
    ... | no  _ = old ∷ []
    ... | yes _ =
      agrees (regions (fo-graph 𝒢) (filter (p ≢?_) C)) subs dists'
      where
      subs : All (_⊆ FO 𝒢) (regions (fo-graph 𝒢) (filter (p ≢?_) C))
      subs = All-map (λ inc {_} h → mono (proj₁ (∈-filter⁻ (p ≢?_) (inc h))))
                     (regions-⊆ (fo-graph 𝒢) (filter (p ≢?_) C))

      dists' : All (AllPairs _≢_) (regions (fo-graph 𝒢) (filter (p ≢?_) C))
      dists' = regions-distinct (fo-graph 𝒢) (filter (p ≢?_) C) (AllPairsP.filter⁺ (p ≢?_) dist)

  reveal-at-partition : (summarise : Summary 𝒢) (p : Path D) (K : Config 𝒢) → Summarised K →
                        p ∈ hidden-set K →
                        (reveal-at summarise p K .visible ++ hidden-set (reveal-at summarise p K)) ↭ FO 𝒢
  reveal-at-partition summarise p K S hp =
    ↭-trans (↭-sym (shift p (K .visible) (hidden-set (reveal-at summarise p K))))
    (↭-trans (++⁺ ↭-refl
                (reveal-set summarise p (K .summaries)
                   (proj₁ (proj₂ (visible-hidden-split K S)))
                   (hidden-∈ K hp)))
             (S .partition))

  reveal-at-summaries : (summarise : Summary 𝒢) → Agrees summarise →
                        (p : Path D) (K : Config 𝒢) → Summarised K →
                        All Summarises (reveal-at summarise p K .summaries)
  reveal-at-summaries summarise agrees p K S =
    AllP.concat⁺ (AllP.map⁺ (All-tabulate (λ {CH} m →
      split-summaries summarise agrees p CH (All-lookup monos m) (All-lookup dists m)
                      (All-lookup (S .summaries) m))))
    where
    monos : All (λ CH → proj₁ CH ⊆ FO 𝒢) (K .summaries)
    monos = All-map (λ inc {_} h → ∈-resp-↭ (S .partition) (∈-++⁺ʳ (K .visible) (inc h)))
                    (AllP.map⁻ (blocks-⊆ (map proj₁ (K .summaries))))

    dists : All (λ CH → AllPairs _≢_ (proj₁ CH)) (K .summaries)
    dists = AllP.map⁻ (blocks-distinct (map proj₁ (K .summaries))
                        (proj₁ (proj₂ (visible-hidden-split K S))))

  private
    visible-graph-summary : (K : Config 𝒢) → Summarised K →
                            ∀ x y →
                            ¬ VertexIn x (fo-hidden 𝒢) → ¬ VertexIn y (fo-hidden 𝒢) →
                            ¬ VertexIn x (hidden-set K) → ¬ VertexIn y (hidden-set K) →
                            visible-graph K x y ≈
                            (fo-graph 𝒢 x y +ₘ summary (hidden-set K) x y)
    visible-graph-summary K S x y hxf hyf hx hy =
      ≈-trans (foldr-base (when both-visible? (G x y))
                          (map (λ CH → table-morphism 𝒢 x y (edge-at 𝒢 ε? idt (proj₂ CH) x y)) (K .summaries)))
              (+ₘ-cong base-eq Σ-eq)
      where
      G  = fo-graph 𝒢
      Cs = map proj₁ (K .summaries)

      blocks-sub : All (λ CH → proj₁ CH ⊆ hidden-set K) (K .summaries)
      blocks-sub = AllP.map⁻ (blocks-⊆ Cs)

      both-visible? = ¬? (x ∈ᵥ? hidden-set K) ×-dec ¬? (y ∈ᵥ? hidden-set K)

      base-eq : when both-visible? (G x y) ≈ G x y
      base-eq = when-yes both-visible? (hx , hy) (G x y)

      seps : AllPairs (λ C C' → Apart G C' C × Distinct C C') Cs
      seps = AllPairs-map (λ {C} {C'} (ap , d) → (apart-sym G {C} {C'} ap , d))
                          (AllPairs.zip (separated S , summarised-distinct K S))

      restrict-O : restrict G (hidden-set K) x y ≈ εₘ
      restrict-O = when-O (x ∈ᵥ? hidden-set K ⊎-dec y ∈ᵥ? hidden-set K) (G x y)
                          (set-elim.⊎-case (λ h → set-elim.⊥-elim (hx h)) (λ h → set-elim.⊥-elim (hy h)))

      Σ-eq : foldr _+ₘ_ εₘ (map (λ CH → table-morphism 𝒢 x y (edge-at 𝒢 ε? idt (proj₂ CH) x y)) (K .summaries))
             ≈ summary (hidden-set K) x y
      Σ-eq =
        ≈-trans (foldr-map-≈ εₘ (λ CH → table-morphism 𝒢 x y (edge-at 𝒢 ε? idt (proj₂ CH) x y))
                             (λ CH → summary (proj₁ CH) x y) (K .summaries)
                  (All-tabulate (λ {CH} m →
                     All-lookup (S .summaries) m x y hxf hyf
                       (λ h → hx (mv-mono (All-lookup blocks-sub m) h))
                       (λ h → hy (mv-mono (All-lookup blocks-sub m) h)))))
        (≈-trans (≡-to-≈ (≡-cong (foldr _+ₘ_ εₘ) (map-∘ {g = λ C → summary C x y} {f = proj₁} (K .summaries))))
        (≈-sym (≈-trans (assemble {E = hidden-set K} Cs (blocks-⊆ Cs) seps x y)
               (≈-trans (foldr-base (restrict G (hidden-set K) x y) (map (λ C → summary C x y) Cs))
               (≈-trans (+ₘ-cong restrict-O ≈-refl)
                        (+ₘ-lunit (foldr _+ₘ_ εₘ (map (λ C → summary C x y) Cs))))))))

  hide-reveal-visible : (summarise : Summary 𝒢) (p : Path D) (K : Config 𝒢) → Summarised K →
                        p ∈ K .visible →
                        reveal-at summarise p (hide-at summarise p K) .visible ↭ K .visible
  hide-reveal-visible summarise p K S pv =
    filter-out-↭ (_≟_ {D})
                 (proj₁ (visible-hidden-split K S))
                 pv

  hide-reveal-hidden-set : (summarise : Summary 𝒢) (p : Path D) (K : Config 𝒢) → Summarised K →
                           p ∈ K .visible →
                           hidden-set (reveal-at summarise p (hide-at summarise p K)) ↭ hidden-set K
  private
    head-eq : {A' : Set} {x y : A'} {xs ys : List A'} → x ∷ xs ≡ y ∷ ys → x ≡ y
    head-eq ≡-refl = ≡-refl

  keyed-head : {xs : List (List (Path D) × Graph 𝒢)} {C : List (Path D)} {p : Path D} →
               map proj₁ xs ≡ C ∷ [] → p ∈ C → Any (λ CH → p ∈ proj₁ CH) xs
  keyed-head {(C' , H) ∷ xs} {p = p} eq m =
    here (subst (λ z → p ∈ z) (≡-sym (head-eq eq)) m)

  hide-reveal-hidden-set summarise p K S pv =
    drop-∷ (↭-trans (reveal-set summarise p (hide-at summarise p K .summaries)
                      (proj₁ (proj₂ (AllPairs-++⁻ (hide-at summarise p K .visible)
                                                  (hidden-set (hide-at summarise p K))
                                                  (partition-distinct (hide-at summarise p K)
                                                    (hide-at-partition summarise p K S pv)))))
                      (AnyPr.++⁺ˡ
                        (keyed-head
                          (summarise .keys
                            ((p ∷ concat (map proj₁ (proj₁ (L.partition (adj-p? p) (K .summaries)))))
                             ∷ []))
                          (here ≡-refl))))
                    (hide-at-hidden-set summarise p K))

  private
    hidden-not-visible : (K : Config 𝒢) → Summarised K → ∀ {p} →
                         p ∈ hidden-set K →
                         p ∉ K .visible
    hidden-not-visible K S {p} hp k =
      All-lookup (All-lookup (proj₂ (proj₂ (visible-hidden-split K S)))
                             k)
                 hp ≡-refl

  reveal-hide-visible : (summarise : Summary 𝒢) (p : Path D) (K : Config 𝒢) → Summarised K →
                        p ∈ hidden-set K →
                        hide-at summarise p (reveal-at summarise p K) .visible ≡ K .visible
  reveal-hide-visible summarise p K S hp =
    ≡-trans (filter-reject (p ≢?_) (λ k → k ≡-refl))
            (filter-all (p ≢?_)
              (All-tabulate (λ {q} m e →
                 hidden-not-visible K S {p = p} hp (subst (_∈ K .visible) (≡-sym e) m))))

  reveal-hide-hidden-set : (summarise : Summary 𝒢) (p : Path D) (K : Config 𝒢) → Summarised K →
                           p ∈ hidden-set K →
                           hidden-set (hide-at summarise p (reveal-at summarise p K)) ↭ hidden-set K
  reveal-hide-hidden-set summarise p K S hp =
    ↭-trans (hide-at-hidden-set summarise p (reveal-at summarise p K))
            (reveal-set summarise p (K .summaries)
               (proj₁ (proj₂ (visible-hidden-split K S)))
               (hidden-∈ K hp))

  private
    restrict-≤ : (G : DepRels (vertex-object 𝒢)) (C : List (Path D)) →
                 ∀ x y → (restrict G C x y +ₘ G x y) ≈ G x y
    restrict-≤ G C x y with x ∈ᵥ? C ⊎-dec y ∈ᵥ? C
    ... | yes _ = +ₘ-idem (G x y)
    ... | no  _ = +ₘ-lunit (G x y)

    restrict-hidden-agree : (G : DepRels (vertex-object 𝒢)) (C : List (Path D)) →
                            All (λ r → Prf (((z : V 𝒢) → G r z ≈ restrict G C r z)
                                        ∧ₚ ((z : V 𝒢) → G z r ≈ restrict G C z r)))
                                (map at C)
    restrict-hidden-agree G C =
      AllP.map⁺ (All-map (λ {q} h → ⟪
        (λ z → ≈-sym (when-yes (at q ∈ᵥ? C ⊎-dec z ∈ᵥ? C) (inj₁ h) (G (at q) z))) ,ₚ
        (λ z → ≈-sym (when-yes (z ∈ᵥ? C ⊎-dec at q ∈ᵥ? C) (inj₂ h) (G z (at q)))) ⟫)
        (All-tabulate (λ h → h)))

  summaries-assemble : (K : Config 𝒢) → Summarised K →
                       ∀ x y →
                       ¬ VertexIn x (fo-hidden 𝒢) → ¬ VertexIn y (fo-hidden 𝒢) →
                       ¬ VertexIn x (hidden-set K) → ¬ VertexIn y (hidden-set K) →
                       visible-graph K x y ≈
                       hide-all (vertex-object 𝒢) (fo-graph 𝒢) (map at (hidden-set K)) x y
  summaries-assemble K S x y hxf hyf hx hy =
    ≈-trans (visible-graph-summary K S x y hxf hyf hx hy)
            (≈-sym (Hide-𝒢.agree-add {G = restrict (fo-graph 𝒢) (hidden-set K)} {G' = fo-graph 𝒢}
                      (map at (hidden-set K))
                      (λ x' y' → restrict-≤ (fo-graph 𝒢) (hidden-set K) x' y')
                      (restrict-hidden-agree (fo-graph 𝒢) (hidden-set K))
                      x y))

  record _≈K_ (K K' : Config 𝒢) : Set where
    field
      visible-≈ : K .visible ↭ K' .visible
      hidden-≈  : hidden-set K ↭ hidden-set K'

  open _≈K_ public

  hide-reveal : (summarise : Summary 𝒢) (p : Path D) (K : Config 𝒢) → Summarised K → p ∈ K .visible →
                reveal-at summarise p (hide-at summarise p K) ≈K K
  hide-reveal summarise p K S pv .visible-≈ = hide-reveal-visible summarise p K S pv
  hide-reveal summarise p K S pv .hidden-≈  = hide-reveal-hidden-set summarise p K S pv

  reveal-hide : (summarise : Summary 𝒢) (p : Path D) (K : Config 𝒢) → Summarised K → p ∈ hidden-set K →
                hide-at summarise p (reveal-at summarise p K) ≈K K
  reveal-hide summarise p K S hp .visible-≈ = ↭-reflexive (reveal-hide-visible summarise p K S hp)
  reveal-hide summarise p K S hp .hidden-≈  = reveal-hide-hidden-set summarise p K S hp

  merge-region-resp : (G : DepRels (vertex-object 𝒢)) (w : Path D) {rss rss' : List (List (Path D))} →
                      rss ↭↭ rss' → merge-region G w rss ↭↭ merge-region G w rss'
  merge-region-resp G w {rss} {rss'} p =
    H.prep (↭.prep w (concat-resp (proj₁ tp-p))) (proj₂ tp-p)
    where
    tp-p = partition-permᴿ (adjacent-in? G w) Any-resp-↭ (λ pc → Any-resp-↭ (↭-sym pc)) p

  private
    merge-region-filter : (G : DepRels (vertex-object 𝒢)) (w : Path D) (rss : List (List (Path D))) →
                          merge-region G w rss ≡
                          ((w ∷ concat (filter (adjacent-in? G w) rss)) ∷
                           filter (∁? (adjacent-in? G w)) rss)
    merge-region-filter G w rss =
      ≡-cong (λ u → (w ∷ concat (proj₁ u)) ∷ proj₂ u) (partition-defn (adjacent-in? G w) rss)

    cross : (G : DepRels (vertex-object 𝒢)) (u u' : Path D) (rss : List (List (Path D))) →
            AdjacentIn G u (u' ∷ concat (filter (adjacent-in? G u') rss)) →
            AdjacentIn G u' (u ∷ concat (filter (adjacent-in? G u) rss))
    cross G u u' rss (here a)  = here (adjacent-sym G a)
    cross G u u' rss (there m) =
      there (AnyPr.concat⁺ (Any-filter⁺ (adjacent-in? G u)
               (Any-filter⁻ (adjacent-in? G u') rss (AnyPr.concat⁻ (filter (adjacent-in? G u') rss) m))))

  merge-region-comm : (G : DepRels (vertex-object 𝒢)) (w w' : Path D) (rss : List (List (Path D))) →
                      merge-region G w (merge-region G w' rss) ↭↭
                      merge-region G w' (merge-region G w rss)
  merge-region-comm G w w' rss =
    subst₂ _↭↭_
      (≡-sym (≡-trans (≡-cong (merge-region G w) (merge-region-filter G w' rss))
                      (merge-region-filter G w ((w' ∷ concat F') ∷ N'))))
      (≡-sym (≡-trans (≡-cong (merge-region G w') (merge-region-filter G w rss))
                      (merge-region-filter G w' ((w ∷ concat F) ∷ N))))
      (dec-case (adjacent-in? G w (w' ∷ concat F')) true-branch false-branch)
    where
    A?  = adjacent-in? G w
    A'? = adjacent-in? G w'
    F   = filter A?  rss
    F'  = filter A'? rss
    N   = filter (∁? A?)  rss
    N'  = filter (∁? A'?) rss

    Goal : Set
    Goal = ((w ∷ concat (filter A? ((w' ∷ concat F') ∷ N'))) ∷
            filter (∁? A?) ((w' ∷ concat F') ∷ N'))
           ↭↭
           ((w' ∷ concat (filter A'? ((w ∷ concat F) ∷ N))) ∷
            filter (∁? A'?) ((w ∷ concat F) ∷ N))

    untouched : filter (∁? A?) N' ↭↭ filter (∁? A'?) N
    untouched = subst (λ z → filter (∁? A?) N' ↭↭ z) (filter-comm (∁? A?) (∁? A'?) rss) ↭↭-refl

    true-branch : AdjacentIn G w (w' ∷ concat F') → Goal
    true-branch b =
      subst₂ _↭↭_
        (≡-sym (≡-cong₂ (λ u v → (w ∷ concat u) ∷ v)
                  (filter-accept A? {w' ∷ concat F'} {N'} b)
                  (filter-reject (∁? A?) {w' ∷ concat F'} {N'} (λ k → k b))))
        (≡-sym (≡-cong₂ (λ u v → (w' ∷ concat u) ∷ v)
                  (filter-accept A'? {w ∷ concat F} {N} b')
                  (filter-reject (∁? A'?) {w ∷ concat F} {N} (λ k → k b'))))
        (H.prep
          (↭.swap w w'
            (↭-trans (↭-reflexive (concat-++ F' (filter A? N')))
            (↭-trans (concat-resp (↭↭-of-↭ (filter-exchange A? A'? rss)))
                     (↭-reflexive (≡-sym (concat-++ F (filter A'? N)))))))
          untouched)
      where b' = cross G w w' rss b

    false-branch : ¬ AdjacentIn G w (w' ∷ concat F') → Goal
    false-branch ¬b =
      subst₂ _↭↭_
        (≡-sym (≡-cong₂ (λ u v → (w ∷ concat u) ∷ v)
                  (filter-reject A? {w' ∷ concat F'} {N'} ¬b)
                  (filter-accept (∁? A?) {w' ∷ concat F'} {N'} ¬b)))
        (≡-sym (≡-cong₂ (λ u v → (w' ∷ concat u) ∷ v)
                  (filter-reject A'? {w ∷ concat F} {N} ¬b')
                  (filter-accept (∁? A'?) {w ∷ concat F} {N} ¬b')))
        (H.swap
          (↭-reflexive (≡-cong (λ z → w ∷ concat z) (filter-avoid A? A'? rss hb)))
          (↭-reflexive (≡-cong (λ z → w' ∷ concat z) (≡-sym (filter-avoid A'? A? rss hb'))))
          untouched)
      where
      ¬b' : ¬ AdjacentIn G w' (w ∷ concat F)
      ¬b' k = ¬b (cross G w' w rss k)

      hb : ¬ Any (λ C → AdjacentIn G w' C × AdjacentIn G w C) rss
      hb m = ¬b (there (AnyPr.concat⁺ (Any-filter⁺ A'? m)))

      hb' : ¬ Any (λ C → AdjacentIn G w C × AdjacentIn G w' C) rss
      hb' m = ¬b' (there (AnyPr.concat⁺ (Any-filter⁺ A? m)))

  regions-perm : (G : DepRels (vertex-object 𝒢)) {ws ws' : List (Path D)} → ws ↭ ws' →
                 regions G ws ↭↭ regions G ws'
  regions-perm G ↭.refl         = ↭↭-refl
  regions-perm G (↭.prep w p)   = merge-region-resp G w (regions-perm G p)
  regions-perm G (↭.swap {xs = ws₁} {ys = ws₂} w w' p) =
    H.trans (merge-region-resp G w (merge-region-resp G w' (regions-perm G p)))
            (merge-region-comm G w w' (regions G ws₂))
  regions-perm G (↭.trans p q)  = H.trans (regions-perm G p) (regions-perm G q)

  private
    tabulated≡ : (summarise : Summary 𝒢) →
              map proj₁ (initial summarise .summaries) ≡ regions (fo-graph 𝒢) (FO 𝒢)
    tabulated≡ summarise = summarise .keys (regions (fo-graph 𝒢) (FO 𝒢))

  initial-summarised : (summarise : Summary 𝒢) → Agrees summarise → Summarised (initial summarise)
  initial-summarised summarise agrees .partition =
    subst (λ z → concat z ↭ FO 𝒢) (≡-sym (tabulated≡ summarise)) (regions-concat (fo-graph 𝒢) (FO 𝒢))
  initial-summarised summarise agrees .canonical =
    subst (λ z → z ↭↭ regions (fo-graph 𝒢) (concat z))
          (≡-sym (tabulated≡ summarise))
          (regions-perm (fo-graph 𝒢) (↭-sym (regions-concat (fo-graph 𝒢) (FO 𝒢))))
  initial-summarised summarise agrees .summaries =
    agrees (regions (fo-graph 𝒢) (FO 𝒢))
           (regions-⊆ (fo-graph 𝒢) (FO 𝒢))
           (regions-distinct (fo-graph 𝒢) (FO 𝒢) FO-distinct)

  -- From the inputs to the root, the visible graph of the initial state is the collapse of
  -- the underlying graph: reading the stored region summaries computes the same dependence as
  -- hiding every interior vertex.
  root-not-hidden : (K : Config 𝒢) → Summarised K → ¬ VertexIn (inj₂ ε) (hidden-set K)
  root-not-hidden K S mem =
    All-lookup (vertices-no-ε D)
               (∈-resp-↭ (filterᵇ-split (fo-at D) (vertices D))
                         (∈-++⁺ʳ (fo-hidden 𝒢)
                                 (∈-resp-↭ (S .partition) (∈-++⁺ʳ (K .visible) mem))))
    ≡-refl

  root-not-fo-hidden : ¬ VertexIn (inj₂ ε) (fo-hidden 𝒢)
  root-not-fo-hidden mem =
    All-lookup (vertices-no-ε D)
               (∈-resp-↭ (filterᵇ-split (fo-at D) (vertices D)) (∈-++⁺ˡ mem))
    ≡-refl

  initial-collapse : (summarise : Summary 𝒢) → Agrees summarise →
                     visible-graph (initial summarise) (inj₁ input) (inj₂ ε) ≈ collapse 𝒢
  initial-collapse summarise agrees =
    ≈-trans (summaries-assemble (initial summarise) (initial-summarised summarise agrees)
              (inj₁ input) (inj₂ ε) (λ ()) root-not-fo-hidden (λ ())
              (root-not-hidden (initial summarise) (initial-summarised summarise agrees)))
            (≈-trans (hide-all-perm 𝒢 (fo-forward 𝒢)
                       (map⁺ at (initial-summarised summarise agrees .partition))
                       (inj₁ input) (inj₂ ε))
                     (fo-collapse 𝒢))

  hide-at-summarised : (summarise : Summary 𝒢) → Agrees summarise →
                       (p : Path D) (K : Config 𝒢) (S : Summarised K) →
                       p ∈ K .visible →
                       Summarised (hide-at summarise p K)
  hide-at-summarised summarise agrees p K S pv .partition = hide-at-partition summarise p K S pv
  hide-at-summarised summarise agrees p K S pv .canonical =
    subst (λ z → z ↭↭ regions (fo-graph 𝒢) (hidden-set (hide-at summarise p K)))
          lhs-eq
          (H.trans (merge-region-resp (fo-graph 𝒢) p (S .canonical))
                   (H.sym ↭-sym (regions-perm (fo-graph 𝒢) (hide-at-hidden-set summarise p K))))
    where
    tp = L.partition (adj-p? p) (K .summaries)
    C  = p ∷ concat (map proj₁ (proj₁ tp))

    keys-eq : map proj₁ (hide-at summarise p K .summaries) ≡ C ∷ map proj₁ (proj₂ tp)
    keys-eq = ≡-trans (map-++ proj₁ (summarise .regions-to (C ∷ [])) (proj₂ tp))
                      (≡-cong (_++ map proj₁ (proj₂ tp)) (summarise .keys (C ∷ [])))

    lhs-eq : merge-region (fo-graph 𝒢) p (map proj₁ (K .summaries)) ≡
             map proj₁ (hide-at summarise p K .summaries)
    lhs-eq =
      ≡-trans (≡-cong₂ (λ u v → (p ∷ concat u) ∷ v)
                       (map-partition₁ proj₁ (adjacent-in? (fo-graph 𝒢) p) (K .summaries))
                       (map-partition₂ proj₁ (adjacent-in? (fo-graph 𝒢) p) (K .summaries)))
              (≡-sym keys-eq)
  hide-at-summarised summarise agrees p K S pv .summaries = hide-at-summaries summarise agrees p K S pv

  private
    merge-region-inert : (G : DepRels (vertex-object 𝒢)) (w : Path D) (X' Y' : List (List (Path D))) →
                         All (λ C → ¬ AdjacentIn G w C) Y' →
                         merge-region G w (X' ++ Y') ≡ merge-region G w X' ++ Y'
    merge-region-inert G w X' Y' h =
      ≡-trans (merge-region-filter G w (X' ++ Y'))
      (≡-trans (≡-cong₂ (λ u v → (w ∷ concat u) ∷ v)
                 (≡-trans (filter-++ (adjacent-in? G w) X' Y')
                 (≡-trans (≡-cong (filter (adjacent-in? G w) X' ++_) (filter-none (adjacent-in? G w) h))
                          (++-identityʳ (filter (adjacent-in? G w) X'))))
                 (≡-trans (filter-++ (∁? (adjacent-in? G w)) X' Y')
                          (≡-cong (filter (∁? (adjacent-in? G w)) X' ++_)
                                  (filter-all (∁? (adjacent-in? G w)) h))))
               (≡-cong (_++ Y') (≡-sym (merge-region-filter G w X'))))

  regions-apart : (G : DepRels (vertex-object 𝒢)) (B' rest : List (Path D)) → Apart G B' rest →
                  regions G (B' ++ rest) ↭↭ (regions G B' ++ regions G rest)
  regions-apart G []       rest ap = ↭↭-refl
  regions-apart G (b ∷ B') rest (hb ∷ hB) =
    H.trans (merge-region-resp G b (regions-apart G B' rest hB))
            (↭↭-of-≡ (merge-region-inert G b (regions G B') (regions G rest)
              (All-map (λ {C} inc →
                 AllP.All¬⇒¬Any (All-tabulate (λ h → All-lookup hb (inc h))))
                (regions-⊆ G rest))))

  private
    apart-concat : {G : DepRels (vertex-object 𝒢)} {C : List (Path D)} {Cs : List (List (Path D))} →
                   All (Apart G C) Cs → Apart G C (concat Cs)
    apart-concat aps = All-tabulate (λ m → AllP.concat⁺ (All-map (λ ap → All-lookup ap m) aps))

    regions-nonempty : (G : DepRels (vertex-object 𝒢)) (ws : List (Path D)) →
                       All (λ C → 1 ≤ length C) (regions G ws)
    regions-nonempty G []       = []
    regions-nonempty G (w ∷ ws) = s≤s z≤n ∷ proj₂ (partition-All (adjacent-in? G w) (regions-nonempty G ws))

  regions-apart-concat : {G : DepRels (vertex-object 𝒢)} {Cs : List (List (Path D))} →
                         AllPairs (Apart G) Cs →
                         regions G (concat Cs) ↭↭ concat (map (regions G) Cs)
  regions-apart-concat {G = G}           []                    = ↭↭-refl
  regions-apart-concat {G = G} {C ∷ Cs} (aps ∷ pairs) =
    H.trans (regions-apart G C (concat Cs) (apart-concat {G = G} {C = C} {Cs = Cs} aps))
            (↭↭-++⁺ ↭↭-refl (regions-apart-concat pairs))

  blocks-one-region : (K : Config 𝒢) → Summarised K →
                      All (λ C → regions (fo-graph 𝒢) C ↭↭ (C ∷ []))
                          (map proj₁ (K .summaries))
  blocks-one-region K S = All-map (λ {C} e → one {C} e) lens1
    where
    G  = fo-graph 𝒢
    Cs = map proj₁ (K .summaries)

    perm2 : Cs ↭↭ concat (map (regions G) Cs)
    perm2 = H.trans (S .canonical) (regions-apart-concat (separated S))

    nonempty : All (λ C → 1 ≤ length C) Cs
    nonempty = perm-All (λ {C} {C'} pc h → subst (1 ≤_) (↭-length pc) h)
                        (H.sym ↭-sym (S .canonical))
                        (regions-nonempty G (hidden-set K))

    len-regions : ∀ (C : List (Path D)) → 1 ≤ length C → 1 ≤ length (regions G C)
    len-regions (q ∷ C') _ = s≤s z≤n

    atleast : All (λ C → 1 ≤ length (regions G C)) Cs
    atleast = All-map (λ {C} h → len-regions C h) nonempty

    lens-eq : sum (map (λ C → length (regions G C)) Cs) ≡ length (map (λ C → length (regions G C)) Cs)
    lens-eq =
      ≡-trans (≡-cong sum (map-∘ {g = length} {f = regions G} Cs))
      (≡-trans (≡-sym (length-concat (map (regions G) Cs)))
      (≡-trans (≡-sym (perm-length perm2))
               (≡-sym (length-map (λ C → length (regions G C)) Cs))))

    lens1 : All (λ C → length (regions G C) ≡ 1) Cs
    lens1 = AllP.map⁻ (sum-ones (AllP.map⁺ atleast) lens-eq)

    one : ∀ {C : List (Path D)} → length (regions G C) ≡ 1 → regions G C ↭↭ (C ∷ [])
    one {C} e with singleton (regions G C) e
    ... | (C₀ , eq) =
      subst (_↭↭ (C ∷ [])) (≡-sym eq)
            (H.prep (↭-trans (↭-reflexive (≡-sym (++-identityʳ C₀)))
                             (subst (λ z → concat z ↭ C) eq (regions-concat G C)))
                    (H.refl []))

  reveal-at-summarised : (summarise : Summary 𝒢) → Agrees summarise →
                         (p : Path D) (K : Config 𝒢) (S : Summarised K) →
                         p ∈ hidden-set K →
                         Summarised (reveal-at summarise p K)
  reveal-at-summarised summarise agrees p K S hp .partition = reveal-at-partition summarise p K S hp
  reveal-at-summarised summarise agrees p K S hp .summaries = reveal-at-summaries summarise agrees p K S
  reveal-at-summarised summarise agrees p K S hp .canonical =
    subst (λ z → z ↭↭ regions G (hidden-set (reveal-at summarise p K)))
          (≡-trans (≡-cong concat (map-∘ {g = map proj₁} {f = split-region summarise p} (K .summaries)))
                   (concat-map {f = proj₁} (map (split-region summarise p) (K .summaries))))
          (H.trans blocks-part
          (H.trans (↭↭-of-≡ (≡-cong concat maps-eq))
          (H.trans (H.sym ↭.↭-sym (regions-apart-concat {G = G} apart-filtered))
          (H.trans (↭↭-of-≡ (≡-cong (regions G) (≡-sym (filter-concat notp Cs))))
                   (H.sym ↭.↭-sym (regions-perm G hrev))))))
    where
    G    = fo-graph 𝒢
    Cs   = map proj₁ (K .summaries)
    notp = p ≢?_

    distinct-hs : AllPairs _≢_ (hidden-set K)
    distinct-hs = proj₁ (proj₂ (visible-hidden-split K S))

    hrev : hidden-set (reveal-at summarise p K) ↭ filter notp (hidden-set K)
    hrev = drop-∷
      (↭-trans (reveal-set summarise p (K .summaries) distinct-hs (hidden-∈ K hp))
               (↭.↭-sym (filter-out-↭ (_≟_ {D}) distinct-hs hp)))

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

    maps-eq : map (λ CH → regions G (filter notp (proj₁ CH))) (K .summaries) ≡
              map (regions G) (map (filter notp) Cs)
    maps-eq =
      ≡-trans (map-∘ {g = λ C → regions G (filter notp C)} {f = proj₁} (K .summaries))
              (map-∘ {g = regions G} {f = filter notp} Cs)

    per-block : ∀ CH → regions G (proj₁ CH) ↭↭ (proj₁ CH ∷ []) →
                map proj₁ (split-region summarise p CH) ↭↭ regions G (filter notp (proj₁ CH))
    per-block (C , H') one =
      dec-case (p ∈? C)
        (λ k → ↭↭-of-≡ (≡-trans (≡-cong (map proj₁) (split-region-∈ summarise p C H' k))
                                (summarise .keys (regions G (filter notp C)))))
        (λ ¬k → subst₂ _↭↭_
                  (≡-sym (≡-cong (map proj₁) (split-region-∉ summarise p C H' ¬k)))
                  (≡-sym (≡-cong (regions G)
                           (filter-all (p ≢?_)
                             (All-tabulate (λ {q} m e' → ¬k (subst (_∈ C) (≡-sym e') m))))))
                  (H.sym ↭.↭-sym one))

    blocks-part : concat (map (λ CH → map proj₁ (split-region summarise p CH)) (K .summaries)) ↭↭
                  concat (map (λ CH → regions G (filter notp (proj₁ CH))) (K .summaries))
    blocks-part = concat-↭↭ (All-map (λ {CH} one → per-block CH one) (AllP.map⁻ (blocks-one-region K S)))

  private
    ≡ᵇ-self : (n : ℕ) → (n ≡ᵇ n) ≡ true
    ≡ᵇ-self zero    = ≡-refl
    ≡ᵇ-self (suc n) = ≡ᵇ-self n

    ≡ᵇ-to-≡ : (i j : ℕ) → (i ≡ᵇ j) ≡ true → i ≡ j
    ≡ᵇ-to-≡ zero    zero    _  = ≡-refl
    ≡ᵇ-to-≡ zero    (suc j) ()
    ≡ᵇ-to-≡ (suc i) zero    ()
    ≡ᵇ-to-≡ (suc i) (suc j) e  = ≡-cong suc (≡ᵇ-to-≡ i j e)

    ∨-true : (a : Bool) {b : Bool} → (a ∨ b) ≡ true → (a ≡ true) ⊎ (b ≡ true)
    ∨-true true  e = inj₁ ≡-refl
    ∨-true false e = inj₂ e

    ∨-trueˡ : {a b : Bool} → a ≡ true → (a ∨ b) ≡ true
    ∨-trueˡ {a} {b} e = ≡-cong (_∨ b) e

    ∨-trueʳ : (a : Bool) {b : Bool} → b ≡ true → (a ∨ b) ≡ true
    ∨-trueʳ true  e = ≡-refl
    ∨-trueʳ false e = e

    not-both : {b : Bool} → b ≡ true → not b ≡ true → ⊥
    not-both {true}  _  ()
    not-both {false} () _

    any-≡ᵇ-∈ : (n : ℕ) (L : List ℕ) → any (n ≡ᵇ_) L ≡ true → Any (n ≡_) L
    any-≡ᵇ-∈ n []      ()
    any-≡ᵇ-∈ n (j ∷ L) e with n ≡ᵇ j in nj
    ... | true  = here (≡ᵇ-to-≡ n j nj)
    ... | false = there (any-≡ᵇ-∈ n L e)

    ∈-any-≡ᵇ : (n : ℕ) (L : List ℕ) → Any (n ≡_) L → any (n ≡ᵇ_) L ≡ true
    ∈-any-≡ᵇ n (j ∷ L) (here ≡-refl) rewrite ≡ᵇ-self n = ≡-refl
    ∈-any-≡ᵇ n (j ∷ L) (there m) with n ≡ᵇ j
    ... | true  = ≡-refl
    ... | false = ∈-any-≡ᵇ n L m

    filterᵇ-true : {A' : Set} (f : A' → Bool) {x : A'} (xs : List A') →
                   x ∈ₚ filterᵇ f xs → f x ≡ true
    filterᵇ-true f []       ()
    filterᵇ-true f (y ∷ xs) m with f y in fy | m
    ... | true  | here e   = ≡-trans (≡-cong f e) fy
    ... | true  | there m' = filterᵇ-true f xs m'
    ... | false | m'       = filterᵇ-true f xs m'

    F₀ : DepTables
    F₀ = fo-tabulation idt

    sorted-pairs : (G : DepRels (vertex-object 𝒢)) → Fwd 𝒢 G →
                   (C : List (Path D)) → AllPairs _≢_ C →
                   AllPairs (λ v u → Prf (G u v ≈ εₘ)) (map at (sort C))
    sorted-pairs G fwd C dist =
      AllPairsP.map⁺ (AllPairs-map step (AllPairs.zip (le-pairs , ne-pairs)))
      where
      le-pairs : AllPairs Vertex≤._≤_ (sort C)
      le-pairs = LinkedP.Linked⇒AllPairs Vertex≤.trans (sort-↗ C)

      ne-pairs : AllPairs _≢_ (sort C)
      ne-pairs = AllPairs-perm (λ h e → h (≡-sym e)) (↭-sym (sort-↭ C)) dist

      step : {p q : Path D} → Vertex≤._≤_ p q × p ≢ q → Prf (G (at q) (at p) ≈ εₘ)
      step {p} {q} (inj₁ lt-pq , ne) with fwd (at q) (at p)
      ... | inj₂ z  = z
      ... | inj₁ qp = ⊥-elim (asym p q lt-pq qp)
      step (inj₂ e , ne) = ⊥-elim (ne e)

    fo-hidden-distinct : AllPairs _≢_ (fo-hidden 𝒢)
    fo-hidden-distinct = AllPairsP.filter⁺ (λ q → T? (not (fo-at D q))) (distinct D)

    fo-hid-mem : All (_∈ₚ all-vertices 𝒢) fo-hid
    fo-hid-mem = All-tabulate (λ {w} _ → ∈-all-vertices 𝒢 w)

    fo-hid-pairs : AllPairs (λ v u → Prf (dep-rels 𝒢 u v ≈ εₘ)) fo-hid
    fo-hid-pairs = sorted-pairs (dep-rels 𝒢) (dep-rels-forward 𝒢) (fo-hidden 𝒢)
                                fo-hidden-distinct

    module FoHide = HideRepresents 𝒢 ε? (dep-tables-rep 𝒢 ε?) fo-hid fo-hid-mem fo-hid-pairs

    fo-rep : Represents 𝒢 F₀ FoHide.remaining (fo-graph 𝒢)
    fo-rep = rep-cong 𝒢 (λ x y → hide-all-perm 𝒢 (dep-rels-forward 𝒢)
                                                 (map⁺ at (sort-↭ (fo-hidden 𝒢))) x y)
                     FoHide.hide-rep

  -- The tabulated summariser at identity tick satisfies boundary agreement: the stored
  -- fo-tabulation represents the first-order graph at its surviving vertices, restriction and
  -- hiding preserve representation, and sorting the region is sound because the restricted graph
  -- is forward.
  tabulated-one-agrees : (C : List (Path D)) → C ⊆ FO 𝒢 → AllPairs _≢_ C →
                         Summarises (C , tabulated-one (λ _ x → x) (fo-tabulation (λ _ x → x)) C)
  tabulated-one-agrees C C⊆FO C-dist x y hxf hyf hxC hyC =
    ⟪ ≈-trans (≡-to-≈ region-eq)
      (≈-trans (dep-rel-at-rep 𝒢 RH.hide-rep x∈rem y∈rem)
               (hide-all-perm 𝒢 (restrict-forward C (fo-forward 𝒢)) (map⁺ at (sort-↭ C)) x y)) ⟫
    where
    regionV : List (V 𝒢)
    regionV = map at (sort C)

    idxs : List ℕ
    idxs = map (index-of 𝒢) regionV

    side⁻ : (z : V 𝒢) → any (index-of 𝒢 z ≡ᵇ_) idxs ≡ true → VertexIn z C
    side⁻ z e with ∈-map⁻ at (Any-map (λ ie → index-of-injective 𝒢 ie)
                                   (AnyPr.map⁻ (any-≡ᵇ-∈ (index-of 𝒢 z) idxs e)))
    ... | (p , pm , ze) = subst (λ v → VertexIn v C) (≡-sym ze) (∈-resp-↭ (sort-↭ C) pm)

    side⁺ : (z : V 𝒢) → VertexIn z C → any (index-of 𝒢 z ≡ᵇ_) idxs ≡ true
    side⁺ (inj₁ _) ()
    side⁺ (inj₂ p) h =
      ∈-any-≡ᵇ (index-of 𝒢 (at p)) idxs
               (∈-map⁺ (index-of 𝒢) (∈-map⁺ at (∈-resp-↭ (↭-sym (sort-↭ C)) h)))

    region-restrict : (x' y' : V 𝒢) →
                      restrict-vertices 𝒢 regionV (fo-graph 𝒢) x' y' ≈ restrict (fo-graph 𝒢) C x' y'
    region-restrict x' y' with x' ∈ᵥ? C ⊎-dec y' ∈ᵥ? C
    ... | yes k =
      ≡-to-≈ (≡-cong (λ b → if b then fo-graph 𝒢 x' y' else εₘ) (mem-true k))
      where
      mem-true : (VertexIn x' C ⊎ VertexIn y' C) →
                 (any (index-of 𝒢 x' ≡ᵇ_) idxs ∨ any (index-of 𝒢 y' ≡ᵇ_) idxs) ≡ true
      mem-true (inj₁ h) = ∨-trueˡ (side⁺ x' h)
      mem-true (inj₂ h) = ∨-trueʳ (any (index-of 𝒢 x' ≡ᵇ_) idxs) (side⁺ y' h)
    ... | no ¬k with any (index-of 𝒢 x' ≡ᵇ_) idxs ∨ any (index-of 𝒢 y' ≡ᵇ_) idxs in bb
    ...   | false = ≈-refl
    ...   | true  = ⊥-elimₚ (¬k (bool-mem (∨-true (any (index-of 𝒢 x' ≡ᵇ_) idxs) bb)))
      where
      bool-mem : (any (index-of 𝒢 x' ≡ᵇ_) idxs ≡ true) ⊎ (any (index-of 𝒢 y' ≡ᵇ_) idxs ≡ true) →
                 VertexIn x' C ⊎ VertexIn y' C
      bool-mem (inj₁ ex) = inj₁ (side⁻ x' ex)
      bool-mem (inj₂ ey) = inj₂ (side⁻ y' ey)

    R-region : Represents 𝒢 (restrict-tables (map (index-of 𝒢) regionV) F₀)
                          FoHide.remaining (restrict (fo-graph 𝒢) C)
    R-region = rep-cong 𝒢 region-restrict (restrict-rep 𝒢 fo-rep regionV)

    C-mem : All (_∈ₚ FoHide.remaining) regionV
    C-mem = All-tabulate in-rem
      where
      in-rem : {w : V 𝒢} → w ∈ₚ regionV → w ∈ₚ FoHide.remaining
      in-rem {w} mw with ∈-map⁻ at mw
      ... | (p , pm , eq) = FoHide.∈-remaining (∈-all-vertices 𝒢 w) not-hid
        where
        not-hid : ¬ (w ∈ₚ fo-hid)
        not-hid mh with ∈-map⁻ at mh
        ... | (q , qm , eq') =
          not-both (filterᵇ-true (fo-at D) (vertices D) (C⊆FO (∈-resp-↭ (sort-↭ C) pm)))
                   (filterᵇ-true (λ r → not (fo-at D r)) (vertices D)
                     (subst (_∈ fo-hidden 𝒢)
                            (≡-sym (inj₂-injective (≡-trans (≡-sym eq) eq')))
                            (∈-resp-↭ (sort-↭ (fo-hidden 𝒢)) qm)))

    region-pairs : AllPairs (λ v u → Prf (restrict (fo-graph 𝒢) C u v ≈ εₘ)) regionV
    region-pairs = sorted-pairs (restrict (fo-graph 𝒢) C) (restrict-forward C (fo-forward 𝒢))
                                C C-dist

    module RH = HideRepresents 𝒢 ε? R-region regionV C-mem region-pairs

    region-eq : table-morphism 𝒢 x y
                  (edge-at 𝒢 ε? idt (tabulated-one (λ _ x' → x') (fo-tabulation (λ _ x' → x')) C) x y)
                ≡ dep-rel-at 𝒢 (Tabulated.hide-graph
                                (restrict-tables (map (index-of 𝒢) regionV) F₀)
                                (λ _ c → c) ε? (map (index-of 𝒢) regionV)) x y
    region-eq =
      ≡-cong (λ l → dep-rel-at 𝒢 (Tabulated.hide-graph (restrict-tables l F₀)
                                  (λ _ c → c) ε? l) x y)
             (map-∘ {g = index-of 𝒢} {f = at} (sort C))

    not-in-map : {v : V 𝒢} (L : List (Path D)) → ¬ VertexIn v L → ¬ (v ∈ₚ map at (sort L))
    not-in-map L nh mv with ∈-map⁻ at mv
    ... | (p , pm , eq) =
      nh (subst (λ v' → VertexIn v' L) (≡-sym eq) (∈-resp-↭ (sort-↭ L) pm))

    x∈rem : x ∈ₚ RH.remaining
    x∈rem = RH.∈-remaining
              (FoHide.∈-remaining (∈-all-vertices 𝒢 x) (not-in-map (fo-hidden 𝒢) hxf))
              (not-in-map C hxC)

    y∈rem : y ∈ₚ RH.remaining
    y∈rem = RH.∈-remaining
              (FoHide.∈-remaining (∈-all-vertices 𝒢 y) (not-in-map (fo-hidden 𝒢) hyf))
              (not-in-map C hyC)

  tabulated-agrees : Agrees (tabulated-summary (λ _ x → x) (fo-tabulation (λ _ x → x)))
  tabulated-agrees []       _              _              = []
  tabulated-agrees (C ∷ Cs) (mono ∷ monos) (dist ∷ dists) =
    tabulated-one-agrees C mono dist ∷ tabulated-agrees Cs monos dists
