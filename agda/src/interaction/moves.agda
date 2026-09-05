{-# OPTIONS --prop --postfix-projections --safe #-}

open import Agda.Builtin.Strict using (primForce; primForceLemma)
open import Data.Bool.Properties using (T?)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; allFin; length; map; filter; concat; foldr)
import Data.List as L
open import Data.List.Properties
  using (++-identityʳ; concat-++; concat-map; foldl-++; length-map; map-++; map-∘;
         filter-all; filter-accept; filter-reject; filter-none; filter-++; partition-defn)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
  using (map⁺; shift; ++⁺; drop-∷; All-resp-↭; Any-resp-↭; ↭-length; ∈-resp-↭)
open import Data.List.Relation.Binary.Pointwise using ([]; _∷_)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-concat⁻; ∈-concat⁺′; ∈-map⁺; ∈-filter⁻)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_; universal)
  renaming (map to All-map; tabulate to All-tabulate; lookup to All-lookup)
open import Data.List.Relation.Unary.AllPairs as AllPairs using (AllPairs; []; _∷_)
  renaming (map to AllPairs-map)
open import Data.List.Relation.Unary.Any using (Any; any?; here; there; tail) renaming (map to Any-map)
open import Data.Nat using (ℕ; _≤_; z≤n; s≤s)
open import Data.Nat.ListAction using (sum)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst; subst₂)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; cong to ≡-cong; cong₂ to ≡-cong₂)
open import Relation.Nullary using (¬_)
open import Relation.Unary.Properties using (∁?)
open import Relation.Nullary.Decidable using (Dec; yes; no; ¬?; _⊎-dec_; _×-dec_)
import Data.List.Relation.Binary.Permutation.Homogeneous as H
import Data.List.Relation.Binary.Permutation.Propositional as ↭
open ↭ using (_↭_; ↭-refl; ↭-sym; ↭-trans; ↭-reflexive)
import Data.List.Relation.Unary.All.Properties as AllP
import Data.List.Relation.Unary.Linked.Properties as LinkedP
import Data.List.Sort.Base as SortBase
import Data.List.Sort.MergeSort as MergeSort
import Relation.Binary.Properties.StrictTotalOrder as StrictTotalOrderP
import Data.List.Relation.Unary.AllPairs.Properties as AllPairsP
import Data.Sum.Properties as SumP
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
-- splits the region containing one. The moves preserve the invariant that the stored regions are
-- the regions of the hidden set with their summaries, and are mutually inverse. Adjacency is
-- decided through a width witness exhibiting each vertex object as a free semimodule, by reading
-- an edge's matrix off basis vectors.
module interaction.moves {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (let module S = CommutativeSemiring S)
  (+-idem : ∀ x → (x S.+ x) S.≈ x)
  (≡-of-≈ : ∀ {x y} → x S.≈ y → x ≡ y)
  (ε? : (x : S.Carrier) → Dec (x ≡ S.ε)) where

open import interaction.graph S +-idem
open import matrix-embedding S using (𝔽; mat; mat-cong; mat-ε; 𝔽F-full)
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
-- graph. No invariant is imposed; that the pairs are the regions of the hidden set with their
-- summaries is a property the moves preserve.
record Config {m : ℕ} {D : Derivation} (B : Graph m D) : Set₁ where
  field
    visible : List (Path D)
    hidden  : List (List (Path D) × EdgeLabels (vertex-object B))

open Config public

module Interaction {m : ℕ} {D : Derivation} (B : Graph m D)
                   (first-order : EdgeLabels (vertex-object B)) where

  private
    wd : V B → ℕ
    wd = vertex-width B

  private
    at : Path D → V B
    at p = inj₂ p

  open DecMem (_≟_ {D}) public using (_∈_; _∉_; _∈?_)

  _≢?_ : (p q : Path D) → Dec (p ≢ q)
  p ≢? q = ¬? (_≟_ {D} p q)

  entry : ∀ (x y : V B) → (vertex-object B x ⇒ vertex-object B y) → M.Matrix (wd y) (wd x)
  entry x y f = ∃ₛ.fst (𝔽F-full f)

  entry-ε : ∀ (x y : V B) (f : vertex-object B x ⇒ vertex-object B y) →
            (∀ i j → entry x y f i j ≡ S.ε) → f ≈ εₘ
  entry-ε x y f h =
    ≈-trans (≈-sym (∃ₛ.snd (𝔽F-full f)))
    (≈-trans (mat-cong (λ i j → ≈-of-≡ (h i j))) mat-ε)

  Adjacent : EdgeLabels (vertex-object B) → V B → V B → Set
  Adjacent G x y = NonZero (entry x y (G x y)) ⊎ NonZero (entry y x (G y x))

  Adjacent? : (G : EdgeLabels (vertex-object B)) (x y : V B) → Dec (Adjacent G x y)
  Adjacent? G x y = NonZero? (entry x y (G x y)) ⊎-dec NonZero? (entry y x (G y x))

  AdjacentIn : EdgeLabels (vertex-object B) → Path D → List (Path D) → Set
  AdjacentIn G p C = Any (λ q → Adjacent G (at p) (at q)) C

  adjacent-in? : (G : EdgeLabels (vertex-object B)) (p : Path D)
                 (C : List (Path D)) → Dec (AdjacentIn G p C)
  adjacent-in? G p C = any? (λ q → Adjacent? G (at p) (at q)) C

  adjacent-O : (G : EdgeLabels (vertex-object B)) (x y : V B) → ¬ Adjacent G x y →
               Prf ((G x y ≈ εₘ) ∧ₚ (G y x ≈ εₘ))
  adjacent-O G x y h =
    ⟪ entry-ε x y (G x y) (NonZero-O (entry x y (G x y)) (λ k → h (inj₁ k))) ,ₚ
      entry-ε y x (G y x) (NonZero-O (entry y x (G y x)) (λ k → h (inj₂ k))) ⟫

  merge-region : EdgeLabels (vertex-object B) → Path D → List (List (Path D)) →
                 List (List (Path D))
  merge-region G w rss = (w ∷ concat (proj₁ tp)) ∷ proj₂ tp
    where tp = L.partition (adjacent-in? G w) rss

  regions : EdgeLabels (vertex-object B) → List (Path D) → List (List (Path D))
  regions G []       = []
  regions G (w ∷ ws) = merge-region G w (regions G ws)

  -- The inputs and the root are never hidden, so only an interior vertex can lie in a region.
  VertexIn : V B → List (Path D) → Set
  VertexIn (inj₁ _) C = ⊥
  VertexIn (inj₂ p) C = p ∈ C

  _∈ᵥ?_ : (z : V B) (C : List (Path D)) → Dec (VertexIn z C)
  inj₁ _        ∈ᵥ? C = no (λ ())
  inj₂ p ∈ᵥ? C = p ∈? C

  Adj-p : Path D → List (Path D) × EdgeLabels (vertex-object B) → Set
  Adj-p p CH = AdjacentIn first-order p (proj₁ CH)

  adj-p? : (p : Path D)
           (CH : List (Path D) × EdgeLabels (vertex-object B)) → Dec (Adj-p p CH)
  adj-p? p CH = adjacent-in? first-order p (proj₁ CH)

  restrict : EdgeLabels (vertex-object B) → List (Path D) → EdgeLabels (vertex-object B)
  restrict G C x y = when (x ∈ᵥ? C ⊎-dec y ∈ᵥ? C) (G x y)

  -- The summary of a hidden region: the dependence routed through it, as relations between the
  -- vertices adjacent to it. Restriction first, so direct edges between boundary vertices are not
  -- carried by the summary.
  summary : List (Path D) → EdgeLabels (vertex-object B)
  summary C = hide-all (vertex-object B) (restrict first-order C) (map at C)

  Summary : Set
  Summary = List (Path D) → EdgeLabels (vertex-object B)

  initial : Summary → Config B
  initial summarise .visible = []
  initial summarise .hidden  = map (λ C → C , summarise C) (regions first-order (FO B))

  hidden-set : Config B → List (Path D)
  hidden-set K = concat (map proj₁ (K .hidden))

  hidden-∈ : ∀ {p} (K : Config B) → p ∈ hidden-set K → Any (λ CH → p ∈ proj₁ CH) (K .hidden)
  hidden-∈ K h = AnyPr.map⁻ (∈-concat⁻ (map proj₁ (K .hidden)) h)

  hidden-∉ : ∀ {p} (K : Config B) → p ∉ hidden-set K → All (λ CH → p ∉ proj₁ CH) (K .hidden)
  hidden-∉ K h = All-tabulate (λ m k → h (∈-concat⁺′ k (∈-map⁺ proj₁ m)))

  visible-graph : Config B → EdgeLabels (vertex-object B)
  visible-graph K x y =
    foldr _+ₘ_
          (when (¬? (x ∈ᵥ? hs) ×-dec ¬? (y ∈ᵥ? hs)) (first-order x y))
          (map (λ CH → proj₂ CH x y) (K .hidden))
    where hs = hidden-set K

  hide-at : Summary → Path D → Config B → Config B
  hide-at summarise p K .visible = filter (p ≢?_) (K .visible)
  hide-at summarise p K .hidden  = (C , summarise C) ∷ proj₂ tp
    where
      tp = L.partition (adj-p? p) (K .hidden)
      C  = p ∷ concat (map proj₁ (proj₁ tp))

  split-region : Summary → Path D →
                 List (Path D) × EdgeLabels (vertex-object B) →
                 List (List (Path D) × EdgeLabels (vertex-object B))
  split-region summarise p (C , H) with p ∈? C
  ... | yes _ = map (λ C' → C' , summarise C') (regions first-order (filter (p ≢?_) C))
  ... | no  _ = (C , H) ∷ []

  split-region-∈ : ∀ (summarise : Summary) p C (H : EdgeLabels (vertex-object B)) → p ∈ C →
                   split-region summarise p (C , H) ≡
                   map (λ C' → C' , summarise C') (regions first-order (filter (p ≢?_) C))
  split-region-∈ summarise p C H h with p ∈? C
  ... | yes _ = ≡-refl
  ... | no ¬k = ⊥-elim (¬k h)

  split-region-∉ : ∀ (summarise : Summary) p C (H : EdgeLabels (vertex-object B)) → p ∉ C →
                   split-region summarise p (C , H) ≡ (C , H) ∷ []
  split-region-∉ summarise p C H h with p ∈? C
  ... | yes k = ⊥-elim (h k)
  ... | no  _ = ≡-refl

  reveal-at : Summary → Path D → Config B → Config B
  reveal-at summarise p K .visible = p ∷ K .visible
  reveal-at summarise p K .hidden  = concat (map (split-region summarise p) (K .hidden))

module _ {m : ℕ} {D : Derivation} (𝒢 : Graph m D) where

  open Interaction 𝒢 (fo-graph 𝒢)

  private
    module Hide-𝒢 = Hide (V 𝒢) (vertex-object 𝒢)

    at : Path D → V 𝒢
    at p = inj₂ p

  restrict-forward : {G : EdgeLabels (vertex-object 𝒢)} (C : List (Path D)) → Fwd 𝒢 G → Fwd 𝒢 (restrict G C)
  restrict-forward {G} C fwd x y with x ∈ᵥ? C ⊎-dec y ∈ᵥ? C
  ... | yes _ = fwd x y
  ... | no  _ = inj₂ ⟪ ≈-refl ⟫

  private
    module Vertex≤ = StrictTotalOrderP (vertex-order D)
    module MS = MergeSort Vertex≤.decTotalOrder
    open SortBase.SortingAlgorithm MS.mergeSort using (sort; sort-↭; sort-↗)
    open IsStrictOrder (lt-order D) using (asym; irrefl)

    sorted-forward : {G : EdgeLabels (vertex-object 𝒢)} → Fwd 𝒢 G → {C : List (Path D)} →
                     AllPairs Vertex≤._≤_ C →
                     AllPairs (λ v u → Prf (G u v ≈ εₘ)) (map at C)
    sorted-forward fwd hs =
      AllPairsP.map⁺
        (AllPairs-map (λ {q} {q'} le → [ (λ l → ⊥-elim (no-back le l)) , (λ e → e) ]′ (fwd (at q') (at q)))
                      hs)
      where
      no-back : ∀ {q q'} → Vertex≤._≤_ q q' → lt D q' q → ⊥
      no-back {q} {q'} (inj₁ l)      l' = asym q q' l l'
      no-back {q}      (inj₂ ≡-refl) l' = irrefl q l'

  private
    sources : List (V 𝒢)
    sources = inj₁ input ∷ map at (vertices D) ++ (inj₂ ε ∷ [])

    _≟ᵥ_ : (x y : V 𝒢) → Dec (x ≡ y)
    _≟ᵥ_ = SumP.≡-dec input-≟ (_≟_ {D})

    hid-first-order : List (V 𝒢)
    hid-first-order = map at (sort (fo-hidden 𝒢))

    -- Stored tables for hiding hid in G: one tabulated pass per source vertex, read by lookup. A
    -- reader applied to a store captures it, so a stored summary shares its tables across reads.
    module Rows (G : EdgeLabels (vertex-object 𝒢)) (hid : List (V 𝒢)) where

      private
        module TG = Tabulated 𝒢 G (λ _ x → x)

        force-list : {A : Set} → List A → List A
        force-list []       = []
        force-list (x ∷ xs) = primForce x λ x' → primForce (force-list xs) λ xs' → x' ∷ xs'

        force-table : TG.Table → TG.Table
        force-table t = force-list (map force-list t)

        force-tables : List (V 𝒢 × TG.Table) → List (V 𝒢 × TG.Table)
        force-tables []             = []
        force-tables ((v , t) ∷ ts) = primForce (force-table t) λ t' → (v , t') ∷ force-tables ts

        row : (a : V 𝒢) → List (V 𝒢 × TG.Table)
        row a = force-tables (TG.summaries 0 a [] hid)

        force-list-id : {A : Set} (xs : List A) → force-list xs ≡ xs
        force-list-id []       = ≡-refl
        force-list-id (x ∷ xs) =
          ≡-trans (primForceLemma x _)
                  (≡-trans (primForceLemma (force-list xs) _) (≡-cong (x ∷_) (force-list-id xs)))

        force-table-id : (t : TG.Table) → force-table t ≡ t
        force-table-id t = ≡-trans (force-list-id (map force-list t)) (rows-id t)
          where
          rows-id : (t : TG.Table) → map force-list t ≡ t
          rows-id []       = ≡-refl
          rows-id (r ∷ rs) = ≡-cong₂ _∷_ (force-list-id r) (rows-id rs)

        force-tables-id : (ts : List (V 𝒢 × TG.Table)) → force-tables ts ≡ ts
        force-tables-id []             = ≡-refl
        force-tables-id ((v , t) ∷ ts) =
          ≡-trans (primForceLemma (force-table t) _)
                  (≡-cong₂ (λ t' ts' → (v , t') ∷ ts') (force-table-id t) (force-tables-id ts))

      Store : Set
      Store = List (V 𝒢 × List (V 𝒢 × TG.Table))

      store : Store
      store = map (λ a → a , row a) sources

      private
        find : (x : V 𝒢) → Store → List (V 𝒢 × TG.Table)
        find x []             = row x
        find x ((a , t) ∷ ts) with x ≟ᵥ a
        ... | yes _ = t
        ... | no  _ = find x ts

        find-row : ∀ x as → find x (map (λ a → a , row a) as) ≡ row x
        find-row x []       = ≡-refl
        find-row x (a ∷ as) with x ≟ᵥ a
        ... | yes ≡-refl = ≡-refl
        ... | no  _      = find-row x as

      read : Store → EdgeLabels (vertex-object 𝒢)
      read ts x y =
        mat (TG.look {vertex-width 𝒢 y} {vertex-width 𝒢 x} (TG.through x y (find x ts)))

      read-agrees : AllPairs (λ v u → Prf (G u v ≈ εₘ)) hid →
                    ∀ x y → read store x y ≈ hide-all (vertex-object 𝒢) G hid x y
      read-agrees pairs x y =
        ≈-trans (≡-to-≈ (≡-cong (λ r → mat (TG.look (TG.through x y r)))
                                (≡-trans (find-row x sources)
                                         (force-tables-id (TG.summaries 0 x [] hid)))))
                (tabulated-hide-all 𝒢 G hid x y pairs)

  Tables : Set
  Tables = Rows.Store (edge-labels 𝒢) hid-first-order

  first-order-tables : Tables
  first-order-tables = Rows.store (edge-labels 𝒢) hid-first-order

  tabulated-first-order : Tables → EdgeLabels (vertex-object 𝒢)
  tabulated-first-order = Rows.read (edge-labels 𝒢) hid-first-order

  tabulated-first-order-agrees : ∀ x y →
                                 tabulated-first-order first-order-tables x y ≈ fo-graph 𝒢 x y
  tabulated-first-order-agrees x y =
    ≈-trans (Rows.read-agrees (edge-labels 𝒢) hid-first-order
              (sorted-forward (edge-labels-forward 𝒢)
                (LinkedP.Linked⇒AllPairs Vertex≤.trans (sort-↗ (fo-hidden 𝒢)))) x y)
            (hide-all-perm 𝒢 (edge-labels-forward 𝒢) (map⁺ at (sort-↭ (fo-hidden 𝒢))) x y)

  -- The summary of a hidden region as a reader over its stored tables, the region sorted into
  -- evaluation order so that every nonzero edge among its vertices runs forward.
  tabulated-summary : EdgeLabels (vertex-object 𝒢) → Summary
  tabulated-summary first-order C =
    Rows.read (restrict first-order C) (map at (sort C))
              (Rows.store (restrict first-order C) (map at (sort C)))

  tabulated-summary-agrees : ∀ C x y → tabulated-summary (fo-graph 𝒢) C x y ≈ summary C x y
  tabulated-summary-agrees C x y =
    ≈-trans (Rows.read-agrees (restrict (fo-graph 𝒢) C) (map at (sort C))
              (sorted-forward fwd (LinkedP.Linked⇒AllPairs Vertex≤.trans (sort-↗ C))) x y)
            (hide-all-perm 𝒢 fwd (map⁺ at (sort-↭ C)) x y)
    where fwd = restrict-forward C (fo-forward 𝒢)

  adjacent-sym : (G : EdgeLabels (vertex-object 𝒢)) {x y : V 𝒢} → Adjacent G x y → Adjacent G y x
  adjacent-sym G = [ inj₂ , inj₁ ]′

  Apart : EdgeLabels (vertex-object 𝒢) → List (Path D) → List (Path D) → Set
  Apart G C C' = All (λ q → All (λ q' → ¬ Adjacent G (at q) (at q')) C') C

  apart-sym : (G : EdgeLabels (vertex-object 𝒢)) {C C' : List (Path D)} → Apart G C C' → Apart G C' C
  apart-sym G h =
    All-tabulate (λ m' → All-tabulate (λ m a → All-lookup (All-lookup h m) m' (adjacent-sym G a)))

  merge-separated : (G : EdgeLabels (vertex-object 𝒢)) (w : Path D) {rs : List (List (Path D))} →
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

  regions-separated : (G : EdgeLabels (vertex-object 𝒢)) (ws : List (Path D)) → AllPairs (Apart G) (regions G ws)
  regions-separated G []       = []
  regions-separated G (w ∷ ws) = merge-separated G w (regions-separated G ws)

  record Summarised (K : Config 𝒢) : Set where
    field
      partition : (K .visible ++ hidden-set K) ↭ FO 𝒢
      canonical : map proj₁ (K .hidden) ↭↭ regions (fo-graph 𝒢) (hidden-set K)
      summaries : All (λ CH → ∀ x y → Prf (proj₂ CH x y ≈ summary (proj₁ CH) x y))
                      (K .hidden)

  open Summarised public

  separated : {K : Config 𝒢} → Summarised K → AllPairs (Apart (fo-graph 𝒢)) (map proj₁ (K .hidden))
  separated {K} S =
    perm-AllPairs (λ {C} {C'} → apart-sym (fo-graph 𝒢) {C} {C'})
                  (λ {C} {C'} {C''} → resp C C' C'')
                  (H.sym ↭-sym (S .canonical))
                  (regions-separated (fo-graph 𝒢) (hidden-set K))
    where
    resp : (C C' C'' : List (Path D)) → C ↭ C' → Apart (fo-graph 𝒢) C C'' →
           Apart (fo-graph 𝒢) C' C''
    resp C C' C'' r ap = All-resp-↭ r ap

  regions-concat : (G : EdgeLabels (vertex-object 𝒢)) (ws : List (Path D)) → concat (regions G ws) ↭ ws
  regions-concat G []       = ↭.refl
  regions-concat G (w ∷ ws) =
    ↭.prep w (↭-trans (↭-reflexive (concat-++ (proj₁ tp) (proj₂ tp)))
             (↭-trans (concat-resp (↭↭-of-↭ (partition-↭ _ (regions G ws))))
                      (regions-concat G ws)))
    where tp = L.partition (adjacent-in? G w) (regions G ws)

  hide-at-hidden-set : (summarise : Summary) (p : Path D) (K : Config 𝒢) →
                       hidden-set (hide-at summarise p K) ↭ (p ∷ hidden-set K)
  hide-at-hidden-set summarise p K =
    ↭.prep p
      (↭-trans (↭-reflexive (concat-++ (map proj₁ (proj₁ tp)) (map proj₁ (proj₂ tp))))
      (↭-trans (↭-reflexive (≡-cong concat (≡-sym (map-++ proj₁ (proj₁ tp) (proj₂ tp)))))
               (concat-resp (↭↭-of-↭ (map⁺ proj₁ (partition-↭ _ (K .hidden)))))))
    where tp = L.partition (adj-p? p) (K .hidden)

  private
    mv-mono : {C E : List (Path D)} → C ⊆ E → ∀ {z} → VertexIn z C → VertexIn z E
    mv-mono mono {inj₂ q} h = mono h

  restrict-sub : (G : EdgeLabels (vertex-object 𝒢)) {C E : List (Path D)} → C ⊆ E →
                 ∀ x y → (restrict G C x y +ₘ restrict G E x y) ≈ restrict G E x y
  restrict-sub G {C} {E} mono x y =
    when-sub (x ∈ᵥ? C ⊎-dec y ∈ᵥ? C) (x ∈ᵥ? E ⊎-dec y ∈ᵥ? E) (G x y)
             [ (λ hx → inj₁ (mv-mono mono hx)) , (λ hy → inj₂ (mv-mono mono hy)) ]′

  restrict-agree : (G : EdgeLabels (vertex-object 𝒢)) {C E : List (Path D)} → C ⊆ E →
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

    visible-hidden-split : (K : Config 𝒢) → Summarised K →
                           AllPairs _≢_ (K .visible) × AllPairs _≢_ (hidden-set K) ×
                             All (λ p → All (p ≢_) (hidden-set K)) (K .visible)
    visible-hidden-split K S = AllPairs-++⁻ (K .visible) (hidden-set K) (partition-distinct K (S .partition))

  summarised-distinct : (K : Config 𝒢) → Summarised K → AllPairs Distinct (map proj₁ (K .hidden))
  summarised-distinct K S =
    concat-distinct (map proj₁ (K .hidden))
      (proj₁ (proj₂ (visible-hidden-split K S)))

  hide-at-partition : (summarise : Summary) (p : Path D) (K : Config 𝒢) → Summarised K →
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

  hide-at-summaries : (summarise : Summary) →
                      (∀ C x y → summarise C x y ≈ summary C x y) →
                      (p : Path D) (K : Config 𝒢) → Summarised K →
                      All (λ CH → ∀ x y → Prf (proj₂ CH x y ≈ summary (proj₁ CH) x y))
                          (hide-at summarise p K .hidden)
  hide-at-summaries summarise agrees p K S =
    (λ x y → ⟪ agrees (p ∷ concat (map proj₁ (proj₁ (L.partition (adj-p? p) (K .hidden))))) x y ⟫) ∷
    proj₂ (partition-All (adj-p? p) (S .summaries))

  Apart-mono : {G : EdgeLabels (vertex-object 𝒢)} {C₁ C₂ C₁' C₂' : List (Path D)} →
               C₁ ⊆ C₁' → C₂ ⊆ C₂' → Apart G C₁' C₂' → Apart G C₁ C₂
  Apart-mono m₁ m₂ ap = All-tabulate (λ h → All-tabulate (λ h' → All-lookup (All-lookup ap (m₁ h)) (m₂ h')))

  private
    split-none : (summarise : Summary) (p : Path D)
                 {CHs : List (List (Path D) × EdgeLabels (vertex-object 𝒢))} →
                 All (λ CH → p ∉ proj₁ CH) CHs →
                 concat (map (split-region summarise p) CHs) ≡ CHs
    split-none summarise p []                     = ≡-refl
    split-none summarise p (_∷_ {C , H} h hs) rewrite split-region-∉ summarise p C H h =
      ≡-cong ((C , H) ∷_) (split-none summarise p hs)

  reveal-set : (summarise : Summary) (p : Path D)
               (CHs : List (List (Path D) × EdgeLabels (vertex-object 𝒢))) →
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
                                   (map-proj₁-pair summarise Regs)
                                   (split-none summarise p no-p-tail)))
             (++⁺ head-perm ↭-refl)))
    where
    C∖p  = filter (p ≢?_) C
    Regs = regions (fo-graph 𝒢) C∖p
    Xs   = map (λ C' → C' , summarise C') Regs
    Zs   = concat (map (split-region summarise p) CHs)

    no-p-tail : All (λ CH → p ∉ proj₁ CH) CHs
    no-p-tail =
      All-tabulate (λ mCH k →
        All-lookup (All-lookup cross m) (∈-concat⁺′ k (∈-map⁺ proj₁ mCH)) ≡-refl)

    head-perm : (p ∷ concat Regs) ↭ C
    head-perm = ↭-trans (↭.prep p (regions-concat (fo-graph 𝒢) C∖p)) (filter-out-↭ (_≟_ {D}) aC m)

  private
    split-summaries : (summarise : Summary) →
                      (∀ C x y → summarise C x y ≈ summary C x y) →
                      (p : Path D)
                      (CH : List (Path D) × EdgeLabels (vertex-object 𝒢)) →
                      (∀ x y → Prf (proj₂ CH x y ≈ summary (proj₁ CH) x y)) →
                      All (λ CH' → ∀ x y → Prf (proj₂ CH' x y ≈ summary (proj₁ CH') x y))
                          (split-region summarise p CH)
    split-summaries summarise agrees p (C , H) old with p ∈? C
    ... | no  _ = old ∷ []
    ... | yes _ =
      AllP.map⁺ (universal (λ C' x y → ⟪ agrees C' x y ⟫)
                           (regions (fo-graph 𝒢) (filter (p ≢?_) C)))

  reveal-at-partition : (summarise : Summary) (p : Path D) (K : Config 𝒢) → Summarised K →
                        p ∈ hidden-set K →
                        (reveal-at summarise p K .visible ++ hidden-set (reveal-at summarise p K)) ↭ FO 𝒢
  reveal-at-partition summarise p K S hp =
    ↭-trans (↭-sym (shift p (K .visible) (hidden-set (reveal-at summarise p K))))
    (↭-trans (++⁺ ↭-refl
                (reveal-set summarise p (K .hidden)
                   (proj₁ (proj₂ (visible-hidden-split K S)))
                   (hidden-∈ K hp)))
             (S .partition))

  reveal-at-summaries : (summarise : Summary) →
                        (∀ C x y → summarise C x y ≈ summary C x y) →
                        (p : Path D) (K : Config 𝒢) → Summarised K →
                        All (λ CH → ∀ x y → Prf (proj₂ CH x y ≈ summary (proj₁ CH) x y))
                            (reveal-at summarise p K .hidden)
  reveal-at-summaries summarise agrees p K S =
    AllP.concat⁺ (AllP.map⁺ (All-map (λ {CH} old → split-summaries summarise agrees p CH old)
                                     (S .summaries)))

  private
    visible-graph-summary : (K : Config 𝒢) → Summarised K →
                            ∀ x y →
                            ¬ VertexIn x (hidden-set K) → ¬ VertexIn y (hidden-set K) →
                            visible-graph K x y ≈
                            (fo-graph 𝒢 x y +ₘ summary (hidden-set K) x y)
    visible-graph-summary K S x y hx hy =
      ≈-trans (foldr-base (when both-visible? (G x y)) (map (λ CH → proj₂ CH x y) (K .hidden)))
              (+ₘ-cong base-eq Σ-eq)
      where
      G  = fo-graph 𝒢
      Cs = map proj₁ (K .hidden)

      both-visible? = ¬? (x ∈ᵥ? hidden-set K) ×-dec ¬? (y ∈ᵥ? hidden-set K)

      base-eq : when both-visible? (G x y) ≈ G x y
      base-eq = when-yes both-visible? (hx , hy) (G x y)

      seps : AllPairs (λ C C' → Apart G C' C × Distinct C C') Cs
      seps = AllPairs-map (λ {C} {C'} (ap , d) → (apart-sym G {C} {C'} ap , d))
                          (AllPairs.zip (separated S , summarised-distinct K S))

      restrict-O : restrict G (hidden-set K) x y ≈ εₘ
      restrict-O = when-O (x ∈ᵥ? hidden-set K ⊎-dec y ∈ᵥ? hidden-set K) (G x y)
                          (set-elim.⊎-case (λ h → set-elim.⊥-elim (hx h)) (λ h → set-elim.⊥-elim (hy h)))

      Σ-eq : foldr _+ₘ_ εₘ (map (λ CH → proj₂ CH x y) (K .hidden)) ≈ summary (hidden-set K) x y
      Σ-eq =
        ≈-trans (foldr-map-≈ εₘ (λ CH → proj₂ CH x y) (λ CH → summary (proj₁ CH) x y) (K .hidden)
                  (All-map (λ inv → inv x y) (S .summaries)))
        (≈-trans (≡-to-≈ (≡-cong (foldr _+ₘ_ εₘ) (map-∘ {g = λ C → summary C x y} {f = proj₁} (K .hidden))))
        (≈-sym (≈-trans (assemble {E = hidden-set K} Cs (blocks-⊆ Cs) seps x y)
               (≈-trans (foldr-base (restrict G (hidden-set K) x y) (map (λ C → summary C x y) Cs))
               (≈-trans (+ₘ-cong restrict-O ≈-refl)
                        (+ₘ-lunit (foldr _+ₘ_ εₘ (map (λ C → summary C x y) Cs))))))))

  hide-reveal-visible : (summarise : Summary) (p : Path D) (K : Config 𝒢) → Summarised K →
                        p ∈ K .visible →
                        reveal-at summarise p (hide-at summarise p K) .visible ↭ K .visible
  hide-reveal-visible summarise p K S pv =
    filter-out-↭ (_≟_ {D})
                 (proj₁ (visible-hidden-split K S))
                 pv

  hide-reveal-hidden-set : (summarise : Summary) (p : Path D) (K : Config 𝒢) → Summarised K →
                           p ∈ K .visible →
                           hidden-set (reveal-at summarise p (hide-at summarise p K)) ↭ hidden-set K
  hide-reveal-hidden-set summarise p K S pv =
    drop-∷ (↭-trans (reveal-set summarise p (hide-at summarise p K .hidden)
                      (proj₁ (proj₂ (AllPairs-++⁻ (hide-at summarise p K .visible)
                                                  (hidden-set (hide-at summarise p K))
                                                  (partition-distinct (hide-at summarise p K)
                                                    (hide-at-partition summarise p K S pv)))))
                      (here (here ≡-refl)))
                    (hide-at-hidden-set summarise p K))

  private
    hidden-not-visible : (K : Config 𝒢) → Summarised K → ∀ {p} →
                         p ∈ hidden-set K →
                         p ∉ K .visible
    hidden-not-visible K S {p} hp k =
      All-lookup (All-lookup (proj₂ (proj₂ (visible-hidden-split K S)))
                             k)
                 hp ≡-refl

  reveal-hide-visible : (summarise : Summary) (p : Path D) (K : Config 𝒢) → Summarised K →
                        p ∈ hidden-set K →
                        hide-at summarise p (reveal-at summarise p K) .visible ≡ K .visible
  reveal-hide-visible summarise p K S hp =
    ≡-trans (filter-reject (p ≢?_) (λ k → k ≡-refl))
            (filter-all (p ≢?_)
              (All-tabulate (λ {q} m e →
                 hidden-not-visible K S {p = p} hp (subst (_∈ K .visible) (≡-sym e) m))))

  reveal-hide-hidden-set : (summarise : Summary) (p : Path D) (K : Config 𝒢) → Summarised K →
                           p ∈ hidden-set K →
                           hidden-set (hide-at summarise p (reveal-at summarise p K)) ↭ hidden-set K
  reveal-hide-hidden-set summarise p K S hp =
    ↭-trans (hide-at-hidden-set summarise p (reveal-at summarise p K))
            (reveal-set summarise p (K .hidden)
               (proj₁ (proj₂ (visible-hidden-split K S)))
               (hidden-∈ K hp))

  private
    restrict-≤ : (G : EdgeLabels (vertex-object 𝒢)) (C : List (Path D)) →
                 ∀ x y → (restrict G C x y +ₘ G x y) ≈ G x y
    restrict-≤ G C x y with x ∈ᵥ? C ⊎-dec y ∈ᵥ? C
    ... | yes _ = +ₘ-idem (G x y)
    ... | no  _ = +ₘ-lunit (G x y)

    restrict-hidden-agree : (G : EdgeLabels (vertex-object 𝒢)) (C : List (Path D)) →
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
                       ¬ VertexIn x (hidden-set K) → ¬ VertexIn y (hidden-set K) →
                       visible-graph K x y ≈
                       hide-all (vertex-object 𝒢) (fo-graph 𝒢) (map at (hidden-set K)) x y
  summaries-assemble K S x y hx hy =
    ≈-trans (visible-graph-summary K S x y hx hy)
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

  hide-reveal : (summarise : Summary) (p : Path D) (K : Config 𝒢) → Summarised K → p ∈ K .visible →
                reveal-at summarise p (hide-at summarise p K) ≈K K
  hide-reveal summarise p K S pv .visible-≈ = hide-reveal-visible summarise p K S pv
  hide-reveal summarise p K S pv .hidden-≈  = hide-reveal-hidden-set summarise p K S pv

  reveal-hide : (summarise : Summary) (p : Path D) (K : Config 𝒢) → Summarised K → p ∈ hidden-set K →
                hide-at summarise p (reveal-at summarise p K) ≈K K
  reveal-hide summarise p K S hp .visible-≈ = ↭-reflexive (reveal-hide-visible summarise p K S hp)
  reveal-hide summarise p K S hp .hidden-≈  = reveal-hide-hidden-set summarise p K S hp

  merge-region-resp : (G : EdgeLabels (vertex-object 𝒢)) (w : Path D) {rss rss' : List (List (Path D))} →
                      rss ↭↭ rss' → merge-region G w rss ↭↭ merge-region G w rss'
  merge-region-resp G w {rss} {rss'} p =
    H.prep (↭.prep w (concat-resp (proj₁ tp-p))) (proj₂ tp-p)
    where
    tp-p = partition-permᴿ (adjacent-in? G w) Any-resp-↭ (λ pc → Any-resp-↭ (↭-sym pc)) p

  private
    merge-region-filter : (G : EdgeLabels (vertex-object 𝒢)) (w : Path D) (rss : List (List (Path D))) →
                          merge-region G w rss ≡
                          ((w ∷ concat (filter (adjacent-in? G w) rss)) ∷
                           filter (∁? (adjacent-in? G w)) rss)
    merge-region-filter G w rss =
      ≡-cong (λ u → (w ∷ concat (proj₁ u)) ∷ proj₂ u) (partition-defn (adjacent-in? G w) rss)

    cross : (G : EdgeLabels (vertex-object 𝒢)) (u u' : Path D) (rss : List (List (Path D))) →
            AdjacentIn G u (u' ∷ concat (filter (adjacent-in? G u') rss)) →
            AdjacentIn G u' (u ∷ concat (filter (adjacent-in? G u) rss))
    cross G u u' rss (here a)  = here (adjacent-sym G a)
    cross G u u' rss (there m) =
      there (AnyPr.concat⁺ (Any-filter⁺ (adjacent-in? G u)
               (Any-filter⁻ (adjacent-in? G u') rss (AnyPr.concat⁻ (filter (adjacent-in? G u') rss) m))))

  merge-region-comm : (G : EdgeLabels (vertex-object 𝒢)) (w w' : Path D) (rss : List (List (Path D))) →
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

  regions-perm : (G : EdgeLabels (vertex-object 𝒢)) {ws ws' : List (Path D)} → ws ↭ ws' →
                 regions G ws ↭↭ regions G ws'
  regions-perm G ↭.refl         = ↭↭-refl
  regions-perm G (↭.prep w p)   = merge-region-resp G w (regions-perm G p)
  regions-perm G (↭.swap {xs = ws₁} {ys = ws₂} w w' p) =
    H.trans (merge-region-resp G w (merge-region-resp G w' (regions-perm G p)))
            (merge-region-comm G w w' (regions G ws₂))
  regions-perm G (↭.trans p q)  = H.trans (regions-perm G p) (regions-perm G q)

  private
    stored≡ : (summarise : Summary) →
              map proj₁ (initial summarise .hidden) ≡ regions (fo-graph 𝒢) (FO 𝒢)
    stored≡ summarise = map-proj₁-pair summarise (regions (fo-graph 𝒢) (FO 𝒢))

  initial-summarised : (summarise : Summary) →
                       (∀ C x y → summarise C x y ≈ summary C x y) →
                       Summarised (initial summarise)
  initial-summarised summarise agrees .partition =
    subst (λ z → concat z ↭ FO 𝒢) (≡-sym (stored≡ summarise)) (regions-concat (fo-graph 𝒢) (FO 𝒢))
  initial-summarised summarise agrees .canonical =
    subst (λ z → z ↭↭ regions (fo-graph 𝒢) (concat z))
          (≡-sym (stored≡ summarise))
          (regions-perm (fo-graph 𝒢) (↭-sym (regions-concat (fo-graph 𝒢) (FO 𝒢))))
  initial-summarised summarise agrees .summaries =
    AllP.map⁺ (universal (λ C x y → ⟪ agrees C x y ⟫) (regions (fo-graph 𝒢) (FO 𝒢)))

  -- From the inputs to the root, the visible graph of the initial configuration is the collapse of
  -- the underlying graph: reading the stored region summaries computes the same dependence as
  -- hiding every interior vertex.
  root-not-hidden : (K : Config 𝒢) → Summarised K → ¬ VertexIn (inj₂ ε) (hidden-set K)
  root-not-hidden K S mem =
    All-lookup (vertices-no-ε D)
               (∈-resp-↭ (filterᵇ-split (fo-at D) (vertices D))
                         (∈-++⁺ʳ (fo-hidden 𝒢)
                                 (∈-resp-↭ (S .partition) (∈-++⁺ʳ (K .visible) mem))))
    ≡-refl

  initial-collapse : (summarise : Summary) →
                     (∀ C x y → summarise C x y ≈ summary C x y) →
                     visible-graph (initial summarise) (inj₁ input) (inj₂ ε) ≈ collapse 𝒢
  initial-collapse summarise agrees =
    ≈-trans (summaries-assemble (initial summarise) (initial-summarised summarise agrees)
              (inj₁ input) (inj₂ ε) (λ ())
              (root-not-hidden (initial summarise) (initial-summarised summarise agrees)))
            (≈-trans (hide-all-perm 𝒢 (fo-forward 𝒢)
                       (map⁺ at (initial-summarised summarise agrees .partition))
                       (inj₁ input) (inj₂ ε))
                     (fo-collapse 𝒢))

  hide-at-summarised : (summarise : Summary) →
                       (∀ C x y → summarise C x y ≈ summary C x y) →
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
    lhs-eq : merge-region (fo-graph 𝒢) p (map proj₁ (K .hidden)) ≡
             map proj₁ (hide-at summarise p K .hidden)
    lhs-eq =
      ≡-cong₂ (λ u v → (p ∷ concat u) ∷ v)
              (map-partition₁ proj₁ (adjacent-in? (fo-graph 𝒢) p) (K .hidden))
              (map-partition₂ proj₁ (adjacent-in? (fo-graph 𝒢) p) (K .hidden))
  hide-at-summarised summarise agrees p K S pv .summaries = hide-at-summaries summarise agrees p K S

  private
    regions-⊆ : (G : EdgeLabels (vertex-object 𝒢)) (ws : List (Path D)) → All (_⊆ ws) (regions G ws)
    regions-⊆ G ws = All-map (λ inc {_} h → ∈-resp-↭ (regions-concat G ws) (inc h)) (blocks-⊆ (regions G ws))

    merge-region-inert : (G : EdgeLabels (vertex-object 𝒢)) (w : Path D) (X' Y' : List (List (Path D))) →
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

  regions-apart : (G : EdgeLabels (vertex-object 𝒢)) (B' rest : List (Path D)) → Apart G B' rest →
                  regions G (B' ++ rest) ↭↭ (regions G B' ++ regions G rest)
  regions-apart G []       rest ap = ↭↭-refl
  regions-apart G (b ∷ B') rest (hb ∷ hB) =
    H.trans (merge-region-resp G b (regions-apart G B' rest hB))
            (↭↭-of-≡ (merge-region-inert G b (regions G B') (regions G rest)
              (All-map (λ {C} inc →
                 AllP.All¬⇒¬Any (All-tabulate (λ h → All-lookup hb (inc h))))
                (regions-⊆ G rest))))

  private
    apart-concat : {G : EdgeLabels (vertex-object 𝒢)} {C : List (Path D)} {Cs : List (List (Path D))} →
                   All (Apart G C) Cs → Apart G C (concat Cs)
    apart-concat aps = All-tabulate (λ m → AllP.concat⁺ (All-map (λ ap → All-lookup ap m) aps))

    regions-nonempty : (G : EdgeLabels (vertex-object 𝒢)) (ws : List (Path D)) →
                       All (λ C → 1 ≤ length C) (regions G ws)
    regions-nonempty G []       = []
    regions-nonempty G (w ∷ ws) = s≤s z≤n ∷ proj₂ (partition-All (adjacent-in? G w) (regions-nonempty G ws))

  regions-apart-concat : {G : EdgeLabels (vertex-object 𝒢)} {Cs : List (List (Path D))} →
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

  reveal-at-summarised : (summarise : Summary) →
                         (∀ C x y → summarise C x y ≈ summary C x y) →
                         (p : Path D) (K : Config 𝒢) (S : Summarised K) →
                         p ∈ hidden-set K →
                         Summarised (reveal-at summarise p K)
  reveal-at-summarised summarise agrees p K S hp .partition = reveal-at-partition summarise p K S hp
  reveal-at-summarised summarise agrees p K S hp .summaries = reveal-at-summaries summarise agrees p K S
  reveal-at-summarised summarise agrees p K S hp .canonical =
    subst (λ z → z ↭↭ regions G (hidden-set (reveal-at summarise p K)))
          (≡-trans (≡-cong concat (map-∘ {g = map proj₁} {f = split-region summarise p} (K .hidden)))
                   (concat-map {f = proj₁} (map (split-region summarise p) (K .hidden))))
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
    distinct-hs = proj₁ (proj₂ (visible-hidden-split K S))

    hrev : hidden-set (reveal-at summarise p K) ↭ filter notp (hidden-set K)
    hrev = drop-∷
      (↭-trans (reveal-set summarise p (K .hidden) distinct-hs (hidden-∈ K hp))
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

    maps-eq : map (λ CH → regions G (filter notp (proj₁ CH))) (K .hidden) ≡
              map (regions G) (map (filter notp) Cs)
    maps-eq =
      ≡-trans (map-∘ {g = λ C → regions G (filter notp C)} {f = proj₁} (K .hidden))
              (map-∘ {g = regions G} {f = filter notp} Cs)

    per-block : ∀ CH → regions G (proj₁ CH) ↭↭ (proj₁ CH ∷ []) →
                map proj₁ (split-region summarise p CH) ↭↭ regions G (filter notp (proj₁ CH))
    per-block (C , H') one =
      dec-case (p ∈? C)
        (λ k → ↭↭-of-≡ (≡-trans (≡-cong (map proj₁) (split-region-∈ summarise p C H' k))
                                (map-proj₁-pair summarise (regions G (filter notp C)))))
        (λ ¬k → subst₂ _↭↭_
                  (≡-sym (≡-cong (map proj₁) (split-region-∉ summarise p C H' ¬k)))
                  (≡-sym (≡-cong (regions G)
                           (filter-all (p ≢?_)
                             (All-tabulate (λ {q} m e' → ¬k (subst (_∈ C) (≡-sym e') m))))))
                  (H.sym ↭.↭-sym one))

    blocks-part : concat (map (λ CH → map proj₁ (split-region summarise p CH)) (K .hidden)) ↭↭
                  concat (map (λ CH → regions G (filter notp (proj₁ CH))) (K .hidden))
    blocks-part = concat-↭↭ (All-map (λ {CH} one → per-block CH one) (AllP.map⁻ (blocks-one-region K S)))
