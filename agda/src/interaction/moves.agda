{-# OPTIONS --prop --postfix-projections --safe #-}

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
open import Data.List.Relation.Unary.All using (All; []; _∷_; universal)
  renaming (map to All-map; tabulate to All-tabulate; lookup to All-lookup)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_) renaming (map to AllPairs-map)
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
import Data.List.Relation.Unary.AllPairs.Properties as AllPairsP
import Data.List.Relation.Unary.Any.Properties as AnyPr
import Data.Fin.Properties as FinP
import Data.List.Membership.DecPropositional as DecMem
import matrix
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import list

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

  εₛ : S.Carrier
  εₛ = S.ε

  absurd : ∀ {p} {P : Prop p} → ⊥ → P
  absurd ()

  dec-caseₚ : ∀ {a p} {A : Set a} {P : Prop p} → Dec A → (A → P) → (¬ A → P) → P
  dec-caseₚ (yes k)  t f = t k
  dec-caseₚ (no  ¬k) t f = f ¬k

  any-extract : ∀ {a q} {A' : Set a} {P : A' → Set a} {Q : Set q} {xs : List A'} →
                (∀ {x} → P x → Q) → Any P xs → Q
  any-extract f (here px)  = f px
  any-extract f (there a₁) = any-extract f a₁

  ⊎-caseₚ : ∀ {a b p} {A' : Set a} {B' : Set b} {P : Prop p} → (A' → P) → (B' → P) → A' ⊎ B' → P
  ⊎-caseₚ f g (inj₁ x) = f x
  ⊎-caseₚ f g (inj₂ y) = g y

  foldr-base : ∀ {P Q : SemiMod.Semimodule} (b : P ⇒ Q) (ts : List (P ⇒ Q)) →
               foldr _+ₘ_ b ts ≈ (b +ₘ foldr _+ₘ_ εₘ ts)
  foldr-base b []       = ≈-sym (+ₘ-runit b)
  foldr-base b (t ∷ ts) = ≈-trans (+ₘ-cong ≈-refl (foldr-base b ts)) (+ₘ-swap-mid t b (foldr _+ₘ_ εₘ ts))

  foldr-resp-↭ : ∀ {P Q : SemiMod.Semimodule} (b : P ⇒ Q) {ts ts' : List (P ⇒ Q)} → ts ↭ ts' →
                 foldr _+ₘ_ b ts ≈ foldr _+ₘ_ b ts'
  foldr-resp-↭ b ↭.refl         = ≈-refl
  foldr-resp-↭ b (↭.prep t q)   = +ₘ-cong ≈-refl (foldr-resp-↭ b q)
  foldr-resp-↭ b (↭.swap t u q) =
    ≈-trans (+ₘ-cong ≈-refl (+ₘ-cong ≈-refl (foldr-resp-↭ b q))) (+ₘ-swap-mid t u _)
  foldr-resp-↭ b (↭.trans q r)  = ≈-trans (foldr-resp-↭ b q) (foldr-resp-↭ b r)

  foldr-zeros : ∀ {P Q : SemiMod.Semimodule} (b : P ⇒ Q) {ts : List (P ⇒ Q)} →
                All (λ t → Prf (t ≈ εₘ)) ts → foldr _+ₘ_ b ts ≈ b
  foldr-zeros b []            = ≈-refl
  foldr-zeros b (⟪ e ⟫ ∷ es) = ≈-trans (+ₘ-cong e (foldr-zeros b es)) (+ₘ-lunit b)

  foldr-++ₕ : ∀ {P Q : SemiMod.Semimodule} (b : P ⇒ Q) (xs ys : List (P ⇒ Q)) →
              foldr _+ₘ_ b (xs ++ ys) ≡ foldr _+ₘ_ (foldr _+ₘ_ b ys) xs
  foldr-++ₕ b []       ys = ≡-refl
  foldr-++ₕ b (x ∷ xs) ys = ≡-cong (x +ₘ_) (foldr-++ₕ b xs ys)

  absorb-anyₕ : ∀ {P Q : SemiMod.Semimodule} (b : P ⇒ Q) {a : P ⇒ Q} {ts : List (P ⇒ Q)} →
                Any (λ t → Prf ((a +ₘ t) ≈ t)) ts → (a +ₘ foldr _+ₘ_ b ts) ≈ foldr _+ₘ_ b ts
  absorb-anyₕ b {a} {t ∷ ts} (here ⟪ e ⟫) =
    ≈-trans (≈-sym +ₘ-assoc) (+ₘ-cong e ≈-refl)
  absorb-anyₕ b {a} {t ∷ ts} (there m) =
    ≈-trans (+ₘ-swap-mid a t (foldr _+ₘ_ b ts)) (+ₘ-cong ≈-refl (absorb-anyₕ b m))

  foldr-map-≈ : ∀ {a} {A' : Set a} {P Q : SemiMod.Semimodule} (b : P ⇒ Q)
                (f g : A' → P ⇒ Q) (xs : List A') →
                All (λ x → Prf (f x ≈ g x)) xs →
                foldr _+ₘ_ b (map f xs) ≈ foldr _+ₘ_ b (map g xs)
  foldr-map-≈ b f g []       []            = ≈-refl
  foldr-map-≈ b f g (x ∷ xs) (⟪ e ⟫ ∷ es) = +ₘ-cong e (foldr-map-≈ b f g xs es)

  foldr-baseᶜ : ∀ {P Q : SemiMod.Semimodule} {b b' : P ⇒ Q} (ts : List (P ⇒ Q)) →
                b ≈ b' → foldr _+ₘ_ b ts ≈ foldr _+ₘ_ b' ts
  foldr-baseᶜ []       e = e
  foldr-baseᶜ (t ∷ ts) e = +ₘ-cong ≈-refl (foldr-baseᶜ ts e)

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
  when-yes (no  ¬h) h f = absurd (¬h h)

  when-O : ∀ {p} {P : Set p} (d : Dec P) {X Y : SemiMod.Semimodule} (f : X ⇒ Y) →
           (P → f ≈ εₘ) → when d f ≈ εₘ
  when-O (no  _) f h = ≈-refl
  when-O (yes k) f h = h k

  when-sub : ∀ {p q} {P : Set p} {Q : Set q} (d₁ : Dec P) (d₂ : Dec Q)
             {X Y : SemiMod.Semimodule} (f : X ⇒ Y) → (P → Q) →
             (when d₁ f +ₘ when d₂ f) ≈ when d₂ f
  when-sub (no  _) d₂        f imp = +ₘ-lunit (when d₂ f)
  when-sub (yes k) (yes _)   f imp = +ₘ-idem f
  when-sub (yes k) (no  ¬k') f imp = absurd (¬k' (imp k))

-- A configuration: the visible set, and one pair per hidden region of a set of vertices and a
-- graph. No invariant is imposed; that the pairs are the regions of the hidden set with their
-- summaries is a property the moves preserve.
record Config {X Y : SemiMod.Semimodule} (B : Graph X Y) : Set₁ where
  field
    visible : List (Vertex (Graph.shape B))
    hidden  : List (List (Vertex (Graph.shape B)) × Relation (vertex-object B))

open Config public

module Interaction {X Y : SemiMod.Semimodule} (B : Graph X Y)
                   (wd : V B → ℕ) (free : ∀ v → vertex-object B v ≡ 𝔽 (wd v)) where

  private
    at : Vertex (Graph.shape B) → V B
    at p = inj₂ (inj₁ p)

  open DecMem (_≟_ {Graph.shape B}) public using (_∈_; _∉_; _∈?_)

  _≢?_ : (p q : Vertex (Graph.shape B)) → Dec (p ≢ q)
  p ≢? q = ¬? (_≟_ {Graph.shape B} p q)

  entry : ∀ (x y : V B) → (vertex-object B x ⇒ vertex-object B y) → M.Matrix (wd y) (wd x)
  entry x y f = ∃ₛ.fst (𝔽F-full (subst₂ _⇒_ (free x) (free y) f))

  private
    unsubst-ε : ∀ {V₁ V₂ W₁ W₂ : SemiMod.Semimodule} (e₁ : V₁ ≡ W₁) (e₂ : V₂ ≡ W₂) (f : V₁ ⇒ V₂) →
                subst₂ _⇒_ e₁ e₂ f ≈ εₘ → f ≈ εₘ
    unsubst-ε ≡-refl ≡-refl f h = h

  entry-ε : ∀ (x y : V B) (f : vertex-object B x ⇒ vertex-object B y) →
            (∀ i j → entry x y f i j ≡ εₛ) → f ≈ εₘ
  entry-ε x y f h =
    unsubst-ε (free x) (free y) f
      (≈-trans (≈-sym (∃ₛ.snd (𝔽F-full (subst₂ _⇒_ (free x) (free y) f))))
      (≈-trans (mat-cong (λ i j → ≈-of-≡ (h i j))) mat-ε))

  Adjacent : Relation (vertex-object B) → V B → V B → Set
  Adjacent G x y = NonZero (entry x y (G x y)) ⊎ NonZero (entry y x (G y x))

  Adjacent? : (G : Relation (vertex-object B)) (x y : V B) → Dec (Adjacent G x y)
  Adjacent? G x y = NonZero? (entry x y (G x y)) ⊎-dec NonZero? (entry y x (G y x))

  AdjacentIn : Relation (vertex-object B) → Vertex (Graph.shape B) → List (Vertex (Graph.shape B)) → Set
  AdjacentIn G p C = Any (λ q → Adjacent G (at p) (at q)) C

  adjacent-in? : (G : Relation (vertex-object B)) (p : Vertex (Graph.shape B))
                 (C : List (Vertex (Graph.shape B))) → Dec (AdjacentIn G p C)
  adjacent-in? G p C = any? (λ q → Adjacent? G (at p) (at q)) C

  adjacent-O : (G : Relation (vertex-object B)) (x y : V B) → ¬ Adjacent G x y →
               Prf ((G x y ≈ εₘ) ∧ₚ (G y x ≈ εₘ))
  adjacent-O G x y h =
    ⟪ entry-ε x y (G x y) (NonZero-O (entry x y (G x y)) (λ k → h (inj₁ k))) ,ₚ
      entry-ε y x (G y x) (NonZero-O (entry y x (G y x)) (λ k → h (inj₂ k))) ⟫

  merge-region : Relation (vertex-object B) → Vertex (Graph.shape B) → List (List (Vertex (Graph.shape B))) →
                 List (List (Vertex (Graph.shape B)))
  merge-region G w rss = (w ∷ concat (proj₁ tp)) ∷ proj₂ tp
    where tp = L.partition (adjacent-in? G w) rss

  regions : Relation (vertex-object B) → List (Vertex (Graph.shape B)) → List (List (Vertex (Graph.shape B)))
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

  Adj-p : Vertex (Graph.shape B) → List (Vertex (Graph.shape B)) × Relation (vertex-object B) → Set
  Adj-p p CH = AdjacentIn (fo-graph B) p (proj₁ CH)

  adj-p? : (p : Vertex (Graph.shape B))
           (CH : List (Vertex (Graph.shape B)) × Relation (vertex-object B)) → Dec (Adj-p p CH)
  adj-p? p CH = adjacent-in? (fo-graph B) p (proj₁ CH)

  restrict : Relation (vertex-object B) → List (Vertex (Graph.shape B)) → Relation (vertex-object B)
  restrict G C x y = when (x ∈ᵥ? C ⊎-dec y ∈ᵥ? C) (G x y)

  -- The summary of a hidden region: the dependence routed through it, as relations between the
  -- vertices adjacent to it. Restriction first, so direct edges between boundary vertices are not
  -- carried by the summary.
  summary : List (Vertex (Graph.shape B)) → Relation (vertex-object B)
  summary C = hide-all (vertex-object B) (restrict (fo-graph B) C) (map at C)

  initial : Config B
  initial .visible = []
  initial .hidden  = map (λ C → C , summary C) (regions (fo-graph B) (FO B))

  hidden-set : Config B → List (Vertex (Graph.shape B))
  hidden-set K = concat (map proj₁ (K .hidden))

  hidden-∈ : ∀ {p} (K : Config B) → p ∈ hidden-set K → Any (λ CH → p ∈ proj₁ CH) (K .hidden)
  hidden-∈ K h = AnyPr.map⁻ (∈-concat⁻ (map proj₁ (K .hidden)) h)

  hidden-∉ : ∀ {p} (K : Config B) → p ∉ hidden-set K → All (λ CH → p ∉ proj₁ CH) (K .hidden)
  hidden-∉ K h = All-tabulate (λ m k → h (∈-concat⁺′ k (∈-map⁺ proj₁ m)))

  visible-graph : Config B → Relation (vertex-object B)
  visible-graph K x y =
    foldr _+ₘ_
          (when (¬? (x ∈ᵥ? hs) ×-dec ¬? (y ∈ᵥ? hs)) (fo-graph B x y))
          (map (λ CH → proj₂ CH x y) (K .hidden))
    where hs = hidden-set K

  _+G_ : Relation (vertex-object B) → Relation (vertex-object B) → Relation (vertex-object B)
  (G +G H) x y = G x y +ₘ H x y

  hide-at : Vertex (Graph.shape B) → Config B → Config B
  hide-at p K .visible = filter (p ≢?_) (K .visible)
  hide-at p K .hidden  =
    (p ∷ concat (map proj₁ (proj₁ tp)) , hide (vertex-object B) assembled (at p)) ∷ proj₂ tp
    where
      tp = L.partition (adj-p? p) (K .hidden)
      assembled = foldr _+G_ (restrict (visible-graph K) (p ∷ [])) (map proj₂ (proj₁ tp))

  split-region : Vertex (Graph.shape B) → List (Vertex (Graph.shape B)) × Relation (vertex-object B) →
                 List (List (Vertex (Graph.shape B)) × Relation (vertex-object B))
  split-region p (C , H) with p ∈? C
  ... | yes _ = map (λ C' → C' , summary C') (regions (fo-graph B) (filter (p ≢?_) C))
  ... | no  _ = (C , H) ∷ []

  split-region-∈ : ∀ p C (H : Relation (vertex-object B)) → p ∈ C →
                   split-region p (C , H) ≡
                   map (λ C' → C' , summary C') (regions (fo-graph B) (filter (p ≢?_) C))
  split-region-∈ p C H h with p ∈? C
  ... | yes _ = ≡-refl
  ... | no ¬k = ⊥-elim (¬k h)

  split-region-∉ : ∀ p C (H : Relation (vertex-object B)) → p ∉ C → split-region p (C , H) ≡ (C , H) ∷ []
  split-region-∉ p C H h with p ∈? C
  ... | yes k = ⊥-elim (h k)
  ... | no  _ = ≡-refl

  reveal-at : Vertex (Graph.shape B) → Config B → Config B
  reveal-at p K .visible = p ∷ K .visible
  reveal-at p K .hidden  = concat (map (split-region p) (K .hidden))

module _ {X Y : SemiMod.Semimodule} (𝒢 : Graph X Y)
         (wd : V 𝒢 → ℕ) (free : ∀ v → vertex-object 𝒢 v ≡ 𝔽 (wd v)) where

  open Graph 𝒢 using (shape)

  Path : Set
  Path = Vertex shape
  open Interaction 𝒢 wd free

  private
    module Hide-𝒢 = Hide (V 𝒢) (vertex-object 𝒢)

    at : Path → V 𝒢
    at p = inj₂ (inj₁ p)


  restrict-forward : {G : Relation (vertex-object 𝒢)} (C : List (Path)) → Fwd 𝒢 G → Fwd 𝒢 (restrict G C)
  restrict-forward {G} C fwd x y with x ∈ᵥ? C ⊎-dec y ∈ᵥ? C
  ... | yes _ = fwd x y
  ... | no  _ = inj₂ ⟪ ≈-refl ⟫

  adjacent-sym : (G : Relation (vertex-object 𝒢)) {x y : V 𝒢} → Adjacent G x y → Adjacent G y x
  adjacent-sym G = [ inj₂ , inj₁ ]′

  Apart : Relation (vertex-object 𝒢) → List (Path) → List (Path) → Set
  Apart G C C' = All (λ q → All (λ q' → ¬ Adjacent G (at q) (at q')) C') C

  apart-sym : (G : Relation (vertex-object 𝒢)) {C C' : List (Path)} → Apart G C C' → Apart G C' C
  apart-sym G h =
    All-tabulate (λ m' → All-tabulate (λ m a → All-lookup (All-lookup h m) m' (adjacent-sym G a)))

  merge-separated : (G : Relation (vertex-object 𝒢)) (w : Path) {rs : List (List (Path))} →
                    AllPairs (Apart G) rs →
                    let tp = L.partition (adjacent-in? G w) rs in
                    AllPairs (Apart G) ((w ∷ concat (proj₁ tp)) ∷ proj₂ tp)
  merge-separated G w {rs} sep = apart-w ∷ proj₁ (proj₂ pa)
    where
    pa = partition-AllPairs {S = Apart G} (adjacent-in? G w) (λ {C} {C'} → apart-sym G {C} {C'}) sep
    tp = L.partition (adjacent-in? G w) rs
    apart-w : All (Apart G (w ∷ concat (proj₁ tp))) (proj₂ tp)
    apart-w =
      All-zip (λ {C'} hf hc → AllP.¬Any⇒All¬ C' hf ∷ AllP.concat⁺ hc)
              (part₂-¬ (adjacent-in? G w) rs) (proj₂ (proj₂ pa))

  regions-separated : (G : Relation (vertex-object 𝒢)) (ws : List (Path)) → AllPairs (Apart G) (regions G ws)
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
    resp : (C C' C'' : List (Path)) → C ↭ C' → Apart (fo-graph 𝒢) C C'' →
           Apart (fo-graph 𝒢) C' C''
    resp C C' C'' r ap = All-resp-↭ r ap

  regions-concat : (G : Relation (vertex-object 𝒢)) (ws : List (Path)) → concat (regions G ws) ↭ ws
  regions-concat G []       = ↭.refl
  regions-concat G (w ∷ ws) =
    ↭.prep w (↭-trans (↭-reflexive (concat-++ (proj₁ tp) (proj₂ tp)))
             (↭-trans (concat-resp (↭↭-of-↭ (partition-↭ _ (regions G ws))))
                      (regions-concat G ws)))
    where tp = L.partition (adjacent-in? G w) (regions G ws)

  hide-at-hidden-set : (p : Path) (K : Config 𝒢) → hidden-set (hide-at p K) ↭ (p ∷ hidden-set K)
  hide-at-hidden-set p K =
    ↭.prep p
      (↭-trans (↭-reflexive (concat-++ (map proj₁ (proj₁ tp)) (map proj₁ (proj₂ tp))))
      (↭-trans (↭-reflexive (≡-cong concat (≡-sym (map-++ proj₁ (proj₁ tp) (proj₂ tp)))))
               (concat-resp (↭↭-of-↭ (map⁺ proj₁ (partition-↭ _ (K .hidden)))))))
    where tp = L.partition (adj-p? p) (K .hidden)

  private
    mv-mono : {C E : List (Path)} → C ⊆ E → ∀ {z} → VertexIn z C → VertexIn z E
    mv-mono mono {inj₂ (inj₁ q)} h = mono h

  restrict-sub : (G : Relation (vertex-object 𝒢)) {C E : List (Path)} → C ⊆ E →
                 ∀ x y → (restrict G C x y +ₘ restrict G E x y) ≈ restrict G E x y
  restrict-sub G {C} {E} mono x y =
    when-sub (x ∈ᵥ? C ⊎-dec y ∈ᵥ? C) (x ∈ᵥ? E ⊎-dec y ∈ᵥ? E) (G x y)
             [ (λ hx → inj₁ (mv-mono mono hx)) , (λ hy → inj₂ (mv-mono mono hy)) ]′

  restrict-agree : (G : Relation (vertex-object 𝒢)) {C E : List (Path)} → C ⊆ E →
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

  localise : {C E : List (Path)} → C ⊆ E →
             ∀ x y →
             hide-all (vertex-object 𝒢) (restrict (fo-graph 𝒢) E) (map at C) x y ≈
             (restrict (fo-graph 𝒢) E x y +ₘ summary C x y)
  localise {C = C} {E = E} mono x y =
    Hide-𝒢.agree-add {G = restrict (fo-graph 𝒢) C} {G' = restrict (fo-graph 𝒢) E} (map at C)
      (λ x' y' → restrict-sub (fo-graph 𝒢) mono x' y')
      (restrict-agree (fo-graph 𝒢) mono)
      x y

  summary-zero : {C : List (Path)} (q : Path) → q ∉ C →
                 All (λ q' → ¬ Adjacent (fo-graph 𝒢) (at q) (at q')) C →
                 Prf (((z : V 𝒢) → summary C (at q) z ≈ εₘ)
                   ∧ₚ ((z : V 𝒢) → summary C z (at q) ≈ εₘ))
  summary-zero {C = C} q hm hadj =
    ⟪ Hide-𝒢.zero-fold {G = restrict (fo-graph 𝒢) C} (map at C) (at q) (base-row ,ₚ base-col) ⟫
    where
    entry-row : ∀ {z} → VertexIn z C → fo-graph 𝒢 (at q) z ≈ εₘ
    entry-row {inj₂ (inj₁ q')} hz =
      proj₁ₚ (Prf.prf (adjacent-O (fo-graph 𝒢) (at q) (at q') (All-lookup hadj hz)))

    entry-col : ∀ {z} → VertexIn z C → fo-graph 𝒢 z (at q) ≈ εₘ
    entry-col {inj₂ (inj₁ q')} hz =
      proj₂ₚ (Prf.prf (adjacent-O (fo-graph 𝒢) (at q) (at q') (All-lookup hadj hz)))

    base-row : (z : V 𝒢) → restrict (fo-graph 𝒢) C (at q) z ≈ εₘ
    base-row z =
      when-O (at q ∈ᵥ? C ⊎-dec z ∈ᵥ? C) (fo-graph 𝒢 (at q) z)
             (⊎-caseₚ (λ h → absurd (hm h)) (λ hz → entry-row hz))

    base-col : (z : V 𝒢) → restrict (fo-graph 𝒢) C z (at q) ≈ εₘ
    base-col z =
      when-O (z ∈ᵥ? C ⊎-dec at q ∈ᵥ? C) (fo-graph 𝒢 z (at q))
             (⊎-caseₚ (λ hz → entry-col hz) (λ h → absurd (hm h)))

  Distinct : List (Path) → List (Path) → Set
  Distinct C C' = All (_∉ C) C'

  distinct-sym : {C C' : List (Path)} → Distinct C C' → Distinct C' C
  distinct-sym d = All-tabulate (λ m k → All-lookup d k m)

  assemble : {E : List (Path)} (Cs : List (List (Path))) →
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
                All-zip (λ {q} ha hm → summary-zero {C = C} q hm ha)
                        ap ds)
              shead))

  private
    foldr-apply : (B : Relation (vertex-object 𝒢)) (Gs : List (Relation (vertex-object 𝒢))) →
                  ∀ x y →
                  foldr _+G_ B Gs x y ≡
                  foldr _+ₘ_ (B x y) (map (λ H → H x y) Gs)
    foldr-apply B []       x y = ≡-refl
    foldr-apply B (H ∷ Gs) x y = ≡-cong (H x y +ₘ_) (foldr-apply B Gs x y)

  blocks-⊆ : (Css : List (List (Path))) → All (_⊆ concat Css) Css
  blocks-⊆ []        = []
  blocks-⊆ (C ∷ Css) = ∈-++⁺ˡ ∷ All-map (λ g {_} h → ∈-++⁺ʳ C (g h)) (blocks-⊆ Css)

  summary-snoc : (p : Path) (C : List (Path)) →
                 ∀ x y →
                 summary (p ∷ C) x y ≈
                 hide (vertex-object 𝒢) (hide-all (vertex-object 𝒢) (restrict (fo-graph 𝒢) (p ∷ C)) (map at C)) (at p) x y
  summary-snoc p C x y =
    ≈-trans (hide-all-perm 𝒢 (restrict-forward (p ∷ C) (fo-forward 𝒢)) perm x y)
            (≡-to-≈ (≡-cong (λ H → H x y)
                    (foldl-++ (hide (vertex-object 𝒢)) (restrict (fo-graph 𝒢) (p ∷ C)) (map at C) (at p ∷ []))))
    where
    perm : (at p ∷ map at C) ↭ (map at C ++ (at p ∷ []))
    perm = ↭-sym (↭-trans (shift (at p) (map at C) [])
                          (↭-reflexive (≡-cong (at p ∷_) (++-identityʳ (map at C)))))

  merged-summary : (p : Path) (K : Config 𝒢) → Summarised K →
                   p ∉ hidden-set K →
                   AllPairs Distinct (map proj₁ (K .hidden)) →
                   let tp = L.partition (adj-p? p) (K .hidden) in
                   ∀ x y →
                   hide (vertex-object 𝒢) (foldr _+G_ (restrict (visible-graph K) (p ∷ []))
                                    (map proj₂ (proj₁ tp)))
                        (at p) x y
                   ≈ summary (p ∷ concat (map proj₁ (proj₁ tp))) x y
  merged-summary p K S hp dist x y =
    ≈-trans (Hide-𝒢.h-cong (at p) (λ x' y' → core x' y') x y)
            (≈-sym (summary-snoc p (concat Ms) x y))
    where
    G  = fo-graph 𝒢
    tp = L.partition (adj-p? p) (K .hidden)
    Ms = map proj₁ (proj₁ tp)
    C* = p ∷ concat Ms
    B = restrict (visible-graph K) (p ∷ [])

    sums-at : ∀ x' y' → List (vertex-object 𝒢 x' ⇒ vertex-object 𝒢 y')
    sums-at x' y' = map (λ C → summary C x' y') Ms

    Σat : ∀ x' y' → vertex-object 𝒢 x' ⇒ vertex-object 𝒢 y'
    Σat x' y' = foldr _+ₘ_ εₘ (sums-at x' y')

    u-adj : All (λ CH → ¬ Adj-p p CH) (proj₂ tp)
    u-adj = part₂-¬ (adj-p? p) (K .hidden)

    u-szero : All (λ CH →
                Prf (((z : V 𝒢) → summary (proj₁ CH) (at p) z ≈ εₘ)
                  ∧ₚ ((z : V 𝒢) → summary (proj₁ CH) z (at p) ≈ εₘ))) (proj₂ tp)
    u-szero = All-zip (λ {CH} hadj hm →
                        summary-zero {C = proj₁ CH} p hm (AllP.¬Any⇒All¬ (proj₁ CH) hadj))
                      u-adj
                (proj₂ (partition-All (adj-p? p) (hidden-∉ K hp)))

    stored₁-≈ : ∀ x' y' {b : vertex-object 𝒢 x' ⇒ vertex-object 𝒢 y'} →
                foldr _+ₘ_ b (map (λ CH → proj₂ CH x' y') (proj₁ tp)) ≈
                foldr _+ₘ_ b (sums-at x' y')
    stored₁-≈ x' y' {b} =
      ≈-trans (foldr-map-≈ b (λ CH → proj₂ CH x' y') (λ CH → summary (proj₁ CH) x' y') (proj₁ tp)
                (All-map (λ inv → inv x' y') (proj₁ (partition-All (adj-p? p) (S .summaries)))))
              (≡-to-≈ (≡-cong (foldr _+ₘ_ b) (map-∘ {g = λ C → summary C x' y'} {f = proj₁} (proj₁ tp))))

    maps-≈ : ∀ x' y' {b : vertex-object 𝒢 x' ⇒ vertex-object 𝒢 y'} →
             foldr _+ₘ_ b (map (λ H → H x' y') (map proj₂ (proj₁ tp))) ≈
             foldr _+ₘ_ b (sums-at x' y')
    maps-≈ x' y' {b} =
      ≈-trans (≡-to-≈ (≡-cong (foldr _+ₘ_ b) (≡-sym (map-∘ {g = λ H → H x' y'} {f = proj₂} (proj₁ tp)))))
              (stored₁-≈ x' y' {b})

    mv-p-≡ : ∀ {z} → VertexIn z (p ∷ []) → z ≡ at p
    mv-p-≡ {inj₂ (inj₁ q)} (here ≡-refl) = ≡-refl

    pguard-≡ : ∀ x' y' → VertexIn x' (p ∷ []) ⊎ VertexIn y' (p ∷ []) → (x' ≡ at p) ⊎ (y' ≡ at p)
    pguard-≡ x' y' = [ (λ e → inj₁ (mv-p-≡ e)) , (λ e → inj₂ (mv-p-≡ e)) ]′

    C*-of-p : ∀ {z} → VertexIn z (p ∷ []) → VertexIn z C*
    C*-of-p {inj₂ (inj₁ q)} (here e) = here e

    Ms-any : ∀ {z} → VertexIn z C* → ¬ VertexIn z (p ∷ []) → Any (λ C → VertexIn z C) Ms
    Ms-any {inj₂ (inj₁ q)} (here e)  np = ⊥-elim (np (here e))
    Ms-any {inj₂ (inj₁ q)} (there m) np = ∈-concat⁻ Ms m

    summary-absorb : ∀ (C : List (Path)) x' y' →
                     VertexIn x' C ⊎ VertexIn y' C →
                     (G x' y' +ₘ summary C x' y') ≈ summary C x' y'
    summary-absorb C x' y' gd =
      ≈-sym (≈-trans (Hide-𝒢.increasing (map at C) x' y')
                     (+ₘ-cong (when-yes (x' ∈ᵥ? C ⊎-dec y' ∈ᵥ? C) gd (G x' y')) ≈-refl))

    absorb-G : ∀ x' y' →
               Any (λ C → VertexIn x' C ⊎ VertexIn y' C) Ms →
               (G x' y' +ₘ Σat x' y') ≈ Σat x' y'
    absorb-G x' y' a =
      absorb-anyₕ εₘ (AnyPr.map⁺ (Any-map (λ {C} gd → ⟪ summary-absorb C x' y' gd ⟫) a))

    both-vis? : ∀ x' y' → Dec (¬ VertexIn x' (hidden-set K) × ¬ VertexIn y' (hidden-set K))
    both-vis? x' y' = ¬? (x' ∈ᵥ? hidden-set K) ×-dec ¬? (y' ∈ᵥ? hidden-set K)

    stored-vals : ∀ x' y' → List (vertex-object 𝒢 x' ⇒ vertex-object 𝒢 y')
    stored-vals x' y' = map (λ CH → proj₂ CH x' y') (K .hidden)

    sums-tail = proj₂ (partition-All (adj-p? p) (S .summaries))

    part₂-zero : ∀ x' y' →
                 (x' ≡ at p) ⊎ (y' ≡ at p) →
                 All (λ CH → Prf (proj₂ CH x' y' ≈ εₘ)) (proj₂ tp)
    part₂-zero .(at p) y' (inj₁ ≡-refl) =
      All-zip (λ inv zz → ⟪ ≈-trans (Prf.prf (inv (at p) y')) (proj₁ₚ (Prf.prf zz) y') ⟫) sums-tail u-szero
    part₂-zero x' .(at p) (inj₂ ≡-refl) =
      All-zip (λ inv zz → ⟪ ≈-trans (Prf.prf (inv x' (at p))) (proj₂ₚ (Prf.prf zz) x') ⟫) sums-tail u-szero

    stored-perm : ∀ x' y' →
                  stored-vals x' y' ↭
                  (map (λ CH → proj₂ CH x' y') (proj₁ tp) ++
                   map (λ CH → proj₂ CH x' y') (proj₂ tp))
    stored-perm x' y' =
      ↭-trans (map⁺ (λ CH → proj₂ CH x' y') (↭-sym (partition-↭ (adj-p? p) (K .hidden))))
              (↭-reflexive (map-++ (λ CH → proj₂ CH x' y') (proj₁ tp) (proj₂ tp)))

    stored-≈-Σ : ∀ x' y' →
                 (x' ≡ at p) ⊎ (y' ≡ at p) →
                 foldr _+ₘ_ εₘ (stored-vals x' y') ≈ Σat x' y'
    stored-≈-Σ x' y' side =
      ≈-trans (foldr-resp-↭ εₘ (stored-perm x' y'))
      (≈-trans (≡-to-≈ (foldr-++ₕ εₘ (map (λ CH → proj₂ CH x' y') (proj₁ tp))
                                     (map (λ CH → proj₂ CH x' y') (proj₂ tp))))
      (≈-trans (foldr-baseᶜ (map (λ CH → proj₂ CH x' y') (proj₁ tp))
                            (foldr-zeros εₘ (AllP.map⁺ (part₂-zero x' y' side))))
               (stored₁-≈ x' y')))

    visible-at-p : ∀ x' y' →
                   (x' ≡ at p) ⊎ (y' ≡ at p) →
                   visible-graph K x' y' ≈
                   (when (both-vis? x' y') (G x' y') +ₘ Σat x' y')
    visible-at-p x' y' side =
      ≈-trans (foldr-base (when (both-vis? x' y') (G x' y')) (stored-vals x' y'))
              (+ₘ-cong ≈-refl (stored-≈-Σ x' y' side))

    hid-split : ∀ {q} → q ∈ hidden-set K →
                Any (λ CH → q ∈ proj₁ CH) (proj₁ tp) ⊎ Any (λ CH → q ∈ proj₁ CH) (proj₂ tp)
    hid-split h =
      AnyPr.++⁻ (proj₁ tp) (Any-resp-↭ (↭-sym (partition-↭ (adj-p? p) (K .hidden))) (hidden-∈ K h))

    non-adj-zero : ∀ (q : Path) → Any (λ CH → q ∈ proj₁ CH) (proj₂ tp) →
                   Prf ((G (at p) (at q) ≈ εₘ) ∧ₚ (G (at q) (at p) ≈ εₘ))
    non-adj-zero q a =
      any-extract (λ {CH} (hq , hadj) →
                     adjacent-O G (at p) (at q)
                       (All-lookup (AllP.¬Any⇒All¬ (proj₁ CH) hadj) hq))
                  (Any-All a u-adj)

    at-inj₂ : ∀ {CHs} {q : Path} → Any (λ CH → q ∈ proj₁ CH) CHs →
              Any (λ C → q ∈ C) (map proj₁ CHs)
    at-inj₂ = AnyPr.map⁺

    vis-agree-row : ∀ y' →
                    (when (both-vis? (at p) y') (G (at p) y') +ₘ Σat (at p) y')
                    ≈ (G (at p) y' +ₘ Σat (at p) y')
    vis-agree-row (inj₁ i₀) =
      +ₘ-cong (when-yes (both-vis? (at p) (inj₁ i₀)) (hp , (λ ())) (G (at p) (inj₁ i₀))) ≈-refl
    vis-agree-row (inj₂ (inj₂ r)) =
      +ₘ-cong (when-yes (both-vis? (at p) (inj₂ (inj₂ r))) (hp , (λ ())) (G (at p) (inj₂ (inj₂ r)))) ≈-refl
    vis-agree-row (inj₂ (inj₁ q)) =
      dec-caseₚ (q ∈? hidden-set K)
        (λ hq →
          ≈-trans (+ₘ-cong (when-O (both-vis? (at p) (at q)) (G (at p) (at q))
                                   (λ bv → absurd (proj₂ bv hq))) ≈-refl)
          (≈-trans (+ₘ-lunit (Σat (at p) (at q)))
            (⊎-caseₚ (λ aM → ≈-sym (absorb-G (at p) (at q) (Any-map inj₂ (at-inj₂ aM))))
                     (λ aU → ≈-sym (≈-trans (+ₘ-cong (proj₁ₚ (Prf.prf (non-adj-zero q aU))) ≈-refl)
                                            (+ₘ-lunit (Σat (at p) (at q)))))
                     (hid-split hq))))
        (λ hq → +ₘ-cong (when-yes (both-vis? (at p) (at q)) (hp , hq) (G (at p) (at q))) ≈-refl)

    vis-agree-col : ∀ x' →
                    (when (both-vis? x' (at p)) (G x' (at p)) +ₘ Σat x' (at p))
                    ≈ (G x' (at p) +ₘ Σat x' (at p))
    vis-agree-col (inj₁ i₀) =
      +ₘ-cong (when-yes (both-vis? (inj₁ i₀) (at p)) ((λ ()) , hp) (G (inj₁ i₀) (at p))) ≈-refl
    vis-agree-col (inj₂ (inj₂ r)) =
      +ₘ-cong (when-yes (both-vis? (inj₂ (inj₂ r)) (at p)) ((λ ()) , hp) (G (inj₂ (inj₂ r)) (at p))) ≈-refl
    vis-agree-col (inj₂ (inj₁ q)) =
      dec-caseₚ (q ∈? hidden-set K)
        (λ hq →
          ≈-trans (+ₘ-cong (when-O (both-vis? (at q) (at p)) (G (at q) (at p))
                                   (λ bv → absurd (proj₁ bv hq))) ≈-refl)
          (≈-trans (+ₘ-lunit (Σat (at q) (at p)))
            (⊎-caseₚ (λ aM → ≈-sym (absorb-G (at q) (at p) (Any-map inj₁ (at-inj₂ aM))))
                     (λ aU → ≈-sym (≈-trans (+ₘ-cong (proj₂ₚ (Prf.prf (non-adj-zero q aU))) ≈-refl)
                                            (+ₘ-lunit (Σat (at q) (at p)))))
                     (hid-split hq))))
        (λ hq → +ₘ-cong (when-yes (both-vis? (at q) (at p)) (hq , hp) (G (at q) (at p))) ≈-refl)

    vis-agree : ∀ x' y' →
                (x' ≡ at p) ⊎ (y' ≡ at p) →
                (when (both-vis? x' y') (G x' y') +ₘ Σat x' y')
                ≈ (G x' y' +ₘ Σat x' y')
    vis-agree .(at p) y' (inj₁ ≡-refl) = vis-agree-row y'
    vis-agree x' .(at p) (inj₂ ≡-refl) = vis-agree-col x'

    base-agree : ∀ x' y' →
                 (B x' y' +ₘ Σat x' y') ≈
                 (restrict G C* x' y' +ₘ Σat x' y')
    base-agree x' y' =
      dec-caseₚ (x' ∈ᵥ? (p ∷ []) ⊎-dec y' ∈ᵥ? (p ∷ []))
        (λ bp →
          ≈-trans (+ₘ-cong (≈-trans (when-yes (x' ∈ᵥ? (p ∷ []) ⊎-dec y' ∈ᵥ? (p ∷ [])) bp
                                              (visible-graph K x' y'))
                                    (visible-at-p x' y' (pguard-≡ x' y' bp)))
                           ≈-refl)
          (≈-trans +ₘ-assoc
          (≈-trans (+ₘ-cong ≈-refl (+ₘ-idem (Σat x' y')))
          (≈-trans (vis-agree x' y' (pguard-≡ x' y' bp))
                   (≈-sym (+ₘ-cong (when-yes (x' ∈ᵥ? C* ⊎-dec y' ∈ᵥ? C*)
                                             ([ (λ e → inj₁ (C*-of-p e)) , (λ e → inj₂ (C*-of-p e)) ]′ bp)
                                             (G x' y'))
                                   ≈-refl))))))
        (λ ¬bp →
          dec-caseₚ (x' ∈ᵥ? C* ⊎-dec y' ∈ᵥ? C*)
            (λ cg →
              ≈-trans (+ₘ-cong (when-O (x' ∈ᵥ? (p ∷ []) ⊎-dec y' ∈ᵥ? (p ∷ [])) (visible-graph K x' y')
                                       (λ k → absurd (¬bp k)))
                               ≈-refl)
              (≈-trans (+ₘ-lunit (Σat x' y'))
              (≈-sym (≈-trans (+ₘ-cong (when-yes (x' ∈ᵥ? C* ⊎-dec y' ∈ᵥ? C*) cg (G x' y')) ≈-refl)
                              (absorb-G x' y'
                                 ([ (λ hx → Any-map inj₁ (Ms-any hx (λ k → ¬bp (inj₁ k))))
                                  , (λ hy → Any-map inj₂ (Ms-any hy (λ k → ¬bp (inj₂ k)))) ]′ cg))))))
            (λ ¬cg →
              +ₘ-cong
                (≈-trans (when-O (x' ∈ᵥ? (p ∷ []) ⊎-dec y' ∈ᵥ? (p ∷ [])) (visible-graph K x' y')
                                 (λ k → absurd (¬bp k)))
                         (≈-sym (when-O (x' ∈ᵥ? C* ⊎-dec y' ∈ᵥ? C*) (G x' y')
                                        (λ k → absurd (¬cg k)))))
                ≈-refl))

    base-swap : ∀ x' y' →
                foldr _+ₘ_ (B x' y') (sums-at x' y') ≈
                foldr _+ₘ_ (restrict G C* x' y') (sums-at x' y')
    base-swap x' y' =
      ≈-trans (foldr-base (B x' y') (sums-at x' y'))
      (≈-trans (base-agree x' y')
               (≈-sym (foldr-base (restrict G C* x' y') (sums-at x' y'))))

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

    core : ∀ x' y' →
           foldr _+G_ B (map proj₂ (proj₁ tp)) x' y' ≈
           hide-all (vertex-object 𝒢) (restrict G C*) (map at (concat Ms)) x' y'
    core x' y' =
      ≈-trans (≡-to-≈ (foldr-apply B (map proj₂ (proj₁ tp)) x' y'))
      (≈-trans (maps-≈ x' y')
      (≈-trans (base-swap x' y')
               (≈-sym (assemble {E = C*} Ms monosC* sepsMs x' y'))))

  FO-distinct : AllPairs _≢_ (FO 𝒢)
  FO-distinct = AllPairsP.filter⁺ (λ q → T? (Graph.fo 𝒢 q)) (distinct (Graph.shape 𝒢))

  private
    partition-distinct : (K : Config 𝒢) → (K .visible ++ hidden-set K) ↭ FO 𝒢 →
                         AllPairs _≢_ (K .visible ++ hidden-set K)
    partition-distinct K part =
      AllPairs-perm (λ h e → h (≡-sym e)) (↭-sym part) FO-distinct

    concat-distinct : (Css : List (List (Path))) → AllPairs _≢_ (concat Css) → AllPairs Distinct Css
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

    visible-not-hidden : (K : Config 𝒢) → Summarised K → ∀ {p} → p ∈ K .visible → p ∉ hidden-set K
    visible-not-hidden K S {p} pv k =
      All-lookup (All-lookup (proj₂ (proj₂ (visible-hidden-split K S)))
                             pv)
                 k ≡-refl

  summarised-distinct : (K : Config 𝒢) → Summarised K → AllPairs Distinct (map proj₁ (K .hidden))
  summarised-distinct K S =
    concat-distinct (map proj₁ (K .hidden))
      (proj₁ (proj₂ (visible-hidden-split K S)))

  hide-at-partition : (p : Path) (K : Config 𝒢) → Summarised K →
                      p ∈ K .visible →
                      (hide-at p K .visible ++ hidden-set (hide-at p K)) ↭ FO 𝒢
  hide-at-partition p K S pv =
    ↭-trans (++⁺ ↭-refl (hide-at-hidden-set p K))
    (↭-trans (shift p (hide-at p K .visible) (hidden-set K))
    (↭-trans (++⁺ (filter-out-↭ (_≟_ {shape})
                    (proj₁ (visible-hidden-split K S))
                    pv)
                  ↭-refl)
             (S .partition)))

  hide-at-summaries : (p : Path) (K : Config 𝒢) (S : Summarised K) →
                      p ∈ K .visible →
                      All (λ CH → ∀ x y → Prf (proj₂ CH x y ≈ summary (proj₁ CH) x y))
                          (hide-at p K .hidden)
  hide-at-summaries p K S pv =
    (λ x y → ⟪ merged-summary p K S (visible-not-hidden K S {p = p} pv) (summarised-distinct K S) x y ⟫) ∷
    proj₂ (partition-All (adj-p? p) (S .summaries))

  Apart-mono : {G : Relation (vertex-object 𝒢)} {C₁ C₂ C₁' C₂' : List (Path)} →
               C₁ ⊆ C₁' → C₂ ⊆ C₂' → Apart G C₁' C₂' → Apart G C₁ C₂
  Apart-mono m₁ m₂ ap = All-tabulate (λ h → All-tabulate (λ h' → All-lookup (All-lookup ap (m₁ h)) (m₂ h')))

  private
    split-none : (p : Path)
                 {CHs : List (List (Path) × Relation (vertex-object 𝒢))} →
                 All (λ CH → p ∉ proj₁ CH) CHs →
                 concat (map (split-region p) CHs) ≡ CHs
    split-none p []                     = ≡-refl
    split-none p (_∷_ {C , H} h hs) rewrite split-region-∉ p C H h =
      ≡-cong ((C , H) ∷_) (split-none p hs)

  reveal-set : (p : Path)
               (CHs : List (List (Path) × Relation (vertex-object 𝒢))) →
               AllPairs _≢_ (concat (map proj₁ CHs)) →
               Any (λ CH → p ∈ proj₁ CH) CHs →
               (p ∷ concat (map proj₁ (concat (map (split-region p) CHs))))
               ↭ concat (map proj₁ CHs)
  reveal-set p ((C , H) ∷ CHs) ps h with AllPairs-++⁻ C (concat (map proj₁ CHs)) ps
  ... | (aC , aRest , cross) with p ∈? C
  ...   | no ¬m =
    ↭-trans (↭-sym (shift p C (concat (map proj₁ (concat (map (split-region p) CHs))))))
            (++⁺ ↭-refl (reveal-set p CHs aRest (tail ¬m h)))
  ...   | yes m =
    ↭-trans (↭-reflexive (≡-cong (λ z → p ∷ concat z) (map-++ proj₁ Xs Zs)))
    (↭-trans (↭-reflexive (≡-cong (p ∷_) (≡-sym (concat-++ (map proj₁ Xs) (map proj₁ Zs)))))
    (↭-trans (↭-reflexive (≡-cong₂ (λ u v → p ∷ (concat u ++ concat (map proj₁ v)))
                                   (map-proj₁-pair summary Regs)
                                   (split-none p no-p-tail)))
             (++⁺ head-perm ↭-refl)))
    where
    C∖p  = filter (p ≢?_) C
    Regs = regions (fo-graph 𝒢) C∖p
    Xs   = map (λ C' → C' , summary C') Regs
    Zs   = concat (map (split-region p) CHs)

    no-p-tail : All (λ CH → p ∉ proj₁ CH) CHs
    no-p-tail =
      All-tabulate (λ mCH k →
        All-lookup (All-lookup cross m) (∈-concat⁺′ k (∈-map⁺ proj₁ mCH)) ≡-refl)

    head-perm : (p ∷ concat Regs) ↭ C
    head-perm = ↭-trans (↭.prep p (regions-concat (fo-graph 𝒢) C∖p)) (filter-out-↭ (_≟_ {shape}) aC m)

  private
    split-summaries : (p : Path)
                      (CH : List (Path) × Relation (vertex-object 𝒢)) →
                      (∀ x y → Prf (proj₂ CH x y ≈ summary (proj₁ CH) x y)) →
                      All (λ CH' → ∀ x y → Prf (proj₂ CH' x y ≈ summary (proj₁ CH') x y))
                          (split-region p CH)
    split-summaries p (C , H) old with p ∈? C
    ... | no  _ = old ∷ []
    ... | yes _ =
      AllP.map⁺ (universal (λ C' x y → ⟪ ≈-refl ⟫)
                           (regions (fo-graph 𝒢) (filter (p ≢?_) C)))

  reveal-at-partition : (p : Path) (K : Config 𝒢) → Summarised K →
                        p ∈ hidden-set K →
                        (reveal-at p K .visible ++ hidden-set (reveal-at p K)) ↭ FO 𝒢
  reveal-at-partition p K S hp =
    ↭-trans (↭-sym (shift p (K .visible) (hidden-set (reveal-at p K))))
    (↭-trans (++⁺ ↭-refl
                (reveal-set p (K .hidden)
                   (proj₁ (proj₂ (visible-hidden-split K S)))
                   (hidden-∈ K hp)))
             (S .partition))

  reveal-at-summaries : (p : Path) (K : Config 𝒢) (S : Summarised K) →
                        p ∈ hidden-set K →
                        All (λ CH → ∀ x y → Prf (proj₂ CH x y ≈ summary (proj₁ CH) x y))
                            (reveal-at p K .hidden)
  reveal-at-summaries p K S hp =
    AllP.concat⁺ (AllP.map⁺ (All-map (λ {CH} old → split-summaries p CH old) (S .summaries)))

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
                          (AllPairs-zip (separated S) (summarised-distinct K S))

      restrict-O : restrict G (hidden-set K) x y ≈ εₘ
      restrict-O = when-O (x ∈ᵥ? hidden-set K ⊎-dec y ∈ᵥ? hidden-set K) (G x y)
                          (⊎-caseₚ (λ h → absurd (hx h)) (λ h → absurd (hy h)))

      Σ-eq : foldr _+ₘ_ εₘ (map (λ CH → proj₂ CH x y) (K .hidden)) ≈ summary (hidden-set K) x y
      Σ-eq =
        ≈-trans (foldr-map-≈ εₘ (λ CH → proj₂ CH x y) (λ CH → summary (proj₁ CH) x y) (K .hidden)
                  (All-map (λ inv → inv x y) (S .summaries)))
        (≈-trans (≡-to-≈ (≡-cong (foldr _+ₘ_ εₘ) (map-∘ {g = λ C → summary C x y} {f = proj₁} (K .hidden))))
        (≈-sym (≈-trans (assemble {E = hidden-set K} Cs (blocks-⊆ Cs) seps x y)
               (≈-trans (foldr-base (restrict G (hidden-set K) x y) (map (λ C → summary C x y) Cs))
               (≈-trans (+ₘ-cong restrict-O ≈-refl)
                        (+ₘ-lunit (foldr _+ₘ_ εₘ (map (λ C → summary C x y) Cs))))))))

  hide-reveal-visible : (p : Path) (K : Config 𝒢) → Summarised K →
                        p ∈ K .visible →
                        reveal-at p (hide-at p K) .visible ↭ K .visible
  hide-reveal-visible p K S pv =
    filter-out-↭ (_≟_ {shape})
                 (proj₁ (visible-hidden-split K S))
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
      All-lookup (All-lookup (proj₂ (proj₂ (visible-hidden-split K S)))
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
               (proj₁ (proj₂ (visible-hidden-split K S)))
               (hidden-∈ K hp))

  private
    restrict-≤ : (G : Relation (vertex-object 𝒢)) (C : List (Path)) →
                 ∀ x y → (restrict G C x y +ₘ G x y) ≈ G x y
    restrict-≤ G C x y with x ∈ᵥ? C ⊎-dec y ∈ᵥ? C
    ... | yes _ = +ₘ-idem (G x y)
    ... | no  _ = +ₘ-lunit (G x y)

    restrict-hidden-agree : (G : Relation (vertex-object 𝒢)) (C : List (Path)) →
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

  hide-reveal : (p : Path) (K : Config 𝒢) → Summarised K → p ∈ K .visible → reveal-at p (hide-at p K) ≈K K
  hide-reveal p K S pv .visible-≈ = hide-reveal-visible p K S pv
  hide-reveal p K S pv .hidden-≈  = hide-reveal-hidden-set p K S pv

  reveal-hide : (p : Path) (K : Config 𝒢) → Summarised K → p ∈ hidden-set K → hide-at p (reveal-at p K) ≈K K
  reveal-hide p K S hp .visible-≈ = ↭-reflexive (reveal-hide-visible p K S hp)
  reveal-hide p K S hp .hidden-≈  = reveal-hide-hidden-set p K S hp

  merge-region-resp : (G : Relation (vertex-object 𝒢)) (w : Vertex shape) {rss rss' : List (List (Vertex shape))} →
                      rss ↭↭ rss' → merge-region G w rss ↭↭ merge-region G w rss'
  merge-region-resp G w {rss} {rss'} p =
    H.prep (↭.prep w (concat-resp (proj₁ tp-p))) (proj₂ tp-p)
    where
    tp-p = partition-permᴿ (adjacent-in? G w) Any-resp-↭ (λ pc → Any-resp-↭ (↭-sym pc)) p

  private
    merge-region-filter : (G : Relation (vertex-object 𝒢)) (w : Vertex shape) (rss : List (List (Vertex shape))) →
                          merge-region G w rss ≡
                          ((w ∷ concat (filter (adjacent-in? G w) rss)) ∷
                           filter (∁? (adjacent-in? G w)) rss)
    merge-region-filter G w rss =
      ≡-cong (λ u → (w ∷ concat (proj₁ u)) ∷ proj₂ u) (partition-defn (adjacent-in? G w) rss)

    cross : (G : Relation (vertex-object 𝒢)) (u u' : Vertex shape) (rss : List (List (Vertex shape))) →
            AdjacentIn G u (u' ∷ concat (filter (adjacent-in? G u') rss)) →
            AdjacentIn G u' (u ∷ concat (filter (adjacent-in? G u) rss))
    cross G u u' rss (here a)  = here (adjacent-sym G a)
    cross G u u' rss (there m) =
      there (AnyPr.concat⁺ (Any-filter⁺ (adjacent-in? G u)
               (Any-filter⁻ (adjacent-in? G u') rss (AnyPr.concat⁻ (filter (adjacent-in? G u') rss) m))))

  merge-region-comm : (G : Relation (vertex-object 𝒢)) (w w' : Vertex shape) (rss : List (List (Vertex shape))) →
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

  regions-perm : (G : Relation (vertex-object 𝒢)) {ws ws' : List (Vertex shape)} → ws ↭ ws' →
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
  initial-summarised .summaries = AllP.map⁺ (universal (λ C x y → ⟪ ≈-refl ⟫) (regions (fo-graph 𝒢) (FO 𝒢)))

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
      ≡-cong₂ (λ u v → (p ∷ concat u) ∷ v)
              (map-partition₁ proj₁ (adjacent-in? (fo-graph 𝒢) p) (K .hidden))
              (map-partition₂ proj₁ (adjacent-in? (fo-graph 𝒢) p) (K .hidden))
  hide-at-summarised p K S pv .summaries = hide-at-summaries p K S pv

  private
    regions-⊆ : (G : Relation (vertex-object 𝒢)) (ws : List (Vertex shape)) → All (_⊆ ws) (regions G ws)
    regions-⊆ G ws = All-map (λ inc {_} h → ∈-resp-↭ (regions-concat G ws) (inc h)) (blocks-⊆ (regions G ws))

    merge-region-inert : (G : Relation (vertex-object 𝒢)) (w : Vertex shape) (X' Y' : List (List (Vertex shape))) →
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

  regions-apart : (G : Relation (vertex-object 𝒢)) (B' rest : List (Vertex shape)) → Apart G B' rest →
                  regions G (B' ++ rest) ↭↭ (regions G B' ++ regions G rest)
  regions-apart G []       rest ap = ↭↭-refl
  regions-apart G (b ∷ B') rest (hb ∷ hB) =
    H.trans (merge-region-resp G b (regions-apart G B' rest hB))
            (↭↭-of-≡ (merge-region-inert G b (regions G B') (regions G rest)
              (All-map (λ {C} inc →
                 AllP.All¬⇒¬Any (All-tabulate (λ h → All-lookup hb (inc h))))
                (regions-⊆ G rest))))

  private
    apart-concat : {G : Relation (vertex-object 𝒢)} {C : List (Vertex shape)} {Cs : List (List (Vertex shape))} →
                   All (Apart G C) Cs → Apart G C (concat Cs)
    apart-concat aps = All-tabulate (λ m → AllP.concat⁺ (All-map (λ ap → All-lookup ap m) aps))

    regions-nonempty : (G : Relation (vertex-object 𝒢)) (ws : List (Vertex shape)) →
                       All (λ C → 1 ≤ length C) (regions G ws)
    regions-nonempty G []       = []
    regions-nonempty G (w ∷ ws) = s≤s z≤n ∷ proj₂ (partition-All (adjacent-in? G w) (regions-nonempty G ws))

  regions-apart-concat : {G : Relation (vertex-object 𝒢)} {Cs : List (List (Vertex shape))} →
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

    lens-eq : sum (map (λ C → length (regions G C)) Cs) ≡ length (map (λ C → length (regions G C)) Cs)
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
    distinct-hs = proj₁ (proj₂ (visible-hidden-split K S))

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
    blocks-part = concat-↭↭ (All-map (λ {CH} one → per-block CH one) (AllP.map⁻ (blocks-one-region K S)))
