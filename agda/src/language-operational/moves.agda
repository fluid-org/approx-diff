{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.Bool as Bool using (Bool; _∨_)
open import Data.Bool.ListAction using (any)
open import Data.Bool.Properties using (∨-comm; ∨-identityʳ)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map; concat; filterᵇ; foldr; partitionᵇ)
open import Data.List.Relation.Unary.All using (All; []; _∷_; universal) renaming (map to All-map)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there) renaming (map to Any-map)
import Data.List.Relation.Unary.Any.Properties as AnyPr
import Data.List.Relation.Unary.All.Properties as AllP
import Data.List.Relation.Unary.AllPairs.Properties as AllPairsP
open import Data.List.Properties using (++-identityʳ; concat-++; concat-map; foldl-++; map-++; map-∘)
import Data.List.Relation.Binary.Permutation.Propositional as ↭
open ↭ using (_↭_; ↭-refl; ↭-sym; ↭-trans; ↭-reflexive)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (map⁺; shift; ++⁺; drop-∷; Any-resp-↭)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; cong to ≡-cong; cong₂ to ≡-cong₂)
open import list
open import signature using (Signature)
open import primitives using (Primitives)
import hide-algebra
import matrix
import two

-- The moves preserve the invariant that the stored regions partition the hidden set into
-- pairwise-apart pieces, each carrying its summary. The initial configuration satisfies the
-- invariant, and the hide and reveal moves preserve it.
module language-operational.moves {ℓ} (Sig : Signature ℓ) (𝒫 : Primitives two.semiring Sig) where

open Signature Sig
open Primitives 𝒫
open import language-syntax Sig renaming (_,_ to _▸_) hiding (foldr)
open import language-operational.evaluation Sig 𝒫
open import language-operational.path Sig 𝒫
open import language-operational.graph Sig 𝒫
open import language-operational.hide Sig 𝒫
open import language-operational.topological-order Sig 𝒫

private
  module M = matrix.Mat two.semiring

  module HA {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) =
    hide-algebra.Hide (Vertex D) vertex-width

member-perm : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
              (q : Path D) {C C' : List (Path D)} → C ↭ C' → member q C ≡ member q C'
member-perm q = any-perm (eq-path q)

member-vertex-perm : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
                     (x : Vertex D) {C C' : List (Path D)} → C ↭ C' →
                     member-vertex x C ≡ member-vertex x C'
member-vertex-perm env    p = ≡-refl
member-vertex-perm (at q) p = member-perm q p

-- Restriction reads the region only through membership, so respects permutation.
restrict-perm : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
                (G : Graph D) {C C' : List (Path D)} → C ↭ C' →
                ∀ x y (i : Fin (vertex-width y)) (j : Fin (vertex-width x)) →
                restrict G C x y i j ≡ restrict G C' x y i j
restrict-perm G p x y i j =
  ≡-cong (λ b → when b (G x y) i j)
         (≡-cong₂ _∨_ (member-vertex-perm x p) (member-vertex-perm y p))

-- Restriction only zeroes entries, so preserves the forward-edge property.
restrict-forward : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
                   {G : Graph D} (C : List (Path D)) → Forward G → Forward (restrict G C)
restrict-forward C fwd x y i j with member-vertex x C ∨ member-vertex y C
... | Bool.true  = fwd x y i j
... | Bool.false = λ ()

-- Summaries are stable under permutation of the region: restriction is membership-based, and the
-- hiding order is immaterial on the restricted graph, which is forward.
summary-perm : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ])
               {C C' : List (Path D)} → C ↭ C' →
               ∀ x y (i : Fin (vertex-width y)) (j : Fin (vertex-width x)) →
               summary D C x y i j ≡ summary D C' x y i j
summary-perm D {C} {C'} p x y i j =
  ≡-trans (HA.fold-cong D (map at C) (restrict-perm (fo-graph D) p) x y i j)
          (hide-all-perm (restrict-forward C' (fo-forward D)) (map⁺ at p) x y i j)

adjacent-sym : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
               (G : Graph D) (x y : Vertex D) → adjacent G x y ≡ adjacent G y x
adjacent-sym G x y = ∨-comm (nonzero (G x y)) (nonzero (G y x))

-- Regions with no edge between them; each reads the graph only through its own members, so hiding
-- either leaves the other's summary alone.
Apart : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} →
        Graph D → List (Path D) → List (Path D) → Set
Apart G C C' = any (λ q → any (λ q' → adjacent G (at q) (at q')) C') C ≡ Bool.false

apart-sym : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
            (G : Graph D) {C C' : List (Path D)} → Apart G C C' → Apart G C' C
apart-sym G {C} {C'} h =
  ≡-trans (any-comm (λ q q' → adjacent G (at q) (at q')) C' C)
  (≡-trans (any-cong (λ q → any-cong (λ q' → adjacent-sym G (at q') (at q)) C') C) h)

-- Adding a vertex and merging the regions adjacent to it preserves pairwise apartness: an
-- untouched region fails the adjacency test for the vertex and was already apart from each of the
-- merged regions.
merge-separated : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
                  (G : Graph D) (w : Path D) {rs : List (List (Path D))} →
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

-- The regions computation produces pairwise-apart regions.
regions-separated : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
                    (G : Graph D) (ws : List (Path D)) → AllPairs (Apart G) (regions G ws)
regions-separated G []       = []
regions-separated G (w ∷ ws) = merge-separated G w (regions-separated G ws)

-- A correctly summarised configuration: the visible and hidden vertices partition the first-order
-- paths, the stored regions are pairwise apart, and each carries its summary.
record Summarised {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
                  (K : Config D) : Set ℓ where
  field
    partition : (K .visible ++ hidden-set K) ↭ FO D
    separated : AllPairs (Apart (fo-graph D)) (map proj₁ (K .hidden))
    summaries : All (λ CH → ∀ x y (i : Fin (vertex-width y)) (j : Fin (vertex-width x)) →
                            proj₂ CH x y i j ≡ summary D (proj₁ CH) x y i j)
                    (K .hidden)

open Summarised public

-- The regions of a list are made from exactly its members.
regions-concat : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
                 (G : Graph D) (ws : List (Path D)) → concat (regions G ws) ↭ ws
regions-concat G []       = ↭.refl
regions-concat G (w ∷ ws) =
  ↭.prep w (↭-trans (↭-reflexive (concat-++ (proj₁ tp) (proj₂ tp)))
           (↭-trans (concat-resp (↭↭-of-↭ (partition-↭ _ (regions G ws))))
                    (regions-concat G ws)))
  where tp = partitionᵇ (any (λ q → adjacent G (at w) (at q))) (regions G ws)

private
  stored≡ : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) →
            map proj₁ (initial D .hidden) ≡ regions (fo-graph D) (FO D)
  stored≡ D = map-proj₁-pair (summary D) (regions (fo-graph D) (FO D))

-- The initial configuration is correctly summarised.
initial-summarised : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) →
                     Summarised (initial D)
initial-summarised D .partition =
  subst (λ z → concat z ↭ FO D) (≡-sym (stored≡ D)) (regions-concat (fo-graph D) (FO D))
initial-summarised D .separated =
  subst (AllPairs (Apart (fo-graph D))) (≡-sym (stored≡ D))
        (regions-separated (fo-graph D) (FO D))
initial-summarised D .summaries =
  AllP.map⁺ (universal (λ C x y i j → ≡-refl) (regions (fo-graph D) (FO D)))

-- Hiding a vertex adds it to the hidden set.
hide-at-hidden-set : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ])
                     (p : Path D) (K : Config D) →
                     hidden-set (hide-at D p K) ↭ (p ∷ hidden-set K)
hide-at-hidden-set D p K =
  ↭.prep p
    (↭-trans (↭-reflexive (concat-++ (map proj₁ (proj₁ tp)) (map proj₁ (proj₂ tp))))
    (↭-trans (↭-reflexive (≡-cong concat (≡-sym (map-++ proj₁ (proj₁ tp) (proj₂ tp)))))
             (concat-resp (↭↭-of-↭ (map⁺ proj₁ (partition-↭ _ (K .hidden)))))))
  where tp = partitionᵇ (λ CH → any (λ q → adjacent (fo-graph D) (at p) (at q)) (proj₁ CH))
                        (K .hidden)

-- The merged region and the untouched regions remain pairwise apart.
hide-at-separated : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ])
                    (p : Path D) (K : Config D) → Summarised K →
                    AllPairs (Apart (fo-graph D)) (map proj₁ (hide-at D p K .hidden))
hide-at-separated D p K S =
  subst (AllPairs (Apart (fo-graph D)))
        (≡-cong₂ (λ z₁ z₂ → (p ∷ concat z₁) ∷ z₂)
                 (map-partition₁ proj₁ g (K .hidden))
                 (map-partition₂ proj₁ g (K .hidden)))
        (merge-separated (fo-graph D) p (S .separated))
  where g = any (λ q → adjacent (fo-graph D) (at p) (at q))

private
  mv-mono : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
            {C E : List (Path D)} →
            (∀ q → member q C ≡ Bool.true → member q E ≡ Bool.true) →
            ∀ z → member-vertex z C ≡ Bool.true → member-vertex z E ≡ Bool.true
  mv-mono mono env    ()
  mv-mono mono (at q) h = mono q h

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

restrict-sub : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
               (G : Graph D) {C E : List (Path D)} →
               (∀ q → member q C ≡ Bool.true → member q E ≡ Bool.true) →
               ∀ x y (i : Fin (vertex-width y)) (j : Fin (vertex-width x)) →
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

restrict-agree : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
                 (G : Graph D) {C E : List (Path D)} →
                 (∀ q → member q C ≡ Bool.true → member q E ≡ Bool.true) →
                 All (λ r → ((z : Vertex D) (i : Fin (vertex-width z)) (j : Fin (vertex-width r)) →
                             restrict G E r z i j ≡ restrict G C r z i j)
                          × ((z : Vertex D) (i : Fin (vertex-width r)) (j : Fin (vertex-width z)) →
                             restrict G E z r i j ≡ restrict G C z r i j))
                     (map at C)
restrict-agree G {C} {E} mono =
  AllP.map⁺ (All-map (λ {q} hq →
    (λ z i j →
      ≡-trans (≡-cong (λ b → when (b ∨ member-vertex z E) (G (at q) z) i j) (mono q hq))
              (≡-sym (≡-cong (λ b → when (b ∨ member-vertex z C) (G (at q) z) i j) hq))) ,
    (λ z i j →
      ≡-trans (≡-cong (λ b → when (member-vertex z E ∨ b) (G z (at q)) i j) (mono q hq))
      (≡-trans (≡-cong (λ b → when b (G z (at q)) i j) (∨-true (member-vertex z E)))
      (≡-sym (≡-trans (≡-cong (λ b → when (member-vertex z C ∨ b) (G z (at q)) i j) hq)
                      (≡-cong (λ b → when b (G z (at q)) i j) (∨-true (member-vertex z C))))))))
    (any-self eq-path-refl C))

localise : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ])
           {C E : List (Path D)} →
           (∀ q → member q C ≡ Bool.true → member q E ≡ Bool.true) →
           ∀ x y (i : Fin (vertex-width y)) (j : Fin (vertex-width x)) →
           hide-all (restrict (fo-graph D) E) (map at C) x y i j ≡
           (restrict (fo-graph D) E x y i j two.⊔ summary D C x y i j)
localise D {C} {E} mono x y i j =
  HA.agree-add D (map at C) (restrict-sub (fo-graph D) mono) (restrict-agree (fo-graph D) mono)
               x y i j

-- A region neither containing nor adjacent to a vertex has a summary with no entries at it.
summary-zero : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ])
               {C : List (Path D)} (q : Path D) →
               member q C ≡ Bool.false →
               any (λ q' → adjacent (fo-graph D) (at q) (at q')) C ≡ Bool.false →
               (((z : Vertex D) (i : Fin (vertex-width z)) (j : Fin (vertex-width (at q))) →
                 summary D C (at q) z i j ≡ two.O) ×
                ((z : Vertex D) (i : Fin (vertex-width (at q))) (j : Fin (vertex-width z)) →
                 summary D C z (at q) i j ≡ two.O))
summary-zero D {C} q hm hadj =
  HA.zero-fold D (map at C) (at q) (base-row , base-col)
  where
  adjs : All (λ q' → adjacent (fo-graph D) (at q) (at q') ≡ Bool.false) C
  adjs = any-false-All _ C hadj

  entry-row : ∀ z → member-vertex z C ≡ Bool.true →
              ∀ i j → fo-graph D (at q) z i j ≡ two.O
  entry-row env     ()
  entry-row (at q') hz i j =
    nonzero-O (fo-graph D (at q) (at q'))
              (proj₁ (∨-false (nonzero (fo-graph D (at q) (at q')))
                              (nonzero (fo-graph D (at q') (at q)))
                              (member-All {eq = eq-path} eq-path-≡ {x = q'} adjs hz))) i j

  entry-col : ∀ z → member-vertex z C ≡ Bool.true →
              ∀ i j → fo-graph D z (at q) i j ≡ two.O
  entry-col env     ()
  entry-col (at q') hz i j =
    nonzero-O (fo-graph D (at q') (at q))
              (proj₂ (∨-false (nonzero (fo-graph D (at q) (at q')))
                              (nonzero (fo-graph D (at q') (at q)))
                              (member-All {eq = eq-path} eq-path-≡ {x = q'} adjs hz))) i j

  base-row : (z : Vertex D) (i : Fin (vertex-width z)) (j : Fin (vertex-width (at q))) →
             restrict (fo-graph D) C (at q) z i j ≡ two.O
  base-row z i j =
    ≡-trans (≡-cong (λ b → when (b ∨ member-vertex z C) (fo-graph D (at q) z) i j) hm)
            (when-O (member-vertex z C) (fo-graph D (at q) z) i j (λ hz → entry-row z hz i j))

  base-col : (z : Vertex D) (i : Fin (vertex-width (at q))) (j : Fin (vertex-width z)) →
             restrict (fo-graph D) C z (at q) i j ≡ two.O
  base-col z i j =
    ≡-trans (≡-cong (λ b → when (member-vertex z C ∨ b) (fo-graph D z (at q)) i j) hm)
    (≡-trans (≡-cong (λ b → when b (fo-graph D z (at q)) i j) (∨-identityʳ (member-vertex z C)))
             (when-O (member-vertex z C) (fo-graph D z (at q)) i j (λ hz → entry-col z hz i j)))

-- Hiding pairwise-apart, pairwise-disjoint regions inside a common restriction adds exactly
-- their summaries: each region contributes its summary via localisation, and stays inert while
-- the remaining regions are hidden.
assemble : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ])
           {E : List (Path D)} (Cs : List (List (Path D))) →
           All (λ C → ∀ q → member q C ≡ Bool.true → member q E ≡ Bool.true) Cs →
           AllPairs (λ C C' → Apart (fo-graph D) C' C
                            × (any (λ q → member q C) C' ≡ Bool.false)) Cs →
           ∀ x y (i : Fin (vertex-width y)) (j : Fin (vertex-width x)) →
           hide-all (restrict (fo-graph D) E) (map at (concat Cs)) x y i j ≡
           foldr two._⊔_ (restrict (fo-graph D) E x y i j)
                         (map (λ C → summary D C x y i j) Cs)
assemble D []       []             []              x y i j = ≡-refl
assemble D {E} (C ∷ Cs) (mono ∷ monos) (shead ∷ stail) x y i j =
  ≡-trans (≡-cong (λ ws → hide-all R-E ws x y i j) (map-++ at C (concat Cs)))
  (≡-trans (≡-cong (λ H → H x y i j) (foldl-++ hide R-E (map at C) (map at (concat Cs))))
  (≡-trans (HA.fold-cong D (map at (concat Cs)) (localise D {C = C} mono) x y i j)
  (≡-trans (HA.add-inert D {G = R-E} {S = summary D C} (map at (concat Cs)) inert x y i j)
  (≡-trans (≡-cong (two._⊔ summary D C x y i j) (assemble D Cs monos stail x y i j))
           (two.⊔-comm _ (summary D C x y i j))))))
  where
  R-E = restrict (fo-graph D) E
  inert = AllP.map⁺ (AllP.concat⁺ (All-map
            (λ {C'} (ap , ds) →
              All-zip (λ {q} ha hm → summary-zero D {C = C} q hm ha)
                      (any-false-All _ C' ap) (any-false-All _ C' ds))
            shead))

private
  foldr-entry : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
                (B : Graph D) (Gs : List (Graph D)) →
                ∀ x y (i : Fin (vertex-width y)) (j : Fin (vertex-width x)) →
                foldr _+G_ B Gs x y i j ≡
                foldr two._⊔_ (B x y i j) (map (λ H → H x y i j) Gs)
  foldr-entry B []       x y i j = ≡-refl
  foldr-entry B (H ∷ Gs) x y i j = ≡-cong (H x y i j two.⊔_) (foldr-entry B Gs x y i j)

blocks-⊆ : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
           (Css : List (List (Path D))) →
           All (λ C → ∀ q → member q C ≡ Bool.true → member q (concat Css) ≡ Bool.true) Css
blocks-⊆ []         = []
blocks-⊆ (C ∷ Css) =
  (λ q h → ≡-trans (any-++ (eq-path q) C (concat Css)) (≡-cong (_∨ member q (concat Css)) h)) ∷
  All-map (λ {C'} g q h →
            ≡-trans (any-++ (eq-path q) C (concat Css))
            (≡-trans (≡-cong (member q C ∨_) (g q h)) (∨-true (member q C))))
          (blocks-⊆ Css)

summary-snoc : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ])
               (p : Path D) (C : List (Path D)) →
               ∀ x y (i : Fin (vertex-width y)) (j : Fin (vertex-width x)) →
               summary D (p ∷ C) x y i j ≡
               hide (hide-all (restrict (fo-graph D) (p ∷ C)) (map at C)) (at p) x y i j
summary-snoc D p C x y i j =
  ≡-trans (hide-all-perm (restrict-forward (p ∷ C) (fo-forward D)) perm x y i j)
          (≡-cong (λ H → H x y i j)
                  (foldl-++ hide (restrict (fo-graph D) (p ∷ C)) (map at C) (at p ∷ [])))
  where
  perm : (at p ∷ map at C) ↭ (map at C ++ (at p ∷ []))
  perm = ↭-sym (↭-trans (shift (at p) (map at C) [])
                        (↭-reflexive (≡-cong (at p ∷_) (++-identityʳ (map at C)))))

Distinct : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} →
           List (Path D) → List (Path D) → Set
Distinct C C' = (any (λ q → member q C) C' ≡ Bool.false) × (any (λ q → member q C') C ≡ Bool.false)

distinct-sym : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
               {C C' : List (Path D)} → Distinct C C' → Distinct C' C
distinct-sym (a , b) = (b , a)

private
  bool-case : ∀ {a} {A : Set a} (b : Bool) → (b ≡ Bool.true → A) → (b ≡ Bool.false → A) → A
  bool-case Bool.true  t f = t ≡-refl
  bool-case Bool.false t f = f ≡-refl

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

  block-of : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
             (q : Path D) (Css : List (List (Path D))) →
             member q (concat Css) ≡ Bool.true → Any (λ C → member q C ≡ Bool.true) Css
  block-of q Css h =
    any-Any (λ C → member q C) Css (≡-trans (≡-sym (any-concat (eq-path q) Css)) h)

private
  -- The base of the assembled graph agrees with the restriction of the first-order graph to the
  -- merged region, modulo the joined summaries of the merged regions: an entry at p is either a
  -- first-order edge whose other end is visible or in a merged region, or a stored summary entry;
  -- an end in an unmerged region is ruled out by non-adjacency.
  base-agree : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ])
           (p : Path D) (K : Config D) → Summarised K →
           member p (hidden-set K) ≡ Bool.false →
           let tp = partitionᵇ (λ CH → any (λ q → adjacent (fo-graph D) (at p) (at q)) (proj₁ CH))
                               (K .hidden) in
           ∀ x y (i : Fin (vertex-width y)) (j : Fin (vertex-width x)) →
           (restrict (visible-graph D K) (p ∷ []) x y i j two.⊔
             foldr two._⊔_ two.O (map (λ C → summary D C x y i j) (map proj₁ (proj₁ tp))))
           ≡ (restrict (fo-graph D) (p ∷ concat (map proj₁ (proj₁ tp))) x y i j two.⊔
             foldr two._⊔_ two.O (map (λ C → summary D C x y i j) (map proj₁ (proj₁ tp))))
  base-agree D p K S hp x' y' i' j' =
    two.I-antisym
      (λ h → [ fwd-B x' y' i' j' , two.⊔-I-inr _ ]′
               (two.⊔-I (B x' y' i' j') (foldr two._⊔_ two.O (sums-at x' y' i' j')) h))
      (λ h → [ bwd-B x' y' i' j' , two.⊔-I-inr _ ]′
               (two.⊔-I (restrict G C* x' y' i' j') (foldr two._⊔_ two.O (sums-at x' y' i' j')) h))
    where
    G  = fo-graph D
    adj-p : List (Path D) × Graph D → Bool
    adj-p CH = any (λ q → adjacent G (at p) (at q)) (proj₁ CH)
    tp = partitionᵇ adj-p (K .hidden)
    Mp = proj₁ tp
    Up = proj₂ tp
    Ms = map proj₁ Mp
    CM = concat Ms
    C* = p ∷ CM
    hs = hidden-set K
    Vis = visible-graph D K
    B = restrict Vis (p ∷ [])

    u-adj : All (λ CH → adj-p CH ≡ Bool.false) Up
    u-adj = part₂-false adj-p (K .hidden)

    u-szero : All (λ CH →
                (((z : Vertex D) (i' : Fin (vertex-width z)) (j' : Fin (vertex-width (at p))) →
                  summary D (proj₁ CH) (at p) z i' j' ≡ two.O)
               × ((z : Vertex D) (i' : Fin (vertex-width (at p))) (j' : Fin (vertex-width z)) →
                  summary D (proj₁ CH) z (at p) i' j' ≡ two.O))) Up
    u-szero = All-zip (λ {CH} hadj hm → summary-zero D {C = proj₁ CH} p hm hadj) u-adj
                (proj₂ (partition-All adj-p (any-false-All _ (K .hidden)
                  (≡-trans (≡-sym (any-map (λ C → member p C) proj₁ (K .hidden)))
                           (≡-trans (≡-sym (any-concat (eq-path p) (map proj₁ (K .hidden)))) hp)))))

    edge-O : ∀ {C : List (Path D)} → any (λ q → adjacent G (at p) (at q)) C ≡ Bool.false →
             ∀ q' → member q' C ≡ Bool.true →
             ((∀ i' j' → G (at p) (at q') i' j' ≡ two.O) ×
              (∀ i' j' → G (at q') (at p) i' j' ≡ two.O))
    edge-O {C} hadj q' hq =
      (λ i' j' → nonzero-O (G (at p) (at q')) (proj₁ spl) i' j') ,
      (λ i' j' → nonzero-O (G (at q') (at p)) (proj₂ spl) i' j')
      where
      spl = ∨-false (nonzero (G (at p) (at q'))) (nonzero (G (at q') (at p)))
                    (member-All {eq = eq-path} eq-path-≡ {x = q'} (any-false-All _ C hadj) hq)

    hid-split : ∀ q → member q hs ≡ Bool.true →
                Any (λ CH → member q (proj₁ CH) ≡ Bool.true) Mp
                ⊎ Any (λ CH → member q (proj₁ CH) ≡ Bool.true) Up
    hid-split q h
      with ∨-true-inv (any (λ CH → member q (proj₁ CH)) Mp)
                      (any (λ CH → member q (proj₁ CH)) Up)
                      (≡-trans (≡-sym (any-++ (λ CH → member q (proj₁ CH)) Mp Up))
                       (≡-trans (any-perm (λ CH → member q (proj₁ CH))
                                          (partition-↭ adj-p (K .hidden)))
                        (≡-trans (≡-sym (any-map (λ C → member q C) proj₁ (K .hidden)))
                                 (≡-trans (≡-sym (any-concat (eq-path q) (map proj₁ (K .hidden)))) h))))
    ... | inj₁ e = inj₁ (any-Any _ Mp e)
    ... | inj₂ e = inj₂ (any-Any _ Up e)

    summary-I : ∀ (C : List (Path D)) x' y' (i' : Fin (vertex-width y')) (j' : Fin (vertex-width x')) →
           (member-vertex x' C ∨ member-vertex y' C) ≡ Bool.true →
           G x' y' i' j' ≡ two.I → summary D C x' y' i' j' ≡ two.I
    summary-I C x' y' i' j' gd ge =
      ≡-trans (HA.increasing D (map at C) x' y' i' j')
              (≡-cong (two._⊔ hide-all (restrict G C) (map at C) x' y' i' j')
                      (≡-trans (≡-cong (λ b → when b (G x' y') i' j') gd) ge))

    sums-I : ∀ x' y' (i' : Fin (vertex-width y')) (j' : Fin (vertex-width x')) (b : two.Two) →
          Any (λ C → summary D C x' y' i' j' ≡ two.I) Ms →
          foldr two._⊔_ b (map (λ C → summary D C x' y' i' j') Ms) ≡ two.I
    sums-I x' y' i' j' b a = two.foldr-⊔-at b (AnyPr.map⁺ a)

    mv-p-≡ : ∀ z → member-vertex z (p ∷ []) ≡ Bool.true → z ≡ at p
    mv-p-≡ env ()
    mv-p-≡ (at q) h with ∨-true-inv (eq-path q p) Bool.false h
    ... | inj₁ e = ≡-cong at (eq-path-≡ e)
    ... | inj₂ ()

    pguard-≡ : ∀ x' y' → (member-vertex x' (p ∷ []) ∨ member-vertex y' (p ∷ [])) ≡ Bool.true →
               (x' ≡ at p) ⊎ (y' ≡ at p)
    pguard-≡ x' y' h with ∨-true-inv (member-vertex x' (p ∷ [])) (member-vertex y' (p ∷ [])) h
    ... | inj₁ e = inj₁ (mv-p-≡ x' e)
    ... | inj₂ e = inj₂ (mv-p-≡ y' e)

    p∈C* : member p C* ≡ Bool.true
    p∈C* = or-introl (eq-path p p) (member p CM) (eq-path-refl p)

    vis-or : ∀ x' y' (i' : Fin (vertex-width y')) (j' : Fin (vertex-width x')) →
             (x' ≡ at p) ⊎ (y' ≡ at p) → G x' y' i' j' ≡ two.I →
             restrict G C* x' y' i' j' ≡ two.I
    vis-or .(at p) y' i' j' (inj₁ ≡-refl) ge =
      ≡-trans (≡-cong (λ b → when b (G (at p) y') i' j')
                      (or-introl (member p C*) (member-vertex y' C*) p∈C*)) ge
    vis-or x' .(at p) i' j' (inj₂ ≡-refl) ge =
      ≡-trans (≡-cong (λ b → when b (G x' (at p)) i' j')
                      (or-intror (member-vertex x' C*) (member p C*) p∈C*)) ge

    vis-entry : ∀ x' y' (i' : Fin (vertex-width y')) (j' : Fin (vertex-width x')) →
                Vis x' y' i' j' ≡
                foldr two._⊔_
                      (when (Bool.not (member-vertex x' hs) Bool.∧ Bool.not (member-vertex y' hs))
                            (G x' y') i' j')
                      (map (λ CH → proj₂ CH x' y' i' j') (K .hidden))
    vis-entry x' y' i' j' =
      ≡-trans (foldr-entryₘ _ (map (λ CH → proj₂ CH x' y') (K .hidden)) i' j')
              (≡-cong (foldr two._⊔_ _)
                      (≡-sym (map-∘ {g = λ R' → R' i' j'} {f = λ CH → proj₂ CH x' y'} (K .hidden))))

    sums-at : ∀ x' y' (i' : Fin (vertex-width y')) (j' : Fin (vertex-width x')) → List two.Two
    sums-at x' y' i' j' = map (λ C → summary D C x' y' i' j') Ms

    stored-or : ∀ x' y' (i' : Fin (vertex-width y')) (j' : Fin (vertex-width x')) →
                (x' ≡ at p) ⊎ (y' ≡ at p) →
                (Any (λ CH → summary D (proj₁ CH) x' y' i' j' ≡ two.I) Mp
                 ⊎ Any (λ CH → summary D (proj₁ CH) x' y' i' j' ≡ two.I) Up) →
                (restrict G C* x' y' i' j' two.⊔ foldr two._⊔_ two.O (sums-at x' y' i' j')) ≡ two.I
    stored-or x'      y' i' j' _             (inj₁ aM) =
      two.⊔-I-inr _ (sums-I x' y' i' j' two.O (AnyPr.map⁺ aM))
    stored-or .(at p) y' i' j' (inj₁ ≡-refl) (inj₂ aU) =
      Any-contra (λ { (sI , (zr , _)) → two.O≢I (≡-trans (≡-sym (zr y' i' j')) sI) })
                 (Any-All aU u-szero)
    stored-or x' .(at p) i' j' (inj₂ ≡-refl) (inj₂ aU) =
      Any-contra (λ { (sI , (_ , zc)) → two.O≢I (≡-trans (≡-sym (zc x' i' j')) sI) })
                 (Any-All aU u-szero)

    fwd-B : ∀ x' y' (i' : Fin (vertex-width y')) (j' : Fin (vertex-width x')) →
            B x' y' i' j' ≡ two.I →
            (restrict G C* x' y' i' j' two.⊔ foldr two._⊔_ two.O (sums-at x' y' i' j')) ≡ two.I
    fwd-B x' y' i' j' h with when-I (member-vertex x' (p ∷ []) ∨ member-vertex y' (p ∷ []))
                                    (Vis x' y') i' j' h
    ... | (pgt , ve)
      with two.foldr-⊔-I (when (Bool.not (member-vertex x' hs) Bool.∧ Bool.not (member-vertex y' hs))
                           (G x' y') i' j')
                     (map (λ CH → proj₂ CH x' y' i' j') (K .hidden))
                     (≡-trans (≡-sym (vis-entry x' y' i' j')) ve)
    ...   | inj₁ vb =
      two.⊔-I-inl (vis-or x' y' i' j' (pguard-≡ x' y' pgt)
                          (proj₂ (when-I (Bool.not (member-vertex x' hs) Bool.∧ Bool.not (member-vertex y' hs))
                                     (G x' y') i' j' vb)))
    ...   | inj₂ aS =
      stored-or x' y' i' j' (pguard-≡ x' y' pgt)
        (AnyPr.++⁻ Mp (Any-resp-↭ (↭-sym (partition-↭ adj-p (K .hidden)))
          (Any-map (λ (eI , inv) → ≡-trans (≡-sym (inv x' y' i' j')) eI)
                   (Any-All (AnyPr.map⁻ aS) (S .summaries)))))

    B-visible-x : ∀ y' (i' : Fin (vertex-width y')) (j' : Fin (vertex-width (at p))) →
                   member-vertex y' hs ≡ Bool.false → G (at p) y' i' j' ≡ two.I →
                   B (at p) y' i' j' ≡ two.I
    B-visible-x y' i' j' hy ge =
      ≡-trans (≡-cong (λ b → when b (Vis (at p) y') i' j')
                      (or-introl (member p (p ∷ [])) (member-vertex y' (p ∷ []))
                                 (≡-cong (_∨ Bool.false) (eq-path-refl p))))
      (≡-trans (vis-entry (at p) y' i' j')
               (two.foldr-⊔-here (map (λ CH → proj₂ CH (at p) y' i' j') (K .hidden))
                 (≡-trans (≡-cong (λ b → when b (G (at p) y') i' j')
                                  (∧-intro (not-false hp) (not-false hy)))
                          ge)))

    B-visible-y : ∀ x' (i' : Fin (vertex-width (at p))) (j' : Fin (vertex-width x')) →
                   member-vertex x' hs ≡ Bool.false → G x' (at p) i' j' ≡ two.I →
                   B x' (at p) i' j' ≡ two.I
    B-visible-y x' i' j' hx ge =
      ≡-trans (≡-cong (λ b → when b (Vis x' (at p)) i' j')
                      (or-intror (member-vertex x' (p ∷ [])) (member p (p ∷ []))
                                 (≡-cong (_∨ Bool.false) (eq-path-refl p))))
      (≡-trans (vis-entry x' (at p) i' j')
               (two.foldr-⊔-here (map (λ CH → proj₂ CH x' (at p) i' j') (K .hidden))
                 (≡-trans (≡-cong (λ b → when b (G x' (at p)) i' j')
                                  (∧-intro (not-false hx) (not-false hp)))
                          ge)))

    bwd-px : ∀ y' (i' : Fin (vertex-width y')) (j' : Fin (vertex-width (at p))) →
             G (at p) y' i' j' ≡ two.I →
             (B (at p) y' i' j' two.⊔ foldr two._⊔_ two.O (sums-at (at p) y' i' j')) ≡ two.I
    bwd-px env i' j' ge = two.⊔-I-inl (B-visible-x env i' j' ≡-refl ge)
    bwd-px (at qy) i' j' ge =
      bool-case (member qy hs)
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

    bwd-py : ∀ x' (i' : Fin (vertex-width (at p))) (j' : Fin (vertex-width x')) →
             G x' (at p) i' j' ≡ two.I →
             (B x' (at p) i' j' two.⊔ foldr two._⊔_ two.O (sums-at x' (at p) i' j')) ≡ two.I
    bwd-py env i' j' ge = two.⊔-I-inl (B-visible-y env i' j' ≡-refl ge)
    bwd-py (at qx) i' j' ge =
      bool-case (member qx hs)
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

    bwd-l : ∀ x' y' (i' : Fin (vertex-width y')) (j' : Fin (vertex-width x')) →
            G x' y' i' j' ≡ two.I → member-vertex x' C* ≡ Bool.true →
            (B x' y' i' j' two.⊔ foldr two._⊔_ two.O (sums-at x' y' i' j')) ≡ two.I
    bwd-l env     y' i' j' ge ()
    bwd-l (at qx) y' i' j' ge hx with ∨-true-inv (eq-path qx p) (member qx CM) hx
    ... | inj₂ m =
      two.⊔-I-inr _
        (sums-I (at qx) y' i' j' two.O
             (Any-map (λ {C} mem →
                         summary-I C (at qx) y' i' j' (or-introl (member qx C) (member-vertex y' C) mem) ge)
                      (block-of qx Ms m)))
    ... | inj₁ ep with eq-path-≡ {p = qx} {q = p} ep
    ...   | ≡-refl = bwd-px y' i' j' ge

    bwd-r : ∀ x' y' (i' : Fin (vertex-width y')) (j' : Fin (vertex-width x')) →
            G x' y' i' j' ≡ two.I → member-vertex y' C* ≡ Bool.true →
            (B x' y' i' j' two.⊔ foldr two._⊔_ two.O (sums-at x' y' i' j')) ≡ two.I
    bwd-r x' env     i' j' ge ()
    bwd-r x' (at qy) i' j' ge hy with ∨-true-inv (eq-path qy p) (member qy CM) hy
    ... | inj₂ m =
      two.⊔-I-inr _
        (sums-I x' (at qy) i' j' two.O
             (Any-map (λ {C} mem →
                         summary-I C x' (at qy) i' j' (or-intror (member-vertex x' C) (member qy C) mem) ge)
                      (block-of qy Ms m)))
    ... | inj₁ ep with eq-path-≡ {p = qy} {q = p} ep
    ...   | ≡-refl = bwd-py x' i' j' ge

    bwd-B : ∀ x' y' (i' : Fin (vertex-width y')) (j' : Fin (vertex-width x')) →
            restrict G C* x' y' i' j' ≡ two.I →
            (B x' y' i' j' two.⊔ foldr two._⊔_ two.O (sums-at x' y' i' j')) ≡ two.I
    bwd-B x' y' i' j' h with when-I (member-vertex x' C* ∨ member-vertex y' C*) (G x' y') i' j' h
    ... | (gd , ge) with ∨-true-inv (member-vertex x' C*) (member-vertex y' C*) gd
    ...   | inj₁ hx = bwd-l x' y' i' j' ge hx
    ...   | inj₂ hy = bwd-r x' y' i' j' ge hy

-- The graph assembled by the hide move, hidden at p, is the summary of the merged region.
merged-summary : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ])
                 (p : Path D) (K : Config D) → Summarised K →
                 member p (hidden-set K) ≡ Bool.false →
                 AllPairs Distinct (map proj₁ (K .hidden)) →
                 let tp = partitionᵇ (λ CH → any (λ q → adjacent (fo-graph D) (at p) (at q)) (proj₁ CH))
                                     (K .hidden) in
                 ∀ x y (i : Fin (vertex-width y)) (j : Fin (vertex-width x)) →
                 hide (foldr _+G_ (restrict (visible-graph D K) (p ∷ []))
                                  (map proj₂ (proj₁ tp)))
                      (at p) x y i j
                 ≡ summary D (p ∷ concat (map proj₁ (proj₁ tp))) x y i j
merged-summary D p K S hp dist x y i j =
  ≡-trans (HA.h-cong D (at p) core x y i j) (≡-sym (summary-snoc D p CM x y i j))
  where
  G  = fo-graph D
  adj-p : List (Path D) × Graph D → Bool
  adj-p CH = any (λ q → adjacent G (at p) (at q)) (proj₁ CH)
  tp = partitionᵇ adj-p (K .hidden)
  Mp = proj₁ tp
  Ms = map proj₁ Mp
  CM = concat Ms
  C* = p ∷ CM
  B = restrict (visible-graph D K) (p ∷ [])

  sums-at : ∀ x' y' (i' : Fin (vertex-width y')) (j' : Fin (vertex-width x')) → List two.Two
  sums-at x' y' i' j' = map (λ C → summary D C x' y' i' j') Ms

  base-swap : ∀ x' y' (i' : Fin (vertex-width y')) (j' : Fin (vertex-width x')) →
              foldr two._⊔_ (B x' y' i' j') (sums-at x' y' i' j') ≡
              foldr two._⊔_ (restrict G C* x' y' i' j') (sums-at x' y' i' j')
  base-swap x' y' i' j' =
    ≡-trans (two.foldr-⊔-base (B x' y' i' j') (sums-at x' y' i' j'))
    (≡-trans (base-agree D p K S hp x' y' i' j')
             (≡-sym (two.foldr-⊔-base (restrict G C* x' y' i' j') (sums-at x' y' i' j'))))

  maps≡ : ∀ x' y' (i' : Fin (vertex-width y')) (j' : Fin (vertex-width x')) →
          map (λ H → H x' y' i' j') (map proj₂ Mp) ≡ sums-at x' y' i' j'
  maps≡ x' y' i' j' =
    ≡-trans (≡-sym (map-∘ {g = λ H → H x' y' i' j'} {f = proj₂} Mp))
    (≡-trans (map-All-cong (All-map (λ inv → inv x' y' i' j')
                                    (proj₁ (partition-All adj-p (S .summaries)))))
             (map-∘ {g = λ C → summary D C x' y' i' j'} {f = proj₁} Mp))

  monosC* : All (λ C → ∀ q → member q C ≡ Bool.true → member q C* ≡ Bool.true) Ms
  monosC* = All-map (λ g q h → or-intror (eq-path q p) (member q CM) (g q h)) (blocks-⊆ Ms)

  sepsMs : AllPairs (λ C C' → Apart G C' C × (any (λ q → member q C) C' ≡ Bool.false)) Ms
  sepsMs =
    AllPairs-map (λ {C} {C'} (ap , d) → (apart-sym G {C} {C'} ap , proj₁ d))
      (subst (AllPairs (λ C C' → Apart G C C' × Distinct C C'))
             (map-partition₁ proj₁ (λ C → any (λ q → adjacent G (at p) (at q)) C) (K .hidden))
             (proj₁ (partition-AllPairs {S = λ C C' → Apart G C C' × Distinct C C'}
                      (λ C → any (λ q → adjacent G (at p) (at q)) C)
                      (λ {C} {C'} (ap , d) → (apart-sym G {C} {C'} ap , distinct-sym {C = C} {C' = C'} d))
                      (AllPairs-zip (S .separated) dist))))

  core : ∀ x' y' (i' : Fin (vertex-width y')) (j' : Fin (vertex-width x')) →
         foldr _+G_ B (map proj₂ Mp) x' y' i' j' ≡
         hide-all (restrict G C*) (map at CM) x' y' i' j'
  core x' y' i' j' =
    ≡-trans (foldr-entry B (map proj₂ Mp) x' y' i' j')
    (≡-trans (≡-cong (foldr two._⊔_ (B x' y' i' j')) (maps≡ x' y' i' j'))
    (≡-trans (base-swap x' y' i' j')
             (≡-sym (assemble D {C*} Ms monosC* sepsMs x' y' i' j'))))

-- The first-order paths inherit distinctness from the path enumeration.
FO-distinct : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) →
              AllPairs (λ q q' → eq-path q q' ≡ Bool.false) (FO D)
FO-distinct D = filter-AllPairs (λ p → Bool.not (is-ε p) Bool.∧ fo-at p) (paths-distinct D)

private
  partition-distinct : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
                       (K : Config D) → Summarised K →
                       AllPairs (λ q q' → eq-path q q' ≡ Bool.false)
                                (K .visible ++ hidden-set K)
  partition-distinct {D = D} K S =
    AllPairs-perm (λ {q} {q'} h → eq-path-false-sym {p = q} {q = q'} h)
                  (↭-sym (S .partition)) (FO-distinct D)

  concat-distinct : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
                    (Css : List (List (Path D))) →
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

  visible-not-hidden : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
                       (K : Config D) → Summarised K → ∀ {p} →
                       member p (K .visible) ≡ Bool.true →
                       member p (hidden-set K) ≡ Bool.false
  visible-not-hidden K S {p} pv =
    any-false (member-All {eq = eq-path} eq-path-≡ {x = p}
                (proj₂ (proj₂ (AllPairs-++⁻ (K .visible) (hidden-set K)
                                            (partition-distinct K S))))
                pv)

-- A summarised configuration's stored regions are pairwise disjoint: the partition invariant
-- places them inside the duplicate-free first-order paths.
summarised-distinct : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
                      (K : Config D) → Summarised K →
                      AllPairs Distinct (map proj₁ (K .hidden))
summarised-distinct K S =
  concat-distinct (map proj₁ (K .hidden))
    (proj₁ (proj₂ (AllPairs-++⁻ (K .visible) (hidden-set K) (partition-distinct K S))))

-- Hiding a visible vertex preserves correct summarisation.
hide-at-summarised : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ])
                     (p : Path D) (K : Config D) → Summarised K →
                     member p (K .visible) ≡ Bool.true →
                     Summarised (hide-at D p K)
hide-at-summarised D p K S pv .partition =
  ↭-trans (++⁺ ↭-refl (hide-at-hidden-set D p K))
  (↭-trans (shift p (hide-at D p K .visible) (hidden-set K))
  (↭-trans (++⁺ (filter-out-↭ {eq = eq-path} (λ {q} {q'} e → eq-path-≡ {p = q} {q = q'} e)
                  (proj₁ (AllPairs-++⁻ (K .visible) (hidden-set K) (partition-distinct K S)))
                  pv)
                ↭-refl)
           (S .partition)))
hide-at-summarised D p K S pv .separated = hide-at-separated D p K S
hide-at-summarised D p K S pv .summaries =
  merged-summary D p K S (visible-not-hidden K S {p = p} pv) (summarised-distinct K S) ∷
  proj₂ (partition-All (λ CH → any (λ q → adjacent (fo-graph D) (at p) (at q)) (proj₁ CH))
                      (S .summaries))

private
  -- Apart in pointwise form, and its monotonicity under region inclusion.
  Apart-All : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
              {G : Graph D} {C C' : List (Path D)} → Apart G C C' →
              All (λ q → All (λ q' → adjacent G (at q) (at q') ≡ Bool.false) C') C
  Apart-All {C = C} {C'} ap = All-map (λ h → any-false-All _ C' h) (any-false-All _ C ap)

  Apart-mono : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
               {G : Graph D} {C₁ C₂ C₁' C₂' : List (Path D)} →
               (∀ q → member q C₁ ≡ Bool.true → member q C₁' ≡ Bool.true) →
               (∀ q → member q C₂ ≡ Bool.true → member q C₂' ≡ Bool.true) →
               Apart G C₁' C₂' → Apart G C₁ C₂
  Apart-mono {G = G} {C₁ = C₁} {C₂} {C₁'} {C₂'} m₁ m₂ ap =
    any-false (All-map
      (λ {q} mq → any-false (All-map
        (λ {q'} mq' →
          member-All {eq = eq-path} eq-path-≡ {x = q'}
            (member-All {eq = eq-path} eq-path-≡ {x = q}
               (Apart-All {G = G} {C = C₁'} {C' = C₂'} ap) (m₁ q mq))
            (m₂ q' mq'))
        (any-self eq-path-refl C₂)))
      (any-self eq-path-refl C₁))

  -- Each piece of a split region lies inside the region.
  split-⊆ : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) (p : Path D)
            (CH : List (Path D) × Graph D) →
            All (λ C₁ → ∀ q → member q C₁ ≡ Bool.true → member q (proj₁ CH) ≡ Bool.true)
                (map proj₁ (split-region D p CH))
  split-⊆ D p (C , H) with member p C
  ... | Bool.false = (λ q h → h) ∷ []
  ... | Bool.true  =
    subst (All (λ C₁ → ∀ q → member q C₁ ≡ Bool.true → member q C ≡ Bool.true))
          (≡-sym (map-proj₁-pair (summary D) (regions (fo-graph D) C∖p)))
          (All-map (λ {C₁} inc q h →
                      any-filterᵇ (eq-path q) (λ q' → Bool.not (eq-path p q')) C
                        (≡-trans (≡-sym (member-perm q (regions-concat (fo-graph D) C∖p)))
                                 (inc q h)))
                   (blocks-⊆ (regions (fo-graph D) C∖p)))
    where C∖p = filterᵇ (λ q → Bool.not (eq-path p q)) C

  -- Splitting leaves a region without p alone.
  split-none : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) (p : Path D)
               {CHs : List (List (Path D) × Graph D)} →
               All (λ CH → member p (proj₁ CH) ≡ Bool.false) CHs →
               concat (map (split-region D p) CHs) ≡ CHs
  split-none D p []                     = ≡-refl
  split-none D p (_∷_ {C , H} h hs) rewrite h = ≡-cong ((C , H) ∷_) (split-none D p hs)

  -- Splitting at a hidden vertex removes exactly p from the hidden set.
  reveal-set : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) (p : Path D)
               (CHs : List (List (Path D) × Graph D)) →
               AllPairs (λ q q' → eq-path q q' ≡ Bool.false) (concat (map proj₁ CHs)) →
               any (λ CH → member p (proj₁ CH)) CHs ≡ Bool.true →
               (p ∷ concat (map proj₁ (concat (map (split-region D p) CHs))))
               ↭ concat (map proj₁ CHs)
  reveal-set D p ((C , H) ∷ CHs) ps h
    with AllPairs-++⁻ C (concat (map proj₁ CHs)) ps
  ... | (aC , aRest , cross) with member p C in e
  ...   | Bool.false =
    ↭-trans (↭-sym (shift p C (concat (map proj₁ (concat (map (split-region D p) CHs))))))
            (++⁺ ↭-refl (reveal-set D p CHs aRest h))
  ...   | Bool.true  =
    ↭-trans (↭-reflexive (≡-cong (λ z → p ∷ concat z) (map-++ proj₁ X Z)))
    (↭-trans (↭-reflexive (≡-cong (p ∷_) (≡-sym (concat-++ (map proj₁ X) (map proj₁ Z)))))
    (↭-trans (↭-reflexive (≡-cong₂ (λ u v → p ∷ (concat u ++ concat (map proj₁ v)))
                                   (map-proj₁-pair (summary D) Regs)
                                   (split-none D p no-p-tail)))
             (++⁺ head-perm ↭-refl)))
    where
    C∖p  = filterᵇ (λ q → Bool.not (eq-path p q)) C
    Regs = regions (fo-graph D) C∖p
    X    = map (λ C' → C' , summary D C') Regs
    Z    = concat (map (split-region D p) CHs)

    no-p-tail : All (λ CH → member p (proj₁ CH) ≡ Bool.false) CHs
    no-p-tail =
      any-false-All _ CHs
        (≡-trans (≡-sym (any-map (λ C' → member p C') proj₁ CHs))
          (≡-trans (≡-sym (any-concat (eq-path p) (map proj₁ CHs)))
                   (any-false (member-All {eq = eq-path} eq-path-≡ {x = p} cross e))))

    head-perm : (p ∷ concat Regs) ↭ C
    head-perm =
      ↭-trans (↭.prep p (regions-concat (fo-graph D) C∖p))
              (filter-out-↭ {eq = eq-path} (λ {q} {q'} e' → eq-path-≡ {p = q} {q = q'} e')
                            aC e)

  -- The pieces of a split region are pairwise apart, and each pair equals its summary.
  split-separated : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) (p : Path D)
                    (CH : List (Path D) × Graph D) →
                    AllPairs (Apart (fo-graph D)) (map proj₁ (split-region D p CH))
  split-separated D p (C , H) with member p C
  ... | Bool.false = [] ∷ []
  ... | Bool.true  =
    subst (AllPairs (Apart (fo-graph D)))
          (≡-sym (map-proj₁-pair (summary D) (regions (fo-graph D) C∖p)))
          (regions-separated (fo-graph D) C∖p)
    where C∖p = filterᵇ (λ q → Bool.not (eq-path p q)) C

  split-summaries : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) (p : Path D)
                    (CH : List (Path D) × Graph D) →
                    (∀ x y (i : Fin (vertex-width y)) (j : Fin (vertex-width x)) →
                     proj₂ CH x y i j ≡ summary D (proj₁ CH) x y i j) →
                    All (λ CH' → ∀ x y (i : Fin (vertex-width y)) (j : Fin (vertex-width x)) →
                                 proj₂ CH' x y i j ≡ summary D (proj₁ CH') x y i j)
                        (split-region D p CH)
  split-summaries D p (C , H) old with member p C
  ... | Bool.false = old ∷ []
  ... | Bool.true  =
    AllP.map⁺ (universal (λ C' x y i j → ≡-refl)
                         (regions (fo-graph D) (filterᵇ (λ q → Bool.not (eq-path p q)) C)))

-- Revealing a hidden vertex preserves correct summarisation.
reveal-at-summarised : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ])
                       (p : Path D) (K : Config D) → Summarised K →
                       member p (hidden-set K) ≡ Bool.true →
                       Summarised (reveal-at D p K)
reveal-at-summarised D p K S hp .partition =
  ↭-trans (↭-sym (shift p (K .visible) (hidden-set (reveal-at D p K))))
  (↭-trans (++⁺ ↭-refl
              (reveal-set D p (K .hidden)
                 (proj₁ (proj₂ (AllPairs-++⁻ (K .visible) (hidden-set K)
                                             (partition-distinct K S))))
                 (≡-trans (≡-sym (any-map (λ C → member p C) proj₁ (K .hidden)))
                          (≡-trans (≡-sym (any-concat (eq-path p) (map proj₁ (K .hidden)))) hp))))
           (S .partition))
reveal-at-summarised D p K S hp .separated =
  subst (AllPairs (Apart (fo-graph D)))
        (≡-trans (≡-cong concat (map-∘ {g = map proj₁} {f = split-region D p} (K .hidden)))
                 (concat-map {f = proj₁} (map (split-region D p) (K .hidden))))
        (AllPairsP.concat⁺
          (AllP.map⁺ (All-map (λ {CH} _ → split-separated D p CH)
                              (S .summaries)))
          (AllPairsP.map⁺
            (AllPairs-map (λ {CH} {CH'} ap →
                             All-map (λ {C₁} m₁ →
                                        All-map (λ {C₂} m₂ →
                                                   Apart-mono {G = fo-graph D}
                                                     {C₁ = C₁} {C₂ = C₂}
                                                     {C₁' = proj₁ CH} {C₂' = proj₁ CH'}
                                                     m₁ m₂ ap)
                                                (split-⊆ D p CH'))
                                     (split-⊆ D p CH))
                          (AllPairsP.map⁻ (S .separated)))))
reveal-at-summarised D p K S hp .summaries =
  AllP.concat⁺ (AllP.map⁺ (All-map (λ {CH} old → split-summaries D p CH old) (S .summaries)))

private
  visible-entry : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) (K : Config D) →
                  ∀ x y (i : Fin (vertex-width y)) (j : Fin (vertex-width x)) →
                  visible-graph D K x y i j ≡
                  foldr two._⊔_
                        (when (Bool.not (member-vertex x (hidden-set K)) Bool.∧
                               Bool.not (member-vertex y (hidden-set K)))
                              (fo-graph D x y) i j)
                        (map (λ CH → proj₂ CH x y i j) (K .hidden))
  visible-entry D K x y i j =
    ≡-trans (foldr-entryₘ _ (map (λ CH → proj₂ CH x y) (K .hidden)) i j)
            (≡-cong (foldr two._⊔_ _)
                    (≡-sym (map-∘ {g = λ R' → R' i j} {f = λ CH → proj₂ CH x y} (K .hidden))))

-- At an entry with no hidden endpoint, the visible graph is the first-order entry joined with the
-- summary of the whole hidden set: the stored summaries assemble to the single-region summary.
visible-graph-summary : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ])
                        (K : Config D) → Summarised K →
                        ∀ x y (i : Fin (vertex-width y)) (j : Fin (vertex-width x)) →
                        member-vertex x (hidden-set K) ≡ Bool.false →
                        member-vertex y (hidden-set K) ≡ Bool.false →
                        visible-graph D K x y i j ≡
                        (fo-graph D x y i j two.⊔ summary D (hidden-set K) x y i j)
visible-graph-summary D K S x y i j hx hy =
  ≡-trans (visible-entry D K x y i j)
  (≡-trans (two.foldr-⊔-base _ (map (λ CH → proj₂ CH x y i j) (K .hidden)))
           (≡-cong₂ two._⊔_ base-eq Σ-eq))
  where
  G  = fo-graph D
  E  = hidden-set K
  Cs = map proj₁ (K .hidden)

  base-eq : when (Bool.not (member-vertex x E) Bool.∧ Bool.not (member-vertex y E)) (G x y) i j
            ≡ G x y i j
  base-eq = ≡-cong (λ b → when b (G x y) i j) (∧-intro (not-false hx) (not-false hy))

  stored-eq : map (λ CH → proj₂ CH x y i j) (K .hidden) ≡ map (λ C → summary D C x y i j) Cs
  stored-eq = ≡-trans (map-All-cong (All-map (λ inv → inv x y i j) (S .summaries)))
                      (map-∘ {g = λ C → summary D C x y i j} {f = proj₁} (K .hidden))

  seps : AllPairs (λ C C' → Apart G C' C × (any (λ q → member q C) C' ≡ Bool.false)) Cs
  seps = AllPairs-map (λ {C} {C'} (ap , d) → (apart-sym G {C} {C'} ap , proj₁ d))
                      (AllPairs-zip (S .separated) (summarised-distinct K S))

  restrict-O : restrict G E x y i j ≡ two.O
  restrict-O = ≡-cong (λ b → when b (G x y) i j) (≡-cong₂ _∨_ hx hy)

  Σ-eq : foldr two._⊔_ two.O (map (λ CH → proj₂ CH x y i j) (K .hidden))
         ≡ summary D E x y i j
  Σ-eq =
    ≡-trans (≡-cong (foldr two._⊔_ two.O) stored-eq)
    (≡-sym (≡-trans (assemble D {E} Cs (blocks-⊆ Cs) seps x y i j)
           (≡-trans (two.foldr-⊔-base (restrict G E x y i j)
                                      (map (λ C → summary D C x y i j) Cs))
                    (≡-cong (two._⊔ foldr two._⊔_ two.O (map (λ C → summary D C x y i j) Cs))
                            restrict-O))))

-- Reveal after hide at the same vertex restores the visible set and the hidden set, and hence the
-- visible graph at entries with no hidden endpoint.
hide-reveal-visible : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ])
                      (p : Path D) (K : Config D) → Summarised K →
                      member p (K .visible) ≡ Bool.true →
                      reveal-at D p (hide-at D p K) .visible ↭ K .visible
hide-reveal-visible D p K S pv =
  filter-out-↭ {eq = eq-path} (λ {q} {q'} e → eq-path-≡ {p = q} {q = q'} e)
               (proj₁ (AllPairs-++⁻ (K .visible) (hidden-set K) (partition-distinct K S))) pv

hide-reveal-hidden-set : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ])
                         (p : Path D) (K : Config D) → Summarised K →
                         member p (K .visible) ≡ Bool.true →
                         hidden-set (reveal-at D p (hide-at D p K)) ↭ hidden-set K
hide-reveal-hidden-set D p K S pv =
  drop-∷ (↭-trans (reveal-set D p (hide-at D p K .hidden)
                    (proj₁ (proj₂ (AllPairs-++⁻ (hide-at D p K .visible)
                                                (hidden-set (hide-at D p K))
                                                (partition-distinct (hide-at D p K)
                                                  (hide-at-summarised D p K S pv)))))
                    (or-introl _ _ (or-introl (eq-path p p) _ (eq-path-refl p))))
                  (hide-at-hidden-set D p K))

hide-reveal-graph : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ])
                    (p : Path D) (K : Config D) → Summarised K →
                    member p (K .visible) ≡ Bool.true →
                    ∀ x y (i : Fin (vertex-width y)) (j : Fin (vertex-width x)) →
                    member-vertex x (hidden-set K) ≡ Bool.false →
                    member-vertex y (hidden-set K) ≡ Bool.false →
                    visible-graph D (reveal-at D p (hide-at D p K)) x y i j ≡
                    visible-graph D K x y i j
hide-reveal-graph D p K S pv x y i j hx hy =
  ≡-trans (visible-graph-summary D (reveal-at D p (hide-at D p K))
             (reveal-at-summarised D p (hide-at D p K) (hide-at-summarised D p K S pv)
                (≡-trans (member-perm p (hide-at-hidden-set D p K))
                         (or-introl (eq-path p p) (member p (hidden-set K)) (eq-path-refl p))))
             x y i j
             (≡-trans (member-vertex-perm x (hide-reveal-hidden-set D p K S pv)) hx)
             (≡-trans (member-vertex-perm y (hide-reveal-hidden-set D p K S pv)) hy))
  (≡-trans (≡-cong (fo-graph D x y i j two.⊔_)
                   (summary-perm D (hide-reveal-hidden-set D p K S pv) x y i j))
           (≡-sym (visible-graph-summary D K S x y i j hx hy)))

private
  hidden-not-visible : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
                       (K : Config D) → Summarised K → ∀ {p} →
                       member p (hidden-set K) ≡ Bool.true →
                       member p (K .visible) ≡ Bool.false
  hidden-not-visible K S {p} hp =
    any-false (All-map
      (λ {q} cr → eq-path-false-sym {p = q} {q = p}
                    (member-All {eq = eq-path} eq-path-≡ {x = p} cr hp))
      (proj₂ (proj₂ (AllPairs-++⁻ (K .visible) (hidden-set K) (partition-distinct K S)))))

-- Hide after reveal at the same vertex restores the visible set exactly, the hidden set up to
-- permutation, and the visible graph at entries with no hidden endpoint.
reveal-hide-visible : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ])
                      (p : Path D) (K : Config D) → Summarised K →
                      member p (hidden-set K) ≡ Bool.true →
                      hide-at D p (reveal-at D p K) .visible ≡ K .visible
reveal-hide-visible D p K S hp =
  ≡-trans (filter-head-false (K .visible) (≡-cong Bool.not (eq-path-refl p)))
          (filter-all-true (All-map (λ h → ≡-cong Bool.not h)
             (any-false-All _ (K .visible) (hidden-not-visible K S {p = p} hp))))

reveal-hide-hidden-set : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ])
                         (p : Path D) (K : Config D) → Summarised K →
                         member p (hidden-set K) ≡ Bool.true →
                         hidden-set (hide-at D p (reveal-at D p K)) ↭ hidden-set K
reveal-hide-hidden-set D p K S hp =
  ↭-trans (hide-at-hidden-set D p (reveal-at D p K))
          (reveal-set D p (K .hidden)
             (proj₁ (proj₂ (AllPairs-++⁻ (K .visible) (hidden-set K)
                                         (partition-distinct K S))))
             (≡-trans (≡-sym (any-map (λ C → member p C) proj₁ (K .hidden)))
                      (≡-trans (≡-sym (any-concat (eq-path p) (map proj₁ (K .hidden)))) hp)))

reveal-hide-graph : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ])
                    (p : Path D) (K : Config D) → Summarised K →
                    member p (hidden-set K) ≡ Bool.true →
                    ∀ x y (i : Fin (vertex-width y)) (j : Fin (vertex-width x)) →
                    member-vertex x (hidden-set K) ≡ Bool.false →
                    member-vertex y (hidden-set K) ≡ Bool.false →
                    visible-graph D (hide-at D p (reveal-at D p K)) x y i j ≡
                    visible-graph D K x y i j
reveal-hide-graph D p K S hp x y i j hx hy =
  ≡-trans (visible-graph-summary D (hide-at D p (reveal-at D p K))
             (hide-at-summarised D p (reveal-at D p K)
                (reveal-at-summarised D p K S hp)
                (≡-cong (_∨ member p (K .visible)) (eq-path-refl p)))
             x y i j
             (≡-trans (member-vertex-perm x (reveal-hide-hidden-set D p K S hp)) hx)
             (≡-trans (member-vertex-perm y (reveal-hide-hidden-set D p K S hp)) hy))
  (≡-trans (≡-cong (fo-graph D x y i j two.⊔_)
                   (summary-perm D (reveal-hide-hidden-set D p K S hp) x y i j))
           (≡-sym (visible-graph-summary D K S x y i j hx hy)))

private
  restrict-≤ : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
               (G : Graph D) (C : List (Path D)) →
               ∀ x y (i : Fin (vertex-width y)) (j : Fin (vertex-width x)) →
               (restrict G C x y i j two.⊔ G x y i j) ≡ G x y i j
  restrict-≤ G C x y i j with member-vertex x C ∨ member-vertex y C
  ... | Bool.true  = two.⊔-idem
  ... | Bool.false = ≡-refl

  restrict-hidden-agree : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
                          (G : Graph D) (C : List (Path D)) →
                          All (λ r → ((z : Vertex D) (i : Fin (vertex-width z))
                                      (j : Fin (vertex-width r)) →
                                      G r z i j ≡ restrict G C r z i j)
                                   × ((z : Vertex D) (i : Fin (vertex-width r))
                                      (j : Fin (vertex-width z)) →
                                      G z r i j ≡ restrict G C z r i j))
                              (map at C)
  restrict-hidden-agree G C =
    AllP.map⁺ (All-map (λ {q} hq →
      (λ z i j → ≡-sym (≡-cong (λ b → when b (G (at q) z) i j)
                               (or-introl (member q C) (member-vertex z C) hq))) ,
      (λ z i j → ≡-sym (≡-cong (λ b → when b (G z (at q)) i j)
                               (or-intror (member-vertex z C) (member q C) hq))))
      (any-self eq-path-refl C))

-- The paper's assembly lemma: at an entry with no hidden endpoint, the visible graph is the
-- first-order graph with the whole hidden set hidden. The restriction in the summary is invisible
-- there, since the full graph and its restriction agree on hidden rows and columns.
summaries-assemble : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ])
                     (K : Config D) → Summarised K →
                     ∀ x y (i : Fin (vertex-width y)) (j : Fin (vertex-width x)) →
                     member-vertex x (hidden-set K) ≡ Bool.false →
                     member-vertex y (hidden-set K) ≡ Bool.false →
                     visible-graph D K x y i j ≡
                     hide-all (fo-graph D) (map at (hidden-set K)) x y i j
summaries-assemble D K S x y i j hx hy =
  ≡-trans (visible-graph-summary D K S x y i j hx hy)
          (≡-sym (HA.agree-add D {G = restrict (fo-graph D) (hidden-set K)} {G' = fo-graph D}
                    (map at (hidden-set K))
                    (restrict-≤ (fo-graph D) (hidden-set K))
                    (restrict-hidden-agree (fo-graph D) (hidden-set K))
                    x y i j))
