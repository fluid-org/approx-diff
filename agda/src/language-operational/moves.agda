{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.Bool as Bool using (Bool; _∨_)
open import Data.Bool.ListAction using (any)
open import Data.Bool.Properties using (∨-comm)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map; concat; partitionᵇ)
open import Data.List.Relation.Unary.All using (All; []; _∷_; universal)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
import Data.List.Relation.Unary.All.Properties as AllP
open import Data.List.Properties using (concat-++; map-++)
import Data.List.Relation.Binary.Permutation.Propositional as ↭
open ↭ using (_↭_; ↭-trans; ↭-reflexive)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (map⁺)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; cong to ≡-cong; cong₂ to ≡-cong₂)
open import list
open import signature using (Signature)
open import primitives using (Primitives)
import matrix
import two

-- The moves preserve the invariant that the stored regions partition the hidden set into
-- pairwise-apart pieces, each carrying its summary. So far: summaries are stable under
-- permutation, and hiding preserves the partition and apartness.
module language-operational.moves {ℓ} (Sig : Signature ℓ) (𝒫 : Primitives two.semiring Sig) where

open Signature Sig
open Primitives 𝒫
open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.evaluation Sig 𝒫
open import language-operational.path Sig 𝒫
open import language-operational.graph Sig 𝒫
open import language-operational.hide Sig 𝒫
open import language-operational.topological-order Sig 𝒫

private
  module M = matrix.Mat two.semiring

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
  ≡-trans (hide-all-cong (map at C) (restrict-perm (fo-graph D) p) x y i j)
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
