{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.Bool as Bool using (Bool; not; _∧_; _∨_)
open import Data.Bool.ListAction using (any)
open import Data.Bool.Properties using (∧-comm)
open import Data.List using (List; []; _∷_; _++_; map; concat; filterᵇ; partitionᵇ)
open import Data.List.Properties using (concat-++)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
import Data.List.Relation.Binary.Permutation.Homogeneous as H
import Data.List.Relation.Binary.Permutation.Propositional as ↭
open ↭ using (_↭_; ↭-sym; ↭-trans; ↭-reflexive)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; subst₂)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; cong to ≡-cong; cong₂ to ≡-cong₂)
open import list
open import signature using (Signature)
open import primitives using (Primitives)
import two

-- The stored regions of a reachable configuration are exactly the regions of its hidden set: the
-- merge step of the regions computation respects reordering of the regions it merges.
module language-operational.maintenance {ℓ} (Sig : Signature ℓ) (𝒫 : Primitives two.semiring Sig) where

open Signature Sig
open Primitives 𝒫
open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.evaluation Sig 𝒫
open import language-operational.path Sig 𝒫
open import language-operational.graph Sig 𝒫
open import language-operational.hide Sig 𝒫
open import language-operational.moves Sig 𝒫

merge-region-resp : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
                    (G : Graph D) (w : Path D) {rss rss' : List (List (Path D))} →
                    rss ↭↭ rss' → merge-region G w rss ↭↭ merge-region G w rss'
merge-region-resp G w {rss} {rss'} p =
  H.prep (↭.prep w (concat-resp (proj₁ tp-p))) (proj₂ tp-p)
  where
  tp-p = partition-permᴿ (any (λ q → adjacent G (at w) (at q)))
                         (λ {C} {C'} pc → any-perm (λ q → adjacent G (at w) (at q)) pc)
                         p

private
  adj : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
        (G : Graph D) (w : Path D) → List (Path D) → Bool
  adj G w C = any (λ q → adjacent G (at w) (at q)) C

  merge-region-filter : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
                        (G : Graph D) (w : Path D) (rss : List (List (Path D))) →
                        merge-region G w rss ≡
                        ((w ∷ concat (filterᵇ (adj G w) rss)) ∷
                         filterᵇ (λ C → not (adj G w C)) rss)
  merge-region-filter G w rss =
    ≡-cong (λ u → (w ∷ concat (proj₁ u)) ∷ proj₂ u) (partition-filter (adj G w) rss)

-- Merging two vertices commutes: if they are adjacent or share an adjacent region both orders
-- produce the one merged region, and otherwise the merges are independent.
merge-region-comm : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
                    (G : Graph D) (w w' : Path D) (rss : List (List (Path D))) →
                    merge-region G w (merge-region G w' rss) ↭↭
                    merge-region G w' (merge-region G w rss)
merge-region-comm {D = D} G w w' rss =
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

  Goal : Set ℓ
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

-- Regions are insensitive to the order in which their vertices are enumerated.
regions-perm : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
               (G : Graph D) {ws ws' : List (Path D)} → ws ↭ ws' →
               regions G ws ↭↭ regions G ws'
regions-perm G ↭.refl         = ↭↭-refl
regions-perm G (↭.prep w p)   = merge-region-resp G w (regions-perm G p)
regions-perm G (↭.swap {xs = ws₁} {ys = ws₂} w w' p) =
  H.trans (merge-region-resp G w (merge-region-resp G w' (regions-perm G p)))
          (merge-region-comm G w w' (regions G ws₂))
regions-perm G (↭.trans p q)  = H.trans (regions-perm G p) (regions-perm G q)

-- A canonical configuration: the stored regions are the regions of the hidden set.
record Maintained {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
                  (K : Config D) : Set ℓ where
  field
    canonical : map proj₁ (K .hidden) ↭↭ regions (fo-graph D) (hidden-set K)

open Maintained public

initial-maintained : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) →
                     Maintained (initial D)
initial-maintained D .canonical =
  subst (λ z → z ↭↭ regions (fo-graph D) (concat z))
        (≡-sym (map-proj₁-pair (summary D) (regions (fo-graph D) (FO D))))
        (regions-perm (fo-graph D) (↭-sym (regions-concat (fo-graph D) (FO D))))

-- The hide move preserves canonicity: its merge is the merge step of the regions computation.
hide-at-maintained : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ])
                     (p : Path D) (K : Config D) → Maintained K →
                     Maintained (hide-at D p K)
hide-at-maintained D p K M .canonical =
  subst (λ z → z ↭↭ regions (fo-graph D) (hidden-set (hide-at D p K)))
        lhs-eq
        (H.trans (merge-region-resp (fo-graph D) p (M .canonical))
                 (H.sym ↭-sym (regions-perm (fo-graph D) (hide-at-hidden-set D p K))))
  where
  lhs-eq : merge-region (fo-graph D) p (map proj₁ (K .hidden)) ≡
           map proj₁ (hide-at D p K .hidden)
  lhs-eq = ≡-cong₂ (λ u v → (p ∷ concat u) ∷ v)
             (map-partition₁ proj₁ (adj (fo-graph D) p) (K .hidden))
             (map-partition₂ proj₁ (adj (fo-graph D) p) (K .hidden))
