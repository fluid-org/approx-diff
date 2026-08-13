{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.Bool as Bool using (Bool; not; if_then_else_; _∧_; _∨_)
open import Data.Bool.ListAction using (any)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to All-map)
open import Data.Bool.Properties using (∧-comm)
open import Data.List using (List; []; _∷_; _++_; length; map; concat; filterᵇ)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
import Data.List.Relation.Unary.All.Properties as AllP
import Data.List.Relation.Unary.AllPairs.Properties as AllPairsP
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (↭-length; drop-∷)
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Nat.ListAction using (sum)
open import Data.List.Properties using (concat-++; concat-map; ++-identityʳ; length-map; map-∘)
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
-- initial configuration is canonical, and the hide and reveal moves preserve canonicity.
module interaction.maintenance {ℓ} (Sig : Signature ℓ) (𝒫 : Primitives two.semiring Sig) where

open Signature Sig
open Primitives 𝒫
open import language-syntax Sig renaming (_,_ to _▸_) hiding (if_then_else_)
open import language-operational.evaluation Sig 𝒫
open import interaction.path Sig 𝒫
open import interaction.graph Sig 𝒫
open import interaction.hide Sig 𝒫
open import interaction.config Sig 𝒫
open import interaction.moves Sig 𝒫

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

private
  ↭↭-of-≡ : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
            {xss yss : List (List (Path D))} → xss ≡ yss → xss ↭↭ yss
  ↭↭-of-≡ ≡-refl = ↭↭-refl

  -- Each region of ws lies inside ws.
  regions-⊆ : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
              (G : Graph D) (ws : List (Path D)) →
              All (λ C → ∀ q → member q C ≡ Bool.true → member q ws ≡ Bool.true)
                  (regions G ws)
  regions-⊆ G ws =
    All-map (λ {C} inc q h → ≡-trans (≡-sym (member-perm q (regions-concat G ws))) (inc q h))
            (blocks-⊆ (regions G ws))

  -- Merging a vertex with no adjacency into a suffix of regions leaves the suffix alone.
  merge-region-inert : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
                       (G : Graph D) (w : Path D) (X Y : List (List (Path D))) →
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

-- Regions distribute over a concatenation with an apart suffix: no merge crosses the boundary.
regions-apart : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
                (G : Graph D) (B rest : List (Path D)) → Apart G B rest →
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
  apart-concat : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
                 {G : Graph D} {C : List (Path D)} {Cs : List (List (Path D))} →
                 All (Apart G C) Cs → Apart G C (concat Cs)
  apart-concat {G = G} {C} {Cs} aps =
    ≡-trans (any-cong (λ q → any-concat (λ q' → adjacent G (at q) (at q')) Cs) C)
    (≡-trans (any-comm (λ q C' → any (λ q' → adjacent G (at q) (at q')) C') C Cs)
             (any-false aps))

  regions-nonempty : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
                     (G : Graph D) (ws : List (Path D)) →
                     All (λ C → 1 ≤ length C) (regions G ws)
  regions-nonempty G []       = []
  regions-nonempty G (w ∷ ws) =
    s≤s z≤n ∷ proj₂ (partition-All (adj G w) (regions-nonempty G ws))

-- Regions of a concatenation of pairwise-apart blocks are the blocks' regions.
regions-apart-concat : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
                       {G : Graph D} {Cs : List (List (Path D))} →
                       AllPairs (Apart G) Cs →
                       regions G (concat Cs) ↭↭ concat (map (regions G) Cs)
regions-apart-concat {G = G}           []                    = ↭↭-refl
regions-apart-concat {G = G} {C ∷ Cs} (aps ∷ pairs) =
  H.trans (regions-apart G C (concat Cs) (apart-concat {G = G} {C = C} {Cs = Cs} aps))
          (↭↭-++⁺ ↭↭-refl (regions-apart-concat pairs))

-- Each stored region of a canonical summarised configuration is a single region: distribution
-- makes the stored list a permutation of the per-block regions, and a permutation preserves
-- length while every nonempty block contributes at least one region.
blocks-one-region : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ])
                    (K : Config D) → Summarised K → Maintained K →
                    All (λ C → regions (fo-graph D) C ↭↭ (C ∷ []))
                        (map proj₁ (K .hidden))
blocks-one-region D K S M = All-map (λ {C} e → one {C} e) lens1
  where
  G  = fo-graph D
  Cs = map proj₁ (K .hidden)

  perm2 : Cs ↭↭ concat (map (regions G) Cs)
  perm2 = H.trans (M .canonical) (regions-apart-concat (S .separated))

  nonempty : All (λ C → 1 ≤ length C) Cs
  nonempty = perm-All (λ {C} {C'} pc h → subst (1 ≤_) (↭-length pc) h)
                      (H.sym ↭-sym (M .canonical))
                      (regions-nonempty G (hidden-set K))

  len-regions : ∀ (C : List (Path D)) → 1 ≤ length C → 1 ≤ length (regions G C)
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

  one : ∀ {C : List (Path D)} → length (regions G C) ≡ 1 → regions G C ↭↭ (C ∷ [])
  one {C} e with singleton (regions G C) e
  ... | (C₀ , eq) =
    subst (_↭↭ (C ∷ [])) (≡-sym eq)
          (H.prep (↭-trans (↭-reflexive (≡-sym (++-identityʳ C₀)))
                           (subst (λ z → concat z ↭ C) eq (regions-concat G C)))
                  (H.refl []))

-- The reveal move preserves canonicity: splitting the region containing p computes the regions of
-- the hidden set with p removed, block by block.
reveal-at-maintained : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ])
                       (p : Path D) (K : Config D) → Summarised K → Maintained K →
                       member p (hidden-set K) ≡ Bool.true →
                       Maintained (reveal-at D p K)
reveal-at-maintained D p K S M hp .canonical =
  subst (λ z → z ↭↭ regions G (hidden-set (reveal-at D p K)))
        (≡-trans (≡-cong concat (map-∘ {g = map proj₁} {f = split-region D p} (K .hidden)))
                 (concat-map {f = proj₁} (map (split-region D p) (K .hidden))))
        (H.trans blocks-part
        (H.trans (↭↭-of-≡ (≡-cong concat maps-eq))
        (H.trans (H.sym ↭.↭-sym (regions-apart-concat {G = G} apart-filtered))
        (H.trans (↭↭-of-≡ (≡-cong (regions G) (≡-sym (filter-concat notp Cs))))
                 (H.sym ↭.↭-sym (regions-perm G hrev))))))
  where
  G    = fo-graph D
  Cs   = map proj₁ (K .hidden)
  notp = λ q → not (eq-path p q)

  vis-hid-distinct : AllPairs (λ q q' → eq-path q q' ≡ Bool.false)
                             (K .visible ++ hidden-set K)
  vis-hid-distinct =
    AllPairs-perm (λ {q} {q'} h → eq-path-false-sym {p = q} {q = q'} h)
                  (↭.↭-sym (S .partition)) (FO-distinct D)

  distinct-hs : AllPairs (λ q q' → eq-path q q' ≡ Bool.false) (hidden-set K)
  distinct-hs = proj₁ (proj₂ (AllPairs-++⁻ (K .visible) (hidden-set K) vis-hid-distinct))

  hrev : hidden-set (reveal-at D p K) ↭ filterᵇ notp (hidden-set K)
  hrev = drop-∷
    (↭-trans (reveal-set D p (K .hidden) distinct-hs
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
                    (S .separated))

  maps-eq : map (λ CH → regions G (filterᵇ notp (proj₁ CH))) (K .hidden) ≡
            map (regions G) (map (filterᵇ notp) Cs)
  maps-eq =
    ≡-trans (map-∘ {g = λ C → regions G (filterᵇ notp C)} {f = proj₁} (K .hidden))
            (map-∘ {g = regions G} {f = filterᵇ notp} Cs)

  split-true : ∀ C (H' : Graph D) → member p C ≡ Bool.true →
               split-region D p (C , H') ≡
               map (λ C' → C' , summary D C') (regions G (filterᵇ notp C))
  split-true C H' e =
    ≡-cong (λ b → if b then map (λ C' → C' , summary D C') (regions G (filterᵇ notp C))
                       else (C , H') ∷ []) e

  split-false : ∀ C (H' : Graph D) → member p C ≡ Bool.false →
                split-region D p (C , H') ≡ (C , H') ∷ []
  split-false C H' e =
    ≡-cong (λ b → if b then map (λ C' → C' , summary D C') (regions G (filterᵇ notp C))
                       else (C , H') ∷ []) e

  per-block : ∀ CH → regions G (proj₁ CH) ↭↭ (proj₁ CH ∷ []) →
              map proj₁ (split-region D p CH) ↭↭ regions G (filterᵇ notp (proj₁ CH))
  per-block (C , H') one =
    bool-case (member p C)
      (λ e → ↭↭-of-≡ (≡-trans (≡-cong (map proj₁) (split-true C H' e))
                              (map-proj₁-pair (summary D) (regions G (filterᵇ notp C)))))
      (λ e → subst₂ _↭↭_
               (≡-sym (≡-cong (map proj₁) (split-false C H' e)))
               (≡-sym (≡-cong (regions G)
                        (filter-all-true (All-map (λ h → ≡-cong not h)
                                                  (any-false-All _ C e)))))
               (H.sym ↭.↭-sym one))

  blocks-part : concat (map (λ CH → map proj₁ (split-region D p CH)) (K .hidden)) ↭↭
                concat (map (λ CH → regions G (filterᵇ notp (proj₁ CH))) (K .hidden))
  blocks-part =
    concat-↭↭ (All-map (λ {CH} one → per-block CH one)
                       (AllP.map⁻ (blocks-one-region D K S M)))
