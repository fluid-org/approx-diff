{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.Bool as Bool using (Bool; not; if_then_else_; _∧_; _∨_)
open import Data.Bool.ListAction using (any)
open import Data.List.Relation.Unary.All using (All; []; _∷_; universal) renaming (map to All-map)
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
open import Data.Sum using (inj₁; inj₂)
import Data.List.Relation.Binary.Permutation.Homogeneous as H
import Data.List.Relation.Binary.Permutation.Propositional as ↭
open ↭ using (_↭_; ↭-sym; ↭-trans; ↭-reflexive)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; subst₂)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; cong to ≡-cong; cong₂ to ≡-cong₂)
open import Data.Nat using (ℕ)
open import Level using (0ℓ)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary.Decidable using (⌊_⌋; yes; no)
open import list
import two

-- The moves preserve correct summarisation, including the canonicity of the stored regions: the
-- initial configuration is correctly summarised, and the hide and reveal moves preserve it.
module interaction.maintenance where

open import interaction.graph-algebra 0ℓ
open import interaction.config
open import interaction.moves

module _ {Inp : Set} {iw : Inp → ℕ} {n : ℕ} (𝒢 : Graph Inp iw n) where

  open Graph 𝒢 using (Path)
  open Interaction 𝒢

  private
    at : Path → V 𝒢
    at p = inj₂ (inj₁ p)

    eq-path : Path → Path → Bool
    eq-path p q = ⌊ Graph._≟_ 𝒢 p q ⌋

    eq-path-refl : ∀ (p : Path) → eq-path p p ≡ Bool.true
    eq-path-refl p with Graph._≟_ 𝒢 p p
    ... | yes _ = ≡-refl
    ... | no ¬e = ⊥-elim (¬e ≡-refl)

    eq-path-≡ : ∀ {p q : Path} → eq-path p q ≡ Bool.true → p ≡ q
    eq-path-≡ {p} {q} h with Graph._≟_ 𝒢 p q
    ... | yes e = e

    eq-path-false-sym : ∀ {p q : Path} → eq-path p q ≡ Bool.false → eq-path q p ≡ Bool.false
    eq-path-false-sym {p} {q} h with Graph._≟_ 𝒢 q p
    ... | no _  = ≡-refl
    ... | yes e with Graph._≟_ 𝒢 p q
    ...   | no ¬e = ⊥-elim (¬e (≡-sym e))

  merge-region-resp : (G : Entries (vw 𝒢)) (w : Path) {rss rss' : List (List (Path))} →
                      rss ↭↭ rss' → merge-region G w rss ↭↭ merge-region G w rss'
  merge-region-resp G w {rss} {rss'} p =
    H.prep (↭.prep w (concat-resp (proj₁ tp-p))) (proj₂ tp-p)
    where
    tp-p = partition-permᴿ (any (λ q → adjacent G (at w) (at q)))
                           (λ {C} {C'} pc → any-perm (λ q → adjacent G (at w) (at q)) pc)
                           p

  private
    adj : (G : Entries (vw 𝒢)) (w : Path) → List (Path) → Bool
    adj G w C = any (λ q → adjacent G (at w) (at q)) C

    merge-region-filter : (G : Entries (vw 𝒢)) (w : Path) (rss : List (List (Path))) →
                          merge-region G w rss ≡
                          ((w ∷ concat (filterᵇ (adj G w) rss)) ∷
                           filterᵇ (λ C → not (adj G w C)) rss)
    merge-region-filter G w rss =
      ≡-cong (λ u → (w ∷ concat (proj₁ u)) ∷ proj₂ u) (partition-filter (adj G w) rss)

  -- Merging two vertices commutes: if they are adjacent or share an adjacent region both orders
  -- produce the one merged region, and otherwise the merges are independent.
  merge-region-comm : (G : Entries (vw 𝒢)) (w w' : Path) (rss : List (List (Path))) →
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
      ≡-cong₂ _∨_ (adjacent-sym 𝒢 G (at w) (at w'))
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

  -- Regions are insensitive to the order in which their vertices are enumerated.
  regions-perm : (G : Entries (vw 𝒢)) {ws ws' : List (Path)} → ws ↭ ws' →
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

  initial-summarised : Summarised 𝒢 (initial)
  initial-summarised .partition =
    subst (λ z → concat z ↭ FO 𝒢) (≡-sym stored≡) (regions-concat 𝒢 (fo-graph 𝒢) (FO 𝒢))
  initial-summarised .canonical =
    subst (λ z → z ↭↭ regions (fo-graph 𝒢) (concat z))
          (≡-sym stored≡)
          (regions-perm (fo-graph 𝒢) (↭-sym (regions-concat 𝒢 (fo-graph 𝒢) (FO 𝒢))))
  initial-summarised .summaries =
    AllP.map⁺ (universal (λ C x y i j → ≡-refl) (regions (fo-graph 𝒢) (FO 𝒢)))

  hide-at-summarised : (p : Path) (K : Config 𝒢) (S : Summarised 𝒢 K) →
                       member p (K .visible) ≡ Bool.true →
                       Summarised 𝒢 (hide-at p K)
  hide-at-summarised p K S pv .partition = hide-at-partition 𝒢 p K S pv
  hide-at-summarised p K S pv .canonical =
    subst (λ z → z ↭↭ regions (fo-graph 𝒢) (hidden-set (hide-at p K)))
          lhs-eq
          (H.trans (merge-region-resp (fo-graph 𝒢) p (S .canonical))
                   (H.sym ↭-sym (regions-perm (fo-graph 𝒢) (hide-at-hidden-set 𝒢 p K))))
    where
    lhs-eq : merge-region (fo-graph 𝒢) p (map proj₁ (K .hidden)) ≡
             map proj₁ (hide-at p K .hidden)
    lhs-eq = ≡-cong₂ (λ u v → (p ∷ concat u) ∷ v)
               (map-partition₁ proj₁ (adj (fo-graph 𝒢) p) (K .hidden))
               (map-partition₂ proj₁ (adj (fo-graph 𝒢) p) (K .hidden))
  hide-at-summarised p K S pv .summaries = hide-at-summaries 𝒢 p K S pv

  private
    ↭↭-of-≡ : {xss yss : List (List (Path))} → xss ≡ yss → xss ↭↭ yss
    ↭↭-of-≡ ≡-refl = ↭↭-refl

    -- Each region of ws lies inside ws.
    regions-⊆ : (G : Entries (vw 𝒢)) (ws : List (Path)) →
                All (λ C → ∀ q → member q C ≡ Bool.true → member q ws ≡ Bool.true)
                    (regions G ws)
    regions-⊆ G ws =
      All-map (λ {C} inc q h → ≡-trans (≡-sym (member-perm 𝒢 q (regions-concat 𝒢 G ws))) (inc q h))
              (blocks-⊆ 𝒢 (regions G ws))

    -- Merging a vertex with no adjacency into a suffix of regions leaves the suffix alone.
    merge-region-inert : (G : Entries (vw 𝒢)) (w : Path) (X Y : List (List (Path))) →
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
  regions-apart : (G : Entries (vw 𝒢)) (B rest : List (Path)) → Apart 𝒢 G B rest →
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
    apart-concat : {G : Entries (vw 𝒢)} {C : List (Path)} {Cs : List (List (Path))} →
                   All (Apart 𝒢 G C) Cs → Apart 𝒢 G C (concat Cs)
    apart-concat {G = G} {C} {Cs} aps =
      ≡-trans (any-cong (λ q → any-concat (λ q' → adjacent G (at q) (at q')) Cs) C)
      (≡-trans (any-comm (λ q C' → any (λ q' → adjacent G (at q) (at q')) C') C Cs)
               (any-false aps))

    regions-nonempty : (G : Entries (vw 𝒢)) (ws : List (Path)) →
                       All (λ C → 1 ≤ length C) (regions G ws)
    regions-nonempty G []       = []
    regions-nonempty G (w ∷ ws) =
      s≤s z≤n ∷ proj₂ (partition-All (adj G w) (regions-nonempty G ws))

  -- Regions of a concatenation of pairwise-apart blocks are the blocks' regions.
  regions-apart-concat : {G : Entries (vw 𝒢)} {Cs : List (List (Path))} →
                         AllPairs (Apart 𝒢 G) Cs →
                         regions G (concat Cs) ↭↭ concat (map (regions G) Cs)
  regions-apart-concat {G = G}           []                    = ↭↭-refl
  regions-apart-concat {G = G} {C ∷ Cs} (aps ∷ pairs) =
    H.trans (regions-apart G C (concat Cs) (apart-concat {G = G} {C = C} {Cs = Cs} aps))
            (↭↭-++⁺ ↭↭-refl (regions-apart-concat pairs))

  -- Each stored region of a summarised configuration is a single region: distribution
  -- makes the stored list a permutation of the per-block regions, and a permutation preserves
  -- length while every nonempty block contributes at least one region.
  blocks-one-region : (K : Config 𝒢) → Summarised 𝒢 K →
                      All (λ C → regions (fo-graph 𝒢) C ↭↭ (C ∷ []))
                          (map proj₁ (K .hidden))
  blocks-one-region K S = All-map (λ {C} e → one {C} e) lens1
    where
    G  = fo-graph 𝒢
    Cs = map proj₁ (K .hidden)

    perm2 : Cs ↭↭ concat (map (regions G) Cs)
    perm2 = H.trans (S .canonical) (regions-apart-concat (separated 𝒢 S))

    nonempty : All (λ C → 1 ≤ length C) Cs
    nonempty = perm-All (λ {C} {C'} pc h → subst (1 ≤_) (↭-length pc) h)
                        (H.sym ↭-sym (S .canonical))
                        (regions-nonempty G (hidden-set K))

    len-regions : ∀ (C : List (Path)) → 1 ≤ length C → 1 ≤ length (regions G C)
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

    one : ∀ {C : List (Path)} → length (regions G C) ≡ 1 → regions G C ↭↭ (C ∷ [])
    one {C} e with singleton (regions G C) e
    ... | (C₀ , eq) =
      subst (_↭↭ (C ∷ [])) (≡-sym eq)
            (H.prep (↭-trans (↭-reflexive (≡-sym (++-identityʳ C₀)))
                             (subst (λ z → concat z ↭ C) eq (regions-concat 𝒢 G C)))
                    (H.refl []))

  -- The reveal move preserves correct summarisation: splitting the region containing p computes the
  -- regions of the hidden set with p removed, block by block.
  reveal-at-summarised : (p : Path) (K : Config 𝒢) (S : Summarised 𝒢 K) →
                         member p (hidden-set K) ≡ Bool.true →
                         Summarised 𝒢 (reveal-at p K)
  reveal-at-summarised p K S hp .partition = reveal-at-partition 𝒢 p K S hp
  reveal-at-summarised p K S hp .summaries = reveal-at-summaries 𝒢 p K S hp
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

    vis-hid-distinct : AllPairs (λ q q' → eq-path q q' ≡ Bool.false)
                               (K .visible ++ hidden-set K)
    vis-hid-distinct =
      AllPairs-perm (λ {q} {q'} h → eq-path-false-sym {p = q} {q = q'} h)
                    (↭.↭-sym (S .partition)) (FO-distinct 𝒢)

    distinct-hs : AllPairs (λ q q' → eq-path q q' ≡ Bool.false) (hidden-set K)
    distinct-hs = proj₁ (proj₂ (AllPairs-++⁻ (K .visible) (hidden-set K) vis-hid-distinct))

    hrev : hidden-set (reveal-at p K) ↭ filterᵇ notp (hidden-set K)
    hrev = drop-∷
      (↭-trans (reveal-set 𝒢 p (K .hidden) distinct-hs
                  (≡-trans (≡-sym (any-map (λ C → member p C) proj₁ (K .hidden)))
                           (≡-trans (≡-sym (any-concat (eq-path p) Cs)) hp)))
               (↭.↭-sym (filter-out-↭ {eq = eq-path}
                          (λ {q} {q'} e → eq-path-≡ {p = q} {q = q'} e)
                          distinct-hs hp)))

    apart-filtered : AllPairs (Apart 𝒢 G) (map (filterᵇ notp) Cs)
    apart-filtered =
      AllPairsP.map⁺
        (AllPairs-map (λ {C} {C'} ap →
                         Apart-mono 𝒢 {G = G} {C₁ = filterᵇ notp C} {C₂ = filterᵇ notp C'}
                                    {C₁' = C} {C₂' = C'}
                                    (λ q h → any-filterᵇ (eq-path q) notp C h)
                                    (λ q h → any-filterᵇ (eq-path q) notp C' h)
                                    ap)
                      (separated 𝒢 S))

    maps-eq : map (λ CH → regions G (filterᵇ notp (proj₁ CH))) (K .hidden) ≡
              map (regions G) (map (filterᵇ notp) Cs)
    maps-eq =
      ≡-trans (map-∘ {g = λ C → regions G (filterᵇ notp C)} {f = proj₁} (K .hidden))
              (map-∘ {g = regions G} {f = filterᵇ notp} Cs)

    split-true : ∀ C (H' : Entries (vw 𝒢)) → member p C ≡ Bool.true →
                 split-region p (C , H') ≡
                 map (λ C' → C' , summary C') (regions G (filterᵇ notp C))
    split-true C H' e =
      ≡-cong (λ b → if b then map (λ C' → C' , summary C') (regions G (filterᵇ notp C))
                         else (C , H') ∷ []) e

    split-false : ∀ C (H' : Entries (vw 𝒢)) → member p C ≡ Bool.false →
                  split-region p (C , H') ≡ (C , H') ∷ []
    split-false C H' e =
      ≡-cong (λ b → if b then map (λ C' → C' , summary C') (regions G (filterᵇ notp C))
                         else (C , H') ∷ []) e

    per-block : ∀ CH → regions G (proj₁ CH) ↭↭ (proj₁ CH ∷ []) →
                map proj₁ (split-region p CH) ↭↭ regions G (filterᵇ notp (proj₁ CH))
    per-block (C , H') one =
      bool-case (member p C)
        (λ e → ↭↭-of-≡ (≡-trans (≡-cong (map proj₁) (split-true C H' e))
                                (map-proj₁-pair summary (regions G (filterᵇ notp C)))))
        (λ e → subst₂ _↭↭_
                 (≡-sym (≡-cong (map proj₁) (split-false C H' e)))
                 (≡-sym (≡-cong (regions G)
                          (filter-all-true (All-map (λ h → ≡-cong not h)
                                                    (any-false-All _ C e)))))
                 (H.sym ↭.↭-sym one))

    blocks-part : concat (map (λ CH → map proj₁ (split-region p CH)) (K .hidden)) ↭↭
                  concat (map (λ CH → regions G (filterᵇ notp (proj₁ CH))) (K .hidden))
    blocks-part =
      concat-↭↭ (All-map (λ {CH} one → per-block CH one)
                         (AllP.map⁻ (blocks-one-region K S)))
