{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.Bool as Bool using (Bool; _∨_)
open import Data.Bool.ListAction using (any)
open import Data.Bool.Properties using (∨-comm; ∧-comm)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map; concat; filterᵇ; partitionᵇ)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Binary.Permutation.Homogeneous as H
import Data.List.Relation.Binary.Permutation.Propositional as ↭
open ↭ using (_↭_; ↭-trans; ↭-sym; ↭-reflexive)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (map⁺)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; cong to ≡-cong; cong₂ to ≡-cong₂)
open import list
open import signature using (Signature)
open import primitives using (Primitives)
import matrix
import two

-- The moves preserve the invariant that each hidden pair is a region of the hidden set with its
-- summary, and are mutually inverse. So far: summaries and the regions computation are stable
-- under permutation.
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

-- Region lists that agree up to reordering of the regions and of the members within each.
_≈ᵣ_ : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} →
       List (List (Path D)) → List (List (Path D)) → Set ℓ
_≈ᵣ_ = _↭↭_

-- The congruence step of the regions computation: equivalent prior regions give equivalent
-- regions after a vertex is added, since adjacency of the vertex reads regions only through
-- membership and the merged members only through concatenation.
regions-prep : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
               (G : Graph D) (w : Path D) {ws ws' : List (Path D)} →
               regions G ws ≈ᵣ regions G ws' →
               regions G (w ∷ ws) ≈ᵣ regions G (w ∷ ws')
regions-prep G w ih =
  H.prep (↭.prep w (concat-resp (proj₁ tp))) (proj₂ tp)
  where tp = partition-resp (any (λ q → adjacent G (at w) (at q)))
                            (any-perm (λ q → adjacent G (at w) (at q)))
                            ih

-- Adding two vertices to a region list in either order gives equivalent regions. Both orders
-- merge exactly when the vertices are adjacent or some region is adjacent to both; in that case
-- the merged region collects the regions adjacent to either vertex, and otherwise the two new
-- regions absorb disjoint groups.
private
  module Step {ℓa} (A : Set ℓa) (adj-a adj-b : A → Bool) (a b : A)
              (sym-ab : adj-a b ≡ adj-b a) where
    fA fB : List A → Bool
    fA = any adj-a
    fB = any adj-b

    stepA stepB stepA' stepB' : List (List A) → List (List A)
    stepA  R = (a ∷ concat (proj₁ (partitionᵇ fA R))) ∷ proj₂ (partitionᵇ fA R)
    stepB  R = (b ∷ concat (proj₁ (partitionᵇ fB R))) ∷ proj₂ (partitionᵇ fB R)
    stepA' R = (a ∷ concat (filterᵇ fA R)) ∷ filterᵇ (λ C → Bool.not (fA C)) R
    stepB' R = (b ∷ concat (filterᵇ fB R)) ∷ filterᵇ (λ C → Bool.not (fB C)) R

    stepA≡ : ∀ R → stepA R ≡ stepA' R
    stepA≡ R = ≡-cong₂ _∷_ (≡-cong (λ z → a ∷ concat z) (part₁-filter fA R)) (part₂-filter fA R)

    stepB≡ : ∀ R → stepB R ≡ stepB' R
    stepB≡ R = ≡-cong₂ _∷_ (≡-cong (λ z → b ∷ concat z) (part₁-filter fB R)) (part₂-filter fB R)

    -- The merge test is symmetric: either vertex merges with the other's region exactly when they
    -- are adjacent or some prior region is adjacent to both.
    merge-sym : ∀ R → fA (b ∷ concat (filterᵇ fB R)) ≡ fB (a ∷ concat (filterᵇ fA R))
    merge-sym R =
      ≡-cong₂ _∨_ sym-ab
        (≡-trans (any-concat adj-a (filterᵇ fB R))
        (≡-trans (any-filter fB fA R)
        (≡-trans (any-cong (λ C → ∧-comm (fB C) (fA C)) R)
                 (≡-sym (≡-trans (any-concat adj-b (filterᵇ fA R)) (any-filter fA fB R))))))

    -- The regions adjacent to neither vertex, left alone by both orders.
    unmerged : ∀ R → filterᵇ (λ C → Bool.not (fA C)) (filterᵇ (λ C → Bool.not (fB C)) R)
                   ≡ filterᵇ (λ C → Bool.not (fB C)) (filterᵇ (λ C → Bool.not (fA C)) R)
    unmerged R =
      ≡-trans (filter-filter (λ C → Bool.not (fB C)) (λ C → Bool.not (fA C)) R)
      (≡-trans (filter-cong (λ C → ∧-comm (Bool.not (fB C)) (Bool.not (fA C))) R)
               (≡-sym (filter-filter (λ C → Bool.not (fA C)) (λ C → Bool.not (fB C)) R)))

    step-comm' : ∀ R → stepA' (stepB' R) ↭↭ stepB' (stepA' R)
    step-comm' R with fA (b ∷ concat (filterᵇ fB R)) in eqA
                    | fB (a ∷ concat (filterᵇ fA R)) in eqB
    ... | Bool.true  | Bool.true  =
      H.prep (↭.swap a b
               (↭-trans (concat-select fB fA R)
                (↭-trans (↭-reflexive (≡-cong concat (filter-cong (λ C → ∨-comm (fB C) (fA C)) R)))
                         (↭-sym (concat-select fA fB R)))))
             (↭↭-of-≡ (unmerged R))
    ... | Bool.true  | Bool.false with ≡-trans (≡-sym eqA) (≡-trans (merge-sym R) eqB)
    ...   | ()
    step-comm' R | Bool.false | Bool.true with ≡-trans (≡-sym eqB) (≡-trans (≡-sym (merge-sym R)) eqA)
    ...   | ()
    step-comm' R | Bool.false | Bool.false =
      H.swap (↭-reflexive (≡-cong (λ z → a ∷ concat z) absorbA))
             (↭-reflexive (≡-cong (λ z → b ∷ concat z) (≡-sym absorbB)))
             (↭↭-of-≡ (unmerged R))
      where
        hAB : any (λ C → fB C Bool.∧ fA C) R ≡ Bool.false
        hAB = ≡-trans (≡-sym (≡-trans (any-concat adj-a (filterᵇ fB R)) (any-filter fB fA R)))
                      (proj₂ (∨-false (adj-a b) _ eqA))

        absorbA : filterᵇ fA (filterᵇ (λ C → Bool.not (fB C)) R) ≡ filterᵇ fA R
        absorbA = filter-absorb fB fA R hAB

        absorbB : filterᵇ fB (filterᵇ (λ C → Bool.not (fA C)) R) ≡ filterᵇ fB R
        absorbB = filter-absorb fA fB R (≡-trans (any-cong (λ C → ∧-comm (fA C) (fB C)) R) hAB)

    step-comm : ∀ R → stepA (stepB R) ↭↭ stepB (stepA R)
    step-comm R =
      H.trans (↭↭-of-≡ (≡-trans (≡-cong stepA (stepB≡ R)) (stepA≡ (stepB' R))))
      (H.trans (step-comm' R)
               (↭↭-of-≡ (≡-sym (≡-trans (≡-cong stepB (stepA≡ R)) (stepB≡ (stepA' R))))))

adjacent-sym : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
               (G : Graph D) (x y : Vertex D) → adjacent G x y ≡ adjacent G y x
adjacent-sym G x y = ∨-comm (nonzero (G x y)) (nonzero (G y x))

-- Adding two vertices in either order gives equivalent regions.
regions-swap : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
               (G : Graph D) (a b : Path D) (ws : List (Path D)) →
               regions G (a ∷ b ∷ ws) ≈ᵣ regions G (b ∷ a ∷ ws)
regions-swap G a b ws =
  Step.step-comm _ (λ q → adjacent G (at a) (at q)) (λ q → adjacent G (at b) (at q))
                 a b (adjacent-sym G (at a) (at b)) (regions G ws)

-- Order-independence of the regions computation.
regions-perm : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
               (G : Graph D) {ws ws' : List (Path D)} → ws ↭ ws' →
               regions G ws ≈ᵣ regions G ws'
regions-perm G ↭.refl       = ↭↭-refl
regions-perm G (↭.prep w p) = regions-prep G w (regions-perm G p)
regions-perm G (↭.swap {xs = ws} {ys = ws'} a b p) =
  H.trans (regions-swap G a b ws)
          (regions-prep G b {a ∷ ws} {a ∷ ws'} (regions-prep G a {ws} {ws'} (regions-perm G p)))
regions-perm G (↭.trans p q) = H.trans (regions-perm G p) (regions-perm G q)

-- A correctly summarised configuration: the visible and hidden vertices partition the first-order
-- paths, the stored regions are the regions of the hidden set, and each carries its summary.
record Summarised {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
                  (K : Config D) : Set ℓ where
  field
    partition : (K .visible ++ hidden-set K) ↭ FO D
    regioned  : map proj₁ (K .hidden) ≈ᵣ regions (fo-graph D) (hidden-set K)
    summaries : All (λ CH → ∀ x y (i : Fin (vertex-width y)) (j : Fin (vertex-width x)) →
                            proj₂ CH x y i j ≡ summary D (proj₁ CH) x y i j)
                    (K .hidden)

open Summarised public
