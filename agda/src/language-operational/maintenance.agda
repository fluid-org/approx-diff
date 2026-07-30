{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.Bool as Bool using (Bool; _∨_)
open import Data.Bool.ListAction using (any)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map; concat; partitionᵇ)
open import Data.List.Properties using (++-assoc)
import Data.List.Relation.Binary.Permutation.Homogeneous as H
import Data.List.Relation.Binary.Permutation.Propositional as ↭
open ↭ using (_↭_; ↭-refl; ↭-trans; ↭-reflexive)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (map⁺; ++⁺; ++-comm)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; cong to ≡-cong; cong₂ to ≡-cong₂)
open import signature using (Signature)
open import primitives using (Primitives)
import matrix
import two

-- Groundwork for the maintenance theorem: the moves preserve the invariant that each hidden pair
-- is a region of the hidden set with its summary. Here: summaries are stable under permutation of
-- the region.
module language-operational.maintenance {ℓ} (Sig : Signature ℓ) (𝒫 : Primitives two.semiring Sig) where

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

private
  ∨-swap : ∀ a b c → (a ∨ (b ∨ c)) ≡ (b ∨ (a ∨ c))
  ∨-swap Bool.false b c = ≡-refl
  ∨-swap Bool.true Bool.false c = ≡-refl
  ∨-swap Bool.true Bool.true c = ≡-refl

  any-perm : ∀ {a} {A : Set a} (f : A → Bool) {rs rs' : List A} →
             rs ↭ rs' → any f rs ≡ any f rs'
  any-perm f ↭.refl = ≡-refl
  any-perm f (↭.prep r p) = ≡-cong (f r ∨_) (any-perm f p)
  any-perm f (↭.swap a b p) =
    ≡-trans (≡-cong (λ z → f a ∨ (f b ∨ z)) (any-perm f p)) (∨-swap (f a) (f b) _)
  any-perm f (↭.trans p q) = ≡-trans (any-perm f p) (any-perm f q)

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
_≈ᵣ_ = H.Permutation _↭_

private
  ++-swap : ∀ {a} {A : Set a} (xs ys zs : List A) → xs ++ (ys ++ zs) ↭ ys ++ (xs ++ zs)
  ++-swap xs ys zs =
    ↭-trans (↭-reflexive (≡-sym (++-assoc xs ys zs)))
            (↭-trans (++⁺ (++-comm xs ys) ↭-refl) (↭-reflexive (++-assoc ys xs zs)))

  concat-resp : ∀ {a} {A : Set a} {rss rss' : List (List A)} →
                H.Permutation _↭_ rss rss' → concat rss ↭ concat rss'
  concat-resp (H.refl [])       = ↭-refl
  concat-resp (H.refl (r ∷ pw)) = ++⁺ r (concat-resp (H.refl pw))
  concat-resp (H.prep r p)      = ++⁺ r (concat-resp p)
  concat-resp (H.swap {ys = ys} {x′ = x′} {y′ = y′} r₁ r₂ p) =
    ↭-trans (++⁺ r₁ (++⁺ r₂ (concat-resp p))) (++-swap x′ y′ (concat ys))
  concat-resp (H.trans p q)     = ↭-trans (concat-resp p) (concat-resp q)

  partition-resp : ∀ {a r} {A : Set a} {S : A → A → Set r} (f : A → Bool) →
                   (∀ {x y} → S x y → f x ≡ f y) →
                   ∀ {rs rs'} → H.Permutation S rs rs' →
                   H.Permutation S (proj₁ (partitionᵇ f rs)) (proj₁ (partitionᵇ f rs'))
                   × H.Permutation S (proj₂ (partitionᵇ f rs)) (proj₂ (partitionᵇ f rs'))
  partition-resp f resp (H.refl []) = H.refl [] , H.refl []
  partition-resp f resp (H.refl (_∷_ {x} {y} s pw)) with partition-resp f resp (H.refl pw)
  ... | (p₁ , p₂) with f x | f y | resp s
  ...   | Bool.true  | _ | ≡-refl = H.prep s p₁ , p₂
  ...   | Bool.false | _ | ≡-refl = p₁ , H.prep s p₂
  partition-resp f resp (H.prep {x = x} {y} s p) with partition-resp f resp p
  ... | (p₁ , p₂) with f x | f y | resp s
  ...   | Bool.true  | _ | ≡-refl = H.prep s p₁ , p₂
  ...   | Bool.false | _ | ≡-refl = p₁ , H.prep s p₂
  partition-resp f resp (H.swap {x = x} {y} {x′} {y′} s₁ s₂ p) with partition-resp f resp p
  ... | (p₁ , p₂) with f x | f x′ | resp s₁ | f y | f y′ | resp s₂
  ...   | Bool.true  | _ | ≡-refl | Bool.true  | _ | ≡-refl = H.swap s₁ s₂ p₁ , p₂
  ...   | Bool.true  | _ | ≡-refl | Bool.false | _ | ≡-refl = H.prep s₁ p₁ , H.prep s₂ p₂
  ...   | Bool.false | _ | ≡-refl | Bool.true  | _ | ≡-refl = H.prep s₂ p₁ , H.prep s₁ p₂
  ...   | Bool.false | _ | ≡-refl | Bool.false | _ | ≡-refl = p₁ , H.swap s₁ s₂ p₂
  partition-resp f resp (H.trans p q) with partition-resp f resp p | partition-resp f resp q
  ... | (p₁ , p₂) | (q₁ , q₂) = H.trans p₁ q₁ , H.trans p₂ q₂

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
