{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.Bool as Bool using (Bool; _∨_)
open import Data.Bool.ListAction using (any)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; map)
import Data.List.Relation.Binary.Permutation.Propositional as ↭
open ↭ using (_↭_)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (map⁺)
open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (refl to ≡-refl; trans to ≡-trans; cong to ≡-cong; cong₂ to ≡-cong₂)
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
