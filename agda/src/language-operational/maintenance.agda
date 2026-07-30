{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.Bool as Bool using (Bool)
open import Data.Bool.ListAction using (any)
open import Data.List using (List; []; _∷_; map; concat; partitionᵇ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
import Data.List.Relation.Binary.Permutation.Homogeneous as H
import Data.List.Relation.Binary.Permutation.Propositional as ↭
open ↭ using (_↭_)
open import Relation.Binary.PropositionalEquality using (_≡_)
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

merge-region-resp : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
                    (G : Graph D) (w : Path D) {rss rss' : List (List (Path D))} →
                    rss ↭↭ rss' → merge-region G w rss ↭↭ merge-region G w rss'
merge-region-resp G w {rss} {rss'} p =
  H.prep (↭.prep w (concat-resp (proj₁ tp-p))) (proj₂ tp-p)
  where
  tp-p = partition-permᴿ (any (λ q → adjacent G (at w) (at q)))
                         (λ {C} {C'} pc → any-perm (λ q → adjacent G (at w) (at q)) pc)
                         p
