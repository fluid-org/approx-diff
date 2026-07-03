{-# OPTIONS --postfix-projections --prop --safe #-}

-- The Galois-connection model: Fam(galois.cat) interpreted in Fam(M×Jop).
module ho-model-galois where

open import Level using (0ℓ; suc)
open import categories using (Category; HasTerminal; HasProducts; HasInitial; IsTerminal; IsInitial; HasCoproducts; op-coproducts→products; op-initial→terminal)
open import product-category using (product; product-limit; product-products; product-terminal)
open import functor using (Functor; HasLimits; op-colimit)
open import cmon-enriched using (CMonEnriched; product-cmon-enriched; op-cmon-enriched; Biproduct; biproducts→products)
open import finite-product-functor using (preserve-chosen-products; preserve-chosen-terminal)
open import prop-setoid using (IsEquivalence)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import ho-model
open Category using (opposite)

import galois
import preorder
import meet-semilattice
import join-semilattice
import meet-semilattice-category
import join-semilattice-category
open import prop using (tt; _,_; proj₁; proj₂)
open meet-semilattice-category._⇒_
open join-semilattice-category._⇒_
open meet-semilattice-category._≃m_
open join-semilattice-category._≃m_
open meet-semilattice._≃m_
open join-semilattice._≃m_
open preorder._≃m_
open galois.Obj
open Functor

------------------------------------------------------------------------------
-- The target category Meet × Join^op.

M×Jop : Category (suc 0ℓ) 0ℓ 0ℓ
M×Jop = product meet-semilattice-category.cat (opposite join-semilattice-category.cat)

private
  module M×Jop = Category M×Jop

M×Jop-cmon-enriched : CMonEnriched M×Jop
M×Jop-cmon-enriched =
  product-cmon-enriched
    meet-semilattice-category.cmon-enriched
    (op-cmon-enriched join-semilattice-category.cmon-enriched)

M×Jop-limits : ∀ (𝒮 : Category 0ℓ 0ℓ 0ℓ) → HasLimits 𝒮 M×Jop
M×Jop-limits 𝒮 D =
  product-limit 𝒮 D
    (meet-semilattice-category.limits 𝒮 _)
    (op-colimit _ (join-semilattice-category.colimits (opposite 𝒮) _))

-- The products and terminal object are made "by hand" so the representations used for programs are nice.
M×Jop-terminal : HasTerminal M×Jop
M×Jop-terminal =
  product-terminal meet-semilattice-category.terminal
                   (op-initial→terminal join-semilattice-category.initial)

M×Jop-biproducts : ∀ x y → Biproduct M×Jop-cmon-enriched x y
M×Jop-biproducts =
  cmon-enriched.cmon+products→biproducts M×Jop-cmon-enriched
    (product-products
      meet-semilattice-category.products
      (op-coproducts→products join-semilattice-category.coproducts))

M×Jop-products : HasProducts M×Jop
M×Jop-products = biproducts→products _ M×Jop-biproducts

𝓕 : Functor galois.cat M×Jop
𝓕 .fobj X .proj₁ = record { carrier = X .galois.Obj.carrier ; meets = X .galois.Obj.meets }
𝓕 .fobj X .proj₂ = record { carrier = X .galois.Obj.carrier ; joins = X .galois.Obj.joins }
𝓕 .fmor f .proj₁ .*→* = galois._⇒g_.right-∧ f
𝓕 .fmor f .proj₂ .*→* = galois._⇒g_.left-∨ f
𝓕 .fmor-cong f≃g .proj₁ .f≃f .eqfunc = f≃g .galois._≃g_.right-eq
𝓕 .fmor-cong f≃g .proj₂ .f≃f .eqfunc = galois._≃g_.left-eq f≃g
𝓕 .fmor-id .proj₁ .f≃f .eqfunc = preorder.≃m-isEquivalence .IsEquivalence.refl
𝓕 .fmor-id .proj₂ .f≃f .eqfunc = preorder.≃m-isEquivalence .IsEquivalence.refl
𝓕 .fmor-comp f g .proj₁ .f≃f .eqfunc = preorder.≃m-isEquivalence .IsEquivalence.refl
𝓕 .fmor-comp f g .proj₂ .f≃f .eqfunc = preorder.≃m-isEquivalence .IsEquivalence.refl

private
  module M×Jop' = Category M×Jop

open M×Jop'.IsIso

𝓕-preserve-terminal : preserve-chosen-terminal 𝓕 galois.terminal M×Jop-terminal
𝓕-preserve-terminal .inverse .proj₁ .*→* = meet-semilattice.terminal
𝓕-preserve-terminal .inverse .proj₂ .*→* = join-semilattice.initial
𝓕-preserve-terminal .f∘inverse≈id =
  HasTerminal.to-terminal-unique M×Jop-terminal _ _
𝓕-preserve-terminal .inverse∘f≈id .proj₁ .f≃f .eqfunc .eqfun x = tt , tt
𝓕-preserve-terminal .inverse∘f≈id .proj₂ .f≃f .eqfunc .eqfun x = tt , tt

𝓕-preserve-products : preserve-chosen-products 𝓕 galois.products (biproducts→products _ M×Jop-biproducts)
𝓕-preserve-products .inverse .proj₁ .*→* = meet-semilattice.id
𝓕-preserve-products .inverse .proj₂ .*→* = join-semilattice.id
𝓕-preserve-products {X} {Y} .f∘inverse≈id .proj₁ .f≃f .eqfunc .eqfun (x , y) =
  (X .π₁ , Y .π₂) ,
  (X .⟨_∧_⟩ (X .≤-refl) (X .≤-top) , Y .⟨_∧_⟩ (Y .≤-top) (Y .≤-refl))
𝓕-preserve-products {X} {Y} .f∘inverse≈id .proj₂ .f≃f .eqfunc .eqfun (x , y) =
  (X .[_∨_] (X .[_∨_] (X .≤-refl) (X .≤-bottom)) (X .≤-bottom) ,
   Y .[_∨_] (Y .≤-bottom) (Y .[_∨_] (Y .≤-bottom) (Y .≤-refl))) ,
  (X .≤-trans (X .inl) (X .inl) , Y .≤-trans (Y .inr) (Y .inr))
𝓕-preserve-products {X} {Y} .inverse∘f≈id .proj₁ .f≃f .eqfunc .eqfun (x , y) =
  (X .π₁ , Y .π₂) ,
  (X .⟨_∧_⟩ (X .≤-refl) (X .≤-top) , Y .⟨_∧_⟩ (Y .≤-top) (Y .≤-refl))
𝓕-preserve-products {X} {Y} .inverse∘f≈id .proj₂ .f≃f .eqfunc .eqfun (x , y) =
  (X .[_∨_] (X .[_∨_] (X .≤-refl) (X .≤-bottom)) (X .≤-bottom) ,
   Y .[_∨_] (Y .≤-bottom) (Y .[_∨_] (Y .≤-bottom) (Y .≤-refl))) ,
  (X .≤-trans (X .inl) (X .inl) , Y .≤-trans (Y .inr) (Y .inr))

open Interpretation
  galois.cat galois.terminal galois.products
  M×Jop M×Jop-cmon-enriched M×Jop-limits M×Jop-terminal M×Jop-biproducts
  𝓕 𝓕-preserve-terminal (λ {X} {Y} → 𝓕-preserve-products {X} {Y})
  public
