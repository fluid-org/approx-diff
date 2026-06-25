{-# OPTIONS --postfix-projections --prop --safe #-}

-- The conjugate-pair model: Fam(conjugate.cat) interpreted in Fam(J×Jop).
module ho-model-conjugate where

open import Level using (0ℓ)
open import categories using (Category; HasTerminal; HasProducts)
open import functor using (Functor)
open import cmon-enriched using (biproducts→products)
open import finite-product-functor using (preserve-chosen-products; preserve-chosen-terminal)
open import prop-setoid using (IsEquivalence)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import ho-model

import preorder
import join-semilattice
import join-semilattice-category
import conjugate
open import prop using (tt; _,_; proj₁; proj₂)
open join-semilattice-category._⇒_
open join-semilattice-category._≃m_
open join-semilattice._≃m_
open preorder._≃m_
open conjugate.Obj
open Functor

𝓕 : Functor conjugate.cat J×Jop
𝓕 .fobj X .proj₁ = record { carrier = X .conjugate.Obj.carrier ; joins = X .conjugate.Obj.joins }
𝓕 .fobj X .proj₂ = record { carrier = X .conjugate.Obj.carrier ; joins = X .conjugate.Obj.joins }
𝓕 .fmor f .proj₁ .*→* = conjugate._⇒c_.right f
𝓕 .fmor f .proj₂ .*→* = conjugate._⇒c_.left f
𝓕 .fmor-cong f≃g .proj₁ .f≃f = f≃g .conjugate._≃c_.right-eq
𝓕 .fmor-cong f≃g .proj₂ .f≃f = f≃g .conjugate._≃c_.left-eq
𝓕 .fmor-id .proj₁ .f≃f .eqfunc = preorder.≃m-isEquivalence .IsEquivalence.refl
𝓕 .fmor-id .proj₂ .f≃f .eqfunc = preorder.≃m-isEquivalence .IsEquivalence.refl
𝓕 .fmor-comp f g .proj₁ .f≃f .eqfunc = preorder.≃m-isEquivalence .IsEquivalence.refl
𝓕 .fmor-comp f g .proj₂ .f≃f .eqfunc = preorder.≃m-isEquivalence .IsEquivalence.refl

private
  module J×Jop' = Category J×Jop

open J×Jop'.IsIso

𝓕-preserve-terminal : preserve-chosen-terminal 𝓕 conjugate.terminal J×Jop-terminal
𝓕-preserve-terminal .inverse .proj₁ .*→* = join-semilattice.terminal
𝓕-preserve-terminal .inverse .proj₂ .*→* = join-semilattice.initial
𝓕-preserve-terminal .f∘inverse≈id =
  HasTerminal.to-terminal-unique J×Jop-terminal _ _
𝓕-preserve-terminal .inverse∘f≈id .proj₁ .f≃f .eqfunc .eqfun x = tt , tt
𝓕-preserve-terminal .inverse∘f≈id .proj₂ .f≃f .eqfunc .eqfun x = tt , tt

𝓕-preserve-products : preserve-chosen-products 𝓕 conjugate.products (biproducts→products _ J×Jop-biproducts)
𝓕-preserve-products .inverse .proj₁ .*→* = join-semilattice.id
𝓕-preserve-products .inverse .proj₂ .*→* = join-semilattice.id
𝓕-preserve-products {X} {Y} .f∘inverse≈id .proj₁ .f≃f .eqfunc .eqfun (x , y) =
  (X .[_∨_] (X .≤-refl) (X .≤-bottom) , Y .[_∨_] (Y .≤-bottom) (Y .≤-refl)) ,
  (X .inl , Y .inr)
𝓕-preserve-products {X} {Y} .f∘inverse≈id .proj₂ .f≃f .eqfunc .eqfun (x , y) =
  (X .[_∨_] (X .[_∨_] (X .≤-refl) (X .≤-bottom)) (X .≤-bottom) ,
   Y .[_∨_] (Y .≤-bottom) (Y .[_∨_] (Y .≤-bottom) (Y .≤-refl))) ,
  (X .≤-trans (X .inl) (X .inl) , Y .≤-trans (Y .inr) (Y .inr))
𝓕-preserve-products {X} {Y} .inverse∘f≈id .proj₁ .f≃f .eqfunc .eqfun (x , y) =
  (X .[_∨_] (X .≤-refl) (X .≤-bottom) , Y .[_∨_] (Y .≤-bottom) (Y .≤-refl)) ,
  (X .inl , Y .inr)
𝓕-preserve-products {X} {Y} .inverse∘f≈id .proj₂ .f≃f .eqfunc .eqfun (x , y) =
  (X .[_∨_] (X .[_∨_] (X .≤-refl) (X .≤-bottom)) (X .≤-bottom) ,
   Y .[_∨_] (Y .≤-bottom) (Y .[_∨_] (Y .≤-bottom) (Y .≤-refl))) ,
  (X .≤-trans (X .inl) (X .inl) , Y .≤-trans (Y .inr) (Y .inr))

open Interpretation
  conjugate.cat conjugate.terminal conjugate.products
  J×Jop J×Jop-cmon-enriched J×Jop-limits J×Jop-terminal J×Jop-biproducts
  𝓕 𝓕-preserve-terminal (λ {X} {Y} → 𝓕-preserve-products {X} {Y})
  public
