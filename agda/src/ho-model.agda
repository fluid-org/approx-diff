{-# OPTIONS --postfix-projections --prop --safe #-}

module ho-model where

open import Level using (Level; 0ℓ; suc)
open import categories using (Category; HasProducts; HasTerminal; HasInitial; IsTerminal; IsInitial; op-coproducts→products; op-initial→terminal; HasCoproducts)
open import product-category using (product; product-limit; product-products; product-terminal)
open import cmon-enriched
  using (CMonEnriched; product-cmon-enriched; op-cmon-enriched; Biproduct; biproducts→products)
open import functor using (HasLimits; op-colimit; limits→limits')
import meet-semilattice-category
import join-semilattice-category
import fam
import indexed-family
open Category using (opposite)

------------------------------------------------------------------------------
-- Construct Meet × Join^op

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
  product-limit _ _ 𝒮 D
    (meet-semilattice-category.limits 𝒮 _)
    (op-colimit _ (join-semilattice-category.colimits (opposite 𝒮) _))

-- We make the products and terminal object "by hand" so that the
-- representations used for programs are nice.

M×Jop-terminal : HasTerminal M×Jop
M×Jop-terminal =
  product-terminal _ _ meet-semilattice-category.terminal
                       (op-initial→terminal join-semilattice-category.initial)

M×Jop-biproducts : ∀ x y → cmon-enriched.Biproduct M×Jop-cmon-enriched x y
M×Jop-biproducts =
  cmon-enriched.cmon+products→biproducts M×Jop-cmon-enriched
    (product-products _ _
      meet-semilattice-category.products
      (op-coproducts→products join-semilattice-category.coproducts))

M×Jop-products : HasProducts M×Jop
M×Jop-products = biproducts→products _ M×Jop-biproducts

------------------------------------------------------------------------------
-- Construct Join × Join^op

J×Jop : Category (suc 0ℓ) 0ℓ 0ℓ
J×Jop = product join-semilattice-category.cat (opposite join-semilattice-category.cat)

J×Jop-cmon-enriched : CMonEnriched J×Jop
J×Jop-cmon-enriched =
  product-cmon-enriched
    join-semilattice-category.cmon-enriched
    (op-cmon-enriched join-semilattice-category.cmon-enriched)

J×Jop-limits : ∀ (𝒮 : Category 0ℓ 0ℓ 0ℓ) → HasLimits 𝒮 J×Jop
J×Jop-limits 𝒮 D =
  product-limit _ _ 𝒮 D
    (join-semilattice-category.limits 𝒮 _)
    (op-colimit _ (join-semilattice-category.colimits (opposite 𝒮) _))

J×Jop-terminal : HasTerminal J×Jop
J×Jop-terminal =
  product-terminal _ _ join-semilattice-category.terminal
                       (op-initial→terminal join-semilattice-category.initial)

J×Jop-biproducts : ∀ x y → cmon-enriched.Biproduct J×Jop-cmon-enriched x y
J×Jop-biproducts =
  cmon-enriched.cmon+products→biproducts J×Jop-cmon-enriched
    (product-products _ _
      join-semilattice-category.products
      (op-coproducts→products join-semilattice-category.coproducts))

J×Jop-products : HasProducts J×Jop
J×Jop-products = biproducts→products _ J×Jop-biproducts

open import functor using (Functor)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import prop using (_,_)
open import prop-setoid using (IsEquivalence)
open import finite-product-functor
  using (preserve-chosen-products; preserve-chosen-terminal)

open Functor

------------------------------------------------------------------------------
-- Given a CMon-enriched category 𝒟 with limits, terminal, and
-- biproducts, a source category 𝒞 with terminal and products, and a
-- finite-product-preserving functor F : 𝒞 → 𝒟, we get an
-- interpretation in Fam⟨𝒟⟩ from a model in Fam⟨𝒞⟩.

open import fam-functor using (FamF)
open import signature
import lists

module Interpretation
  {o : Level}
  (𝒞 : Category o 0ℓ 0ℓ)
  (𝒞-terminal : HasTerminal 𝒞)
  (𝒞-products : HasProducts 𝒞)
  (𝒟 : Category (suc 0ℓ) 0ℓ 0ℓ)
  (𝒟-cmon : CMonEnriched 𝒟)
  (𝒟-limits : ∀ (𝒮 : Category 0ℓ 0ℓ 0ℓ) → HasLimits 𝒮 𝒟)
  (𝒟-terminal : HasTerminal 𝒟)
  (𝒟-biproducts : ∀ x y → Biproduct 𝒟-cmon x y)
  (F : Functor 𝒞 𝒟)
  (F-preserve-terminal : preserve-chosen-terminal F 𝒞-terminal 𝒟-terminal)
  (F-preserve-products : preserve-chosen-products F 𝒞-products (biproducts→products _ 𝒟-biproducts))
  where

  -- Target: Fam⟨𝒟⟩
  module Fam⟨𝒟⟩ = fam.CategoryOfFamilies 0ℓ 0ℓ 𝒟

  Fam⟨𝒟⟩-terminal : HasTerminal Fam⟨𝒟⟩.cat
  Fam⟨𝒟⟩-terminal = Fam⟨𝒟⟩.terminal 𝒟-terminal

  Fam⟨𝒟⟩-coproducts = Fam⟨𝒟⟩.coproducts

  open import fam-exponentials 0ℓ 0ℓ
    𝒟 𝒟-cmon 𝒟-biproducts
    (indexed-family.hasSetoidProducts 0ℓ 0ℓ 𝒟 λ A → limits→limits' (𝒟-limits _))
    renaming ( exponentials to Fam⟨𝒟⟩-exponentials
             ; products     to Fam⟨𝒟⟩-products
             )
    using ()
    public

  Fam⟨𝒟⟩-lists = lists.lists Fam⟨𝒟⟩.cat Fam⟨𝒟⟩-terminal Fam⟨𝒟⟩-products Fam⟨𝒟⟩-exponentials Fam⟨𝒟⟩.bigCoproducts

  Fam⟨𝒟⟩-bool =
    Fam⟨𝒟⟩-coproducts .HasCoproducts.coprod
      (Fam⟨𝒟⟩-terminal .HasTerminal.witness)
      (Fam⟨𝒟⟩-terminal .HasTerminal.witness)

  -- Source: Fam⟨𝒞⟩
  module Fam⟨𝒞⟩ = fam.CategoryOfFamilies 0ℓ 0ℓ 𝒞

  Fam⟨𝒞⟩-terminal = Fam⟨𝒞⟩.terminal 𝒞-terminal
  Fam⟨𝒞⟩-products = Fam⟨𝒞⟩.products.products 𝒞-products
  Fam⟨𝒞⟩-coproducts = Fam⟨𝒞⟩.coproducts

  Fam⟨𝒞⟩-bool =
    Fam⟨𝒞⟩-coproducts .HasCoproducts.coprod
      (Fam⟨𝒞⟩-terminal .HasTerminal.witness)
      (Fam⟨𝒞⟩-terminal .HasTerminal.witness)

  -- Lifted functor Fam⟨F⟩ : Fam⟨𝒞⟩ → Fam⟨𝒟⟩
  Fam⟨F⟩ : Functor Fam⟨𝒞⟩.cat Fam⟨𝒟⟩.cat
  Fam⟨F⟩ = FamF 0ℓ 0ℓ F

  Fam⟨F⟩-preserves-products =
    fam-functor.preserve-products 0ℓ 0ℓ F 𝒞-products (biproducts→products _ 𝒟-biproducts)
      (λ {X} {Y} → F-preserve-products {X} {Y})

  Fam⟨F⟩-preserves-coproducts =
    fam-functor.preserve-coproducts 0ℓ 0ℓ F

  Fam⟨F⟩-preserves-terminal =
    fam-functor.preserve-terminal 0ℓ 0ℓ F 𝒞-terminal 𝒟-terminal F-preserve-terminal

  Fam⟨F⟩-preserves-bool : Fam⟨𝒟⟩.Mor (Fam⟨F⟩ .fobj Fam⟨𝒞⟩-bool) Fam⟨𝒟⟩-bool
  Fam⟨F⟩-preserves-bool =
    Fam⟨𝒟⟩.Mor-∘ (HasCoproducts.coprod-m Fam⟨𝒟⟩-coproducts (Fam⟨𝒟⟩-terminal .HasTerminal.to-terminal) (Fam⟨𝒟⟩-terminal .HasTerminal.to-terminal))
                  (Fam⟨F⟩-preserves-coproducts .Category.IsIso.inverse)

  -- Interpretation
  module interp (Sig : Signature 0ℓ)
                (Impl : Model PFPC[ Fam⟨𝒞⟩.cat , Fam⟨𝒞⟩-terminal , Fam⟨𝒞⟩-products , Fam⟨𝒞⟩-bool ] Sig)
     where

     open Fam⟨𝒟⟩.Mor public
     open Fam⟨𝒟⟩.Obj public

     open import language-interpretation Sig
       Fam⟨𝒟⟩.cat
       Fam⟨𝒟⟩-terminal
       Fam⟨𝒟⟩-products
       Fam⟨𝒟⟩-coproducts
       Fam⟨𝒟⟩-exponentials
       Fam⟨𝒟⟩-lists
       (transport-model Sig Fam⟨F⟩ Fam⟨F⟩-preserves-terminal Fam⟨F⟩-preserves-products Fam⟨F⟩-preserves-bool Impl)
       public

------------------------------------------------------------------------------
-- Conservativity instance for the (𝒞, 𝒟, F) context.

module Conservativity
  (𝒞 : Category 0ℓ 0ℓ 0ℓ)
  (𝒞-terminal : HasTerminal 𝒞)
  (𝒞-products : HasProducts 𝒞)
  (𝒟 : Category (suc 0ℓ) 0ℓ 0ℓ)
  (𝒟-cmon : CMonEnriched 𝒟)
  (𝒟-limits : ∀ (𝒮 : Category 0ℓ 0ℓ 0ℓ) → HasLimits 𝒮 𝒟)
  (𝒟-terminal : HasTerminal 𝒟)
  (𝒟-biproducts : ∀ x y → Biproduct 𝒟-cmon x y)
  (F : Functor 𝒞 𝒟)
  (F-preserve-terminal : preserve-chosen-terminal F 𝒞-terminal 𝒟-terminal)
  (F-preserve-products : preserve-chosen-products F 𝒞-products (biproducts→products _ 𝒟-biproducts))
  where

  open Interpretation 𝒞 𝒞-terminal 𝒞-products 𝒟 𝒟-cmon 𝒟-limits 𝒟-terminal 𝒟-biproducts F F-preserve-terminal F-preserve-products

  open import conservativity
    Fam⟨𝒞⟩.cat Fam⟨𝒞⟩-terminal Fam⟨𝒞⟩-products Fam⟨𝒞⟩-coproducts Fam⟨𝒞⟩.fam-stable
    Fam⟨𝒟⟩.cat Fam⟨𝒟⟩-terminal Fam⟨𝒟⟩-products Fam⟨𝒟⟩-coproducts Fam⟨𝒟⟩-exponentials Fam⟨𝒟⟩.bigCoproducts
    Fam⟨F⟩ Fam⟨F⟩-preserves-terminal Fam⟨F⟩-preserves-products Fam⟨F⟩-preserves-coproducts
    public
