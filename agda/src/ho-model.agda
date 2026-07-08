{-# OPTIONS --postfix-projections --prop --safe #-}

module ho-model where

open import Level using (Level; 0ℓ; suc)
open import categories
  using (Category; HasProducts; HasTerminal; HasInitial; IsTerminal; IsInitial;
         op-coproducts→products; op-initial→terminal; HasCoproducts;
         HasStrongCoproducts; strong-coproducts→coproducts; ccc→strong-coproducts)
import polynomial-functor-2
open import cmon-enriched
  using (CMonEnriched; product-cmon-enriched; op-cmon-enriched; Biproduct; biproducts→products)
open import functor using (HasLimits; op-colimit; limits→limits'; Colimit; _∘F_; NatTrans; colambda-unique; constF)
open import categories using (setoid→category)
import fam
import fam-mu-types-2.carrier
import fam-mu-types-2
import fam-stable-indexed
import indexed-family

open import functor using (Functor)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import prop using (_,_; ∃; ∃ₛ; Prf; ⟪_⟫)
open import prop-setoid using (IsEquivalence; Setoid)
open import finite-product-functor
  using (preserve-chosen-products; preserve-chosen-terminal)
open import finite-coproduct-functor using (preserve-chosen-coproducts)

open Functor

------------------------------------------------------------------------------
-- Given a CMon-enriched category 𝒟 with limits, terminal, and
-- biproducts, a source category 𝒞 with terminal and products, and a
-- finite-product-preserving functor F : 𝒞 → 𝒟, we get an
-- interpretation in Fam⟨𝒟⟩ from a model in Fam⟨𝒞⟩.

open import fam-functor using (FamF)
open import signature
import lists
import language-syntax

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
  -- For the conservativity theorem: F is faithful and picks definability
  -- witnesses uniformly (both hold when F is full and faithful)
  (F-faithful : ∀ {a b} {g₁ g₂ : Category._⇒_ 𝒞 a b} → Category._≈_ 𝒟 (F .fmor g₁) (F .fmor g₂) → Category._≈_ 𝒞 g₁ g₂)
  (F-def : ∀ {a b} (h : Category._⇒_ 𝒟 (F .fobj a) (F .fobj b)) →
           Prf (∃ (Category._⇒_ 𝒞 a b) λ g → Category._≈_ 𝒟 (F .fmor g) h) →
           ∃ₛ (Category._⇒_ 𝒞 a b) λ g → Category._≈_ 𝒟 (F .fmor g) h)
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
     open language-syntax Sig using (_⊢_)
     open indexed-family._⇒f_ using (transf)
     open Setoid using (Carrier)

     open import language-interpretation Sig
       Fam⟨𝒟⟩.cat
       Fam⟨𝒟⟩-terminal
       Fam⟨𝒟⟩-products
       Fam⟨𝒟⟩-coproducts
       Fam⟨𝒟⟩-exponentials
       Fam⟨𝒟⟩-lists
       (transport-model Sig Fam⟨F⟩ Fam⟨F⟩-preserves-terminal Fam⟨F⟩-preserves-products Fam⟨F⟩-preserves-bool Impl)
       public

     -- The fibre map of a term at a given environment.
     mor : ∀ {Γ τ} (M : Γ ⊢ τ) (env : ⟦ Γ ⟧ctxt .idx .Carrier) → _
     mor M env = ⟦ M ⟧tm .famf .transf env

  -- Direct interpretation of the language with general recursive types, via the
  -- W-type μ-instance for Fam together with its initial-algebra laws.
  Fam⟨𝒟⟩-strongCoproducts =
    Fam⟨𝒟⟩.products.strongCoproducts (biproducts→products _ 𝒟-biproducts)

  module Fam⟨𝒟⟩-μ =
    fam-mu-types-2.carrier 0ℓ 0ℓ 𝒟-terminal (biproducts→products _ 𝒟-biproducts)

  Fam⟨𝒟⟩-hasMu =
    fam-mu-types-2.hasMu 0ℓ 0ℓ 𝒟-terminal (biproducts→products _ 𝒟-biproducts)

  Fam⟨𝒟⟩-hasMuLaws =
    fam-mu-types-2.hasMuLaws 0ℓ 0ℓ 𝒟-terminal (biproducts→products _ 𝒟-biproducts)

  module interp-2 (Sig : Signature 0ℓ)
                  (Impl : Model PFPC[ Fam⟨𝒞⟩.cat , Fam⟨𝒞⟩-terminal , Fam⟨𝒞⟩-products , Fam⟨𝒞⟩-bool ] Sig)
     where

     open Fam⟨𝒟⟩.Mor public
     open Fam⟨𝒟⟩.Obj public

     open import language-interpretation-2 Sig
       Fam⟨𝒟⟩.cat
       Fam⟨𝒟⟩-terminal
       Fam⟨𝒟⟩-products
       Fam⟨𝒟⟩-strongCoproducts
       Fam⟨𝒟⟩-exponentials
       Fam⟨𝒟⟩-hasMu
       (transport-model Sig Fam⟨F⟩ Fam⟨F⟩-preserves-terminal Fam⟨F⟩-preserves-products Fam⟨F⟩-preserves-bool Impl)
       public

  module Conservativity where
    open import monad using (IdentityMonad; preserve-identity-monad; Identity-monad-preserve-coproducts)

    𝒞istable = fam-stable-indexed.fam-stable-indexed {os = 0ℓ} 𝒞

    open import conservativity
      Fam⟨𝒞⟩.cat Fam⟨𝒞⟩-terminal Fam⟨𝒞⟩-products Fam⟨𝒞⟩-coproducts Fam⟨𝒞⟩.fam-stable (IdentityMonad Fam⟨𝒞⟩.cat)
      Fam⟨𝒞⟩.bigCoproducts 𝒞istable
      Fam⟨𝒟⟩.cat Fam⟨𝒟⟩-terminal Fam⟨𝒟⟩-products Fam⟨𝒟⟩-coproducts Fam⟨𝒟⟩-exponentials (IdentityMonad Fam⟨𝒟⟩.cat) Fam⟨𝒟⟩.bigCoproducts
      Fam⟨F⟩ Fam⟨F⟩-preserves-terminal Fam⟨F⟩-preserves-products Fam⟨F⟩-preserves-coproducts
      (preserve-identity-monad Fam⟨F⟩) (Identity-monad-preserve-coproducts Fam⟨𝒞⟩-coproducts)
      {!FM-DC!} {!F-DC!} {!FamF-faithful!} {!FamF-def!}
      public

    Fam⟨𝒞⟩-strongCoproducts : HasStrongCoproducts Fam⟨𝒞⟩.cat Fam⟨𝒞⟩-products
    Fam⟨𝒞⟩-strongCoproducts = Fam⟨𝒞⟩.products.strongCoproducts 𝒞-products

    Fam⟨𝒞⟩-hasMu : polynomial-functor-2.Interp.HasMu Fam⟨𝒞⟩-terminal Fam⟨𝒞⟩-products Fam⟨𝒞⟩-strongCoproducts
    Fam⟨𝒞⟩-hasMu = fam-mu-types-2.hasMu 0ℓ 0ℓ 𝒞-terminal 𝒞-products

    -- The embedding preserves the coproducts derived from the strong coproducts
    -- on either side: the canonical maps differ from those for the chosen
    -- coproducts only in the copairing, which is unique.
    GF-preserve-strong-coproducts :
      preserve-chosen-coproducts GF
        (strong-coproducts→coproducts Fam⟨𝒞⟩-terminal Fam⟨𝒞⟩-strongCoproducts)
        (strong-coproducts→coproducts GlPE.terminal (ccc→strong-coproducts GlCP.coproducts GlPE.exponentials))
    GF-preserve-strong-coproducts {x} {y} =
      Glued.IsIso-cong (Glued.≈-sym map'≈map) GF-preserve-coproducts
      where
        module CP' = HasCoproducts
          (strong-coproducts→coproducts GlPE.terminal (ccc→strong-coproducts GlCP.coproducts GlPE.exponentials))
        module CPC = HasCoproducts Fam⟨𝒞⟩-coproducts

        map' = CP'.copair (GF .fmor (CPC.in₁ {x} {y})) (GF .fmor (CPC.in₂ {x} {y}))

        map'≈map : map' Glued.≈ GlCPM.copair (GF .fmor (CPC.in₁ {x} {y})) (GF .fmor (CPC.in₂ {x} {y}))
        map'≈map =
          Glued.≈-trans (Glued.≈-sym (GlCPM.copair-ext map'))
            (GlCPM.copair-cong (CP'.copair-in₁ _ _) (CP'.copair-in₂ _ _))
