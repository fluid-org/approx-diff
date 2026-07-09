{-# OPTIONS --postfix-projections --prop --safe #-}

module ho-model where

open import Level using (Level; 0ℓ; suc)
open import categories
  using (Category; HasProducts; HasTerminal; HasInitial; IsTerminal; IsInitial;
         op-coproducts→products; op-initial→terminal; HasCoproducts;
         HasStrongCoproducts; strong-coproducts→coproducts; ccc→strong-coproducts;
         coproducts-canonical-iso)
import polynomial-functor-2
open import cmon-enriched
  using (CMonEnriched; product-cmon-enriched; op-cmon-enriched; Biproduct; biproducts→products)
open import functor using (HasLimits; op-colimit; limits→limits'; Colimit; _∘F_; NatTrans; colambda-unique; constF; functor-preserve-iso)
open import categories using (setoid→category)
import fam
import finite-coproducts-from-indexed
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
    open import monad using (Monad; IdentityMonad; preserve-identity-monad)
    open import functor using (Id; Colimit; _∘F_; NatTrans)
    open import prop using (∃ₛ)
    open fam.CategoryOfFamilies.Obj
    open fam.CategoryOfFamilies.Mor
    open fam.CategoryOfFamilies._≃_
    open indexed-family._⇒f_
    open indexed-family._≃f_
    open indexed-family.Fam
    open prop-setoid._⇒_
    open prop-setoid._≃m_
    private module 𝒞C = Category 𝒞

    𝒞istable = fam-stable-indexed.fam-stable-indexed {os = 0ℓ} 𝒞

    private M = Monad.funct (IdentityMonad Fam⟨𝒞⟩.cat)

    -- The identity monad functor preserves set-indexed coproducts: Id ∘F D and
    -- D have the same action, so the two coproducts have identical data.
    FM-DC : ∀ (S : Setoid 0ℓ 0ℓ) (D : functor.Functor (categories.setoid→category S) Fam⟨𝒞⟩.cat) →
            ∃ₛ (Category.Iso Fam⟨𝒞⟩.cat
                  (Colimit.apex (Fam⟨𝒞⟩.bigCoproducts S (M ∘F D)))
                  (M .Functor.fobj (Colimit.apex (Fam⟨𝒞⟩.bigCoproducts S D))))
               (λ i → ∀ s → Category._≈_ Fam⟨𝒞⟩.cat
                             (Category._∘_ Fam⟨𝒞⟩.cat (Category.Iso.fwd i)
                                (Colimit.cocone (Fam⟨𝒞⟩.bigCoproducts S (M ∘F D)) .NatTrans.transf s))
                             (M .Functor.fmor (Colimit.cocone (Fam⟨𝒞⟩.bigCoproducts S D) .NatTrans.transf s)))
    FM-DC S D = theIso , compat
      where
        Lo = Colimit.apex (Fam⟨𝒞⟩.bigCoproducts S (M ∘F D))
        Ro = M .Functor.fobj (Colimit.apex (Fam⟨𝒞⟩.bigCoproducts S D))

        fwd : Category._⇒_ Fam⟨𝒞⟩.cat Lo Ro
        fwd .idxf .func p = p
        fwd .idxf .func-resp-≈ e = e
        fwd .famf .transf p = 𝒞C.id _
        fwd .famf .natural e = 𝒞C.≈-trans 𝒞C.id-left (𝒞C.≈-sym 𝒞C.id-right)

        bwd : Category._⇒_ Fam⟨𝒞⟩.cat Ro Lo
        bwd .idxf .func p = p
        bwd .idxf .func-resp-≈ e = e
        bwd .famf .transf p = 𝒞C.id _
        bwd .famf .natural e = 𝒞C.≈-trans 𝒞C.id-left (𝒞C.≈-sym 𝒞C.id-right)

        theIso : Category.Iso Fam⟨𝒞⟩.cat Lo Ro
        theIso .Category.Iso.fwd = fwd
        theIso .Category.Iso.bwd = bwd
        theIso .Category.Iso.fwd∘bwd≈id .idxf-eq .func-eq e = e
        theIso .Category.Iso.fwd∘bwd≈id .famf-eq .transf-eq {p} =
          𝒞C.≈-trans (𝒞C.∘-cong (Ro .fam .refl*) (𝒞C.≈-trans 𝒞C.id-left 𝒞C.id-left)) 𝒞C.id-left
        theIso .Category.Iso.bwd∘fwd≈id .idxf-eq .func-eq e = e
        theIso .Category.Iso.bwd∘fwd≈id .famf-eq .transf-eq {p} =
          𝒞C.≈-trans (𝒞C.∘-cong (Lo .fam .refl*) (𝒞C.≈-trans 𝒞C.id-left 𝒞C.id-left)) 𝒞C.id-left

        compat : ∀ s → Category._≈_ Fam⟨𝒞⟩.cat
                        (Category._∘_ Fam⟨𝒞⟩.cat fwd (Colimit.cocone (Fam⟨𝒞⟩.bigCoproducts S (M ∘F D)) .NatTrans.transf s))
                        (M .Functor.fmor (Colimit.cocone (Fam⟨𝒞⟩.bigCoproducts S D) .NatTrans.transf s))
        compat s .idxf-eq .func-eq e =
          Colimit.cocone (Fam⟨𝒞⟩.bigCoproducts S D) .NatTrans.transf s .idxf .func-resp-≈ e
        compat s .famf-eq .transf-eq {d} =
          𝒞C.≈-trans (𝒞C.∘-cong (Ro .fam .refl*) (𝒞C.≈-trans 𝒞C.id-left 𝒞C.id-left)) 𝒞C.id-left

    open import conservativity
      Fam⟨𝒞⟩.cat Fam⟨𝒞⟩-terminal Fam⟨𝒞⟩-products (IdentityMonad Fam⟨𝒞⟩.cat)
      Fam⟨𝒞⟩.bigCoproducts 𝒞istable
      Fam⟨𝒟⟩.cat Fam⟨𝒟⟩-terminal Fam⟨𝒟⟩-products Fam⟨𝒟⟩-exponentials (IdentityMonad Fam⟨𝒟⟩.cat) Fam⟨𝒟⟩.bigCoproducts
      Fam⟨F⟩ Fam⟨F⟩-preserves-terminal Fam⟨F⟩-preserves-products
      (preserve-identity-monad Fam⟨F⟩)
      FM-DC
      (fam-functor.FamF-preserve-bigCopro 0ℓ 0ℓ F)
      (fam-functor.FamF-faithful 0ℓ 0ℓ F F-faithful)
      (fam-functor.FamF-def 0ℓ 0ℓ F F-def F-faithful)
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
    GF-preserve-strong-coproducts {x} {y} = Glued.IsIso-cong comp≈n comp-isIso
      where
        open Glued.Iso
        open Glued.IsIso
        module CP' = HasCoproducts
          (strong-coproducts→coproducts GlPE.terminal (ccc→strong-coproducts GlCP.coproducts GlPE.exponentials))
        module CPC = HasCoproducts Fam⟨𝒞⟩-coproducts
        module B-derive = finite-coproducts-from-indexed.derive Fam⟨𝒞⟩.bigCoproducts
        module B = HasCoproducts B-derive.coproducts-from-indexed

        -- The goal's chosen coproduct differs from the one conservativity uses
        -- (the two-element instance of Fam⟨𝒞⟩'s set-indexed coproducts) only by
        -- the canonical iso, which GF preserves.
        ρ = coproducts-canonical-iso Fam⟨𝒞⟩-coproducts B-derive.coproducts-from-indexed x y

        theIso : Glued.Iso (GlCPM.coprod (GF .fobj x) (GF .fobj y)) (GF .fobj (CPC.coprod x y))
        theIso = Glued.Iso-trans (Glued.IsIso→Iso GF-preserve-coproducts)
                                 (Glued.Iso-sym (functor-preserve-iso GF ρ))

        comp-isIso : Glued.IsIso (theIso .fwd)
        comp-isIso .inverse = theIso .bwd
        comp-isIso .f∘inverse≈id = theIso .fwd∘bwd≈id
        comp-isIso .inverse∘f≈id = theIso .bwd∘fwd≈id

        n = CP'.copair (GF .fmor (CPC.in₁ {x} {y})) (GF .fmor (CPC.in₂ {x} {y}))

        comp≈n : theIso .fwd Glued.≈ n
        comp≈n = Glued.≈-trans (Glued.≈-sym (CP'.copair-ext (theIso .fwd)))
                   (CP'.copair-cong onIn₁ onIn₂)
          where
            onIn₁ : (theIso .fwd Glued.∘ CP'.in₁) Glued.≈ GF .fmor (CPC.in₁ {x} {y})
            onIn₁ = Glued.≈-trans (Glued.assoc _ _ _)
                      (Glued.≈-trans (Glued.∘-cong Glued.≈-refl (GlCPM.copair-in₁ _ _))
                        (Glued.≈-trans (Glued.≈-sym (GF .fmor-comp _ _)) (GF .fmor-cong (B.copair-in₁ _ _))))
            onIn₂ : (theIso .fwd Glued.∘ CP'.in₂) Glued.≈ GF .fmor (CPC.in₂ {x} {y})
            onIn₂ = Glued.≈-trans (Glued.assoc _ _ _)
                      (Glued.≈-trans (Glued.∘-cong Glued.≈-refl (GlCPM.copair-in₂ _ _))
                        (Glued.≈-trans (Glued.≈-sym (GF .fmor-comp _ _)) (GF .fmor-cong (B.copair-in₂ _ _))))
