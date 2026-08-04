{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- The rooted logical relations: the family-level construction of
-- conservativity-fam with the rooted μ-types glued on top. The model side of
-- that construction is already the category of families the rooted machinery
-- is built over, so its nerve serves as the glueing functor unchanged, and no
-- comparison between the two levels is needed. The root predicate picks out
-- the definable root selections: the maps into a lifted family that factor
-- through a bare root at some index, up to cover refinement.
------------------------------------------------------------------------------

open import Level using (Level; 0ℓ)
open import prop using (Prf; ∃; ∃ₛ)
open import prop-setoid as PS using (Setoid)
open import categories using (Category; HasTerminal; HasProducts; HasWeakExponentials)
open import cmon-enriched using (CMonEnriched; Biproduct; biproducts→products)
open import lifting using (Lifting)
open import functor using (Functor)
open import indexed-family using (_⇒f_)
open import predicate-system using (PredicateSystem; ClosureOp)
open import finite-product-functor
  using (preserve-chosen-terminal; preserve-chosen-products)
import fam
import conservativity-fam
import fam-mu-lifting.laws
import fam-mu-lifting.glued-interface

module conservativity-rooted {o₁ o₂ m e}
  {𝒞₀ : Category o₁ m e} (𝒞₀T : HasTerminal 𝒞₀) (𝒞₀P : HasProducts 𝒞₀)
  {𝒟₀ : Category o₂ m e} (𝒟₀T : HasTerminal 𝒟₀)
  (CM' : CMonEnriched 𝒟₀) (BP' : ∀ x y → Biproduct CM' x y)
  {𝟙d : Category.obj 𝒟₀} (Lft' : Lifting CM' 𝟙d)
  (let 𝒟₀P = biproducts→products CM' BP')
  (F₀ : Functor 𝒞₀ 𝒟₀)
  (F₀T : preserve-chosen-terminal F₀ 𝒞₀T 𝒟₀T)
  (F₀P : preserve-chosen-products F₀ 𝒞₀P 𝒟₀P)
  (let module Fam𝒟 = fam.CategoryOfFamilies 0ℓ 0ℓ 𝒟₀)
  (let module Fam𝒟P = Fam𝒟.products 𝒟₀P)
  (𝒟E : HasWeakExponentials Fam𝒟.cat Fam𝒟P.products)
  (F₀-faithful : ∀ {a b} {g₁ g₂ : Category._⇒_ 𝒞₀ a b} →
                 Category._≈_ 𝒟₀ (F₀ .Functor.fmor g₁) (F₀ .Functor.fmor g₂) →
                 Category._≈_ 𝒞₀ g₁ g₂)
  (F₀def : ∀ {a b} (k : Category._⇒_ 𝒟₀ (F₀ .Functor.fobj a) (F₀ .Functor.fobj b)) →
           Prf (∃ (Category._⇒_ 𝒞₀ a b) λ g → Category._≈_ 𝒟₀ (F₀ .Functor.fmor g) k) →
           ∃ₛ (Category._⇒_ 𝒞₀ a b) λ g → Category._≈_ 𝒟₀ (F₀ .Functor.fmor g) k)
  where

open Functor

-- The family-level logical relations, reused wholesale.
module CF = conservativity-fam 𝒞₀T 𝒞₀P 𝒟₀T 𝒟₀P F₀ F₀T F₀P 𝒟E F₀-faithful F₀def

open CF.Rel using (G; PSh⟨𝒞⟩; PSh⟨𝒞⟩-products; PSh⟨𝒞⟩-system; closureOp)

-- The rooted structure on the same category of families.
module RML = fam-mu-lifting.laws 0ℓ 0ℓ 𝒟₀T CM' BP' Lft'

open PredicateSystem PSh⟨𝒞⟩-system using (Predicate; TT; _⟨_⟩; ⋁)
open ClosureOp closureOp using (𝐂)

-- The singleton family at the lifting's unit.
𝟙L : RML.Obj
𝟙L = RML.simple[ PS.𝟙 {0ℓ} {0ℓ} , 𝟙d ]

-- The bare root of a lifted family at an index.
root-mor : ∀ (C : RML.Obj) (i : Setoid.Carrier (RML.idx C)) → RML.Mor 𝟙L (RML.Lf C)
root-mor C i .RML.idxf .PS._⇒_.func _ = i
root-mor C i .RML.idxf .PS._⇒_.func-resp-≈ _ = Setoid.refl (RML.idx C)
root-mor C i .RML.famf ._⇒f_.transf _ = RML.root
root-mor C i .RML.famf ._⇒f_.natural _ =
  RML.≈-trans RML.id-right (RML.≈-sym (RML.Lmap-root _))

-- Definable root selections: up to cover refinement, the maps into a lifted
-- family that factor through a bare root.
Rt : ∀ (C : RML.Obj) → Predicate (G .fobj (RML.Lf C))
Rt C = 𝐂 (⋁ (Setoid.Carrier (RML.idx C)) (λ i → TT ⟨ G .fmor (root-mor C i) ⟩))

-- The glued rooted μ interface at the family-level nerve.
module RootedMu =
  fam-mu-lifting.glued-interface 𝒟₀T CM' BP' Lft'
    PSh⟨𝒞⟩ PSh⟨𝒞⟩-products PSh⟨𝒞⟩-system G Rt closureOp
