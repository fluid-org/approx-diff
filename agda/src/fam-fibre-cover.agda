{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- Every family is the set-indexed coproduct of its fibres, indexed by its own
-- index setoid. A stage of the family-level logical relations is a family, so
-- this is the decomposition that lets a cover of a stage reach a single fibre.
------------------------------------------------------------------------------

open import Level using (Level; lift)
open import Data.Unit using () renaming (tt to ttS)
open import Data.Product using (_,_)
open import prop using (⟪_⟫; tt) renaming (_,_ to _,ₚ_)
open import prop-setoid as PS using (Setoid; IsEquivalence)
open import categories using (Category; setoid→category)
open import functor using (Functor; Colimit; HasColimits; NatTrans)
open import indexed-family using (Fam; _⇒f_; _≃f_)
import fam

module fam-fibre-cover {o m e} (os es : Level) (𝒞 : Category o m e) where

open fam.CategoryOfFamilies os es 𝒞
open Category 𝒞
open Obj
open Mor
open _≃_
open Fam
open _⇒f_
open _≃f_
open Functor
open Colimit
open NatTrans
open Setoid using (Carrier)
open IsEquivalence

-- The inclusion of a single fibre.
elem : (X : Obj) (v : X .idx .Carrier) → Mor simple[ PS.𝟙 , X .fam .fm v ] X
elem X v .idxf .PS._⇒_.func _ = v
elem X v .idxf .PS._⇒_.func-resp-≈ _ = X .idx .Setoid.isEquivalence .refl
elem X v .famf .transf _ = id _
elem X v .famf .natural _ = ≈-trans id-left (≈-sym (≈-trans id-right (X .fam .refl*)))

-- The fibres as a diagram over the index setoid.
fibres : (X : Obj) → Functor (setoid→category (X .idx)) cat
fibres X .fobj v = simple[ PS.𝟙 , X .fam .fm v ]
fibres X .fmor ⟪ p ⟫ = simplef[ PS.idS PS.𝟙 , X .fam .subst p ]
fibres X .fmor-cong _ = ≃-isEquivalence .refl
fibres X .fmor-id .idxf-eq .PS._≃m_.func-eq _ = tt
fibres X .fmor-id .famf-eq .transf-eq = ≈-trans id-left (X .fam .refl*)
fibres X .fmor-comp ⟪ p ⟫ ⟪ q ⟫ .idxf-eq .PS._≃m_.func-eq _ = tt
fibres X .fmor-comp ⟪ p ⟫ ⟪ q ⟫ .famf-eq .transf-eq =
  ≈-trans id-left (≈-trans (X .fam .trans* p q) (≈-sym id-left))

∐fib : (X : Obj) → Obj
∐fib X = bigCoproducts (X .idx) (fibres X) .apex

fib-fwd : (X : Obj) → Mor (∐fib X) X
fib-fwd X .idxf .PS._⇒_.func (v , _) = v
fib-fwd X .idxf .PS._⇒_.func-resp-≈ (p ,ₚ _) = p
fib-fwd X .famf .transf _ = id _
fib-fwd X .famf .natural _ = ≈-trans id-left (≈-trans id-left (≈-sym id-right))

fib-bwd : (X : Obj) → Mor X (∐fib X)
fib-bwd X .idxf .PS._⇒_.func v = v , lift ttS
fib-bwd X .idxf .PS._⇒_.func-resp-≈ p = p ,ₚ tt
fib-bwd X .famf .transf _ = id _
fib-bwd X .famf .natural _ = ≈-trans id-left (≈-sym (≈-trans id-right id-left))

fib-iso : (X : Obj) → Category.Iso cat (∐fib X) X
fib-iso X .Category.Iso.fwd = fib-fwd X
fib-iso X .Category.Iso.bwd = fib-bwd X
fib-iso X .Category.Iso.fwd∘bwd≈id .idxf-eq .PS._≃m_.func-eq p = p
fib-iso X .Category.Iso.fwd∘bwd≈id .famf-eq .transf-eq =
  ≈-trans (∘-cong (X .fam .refl*) (≈-trans id-left id-left)) id-left
fib-iso X .Category.Iso.bwd∘fwd≈id .idxf-eq .PS._≃m_.func-eq (p ,ₚ _) = p ,ₚ tt
fib-iso X .Category.Iso.bwd∘fwd≈id .famf-eq .transf-eq =
  ≈-trans (∘-cong (≈-trans id-left (X .fam .refl*)) (≈-trans id-left id-left)) id-left

-- Restricting along the injection of a fibre lands in that fibre.
fib-leg : ∀ (X : Obj) (v : X .idx .Carrier) →
          Category._≈_ cat
            (Category._∘_ cat (fib-fwd X)
               (bigCoproducts (X .idx) (fibres X) .cocone .transf v))
            (elem X v)
fib-leg X v .idxf-eq .PS._≃m_.func-eq _ = X .idx .Setoid.isEquivalence .refl
fib-leg X v .famf-eq .transf-eq =
  ≈-trans (∘-cong (X .fam .refl*) (≈-trans id-left id-left)) id-left
