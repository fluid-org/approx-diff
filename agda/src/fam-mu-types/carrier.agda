{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- Carrier of μ-types for the Fam construction: nested μ reduced to a single
-- sort-indexed W-type in setoids, with the fibre family computed by structural
-- recursion over trees. The sorts and trees are category-free, built from the
-- index setoids alone; the fibres recover the objects of the original
-- polynomial and environment through a decoration of the sorts.
--
-- Abbott, Altenkirch, Ghani. Containers: constructing strictly positive types. TCS 342(1), 2005.
-- Abbott, Altenkirch, Ghani. Representing nested inductive types using W-types. ICALP 2004.
-- Emmenegger. W-types in setoids. arXiv:1809.02375, 2018.
------------------------------------------------------------------------------

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Nat using (ℕ; suc)
import Data.Fin as Fin
open Fin using (Fin)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import prop using (_,_)
open import categories using (Category; HasTerminal; HasProducts)
open import prop-setoid using (IsEquivalence; Setoid)
open import indexed-family using (Fam; _⇒f_)
import fam
import polynomial-functor
import fam-mu-types.sort
import fam-mu-types.fibre
import fam-functor
import functor

module fam-mu-types.carrier {o m e} (os es : Level) {𝒞 : Category o m e}
    (T : HasTerminal 𝒞) (P : HasProducts 𝒞) (𝕃 : functor.StrongFunctor P) where

open Category 𝒞 public
open IsEquivalence public
open HasProducts P public
open fam.CategoryOfFamilies os (os ⊔ es) 𝒞 public
open Obj public
open Mor public
open Fam public
module Fam𝒞 = Category cat
open products P public  -- Fam-level products
module Fam𝒞-P = HasProducts products
open _⇒f_ public
open polynomial-functor using (extend) public
open polynomial-functor.Poly public
open polynomial-functor.Interp (terminal T) products strongCoproducts
       (fam-functor.FamF-strong os (os ⊔ es) P 𝕃) public
  using (fobj; HasMu; HasMuLaws)

Poly = polynomial-functor.Poly cat
open Setoid using (Carrier; isEquivalence) renaming (_≈_ to _≈s_) public

open import Data.Sum using (_⊎_) public
open import Data.Product using () renaming (_×_ to _×T_) public
open import prop using (_∧_; ⊥) public

-- The category-free sort layer, shared by every base category, and the
-- decorated fibre layer over this one.
module Sh = fam-mu-types.sort os es
open Sh public using (Sort; mkSort)
open fam-mu-types.fibre os es T P 𝕃 public using (Idx; ∣_∣; module Fibre; μObj)

-- Trees over an environment: shapes at its index setoids, fibres by decoration.
module Tree {n} (δ : Fin n → Obj) where
  open Sh.Tree (λ i → δ i .idx) public
  open Fibre δ public
