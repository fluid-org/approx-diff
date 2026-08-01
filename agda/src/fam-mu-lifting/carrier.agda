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
open import categories using (Category; HasTerminal; HasProducts; HasCoproducts)
open import cmon-enriched using (CMonEnriched; Biproduct; biproducts→products)
open import lifting using (Lifting)
open import prop-setoid using (IsEquivalence; Setoid)
open import indexed-family using (Fam; _⇒f_)
import fam
import polynomial-functor
import fam-mu-types.sort
import fam-mu-lifting.fibre

module fam-mu-lifting.carrier {o m e} (os es : Level) {𝒞 : Category o m e}
    (T : HasTerminal 𝒞) (CM : CMonEnriched 𝒞) (BP : ∀ x y → Biproduct CM x y)
    {𝟙c : Category.obj 𝒞} (Lft : Lifting 𝒞 𝟙c) where

open Category 𝒞 public
open IsEquivalence public

P : HasProducts 𝒞
P = biproducts→products CM BP

open HasProducts P public
open Lifting Lft public
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
Poly = polynomial-functor.Poly cat
open Setoid using (Carrier; isEquivalence) renaming (_≈_ to _≈s_) public

open import Data.Sum using (_⊎_) public
open import Data.Product using () renaming (_×_ to _×T_) public
open import prop using (_∧_; ⊥) public

-- The category-free sort layer, shared by every base category, and the
-- decorated fibre layer over this one.
module Sh = fam-mu-types.sort os es
open Sh public using (Sort; mkSort)
open fam-mu-lifting.fibre os es CM BP Lft public using (Idx; ∣_∣; module Fibre; μObj)

-- The fibrewise lift of a family: same index, each fibre lifted, transports under the action.
Lf : Obj → Obj
Lf X .idx = X .idx
Lf X .fam .fm x = L (X .fam .fm x)
Lf X .fam .subst e = Lmap (X .fam .subst e)
Lf X .fam .refl* = ≈-trans (Lmap-cong (X .fam .refl*)) Lmap-id
Lf X .fam .trans* q p = ≈-trans (Lmap-cong (X .fam .trans* q p)) (Lmap-comp _ _)

-- The interpretation of a polynomial with a root at every value former: sums are coproducts of
-- lifted summands, products are lifted products, mirroring the fibres of the trees.
fobj : (μ-obj : ∀ {k} → Poly (suc k) → (Fin k → Obj) → Obj) →
       ∀ {n} → Poly n → (Fin n → Obj) → Obj
fobj μ-obj (const A) δ = A
fobj μ-obj (var i)   δ = δ i
fobj μ-obj (P' + Q') δ =
  HasCoproducts.coprod coproducts (Lf (fobj μ-obj P' δ)) (Lf (fobj μ-obj Q' δ))
fobj μ-obj (P' × Q') δ = Lf (Fam𝒞-P.prod (fobj μ-obj P' δ) (fobj μ-obj Q' δ))
fobj μ-obj (μ P')    δ = μ-obj P' δ

-- Reindexing a context-paired morphism under a root: the root passes through, the context enters
-- the payload, and absorption records under the target root whatever the context contributes.
under-root : ∀ {G X Y} → (prod G X ⇒ Y) → (prod G (L X) ⇒ L Y)
under-root {G} {X} {Y} r =
  Biproduct.copair (BP G (L X))
    (inj ∘ (r ∘ Biproduct.in₁ (BP G X)))
    (affine root (inj ∘ (r ∘ Biproduct.in₂ (BP G X))))

under-root-cong : ∀ {G X Y} {r r' : prod G X ⇒ Y} → r ≈ r' → under-root r ≈ under-root r'
under-root-cong {G} {X} {Y} er =
  Biproduct.copair-cong (BP G (L X))
    (∘-cong ≈-refl (∘-cong er ≈-refl))
    (affine-cong ≈-refl (∘-cong ≈-refl (∘-cong er ≈-refl)))

-- Trees over an environment: shapes at its index setoids, fibres by decoration.
module Tree {n} (δ : Fin n → Obj) where
  open Sh.Tree (λ i → δ i .idx) public
  open Fibre δ public
