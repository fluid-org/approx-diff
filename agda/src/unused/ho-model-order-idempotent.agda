{-# OPTIONS --postfix-projections --prop --safe #-}

-- The higher-order model with position orders as the first-order model: families over the
-- order-idempotent category, interpreted in Fam(SemiMod S) via the inclusion 𝓚, which sends an
-- order to its semimodule of down-closed selections and a morphism to itself, so it is full and
-- faithful outright. Sorts carry discrete orders, where absorption is trivial, so the free
-- first-order model is the special case.
open import Level using (0ℓ)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)
open import Data.Unit.Polymorphic using (tt)
open import prop-setoid using (Setoid; idS; _∘S_)
open import commutative-semiring using (CommutativeSemiring)
open import signature using (Signature; Model; PointedFPCat; PFPC[_,_,_,_])
open import categories using (Category; HasProducts; HasTerminal)
open import cmon-enriched using (CMonEnriched; Biproduct; biproducts→products; biproduct-iso)
open import functor using (Functor)
open import finite-product-functor using (preserve-chosen-terminal; preserve-chosen-products)
import prop
open prop using (_,_)
open import primitives using (Primitives; sort-vals-setoid)
import indexed-family
import semimodule
import matrix
import order-idempotent
import ho-model

module ho-model-order-idempotent
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (let open CommutativeSemiring S hiding (_≈_; trans; sym; refl); open Setoid A)
  (∨-idem    : ∀ {x} → x + x ≈ x)
  (∧-idem    : ∀ {x} → x · x ≈ x)
  (⊤-add-top : ∀ {x} → ι + x ≈ ι)
  where

module SemiMod = semimodule S
module OI = order-idempotent S ∨-idem ∧-idem ⊤-add-top
open SemiMod._⇒_
open SemiMod._≈m_

-- The chosen products on the order-idempotent category, from its biproducts.
OI-products : HasProducts OI.cat
OI-products = biproducts→products OI.cmon OI.biproduct

-- The inclusion into the semimodules: the selection semimodule on objects, the identity on
-- morphisms.
𝓚 : Functor OI.cat SemiMod.cat
𝓚 .Functor.fobj = OI.𝒟
𝓚 .Functor.fmor h = h
𝓚 .Functor.fmor-cong e = e
𝓚 .Functor.fmor-id {P} = OI.≈p-refl {f = OI.id P}
𝓚 .Functor.fmor-comp g f = OI.≈p-refl {f = OI._∘_ g f}

-- The empty order's selection semimodule is terminal: it has one selection.
private
  ⊥-into : SemiMod._⇒_ SemiMod.𝟘 (OI.𝒟 OI.𝟘p)
  ⊥-into .*→* .prop-setoid._⇒_.func _ = (λ ()) , (λ ())
  ⊥-into .*→* .prop-setoid._⇒_.func-resp-≈ _ ()
  ⊥-into .preserve-ze ()
  ⊥-into .preserve-+ ()
  ⊥-into .preserve-· ()

𝓚-preserve-terminal : preserve-chosen-terminal 𝓚 OI.terminal SemiMod.terminal
𝓚-preserve-terminal .Category.IsIso.inverse = ⊥-into
𝓚-preserve-terminal .Category.IsIso.f∘inverse≈id =
  HasTerminal.to-terminal-unique SemiMod.terminal _ _
𝓚-preserve-terminal .Category.IsIso.inverse∘f≈id .*≈* .prop-setoid._≃m_.func-eq _ ()

-- The image of a block order's biproduct structure is a biproduct on the selection semimodules
-- outright, so the inclusion preserves the chosen products via the canonical comparison.
biproduct𝓚 : ∀ P Q → Biproduct SemiMod.cmon-enriched (OI.𝒟 P) (OI.𝒟 Q)
biproduct𝓚 P Q .Biproduct.prod = OI.𝒟 (OI._⊕_ P Q)
biproduct𝓚 P Q .Biproduct.p₁ = OI.π₁ P Q
biproduct𝓚 P Q .Biproduct.p₂ = OI.π₂ P Q
biproduct𝓚 P Q .Biproduct.in₁ = OI.ι₁ P Q
biproduct𝓚 P Q .Biproduct.in₂ = OI.ι₂ P Q
biproduct𝓚 P Q .Biproduct.id-1 = OI.biproduct P Q .Biproduct.id-1
biproduct𝓚 P Q .Biproduct.id-2 = OI.biproduct P Q .Biproduct.id-2
biproduct𝓚 P Q .Biproduct.zero-1 = OI.biproduct P Q .Biproduct.zero-1
biproduct𝓚 P Q .Biproduct.zero-2 = OI.biproduct P Q .Biproduct.zero-2
biproduct𝓚 P Q .Biproduct.id-+ = OI.biproduct P Q .Biproduct.id-+

𝓚-preserve-products :
  preserve-chosen-products 𝓚 OI-products
    (biproducts→products SemiMod.cmon-enriched SemiMod.biproduct)
𝓚-preserve-products {P} {Q} =
  biproduct-iso SemiMod.cmon-enriched (biproduct𝓚 P Q) (SemiMod.biproduct (OI.𝒟 P) (OI.𝒟 Q))

open ho-model.Interpretation
  OI.cat OI.terminal OI-products
  SemiMod.cat SemiMod.cmon-enriched SemiMod.limits SemiMod.terminal SemiMod.biproduct
  𝓚 𝓚-preserve-terminal (λ {X} {Y} → 𝓚-preserve-products {X} {Y})
  (λ {a} {b} {g₁} {g₂} h → h) (λ h _ → h , OI.≈p-refl {f = h})
  public
