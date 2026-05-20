{-# OPTIONS --postfix-projections --safe --prop #-}

-- Experimental sketch: Galois objects with decidable bottom. Each Obj here is
-- a `galois.Obj` together with a decision procedure for "is this element ⊥?"
-- on the underlying carrier. Used to enable a `force : 𝕃 X ⇒g X` morphism
-- (and thus a PointedMonad instance on 𝕃), since force needs to dispatch
-- between "this value is ⊥" (map to `bottom` in 𝕃 X) and "not ⊥" (map to <·>).

open import Level using (suc; 0ℓ)
open import basics using (IsBottom)
open import prop using (Dec; yes; no; tt; _,_; proj₁; proj₂) renaming (⊥ to ⊥p)
open import preorder using (Preorder; bottom; <_>)
open import join-semilattice using (JoinSemilattice)
open import categories using (Category; HasProducts)
open import galois using (Obj; _⇒g_; 𝕃; idg; _∘g_; _≃g_; ∘g-cong; ≃g-isEquivalence;
                            _⊕_; products)
import galois

module galois-dec where

------------------------------------------------------------------------------
-- A Galois object with decidable bottom on its underlying carrier.
record Obj-dec : Set (suc 0ℓ) where
  field
    obj         : Obj
    ⊥-decidable : (x : Obj.carrier obj .Preorder.Carrier)
                → Dec (Preorder._≃_ (Obj.carrier obj) x (JoinSemilattice.⊥ (Obj.joins obj)))

------------------------------------------------------------------------------
-- 𝕃 is pointed.
module _ (X : Obj-dec) where
  open Obj-dec X
  open Obj obj using (carrier; meets; joins)
  private
    module X≤ = Preorder carrier
    module Xj = JoinSemilattice joins

  open preorder._=>_

  force : 𝕃 obj ⇒g obj
  force ._⇒g_.right .fun bottom  = Xj.⊥
  force ._⇒g_.right .fun < x >   = x
  force ._⇒g_.right .mono {bottom}  {bottom}  _    = X≤.≤-refl
  force ._⇒g_.right .mono {bottom}  {< _ >}   _    = Xj.⊥-isBottom .IsBottom.≤-bottom
  force ._⇒g_.right .mono {< _ >}   {< _ >}   x≤y  = x≤y

  force ._⇒g_.left .fun y with ⊥-decidable y
  ... | yes _ = bottom
  ... | no _  = < y >
  force ._⇒g_.left .mono {y₁} {y₂} y₁≤y₂ with ⊥-decidable y₁ | ⊥-decidable y₂
  ... | yes _    | yes _    = tt
  ... | yes _    | no _     = tt
  ... | no y₁≇⊥  | yes y₂≃⊥ = y₁≇⊥ (X≤.≤-trans y₁≤y₂ (y₂≃⊥ .proj₁) , Xj.⊥-isBottom .IsBottom.≤-bottom)
  ... | no _     | no _     = y₁≤y₂

  force ._⇒g_.left⊣right {bottom}  {y} with ⊥-decidable y
  ... | yes y≃⊥ = (λ y≤⊥ → tt) , (λ _ → y≃⊥ .proj₁)
  ... | no y≇⊥  = (λ y≤⊥ → y≇⊥ (y≤⊥ , Xj.⊥-isBottom .IsBottom.≤-bottom)) , λ ()
  force ._⇒g_.left⊣right {< x >}   {y} with ⊥-decidable y
  ... | yes y≃⊥ = (λ y≤x → tt) , λ _ → X≤.≤-trans (y≃⊥ .proj₁) (Xj.⊥-isBottom .IsBottom.≤-bottom)
  ... | no _    = (λ y≤x → y≤x) , λ y≤x → y≤x

------------------------------------------------------------------------------
-- Full subcategory of LatGal.
cat : Category (suc 0ℓ) 0ℓ 0ℓ
cat .Category.obj                   = Obj-dec
cat .Category._⇒_   X Y             = Obj-dec.obj X ⇒g Obj-dec.obj Y
cat .Category._≈_                   = _≃g_
cat .Category.isEquiv               = ≃g-isEquivalence
cat .Category.id    X               = idg (Obj-dec.obj X)
cat .Category._∘_                   = _∘g_
cat .Category.∘-cong                = ∘g-cong
cat .Category.id-left {X} {Y} {f}   = galois.cat .Category.id-left {Obj-dec.obj X} {Obj-dec.obj Y} {f}
cat .Category.id-right {X} {Y} {f}  = galois.cat .Category.id-right {Obj-dec.obj X} {Obj-dec.obj Y} {f}
cat .Category.assoc                 = galois.cat .Category.assoc

------------------------------------------------------------------------------
-- Pending:
--   * products on cat (derive ⊥-decidable from component decidabilities).
--   * 𝕃 lifted to a Functor cat cat.
--   * IsStrongMonad on this functor.
--   * PointedMonad packaging (with force above).
