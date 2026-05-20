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
open import galois using (Obj; _⇒g_; 𝕃)

module galois-dec where

------------------------------------------------------------------------------
-- A Galois object with decidable bottom on its underlying carrier.
record Obj-dec : Set (suc 0ℓ) where
  field
    obj         : Obj
    ⊥-decidable : (x : Obj.carrier obj .Preorder.Carrier)
                → Dec (Preorder._≃_ (Obj.carrier obj) x (JoinSemilattice.⊥ (Obj.joins obj)))

------------------------------------------------------------------------------
-- Force: extract from 𝕃 X, mapping bottom to X's join-bottom (using decidable ⊥
-- on the left side to dispatch).
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
  force ._⇒g_.left .mono {a} {b} a≤b with ⊥-decidable a | ⊥-decidable b
  ... | yes _    | yes _    = tt
  ... | yes _    | no _     = tt
  ... | no a≇⊥   | yes b≃⊥  = a≇⊥ (X≤.≤-trans a≤b (b≃⊥ .proj₁) , Xj.⊥-isBottom .IsBottom.≤-bottom)
  ... | no _     | no _     = a≤b

  force ._⇒g_.left⊣right {bottom}  {y} with ⊥-decidable y
  ... | yes y≃⊥ = (λ y≤⊥ → tt) , (λ _ → y≃⊥ .proj₁)
  ... | no y≇⊥  = (λ y≤⊥ → y≇⊥ (y≤⊥ , Xj.⊥-isBottom .IsBottom.≤-bottom)) , λ ()
  force ._⇒g_.left⊣right {< x >}   {y} with ⊥-decidable y
  ... | yes y≃⊥ = (λ y≤x → tt) , λ _ → X≤.≤-trans (y≃⊥ .proj₁) (Xj.⊥-isBottom .IsBottom.≤-bottom)
  ... | no _    = (λ y≤x → y≤x) , λ y≤x → y≤x
