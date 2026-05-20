{-# OPTIONS --postfix-projections --safe --prop #-}

-- Experimental sketch: Galois objects with decidable bottom. Each Obj here is
-- a `galois.Obj` together with a decision procedure for "is this element ⊥?"
-- on the underlying carrier. Used to enable a `force : 𝕃 X ⇒g X` morphism
-- (and thus a PointedStrongMonad instance on 𝕃), since force needs to dispatch
-- between "this value is ⊥" (map to `bottom` in 𝕃 X) and "not ⊥" (map to <·>).

open import Level using (suc; 0ℓ)
open import basics using (IsBottom)
open import prop using (Dec; yes; no; tt; _,_; proj₁; proj₂) renaming (⊥ to ⊥p)
open import preorder using (Preorder; bottom; <_>)
open import join-semilattice using (JoinSemilattice)
import meet-semilattice
import join-semilattice
open import Data.Product using () renaming (_,_ to _,p_)
open import categories using (Category; HasProducts)
open import functor using (Functor; PointedFunctor)
open Functor
open import galois using (Obj; _⇒g_; 𝕃; 𝕃-map; 𝕃-unit; 𝕃-join; 𝕃-strength;
                            idg; _∘g_; _≃g_; ∘g-cong; ≃g-isEquivalence)
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
-- Binary products.
_⊕_ : Obj-dec → Obj-dec → Obj-dec
(X ⊕ Y) .Obj-dec.obj = Obj-dec.obj X galois.⊕ Obj-dec.obj Y
(X ⊕ Y) .Obj-dec.⊥-decidable (a ,p b) with Obj-dec.⊥-decidable X a | Obj-dec.⊥-decidable Y b
... | yes a≃⊥ | yes b≃⊥ = yes (preorder.×-≃ {X = Obj.carrier (Obj-dec.obj X)} {Y = Obj.carrier (Obj-dec.obj Y)} a≃⊥ b≃⊥)
... | yes _   | no b≇⊥  = no (λ p → b≇⊥ (p .proj₁ .proj₂ , p .proj₂ .proj₂))
... | no a≇⊥  | _       = no (λ p → a≇⊥ (p .proj₁ .proj₁ , p .proj₂ .proj₁))

products : HasProducts cat
products .HasProducts.prod              = _⊕_
products .HasProducts.p₁                = galois.products .HasProducts.p₁
products .HasProducts.p₂                = galois.products .HasProducts.p₂
products .HasProducts.pair              = galois.products .HasProducts.pair
products .HasProducts.pair-cong         = galois.products .HasProducts.pair-cong
products .HasProducts.pair-p₁           = galois.products .HasProducts.pair-p₁
products .HasProducts.pair-p₂           = galois.products .HasProducts.pair-p₂
products .HasProducts.pair-ext          = galois.products .HasProducts.pair-ext

------------------------------------------------------------------------------
-- 𝕃 is pointed (per object, with the ⊥-decidable on its carrier).

𝕃-functor : Functor cat cat
𝕃-functor .fobj X .Obj-dec.obj                   = 𝕃 (Obj-dec.obj X)
𝕃-functor .fobj X .Obj-dec.⊥-decidable bottom    = yes (tt , tt)
𝕃-functor .fobj X .Obj-dec.⊥-decidable < x >     = no (λ p → p .proj₁)
𝕃-functor .fmor                                  = 𝕃-map
𝕃-functor .fmor-cong                             = galois.𝕃-functor .fmor-cong
𝕃-functor .fmor-id                               = galois.𝕃-functor .fmor-id
𝕃-functor .fmor-comp                             = galois.𝕃-functor .fmor-comp

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

pointedFunctor : PointedFunctor products
pointedFunctor .PointedFunctor.F                          = 𝕃-functor
pointedFunctor .PointedFunctor.unit                       = 𝕃-unit
pointedFunctor .PointedFunctor.force {X}                  = force X
pointedFunctor .PointedFunctor.right-strength             = 𝕃-strength
pointedFunctor .PointedFunctor.right-strength-natural f g ._≃g_.right-eq =
  meet-semilattice.L-strength-natural (_⇒g_.right-∧ f) (_⇒g_.right-∧ g)
    .meet-semilattice._≃m_.eqfunc
-- FIXME: left-eq. join-semilattice.L-costrength-natural uses ⟨_,_⟩ (pair) form,
-- but galois.products' (prod-m f g).left uses [_,_] (copair) form (via join-side
-- biproduct). They're equal modulo ⊥-identity laws (x ∨ ⊥ ≃ x), but proving the
-- bridge requires a separate biproduct lemma in join-semilattice — or a
-- copair-form version of L-costrength-natural.
pointedFunctor .PointedFunctor.right-strength-natural f g ._≃g_.left-eq = {!!}
