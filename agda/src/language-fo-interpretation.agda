{-# OPTIONS --prop --postfix-projections --safe #-}

-- The first-order fragment of the interpretation, compared across a change of base. The
-- source side interprets first-order types directly over its family category; the target side is
-- the interpretation of the language at the transported model, with the unit object the
-- image of the source unit and the empty environment the image environment. With those choices the
-- two polynomial translations agree on the nose, so the μ case is exactly the fibrewise
-- comparison of μ-carriers, and every first-order type's interpretation on the target side
-- is isomorphic to the image of its interpretation on the source side.

open import Level using (Level)
open import Data.Nat using (suc; _+_)
import Data.Fin as Fin
open Fin using (Fin; splitAt)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import categories
  using (Category; HasTerminal; HasProducts; HasCoproducts; HasWeakExponentials)
open import cmon-enriched using (CMonEnriched; Biproduct; biproducts→products)
import lifting
open import functor using (Functor)
open import finite-product-functor using (preserve-chosen-products; preserve-chosen-terminal)
open import polynomial-functor using (Poly; Poly-map)
open import signature using (Signature; Model; PFPC[_,_,_,_]; transport-model)
import fam-mu-lifting.in-map
import fam-change-of-base
import language-syntax

open Functor

module language-fo-interpretation {ℓ} (Sig : Signature ℓ)
  {o m e o₂ m₂ e₂} (os es : Level)
  {𝒞 : Category o m e} (T𝒞 : HasTerminal 𝒞)
  (CM𝒞 : CMonEnriched 𝒞) (BP𝒞 : ∀ x y → Biproduct CM𝒞 x y)
  (𝟙𝒞 : Category.obj 𝒞)
  {𝒟 : Category o₂ m₂ e₂} (T𝒟 : HasTerminal 𝒟)
  (CM𝒟 : CMonEnriched 𝒟) (BP𝒟 : ∀ x y → Biproduct CM𝒟 x y)
  (𝟙𝒟 : Category.obj 𝒟)
  (F : Functor 𝒞 𝒟)
  (F-terminal : preserve-chosen-terminal F T𝒞 T𝒟)
  (F-prod : preserve-chosen-products F (biproducts→products CM𝒞 BP𝒞) (biproducts→products CM𝒟 BP𝒟))
  (let module L𝒞 = lifting CM𝒞 BP𝒞 𝟙𝒞) (let module L𝒟 = lifting CM𝒟 BP𝒟 𝟙𝒟)
  (let module 𝒞 = Category 𝒞) (let module 𝒟 = Category 𝒟)
  (F-L : ∀ X → 𝒟.Iso (Functor.fobj F (L𝒞.L X)) (L𝒟.L (Functor.fobj F X)))
  (F-L-natural : ∀ {X Y} (f : X 𝒞.⇒ Y) →
     (F-L Y .𝒟.Iso.fwd 𝒟.∘ Functor.fmor F (L𝒞.Lmap f))
       𝒟.≈ (L𝒟.Lmap (Functor.fmor F f) 𝒟.∘ F-L X .𝒟.Iso.fwd))
  (let module Fam⟨𝒞⟩μ = fam-mu-lifting.in-map os es CM𝒞 BP𝒞 𝟙𝒞)
  (let module Fam⟨𝒟⟩μ = fam-mu-lifting.in-map os es CM𝒟 BP𝒟 𝟙𝒟)
  (𝒟E : HasWeakExponentials Fam⟨𝒟⟩μ.cat Fam⟨𝒟⟩μ.products)
  (𝒞𝟙ty : Fam⟨𝒞⟩μ.Obj)
  (𝒞unit-pt : Fam⟨𝒞⟩μ.Mor (HasTerminal.witness (Fam⟨𝒞⟩μ.terminal T𝒞)) 𝒞𝟙ty)
  (let 𝒞Bool = HasCoproducts.coprod Fam⟨𝒞⟩μ.coproducts (Fam⟨𝒞⟩μ.Lf 𝒞𝟙ty) (Fam⟨𝒞⟩μ.Lf 𝒞𝟙ty))
  (𝒞-Sig-model : Model PFPC[ Fam⟨𝒞⟩μ.cat , Fam⟨𝒞⟩μ.terminal T𝒞 , Fam⟨𝒞⟩μ.products , 𝒞Bool ] Sig)
  (elim-w : 𝟙𝒟 𝒟.⇒ 𝟙𝒟)
  (𝒟-exp-const : ∀ {X Y : Fam⟨𝒟⟩μ.Obj} → Fam⟨𝒟⟩μ.Constant Y →
                 Fam⟨𝒟⟩μ.Constant (HasWeakExponentials.exp 𝒟E X Y))
  (F𝟙 : 𝟙𝒟 𝒟.⇒ Functor.fobj F 𝟙𝒞)
  (𝒞𝟙ty-const : Fam⟨𝒞⟩μ.Constant 𝒞𝟙ty)
  (𝒞-sort-const : ∀ s → Fam⟨𝒞⟩μ.Constant (Model.⟦sort⟧ 𝒞-Sig-model s))
  where

open language-syntax Sig

module HR = fam-change-of-base os es T𝒞 CM𝒞 BP𝒞 𝟙𝒞 T𝒟 CM𝒟 BP𝒟 𝟙𝒟 F F-terminal F-prod F-L F-L-natural
open HR using (Fam⟨F⟩; Fam⟨F⟩-preserves-terminal; Fam⟨F⟩-preserves-products;
               Fam⟨F⟩-preserves-coproducts; Fam⟨F⟩-L)

private
  module FD = Category Fam⟨𝒟⟩μ.cat
  module FDP = HasProducts Fam⟨𝒟⟩μ.products
  module FDC = HasCoproducts Fam⟨𝒟⟩μ.coproducts

-- The chosen empty environment on the source side, and its image on the target side.
∅𝒞 : Fin 0 → Fam⟨𝒞⟩μ.Obj
∅𝒞 ()

δ∅𝒟 : Fin 0 → Fam⟨𝒟⟩μ.Obj
δ∅𝒟 = λ i → Fam⟨F⟩ .fobj (∅𝒞 i)

-- Interpretation of the first-order types on the source side, with the value formers and
-- μ-types via the polynomial translation of the first-order witness.
module _ where
  open Category Fam⟨𝒞⟩μ.cat
  open HasTerminal (Fam⟨𝒞⟩μ.terminal T𝒞) renaming (witness to 𝟙)
  open HasProducts Fam⟨𝒞⟩μ.products
  open HasCoproducts Fam⟨𝒞⟩μ.coproducts
  open Fam⟨𝒞⟩μ using (Lf)

  fo-as-poly : ∀ {Δ n} {τ : type (n + Δ)} → first-order τ → (Fin Δ → obj) → Poly Fam⟨𝒞⟩μ.cat n
  fo-as-poly {n = n} (var i)   δ = [ Poly.var , (λ j → Poly.const (δ j)) ] (splitAt n i)
  fo-as-poly unit              δ = Poly.const 𝒞𝟙ty
  fo-as-poly (base s)          δ = Poly.const (𝒞-Sig-model .Model.⟦sort⟧ s)
  fo-as-poly (fo₁ [+] fo₂)     δ = fo-as-poly fo₁ δ Poly.+ fo-as-poly fo₂ δ
  fo-as-poly (fo₁ [×] fo₂)     δ = fo-as-poly fo₁ δ Poly.× fo-as-poly fo₂ δ
  fo-as-poly (μ fo)            δ = Poly.μ (fo-as-poly fo δ)

  𝒞⟦_⟧ty : ∀ {Δ} {τ : type Δ} → first-order τ → (Fin Δ → obj) → obj
  𝒞⟦ var i ⟧ty       δ = δ i
  𝒞⟦ unit ⟧ty        δ = 𝒞𝟙ty
  𝒞⟦ base s ⟧ty      δ = 𝒞-Sig-model .Model.⟦sort⟧ s
  𝒞⟦ fo₁ [+] fo₂ ⟧ty δ = coprod (Lf (𝒞⟦ fo₁ ⟧ty δ)) (Lf (𝒞⟦ fo₂ ⟧ty δ))
  𝒞⟦ fo₁ [×] fo₂ ⟧ty δ = Lf (prod (𝒞⟦ fo₁ ⟧ty δ) (𝒞⟦ fo₂ ⟧ty δ))
  𝒞⟦ μ fo ⟧ty        δ = Fam⟨𝒞⟩μ.μ-fam (fo-as-poly {n = 1} fo δ) ∅𝒞

  𝒞⟦_⟧ctxt : ∀ {Γ} → first-order-ctxt Γ → obj
  𝒞⟦ emp ⟧ctxt    = 𝟙
  𝒞⟦ Γ , τ ⟧ctxt = prod 𝒞⟦ Γ ⟧ctxt (𝒞⟦ τ ⟧ty ∅𝒞)

-- The target side: the interpretation of the language at the transported model, with unit
-- the image of the source unit and the empty environment the image environment.
𝒟𝟙ty : Fam⟨𝒟⟩μ.Obj
𝒟𝟙ty = Fam⟨F⟩ .fobj 𝒞𝟙ty

𝒟unit-pt : Fam⟨𝒟⟩μ.Mor (HasTerminal.witness (Fam⟨𝒟⟩μ.terminal T𝒟)) 𝒟𝟙ty
𝒟unit-pt = FD._∘_ (Fam⟨F⟩ .fmor 𝒞unit-pt) (Fam⟨F⟩-preserves-terminal .Category.IsIso.inverse)

𝒟Bool = FDC.coprod (Fam⟨𝒟⟩μ.Lf 𝒟𝟙ty) (Fam⟨𝒟⟩μ.Lf 𝒟𝟙ty)

𝒟-Sig-model : Model PFPC[ Fam⟨𝒟⟩μ.cat , Fam⟨𝒟⟩μ.terminal T𝒟 , Fam⟨𝒟⟩μ.products , 𝒟Bool ] Sig
𝒟-Sig-model =
  transport-model Sig Fam⟨F⟩ Fam⟨F⟩-preserves-terminal
    (λ {X} {Y} → Fam⟨F⟩-preserves-products {X} {Y})
    (HR.bool.Fam⟨F⟩-preserves-bool 𝒞𝟙ty)
    𝒞-Sig-model

-- The target-side constants: the unit and sort constants are the images of the source-side
-- ones, entered through the chosen map from the target unit object.
𝒟𝟙ty-const : Fam⟨𝒟⟩μ.Constant 𝒟𝟙ty
𝒟𝟙ty-const = HR.Fam⟨F⟩-constant F𝟙 𝒞𝟙ty-const

𝒟-sort-const : ∀ s → Fam⟨𝒟⟩μ.Constant (Model.⟦sort⟧ 𝒟-Sig-model s)
𝒟-sort-const s = HR.Fam⟨F⟩-constant F𝟙 (𝒞-sort-const s)

open import language-interpretation Sig os es T𝒟 CM𝒟 BP𝒟 𝟙𝒟 𝒟E δ∅𝒟
  𝒟𝟙ty 𝒟unit-pt 𝒟-Sig-model elim-w 𝒟-exp-const 𝒟𝟙ty-const 𝒟-sort-const
  renaming (⟦_⟧ty to 𝒟⟦_⟧ty; ⟦_⟧ctxt to 𝒟⟦_⟧ctxt; ⟦_⟧tm to 𝒟⟦_⟧tm; as-poly to 𝒟-as-poly;
            ty-cong to 𝒟-ty-cong)
  using ()
  public

-- The polynomial translations agree on the nose: the change of base leaves variables in place and
-- carries each const leaf to the leaf the transported model interprets there.
fo-poly-map-≡ : ∀ {Δ n} {τ : type (n + Δ)} (fo : first-order τ) (δ𝒞 : Fin Δ → Fam⟨𝒞⟩μ.Obj) →
                Poly-map Fam⟨F⟩ (fo-as-poly {Δ} {n} fo δ𝒞)
                  ≡ 𝒟-as-poly {Δ} {n} τ (λ i → Fam⟨F⟩ .fobj (δ𝒞 i))
fo-poly-map-≡ {Δ} {n} (var i) δ𝒞 = go (splitAt n i)
  where
    go : (s : Fin n ⊎ Fin Δ) →
         Poly-map Fam⟨F⟩ ([ Poly.var , (λ j → Poly.const (δ𝒞 j)) ] s)
           ≡ [ Poly.var , (λ j → Poly.const (Fam⟨F⟩ .fobj (δ𝒞 j))) ] s
    go (inj₁ k) = refl
    go (inj₂ j) = refl
fo-poly-map-≡ unit          δ𝒞 = refl
fo-poly-map-≡ (base s)      δ𝒞 = refl
fo-poly-map-≡ (fo₁ [+] fo₂) δ𝒞 = cong₂ Poly._+_ (fo-poly-map-≡ fo₁ δ𝒞) (fo-poly-map-≡ fo₂ δ𝒞)
fo-poly-map-≡ (fo₁ [×] fo₂) δ𝒞 = cong₂ Poly._×_ (fo-poly-map-≡ fo₁ δ𝒞) (fo-poly-map-≡ fo₂ δ𝒞)
fo-poly-map-≡ (μ fo)        δ𝒞 = cong Poly.μ (fo-poly-map-≡ fo δ𝒞)

private
  ≡-Iso : ∀ {x y} → x ≡ y → FD.Iso x y
  ≡-Iso refl = FD.Iso-refl

-- Every first-order type's interpretation on the target side is isomorphic to the image of its
-- interpretation on the source side; μ-types by the fibrewise comparison over shared trees.
⟦_⟧-iso : ∀ {Δ} {τ : type Δ} (fo : first-order τ) (δ𝒞 : Fin Δ → Fam⟨𝒞⟩μ.Obj) →
          FD.Iso (Fam⟨F⟩ .fobj (𝒞⟦ fo ⟧ty δ𝒞)) (𝒟⟦ τ ⟧ty (λ i → Fam⟨F⟩ .fobj (δ𝒞 i)))
⟦ var i ⟧-iso       δ𝒞 = FD.Iso-refl
⟦ unit ⟧-iso        δ𝒞 = FD.Iso-refl
⟦ base s ⟧-iso      δ𝒞 = FD.Iso-refl
⟦ fo₁ [+] fo₂ ⟧-iso δ𝒞 =
  FD.Iso-trans (FD.Iso-sym (FD.IsIso→Iso Fam⟨F⟩-preserves-coproducts))
    (FDC.coproduct-preserve-iso
      (FD.Iso-trans (Fam⟨F⟩-L _) (Fam⟨𝒟⟩μ.Lf-iso (⟦ fo₁ ⟧-iso δ𝒞)))
      (FD.Iso-trans (Fam⟨F⟩-L _) (Fam⟨𝒟⟩μ.Lf-iso (⟦ fo₂ ⟧-iso δ𝒞))))
⟦ fo₁ [×] fo₂ ⟧-iso δ𝒞 =
  FD.Iso-trans (Fam⟨F⟩-L _)
    (Fam⟨𝒟⟩μ.Lf-iso
      (FD.Iso-trans (FD.IsIso→Iso Fam⟨F⟩-preserves-products)
        (FDP.product-preserves-iso (⟦ fo₁ ⟧-iso δ𝒞) (⟦ fo₂ ⟧-iso δ𝒞))))
⟦ μ fo ⟧-iso        δ𝒞 =
  FD.Iso-trans (HR.FW.FibrewiseMu.fibrewise-μ-iso (fo-as-poly fo δ𝒞) ∅𝒞)
    (≡-Iso (cong (λ (Q : Poly Fam⟨𝒟⟩μ.cat 1) → Fam⟨𝒟⟩μ.μ-fam Q δ∅𝒟) (fo-poly-map-≡ fo δ𝒞)))

-- At closed types the target environment is the empty one, up to pointwise equality.
closed-iso : ∀ {τ : type 0} (fo : first-order τ) →
             FD.Iso (Fam⟨F⟩ .fobj (𝒞⟦ fo ⟧ty ∅𝒞)) (𝒟⟦ τ ⟧ty (λ ()))
closed-iso {τ} fo = FD.Iso-trans (⟦ fo ⟧-iso ∅𝒞) (≡-Iso (𝒟-ty-cong τ (λ ())))

⟦_⟧ctxt-iso : ∀ {Γ} (Γ-fo : first-order-ctxt Γ) → FD.Iso (Fam⟨F⟩ .fobj 𝒞⟦ Γ-fo ⟧ctxt) (𝒟⟦ Γ ⟧ctxt)
⟦ emp ⟧ctxt-iso    = FD.IsIso→Iso Fam⟨F⟩-preserves-terminal
⟦ Γ-fo , fo ⟧ctxt-iso =
  FD.Iso-trans (FD.IsIso→Iso Fam⟨F⟩-preserves-products)
    (FDP.product-preserves-iso ⟦ Γ-fo ⟧ctxt-iso (closed-iso fo))
