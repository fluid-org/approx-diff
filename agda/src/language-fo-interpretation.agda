{-# OPTIONS --postfix-projections --prop --safe #-}

open import Data.Nat using (ℕ; suc; _+_)
import Data.Fin as Fin
open Fin using (Fin; splitAt)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import categories
  using (Category; HasTerminal; HasProducts; HasCoproducts; HasStrongCoproducts;
         strong-coproducts→coproducts; HasExponentials)
open import functor using (Functor)
open import finite-product-functor using (preserve-chosen-products)
open import finite-coproduct-functor using (preserve-chosen-coproducts)
import polynomial-functor
import language-syntax
open import signature

open Functor

module language-fo-interpretation {ℓ} (Sig : Signature ℓ)
  {o₁ m₁ e₁ o₂ m₂ e₂}
  (𝒞 : Category o₁ m₁ e₁) (𝒞T : HasTerminal 𝒞) (𝒞P : HasProducts 𝒞) (𝒞SC : HasStrongCoproducts 𝒞 𝒞P)
  (𝒞Mu : polynomial-functor.Interp.HasMu 𝒞T 𝒞P 𝒞SC)
  (𝒟 : Category o₂ m₂ e₂) (𝒟T : HasTerminal 𝒟) (𝒟P : HasProducts 𝒟) (𝒟SC : HasStrongCoproducts 𝒟 𝒟P)
  (𝒟E : HasExponentials 𝒟 𝒟P)
  (𝒟Mu : polynomial-functor.Interp.HasMu 𝒟T 𝒟P 𝒟SC)
  (𝒟MuLaws : polynomial-functor.Interp.HasMuLaws 𝒟T 𝒟P 𝒟SC 𝒟Mu)
  (F : Functor 𝒞 𝒟)
  (FT : Category.IsIso 𝒟 (HasTerminal.to-terminal 𝒟T {F .fobj (𝒞T .HasTerminal.witness)}))
  (FP : preserve-chosen-products F 𝒞P 𝒟P)
  (FC : preserve-chosen-coproducts F (strong-coproducts→coproducts 𝒞T 𝒞SC) (strong-coproducts→coproducts 𝒟T 𝒟SC))
  (Fμ : polynomial-functor.Preserves-μ 𝒞T 𝒞P 𝒞SC 𝒟T 𝒟P 𝒟SC 𝒞Mu 𝒟Mu F)
  (𝒞-Sig-model : Model PFPC[ 𝒞 , 𝒞T , 𝒞P ,
                  HasCoproducts.coprod (strong-coproducts→coproducts 𝒞T 𝒞SC)
                    (𝒞T .HasTerminal.witness) (𝒞T .HasTerminal.witness) ] Sig)
  where

open language-syntax Sig
open polynomial-functor using (Poly; Poly-map; extend)

-- Interpretation of the first-order types in 𝒞, with μ-types via the
-- polynomial translation of the first-order witness.
module _ where
  open Category 𝒞
  open HasTerminal 𝒞T renaming (witness to 𝟙)
  open HasProducts 𝒞P
  open HasCoproducts (strong-coproducts→coproducts 𝒞T 𝒞SC)

  module CMu = polynomial-functor.Interp.HasMu 𝒞Mu

  fo-as-poly : ∀ {Δ n} {τ : type (n + Δ)} → first-order τ → (Fin Δ → obj) → Poly 𝒞 n
  fo-as-poly {n = n} (var i)   δ = [ Poly.var , (λ j → Poly.const (δ j)) ] (splitAt n i)
  fo-as-poly unit              δ = Poly.const 𝟙
  fo-as-poly (base s)          δ = Poly.const (𝒞-Sig-model .Model.⟦sort⟧ s)
  fo-as-poly (fo₁ [+] fo₂)     δ = fo-as-poly fo₁ δ Poly.+ fo-as-poly fo₂ δ
  fo-as-poly (fo₁ [×] fo₂)     δ = fo-as-poly fo₁ δ Poly.× fo-as-poly fo₂ δ
  fo-as-poly (μ fo)            δ = Poly.μ (fo-as-poly fo δ)

  𝒞⟦_⟧ty : ∀ {Δ} {τ : type Δ} → first-order τ → (Fin Δ → obj) → obj
  𝒞⟦ var i ⟧ty       δ = δ i
  𝒞⟦ unit ⟧ty        δ = 𝟙
  𝒞⟦ base s ⟧ty      δ = 𝒞-Sig-model .Model.⟦sort⟧ s
  𝒞⟦ fo₁ [×] fo₂ ⟧ty δ = prod (𝒞⟦ fo₁ ⟧ty δ) (𝒞⟦ fo₂ ⟧ty δ)
  𝒞⟦ fo₁ [+] fo₂ ⟧ty δ = coprod (𝒞⟦ fo₁ ⟧ty δ) (𝒞⟦ fo₂ ⟧ty δ)
  𝒞⟦ μ fo ⟧ty        δ = CMu.μ-obj (fo-as-poly {n = 1} fo δ) (λ ())

  𝒞⟦_⟧ctxt : ∀ {Γ} → first-order-ctxt Γ → obj
  𝒞⟦ emp ⟧ctxt    = 𝟙
  𝒞⟦ Γ , τ ⟧ctxt = prod 𝒞⟦ Γ ⟧ctxt (𝒞⟦ τ ⟧ty (λ ()))

private
  module 𝒟 = Category 𝒟
  module 𝒞CPm = HasCoproducts (strong-coproducts→coproducts 𝒞T 𝒞SC)
  module 𝒟CPm = HasCoproducts (strong-coproducts→coproducts 𝒟T 𝒟SC)
  module 𝒟Pm = HasProducts 𝒟P
  module PM = polynomial-functor.MuIso 𝒟T 𝒟P 𝒟SC 𝒟Mu 𝒟MuLaws

𝒞Bool = 𝒞CPm.coprod (𝒞T .HasTerminal.witness) (𝒞T .HasTerminal.witness)
𝒟Bool = 𝒟CPm.coprod (𝒟T .HasTerminal.witness) (𝒟T .HasTerminal.witness)

Bool-iso : 𝒟.Iso (F .fobj 𝒞Bool) 𝒟Bool
Bool-iso =
  𝒟.Iso-trans (𝒟.Iso-sym (𝒟.IsIso→Iso FC))
              (𝒟CPm.coproduct-preserve-iso (𝒟.IsIso→Iso FT) (𝒟.IsIso→Iso FT))

𝒟-Sig-model : Model PFPC[ 𝒟 , 𝒟T , 𝒟P , 𝒟Bool ] Sig
𝒟-Sig-model = transport-model Sig F FT FP (Bool-iso .𝒟.Iso.fwd) 𝒞-Sig-model

open import language-interpretation Sig 𝒟 𝒟T 𝒟P 𝒟SC 𝒟E 𝒟Mu 𝒟-Sig-model
  renaming (⟦_⟧ty to 𝒟⟦_⟧ty; ⟦_⟧ctxt to 𝒟⟦_⟧ctxt; ⟦_⟧tm to 𝒟⟦_⟧tm; as-poly to 𝒟-as-poly)
  using ()
  public

-- The polynomial translations of a first-order type agree componentwise, up to
-- the isomorphisms witnessing that F preserves the first-order structure.
fo-poly-iso : ∀ {Δ n} {τ : type (n + Δ)} (fo : first-order τ)
              (δ𝒞 : Fin Δ → Category.obj 𝒞) (δ𝒟 : Fin Δ → Category.obj 𝒟) →
              (∀ i → 𝒟.Iso (F .fobj (δ𝒞 i)) (δ𝒟 i)) →
              PM.PolyIso (Poly-map F (fo-as-poly {Δ} {n} fo δ𝒞)) (𝒟-as-poly {Δ} {n} τ δ𝒟)
fo-poly-iso {n = n} (var i) δ𝒞 δ𝒟 es with splitAt n i
... | inj₁ k = PM.pm-iso-var k
... | inj₂ j = PM.pm-iso-const (es j)
fo-poly-iso unit          δ𝒞 δ𝒟 es = PM.pm-iso-const (𝒟.IsIso→Iso FT)
fo-poly-iso (base s)      δ𝒞 δ𝒟 es = PM.pm-iso-const 𝒟.Iso-refl
fo-poly-iso (fo₁ [+] fo₂) δ𝒞 δ𝒟 es = PM.pm-iso-sum (fo-poly-iso fo₁ δ𝒞 δ𝒟 es) (fo-poly-iso fo₂ δ𝒞 δ𝒟 es)
fo-poly-iso (fo₁ [×] fo₂) δ𝒞 δ𝒟 es = PM.pm-iso-prod (fo-poly-iso fo₁ δ𝒞 δ𝒟 es) (fo-poly-iso fo₂ δ𝒞 δ𝒟 es)
fo-poly-iso (μ fo)        δ𝒞 δ𝒟 es = PM.pm-iso-μ (fo-poly-iso fo δ𝒞 δ𝒟 es)

-- Every first-order type's interpretation in 𝒟 is isomorphic to the image
-- under F of its interpretation in 𝒞; μ-types via preservation of μ and the
-- componentwise isomorphism of the two polynomial translations.
⟦_⟧-iso : ∀ {Δ} {τ : type Δ} (fo : first-order τ)
          {δ𝒞 : Fin Δ → Category.obj 𝒞} {δ𝒟 : Fin Δ → Category.obj 𝒟} →
          (∀ i → 𝒟.Iso (F .fobj (δ𝒞 i)) (δ𝒟 i)) →
          𝒟.Iso (F .fobj (𝒞⟦ fo ⟧ty δ𝒞)) (𝒟⟦ τ ⟧ty δ𝒟)
⟦ var i ⟧-iso es       = es i
⟦ unit ⟧-iso es        = 𝒟.IsIso→Iso FT
⟦ base s ⟧-iso es      = 𝒟.Iso-refl
⟦ fo₁ [×] fo₂ ⟧-iso es =
  𝒟.Iso-trans (𝒟.IsIso→Iso FP) (𝒟Pm.product-preserves-iso (⟦ fo₁ ⟧-iso es) (⟦ fo₂ ⟧-iso es))
⟦ fo₁ [+] fo₂ ⟧-iso es =
  𝒟.Iso-trans (𝒟.Iso-sym (𝒟.IsIso→Iso FC)) (𝒟CPm.coproduct-preserve-iso (⟦ fo₁ ⟧-iso es) (⟦ fo₂ ⟧-iso es))
⟦ μ fo ⟧-iso {δ𝒞} {δ𝒟} es =
  𝒟.Iso-trans (Fμ (fo-as-poly fo δ𝒞) (λ ()))
              (PM.pm-μ-iso (fo-poly-iso fo δ𝒞 δ𝒟 es) (λ ()))

⟦_⟧ctxt-iso : ∀ {Γ} (Γ-fo : first-order-ctxt Γ) → 𝒟.Iso (F .fobj 𝒞⟦ Γ-fo ⟧ctxt) 𝒟⟦ Γ ⟧ctxt
⟦ emp ⟧ctxt-iso    = 𝒟.IsIso→Iso FT
⟦ Γ , τ ⟧ctxt-iso =
  𝒟.Iso-trans (𝒟.IsIso→Iso FP) (𝒟Pm.product-preserves-iso ⟦ Γ ⟧ctxt-iso (⟦ τ ⟧-iso (λ ())))
