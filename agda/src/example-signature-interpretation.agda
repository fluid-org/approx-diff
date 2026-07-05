{-# OPTIONS --postfix-projections --prop --safe #-}

open import Level using (Level; 0ℓ; suc)
open import categories using (Category; HasProducts; HasTerminal; HasCoproducts)
open import prop-setoid using (Setoid)

module example-signature-interpretation
  {o : Level}
  (𝒞 : Category o 0ℓ 0ℓ)
  (𝒞-products : HasProducts 𝒞)
  (𝒞-terminal : HasTerminal 𝒞)
  -- the object approximating the `number` and `approx` sorts; unit and conjunct give it a monoid structure.
  (Approx : Category.obj 𝒞)
  (unit : Category._⇒_ 𝒞 (HasTerminal.witness 𝒞-terminal) Approx)
  (conjunct : Category._⇒_ 𝒞 (HasProducts.prod 𝒞-products Approx Approx) Approx)
  -- what a `number` carries, with zero/add/mult on the index side.
  (Numₛ : Setoid 0ℓ 0ℓ)
  (num-zero : prop-setoid._⇒_ (prop-setoid.𝟙 {0ℓ} {0ℓ}) Numₛ)
  (num-add  : prop-setoid._⇒_ (prop-setoid.⊗-setoid Numₛ Numₛ) Numₛ)
  (num-mult : prop-setoid._⇒_ (prop-setoid.⊗-setoid Numₛ Numₛ) Numₛ)
  where

import fam

private
  module 𝒞m = Category 𝒞
  𝟙-base = HasTerminal.witness 𝒞-terminal
  to-𝟙-base : ∀ {X} → X 𝒞m.⇒ 𝟙-base
  to-𝟙-base = HasTerminal.to-terminal 𝒞-terminal

------------------------------------------------------------------------------
-- Construct the category of first-order approximations
module Fam⟨𝒞⟩ = fam.CategoryOfFamilies 0ℓ 0ℓ 𝒞

open Fam⟨𝒞⟩ using (simple[_,_]; simplef[_,_]) public

cat : Category _ _ _
cat = Fam⟨𝒞⟩.cat

module C = Category cat

open Fam⟨𝒞⟩.products 𝒞-products
  using (products; simple-monoidal)
  renaming (_⊗_ to _×_)
  public

terminal : HasTerminal cat
terminal = Fam⟨𝒞⟩.terminal 𝒞-terminal

coproducts : HasCoproducts cat
coproducts = Fam⟨𝒞⟩.coproducts

module P = HasProducts products

_+_ = HasCoproducts.coprod coproducts
𝟙 = HasTerminal.witness terminal

𝟚 : Category.obj cat
𝟚 = 𝟙 + 𝟙

------------------------------------------------------------------------------

open import Data.Sum using (inj₁; inj₂)
open import prop-setoid using (Setoid; idS)
  renaming (⊗-setoid to _×ₛ_; +-setoid to _+ₛ_; 𝟙 to 𝟙ₛ; _⇒_ to _⇒s_; const to constₛ)
import indexed-family

𝟚ₛ : Setoid 0ℓ 0ℓ
𝟚ₛ = 𝟙ₛ +ₛ 𝟙ₛ

open Fam⟨𝒞⟩.Mor
open Fam⟨𝒞⟩.Obj
open indexed-family.Fam
open indexed-family._⇒f_
open _⇒s_

private
  predicate-transf : ∀ X x y → X .fam .fm x 𝒞m.⇒ 𝟚 .fam .fm y
  predicate-transf X x (inj₁ _) = to-𝟙-base
  predicate-transf X x (inj₂ _) = to-𝟙-base

  predicate-natural : ∀ X {x₁} {x₂} {y₁} {y₂}
    (x-eq : X .idx .Setoid._≈_ x₁ x₂)
    (y-eq : 𝟚ₛ .Setoid._≈_ y₁ y₂) →
    𝒞m._≈_ (𝒞m._∘_ (predicate-transf X x₂ y₂) (X .fam .subst x-eq))
            (𝒞m._∘_ (𝟚 .fam .subst {y₁} {y₂} y-eq) (predicate-transf X x₁ y₁))
  predicate-natural X {x₁} {x₂} {inj₁ x} {inj₁ x₃} x-eq y-eq = HasTerminal.to-terminal-unique 𝒞-terminal _ _
  predicate-natural X {x₁} {x₂} {inj₂ y} {inj₂ y₁} x-eq y-eq = HasTerminal.to-terminal-unique 𝒞-terminal _ _

-- Convert predicates on setoids to ones that forget approximation information
predicate : ∀ {X} → X .idx ⇒s 𝟚ₛ → X C.⇒ 𝟚
predicate f .idxf = f
predicate {X} f .famf .transf x = predicate-transf X x (f .func x)
predicate {X} f .famf .natural {x₁}{x₂} x₁≈x₂ =
  predicate-natural X {y₁ = f .func x₁} x₁≈x₂ (f .func-resp-≈ x₁≈x₂)

-- Helpers for binary functions on simple families
binary2 : ∀ {X Y} → (X × (Y × 𝟙)) C.⇒ (X × Y)
binary2 = P.pair P.p₁ (P.p₁ C.∘ P.p₂)

binary : ∀ {X G} → (simple[ X , G ] × (simple[ X , G ] × 𝟙)) C.⇒ simple[ X ×ₛ X , 𝒞-products .HasProducts.prod G G ]
binary = simple-monoidal C.∘ binary2

open import example-signature (Setoid.Carrier Numₛ)
open import signature
import label

private
  module CP = HasProducts 𝒞-products
  import prop
  open import Data.Product using (proj₁; proj₂)
  open import prop-setoid using (IsEquivalence)

  num-sym : ∀ {x y} → Setoid._≈_ Numₛ x y → Setoid._≈_ Numₛ y x
  num-sym = Setoid.isEquivalence Numₛ .IsEquivalence.sym

BaseInterp0 : Model PFPC[ cat , terminal , products , 𝟚 ] Sig
BaseInterp0 .Model.⟦sort⟧ number = simple[ Numₛ , 𝟙-base ]
BaseInterp0 .Model.⟦sort⟧ label = simple[ label.Label , 𝟙-base ]
BaseInterp0 .Model.⟦sort⟧ approx = simple[ 𝟙ₛ , Approx ]
BaseInterp0 .Model.⟦op⟧ zero = simplef[ num-zero , 𝒞m.id _ ]
BaseInterp0 .Model.⟦op⟧ (lit n) = simplef[ constₛ _ n , 𝒞m.id _ ]
BaseInterp0 .Model.⟦op⟧ add = simplef[ num-add , to-𝟙-base ] C.∘ binary
BaseInterp0 .Model.⟦op⟧ mult = simplef[ num-mult , to-𝟙-base ] C.∘ binary
BaseInterp0 .Model.⟦op⟧ (lbl l) = simplef[ constₛ _ l , 𝒞m.id _ ]
BaseInterp0 .Model.⟦rel⟧ equal-label = predicate label.equal-label C.∘ binary
BaseInterp0 .Model.⟦op⟧ approx-unit = simplef[ idS _ , unit ]
BaseInterp0 .Model.⟦op⟧ approx-mult = simplef[ prop-setoid.to-𝟙 , conjunct ] C.∘ binary

-- The value-carrying model, parameterized by per-argument derivative coefficients for the binary
-- arithmetic primitives: at run values (x, y), the derivative of an operation is c₁ x y on its
-- first argument plus c₂ x y on its second. This is the only part of the interpretation that
-- varies between the models.
module BinDeriv
  (add-c₁ add-c₂ mult-c₁ mult-c₂ : Setoid.Carrier Numₛ → Setoid.Carrier Numₛ → Category._⇒_ 𝒞 Approx Approx)
  (add-c₁-cong : ∀ {x x' y y'} → Setoid._≈_ Numₛ x x' → Setoid._≈_ Numₛ y y' → Category._≈_ 𝒞 (add-c₁ x y) (add-c₁ x' y'))
  (add-c₂-cong : ∀ {x x' y y'} → Setoid._≈_ Numₛ x x' → Setoid._≈_ Numₛ y y' → Category._≈_ 𝒞 (add-c₂ x y) (add-c₂ x' y'))
  (mult-c₁-cong : ∀ {x x' y y'} → Setoid._≈_ Numₛ x x' → Setoid._≈_ Numₛ y y' → Category._≈_ 𝒞 (mult-c₁ x y) (mult-c₁ x' y'))
  (mult-c₂-cong : ∀ {x x' y y'} → Setoid._≈_ Numₛ x x' → Setoid._≈_ Numₛ y y' → Category._≈_ 𝒞 (mult-c₂ x y) (mult-c₂ x' y'))
  where

  private
    op-deriv : (g : prop-setoid._⇒_ (prop-setoid.⊗-setoid Numₛ Numₛ) Numₛ)
               (c₁ c₂ : Setoid.Carrier Numₛ → Setoid.Carrier Numₛ → Category._⇒_ 𝒞 Approx Approx)
               (c₁-cong : ∀ {x x' y y'} → Setoid._≈_ Numₛ x x' → Setoid._≈_ Numₛ y y' → Category._≈_ 𝒞 (c₁ x y) (c₁ x' y'))
               (c₂-cong : ∀ {x x' y y'} → Setoid._≈_ Numₛ x x' → Setoid._≈_ Numₛ y y' → Category._≈_ 𝒞 (c₂ x y) (c₂ x' y')) →
               simple[ Numₛ ×ₛ Numₛ , CP.prod Approx Approx ] C.⇒ simple[ Numₛ , Approx ]
    op-deriv g c₁ c₂ c₁-cong c₂-cong .idxf = g
    op-deriv g c₁ c₂ c₁-cong c₂-cong .famf .transf xy =
      conjunct 𝒞m.∘ CP.pair (c₁ (proj₁ xy) (proj₂ xy) 𝒞m.∘ CP.p₁) (c₂ (proj₁ xy) (proj₂ xy) 𝒞m.∘ CP.p₂)
    op-deriv g c₁ c₂ c₁-cong c₂-cong .famf .natural e =
      𝒞m.≈-trans 𝒞m.id-right (𝒞m.≈-trans
        (𝒞m.∘-cong 𝒞m.≈-refl
          (CP.pair-cong (𝒞m.∘-cong (c₁-cong (num-sym (prop.proj₁ e)) (num-sym (prop.proj₂ e))) 𝒞m.≈-refl)
                        (𝒞m.∘-cong (c₂-cong (num-sym (prop.proj₁ e)) (num-sym (prop.proj₂ e))) 𝒞m.≈-refl)))
        (𝒞m.≈-sym 𝒞m.id-left))

  add-deriv : simple[ Numₛ ×ₛ Numₛ , CP.prod Approx Approx ] C.⇒ simple[ Numₛ , Approx ]
  add-deriv = op-deriv num-add add-c₁ add-c₂ add-c₁-cong add-c₂-cong

  mult-deriv : simple[ Numₛ ×ₛ Numₛ , CP.prod Approx Approx ] C.⇒ simple[ Numₛ , Approx ]
  mult-deriv = op-deriv num-mult mult-c₁ mult-c₂ mult-c₁-cong mult-c₂-cong

  BaseInterp1 : Model PFPC[ cat , terminal , products , 𝟚 ] Sig
  BaseInterp1 .Model.⟦sort⟧ number = simple[ Numₛ , Approx ]
  BaseInterp1 .Model.⟦sort⟧ label = simple[ label.Label , 𝟙-base ]
  BaseInterp1 .Model.⟦sort⟧ approx = simple[ 𝟙ₛ , Approx ]
  BaseInterp1 .Model.⟦op⟧ zero = simplef[ num-zero , unit ]
  BaseInterp1 .Model.⟦op⟧ (lit n) = simplef[ constₛ _ n , unit ]
  BaseInterp1 .Model.⟦op⟧ add = add-deriv C.∘ binary
  BaseInterp1 .Model.⟦op⟧ mult = mult-deriv C.∘ binary
  BaseInterp1 .Model.⟦op⟧ (lbl l) = simplef[ constₛ _ l , 𝒞m.id _ ]
  BaseInterp1 .Model.⟦rel⟧ equal-label = predicate label.equal-label C.∘ binary
  BaseInterp1 .Model.⟦op⟧ approx-unit = simplef[ idS _ , unit ]
  BaseInterp1 .Model.⟦op⟧ approx-mult = simplef[ prop-setoid.to-𝟙 , conjunct ] C.∘ binary

-- The special case with addition's coefficients the identity and multiplication's the Jacobian
-- entries [ ∂/∂x , ∂/∂y ] = [ coeff y , coeff x ].
module Deriv
  (coeff : Setoid.Carrier Numₛ → Category._⇒_ 𝒞 Approx Approx)
  (coeff-cong : ∀ {x y} → Setoid._≈_ Numₛ x y → Category._≈_ 𝒞 (coeff x) (coeff y))
  where

  open BinDeriv (λ _ _ → 𝒞m.id Approx) (λ _ _ → 𝒞m.id Approx)
                (λ _ y → coeff y) (λ x _ → coeff x)
                (λ _ _ → 𝒞m.≈-refl) (λ _ _ → 𝒞m.≈-refl)
                (λ _ e₂ → coeff-cong e₂) (λ e₁ _ → coeff-cong e₁)
                public
