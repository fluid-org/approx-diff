{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (suc; _⊔_; 0ℓ)
open import prop-setoid using (module ≈-Reasoning; IsEquivalence)
open import basics using (IsPreorder; IsMeet; IsTop; IsResidual; module ≤-Reasoning; IsJoin; IsBigJoin)
open import categories using (Category; HasProducts; HasExponentials; HasWeakExponentials;
                              exponentials→weak; HasCoproducts; HasTerminal; IsTerminal)
open import functor using (Functor; HasColimits; Colimit; IsColimit; _∘F_; NatTrans; ≃-NatTrans)
open import monad using (Monad; MonadFunctor)
open import predicate-system using (PredicateSystem; FunctorPred; MonadPred)
open import finite-product-functor using (preserve-chosen-products; module preserve-chosen-products-consequences)

-- FIXME: refactor this into
--   1. glueing with predicates over 𝒞 directly
--   2. pullback of PredicateSystems along product preserving functors

module glueing-simple {o₁ m₁ e₁ o₂ m₂ e₂}
  (𝒞 : Category o₁ m₁ e₁)
  (𝒟 : Category o₂ m₂ e₂) (𝒟P : HasProducts 𝒟)
  (𝒟-predicates : PredicateSystem 𝒟 𝒟P)
  (F : Functor 𝒞 𝒟) where

private
  module 𝒞 = Category 𝒞
  module 𝒟 = Category 𝒟
  module 𝒟P = HasProducts 𝒟P
open Functor
open PredicateSystem 𝒟-predicates

⊑-refl : ∀ {X}{P : Predicate X} → P ⊑ P
⊑-refl = ⊑-isPreorder .IsPreorder.refl

record Obj : Set (suc o₁ ⊔ suc m₁ ⊔ suc e₁ ⊔ suc o₂ ⊔ suc m₂ ⊔ suc e₂) where
  no-eta-equality
  field
    carrier : 𝒞.obj
    pred    : Predicate (F .fobj carrier)
open Obj

record _=>_ (X Y : Obj) : Set (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂) where
  no-eta-equality
  field
    morph : X .carrier 𝒞.⇒ Y .carrier
    presv : X .pred ⊑ (Y .pred [ F .fmor morph ])
open _=>_

record _≃m_ {X Y} (f g : X => Y) : Prop (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂) where
  no-eta-equality
  field
    f≃f : f .morph 𝒞.≈ g .morph
open _≃m_

id : ∀ X → X => X
id X .morph = 𝒞.id _
id X .presv = begin
     X .pred                       ≤⟨ []-id ⟩
     X .pred [ 𝒟.id _ ]           ≤⟨ []-cong (𝒟.≈-sym (F .fmor-id)) ⟩
     X .pred [ F .fmor (𝒞.id _) ]
  ∎
  where open ≤-Reasoning ⊑-isPreorder

_∘_ : ∀ {X Y Z} → Y => Z → X => Y → X => Z
(f ∘ g) .morph = f .morph 𝒞.∘ g .morph
_∘_ {X}{Y}{Z} f g .presv = begin
    X .pred                                                 ≤⟨ g .presv ⟩
    Y .pred [ F .fmor (g .morph) ]                          ≤⟨ (f .presv) [ F .fmor (g .morph) ]m ⟩
    (Z .pred [ F .fmor (f .morph) ]) [ F .fmor (g .morph) ] ≤⟨ []-comp _ _ ⟩
    Z .pred [ F .fmor (f .morph) 𝒟.∘ F .fmor (g .morph) ]  ≤⟨ []-cong (𝒟.≈-sym (F .fmor-comp _ _)) ⟩
    Z .pred [ F .fmor (f .morph 𝒞.∘ g .morph) ]
  ∎
  where open ≤-Reasoning ⊑-isPreorder

cat : Category (suc o₁ ⊔ suc m₁ ⊔ suc e₁ ⊔ suc o₂ ⊔ suc m₂ ⊔ suc e₂) (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂) (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂)
cat .Category.obj = Obj
cat .Category._⇒_ = _=>_
cat .Category._≈_ = _≃m_
cat .Category.isEquiv .IsEquivalence.refl .f≃f = 𝒞.≈-refl
cat .Category.isEquiv .IsEquivalence.sym e .f≃f = 𝒞.≈-sym (e .f≃f)
cat .Category.isEquiv .IsEquivalence.trans e₁ e₂ .f≃f = 𝒞.≈-trans (e₁ .f≃f) (e₂ .f≃f)
cat .Category.id = id
cat .Category._∘_ = _∘_
cat .Category.∘-cong e₁ e₂ .f≃f = 𝒞.∘-cong (e₁ .f≃f) (e₂ .f≃f)
cat .Category.id-left .f≃f = 𝒞.id-left
cat .Category.id-right .f≃f = 𝒞.id-right
cat .Category.assoc f g h .f≃f = 𝒞.assoc (f .morph) (g .morph) (h .morph)

project : Functor cat 𝒞
project .fobj x = x .carrier
project .fmor f = f .morph
project .fmor-cong eq = eq .f≃f
project .fmor-id = IsEquivalence.refl 𝒞.isEquiv
project .fmor-comp f g = IsEquivalence.refl 𝒞.isEquiv

-- Binary Coproducts
module coproducts (CP : HasCoproducts 𝒞) where

  private
    module CP = HasCoproducts CP

  _[+]_ : Obj → Obj → Obj
  (X [+] Y) .carrier = CP.coprod (X .carrier) (Y .carrier)
  (X [+] Y) .pred = (X .pred ⟨ F .fmor CP.in₁ ⟩) ++ (Y .pred ⟨ F .fmor CP.in₂ ⟩)

  in₁ : ∀ {X Y} → X => (X [+] Y)
  in₁ .morph = CP.in₁
  in₁ {X} {Y} .presv = begin
      X .pred
    ≤⟨ unit _ ⟩
      X .pred ⟨ F .fmor CP.in₁ ⟩ [ F .fmor CP.in₁ ]
    ≤⟨ ++-isJoin .IsJoin.inl [ _ ]m ⟩
      ((X .pred ⟨ F .fmor CP.in₁ ⟩) ++ (Y .pred ⟨ F .fmor CP.in₂ ⟩)) [ F .fmor CP.in₁ ]
    ∎
    where open ≤-Reasoning ⊑-isPreorder

  in₂ : ∀ {X Y} → Y => (X [+] Y)
  in₂ .morph = CP.in₂
  in₂ {X} {Y} .presv = begin
      Y .pred
    ≤⟨ unit _ ⟩
      Y .pred ⟨ F .fmor CP.in₂ ⟩ [ F .fmor CP.in₂ ]
    ≤⟨ ++-isJoin .IsJoin.inr [ _ ]m ⟩
      ((X .pred ⟨ F .fmor CP.in₁ ⟩) ++ (Y .pred ⟨ F .fmor CP.in₂ ⟩)) [ F .fmor CP.in₂ ]
    ∎
    where open ≤-Reasoning ⊑-isPreorder

  copair : ∀ {X Y Z} → X => Z → Y => Z → (X [+] Y) => Z
  copair f g .morph = CP.copair (f .morph) (g .morph)
  copair {X} {Y} {Z} f g .presv = begin
      (X .pred ⟨ F .fmor CP.in₁ ⟩) ++ (Y .pred ⟨ F .fmor CP.in₂ ⟩)
    ≤⟨ IsJoin.mono ++-isJoin (f .presv ⟨ _ ⟩m) (g .presv ⟨ _ ⟩m) ⟩
      (Z .pred [ F .fmor (f .morph) ] ⟨ F .fmor CP.in₁ ⟩) ++ (Z .pred [ F .fmor (g .morph) ] ⟨ F .fmor CP.in₂ ⟩)
    ≤⟨ IsJoin.mono ++-isJoin ([]-cong (F .fmor-cong (𝒞.≈-sym (CP.copair-in₁ _ _))) ⟨ _ ⟩m)
                             ([]-cong (F .fmor-cong (𝒞.≈-sym (CP.copair-in₂ _ _))) ⟨ _ ⟩m) ⟩
      (Z .pred [ F .fmor (CP.copair (f .morph) (g .morph) 𝒞.∘ CP.in₁) ] ⟨ F .fmor CP.in₁ ⟩)
        ++
      (Z .pred [ F .fmor (CP.copair (f .morph) (g .morph) 𝒞.∘ CP.in₂) ] ⟨ F .fmor CP.in₂ ⟩)
    ≤⟨ IsJoin.mono ++-isJoin ([]-cong (F .fmor-comp _ _) ⟨ _ ⟩m)
                             ([]-cong (F .fmor-comp _ _) ⟨ _ ⟩m) ⟩
      (Z .pred [ F .fmor (CP.copair (f .morph) (g .morph)) 𝒟.∘ F .fmor CP.in₁ ] ⟨ F .fmor CP.in₁ ⟩)
        ++
      (Z .pred [ F .fmor (CP.copair (f .morph) (g .morph)) 𝒟.∘ F .fmor CP.in₂ ] ⟨ F .fmor CP.in₂ ⟩)
    ≤⟨ IsJoin.mono ++-isJoin (([]-comp⁻¹ _ _) ⟨ _ ⟩m) (([]-comp⁻¹ _ _) ⟨ _ ⟩m) ⟩
      (Z .pred [ F .fmor (CP.copair (f .morph) (g .morph)) ] [ F .fmor CP.in₁ ] ⟨ F .fmor CP.in₁ ⟩)
        ++
      (Z .pred [ F .fmor (CP.copair (f .morph) (g .morph)) ] [ F .fmor CP.in₂ ] ⟨ F .fmor CP.in₂ ⟩)
    ≤⟨ IsJoin.[_,_] ++-isJoin (counit _) (counit _) ⟩
      Z .pred [ F .fmor (CP.copair (f .morph) (g .morph)) ]
    ∎
    where open ≤-Reasoning ⊑-isPreorder

  coproducts : HasCoproducts cat
  coproducts .HasCoproducts.coprod = _[+]_
  coproducts .HasCoproducts.in₁ = in₁
  coproducts .HasCoproducts.in₂ = in₂
  coproducts .HasCoproducts.copair = copair
  coproducts .HasCoproducts.copair-cong e₁ e₂ .f≃f = CP.copair-cong (e₁ .f≃f) (e₂ .f≃f)
  coproducts .HasCoproducts.copair-in₁ f g .f≃f = CP.copair-in₁ (f .morph) (g .morph)
  coproducts .HasCoproducts.copair-in₂ f g .f≃f = CP.copair-in₂ (f .morph) (g .morph)
  coproducts .HasCoproducts.copair-ext f .f≃f = CP.copair-ext (f .morph)

-- Products and exponentials. The construction consumes only the weak exponential structure of the
-- base (the one law used is the computation rule, in lambda's preservation proof), so it is stated
-- weakly; the strong wrapper below copies the base's remaining laws across.
module products-and-weak-exponentials
         (T : HasTerminal 𝒞) (P : HasProducts 𝒞) (E : HasWeakExponentials 𝒞 P)
         (FP : preserve-chosen-products F P 𝒟P)
     where

  private
    module T = HasTerminal T
    module P = HasProducts P
    module E = HasWeakExponentials E

  open preserve-chosen-products-consequences F P 𝒟P FP

  open IsMeet

  -- Terminal
  [⊤] : Obj
  [⊤] .carrier = T.witness
  [⊤] .pred = TT

  to-terminal : ∀ {X} → X => [⊤]
  to-terminal .morph = T.is-terminal .IsTerminal.to-terminal
  to-terminal {X} .presv = begin
      X .pred
    ≤⟨ TT-isTop .IsTop.≤-top ⟩
      TT
    ≤⟨ []-TT ⟩
      TT [ F .fmor (T.is-terminal .IsTerminal.to-terminal) ]
    ∎
    where open ≤-Reasoning ⊑-isPreorder

  terminal : HasTerminal cat
  terminal .HasTerminal.witness = [⊤]
  terminal .HasTerminal.is-terminal .IsTerminal.to-terminal = to-terminal
  terminal .HasTerminal.is-terminal .IsTerminal.to-terminal-ext f .f≃f =
    T.is-terminal .IsTerminal.to-terminal-ext (f .morph)

  -- Products
  _[×]_ : Obj → Obj → Obj
  (X [×] Y) .carrier = P.prod (X .carrier) (Y .carrier)
  (X [×] Y) .pred = (X .pred [ F .fmor P.p₁ ]) && (Y .pred [ F .fmor P.p₂ ])

  p₁ : ∀ {X Y} → (X [×] Y) => X
  p₁ .morph = P.p₁
  p₁ .presv = &&-isMeet .π₁

  p₂ : ∀ {X Y} → (X [×] Y) => Y
  p₂ .morph = P.p₂
  p₂ .presv = &&-isMeet .π₂

  pair : ∀ {X Y Z} → X => Y → X => Z → X => (Y [×] Z)
  pair f g .morph = P.pair (f .morph) (g .morph)
  pair {X} {Y} {Z} f g .presv = begin
      X .pred
    ≤⟨ &&-isMeet .⟨_,_⟩ (f .presv) (g .presv) ⟩
      (Y .pred [ F .fmor (f .morph) ]) && (Z .pred [ F .fmor (g .morph) ])
    ≤⟨ mono &&-isMeet ([]-cong (F .fmor-cong (𝒞.≈-sym (P.pair-p₁ _ _)))) ([]-cong (F .fmor-cong (𝒞.≈-sym (P.pair-p₂ _ _)))) ⟩
      (Y .pred [ F .fmor (P.p₁ 𝒞.∘ P.pair (f .morph) (g .morph)) ]) && (Z .pred [ F .fmor (P.p₂ 𝒞.∘ P.pair (f .morph) (g .morph)) ])
    ≤⟨ mono &&-isMeet ([]-cong (F .fmor-comp _ _)) ([]-cong (F .fmor-comp _ _)) ⟩
      (Y .pred [ F .fmor P.p₁ 𝒟.∘ F .fmor (P.pair (f .morph) (g .morph)) ]) && (Z .pred [ F .fmor P.p₂ 𝒟.∘ F .fmor (P.pair (f .morph) (g .morph)) ])
    ≤⟨ mono &&-isMeet ([]-comp⁻¹ _ _) ([]-comp⁻¹ _ _) ⟩
      ((Y .pred [ F .fmor P.p₁ ]) [ F .fmor (P.pair (f .morph) (g .morph)) ]) && ((Z .pred [ F .fmor P.p₂ ]) [ F .fmor (P.pair (f .morph) (g .morph)) ])
    ≤⟨ []-&& ⟩
      ((Y .pred [ F .fmor P.p₁ ]) && (Z .pred [ F .fmor P.p₂ ])) [ F .fmor (P.pair (f .morph) (g .morph)) ]
    ∎ where open ≤-Reasoning ⊑-isPreorder

  products : HasProducts cat
  products .HasProducts.prod = _[×]_
  products .HasProducts.p₁ = p₁
  products .HasProducts.p₂ = p₂
  products .HasProducts.pair = pair
  products .HasProducts.pair-cong e₁ e₂ .f≃f = P.pair-cong (e₁ .f≃f) (e₂ .f≃f)
  products .HasProducts.pair-p₁ f g .f≃f = P.pair-p₁ (f .morph) (g .morph)
  products .HasProducts.pair-p₂ f g .f≃f = P.pair-p₂ (f .morph) (g .morph)
  products .HasProducts.pair-ext f .f≃f = P.pair-ext (f .morph)

  -- Exponentials
  _[→]_ : Obj → Obj → Obj
  (X [→] Y) .carrier = E.exp (X .carrier) (Y .carrier)
  (X [→] Y) .pred = ⋀ (((X .pred [ F .fmor P.p₂ ]) ==> (Y .pred [ F .fmor E.eval ])) [ mul ])

  eval : ∀ {X Y} → ((X [→] Y) [×] X) => Y
  eval .morph = E.eval
  eval {X} {Y} .presv = begin
      (⋀ (((X .pred [ F .fmor P.p₂ ]) ==> (Y .pred [ F .fmor E.eval ])) [ mul ]) [ F .fmor P.p₁ ]) && (X .pred [ F .fmor P.p₂ ])
    ≤⟨ mono &&-isMeet ([]-cong F-p₁') ⊑-refl ⟩
      (⋀ (((X .pred [ F .fmor P.p₂ ]) ==> (Y .pred [ F .fmor E.eval ])) [ mul ]) [ 𝒟P.p₁ 𝒟.∘ mul⁻¹ ]) && (X .pred [ F .fmor P.p₂ ])
    ≤⟨ mono &&-isMeet ([]-comp⁻¹ _ _) ⊑-refl ⟩
      ((⋀ (((X .pred [ F .fmor P.p₂ ]) ==> (Y .pred [ F .fmor E.eval ])) [ mul ]) [ 𝒟P.p₁ ]) [ mul⁻¹ ]) && (X .pred [ F .fmor P.p₂ ])
    ≤⟨ mono &&-isMeet (⋀-eval [ _ ]m) ⊑-refl ⟩
      ((((X .pred [ F .fmor P.p₂ ]) ==> (Y .pred [ F .fmor E.eval ])) [ mul ]) [ mul⁻¹ ]) && (X .pred [ F .fmor P.p₂ ])
    ≤⟨ mono &&-isMeet ([]-comp _ _) ⊑-refl ⟩
      (((X .pred [ F .fmor P.p₂ ]) ==> (Y .pred [ F .fmor E.eval ])) [ mul 𝒟.∘ mul⁻¹ ]) && (X .pred [ F .fmor P.p₂ ])
    ≤⟨ mono &&-isMeet ([]-cong mul-inv) ⊑-refl ⟩
      (((X .pred [ F .fmor P.p₂ ]) ==> (Y .pred [ F .fmor E.eval ])) [ 𝒟.id _ ]) && (X .pred [ F .fmor P.p₂ ])
    ≤⟨ mono &&-isMeet []-id⁻¹ ⊑-refl ⟩
      ((X .pred [ F .fmor P.p₂ ]) ==> (Y .pred [ F .fmor E.eval ])) && (X .pred [ F .fmor P.p₂ ])
    ≤⟨ ==>-residual .IsResidual.eval ⟩
      Y .pred [ F .fmor E.eval ]
    ∎
    where open ≤-Reasoning ⊑-isPreorder

  lambda : ∀ {X Y Z} → (X [×] Y) => Z → X => (Y [→] Z)
  lambda f .morph = E.lambda (f .morph)
  lambda {X} {Y} {Z} f .presv = begin
      X .pred
    ≤⟨ ⋀-lambda lemma ⟩
      ⋀ ((((Y .pred [ F .fmor P.p₂ ]) ==> (Z .pred [ F .fmor E.eval ])) [ mul ]) [ 𝒟P.prod-m (F .fmor (E.lambda (f .morph))) (𝒟.id _) ])
    ≤⟨ ⋀-[] ⟩
      ⋀ (((Y .pred [ F .fmor P.p₂ ]) ==> (Z .pred [ F .fmor E.eval ])) [ mul ]) [ F .fmor (E.lambda (f .morph)) ]
    ∎
    where
      lemma : (X .pred [ 𝒟P.p₁ ]) ⊑ ((((Y .pred [ F .fmor P.p₂ ]) ==> (Z .pred [ F .fmor E.eval ])) [ mul ]) [ 𝒟P.prod-m (F .fmor (E.lambda (f .morph))) (𝒟.id _) ])
      lemma = begin
          X .pred [ 𝒟P.p₁ ]
        ≤⟨ []-cong (𝒟.≈-sym F-p₁) ⟩
          X .pred [ F .fmor P.p₁ 𝒟.∘ mul ]
        ≤⟨ []-comp⁻¹ _ _ ⟩
          (X .pred [ F .fmor P.p₁ ]) [ mul ]
        ≤⟨ (==>-residual .IsResidual.lambda (f .presv)) [ _ ]m ⟩
          ((Y .pred [ F .fmor P.p₂ ]) ==> (Z .pred [ F .fmor (f .morph) ])) [ mul ]
        ≤⟨ IsResidual.-∙-mono ==>-residual ([]-cong (F .fmor-cong 𝒞.id-left)) ⊑-refl [ mul ]m ⟩
          ((Y .pred [ F .fmor (𝒞.id _ 𝒞.∘ P.p₂) ]) ==> (Z .pred [ F .fmor (f .morph) ])) [ mul ]
        ≤⟨ IsResidual.-∙-mono ==>-residual ([]-cong (F .fmor-cong (P.pair-p₂ _ _))) ([]-cong (F .fmor-cong (𝒞.≈-sym (E.eval-lambda _)))) [ mul ]m ⟩
          ((Y .pred [ F .fmor (P.p₂ 𝒞.∘ P.prod-m (E.lambda (f .morph)) (𝒞.id _)) ]) ==> (Z .pred [ F .fmor (E.eval 𝒞.∘ P.prod-m (E.lambda (f .morph)) (𝒞.id _)) ])) [ mul ]
        ≤⟨ IsResidual.-∙-mono ==>-residual ([]-cong (𝒟.≈-sym (F .fmor-comp _ _))) ([]-cong (F .fmor-comp _ _)) [ mul ]m ⟩
          ((Y .pred [ F .fmor P.p₂ 𝒟.∘ F .fmor (P.prod-m (E.lambda (f .morph)) (𝒞.id _)) ]) ==> (Z .pred [ F .fmor E.eval 𝒟.∘ F .fmor (P.prod-m (E.lambda (f .morph)) (𝒞.id _)) ])) [ mul ]
        ≤⟨ IsResidual.-∙-mono ==>-residual ([]-comp _ _) ([]-comp⁻¹ _ _) [ mul ]m ⟩
          (((Y .pred [ F .fmor P.p₂ ])  [ F .fmor (P.prod-m (E.lambda (f .morph)) (𝒞.id _)) ]) ==> ((Z .pred [ F .fmor E.eval ]) [ F .fmor (P.prod-m (E.lambda (f .morph)) (𝒞.id _)) ])) [ mul ]
        ≤⟨ []-==> [ mul ]m ⟩
          (((Y .pred [ F .fmor P.p₂ ]) ==> (Z .pred [ F .fmor E.eval ])) [ F .fmor (P.prod-m (E.lambda (f .morph)) (𝒞.id _)) ]) [ mul ]
        ≤⟨ []-comp _ _ ⟩
          ((Y .pred [ F .fmor P.p₂ ]) ==> (Z .pred [ F .fmor E.eval ])) [ F .fmor (P.prod-m (E.lambda (f .morph)) (𝒞.id _)) 𝒟.∘ mul ]
        ≤⟨ []-cong mul-natural ⟩
          ((Y .pred [ F .fmor P.p₂ ]) ==> (Z .pred [ F .fmor E.eval ])) [ mul 𝒟.∘ 𝒟P.prod-m (F .fmor (E.lambda (f .morph))) (F .fmor (𝒞.id _)) ]
        ≤⟨ []-cong (𝒟.∘-cong 𝒟.≈-refl (𝒟P.prod-m-cong 𝒟.≈-refl (F .fmor-id))) ⟩
          ((Y .pred [ F .fmor P.p₂ ]) ==> (Z .pred [ F .fmor E.eval ])) [ mul 𝒟.∘ 𝒟P.prod-m (F .fmor (E.lambda (f .morph))) (𝒟.id _) ]
        ≤⟨ []-comp⁻¹ _ _ ⟩
          (((Y .pred [ F .fmor P.p₂ ]) ==> (Z .pred [ F .fmor E.eval ])) [ mul ]) [ 𝒟P.prod-m (F .fmor (E.lambda (f .morph))) (𝒟.id _) ]
        ∎
        where open ≤-Reasoning ⊑-isPreorder
      open ≤-Reasoning ⊑-isPreorder

  weak-exponentials : HasWeakExponentials cat products
  weak-exponentials .HasWeakExponentials.exp = _[→]_
  weak-exponentials .HasWeakExponentials.eval = eval
  weak-exponentials .HasWeakExponentials.lambda = lambda
  weak-exponentials .HasWeakExponentials.lambda-cong e .f≃f = E.lambda-cong (e .f≃f)
  weak-exponentials .HasWeakExponentials.eval-lambda f .f≃f = E.eval-lambda (f .morph)

module products-and-exponentials
         (T : HasTerminal 𝒞) (P : HasProducts 𝒞) (E : HasExponentials 𝒞 P)
         (FP : preserve-chosen-products F P 𝒟P)
     where

  open products-and-weak-exponentials T P (exponentials→weak E) FP public

  private
    module E = HasExponentials E

  exponentials : HasExponentials cat products
  exponentials .HasExponentials.exp = _[→]_
  exponentials .HasExponentials.eval = eval
  exponentials .HasExponentials.lambda = lambda
  exponentials .HasExponentials.lambda-cong e .f≃f = E.lambda-cong (e .f≃f)
  exponentials .HasExponentials.eval-lambda f .f≃f = E.eval-lambda (f .morph)
  exponentials .HasExponentials.lambda-ext f .f≃f = E.lambda-ext (f .morph)

-- Colimits
--
-- FIXME: be less specific about the universe levels here
module colimits (𝒮 : Category 0ℓ 0ℓ 0ℓ) (𝒞-colimits : HasColimits 𝒮 𝒞) where

  private
    module 𝒮 = Category 𝒮
  open Colimit
  open IsColimit
  open NatTrans
  open ≃-NatTrans

  colimits : HasColimits 𝒮 cat
  colimits D .apex .carrier = 𝒞-colimits (project ∘F D) .apex
  colimits D .apex .pred =
    ⋁ 𝒮.obj λ i → (D .fobj i .pred) ⟨ (F .fmor (𝒞-colimits (project ∘F D) .cocone .transf i)) ⟩
  colimits D .cocone .transf i .morph = 𝒞-colimits (project ∘F D) .cocone .transf i
  colimits D .cocone .transf i .presv = begin
      D .fobj i .pred
    ≤⟨ unit _ ⟩
      D .fobj i .pred ⟨ F .fmor (𝒞-colimits (project ∘F D) .cocone .transf i) ⟩
         [ F .fmor (𝒞-colimits (project ∘F D) .cocone .transf i) ]
    ≤⟨ (IsBigJoin.upper ⋁-isJoin _ _ i) [ _ ]m ⟩
      (⋁ 𝒮.obj (λ i₁ → D .fobj i₁ .pred ⟨ F .fmor (𝒞-colimits (project ∘F D) .cocone .transf i₁) ⟩)
         [ F .fmor (𝒞-colimits (project ∘F D) .cocone .transf i) ])
    ∎
    where open ≤-Reasoning ⊑-isPreorder
  colimits D .cocone .natural f .f≃f = 𝒞-colimits (project ∘F D) .cocone .natural f
  colimits D .isColimit .colambda X α .morph =
    𝒞-colimits (project ∘F D) .isColimit .colambda (X .carrier)
      (record { transf = λ i → α .transf i .morph
              ; natural = λ f → α .natural f .f≃f })
  colimits D .isColimit .colambda X α .presv = begin
      ⋁ 𝒮.obj (λ i → D .fobj i .pred ⟨ F .fmor (inj i) ⟩)
    ≤⟨ IsBigJoin.mono ⋁-isJoin (λ i → α .transf i .presv ⟨ _ ⟩m) ⟩
      ⋁ 𝒮.obj (λ i → X .pred [ F .fmor (α .transf i .morph) ] ⟨ F .fmor (inj i) ⟩)
    ≤⟨ IsBigJoin.mono ⋁-isJoin (λ i → ([]-cong (F .fmor-cong (𝒞.≈-sym (𝒞-colimits _ .isColimit .colambda-coeval _ _ .transf-eq i)))) ⟨ _ ⟩m) ⟩
      ⋁ 𝒮.obj (λ i → X .pred [ F .fmor (elim 𝒞.∘ inj i) ] ⟨ F .fmor (inj i) ⟩)
    ≤⟨ IsBigJoin.mono ⋁-isJoin (λ i → ([]-cong (F .fmor-comp _ _)) ⟨ _ ⟩m) ⟩
      ⋁ 𝒮.obj (λ i → X .pred [ F .fmor elim 𝒟.∘ F. fmor (inj i) ] ⟨ F .fmor (inj i) ⟩)
    ≤⟨ IsBigJoin.mono ⋁-isJoin (λ i → []-comp⁻¹ _ _ ⟨ _ ⟩m) ⟩
      ⋁ 𝒮.obj (λ i → X .pred [ F .fmor elim ] [ F. fmor (inj i) ] ⟨ F .fmor (inj i) ⟩)
    ≤⟨ IsBigJoin.mono ⋁-isJoin (λ i → counit _) ⟩
      ⋁ 𝒮.obj (λ i → X .pred [ F .fmor elim ])
    ≤⟨ IsBigJoin.least ⋁-isJoin _ _ _ (λ i → ⊑-isPreorder .IsPreorder.refl) ⟩
      X .pred [ F .fmor elim ]
    ∎
    where open ≤-Reasoning ⊑-isPreorder
          elim = colambda (𝒞-colimits (project ∘F D) .isColimit) (X .carrier) (record { transf = λ i → α .transf i .morph ; natural = _ })
          inj = 𝒞-colimits (project ∘F D) .cocone .transf
  colimits D .isColimit .colambda-cong α≃β .f≃f =
    𝒞-colimits (project ∘F D) .isColimit .colambda-cong (record { transf-eq = λ i → α≃β .transf-eq i .f≃f })
  colimits D .isColimit .colambda-coeval X α .transf-eq i .f≃f =
    𝒞-colimits (project ∘F D) .isColimit .colambda-coeval (X .carrier) _ .transf-eq i
  colimits D .isColimit .colambda-ext X f .f≃f =
    begin
      𝒞-colimits (project ∘F D) .isColimit .colambda (X .carrier)
         (record { transf = λ i → f .morph 𝒞.∘ 𝒞-colimits (project ∘F D) .cocone .transf i; natural = _ })
    ≈⟨ 𝒞-colimits (project ∘F D) .isColimit .colambda-cong (record { transf-eq = λ x → 𝒞.≈-refl }) ⟩
      𝒞-colimits (project ∘F D) .isColimit .colambda (X .carrier) (functor.constFmor (f .morph) functor.∘ 𝒞-colimits (project ∘F D) .cocone)
    ≈⟨ 𝒞-colimits (project ∘F D) .isColimit .colambda-ext (X .carrier) (f .morph) ⟩
      f .morph
    ∎
    where open ≈-Reasoning 𝒞.isEquiv

-- If we have an endofunctor with a lifting, then we can transfer it to the glued category
module endofunctor
         (𝒞M : Functor 𝒞 𝒞)
         (𝒟M : Functor 𝒟 𝒟)
         (α  : NatTrans (F ∘F 𝒞M) (𝒟M ∘F F))
         (MP : FunctorPred 𝒟 𝒟P 𝒟-predicates 𝒟M)
  where

  open NatTrans
  open FunctorPred

  GF : Functor cat cat
  GF .fobj X .carrier = 𝒞M .fobj (X .carrier)
  GF .fobj X .pred = MP .liftF (X .pred) [ α .transf _ ]
  GF .fmor f .morph = 𝒞M .fmor (f .morph)
  GF .fmor {X} {Y} f .presv = begin
      MP .liftF (X .pred) [ α .transf (X .carrier) ]
    ≤⟨ MP .liftF-⊑ (f .presv) [ _ ]m ⟩
      MP .liftF (Y .pred [ F .fmor (f .morph) ]) [ α .transf (X .carrier) ]
    ≤⟨ (MP .liftF-[] (F .fmor (f .morph))) [ _ ]m ⟩
      MP .liftF (Y .pred) [ 𝒟M .fmor (F .fmor (f .morph)) ] [ α .transf (X .carrier) ]
    ≤⟨ []-comp _ _ ⟩
      MP .liftF (Y .pred) [ 𝒟M .fmor (F .fmor (f .morph)) 𝒟.∘ α .transf (X .carrier) ]
    ≤⟨ []-cong (α .natural (f .morph)) ⟩
      MP .liftF (Y .pred) [ α .transf (Y .carrier) 𝒟.∘ F .fmor (𝒞M .fmor (f .morph)) ]
    ≤⟨ []-comp⁻¹ _ _ ⟩
      MP .liftF (Y .pred) [ α .transf (Y .carrier) ] [ F .fmor (𝒞M .fmor (f .morph)) ]
    ∎
    where open ≤-Reasoning ⊑-isPreorder
  GF .fmor-cong f₁≈f₂ .f≃f = 𝒞M .fmor-cong (f₁≈f₂ .f≃f)
  GF .fmor-id = record { f≃f = 𝒞M .fmor-id }
  GF .fmor-comp = λ f g → record { f≃f = 𝒞M .fmor-comp (f .morph) (g .morph) }

-- If the natural transformation goes the other way, we can glue in
-- the other direction too.
module endofunctor2
         (𝒞M : Functor 𝒞 𝒞)
         (𝒟M : Functor 𝒟 𝒟)
         (α  : NatTrans (𝒟M ∘F F) (F ∘F 𝒞M))
         (MP : FunctorPred 𝒟 𝒟P 𝒟-predicates 𝒟M)
  where

  open NatTrans
  open FunctorPred

  GF : Functor cat cat
  GF .fobj X .carrier = 𝒞M .fobj (X .carrier)
  GF .fobj X .pred = MP .liftF (X .pred) ⟨ α .transf _ ⟩
  GF .fmor f .morph = 𝒞M .fmor (f .morph)
  GF .fmor {X} {Y} f .presv = adjoint₂ (begin
      liftF MP (X .pred)
    ≤⟨ MP .liftF-⊑ (f .presv) ⟩
      liftF MP (Y .pred [ F .fmor (f .morph) ])
    ≤⟨ MP .liftF-[] _ ⟩
      liftF MP (Y .pred) [ 𝒟M .fmor (F .fmor (f .morph)) ]
    ≤⟨ (unit _) [ _ ]m ⟩
      liftF MP (Y .pred) ⟨ α .transf (Y .carrier) ⟩ [ α .transf _ ] [ 𝒟M .fmor (F .fmor (f .morph)) ]
    ≤⟨ []-comp _ _ ⟩
      (liftF MP (Y .pred) ⟨ α .transf (Y .carrier) ⟩) [ α .transf _ 𝒟.∘ 𝒟M .fmor (F .fmor (f .morph)) ]
    ≤⟨ []-cong (𝒟.≈-sym (α .natural (f .morph))) ⟩
      (liftF MP (Y .pred) ⟨ α .transf (Y .carrier) ⟩) [ F .fmor (𝒞M .fmor (f .morph)) 𝒟.∘ α .transf _ ]
    ≤⟨ []-comp⁻¹ _ _ ⟩
      (liftF MP (Y .pred) ⟨ α .transf (Y .carrier) ⟩) [ F .fmor (𝒞M .fmor (f .morph)) ] [ α .transf _ ]
    ∎)
    where open ≤-Reasoning ⊑-isPreorder
  GF .fmor-cong f₁≈f₂ .f≃f = 𝒞M .fmor-cong (f₁≈f₂ .f≃f)
  GF .fmor-id = record { f≃f = 𝒞M .fmor-id }
  GF .fmor-comp = λ f g → record { f≃f = 𝒞M .fmor-comp (f .morph) (g .morph) }

module monad-glueing
  (𝒞M : Monad 𝒞)
  (𝒟M : Monad 𝒟)
  (F-preserve-monad : MonadFunctor F 𝒞M 𝒟M)
  (MP : MonadPred _ _ 𝒟-predicates 𝒟M)
  where

  open MonadFunctor F-preserve-monad renaming (transform to α)
  open MonadPred MP
  open endofunctor2 _ _ α functP
  open Monad renaming (unit to unitM)
  open NatTrans

  private
    module 𝒞M = Monad 𝒞M
    module 𝒟M = Monad 𝒟M

  GM : Monad cat
  GM .funct = GF
  GM .Monad.unit .transf X .morph = 𝒞M.unit .transf _
  GM .Monad.unit .transf X .presv = begin
      X .pred
    ≤⟨ unitP ⟩
      liftF (X .pred) [ 𝒟M.unit .transf _ ]
    ≤⟨ unit _ [ _ ]m ⟩
      liftF (X .pred) ⟨ α .transf _ ⟩ [ α .transf _ ] [ 𝒟M.unit .transf _ ]
    ≤⟨ []-comp _ _ ⟩
      liftF (X .pred) ⟨ α .transf _ ⟩ [ α .transf _ 𝒟.∘ 𝒟M.unit .transf _ ]
    ≤⟨ []-cong preserve-unit ⟩
      liftF (X .pred) ⟨ α .transf _ ⟩ [ F .fmor (𝒞M.unit .transf _) ]
    ∎
    where open ≤-Reasoning ⊑-isPreorder
  GM .Monad.unit .natural f .f≃f = 𝒞M.unit .natural (f .morph)
  GM .join .transf X .morph = 𝒞M.join .transf _
  GM .join .transf X .presv = begin
      liftF (liftF (X .pred) ⟨ α .transf _ ⟩) ⟨ α .transf _ ⟩
    ≤⟨ liftF-⟨⟩ _ ⟨ _ ⟩m ⟩
      liftF (liftF (X .pred)) ⟨ 𝒟M.funct .fmor (α .transf _) ⟩ ⟨ α .transf _ ⟩
    ≤⟨ ⟨⟩-comp _ _ ⟩
      liftF (liftF (X .pred)) ⟨ α .transf _ 𝒟.∘ 𝒟M.funct .fmor (α .transf _) ⟩
    ≤⟨ joinP ⟨ _ ⟩m ⟩
      liftF (X .pred) [ 𝒟M.join .transf _ ] ⟨ α .transf _ 𝒟.∘ 𝒟M.funct .fmor (α .transf _) ⟩
    ≤⟨ (unit _) [ _ ]m ⟨ _ ⟩m ⟩
      liftF (X .pred) ⟨ α .transf _ ⟩ [ α .transf _ ] [ 𝒟M.join .transf _ ] ⟨ α .transf _ 𝒟.∘ 𝒟M.funct .fmor (α .transf _) ⟩
    ≤⟨ ([]-comp _ _) ⟨ _ ⟩m ⟩
      liftF (X .pred) ⟨ α .transf _ ⟩ [ α .transf _ 𝒟.∘ 𝒟M.join .transf _ ] ⟨ α .transf _ 𝒟.∘ 𝒟M.funct .fmor (α .transf _) ⟩
    ≤⟨ ([]-cong preserve-join) ⟨ _ ⟩m ⟩
      liftF (X .pred) ⟨ α .transf _ ⟩ [ F .fmor (𝒞M.join .transf _) 𝒟.∘ (α .transf _ 𝒟.∘ 𝒟M.funct .fmor (α .transf _)) ] ⟨ α .transf _ 𝒟.∘ 𝒟M.funct .fmor (α .transf _) ⟩
    ≤⟨ []-comp⁻¹ _ _ ⟨ _ ⟩m ⟩
      liftF (X .pred) ⟨ α .transf _ ⟩ [ F .fmor (𝒞M.join .transf _) ] [ α .transf _ 𝒟.∘ 𝒟M.funct .fmor (α .transf _) ] ⟨ α .transf _ 𝒟.∘ 𝒟M.funct .fmor (α .transf _) ⟩
    ≤⟨ counit _ ⟩
      liftF (X .pred) ⟨ α .transf _ ⟩ [ F .fmor (𝒞M.join .transf _) ]
    ∎

{-
   begin
      liftF (liftF (X .pred) [ α .transf (X .carrier) ]) [ α .transf (𝒞M.funct .fobj (X .carrier)) ]
    ≤⟨ liftF-[] (α .transf (X .carrier)) [ _ ]m ⟩
      liftF (liftF (X .pred)) [ 𝒟M.funct .fmor (α .transf (X .carrier)) ] [ α .transf (𝒞M.funct .fobj (X .carrier)) ]
    ≤⟨ []-comp _ _ ⟩
      liftF (liftF (X .pred)) [ 𝒟M.funct .fmor (α .transf (X .carrier)) 𝒟.∘ α .transf (𝒞M.funct .fobj (X .carrier)) ]
    ≤⟨ joinP [ _ ]m ⟩
      liftF (X .pred) [ 𝒟M.join .transf _ ] [ 𝒟M.funct .fmor (α .transf (X .carrier)) 𝒟.∘ α .transf (𝒞M.funct .fobj (X .carrier)) ]
    ≤⟨ []-comp _ _ ⟩
      liftF (X .pred) [ 𝒟M.join .transf _ 𝒟.∘ (𝒟M.funct .fmor (α .transf (X .carrier)) 𝒟.∘ α .transf (𝒞M.funct .fobj (X .carrier))) ]
    ≤⟨ []-cong (𝒟.≈-sym preserve-join) ⟩
      liftF (X .pred) [ α .transf (X .carrier) 𝒟.∘ F .fmor (𝒞M.join .transf _) ]
    ≤⟨ []-comp⁻¹ _ _ ⟩
      liftF (X .pred) [ α .transf (X .carrier) ] [ F .fmor (𝒞M.join .transf _) ]
    ∎ -}
    where open ≤-Reasoning ⊑-isPreorder
  GM .join .natural f .f≃f = 𝒞M.join .natural (f .morph)
