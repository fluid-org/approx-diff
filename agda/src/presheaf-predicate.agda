{-# OPTIONS --postfix-projections --prop --safe #-}

open import Level using (_⊔_; suc; 0ℓ)
open import Data.Product using (_,_; proj₁; proj₂) renaming (_×_ to _××_)
open import prop using (_,_; tt; ∃; _∧_; LiftS; liftS; proj₁; proj₂)
open import basics using (IsPreorder; IsMeet; IsTop; IsResidual; module ≤-Reasoning; monoidOfMeet; IsJoin; IsClosureOp; IsBigJoin)
open import prop-setoid using (Setoid; module ≈-Reasoning)
  renaming (_⇒_ to _⇒s_)
open import categories using (Category; HasProducts; HasTerminal; IsTerminal; HasCoproducts)
open import setoid-cat using (SetoidCat; Setoid-products; Setoid-coproducts)
open import functor using (Functor; [_⇒_]; NatTrans; ≃-NatTrans; functor-preserve-iso; Id; _∘F_)
open import monad using (Monad)
open import predicate-system using (PredicateSystem; ClosureOp; FunctorPred; MonadPred)
import setoid-predicate

module presheaf-predicate {o m e} os (𝒞 : Category o m e) where

open import yoneda os 𝒞

private
  ℓ = o ⊔ m ⊔ e ⊔ os
  module P = PredicateSystem (setoid-predicate.system {ℓ} {ℓ})
  module S = Category (SetoidCat ℓ ℓ)
  module SP = HasProducts (Setoid-products ℓ ℓ)
  module 𝒞 = Category 𝒞
  module PSh = Category PSh
  module PShP = HasProducts products

open Functor
open NatTrans
open ≃-NatTrans

record Predicate (X : PSh.obj) : Set (suc (suc ℓ)) where
  no-eta-equality
  field
    pred : ∀ a → P.Predicate (X .fobj a)
    pred-mor : ∀ {a b} (f : b 𝒞.⇒ a) → pred a P.⊑ (pred b P.[ X .fmor f ])
open Predicate

-- pred a : Predicate (X .fobj a)
-- pred b : Predicate (X .fobj b)

-- pred a ⟨ X .fmor CP.in₁ ⟩ : Predicate (X .fobj (CP.coprod a b))
-- pred (CP.coprod a b) : Predicate (X .fobj (CP.coprod a b))

record _⊑_ {X : PSh.obj} (P Q : Predicate X) : Prop (suc ℓ) where
  no-eta-equality
  field
    *⊑* : ∀ a → P .pred a P.⊑ Q .pred a
open _⊑_

infix 2 _⊑_

⊑-isPreorder : ∀ {X} → IsPreorder (_⊑_ {X})
⊑-isPreorder .IsPreorder.refl .*⊑* x = P.⊑-isPreorder .IsPreorder.refl
⊑-isPreorder .IsPreorder.trans ϕ ψ .*⊑* x = P.⊑-isPreorder .IsPreorder.trans (ϕ .*⊑* x) (ψ .*⊑* x)

_[_] : ∀ {X Y} → Predicate Y → X PSh.⇒ Y → Predicate X
(P [ α ]) .pred a = (P .pred a) P.[ α .transf a ]
_[_] {X} {Y} P α .pred-mor {a} {b} f = begin
    (P .pred a) P.[ α .transf a ]
  ≤⟨ P .pred-mor f P.[ α .transf a ]m ⟩
    (P .pred b) P.[ Y .fmor f ] P.[ α .transf a ]
  ≤⟨ P.[]-comp _ _ ⟩
    (P .pred b) P.[ Y .fmor f S.∘ α .transf a ]
  ≤⟨ P.[]-cong (α .natural f) ⟩
    (P .pred b) P.[ α .transf b S.∘ X .fmor f ]
  ≤⟨ P.[]-comp⁻¹ _ _ ⟩
    (P .pred b P.[ α .transf b ]) P.[ X .fmor f ]
  ∎
  where open ≤-Reasoning P.⊑-isPreorder

_⟨_⟩ : ∀ {X Y} → Predicate X → X PSh.⇒ Y → Predicate Y
_⟨_⟩ {X} {Y} P α .pred a = P .pred a P.⟨ α .transf a ⟩
_⟨_⟩ {X} {Y} P α .pred-mor {a} {b} f =
  P.adjoint₂ (begin
    P .pred a
  ≤⟨ P .pred-mor f ⟩
    P .pred b P.[ X .fmor f ]
  ≤⟨ P.unit _ P.[ _ ]m ⟩
    (P .pred b P.⟨ α .transf b ⟩) P.[ α .transf b ] P.[ X .fmor f ]
  ≤⟨ P.[]-comp _ _ ⟩
    (P .pred b P.⟨ α .transf b ⟩) P.[ α .transf b S.∘ X .fmor f ]
  ≤⟨ P.[]-cong (S.≈-sym (α .natural f)) ⟩
    (P .pred b P.⟨ α .transf b ⟩) P.[ Y .fmor f S.∘ α .transf a ]
  ≤⟨ P.[]-comp⁻¹ _ _ ⟩
    (P .pred b P.⟨ α .transf b ⟩) P.[ Y .fmor f ] P.[ α .transf a ]
  ∎)
  where open ≤-Reasoning P.⊑-isPreorder

_[_]m     : ∀ {X Y} {P Q : Predicate Y} → P ⊑ Q → (f : X PSh.⇒ Y) → (P [ f ]) ⊑ (Q [ f ])
_[_]m {X} {Y} {P} {Q} P⊑Q f .*⊑* x = P⊑Q .*⊑* x P.[ _ ]m

[]-cong : ∀ {X Y} {P : Predicate Y}{f₁ f₂ : X PSh.⇒ Y} → f₁ PSh.≈ f₂ → (P [ f₁ ]) ⊑ (P [ f₂ ])
[]-cong f₁≈f₂ .*⊑* x = P.[]-cong (f₁≈f₂ .transf-eq x)

[]-id : ∀ {X} {P : Predicate X} → P ⊑ (P [ PSh.id _ ])
[]-id .*⊑* x = P.[]-id

[]-id⁻¹ : ∀ {X} {P : Predicate X} → (P [ PSh.id _ ]) ⊑ P
[]-id⁻¹ .*⊑* x = P.[]-id⁻¹

[]-comp : ∀ {X Y Z} {P : Predicate Z} (f : Y PSh.⇒ Z) (g : X PSh.⇒ Y) → ((P [ f ]) [ g ]) ⊑ (P [ f PSh.∘ g ])
[]-comp α β .*⊑* x = P.[]-comp _ _

[]-comp⁻¹ : ∀ {X Y Z} {P : Predicate Z} (f : Y PSh.⇒ Z) (g : X PSh.⇒ Y) → (P [ f PSh.∘ g ]) ⊑ ((P [ f ]) [ g ])
[]-comp⁻¹ f g .*⊑* x = P.[]-comp⁻¹ _ _

adjoint₁ : ∀ {X Y} {P : Predicate X} {Q : Predicate Y} {f : X PSh.⇒ Y} → P ⟨ f ⟩ ⊑ Q → P ⊑ Q [ f ]
adjoint₁ ϕ .*⊑* x = P.adjoint₁ (ϕ .*⊑* x)

adjoint₂ : ∀ {X Y} {P : Predicate X} {Q : Predicate Y} {f : X PSh.⇒ Y} → P ⊑ Q [ f ] → P ⟨ f ⟩ ⊑ Q
adjoint₂ ϕ .*⊑* x = P.adjoint₂ (ϕ .*⊑* x)


open IsMeet

TT : ∀ {X} → Predicate X
TT .pred x = P.TT
TT .pred-mor f = P.[]-TT

TT-isTop : ∀ {X} → IsTop (⊑-isPreorder {X}) TT
TT-isTop .IsTop.≤-top .*⊑* a = P.TT-isTop .IsTop.≤-top

_&&_ : ∀ {X} → Predicate X → Predicate X → Predicate X
(P && Q) .pred x = (P .pred x) P.&& (Q .pred x)
_&&_ {X} P Q .pred-mor {x} {y} f = begin
    P .pred x P.&& Q .pred x
  ≤⟨ mono P.&&-isMeet (P .pred-mor f) (Q .pred-mor f) ⟩
    ((P .pred y) P.[ X .fmor f ]) P.&& ((Q .pred y) P.[ X .fmor f ])
  ≤⟨ P.[]-&& ⟩
    (P .pred y P.&& Q .pred y) P.[ X .fmor f ]
  ∎
  where open ≤-Reasoning P.⊑-isPreorder

&&-isMeet : ∀ {X} → IsMeet (⊑-isPreorder {X}) _&&_
&&-isMeet .π₁ .*⊑* a = P.&&-isMeet .π₁
&&-isMeet .π₂ .*⊑* a = P.&&-isMeet .π₂
&&-isMeet .⟨_,_⟩ ϕ ψ .*⊑* a = P.&&-isMeet .⟨_,_⟩ (ϕ .*⊑* a) (ψ .*⊑* a)

_++_ : ∀ {X} → Predicate X → Predicate X → Predicate X
(P ++ Q) .pred x = P .pred x P.++ Q .pred x
_++_ {X} P Q .pred-mor {a} {b} f = begin
    P .pred a P.++ Q .pred a
  ≤⟨ IsJoin.mono P.++-isJoin (P .pred-mor f) (Q .pred-mor f) ⟩
    (P .pred b P.[ X .fmor f ]) P.++ (Q .pred b P.[ X .fmor f ])
  ≤⟨ P.[]-++⁻¹ ⟩
    (P .pred b P.++ Q .pred b) P.[ X .fmor f ]
  ∎
  where open ≤-Reasoning P.⊑-isPreorder

++-isJoin : ∀ {X} → IsJoin (⊑-isPreorder {X}) _++_
++-isJoin .IsJoin.inl .*⊑* a = P.++-isJoin .IsJoin.inl
++-isJoin .IsJoin.inr .*⊑* a = P.++-isJoin .IsJoin.inr
++-isJoin .IsJoin.[_,_] ϕ ψ .*⊑* a = IsJoin.[_,_] P.++-isJoin (ϕ .*⊑* a) (ψ .*⊑* a)

[]-++ : ∀ {X Y} {P Q : Predicate Y} {f : X PSh.⇒ Y} → ((P ++ Q) [ f ]) ⊑ ((P [ f ]) ++ (Q [ f ]))
[]-++ .*⊑* a = record { *⊑* = λ x z → z }

-- Meets distribute over joins, and satisfy Frobenius reciprocity with direct images, stagewise.
&&-++-distrib : ∀ {X} {P Q R : Predicate X} → (P && (Q ++ R)) ⊑ ((P && Q) ++ (P && R))
&&-++-distrib .*⊑* a = setoid-predicate.&&-++-distrib

&&-⟨⟩-frobenius : ∀ {X Y} {P : Predicate Y} {Q : Predicate X} {α : X PSh.⇒ Y} →
                  (P && (Q ⟨ α ⟩)) ⊑ (((P [ α ]) && Q) ⟨ α ⟩)
&&-⟨⟩-frobenius .*⊑* a = setoid-predicate.&&-⟨⟩-frobenius

⋁ : ∀ {X} (I : Set 0ℓ) → (I → Predicate X) → Predicate X
⋁ I P .pred a = P.⋁ I λ i → P i .pred a
⋁ {X} I P .pred-mor {a} {b} f = begin
    P.⋁ I (λ i → P i .pred a)
  ≤⟨ IsBigJoin.mono P.⋁-isJoin (λ i → P i .pred-mor f) ⟩
    P.⋁ I (λ i → P i .pred b P.[ X .fmor f ])
  ≤⟨ IsBigJoin.least P.⋁-isJoin I _ _ (λ i → (IsBigJoin.upper P.⋁-isJoin _ _ i) P.[ _ ]m) ⟩
    (P.⋁ I (λ i → P i .pred b)) P.[ X .fmor f ]
  ∎
  where open ≤-Reasoning P.⊑-isPreorder

⋁-isJoin : ∀ {X} → IsBigJoin (⊑-isPreorder {X}) 0ℓ ⋁
⋁-isJoin .IsBigJoin.upper I P i .*⊑* a = IsBigJoin.upper P.⋁-isJoin _ _ i
⋁-isJoin .IsBigJoin.least I P Q ϕ .*⊑* a = IsBigJoin.least P.⋁-isJoin I _ _ (λ i → ϕ i .*⊑* a)

[]-⋁ : ∀ {X Y I} {P : I → Predicate Y} {f : X PSh.⇒ Y} → (⋁ I P [ f ]) ⊑ ⋁ I (λ i → P i [ f ])
[]-⋁ .*⊑* a = P.[]-⋁


open setoid-predicate.Predicate
open setoid-predicate._⊑_
open prop-setoid.Setoid
open prop-setoid._⇒_
open prop-setoid._≃m_

_==>_ : ∀ {X} → Predicate X → Predicate X → Predicate X
_==>_ {X} P Q .pred a .pred x =
  ∀ b (f : b 𝒞.⇒ a) → P .pred b .pred (X .fmor f .func x) → Q .pred b .pred (X .fmor f .func x)
_==>_ {X} P Q .pred a .pred-≃ x₁≈x₂ ϕ b f p =
  Q .pred b .pred-≃ (X .fmor f .func-resp-≈ x₁≈x₂)
    (ϕ b f (P .pred b .pred-≃ (X .fobj b .sym (X .fmor f .func-resp-≈ x₁≈x₂)) p))
_==>_ {X} P Q .pred-mor {a} {b} f .*⊑* x ϕ c g p =
  Q .pred c .pred-≃ (X .fmor-comp g f .func-eq (X .fobj a .refl))
    (ϕ c (f 𝒞.∘ g) (P .pred c .pred-≃ (X .fobj c .sym (X .fmor-comp g f .func-eq (X .fobj a .refl))) p))

[]-==> : ∀ {X Y}{P Q : Predicate Y}{f : X PSh.⇒ Y} → ((P [ f ]) ==> (Q [ f ])) ⊑ (P ==> Q) [ f ]
[]-==> {X}{Y}{P}{Q}{α} .*⊑* a .*⊑* x ϕ b f p =
  Q .pred b .pred-≃ (Y .fobj b .sym (α .natural f .func-eq (X .fobj a .refl)))
    (ϕ b f (P .pred b .pred-≃ (α .natural f .func-eq (X .fobj a .refl)) p))

==>-residual : ∀ {X} → IsResidual ⊑-isPreorder (monoidOfMeet _ &&-isMeet TT-isTop) (_==>_ {X})
==>-residual {X} .IsResidual.lambda {P}{Q}{R} Φ .*⊑* a .*⊑* x p b f q =
  Φ .*⊑* b .*⊑* (X .fmor f .func x) (P .pred-mor f .*⊑* x p , q)
==>-residual {X} .IsResidual.eval {P} {Q} .*⊑* a .*⊑* x (ϕ , p) =
  Q .pred a .pred-≃ (X .fmor-id .func-eq (X .fobj a .refl))
    (ϕ a (𝒞.id _) (P .pred a .pred-≃ (X .fobj a .sym (X .fmor-id .func-eq (X .fobj a .refl))) p))

⋀ : ∀ {X Y} → Predicate (X × Y) → Predicate X
⋀ {X} {Y} P .pred a .pred x = ∀ b (f : b 𝒞.⇒ a) y → P .pred b .pred (X .fmor f .func x , y)
⋀ {X} {Y} P .pred a .pred-≃ x₁≈x₂ ϕ b f y =
  P .pred b .pred-≃ (X .fmor f .func-resp-≈ x₁≈x₂ , Y .fobj b .refl) (ϕ b f y)
⋀ {X} {Y} P .pred-mor {a} {b} f .*⊑* x ϕ c g y =
  P .pred c .pred-≃ (X .fmor-comp _ _ .func-eq (X .fobj a .refl) , Y .fobj c .refl) (ϕ c (f 𝒞.∘ g) y)

⋀-[] : ∀ {X X' Y} {P : Predicate (PShP.prod X Y)} {α : X' PSh.⇒ X} →
       (⋀ (P [ PShP.prod-m α (PSh.id _) ])) ⊑ (⋀ P) [ α ]
⋀-[] {X} {X'} {Y} {P} {α} .*⊑* a .*⊑* x ϕ b f y =
  P .pred b .pred-≃ (X .fobj b .sym (α .natural f .func-eq (X' .fobj a .refl)) , Y .fobj b .refl)
    (ϕ b f y)

⋀-eval : ∀ {X Y} {P : Predicate (PShP.prod X Y)} → ((⋀ P) [ PShP.p₁ ]) ⊑ P
⋀-eval {X} {Y} {P} .*⊑* a .*⊑* (x , y) ϕ =
  P .pred a .pred-≃ (X .fmor-id .func-eq (X .fobj a .refl) , Y .fobj a .refl) (ϕ a (𝒞.id _) y)

⋀-lambda : ∀ {X Y} {P : Predicate X} {Q : Predicate (PShP.prod X Y)} → P [ PShP.p₁ ] ⊑ Q → P ⊑ ⋀ Q
⋀-lambda {X} {Y} {P} {Q} Φ .*⊑* a .*⊑* x p b f y =
  Φ .*⊑* b .*⊑* (X .fmor f .func x , y) (P .pred-mor f .*⊑* x p)

system : PredicateSystem PSh products
system .PredicateSystem.Predicate = Predicate
system .PredicateSystem._⊑_ = _⊑_
system .PredicateSystem.⊑-isPreorder = ⊑-isPreorder
system .PredicateSystem._[_] = _[_]
system .PredicateSystem._⟨_⟩ = _⟨_⟩
system .PredicateSystem._[_]m = _[_]m
system .PredicateSystem.[]-cong = []-cong
system .PredicateSystem.[]-id = []-id
system .PredicateSystem.[]-id⁻¹ = []-id⁻¹
system .PredicateSystem.[]-comp = []-comp
system .PredicateSystem.[]-comp⁻¹ = []-comp⁻¹
system .PredicateSystem.adjoint₁ = adjoint₁
system .PredicateSystem.adjoint₂ = adjoint₂
system .PredicateSystem.TT = TT
system .PredicateSystem._&&_ = _&&_
system .PredicateSystem._++_ = _++_
system .PredicateSystem._==>_ = _==>_
system .PredicateSystem.⋀ {X} {Y} P = ⋀ {X} {Y} P
system .PredicateSystem.TT-isTop = TT-isTop
system .PredicateSystem.[]-TT = record { *⊑* = λ a → record { *⊑* = λ x _ → tt } }
system .PredicateSystem.&&-isMeet = &&-isMeet
system .PredicateSystem.[]-&& = record { *⊑* = λ a → record { *⊑* = λ x z → z } }
system .PredicateSystem.==>-residual = ==>-residual
system .PredicateSystem.[]-==> = []-==>
system .PredicateSystem.[]-++ = []-++
system .PredicateSystem.++-isJoin = ++-isJoin
system .PredicateSystem.⋀-[] = ⋀-[]
system .PredicateSystem.⋀-eval = ⋀-eval
system .PredicateSystem.⋀-lambda = ⋀-lambda
system .PredicateSystem.⋁ = ⋁
system .PredicateSystem.⋁-isJoin = ⋁-isJoin
system .PredicateSystem.[]-⋁ = []-⋁

------------------------------------------------------------------------------
-- Endofunctors: for any endofunctor on 𝒞, there is a predicate
-- lifting on the matching functor on PSh⟨𝒞⟩

module F-hat-pred (F : Functor 𝒞 𝒞) where

  open FunctorPred
  open UnaryDay F

  endofunctor : FunctorPred _ _ system M-hat
  endofunctor .liftF {X} P .pred a .pred z-g-Xz = ∃ (M-hat-carrier X a) λ z-g-Xz' → LiftS ℓ (M-hat-eq {X} z-g-Xz z-g-Xz') ∧ P .pred _ .pred (z-g-Xz' .proj₂ .proj₂)
  endofunctor .liftF {X} P .pred a .pred-≃ {x₁} {x₂} (liftS eq) (x' , liftS ϕ , ψ) = x' , liftS (eq-trans (eq-sym eq) ϕ) , ψ
  endofunctor .liftF {X} P .pred-mor f .*⊑* (z , g , Xz) (x' , ϕ , ψ) = M-hat-mor X f .func x' , (M-hat-mor X f .func-resp-≈ ϕ) , ψ
  endofunctor .liftF-⊑ {X} {P} {Q} P⊑Q .*⊑* a .*⊑* (z , g , Xz) ((z' , g' , Xz') , ϕ , ψ) =
    (z' , g' , Xz') , ϕ , P⊑Q .*⊑* z' .*⊑* Xz' ψ
  endofunctor .liftF-[] {X} {Y} {P} α .*⊑* a .*⊑* x (x' , ϕ , ψ) =
    M-hat-nat X Y α .transf a .func x' , M-hat-nat X Y α .transf a .func-resp-≈ ϕ , ψ
  endofunctor .liftF-⟨⟩ {X} {Y} {P} α .*⊑* a .*⊑* (z , g , Yz) ((z' , g' , Yz') , liftS eq , (Xz' , ϕ , ψ)) =
    (z' , g' , Xz') , ((z' , g' , Xz') , M-hat-setoid _ _ .refl , ϕ) ,
    liftS (eq-step (𝒞.id _) (𝒞.id _) 𝒞.≈-refl
                   (Y .fmor-id .func-eq (Y .fobj _ .refl))
                   (Y .fmor-id .func-eq ψ)
                   (eq-sym eq))

module Monad-hat-pred (M : Monad 𝒞) where

  open FunctorPred
  open Monad M renaming (funct to Mfunct)
  open DayMonad M
  open UnaryDay Mfunct
  open F-hat-pred Mfunct

  unitP : ∀ {X} {P : Predicate X} → P ⊑ (endofunctor .liftF P) [ unit-hat .transf X ]
  unitP .*⊑* x .*⊑* Xx ϕ = (x , unit .transf x , Xx) , M-hat-setoid _ x .refl , ϕ

  joinP : ∀ {X} {P : Predicate X} → endofunctor .liftF (endofunctor .liftF P) ⊑ endofunctor .liftF P [ join-hat .transf X ]
  joinP {X} .*⊑* x .*⊑* (y , f , z , g , Xz) ((y' , f' , z' , g' , Xz') , eq₁ , (z'' , g'' , Xz'') , liftS eq₂ , ϕ) =
    join-hat .transf X .transf x .func (y' , f' , z'' , g'' , Xz'') ,
    join-hat .transf X .transf x .func-resp-≈
      (M-hat-setoid (M-hat-PSh X) x .trans eq₁
        (liftS
         (eq-step
           (𝒞.id _) (𝒞.id _) 𝒞.≈-refl
           (liftS (eq-step (𝒞.id _) (𝒞.id _) (𝒞.∘-cong 𝒞.≈-refl 𝒞.id-right) (X .fmor-id .func-eq (X .fobj _ .refl)) (X .fmor-id .func-eq (X .fobj _ .refl)) (eq-stop _)))
           (liftS (eq-step (𝒞.id _) (𝒞.id _) (𝒞.∘-cong 𝒞.≈-refl 𝒞.id-right) (X .fmor-id .func-eq (X .fobj _ .refl)) (X .fmor-id .func-eq (X .fobj _ .refl)) eq₂))
           (eq-stop _)))) ,
    ϕ

  MP : MonadPred _ _ system monad-hat
  MP .MonadPred.functP = endofunctor
  MP .MonadPred.unitP = unitP
  MP .MonadPred.joinP = joinP

   -- TODO: strength

-- FIXME: this ought to work for comonads too

------------------------------------------------------------------------------
-- Closure operator generated by a coverage: each object carries a set of
-- covers, a cover being an indexed family of injections, and covers pull back
-- along any morphism. Covers enter the trees as codes, so the index data
-- stays at the level of the predicates. The trees are Prop-valued: with
-- infinitary covers, idempotence needs a subtree for each index out of a
-- family of covering proofs, which a truncated tree cannot supply.
module CoverMonad
    (Cover : 𝒞.obj → Set ℓ)
    (Ix : ∀ {y} → Cover y → Set ℓ)
    (dom : ∀ {y} (c : Cover y) → Ix c → 𝒞.obj)
    (inj : ∀ {y} (c : Cover y) (s : Ix c) → dom c s 𝒞.⇒ y)
  where

  open Setoid
  open _⇒s_
  open setoid-predicate.Predicate
  open setoid-predicate._⊑_

  -- A cover of the target pulls back along any morphism to a cover of the
  -- source, one leg per index.
  record CoverPullback {x y} (c : Cover x) (g : y 𝒞.⇒ x) : Set ℓ where
    field
      cover : Cover y
      reix  : Ix cover → Ix c
      leg   : ∀ s → dom cover s 𝒞.⇒ dom c (reix s)
      eq    : ∀ s → (inj c (reix s) 𝒞.∘ leg s) 𝒞.≈ (g 𝒞.∘ inj cover s)
  open CoverPullback

  data Context (X : PSh.obj) (P : Predicate X) : (a : 𝒞.obj) → X .fobj a .Carrier → Prop ℓ where
    leaf : ∀ {a x} → P .pred a .pred x → Context X P a x
    node : ∀ {y z} (c : Cover y) (xs : ∀ s → X .fobj (dom c s) .Carrier) →
           (∀ s → Context X P (dom c s) (xs s)) →
           (∀ s → X .fobj (dom c s) ._≈_ (xs s) (X .fmor (inj c s) .func z)) →
           Context X P y z

  Context-eq : ∀ {X} {P : Predicate X} {a x₁ x₂} → X .fobj a ._≈_ x₁ x₂ → Context X P a x₁ → Context X P a x₂
  Context-eq {X} {P} x₁≈x₂ (leaf p) = leaf (P .pred _ .pred-≃ x₁≈x₂ p)
  Context-eq {X} {P} x₁≈x₂ (node c xs ts eqs) =
    node c xs ts (λ s → X .fobj (dom c s) .trans (eqs s) (X .fmor (inj c s) .func-resp-≈ x₁≈x₂))

  Context-mono : ∀ {X : PSh.obj} {P Q : Predicate X} (P⊑Q : P ⊑ Q) →
                 ∀ {a x} → Context X P a x → Context X Q a x
  Context-mono P⊑Q (leaf p) = leaf (P⊑Q .*⊑* _ .*⊑* _ p)
  Context-mono P⊑Q (node c xs ts eqs) = node c xs (λ s → Context-mono P⊑Q (ts s)) eqs

  Context-strong : ∀ {X : PSh.obj} {P Q : Predicate X} →
                   ∀ {a x} → Context X P a x → Q .pred a .pred x → Context X (P && Q) a x
  Context-strong (leaf p) q = leaf (p , q)
  Context-strong {X} {P} {Q} (node c xs ts eqs) q =
    node c xs
      (λ s → Context-strong (ts s)
               (Q .pred (dom c s) .pred-≃ (X .fobj (dom c s) .sym (eqs s)) (Q .pred-mor (inj c s) .*⊑* _ q)))
      eqs

  Context-[]⁻¹ : ∀ {X Y} {P : Predicate Y} {f : X PSh.⇒ Y} a x y →
                 Y .fobj a ._≈_ y (f .transf a .func x) →
                 Context Y P a y →
                 Context X (P [ f ]) a x
  Context-[]⁻¹ {X} {Y} {P} {f} a x y eq (leaf p) = leaf (P .pred a .pred-≃ eq p)
  Context-[]⁻¹ {X} {Y} {P} {f} a x y eq (node c xs ts eqs) =
    node c (λ s → X .fmor (inj c s) .func x)
         (λ s → Context-[]⁻¹ (dom c s) (X .fmor (inj c s) .func x) (xs s) (eq' s) (ts s))
         (λ s → X .fobj (dom c s) .refl)
    where
      eq' : ∀ s → Y .fobj (dom c s) ._≈_ (xs s) (f .transf (dom c s) .func (X .fmor (inj c s) .func x))
      eq' s = begin
          xs s
        ≈⟨ eqs s ⟩
          Y .fmor (inj c s) .func y
        ≈⟨ Y .fmor (inj c s) .func-resp-≈ eq ⟩
          Y .fmor (inj c s) .func (f .transf a .func x)
        ≈⟨ f .natural _ .func-eq (X .fobj a .refl) ⟩
          f .transf (dom c s) .func (X .fmor (inj c s) .func x)
        ∎
        where open ≈-Reasoning (Y .fobj (dom c s) .isEquivalence)

  Context-[] : ∀ {X Y} {P : Predicate Y} {f : X PSh.⇒ Y} a x →
               Context X (P [ f ]) a x →
               Context Y P a (f .transf a .func x)
  Context-[] a x (leaf p) = leaf p
  Context-[] {X} {Y} {P} {f} a x (node c xs ts eqs) =
    node c (λ s → f .transf (dom c s) .func (xs s))
         (λ s → Context-[] (dom c s) (xs s) (ts s))
         (λ s → Y .fobj (dom c s) .trans (f .transf (dom c s) .func-resp-≈ (eqs s))
                  (Y .fobj (dom c s) .sym (f .natural _ .func-eq (X .fobj a .refl))))

  -- The closure operator, for a coverage whose covers pull back.
  module Closure (stable : ∀ {x y} (c : Cover x) (g : y 𝒞.⇒ x) → CoverPullback c g) where

    Context-reindex : ∀ {X : PSh.obj} (P : Predicate X) →
                      ∀ {a b} {x} (f : b 𝒞.⇒ a) → Context X P a x → Context X P b (X .fmor f .func x)
    Context-reindex {X} P f (leaf p) =
      leaf (P .pred-mor f .*⊑* _ p)
    Context-reindex {X} P {a} {b} {x} f (node c xs ts eqs) =
      node (pb .cover)
           (λ s → X .fmor (pb .leg s) .func (xs (pb .reix s)))
           (λ s → Context-reindex P (pb .leg s) (ts (pb .reix s)))
           eq'
      where
        pb = stable c f

        eq' : ∀ s → X .fobj (dom (pb .cover) s) ._≈_
                (X .fmor (pb .leg s) .func (xs (pb .reix s)))
                (X .fmor (inj (pb .cover) s) .func (X .fmor f .func x))
        eq' s = begin
            X .fmor (pb .leg s) .func (xs (pb .reix s))
          ≈⟨ X .fmor (pb .leg s) .func-resp-≈ (eqs (pb .reix s)) ⟩
            X .fmor (pb .leg s) .func (X .fmor (inj c (pb .reix s)) .func x)
          ≈˘⟨ X .fmor-comp _ _ .func-eq (X .fobj a .refl) ⟩
            X .fmor (inj c (pb .reix s) 𝒞.∘ pb .leg s) .func x
          ≈⟨ X .fmor-cong (pb .eq s) .func-eq (X .fobj a .refl) ⟩
            X .fmor (f 𝒞.∘ inj (pb .cover) s) .func x
          ≈⟨ X .fmor-comp _ _ .func-eq (X .fobj a .refl) ⟩
            X .fmor (inj (pb .cover) s) .func (X .fmor f .func x)
          ∎
          where open ≈-Reasoning (X .fobj (dom (pb .cover) s) .isEquivalence)

    𝐂 : ∀ {X} → Predicate X → Predicate X
    𝐂 P .pred a .pred x = Context _ P a x
    𝐂 P .pred a .pred-≃ = Context-eq
    𝐂 P .pred-mor f .*⊑* x p = Context-reindex P f p

    Context-join : ∀ {X : PSh.obj} {P : Predicate X} →
                   ∀ {a x} → Context X (𝐂 P) a x → Context X P a x
    Context-join (leaf p) = p
    Context-join (node c xs ts eqs) = node c xs (λ s → Context-join (ts s)) eqs

    𝐂-isClosure : ∀ {X} → IsClosureOp (⊑-isPreorder {X}) 𝐂
    𝐂-isClosure .IsClosureOp.mono P⊑Q .*⊑* a .*⊑* x p = Context-mono P⊑Q p
    𝐂-isClosure .IsClosureOp.unit .*⊑* a .*⊑* x p = leaf p
    𝐂-isClosure .IsClosureOp.closed .*⊑* a .*⊑* x p = Context-join p

    𝐂-strong : ∀ {X} {P Q : Predicate X} → (𝐂 P && Q) ⊑ 𝐂 (P && Q)
    𝐂-strong .*⊑* a .*⊑* x (p , q) = Context-strong p q

    𝐂-[]⁻¹ : ∀ {X Y} {P : Predicate Y} {f : X PSh.⇒ Y} → (𝐂 P [ f ]) ⊑ 𝐂 (P [ f ])
    𝐂-[]⁻¹ {X} {Y} {P} {f} .*⊑* a .*⊑* x t =
      Context-[]⁻¹ a x (f .transf a .func x) (Y .fobj a .refl) t

    𝐂-[] : ∀ {X Y} {P : Predicate Y} {f : X PSh.⇒ Y} → 𝐂 (P [ f ]) ⊑ (𝐂 P [ f ])
    𝐂-[] {X} {Y} {P} {f} .*⊑* a .*⊑* x t = Context-[] a x t

    closureOp : ClosureOp PSh products system
    closureOp .ClosureOp.𝐂 = 𝐂
    closureOp .ClosureOp.𝐂-isClosure = 𝐂-isClosure
    closureOp .ClosureOp.𝐂-[] = 𝐂-[]
    closureOp .ClosureOp.𝐂-[]⁻¹ = 𝐂-[]⁻¹
    closureOp .ClosureOp.𝐂-strong = 𝐂-strong

    -- Lifting a predicate along an endofunctor distributes over the closure,
    -- for endofunctors along whose images the covers pull back.
    module Distrib (F : Functor 𝒞 𝒞) where

      -- A cover of x pulls back along any morphism into the F-image of x,
      -- one leg per index, each leg landing in the F-image of a summand.
      record FCoverPullback {x y} (c : Cover x) (g : y 𝒞.⇒ F .fobj x) : Set ℓ where
        field
          cover : Cover y
          reix  : Ix cover → Ix c
          leg   : ∀ s → dom cover s 𝒞.⇒ F .fobj (dom c (reix s))
          eq    : ∀ s → (F .fmor (inj c (reix s)) 𝒞.∘ leg s) 𝒞.≈ (g 𝒞.∘ inj cover s)
      open FCoverPullback

      module _ (Fpull : ∀ {x y} (c : Cover x) (g : y 𝒞.⇒ F .fobj x) → FCoverPullback c g) where

        open UnaryDay F
        open F-hat-pred F renaming (endofunctor to FP)
        open FunctorPred

        distrib : ∀ {X} {P : Predicate X} → FP .liftF (𝐂 P) ⊑ 𝐂 (FP .liftF P)
        distrib {X} {P} .*⊑* a .*⊑* (z , g , Xz) ((z' , g' , Xz') , liftS ϕ , ψ) =
          Context-eq (liftS (eq-sym ϕ)) (h a z' g' Xz' ψ)
          where
            h : ∀ a z (g : a 𝒞.⇒ F .fobj z) Xz →
                Context X P z Xz → Context (M-hat .fobj X) (FP .liftF P) a (z , g , Xz)
            h a z g Xz (leaf ϕ') = leaf ((z , g , Xz) , M-hat-setoid X _ .refl , ϕ')
            h a z g Xz (node c xs ts eqs) =
              node (fp .cover)
                   (λ s → (dom c (fp .reix s) , fp .leg s , xs (fp .reix s)))
                   (λ s → h _ _ _ _ (ts (fp .reix s)))
                   (λ s → liftS (eq-step {Fy = Xz} (inj c (fp .reix s)) (𝒞.id z)
                            (𝒞.≈-trans (fp .eq s)
                              (𝒞.≈-sym (𝒞.≈-trans (𝒞.∘-cong (F .fmor-id) 𝒞.≈-refl) 𝒞.id-left)))
                            (X .fobj _ .sym (eqs (fp .reix s)))
                            (X .fmor-id .func-eq (X .fobj z .refl))
                            (eq-stop _)))
              where fp = Fpull c g
