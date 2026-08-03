{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (suc; _⊔_; 0ℓ)
open import basics
  using (IsPreorder; IsTop; IsMeet; IsResidual; monoidOfMeet; module ≤-Reasoning; IsJoin; IsClosureOp; IsBigJoin)
open import categories using (Category; HasProducts; HasExponentials)
open import functor using (Functor; NatTrans; Id; _∘F_)
open import monad using (Monad)
open import predicate-system using (PredicateSystem; ClosureOp; FunctorPred; MonadPred)

module closure-predicate
    {o m e}
    {𝒞 : Category o m e} {𝒞P : HasProducts 𝒞}
    (S : PredicateSystem 𝒞 𝒞P)
    (C : ClosureOp 𝒞 𝒞P S)
  where

private
  module 𝒞 = Category 𝒞
  module 𝒞P = HasProducts 𝒞P
  module S = PredicateSystem S

open ClosureOp C
open IsClosureOp
open IsMeet renaming (mono to &&-mono)
open IsJoin renaming (mono to ++-mono)
open IsTop

S⊑-trans : ∀ {X} {P Q R : S.Predicate X} → P S.⊑ Q → Q S.⊑ R → P S.⊑ R
S⊑-trans = S.⊑-isPreorder .IsPreorder.trans

record Predicate (X : 𝒞.obj) : Set (suc o ⊔ suc m ⊔ suc e) where
  no-eta-equality
  field
    pred   : S.Predicate X
    closed : 𝐂 pred S.⊑ pred
open Predicate

embed : ∀ {X} → S.Predicate X → Predicate X
embed P .pred = 𝐂 P
embed P .closed = 𝐂-isClosure .closed

_⊑_ : ∀ {X} → Predicate X → Predicate X → Prop (o ⊔ m ⊔ e)
P ⊑ Q = P .pred S.⊑ Q .pred

⊑-isPreorder : ∀ {X} → IsPreorder (_⊑_ {X})
⊑-isPreorder .IsPreorder.refl = S.⊑-isPreorder .IsPreorder.refl
⊑-isPreorder .IsPreorder.trans = S.⊑-isPreorder .IsPreorder.trans

infix 2 _⊑_

_[_]   : ∀ {X Y} → Predicate Y → X 𝒞.⇒ Y → Predicate X
(P [ f ]) .pred = P .pred S.[ f ]
(P [ f ]) .closed = begin
    𝐂 (P .pred S.[ f ]) ≤⟨ 𝐂-[] ⟩
    𝐂 (P .pred) S.[ f ] ≤⟨ (P .closed) S.[ f ]m ⟩
    P .pred S.[ f ]     ∎
  where open ≤-Reasoning S.⊑-isPreorder

_⟨_⟩ : ∀ {X Y} → Predicate X → X 𝒞.⇒ Y → Predicate Y
(P ⟨ f ⟩) .pred = 𝐂 (P .pred S.⟨ f ⟩)
(P ⟨ f ⟩) .closed = 𝐂-isClosure .closed

adjoint₁ : ∀ {X Y} {P : Predicate X} {Q : Predicate Y} {f : X 𝒞.⇒ Y} → P ⟨ f ⟩ ⊑ Q → P ⊑ Q [ f ]
adjoint₁ {X} {Y} {P} {Q} {f} ϕ = S.adjoint₁ (begin
    P .pred S.⟨ f ⟩       ≤⟨ 𝐂-isClosure .unit ⟩
    𝐂 (P .pred S.⟨ f ⟩)  ≤⟨ ϕ ⟩
    Q .pred               ∎)
  where open ≤-Reasoning S.⊑-isPreorder

adjoint₂ : ∀ {X Y} {P : Predicate X} {Q : Predicate Y} {f : X 𝒞.⇒ Y} → P ⊑ Q [ f ] → P ⟨ f ⟩ ⊑ Q
adjoint₂ {X} {Y} {P} {Q} {f} ϕ = begin
    𝐂 (P .pred S.⟨ f ⟩)
  ≤⟨ 𝐂-isClosure .mono (S.adjoint₂ ϕ) ⟩
    𝐂 (Q .pred)
  ≤⟨ Q .closed ⟩
    Q .pred
  ∎
  where open ≤-Reasoning S.⊑-isPreorder

TT : ∀ {X} → Predicate X
TT .pred = S.TT
TT .closed = IsTop.≤-top S.TT-isTop

_&&_ : ∀ {X} → Predicate X → Predicate X → Predicate X
(P && Q) .pred = P .pred S.&& Q .pred
(P && Q) .closed =
  S.&&-isMeet .⟨_,_⟩
    (S⊑-trans (𝐂-isClosure .mono (S.&&-isMeet .π₁)) (P .closed))
    (S⊑-trans (𝐂-isClosure .mono (S.&&-isMeet .π₂)) (Q .closed))

_++_ : ∀ {X} → Predicate X → Predicate X → Predicate X
(P ++ Q) .pred = 𝐂 (P .pred S.++ Q .pred)
(P ++ Q) .closed = 𝐂-isClosure .closed

_==>_ : ∀ {X} → Predicate X → Predicate X → Predicate X
(P ==> Q) .pred = P .pred S.==> Q .pred
(P ==> Q) .closed = S.==>-residual .IsResidual.lambda (begin
    (𝐂 (P .pred S.==> Q .pred) S.&& P .pred)
  ≤⟨ 𝐂-strong ⟩
    𝐂 ((P .pred S.==> Q .pred) S.&& P .pred)
  ≤⟨ 𝐂-isClosure .mono (S.==>-residual .IsResidual.eval) ⟩
    𝐂 (Q .pred)
  ≤⟨ Q .closed ⟩
    Q .pred
  ∎)
  where open ≤-Reasoning S.⊑-isPreorder

⋀ : ∀ {X Y} → Predicate (𝒞P.prod X Y) → Predicate X
⋀ P .pred = S.⋀ (P .pred)
⋀ P .closed = S.⋀-lambda (begin
    (𝐂 (S.⋀ (P .pred)) S.[ 𝒞P.p₁ ])
  ≤⟨ 𝐂-[]⁻¹ ⟩
    𝐂 (S.⋀ (P .pred) S.[ 𝒞P.p₁ ])
  ≤⟨ 𝐂-isClosure .mono S.⋀-eval ⟩
    𝐂 (P .pred)
  ≤⟨ P .closed ⟩
    P .pred
  ∎)
  where open ≤-Reasoning S.⊑-isPreorder

++-isJoin : ∀ {X} → IsJoin (⊑-isPreorder {X}) _++_
++-isJoin .inl = S⊑-trans (S.++-isJoin .inl) (𝐂-isClosure .unit)
++-isJoin .inr = S⊑-trans (S.++-isJoin .inr) (𝐂-isClosure .unit)
++-isJoin .[_,_] {P} {Q} {R} ϕ ψ = begin
    𝐂 (P .pred S.++ Q .pred)
  ≤⟨ 𝐂-isClosure .mono (S.++-isJoin .[_,_] ϕ ψ) ⟩
    𝐂 (R .pred)
  ≤⟨ R .closed ⟩
    R .pred
  ∎ where open ≤-Reasoning S.⊑-isPreorder

[]-++     : ∀ {X Y} {P Q : Predicate Y} {f : X 𝒞.⇒ Y} → ((P ++ Q) [ f ]) ⊑ ((P [ f ]) ++ (Q [ f ]))
[]-++ {X} {Y} {P} {Q} {f} = begin
    𝐂 (P .pred S.++ Q .pred) S.[ f ]
  ≤⟨ 𝐂-[]⁻¹ ⟩
    𝐂 ((P .pred S.++ Q .pred) S.[ f ])
  ≤⟨ 𝐂-isClosure .mono S.[]-++ ⟩
    𝐂 ((P .pred S.[ f ]) S.++ (Q .pred S.[ f ]))
  ∎
  where open ≤-Reasoning S.⊑-isPreorder

-- Meets distribute over the closed joins and satisfy Frobenius with the closed direct images,
-- provided they do in the underlying system: the closure's strength carries the meet inside.
module distributive
    (S-dist : ∀ {X} {P Q R : S.Predicate X} →
              (P S.&& (Q S.++ R)) S.⊑ ((P S.&& Q) S.++ (P S.&& R)))
    (S-frob : ∀ {X Y} {P : S.Predicate Y} {Q : S.Predicate X} {f : X 𝒞.⇒ Y} →
              (P S.&& (Q S.⟨ f ⟩)) S.⊑ (((P S.[ f ]) S.&& Q) S.⟨ f ⟩))
    where

  &&-++-distrib : ∀ {X} {P Q R : Predicate X} → (P && (Q ++ R)) ⊑ ((P && Q) ++ (P && R))
  &&-++-distrib {X} {P} {Q} {R} = begin
      P .pred S.&& 𝐂 (Q .pred S.++ R .pred)
    ≤⟨ IsMeet.comm (S.&&-isMeet) ⟩
      𝐂 (Q .pred S.++ R .pred) S.&& P .pred
    ≤⟨ 𝐂-strong ⟩
      𝐂 ((Q .pred S.++ R .pred) S.&& P .pred)
    ≤⟨ 𝐂-isClosure .mono (IsMeet.comm (S.&&-isMeet)) ⟩
      𝐂 (P .pred S.&& (Q .pred S.++ R .pred))
    ≤⟨ 𝐂-isClosure .mono S-dist ⟩
      𝐂 ((P .pred S.&& Q .pred) S.++ (P .pred S.&& R .pred))
    ∎
    where open ≤-Reasoning S.⊑-isPreorder

  &&-⟨⟩-frobenius : ∀ {X Y} {P : Predicate Y} {Q : Predicate X} {f : X 𝒞.⇒ Y} →
                    (P && (Q ⟨ f ⟩)) ⊑ (((P [ f ]) && Q) ⟨ f ⟩)
  &&-⟨⟩-frobenius {X} {Y} {P} {Q} {f} = begin
      P .pred S.&& 𝐂 (Q .pred S.⟨ f ⟩)
    ≤⟨ IsMeet.comm (S.&&-isMeet) ⟩
      𝐂 (Q .pred S.⟨ f ⟩) S.&& P .pred
    ≤⟨ 𝐂-strong ⟩
      𝐂 ((Q .pred S.⟨ f ⟩) S.&& P .pred)
    ≤⟨ 𝐂-isClosure .mono (IsMeet.comm (S.&&-isMeet)) ⟩
      𝐂 (P .pred S.&& (Q .pred S.⟨ f ⟩))
    ≤⟨ 𝐂-isClosure .mono S-frob ⟩
      𝐂 (((P .pred S.[ f ]) S.&& Q .pred) S.⟨ f ⟩)
    ∎
    where open ≤-Reasoning S.⊑-isPreorder

⋁ : ∀ {X} (I : Set 0ℓ) → (I → Predicate X) → Predicate X
⋁ I P .pred = 𝐂 (S.⋁ I (λ i → P i .pred))
⋁ I P .closed = 𝐂-isClosure .closed

⋁-isJoin : ∀ {X} → IsBigJoin (⊑-isPreorder {X}) 0ℓ ⋁
⋁-isJoin .IsBigJoin.upper I P i =
  S⊑-trans (IsBigJoin.upper S.⋁-isJoin _ _ i) (𝐂-isClosure .unit)
⋁-isJoin .IsBigJoin.least I P Q ϕ = begin
    𝐂 (S.⋁ I (λ i → P i .pred))
  ≤⟨ 𝐂-isClosure .mono (IsBigJoin.least S.⋁-isJoin _ _ _ ϕ) ⟩
    𝐂 (Q .pred)
  ≤⟨ Q .closed ⟩
    Q .pred
  ∎
  where open ≤-Reasoning S.⊑-isPreorder

[]-⋁ : ∀ {X Y I} {P : I → Predicate Y} {f : X 𝒞.⇒ Y} → (⋁ I P [ f ]) ⊑ ⋁ I (λ i → P i [ f ])
[]-⋁ {X} {Y} {I} {P} {f} = begin
    𝐂 (S.⋁ I (λ i → P i .pred)) S.[ f ]
  ≤⟨ 𝐂-[]⁻¹ ⟩
    𝐂 (S.⋁ I (λ i → P i .pred) S.[ f ])
  ≤⟨ 𝐂-isClosure .mono S.[]-⋁ ⟩
    𝐂 (S.⋁ I (λ i → P i .pred S.[ f ]))
  ∎
  where open ≤-Reasoning S.⊑-isPreorder

system : PredicateSystem 𝒞 𝒞P
system .PredicateSystem.Predicate = Predicate
system .PredicateSystem._⊑_ = _⊑_
system .PredicateSystem.⊑-isPreorder = ⊑-isPreorder
system .PredicateSystem._[_] = _[_]
system .PredicateSystem._⟨_⟩ = _⟨_⟩
system .PredicateSystem._[_]m = S._[_]m
system .PredicateSystem.[]-cong = S.[]-cong
system .PredicateSystem.[]-id = S.[]-id
system .PredicateSystem.[]-id⁻¹ = S.[]-id⁻¹
system .PredicateSystem.[]-comp = S.[]-comp
system .PredicateSystem.[]-comp⁻¹ = S.[]-comp⁻¹
system .PredicateSystem.adjoint₁ {X} {Y} {P} {Q} = adjoint₁ {X} {Y} {P} {Q}
system .PredicateSystem.adjoint₂ {X} {Y} {P} {Q} = adjoint₂ {X} {Y} {P} {Q}
system .PredicateSystem.TT = TT
system .PredicateSystem._&&_ = _&&_
system .PredicateSystem._++_ = _++_
system .PredicateSystem._==>_ = _==>_
system .PredicateSystem.⋀ = ⋀
system .PredicateSystem.TT-isTop = record { ≤-top = λ {x} → ≤-top S.TT-isTop }
system .PredicateSystem.[]-TT = S.[]-TT
system .PredicateSystem.&&-isMeet .π₁ = π₁ S.&&-isMeet
system .PredicateSystem.&&-isMeet .π₂ = π₂ S.&&-isMeet
system .PredicateSystem.&&-isMeet .⟨_,_⟩ = ⟨_,_⟩ S.&&-isMeet
system .PredicateSystem.[]-&& = S.[]-&&
system .PredicateSystem.++-isJoin = ++-isJoin
system .PredicateSystem.[]-++ {X} {Y} {P} {Q} = []-++ {X} {Y} {P} {Q}
system .PredicateSystem.==>-residual .IsResidual.lambda = IsResidual.lambda S.==>-residual
system .PredicateSystem.==>-residual .IsResidual.eval = IsResidual.eval S.==>-residual
system .PredicateSystem.[]-==> = S.[]-==>
system .PredicateSystem.⋀-[] = S.⋀-[]
system .PredicateSystem.⋀-eval = S.⋀-eval
system .PredicateSystem.⋀-lambda = S.⋀-lambda
system .PredicateSystem.⋁ = ⋁
system .PredicateSystem.⋁-isJoin = ⋁-isJoin
system .PredicateSystem.[]-⋁ {X} {Y} {I} {P} = []-⋁ {X} {Y} {I} {P}

-- If we have a functor lifting, then it also works on the closed predicates
--
-- FIXME: we only need the distributivity if we want the functor to
-- commute laxly with ⟨⟩, which is only needed for it to be a monad.
module 𝐂Functor (F : Functor 𝒞 𝒞) (FP : FunctorPred _ _ S F)
       (distrib : ∀ {X} {P : S.Predicate X} → FP .FunctorPred.liftF (𝐂 P) S.⊑ 𝐂 (FP .FunctorPred.liftF P))
    where

  open FunctorPred

  𝐂FP : FunctorPred _ _ system F
  𝐂FP .FunctorPred.liftF P = embed (FP .liftF (P .pred))
  𝐂FP .FunctorPred.liftF-⊑ P⊑Q = 𝐂-isClosure .mono (FP .liftF-⊑ P⊑Q)
  𝐂FP .FunctorPred.liftF-[] f = S⊑-trans (𝐂-isClosure .mono (FP .liftF-[] f)) 𝐂-[]
  𝐂FP .FunctorPred.liftF-⟨⟩ f =
    S⊑-trans (𝐂-isClosure .mono distrib)
   (S⊑-trans (𝐂-isClosure .mono (𝐂-isClosure .mono (FP .liftF-⟨⟩ f)))
   (S⊑-trans (𝐂-isClosure .closed)
             (𝐂-isClosure .mono ((𝐂-isClosure .unit) S.⟨ _ ⟩m))))

-- If we have a Monad that distributes over the closure, then this
-- also lifts to the closed predicates.
module 𝐂Monad (M : Monad 𝒞) (MP : MonadPred _ _  S M)
               (distrib : ∀ {X} {P : S.Predicate X} → MP .MonadPred.liftF (𝐂 P) S.⊑ 𝐂 (MP .MonadPred.liftF P))
          where

  open FunctorPred
  open NatTrans
  open Monad M renaming (funct to Mfunct; unit to Munit)
  open MonadPred MP
  open 𝐂Functor _ functP distrib

  𝐂MP : MonadPred _ _ system M
  𝐂MP .MonadPred.functP = 𝐂FP
  𝐂MP .MonadPred.unitP {X} {P} = S⊑-trans unitP ((𝐂-isClosure .IsClosureOp.unit) S.[ (Munit .transf X) ]m)
  𝐂MP .MonadPred.joinP {X} {P} =
    S⊑-trans (𝐂-isClosure .mono distrib)
   (S⊑-trans (𝐂-isClosure .closed)
   (S⊑-trans (𝐂-isClosure .mono joinP)
             𝐂-[]))

    -- FIXME: strength
