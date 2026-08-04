{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (Level; suc; _⊔_)
open import basics using (IsPreorder; IsJoin; IsMeet)
open import categories using (Category; HasTerminal; HasProducts)
open import cmon-enriched using (CMonEnriched; Biproduct)
open import functor using (Functor)
open import lifting using (Lifting)
open import predicate-system using (PredicateSystem)
import fam-mu-lifting.laws
import glueing-simple

module fam-mu-lifting.glued
  {o m e} (os es : Level) {𝒞 : Category o m e}
  (T : HasTerminal 𝒞) (CM : CMonEnriched 𝒞) (BP : ∀ x y → Biproduct CM x y)
  {𝟙c : Category.obj 𝒞} (Lft : Lifting CM 𝟙c)
  (let module R = fam-mu-lifting.laws os es T CM BP Lft)
  {o₂ m₂ e₂} (𝒫 : Category o₂ m₂ e₂) (𝒫P : HasProducts 𝒫)
  (system : PredicateSystem 𝒫 𝒫P)
  (G : Functor R.cat 𝒫)
  (let open PredicateSystem system)
  (Rt : ∀ (C : R.Obj) → Predicate (Functor.fobj G (R.Lf C)))
  where

open Functor

module Gl = glueing-simple R.cat 𝒫 𝒫P system G

open Gl.Obj
open Gl._=>_

private module 𝒫C = Category 𝒫

-- The lifting on glued objects: a payload predicate assembled with a root over it, joined with the
-- root part. The root joined onto the payload is left free, because an elimination charges the root
-- at the support of the value it consumed, which the payload's own support need not dominate.
Lf-Gl : Gl.Obj → Gl.Obj
Lf-Gl X .carrier = R.Lf (X .carrier)
Lf-Gl X .pred =
  ((X .pred [ G .fmor (R.Fam𝒞-P.p₁ {X .carrier} {R.𝟙L}) ])
     ⟨ G .fmor (R.assembleF {X .carrier}) ⟩)
    ++ Rt (X .carrier)

injF-Gl : ∀ {X} → X Gl.=> Lf-Gl X
injF-Gl {X} .morph = R.injF
injF-Gl {X} .presv = begin
    X .pred
  ≤⟨ []-id ⟩
    X .pred [ 𝒫C.id _ ]
  ≤⟨ []-cong (𝒫C.≈-sym (G .fmor-id)) ⟩
    X .pred [ G .fmor (R.Fam𝒞.id (X .carrier)) ]
  ≤⟨ []-cong (G .fmor-cong (R.Fam𝒞.≈-sym (R.Fam𝒞-P.pair-p₁ _ _))) ⟩
    X .pred [ G .fmor (R.Fam𝒞._∘_ R.Fam𝒞-P.p₁ pr) ]
  ≤⟨ []-cong (G .fmor-comp _ _) ⟩
    X .pred [ G .fmor R.Fam𝒞-P.p₁ 𝒫C.∘ G .fmor pr ]
  ≤⟨ []-comp⁻¹ _ _ ⟩
    (X .pred [ G .fmor (R.Fam𝒞-P.p₁ {X .carrier} {R.𝟙L}) ]) [ G .fmor pr ]
  ≤⟨ (unit (G .fmor R.assembleF)) [ G .fmor pr ]m ⟩
    (((X .pred [ G .fmor R.Fam𝒞-P.p₁ ]) ⟨ G .fmor (R.assembleF {X .carrier}) ⟩)
       [ G .fmor R.assembleF ]) [ G .fmor pr ]
  ≤⟨ []-comp _ _ ⟩
    ((X .pred [ G .fmor R.Fam𝒞-P.p₁ ]) ⟨ G .fmor (R.assembleF {X .carrier}) ⟩)
      [ G .fmor R.assembleF 𝒫C.∘ G .fmor pr ]
  ≤⟨ []-cong (𝒫C.≈-sym (G .fmor-comp _ _)) ⟩
    ((X .pred [ G .fmor R.Fam𝒞-P.p₁ ]) ⟨ G .fmor (R.assembleF {X .carrier}) ⟩)
      [ G .fmor (R.Fam𝒞._∘_ R.assembleF pr) ]
  ≤⟨ []-cong (G .fmor-cong R.injF-assemble) ⟩
    ((X .pred [ G .fmor R.Fam𝒞-P.p₁ ]) ⟨ G .fmor (R.assembleF {X .carrier}) ⟩)
      [ G .fmor R.injF ]
  ≤⟨ (++-isJoin .IsJoin.inl) [ G .fmor R.injF ]m ⟩
    Lf-Gl X .pred [ G .fmor R.injF ]
  ∎
  where
  open basics.≤-Reasoning ⊑-isPreorder
  pr = R.Fam𝒞-P.pair (R.Fam𝒞.id (X .carrier)) R.sptF

-- The product of glued objects, as the glueing category forms it: the product of the carriers
-- with the meet of the reindexed predicates.
_[×]_ : Gl.Obj → Gl.Obj → Gl.Obj
(X [×] Y) .carrier = R.Fam𝒞-P.prod (X .carrier) (Y .carrier)
(X [×] Y) .pred = (X .pred [ G .fmor R.Fam𝒞-P.p₁ ]) && (Y .pred [ G .fmor R.Fam𝒞-P.p₂ ])

-- The glued product is functorial.
[×]-map : ∀ {X X' Y Y'} → X Gl.=> X' → Y Gl.=> Y' →
          (X [×] Y) Gl.=> (X' [×] Y')
[×]-map f g .morph = R.Fam𝒞-P.prod-m (f .morph) (g .morph)
[×]-map {X} {X'} {Y} {Y'} f g .presv =
  ⊑-trans
    (IsMeet.mono &&-isMeet
      (⊑-trans ((f .presv) [ G .fmor R.Fam𝒞-P.p₁ ]m)
      (⊑-trans ([]-comp _ _)
      (⊑-trans ([]-cong (𝒫C.≈-sym (G .fmor-comp _ _)))
      (⊑-trans ([]-cong (G .fmor-cong (R.Fam𝒞.≈-sym (R.Fam𝒞-P.pair-p₁ _ _))))
      (⊑-trans ([]-cong (G .fmor-comp _ _))
               ([]-comp⁻¹ _ _))))))
      (⊑-trans ((g .presv) [ G .fmor R.Fam𝒞-P.p₂ ]m)
      (⊑-trans ([]-comp _ _)
      (⊑-trans ([]-cong (𝒫C.≈-sym (G .fmor-comp _ _)))
      (⊑-trans ([]-cong (G .fmor-cong (R.Fam𝒞.≈-sym (R.Fam𝒞-P.pair-p₂ _ _))))
      (⊑-trans ([]-cong (G .fmor-comp _ _))
               ([]-comp⁻¹ _ _)))))))
    []-&&

-- The glued lifting is functorial at morphisms whose payload square with the assembly holds, which
-- the lifting grants at fibrewise isomorphisms; the root part is supplied by the caller, being
-- knowledge about the root predicate.
Lf-Gl-map : ∀ {X Y} (f : X Gl.=> Y) →
            R.Fam𝒞._≈_ (R.Fam𝒞._∘_ (R.Lf-map (f .morph)) R.assembleF)
                        (R.Fam𝒞._∘_ R.assembleF
                           (R.Fam𝒞-P.prod-m (f .morph) (R.Fam𝒞.id R.𝟙L))) →
            (Rt (X .carrier) ⊑ (Rt (Y .carrier) [ G .fmor (R.Lf-map (f .morph)) ])) →
            Lf-Gl X Gl.=> Lf-Gl Y
Lf-Gl-map f sq rt .morph = R.Lf-map (f .morph)
Lf-Gl-map {X} {Y} f sq rt .presv =
  ++-isJoin .IsJoin.[_,_] (adjoint₂ payload)
    (⊑-trans rt ((++-isJoin .IsJoin.inr) [ G .fmor (R.Lf-map (f .morph)) ]m))
  where
  h = f .morph
  pm = R.Fam𝒞-P.prod-m h (R.Fam𝒞.id R.𝟙L)

  payload : (X .pred [ G .fmor (R.Fam𝒞-P.p₁ {X .carrier} {R.𝟙L}) ])
              ⊑ ((Lf-Gl Y .pred [ G .fmor (R.Lf-map h) ]) [ G .fmor R.assembleF ])
  payload = begin
      X .pred [ G .fmor R.Fam𝒞-P.p₁ ]
    ≤⟨ (f .presv) [ G .fmor R.Fam𝒞-P.p₁ ]m ⟩
      (Y .pred [ G .fmor h ]) [ G .fmor R.Fam𝒞-P.p₁ ]
    ≤⟨ []-comp _ _ ⟩
      Y .pred [ G .fmor h 𝒫C.∘ G .fmor R.Fam𝒞-P.p₁ ]
    ≤⟨ []-cong (𝒫C.≈-sym (G .fmor-comp _ _)) ⟩
      Y .pred [ G .fmor (R.Fam𝒞._∘_ h R.Fam𝒞-P.p₁) ]
    ≤⟨ []-cong (G .fmor-cong (R.Fam𝒞.≈-sym (R.Fam𝒞-P.pair-p₁ _ _))) ⟩
      Y .pred [ G .fmor (R.Fam𝒞._∘_ R.Fam𝒞-P.p₁ pm) ]
    ≤⟨ []-cong (G .fmor-comp _ _) ⟩
      Y .pred [ G .fmor R.Fam𝒞-P.p₁ 𝒫C.∘ G .fmor pm ]
    ≤⟨ []-comp⁻¹ _ _ ⟩
      (Y .pred [ G .fmor (R.Fam𝒞-P.p₁ {Y .carrier} {R.𝟙L}) ]) [ G .fmor pm ]
    ≤⟨ (unit (G .fmor R.assembleF)) [ G .fmor pm ]m ⟩
      (((Y .pred [ G .fmor R.Fam𝒞-P.p₁ ]) ⟨ G .fmor (R.assembleF {Y .carrier}) ⟩)
         [ G .fmor R.assembleF ]) [ G .fmor pm ]
    ≤⟨ ((++-isJoin .IsJoin.inl) [ G .fmor R.assembleF ]m) [ G .fmor pm ]m ⟩
      ((Lf-Gl Y .pred) [ G .fmor R.assembleF ]) [ G .fmor pm ]
    ≤⟨ []-comp _ _ ⟩
      Lf-Gl Y .pred [ G .fmor R.assembleF 𝒫C.∘ G .fmor pm ]
    ≤⟨ []-cong (𝒫C.≈-sym (G .fmor-comp _ _)) ⟩
      Lf-Gl Y .pred [ G .fmor (R.Fam𝒞._∘_ R.assembleF pm) ]
    ≤⟨ []-cong (G .fmor-cong (R.Fam𝒞.≈-sym sq)) ⟩
      Lf-Gl Y .pred [ G .fmor (R.Fam𝒞._∘_ (R.Lf-map h) R.assembleF) ]
    ≤⟨ []-cong (G .fmor-comp _ _) ⟩
      Lf-Gl Y .pred [ G .fmor (R.Lf-map h) 𝒫C.∘ G .fmor R.assembleF ]
    ≤⟨ []-comp⁻¹ _ _ ⟩
      (Lf-Gl Y .pred [ G .fmor (R.Lf-map h) ]) [ G .fmor R.assembleF ]
    ∎
    where open basics.≤-Reasoning ⊑-isPreorder

-- The whole-object glued eliminator is retired: the fold now works at the singletons, and the
-- eliminator's obligations have to be restated against the assembled payload, whose root the
-- elimination charges. The previous version is at commit 72adae86.
