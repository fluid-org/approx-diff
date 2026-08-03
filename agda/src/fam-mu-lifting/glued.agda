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

-- The lifting on glued objects: the payload predicate pushed under the injection, joined with the
-- root part.
Lf-Gl : Gl.Obj → Gl.Obj
Lf-Gl X .carrier = R.Lf (X .carrier)
Lf-Gl X .pred = (X .pred ⟨ G .fmor (R.injF {X = X .carrier}) ⟩) ++ Rt (X .carrier)

injF-Gl : ∀ {X} → X Gl.=> Lf-Gl X
injF-Gl {X} .morph = R.injF
injF-Gl {X} .presv = begin
    X .pred
  ≤⟨ unit (G .fmor R.injF) ⟩
    (X .pred ⟨ G .fmor (R.injF {X = X .carrier}) ⟩) [ G .fmor R.injF ]
  ≤⟨ (++-isJoin .IsJoin.inl) [ G .fmor R.injF ]m ⟩
    ((X .pred ⟨ G .fmor (R.injF {X = X .carrier}) ⟩) ++ Rt (X .carrier)) [ G .fmor R.injF ]
  ∎
  where open basics.≤-Reasoning ⊑-isPreorder

private module 𝒫C = Category 𝒫

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

-- The glued lifting is functorial at morphisms whose payload square with the injection holds,
-- which the lifting grants at fibrewise isomorphisms; the root part is supplied by the caller,
-- being knowledge about the root predicate.
Lf-Gl-map : ∀ {X Y} (f : X Gl.=> Y) →
            R.Fam𝒞._≈_ (R.Fam𝒞._∘_ (R.Lf-map (f .morph)) R.injF)
                        (R.Fam𝒞._∘_ R.injF (f .morph)) →
            (Rt (X .carrier) ⊑ (Rt (Y .carrier) [ G .fmor (R.Lf-map (f .morph)) ])) →
            Lf-Gl X Gl.=> Lf-Gl Y
Lf-Gl-map f sq rt .morph = R.Lf-map (f .morph)
Lf-Gl-map {X} {Y} f sq rt .presv =
  ++-isJoin .IsJoin.[_,_]
    (adjoint₂
      (⊑-trans (f .presv)
      (⊑-trans ((injF-Gl {Y} .presv) [ G .fmor (f .morph) ]m)
      (⊑-trans ([]-comp _ _)
      (⊑-trans ([]-cong (𝒫C.≈-sym (G .fmor-comp _ _)))
      (⊑-trans ([]-cong (G .fmor-cong (R.Fam𝒞.≈-sym sq)))
      (⊑-trans ([]-cong (G .fmor-comp _ _))
               ([]-comp⁻¹ _ _))))))))
    (⊑-trans rt ((++-isJoin .IsJoin.inr) [ G .fmor (R.Lf-map (f .morph)) ]m))

-- The eliminator on glued objects, over the underlying eliminator. The lifted predicate splits
-- into its payload and root parts and each branch is a parameter: the root branch is instance
-- knowledge about the eliminator's constant at bare roots, and the payload branch is predicate
-- preservation for `elim-inj`, the closed form of the eliminator restricted along the payload
-- injection. The payload branch transports to the eliminator itself by the Beck-Chevalley square
-- at the second projection, Frobenius reciprocity and the restriction law `elimF-inj`.
module elim
    (dist : ∀ {V} {P Q S : Predicate V} → (P && (Q ++ S)) ⊑ ((P && Q) ++ (P && S)))
    (frob : ∀ {V V'} {P : Predicate V'} {Q : Predicate V} {α : V 𝒫C.⇒ V'} →
            (P && (Q ⟨ α ⟩)) ⊑ (((P [ α ]) && Q) ⟨ α ⟩))
    (BC : ∀ {W U V : R.Obj} (h : R.Mor U V) {Q : Predicate (G .fobj U)} →
          ((Q ⟨ G .fmor h ⟩) [ G .fmor (R.Fam𝒞-P.p₂ {W} {V}) ])
            ⊑ ((Q [ G .fmor (R.Fam𝒞-P.p₂ {W} {U}) ])
                 ⟨ G .fmor (R.Fam𝒞-P.pair R.Fam𝒞-P.p₁ (R.Fam𝒞._∘_ h R.Fam𝒞-P.p₂)) ⟩))
    {Γ X C : Gl.Obj} (ptC : R.Pointed (C .carrier))
    (f : R.Mor (R.Fam𝒞-P.prod (Γ .carrier) (X .carrier)) (C .carrier))
    (payload : (Γ [×] X) .pred ⊑ (C .pred [ G .fmor (R.elim-inj ptC f) ]))
    (root : ((Γ .pred [ G .fmor R.Fam𝒞-P.p₁ ]) && (Rt (X .carrier) [ G .fmor R.Fam𝒞-P.p₂ ]))
            ⊑ (C .pred [ G .fmor (R.elimF ptC f) ]))
    where

  private
    Γc = Γ .carrier
    Xc = X .carrier
    em = R.elimF ptC f
    pr = R.Fam𝒞-P.pair (R.Fam𝒞-P.p₁ {Γc} {Xc}) (R.Fam𝒞._∘_ R.injF (R.Fam𝒞-P.p₂ {Γc} {Xc}))

    -- The closed-form restriction is the eliminator after the payload injection in context.
    bridge : R.Fam𝒞._≈_ (R.elim-inj ptC f) (R.Fam𝒞._∘_ em pr)
    bridge =
      R.Fam𝒞.≈-trans (R.Fam𝒞.≈-sym (R.elimF-inj ptC f))
        (R.Fam𝒞.∘-cong R.Fam𝒞.≈-refl (R.Fam𝒞-P.pair-cong R.Fam𝒞.id-left R.Fam𝒞.≈-refl))

    -- The context leg passes the pairing untouched.
    ctx-fix : ((Γ .pred [ G .fmor (R.Fam𝒞-P.p₁ {Γc} {R.Lf Xc}) ]) [ G .fmor pr ])
              ⊑ (Γ .pred [ G .fmor (R.Fam𝒞-P.p₁ {Γc} {Xc}) ])
    ctx-fix =
      ⊑-trans ([]-comp _ _)
      (⊑-trans ([]-cong (𝒫C.≈-sym (G .fmor-comp _ _)))
               ([]-cong (G .fmor-cong (R.Fam𝒞-P.pair-p₁ _ _))))

    payload-leg : ((Γ .pred [ G .fmor (R.Fam𝒞-P.p₁ {Γc} {R.Lf Xc}) ])
                    && ((X .pred ⟨ G .fmor R.injF ⟩) [ G .fmor (R.Fam𝒞-P.p₂ {Γc} {R.Lf Xc}) ]))
                  ⊑ (C .pred [ G .fmor em ])
    payload-leg = begin
        (Γ .pred [ G .fmor (R.Fam𝒞-P.p₁ {Γc} {R.Lf Xc}) ])
          && ((X .pred ⟨ G .fmor R.injF ⟩) [ G .fmor (R.Fam𝒞-P.p₂ {Γc} {R.Lf Xc}) ])
      ≤⟨ IsMeet.mono &&-isMeet (⊑-isPreorder .IsPreorder.refl) (BC R.injF) ⟩
        (Γ .pred [ G .fmor (R.Fam𝒞-P.p₁ {Γc} {R.Lf Xc}) ])
          && ((X .pred [ G .fmor (R.Fam𝒞-P.p₂ {Γc} {Xc}) ]) ⟨ G .fmor pr ⟩)
      ≤⟨ frob ⟩
        (((Γ .pred [ G .fmor (R.Fam𝒞-P.p₁ {Γc} {R.Lf Xc}) ]) [ G .fmor pr ])
          && (X .pred [ G .fmor (R.Fam𝒞-P.p₂ {Γc} {Xc}) ])) ⟨ G .fmor pr ⟩
      ≤⟨ (IsMeet.mono &&-isMeet ctx-fix (⊑-isPreorder .IsPreorder.refl)) ⟨ G .fmor pr ⟩m ⟩
        ((Γ [×] X) .pred) ⟨ G .fmor pr ⟩
      ≤⟨ payload ⟨ G .fmor pr ⟩m ⟩
        (C .pred [ G .fmor (R.elim-inj ptC f) ]) ⟨ G .fmor pr ⟩
      ≤⟨ ([]-cong (G .fmor-cong bridge)) ⟨ G .fmor pr ⟩m ⟩
        (C .pred [ G .fmor (R.Fam𝒞._∘_ em pr) ]) ⟨ G .fmor pr ⟩
      ≤⟨ ([]-cong (G .fmor-comp _ _)) ⟨ G .fmor pr ⟩m ⟩
        (C .pred [ G .fmor em 𝒫C.∘ G .fmor pr ]) ⟨ G .fmor pr ⟩
      ≤⟨ ([]-comp⁻¹ _ _) ⟨ G .fmor pr ⟩m ⟩
        ((C .pred [ G .fmor em ]) [ G .fmor pr ]) ⟨ G .fmor pr ⟩
      ≤⟨ counit _ ⟩
        C .pred [ G .fmor em ]
      ∎
      where open basics.≤-Reasoning ⊑-isPreorder

  elimF-Gl : (Γ [×] Lf-Gl X) Gl.=> C
  elimF-Gl .morph = em
  elimF-Gl .presv = begin
      (Γ .pred [ G .fmor R.Fam𝒞-P.p₁ ])
        && (((X .pred ⟨ G .fmor R.injF ⟩) ++ Rt Xc) [ G .fmor R.Fam𝒞-P.p₂ ])
    ≤⟨ IsMeet.mono &&-isMeet (⊑-isPreorder .IsPreorder.refl) []-++ ⟩
      (Γ .pred [ G .fmor R.Fam𝒞-P.p₁ ])
        && (((X .pred ⟨ G .fmor R.injF ⟩) [ G .fmor R.Fam𝒞-P.p₂ ])
              ++ (Rt Xc [ G .fmor R.Fam𝒞-P.p₂ ]))
    ≤⟨ dist ⟩
      ((Γ .pred [ G .fmor R.Fam𝒞-P.p₁ ])
         && ((X .pred ⟨ G .fmor R.injF ⟩) [ G .fmor R.Fam𝒞-P.p₂ ]))
        ++ ((Γ .pred [ G .fmor R.Fam𝒞-P.p₁ ]) && (Rt Xc [ G .fmor R.Fam𝒞-P.p₂ ]))
    ≤⟨ ++-isJoin .IsJoin.[_,_] payload-leg root ⟩
      C .pred [ G .fmor em ]
    ∎
    where open basics.≤-Reasoning ⊑-isPreorder
