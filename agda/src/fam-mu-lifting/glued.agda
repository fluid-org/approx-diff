{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (Level; suc; _⊔_)
open import basics using (IsPreorder; IsJoin; IsMeet)
open import categories using (Category; HasTerminal; HasProducts)
open import cmon-enriched using (CMonEnriched; Biproduct)
open import functor using (Functor)
open import lifting using (Lifting)
open import predicate-system using (PredicateSystem)
import fam-mu-lifting.in-map
import glueing-simple

module fam-mu-lifting.glued
  {o m e} (os es : Level) {𝒞 : Category o m e}
  (T : HasTerminal 𝒞) (CM : CMonEnriched 𝒞) (BP : ∀ x y → Biproduct CM x y)
  {𝟙c : Category.obj 𝒞} (Lft : Lifting CM 𝟙c)
  (let module R = fam-mu-lifting.in-map os es T CM BP Lft)
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
