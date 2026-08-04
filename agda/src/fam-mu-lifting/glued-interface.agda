{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- The interface to the glued rooted μ-types: a record bundling every
-- instance obligation of the algebra map and the fold, and a module that,
-- given the obligations, delivers the decorated μ-carrier together with its
-- algebra map and catamorphism as glued morphisms, at every polynomial and
-- environment.
------------------------------------------------------------------------------

open import Level using (Level; 0ℓ; Lift; lift; _⊔_) renaming (suc to lsuc)
open import Data.Nat using (ℕ; suc)
import Data.Fin as Fin
open Fin using (Fin)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import prop using (_,_)
open import basics using (IsPreorder; IsJoin; IsMeet; IsBigJoin; IsClosureOp)
open import prop-setoid as PS using ()
open import categories using (Category; HasTerminal; HasProducts; HasCoproducts)
open import cmon-enriched using (CMonEnriched; Biproduct)
open import lifting using (Lifting)
open import functor using (Functor)
open import predicate-system using (PredicateSystem; ClosureOp)
open import indexed-family using (_⇒f_)
import fam-mu-lifting.laws
import fam-mu-lifting.glued-fold

module fam-mu-lifting.glued-interface {o m e} {𝒞 : Category o m e}
  (T : HasTerminal 𝒞) (CM : CMonEnriched 𝒞) (BP : ∀ x y → Biproduct CM x y)
  {𝟙c : Category.obj 𝒞} (Lft : Lifting CM 𝟙c)
  (let module R = fam-mu-lifting.laws 0ℓ 0ℓ T CM BP Lft)
  {o₂ m₂ e₂} (𝒫 : Category o₂ m₂ e₂) (𝒫P : HasProducts 𝒫)
  (system : PredicateSystem 𝒫 𝒫P)
  (G : Functor R.cat 𝒫)
  (let open PredicateSystem system)
  (Rt : ∀ (C : R.Obj) → Predicate (Functor.fobj G (R.Lf C)))
  (Cl : ClosureOp 𝒫 𝒫P system)
  where

open Functor

open fam-mu-lifting.glued-fold T CM BP Lft 𝒫 𝒫P system G Rt Cl public

open R hiding (fobj)
open Gl.Obj
open Gl._=>_
open ClosureOp Cl

private
  module 𝒫C'' = Category 𝒫
  module CP'' = HasCoproducts coproducts

  ℓI : Level
  ℓI = lsuc (lsuc 0ℓ) ⊔ lsuc o ⊔ lsuc m ⊔ lsuc e ⊔ lsuc o₂ ⊔ lsuc m₂ ⊔ lsuc e₂

-- Every instance obligation of the glued algebra map and fold, fully
-- quantified. The reindexing squares are knowledge about the predicate
-- system at the singleton inclusions and injections; the two additive
-- obligations absorb the roots the eliminations create; the split and the
-- extraction mediate between an object and its singletons through the
-- closure.
record GlMuObligations : Set ℓI where
  field
    Rt-iso : ∀ {C D : Obj} (h : Mor C D)
             (hinv : ∀ x → D .fam .fm (h .idxf .PS._⇒_.func x) ⇒ C .fam .fm x) →
             (∀ x → (h .famf ._⇒f_.transf x ∘ hinv x) ≈ id _) →
             (∀ x → (hinv x ∘ h .famf ._⇒f_.transf x) ≈ id _) →
             Rt C ⊑ (Rt D [ G .fmor (Lf-map h) ])
    Rt-iso⁻ : ∀ {C D : Obj} (h : Mor C D)
              (hinv : ∀ x → D .fam .fm (h .idxf .PS._⇒_.func x) ⇒ C .fam .fm x) →
              (∀ x → (h .famf ._⇒f_.transf x ∘ hinv x) ≈ id _) →
              (∀ x → (hinv x ∘ h .famf ._⇒f_.transf x) ≈ id _) →
              (Rt D [ G .fmor (Lf-map h) ]) ⊑ Rt C
    in₁-extract : ∀ {X Y : Obj} {Q : Predicate (G .fobj X)} →
                  ((Q ⟨ G .fmor (CP''.in₁ {X} {Y}) ⟩) [ G .fmor (CP''.in₁ {X} {Y}) ]) ⊑ Q
    in₂-extract : ∀ {X Y : Obj} {Q : Predicate (G .fobj Y)} →
                  ((Q ⟨ G .fmor (CP''.in₂ {X} {Y}) ⟩) [ G .fmor (CP''.in₂ {X} {Y}) ]) ⊑ Q
    disjoint₁ : ∀ {X Y : Obj} {Q : Predicate (G .fobj Y)} (x : X .idx .Carrier)
                {S : Predicate (G .fobj simple[ PS.𝟙 , X .fam .fm x ])} →
                ((Q ⟨ G .fmor (CP''.in₂ {X} {Y}) ⟩)
                   [ G .fmor (elem-in (CP''.coprod X Y) (inj₁ x)) ]) ⊑ S
    disjoint₂ : ∀ {X Y : Obj} {Q : Predicate (G .fobj X)} (y : Y .idx .Carrier)
                {S : Predicate (G .fobj simple[ PS.𝟙 , Y .fam .fm y ])} →
                ((Q ⟨ G .fmor (CP''.in₁ {X} {Y}) ⟩)
                   [ G .fmor (elem-in (CP''.coprod X Y) (inj₂ y)) ]) ⊑ S
    BC-assemble : ∀ {C : Obj} {Qp : Predicate (G .fobj (Fam𝒞-P.prod C 𝟙L))}
                  (x : C .idx .Carrier) →
                  ((Qp ⟨ G .fmor (assembleF {C}) ⟩) [ G .fmor (elem-in (Lf C) x) ])
                    ⊑ ((Qp [ G .fmor (elem-in (Fam𝒞-P.prod C 𝟙L) (x , lift tt)) ])
                         ⟨ G .fmor (sing-assemble C x) ⟩)
    sing-extract : ∀ {k} (δ₀ : Fin k → Obj) (δP₀ : ∀ i → Predicate (G .fobj (δ₀ i)))
                   (Q : Poly (suc k)) (pQ : PolyPred Q)
                   (t : Tree.W δ₀ ∣ Q ∣ (λ i → inj₁ i)) →
                   (MuPred.μ-Gl δ₀ δP₀ Q pQ .pred [ G .fmor (elem-in (μObj Q δ₀) t) ])
                     ⊑ (MuPred.fib-Gl δ₀ δP₀ Q (λ i → lift tt) pQ (λ i → lift tt) t .pred
                          [ G .fmor (MuPred.tree-out δ₀ δP₀ Q pQ t) ])
    sing-split : ∀ {X : Obj} {Q : Predicate (G .fobj X)} →
                 Q ⊑ 𝐂 (⋁ (X .idx .Carrier)
                         (λ x → (Q [ G .fmor (elem-in X x) ]) ⟨ G .fmor (elem-in X x) ⟩))
    payload-sing : ∀ (Γg Xg Yg : Gl.Obj) (γ : Γg .carrier .idx .Carrier)
                   (ι : Xg .carrier .idx .Carrier)
                   (hs : Mor simple[ PS.𝟙 , prod (Γg .carrier .fam .fm γ)
                                             (Xg .carrier .fam .fm ι) ]
                             (Yg .carrier)) →
                   (((Γg [×] Xg) .pred
                       [ G .fmor (elem-in (Fam𝒞-P.prod (Γg .carrier) (Xg .carrier))
                                          (γ , ι)) ])
                     ⊑ (Yg .pred [ G .fmor hs ])) →
                   ((((Γg .pred [ G .fmor Fam𝒞-P.p₁ ])
                       && (((Xg .pred [ G .fmor (Fam𝒞-P.p₁ {Xg .carrier} {𝟙L}) ])
                              ⟨ G .fmor (assembleF {Xg .carrier}) ⟩)
                             [ G .fmor Fam𝒞-P.p₂ ]))
                       [ G .fmor (elem-in (Fam𝒞-P.prod (Γg .carrier) (Lf (Xg .carrier)))
                                          (γ , ι)) ])
                     ⊑ (Lf-Gl Yg .pred [ G .fmor (sing-under-root hs) ]))
    root-sing : ∀ (Γg Xg Yg : Gl.Obj) (γ : Γg .carrier .idx .Carrier)
                (ι : Xg .carrier .idx .Carrier)
                (hs : Mor simple[ PS.𝟙 , prod (Γg .carrier .fam .fm γ)
                                          (Xg .carrier .fam .fm ι) ]
                          (Yg .carrier)) →
                (((Γg [×] Xg) .pred
                    [ G .fmor (elem-in (Fam𝒞-P.prod (Γg .carrier) (Xg .carrier))
                                       (γ , ι)) ])
                  ⊑ (Yg .pred [ G .fmor hs ])) →
                ((((Γg .pred [ G .fmor Fam𝒞-P.p₁ ])
                    && (Rt (Xg .carrier) [ G .fmor Fam𝒞-P.p₂ ]))
                    [ G .fmor (elem-in (Fam𝒞-P.prod (Γg .carrier) (Lf (Xg .carrier)))
                                       (γ , ι)) ])
                  ⊑ (Lf-Gl Yg .pred [ G .fmor (sing-under-root hs) ]))
    dist : ∀ {V} {Pp Q S : Predicate V} → (Pp && (Q ++ S)) ⊑ ((Pp && Q) ++ (Pp && S))
    dist-⋁ : ∀ {V} {I : Set 0ℓ} {Pp : Predicate V} {Qs : I → Predicate V} →
             (Pp && ⋁ I Qs) ⊑ ⋁ I (λ i → Pp && Qs i)
    frob : ∀ {V V'} {Pp : Predicate V'} {Q : Predicate V} {α : V 𝒫C''.⇒ V'} →
           (Pp && (Q ⟨ α ⟩)) ⊑ (((Pp [ α ]) && Q) ⟨ α ⟩)
    BC : ∀ {W U V : Obj} (h : Mor U V) {Q : Predicate (G .fobj U)} →
         ((Q ⟨ G .fmor h ⟩) [ G .fmor (Fam𝒞-P.p₂ {W} {V}) ])
           ⊑ ((Q [ G .fmor (Fam𝒞-P.p₂ {W} {U}) ])
                ⟨ G .fmor (Fam𝒞-P.pair Fam𝒞-P.p₁ (Fam𝒞._∘_ h Fam𝒞-P.p₂)) ⟩)

-- Given the obligations, the decorated μ-carrier with its algebra map and
-- catamorphism as glued morphisms.
module GlMu (Ob : GlMuObligations) where
  open GlMuObligations Ob

  module At {n} (P : Poly (suc n)) (pP : PolyPred P)
      (δ : Fin n → Obj) (δP : ∀ i → Predicate (G .fobj (δ i))) where

    open GlInMap P pP δ δP Rt-iso Rt-iso⁻ in₁-extract in₂-extract
                 disjoint₁ disjoint₂ BC-assemble sing-extract sing-split public

    private
      module Mδ = MuPred δ δP

    μGl : Gl.Obj
    μGl = Mδ.μ-Gl P pP

    -- The algebra map as a glued morphism.
    inMapGl : fobj-Gl P pP (extend δ (μObj P δ)) δP⁺ Gl.=> μGl
    inMapGl .morph = InMapDef.inMor P δ
    inMapGl .presv = inMap-Gl

    -- The catamorphism as a glued morphism, for an algebra preserving the
    -- glued interpretation into a closed target.
    foldGl : ∀ (Γg Ag : Gl.Obj)
             (alg : Mor (Fam𝒞-P.prod (Γg .carrier)
                           (R.fobj μObj P (extend δ (Ag .carrier))))
                        (Ag .carrier)) →
             (𝐂 (Ag .pred) ⊑ Ag .pred) →
             ((Γg [×] fobj-Gl P pP (extend δ (Ag .carrier))
                        (extend-pred δ δP (Ag .carrier) (Ag .pred))) .pred
               ⊑ (Ag .pred [ G .fmor alg ])) →
             (Γg [×] μGl) Gl.=> Ag
    foldGl Γg Ag alg A-closed algP .morph =
      FoldDef.foldMor {n} {Γg .carrier} {Ag .carrier} {P} {δ} alg
    foldGl Γg Ag alg A-closed algP .presv =
      GlFold.presv.fold-Gl P pP δ δP Γg Ag alg (payload-sing Γg) (root-sing Γg)
        sing-split dist dist-⋁ frob BC A-closed algP
