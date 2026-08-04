{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- The rooted logical relations: the family-level construction of
-- conservativity-fam with the rooted μ-types glued on top. The model side of
-- that construction is already the category of families the rooted machinery
-- is built over, so its nerve serves as the glueing functor unchanged, and no
-- comparison between the two levels is needed. The root predicate picks out
-- the definable root selections: the maps into a lifted family that factor
-- through a bare root at some index, up to cover refinement.
------------------------------------------------------------------------------

open import Level using (Level; 0ℓ; lift)
open import Data.Nat using (suc)
import Data.Fin as Fin
open Fin using (Fin)
open import Data.Product using (_,_; proj₁)
open import Data.Unit using () renaming (tt to ttS)
open import prop using (Prf; ∃; ∃ₛ; _∧_; _,_; LiftP; lift; ⊥-elim; tt)
open import Data.Sum using (inj₁; inj₂)
open import prop-setoid as PS using (Setoid; module ≈-Reasoning)
open import basics using (IsPreorder; IsMeet; IsBigJoin; IsClosureOp)
open import categories
  using (Category; HasTerminal; HasProducts; HasCoproducts; HasWeakExponentials)
open import cmon-enriched using (CMonEnriched; Biproduct; biproducts→products)
open import lifting using (Lifting)
open import functor using (Functor; NatTrans)
open import indexed-family using (_⇒f_; _≃f_)
open import predicate-system using (PredicateSystem; ClosureOp)
open import finite-product-functor
  using (preserve-chosen-terminal; preserve-chosen-products)
import fam
import setoid-predicate
import closure-predicate
import fam-fibre-cover
import conservativity-fam
import fam-mu-lifting.laws
import fam-mu-lifting.glued-interface

module conservativity-rooted {o₁ o₂ m e}
  {𝒞₀ : Category o₁ m e} (𝒞₀T : HasTerminal 𝒞₀) (𝒞₀P : HasProducts 𝒞₀)
  {𝒟₀ : Category o₂ m e} (𝒟₀T : HasTerminal 𝒟₀)
  (CM' : CMonEnriched 𝒟₀) (BP' : ∀ x y → Biproduct CM' x y)
  {𝟙d : Category.obj 𝒟₀} (Lft' : Lifting CM' 𝟙d)
  (let 𝒟₀P = biproducts→products CM' BP')
  (F₀ : Functor 𝒞₀ 𝒟₀)
  (F₀T : preserve-chosen-terminal F₀ 𝒞₀T 𝒟₀T)
  (F₀P : preserve-chosen-products F₀ 𝒞₀P 𝒟₀P)
  (let module Fam𝒟 = fam.CategoryOfFamilies 0ℓ 0ℓ 𝒟₀)
  (let module Fam𝒟P = Fam𝒟.products 𝒟₀P)
  (𝒟E : HasWeakExponentials Fam𝒟.cat Fam𝒟P.products)
  (F₀-faithful : ∀ {a b} {g₁ g₂ : Category._⇒_ 𝒞₀ a b} →
                 Category._≈_ 𝒟₀ (F₀ .Functor.fmor g₁) (F₀ .Functor.fmor g₂) →
                 Category._≈_ 𝒞₀ g₁ g₂)
  (F₀def : ∀ {a b} (k : Category._⇒_ 𝒟₀ (F₀ .Functor.fobj a) (F₀ .Functor.fobj b)) →
           Prf (∃ (Category._⇒_ 𝒞₀ a b) λ g → Category._≈_ 𝒟₀ (F₀ .Functor.fmor g) k) →
           ∃ₛ (Category._⇒_ 𝒞₀ a b) λ g → Category._≈_ 𝒟₀ (F₀ .Functor.fmor g) k)
  where

open Functor

-- The family-level logical relations, reused wholesale.
module CF = conservativity-fam 𝒞₀T 𝒞₀P 𝒟₀T 𝒟₀P F₀ F₀T F₀P 𝒟E F₀-faithful F₀def

open CF.Rel using (G; PSh⟨𝒞⟩; PSh⟨𝒞⟩-products; PSh⟨𝒞⟩-system; closureOp; system;
                   &&-++-distrib; &&-⋁-distrib; &&-⟨⟩-frobenius; ⟨⟩-[]-BC)

-- The rooted structure on the same category of families.
module RML = fam-mu-lifting.laws 0ℓ 0ℓ 𝒟₀T CM' BP' Lft'

open PredicateSystem PSh⟨𝒞⟩-system
open ClosureOp closureOp using (𝐂; 𝐂-isClosure; 𝐂-[]; 𝐂-[]⁻¹; 𝐂-strong)

module CS = PredicateSystem system

crefl : ∀ {X} (P : CS.Predicate X) → CS._⊑_ P P
crefl P = ⊑-isPreorder .IsPreorder.refl

idCl : ClosureOp PSh⟨𝒞⟩ PSh⟨𝒞⟩-products system
idCl .ClosureOp.𝐂 P = P
idCl .ClosureOp.𝐂-isClosure .IsClosureOp.mono ϕ = ϕ
idCl .ClosureOp.𝐂-isClosure .IsClosureOp.unit {P} = crefl P
idCl .ClosureOp.𝐂-isClosure .IsClosureOp.closed {P} = crefl P
idCl .ClosureOp.𝐂-[] {P = P} {f = f} = crefl (CS._[_] P f)
idCl .ClosureOp.𝐂-[]⁻¹ {P = P} {f = f} = crefl (CS._[_] P f)
idCl .ClosureOp.𝐂-strong {P = P} {Q = Q} = crefl (CS._&&_ P Q)

open NatTrans
open CF.Rel.PShPredicate
open CF.Rel._⊑_
open setoid-predicate.Predicate
open setoid-predicate._⊑_

private
  module FD = Category RML.cat
  module FDP = RML.Fam𝒞-P
  module PSh⟨𝒞⟩C = Category PSh⟨𝒞⟩
  module FamC = fam.CategoryOfFamilies 0ℓ 0ℓ 𝒞₀
  module FC = fam-fibre-cover 0ℓ 0ℓ 𝒞₀
  module CvM = CF.Rel.CvM
  module RCP = HasCoproducts RML.coproducts

  strip : ∀ {A B : RML.obj} (t : A RML.⇒ B) →
          RML._≈_ (RML._∘_ (RML.id _)
                     (RML._∘_ (RML.id _) (RML._∘_ (RML.id _) (RML._∘_ t (RML.id _))))) t
  strip t =
    RML.≈-trans RML.id-left
      (RML.≈-trans RML.id-left (RML.≈-trans RML.id-left RML.id-right))

  strip-f : ∀ {A B B' : RML.obj} (f : RML._⇒_ B B') (t : RML._⇒_ A B) →
            RML._≈_ (RML._∘_ (RML.id _)
                       (RML._∘_ f (RML._∘_ (RML.id _) (RML._∘_ t (RML.id _)))))
                    (RML._∘_ f t)
  strip-f f t =
    RML.≈-trans RML.id-left
      (RML.∘-cong RML.≈-refl (RML.≈-trans RML.id-left RML.id-right))

raw-in₁-extract : ∀ {X Y : RML.Obj} {Q : Predicate (G .fobj X)} →
              ((Q ⟨ G .fmor (RCP.in₁ {X} {Y}) ⟩) [ G .fmor (RCP.in₁ {X} {Y}) ]) ⊑ Q
raw-in₁-extract {X} {Y} {Q} .*⊑* a .*⊑* (lift u) (lift u' , qu' , lift eq) =
  Q .pred a .pred-≃ (lift mono) qu'
  where
  mono : FD._≈_ u' u
  mono .RML._≃_.idxf-eq .PS._≃m_.func-eq p = eq .RML._≃_.idxf-eq .PS._≃m_.func-eq p
  mono .RML._≃_.famf-eq ._≃f_.transf-eq {i} =
    RML.≈-trans (RML.∘-cong RML.≈-refl (RML.≈-sym (strip (u' .RML.famf ._⇒f_.transf i))))
                (RML.≈-trans (eq .RML._≃_.famf-eq ._≃f_.transf-eq)
                             (strip (u .RML.famf ._⇒f_.transf i)))

raw-in₂-extract : ∀ {X Y : RML.Obj} {Q : Predicate (G .fobj Y)} →
              ((Q ⟨ G .fmor (RCP.in₂ {X} {Y}) ⟩) [ G .fmor (RCP.in₂ {X} {Y}) ]) ⊑ Q
raw-in₂-extract {X} {Y} {Q} .*⊑* a .*⊑* (lift u) (lift u' , qu' , lift eq) =
  Q .pred a .pred-≃ (lift mono) qu'
  where
  mono : FD._≈_ u' u
  mono .RML._≃_.idxf-eq .PS._≃m_.func-eq p = eq .RML._≃_.idxf-eq .PS._≃m_.func-eq p
  mono .RML._≃_.famf-eq ._≃f_.transf-eq {i} =
    RML.≈-trans (RML.∘-cong RML.≈-refl (RML.≈-sym (strip (u' .RML.famf ._⇒f_.transf i))))
                (RML.≈-trans (eq .RML._≃_.famf-eq ._≃f_.transf-eq)
                             (strip (u .RML.famf ._⇒f_.transf i)))

-- The singleton family at the lifting's unit.
𝟙L : RML.Obj
𝟙L = RML.simple[ PS.𝟙 {0ℓ} {0ℓ} , 𝟙d ]

-- The bare root of a lifted family at an index.
root-mor : ∀ (C : RML.Obj) (i : Setoid.Carrier (RML.idx C)) → RML.Mor 𝟙L (RML.Lf C)
root-mor C i .RML.idxf .PS._⇒_.func _ = i
root-mor C i .RML.idxf .PS._⇒_.func-resp-≈ _ = Setoid.refl (RML.idx C)
root-mor C i .RML.famf ._⇒f_.transf _ = RML.root
root-mor C i .RML.famf ._⇒f_.natural _ =
  RML.≈-trans RML.id-right (RML.≈-sym (RML.Lmap-root _))

-- Definable root selections: up to cover refinement, the maps into a lifted
-- family that factor through a bare root.
RtJoin : ∀ (C : RML.Obj) → Predicate (G .fobj (RML.Lf C))
RtJoin C = ⋁ (Setoid.Carrier (RML.idx C)) (λ i → TT ⟨ G .fmor (root-mor C i) ⟩)

RtRaw : ∀ (C : RML.Obj) → Predicate (G .fobj (RML.Lf C))
RtRaw C = 𝐂 (RtJoin C)

Rt : ∀ (C : RML.Obj) → CS.Predicate (G .fobj (RML.Lf C))
Rt C = CS.⋁ (Setoid.Carrier (RML.idx C))
            (λ i → CS._⟨_⟩ CS.TT (G .fmor (root-mor C i)))

-- The glued rooted μ interface at the family-level nerve.
module RootedMu =
  fam-mu-lifting.glued-interface 𝒟₀T CM' BP' Lft'
    PSh⟨𝒞⟩ PSh⟨𝒞⟩-products system G Rt idCl

raw-sing-split : ∀ {X : RML.Obj} {Q : Predicate (G .fobj X)} →
             Q ⊑ 𝐂 (⋁ (Setoid.Carrier (RML.idx X))
                      (λ x → (Q [ G .fmor (RootedMu.elem-in X x) ])
                               ⟨ G .fmor (RootedMu.elem-in X x) ⟩))
raw-sing-split {X} {Q} .*⊑* a .*⊑* (lift m) qm = CvM.node cov xs ts eqs
  where
  cvr : CF.Rel.IdxCover a
  cvr .CF.Rel.IdxCover.S = FamC.Obj.idx a
  cvr .CF.Rel.IdxCover.D = FC.fibres a
  cvr .CF.Rel.IdxCover.iso = FC.fib-iso a

  cov : CF.Rel.Cover a
  cov = CF.Rel.idx cvr

  xs : ∀ s → Setoid.Carrier (G .fobj X .fobj (CF.Rel.cDom cov s))
  xs s = G .fobj X .fmor (CF.Rel.cInj cov s) .PS._⇒_.func (lift m)

  eqs : ∀ s → Setoid._≈_ (G .fobj X .fobj (CF.Rel.cDom cov s)) (xs s)
                 (G .fobj X .fmor (CF.Rel.cInj cov s) .PS._⇒_.func (lift m))
  eqs s = Setoid.refl (G .fobj X .fobj (CF.Rel.cDom cov s))

  ts : ∀ s → CvM.Context (G .fobj X)
               (⋁ (Setoid.Carrier (RML.idx X))
                  (λ x → (Q [ G .fmor (RootedMu.elem-in X x) ])
                           ⟨ G .fmor (RootedMu.elem-in X x) ⟩))
               (CF.Rel.cDom cov s) (xs s)
  ts (lift v) = CvM.leaf (xv , (lift wv , (qw , ew)))
    where
    mj : RML.Mor (CF.FamF .fobj (CF.Rel.cDom cov (lift v))) X
    mj = FD._∘_ m (CF.FamF .fmor (CF.Rel.cInj cov (lift v)))

    xv : Setoid.Carrier (RML.idx X)
    xv = mj .RML.idxf .PS._⇒_.func (lift ttS)

    wv : RML.Mor (CF.FamF .fobj (CF.Rel.cDom cov (lift v)))
                 RML.simple[ PS.𝟙 , X .RML.fam .RML.fm xv ]
    wv .RML.idxf = PS.idS PS.𝟙
    wv .RML.famf ._⇒f_.transf i = mj .RML.famf ._⇒f_.transf i
    wv .RML.famf ._⇒f_.natural e =
      RML.≈-trans (mj .RML.famf ._⇒f_.natural e)
                  (RML.∘-cong (X .RML.fam .RML.refl*) RML.≈-refl)

    sq : FD._≈_ (FD._∘_ (RootedMu.elem-in X xv) (FD._∘_ wv (FD.id _))) mj
    sq .RML._≃_.idxf-eq .PS._≃m_.func-eq _ = Setoid.refl (RML.idx X)
    sq .RML._≃_.famf-eq ._≃f_.transf-eq =
      RML.≈-trans (RML.∘-cong (X .RML.fam .RML.refl*)
                    (RML.≈-trans RML.id-left
                      (RML.≈-trans RML.id-left (RML.≈-trans RML.id-left RML.id-right))))
                  RML.id-left

    ew : Setoid._≈_ (G .fobj X .fobj (CF.Rel.cDom cov (lift v)))
           (G .fmor (RootedMu.elem-in X xv) .transf (CF.Rel.cDom cov (lift v))
              .PS._⇒_.func (lift wv))
           (xs (lift v))
    ew = lift sq

    qw : (Q [ G .fmor (RootedMu.elem-in X xv) ]) .pred (CF.Rel.cDom cov (lift v))
           .pred (lift wv)
    qw = Q .pred (CF.Rel.cDom cov (lift v)) .pred-≃
           (Setoid.sym (G .fobj X .fobj (CF.Rel.cDom cov (lift v))) ew)
           (Q .pred-mor (CF.Rel.cInj cov (lift v)) .*⊑* (lift m) qm)

private
  root-square : ∀ {C D : RML.Obj} (h : RML.Mor C D) (i : Setoid.Carrier (RML.idx C)) →
                FD._≈_ (root-mor D (h .RML.idxf .PS._⇒_.func i))
                       (FD._∘_ (RML.Lf-map h) (root-mor C i))
  root-square {C} {D} h i .RML._≃_.idxf-eq .PS._≃m_.func-eq _ = Setoid.refl (RML.idx D)
  root-square {C} {D} h i .RML._≃_.famf-eq ._≃f_.transf-eq =
    RML.≈-trans (RML.Lmap-root _)
                (RML.≈-sym (RML.≈-trans RML.id-left (RML.Lmap-root _)))

raw-Rt-iso : ∀ {C D : RML.Obj} (h : RML.Mor C D)
         (hinv : ∀ x → RML._⇒_ (D .RML.fam .RML.fm (h .RML.idxf .PS._⇒_.func x))
                                (C .RML.fam .RML.fm x)) →
         (∀ x → RML._≈_ (RML._∘_ (h .RML.famf ._⇒f_.transf x) (hinv x)) (RML.id _)) →
         (∀ x → RML._≈_ (RML._∘_ (hinv x) (h .RML.famf ._⇒f_.transf x)) (RML.id _)) →
         RtRaw C ⊑ (RtRaw D [ G .fmor (RML.Lf-map h) ])
raw-Rt-iso {C} {D} h hinv e₁ e₂ =
  ⊑-trans (IsClosureOp.mono 𝐂-isClosure (IsBigJoin.least ⋁-isJoin _ _ _ step)) 𝐂-[]
  where
  step : ∀ i → (TT ⟨ G .fmor (root-mor C i) ⟩) ⊑ (RtJoin D [ G .fmor (RML.Lf-map h) ])
  step i =
    adjoint₂
      (⊑-trans (adjoint₁ (IsBigJoin.upper ⋁-isJoin _ _ (h .RML.idxf .PS._⇒_.func i)))
      (⊑-trans ([]-cong (G .fmor-cong (root-square h i)))
      (⊑-trans ([]-cong (G .fmor-comp _ _)) ([]-comp⁻¹ _ _))))

raw-Rt-iso⁻ : ∀ {C D : RML.Obj} (h : RML.Mor C D)
          (hinv : ∀ x → RML._⇒_ (D .RML.fam .RML.fm (h .RML.idxf .PS._⇒_.func x))
                                 (C .RML.fam .RML.fm x)) →
          (∀ x → RML._≈_ (RML._∘_ (h .RML.famf ._⇒f_.transf x) (hinv x)) (RML.id _)) →
          (∀ x → RML._≈_ (RML._∘_ (hinv x) (h .RML.famf ._⇒f_.transf x)) (RML.id _)) →
          (RtRaw D [ G .fmor (RML.Lf-map h) ]) ⊑ RtRaw C
raw-Rt-iso⁻ {C} {D} h hinv e₁ e₂ =
  ⊑-trans 𝐂-[]⁻¹
          (⊑-trans (IsClosureOp.mono 𝐂-isClosure ψ) (IsClosureOp.closed 𝐂-isClosure))
  where
  src : Predicate (G .fobj (RML.Lf C))
  src = RtJoin D [ G .fmor (RML.Lf-map h) ]

  ψ : src ⊑ 𝐂 (RtJoin C)
  ψ .*⊑* a .*⊑* (lift w) hyp = CvM.node cov xs ts eqs
    where
    cvr : CF.Rel.IdxCover a
    cvr .CF.Rel.IdxCover.S = FamC.Obj.idx a
    cvr .CF.Rel.IdxCover.D = FC.fibres a
    cvr .CF.Rel.IdxCover.iso = FC.fib-iso a

    cov : CF.Rel.Cover a
    cov = CF.Rel.idx cvr

    xs : ∀ s → Setoid.Carrier (G .fobj (RML.Lf C) .fobj (CF.Rel.cDom cov s))
    xs s = G .fobj (RML.Lf C) .fmor (CF.Rel.cInj cov s) .PS._⇒_.func (lift w)

    eqs : ∀ s → Setoid._≈_ (G .fobj (RML.Lf C) .fobj (CF.Rel.cDom cov s)) (xs s)
                  (G .fobj (RML.Lf C) .fmor (CF.Rel.cInj cov s) .PS._⇒_.func (lift w))
    eqs s = Setoid.refl (G .fobj (RML.Lf C) .fobj (CF.Rel.cDom cov s))

    ts : ∀ s → CvM.Context (G .fobj (RML.Lf C)) (RtJoin C) (CF.Rel.cDom cov s) (xs s)
    ts (lift v) = CvM.leaf (go (src .pred-mor (CF.Rel.cInj cov (lift v)) .*⊑* (lift w) hyp))
      where
      wv : RML.Mor (CF.FamF .fobj (CF.Rel.cDom cov (lift v))) (RML.Lf C)
      wv = FD._∘_ w (CF.FamF .fmor (CF.Rel.cInj cov (lift v)))

      iv : Setoid.Carrier (RML.idx C)
      iv = wv .RML.idxf .PS._⇒_.func (lift ttS)

      go : src .pred (CF.Rel.cDom cov (lift v)) .pred (xs (lift v)) →
           RtJoin C .pred (CF.Rel.cDom cov (lift v)) .pred (xs (lift v))
      go (j , (lift t , _ , lift eqj)) = iv , (lift t , (tt , lift sq))
        where
        sq : FD._≈_ (FD._∘_ (root-mor C iv) (FD._∘_ t (FD.id _))) wv
        sq .RML._≃_.idxf-eq .PS._≃m_.func-eq _ = Setoid.refl (RML.idx C)
        sq .RML._≃_.famf-eq ._≃f_.transf-eq {x} = RML.≈-trans lhs main
          where
          T = t .RML.famf ._⇒f_.transf x
          W = wv .RML.famf ._⇒f_.transf x
          HS = h .RML.famf ._⇒f_.transf iv

          reduce : ∀ {B₁ B₂} (s : RML._⇒_ B₁ B₂) →
                   RML._≈_ (RML._∘_ (RML.Lmap s)
                              (RML._∘_ (RML.id _)
                                 (RML._∘_ (RML.root {B₁})
                                    (RML._∘_ (RML.id _) (RML._∘_ T (RML.id _))))))
                           (RML._∘_ (RML.root {B₂}) T)
          reduce s =
            RML.≈-trans
              (RML.∘-cong RML.≈-refl
                (RML.≈-trans RML.id-left
                  (RML.∘-cong RML.≈-refl (RML.≈-trans RML.id-left RML.id-right))))
              (RML.≈-trans (RML.≈-sym (RML.assoc _ _ _))
                           (RML.∘-cong (RML.Lmap-root s) RML.≈-refl))

          lhs : RML._≈_ (RML._∘_ (RML.Lmap (C .RML.fam .RML.subst _))
                           (RML._∘_ (RML.id _)
                              (RML._∘_ RML.root
                                 (RML._∘_ (RML.id _) (RML._∘_ T (RML.id _))))))
                        (RML._∘_ RML.root T)
          lhs = reduce _

          rhs : RML._≈_ (RML._∘_ (RML.id _)
                           (RML._∘_ (RML.Lmap HS)
                              (RML._∘_ (RML.id _) (RML._∘_ W (RML.id _)))))
                        (RML._∘_ (RML.Lmap HS) W)
          rhs = RML.≈-trans RML.id-left
                  (RML.∘-cong RML.≈-refl (RML.≈-trans RML.id-left RML.id-right))

          EQ : RML._≈_ (RML._∘_ RML.root T) (RML._∘_ (RML.Lmap HS) W)
          EQ = RML.≈-trans (RML.≈-sym (reduce (D .RML.fam .RML.subst _)))
                 (RML.≈-trans (eqj .RML._≃_.famf-eq ._≃f_.transf-eq) rhs)

          main : RML._≈_ (RML._∘_ RML.root T) W
          main = begin
              RML._∘_ RML.root T
            ≈˘⟨ RML.∘-cong (RML.Lmap-root (hinv iv)) RML.≈-refl ⟩
              RML._∘_ (RML._∘_ (RML.Lmap (hinv iv)) RML.root) T
            ≈⟨ RML.assoc _ _ _ ⟩
              RML._∘_ (RML.Lmap (hinv iv)) (RML._∘_ RML.root T)
            ≈⟨ RML.∘-cong RML.≈-refl EQ ⟩
              RML._∘_ (RML.Lmap (hinv iv)) (RML._∘_ (RML.Lmap HS) W)
            ≈˘⟨ RML.assoc _ _ _ ⟩
              RML._∘_ (RML._∘_ (RML.Lmap (hinv iv)) (RML.Lmap HS)) W
            ≈˘⟨ RML.∘-cong (RML.Lmap-comp _ _) RML.≈-refl ⟩
              RML._∘_ (RML.Lmap (RML._∘_ (hinv iv) HS)) W
            ≈⟨ RML.∘-cong (RML.Lmap-cong (e₂ iv)) RML.≈-refl ⟩
              RML._∘_ (RML.Lmap (RML.id _)) W
            ≈⟨ RML.∘-cong RML.Lmap-id RML.≈-refl ⟩
              RML._∘_ (RML.id _) W
            ≈⟨ RML.id-left ⟩
              W
            ∎
            where open ≈-Reasoning RML.isEquiv

raw-disjoint₁ : ∀ {X Y : RML.Obj} {Q : Predicate (G .fobj Y)}
                (x : Setoid.Carrier (RML.idx X))
                {T : Predicate (G .fobj RML.simple[ PS.𝟙 , X .RML.fam .RML.fm x ])} →
                ((Q ⟨ G .fmor (RCP.in₂ {X} {Y}) ⟩)
                   [ G .fmor (RootedMu.elem-in (RCP.coprod X Y) (inj₁ x)) ])
                  ⊑ 𝐂 T
raw-disjoint₁ {X} {Y} {Q} x {T} .*⊑* a .*⊑* (lift w) hyp = CvM.node cov xs ts eqs
  where
  SIMP = G .fobj RML.simple[ PS.𝟙 , X .RML.fam .RML.fm x ]

  src : Predicate SIMP
  src = (Q ⟨ G .fmor (RCP.in₂ {X} {Y}) ⟩)
          [ G .fmor (RootedMu.elem-in (RCP.coprod X Y) (inj₁ x)) ]

  cvr : CF.Rel.IdxCover a
  cvr .CF.Rel.IdxCover.S = FamC.Obj.idx a
  cvr .CF.Rel.IdxCover.D = FC.fibres a
  cvr .CF.Rel.IdxCover.iso = FC.fib-iso a

  cov : CF.Rel.Cover a
  cov = CF.Rel.idx cvr

  xs : ∀ s → Setoid.Carrier (SIMP .fobj (CF.Rel.cDom cov s))
  xs s = SIMP .fmor (CF.Rel.cInj cov s) .PS._⇒_.func (lift w)

  eqs : ∀ s → Setoid._≈_ (SIMP .fobj (CF.Rel.cDom cov s)) (xs s)
                (SIMP .fmor (CF.Rel.cInj cov s) .PS._⇒_.func (lift w))
  eqs s = Setoid.refl (SIMP .fobj (CF.Rel.cDom cov s))

  ts : ∀ s → CvM.Context SIMP T (CF.Rel.cDom cov s) (xs s)
  ts (lift v) = CvM.leaf (go (src .pred-mor (CF.Rel.cInj cov (lift v)) .*⊑* (lift w) hyp))
    where
    go : src .pred (CF.Rel.cDom cov (lift v)) .pred (xs (lift v)) →
         T .pred (CF.Rel.cDom cov (lift v)) .pred (xs (lift v))
    go (lift u , qu , lift eqv) =
      ⊥-elim (eqv .RML._≃_.idxf-eq .PS._≃m_.func-eq {lift ttS} {lift ttS} tt)

raw-disjoint₂ : ∀ {X Y : RML.Obj} {Q : Predicate (G .fobj X)}
                (y : Setoid.Carrier (RML.idx Y))
                {T : Predicate (G .fobj RML.simple[ PS.𝟙 , Y .RML.fam .RML.fm y ])} →
                ((Q ⟨ G .fmor (RCP.in₁ {X} {Y}) ⟩)
                   [ G .fmor (RootedMu.elem-in (RCP.coprod X Y) (inj₂ y)) ])
                  ⊑ 𝐂 T
raw-disjoint₂ {X} {Y} {Q} y {T} .*⊑* a .*⊑* (lift w) hyp = CvM.node cov xs ts eqs
  where
  SIMP = G .fobj RML.simple[ PS.𝟙 , Y .RML.fam .RML.fm y ]

  src : Predicate SIMP
  src = (Q ⟨ G .fmor (RCP.in₁ {X} {Y}) ⟩)
          [ G .fmor (RootedMu.elem-in (RCP.coprod X Y) (inj₂ y)) ]

  cvr : CF.Rel.IdxCover a
  cvr .CF.Rel.IdxCover.S = FamC.Obj.idx a
  cvr .CF.Rel.IdxCover.D = FC.fibres a
  cvr .CF.Rel.IdxCover.iso = FC.fib-iso a

  cov : CF.Rel.Cover a
  cov = CF.Rel.idx cvr

  xs : ∀ s → Setoid.Carrier (SIMP .fobj (CF.Rel.cDom cov s))
  xs s = SIMP .fmor (CF.Rel.cInj cov s) .PS._⇒_.func (lift w)

  eqs : ∀ s → Setoid._≈_ (SIMP .fobj (CF.Rel.cDom cov s)) (xs s)
                (SIMP .fmor (CF.Rel.cInj cov s) .PS._⇒_.func (lift w))
  eqs s = Setoid.refl (SIMP .fobj (CF.Rel.cDom cov s))

  ts : ∀ s → CvM.Context SIMP T (CF.Rel.cDom cov s) (xs s)
  ts (lift v) = CvM.leaf (go (src .pred-mor (CF.Rel.cInj cov (lift v)) .*⊑* (lift w) hyp))
    where
    go : src .pred (CF.Rel.cDom cov (lift v)) .pred (xs (lift v)) →
         T .pred (CF.Rel.cDom cov (lift v)) .pred (xs (lift v))
    go (lift u , qu , lift eqv) =
      ⊥-elim (eqv .RML._≃_.idxf-eq .PS._≃m_.func-eq {lift ttS} {lift ttS} tt)

-- Beck-Chevalley for the assembly at a singleton: an assembled element that factors through the
-- singleton at an index is the assembly of something over that singleton, the payload transported
-- along the index equation the factorisation forces.
raw-BC-assemble : ∀ {C : RML.Obj} {Qp : Predicate (G .fobj (FDP.prod C RML.𝟙L))}
                  (x : Setoid.Carrier (RML.idx C)) →
                  ((Qp ⟨ G .fmor (RML.assembleF {C}) ⟩)
                     [ G .fmor (RootedMu.elem-in (RML.Lf C) x) ])
                    ⊑ ((Qp [ G .fmor (RootedMu.elem-in (FDP.prod C RML.𝟙L) (x , lift ttS)) ])
                         ⟨ G .fmor (RootedMu.sing-assemble C x) ⟩)
raw-BC-assemble {C} {Qp} x = ⟨⟩-[]-BC lft
  where
  SING = RML.simple[ PS.𝟙 , RML.prod (C .RML.fam .RML.fm x) 𝟙d ]

  lft : ∀ a (y* : Setoid.Carrier
                    (G .fobj RML.simple[ PS.𝟙 , RML.L (C .RML.fam .RML.fm x) ] .fobj a))
          (u* : Setoid.Carrier (G .fobj (FDP.prod C RML.𝟙L) .fobj a)) →
        Setoid._≈_ (G .fobj (RML.Lf C) .fobj a)
          (PS._⇒_.func (G .fmor (RML.assembleF {C}) .transf a) u*)
          (PS._⇒_.func (G .fmor (RootedMu.elem-in (RML.Lf C) x) .transf a) y*) →
        ∃ (Setoid.Carrier (G .fobj SING .fobj a)) λ w* →
          (Setoid._≈_ (G .fobj (FDP.prod C RML.𝟙L) .fobj a)
            (PS._⇒_.func
              (G .fmor (RootedMu.elem-in (FDP.prod C RML.𝟙L) (x , lift ttS)) .transf a) w*)
            u*)
          ∧ (Setoid._≈_ (G .fobj RML.simple[ PS.𝟙 , RML.L (C .RML.fam .RML.fm x) ] .fobj a)
              (PS._⇒_.func (G .fmor (RootedMu.sing-assemble C x) .transf a) w*) y*)
  lft a (lift y) (lift u) (lift hyp) = lift w , (lift eq₁ , lift eq₂)
    where
    ex : ∀ i → Setoid._≈_ (RML.idx C) (proj₁ (u .RML.idxf .PS._⇒_.func i)) x
    ex i = hyp .RML._≃_.idxf-eq .PS._≃m_.func-eq (Setoid.refl (FamC.Obj.idx a) {i})

    w : RML.Mor (CF.FamF .fobj a) SING
    w .RML.idxf = PS.to-𝟙
    w .RML.famf ._⇒f_.transf i =
      RML._∘_ (RML.prod-m (C .RML.fam .RML.subst (ex i)) (RML.id 𝟙d))
              (u .RML.famf ._⇒f_.transf i)
    w .RML.famf ._⇒f_.natural p =
      RML.≈-trans (RML.assoc _ _ _)
        (RML.≈-trans (RML.∘-cong RML.≈-refl (u .RML.famf ._⇒f_.natural p))
          (RML.≈-trans (RML.≈-sym (RML.assoc _ _ _))
            (RML.≈-trans
              (RML.∘-cong
                (RML.≈-trans (RML.≈-sym (RML.prod-m-comp _ _ _ _))
                             (RML.prod-m-cong (RML.≈-sym (C .RML.fam .RML.trans* _ _))
                                              RML.id-left))
                RML.≈-refl)
              (RML.≈-sym RML.id-left))))

    eq₁ : FD._≈_ (FD._∘_ (RootedMu.elem-in (FDP.prod C RML.𝟙L) (x , lift ttS))
                         (FD._∘_ w (FD.id _))) u
    eq₁ .RML._≃_.idxf-eq .PS._≃m_.func-eq {i₁} {i₂} p =
      Setoid.sym (RML.idx C) (ex i₂) , tt
    eq₁ .RML._≃_.famf-eq ._≃f_.transf-eq {i} =
      RML.≈-trans (RML.∘-cong RML.≈-refl (strip (w .RML.famf ._⇒f_.transf i)))
        (RML.≈-trans (RML.≈-sym (RML.assoc _ _ _))
          (RML.≈-trans
            (RML.∘-cong
              (RML.≈-trans (RML.≈-sym (RML.prod-m-comp _ _ _ _))
                (RML.≈-trans (RML.prod-m-cong (RML.fam-subst-iso₂ (C .RML.fam) (ex i))
                                              RML.id-left)
                             RML.prod-m-id))
              RML.≈-refl)
            RML.id-left))

    HY : ∀ i → RML._≈_ (RML._∘_ (RML.Lmap (C .RML.fam .RML.subst (ex i)))
                          (RML._∘_ (RML.cop RML.inj RML.root) (u .RML.famf ._⇒f_.transf i)))
                       (y .RML.famf ._⇒f_.transf i)
    HY i =
      RML.≈-trans
        (RML.≈-sym (RML.∘-cong RML.≈-refl
                     (strip-f (RML.cop RML.inj RML.root) (u .RML.famf ._⇒f_.transf i))))
        (RML.≈-trans (hyp .RML._≃_.famf-eq ._≃f_.transf-eq {i})
                     (strip (y .RML.famf ._⇒f_.transf i)))

    eq₂ : FD._≈_ (FD._∘_ (RootedMu.sing-assemble C x) (FD._∘_ w (FD.id _))) y
    eq₂ .RML._≃_.idxf-eq .PS._≃m_.func-eq _ = tt
    eq₂ .RML._≃_.famf-eq ._≃f_.transf-eq {i} =
      RML.≈-trans RML.id-left
        (RML.≈-trans (strip-f (RML.cop RML.inj RML.root) (w .RML.famf ._⇒f_.transf i))
          (RML.≈-trans (RML.≈-sym (RML.assoc _ _ _))
            (RML.≈-trans
              (RML.∘-cong
                (RML.≈-sym (RML.Lmap-assemble (RML.fam-subst-iso₁ (C .RML.fam) (ex i))
                                              (RML.fam-subst-iso₂ (C .RML.fam) (ex i))))
                RML.≈-refl)
              (RML.≈-trans (RML.assoc _ _ _) (HY i)))))

raw-BC : ∀ {W U V : RML.Obj} (h : RML.Mor U V) {Q : Predicate (G .fobj U)} →
     ((Q ⟨ G .fmor h ⟩) [ G .fmor (FDP.p₂ {W} {V}) ])
       ⊑ ((Q [ G .fmor (FDP.p₂ {W} {U}) ])
            ⟨ G .fmor (FDP.pair FDP.p₁ (FD._∘_ h FDP.p₂)) ⟩)
raw-BC {W} {U} {V} h {Q} = ⟨⟩-[]-BC lft
  where
  lft : ∀ a (v* : Setoid.Carrier ((G .fobj (FDP.prod W V)) .fobj a))
          (u* : Setoid.Carrier ((G .fobj U) .fobj a)) →
        Setoid._≈_ ((G .fobj V) .fobj a)
          (PS._⇒_.func (G .fmor h .transf a) u*)
          (PS._⇒_.func (G .fmor (FDP.p₂ {W}) .transf a) v*) →
        ∃ (Setoid.Carrier ((G .fobj (FDP.prod W U)) .fobj a)) λ w* →
          (Setoid._≈_ ((G .fobj U) .fobj a)
            (PS._⇒_.func (G .fmor (FDP.p₂ {W} {U}) .transf a) w*) u*)
          ∧ (Setoid._≈_ ((G .fobj (FDP.prod W V)) .fobj a)
              (PS._⇒_.func (G .fmor (FDP.pair FDP.p₁ (FD._∘_ h FDP.p₂)) .transf a) w*) v*)
  lft a (lift v) (lift u) (lift e) = lift w , (lift eq₁ , lift eq₂)
    where
    w = FDP.pair (FD._∘_ FDP.p₁ v) u

    eq₁ : FD._≈_ (FD._∘_ FDP.p₂ (FD._∘_ w (FD.id _))) u
    eq₁ = FD.≈-trans (FD.∘-cong FD.≈-refl FD.id-right) (FDP.pair-p₂ _ _)

    side : FD._≈_ (FD._∘_ (FD._∘_ h FDP.p₂) w) (FD._∘_ FDP.p₂ v)
    side = begin
        FD._∘_ (FD._∘_ h FDP.p₂) w
      ≈⟨ FD.assoc _ _ _ ⟩
        FD._∘_ h (FD._∘_ FDP.p₂ w)
      ≈⟨ FD.∘-cong FD.≈-refl (FDP.pair-p₂ _ _) ⟩
        FD._∘_ h u
      ≈˘⟨ FD.∘-cong FD.≈-refl FD.id-right ⟩
        FD._∘_ h (FD._∘_ u (FD.id _))
      ≈⟨ e ⟩
        FD._∘_ FDP.p₂ (FD._∘_ v (FD.id _))
      ≈⟨ FD.∘-cong FD.≈-refl FD.id-right ⟩
        FD._∘_ FDP.p₂ v
      ∎
      where open ≈-Reasoning FD.isEquiv

    eq₂ : FD._≈_ (FD._∘_ (FDP.pair FDP.p₁ (FD._∘_ h FDP.p₂)) (FD._∘_ w (FD.id _))) v
    eq₂ = begin
        FD._∘_ (FDP.pair FDP.p₁ (FD._∘_ h FDP.p₂)) (FD._∘_ w (FD.id _))
      ≈⟨ FD.∘-cong FD.≈-refl FD.id-right ⟩
        FD._∘_ (FDP.pair FDP.p₁ (FD._∘_ h FDP.p₂)) w
      ≈⟨ FDP.pair-natural _ _ _ ⟩
        FDP.pair (FD._∘_ FDP.p₁ w) (FD._∘_ (FD._∘_ h FDP.p₂) w)
      ≈⟨ FDP.pair-cong (FDP.pair-p₁ _ _) side ⟩
        FDP.pair (FD._∘_ FDP.p₁ v) (FD._∘_ FDP.p₂ v)
      ≈⟨ FDP.pair-ext v ⟩
        v
      ∎
      where open ≈-Reasoning FD.isEquiv

private
  module CPm = closure-predicate PSh⟨𝒞⟩-system closureOp
  module CPd = CPm.distributive &&-++-distrib &&-⟨⟩-frobenius

  RtDown : ∀ (C : RML.Obj) → CPm.Predicate.pred (Rt C) ⊑ RtRaw C
  RtDown C =
    ⊑-trans (𝐂-isClosure .IsClosureOp.mono
              (IsBigJoin.least ⋁-isJoin _ _ _
                (λ i → 𝐂-isClosure .IsClosureOp.mono (IsBigJoin.upper ⋁-isJoin _ _ i))))
            (𝐂-isClosure .IsClosureOp.closed)

  RtUp : ∀ (C : RML.Obj) → RtRaw C ⊑ CPm.Predicate.pred (Rt C)
  RtUp C =
    𝐂-isClosure .IsClosureOp.mono
      (IsBigJoin.least ⋁-isJoin _ _ _
        (λ i → ⊑-trans (𝐂-isClosure .IsClosureOp.unit) (IsBigJoin.upper ⋁-isJoin _ _ i)))

dist : ∀ {V} {Pp Q S : CS.Predicate V} →
       CS._⊑_ (CS._&&_ Pp (CS._++_ Q S)) (CS._++_ (CS._&&_ Pp Q) (CS._&&_ Pp S))
dist {V} {Pp} {Q} {S} = CPd.&&-++-distrib {V} {Pp} {Q} {S}

dist-⋁ : ∀ {V} {I : Set 0ℓ} {Pp : CS.Predicate V} {Qs : I → CS.Predicate V} →
         CS._⊑_ (CS._&&_ Pp (CS.⋁ I Qs)) (CS.⋁ I (λ i → CS._&&_ Pp (Qs i)))
dist-⋁ =
  ⊑-trans (IsMeet.comm &&-isMeet)
  (⊑-trans 𝐂-strong
  (⊑-trans (𝐂-isClosure .IsClosureOp.mono (IsMeet.comm &&-isMeet))
           (𝐂-isClosure .IsClosureOp.mono &&-⋁-distrib)))

frob : ∀ {V V'} {Pp : CS.Predicate V'} {Q : CS.Predicate V} {α : V PSh⟨𝒞⟩C.⇒ V'} →
       CS._⊑_ (CS._&&_ Pp (CS._⟨_⟩ Q α)) (CS._⟨_⟩ (CS._&&_ (CS._[_] Pp α) Q) α)
frob {V} {V'} {Pp} {Q} {α} = CPd.&&-⟨⟩-frobenius {V} {V'} {Pp} {Q} {α}

BC : ∀ {W U V : RML.Obj} (h : RML.Mor U V) {Q : CS.Predicate (G .fobj U)} →
     CS._⊑_ (CS._[_] (CS._⟨_⟩ Q (G .fmor h)) (G .fmor (FDP.p₂ {W} {V})))
            (CS._⟨_⟩ (CS._[_] Q (G .fmor (FDP.p₂ {W} {U})))
                     (G .fmor (FDP.pair FDP.p₁ (FD._∘_ h FDP.p₂))))
BC {W} {U} {V} h {Q} = CPm.⟨⟩-[]-transport {P = Q} (raw-BC h)

BC-assemble : ∀ {C : RML.Obj} {Qp : CS.Predicate (G .fobj (FDP.prod C RML.𝟙L))}
              (x : Setoid.Carrier (RML.idx C)) →
              CS._⊑_ (CS._[_] (CS._⟨_⟩ Qp (G .fmor (RML.assembleF {C})))
                              (G .fmor (RootedMu.elem-in (RML.Lf C) x)))
                     (CS._⟨_⟩ (CS._[_] Qp
                                 (G .fmor (RootedMu.elem-in (FDP.prod C RML.𝟙L)
                                                            (x , lift ttS))))
                              (G .fmor (RootedMu.sing-assemble C x)))
BC-assemble {C} {Qp} x = CPm.⟨⟩-[]-transport {P = Qp} (raw-BC-assemble x)

in₁-extract : ∀ {X Y : RML.Obj} {Q : CS.Predicate (G .fobj X)} →
              CS._⊑_ (CS._[_] (CS._⟨_⟩ Q (G .fmor (RCP.in₁ {X} {Y})))
                              (G .fmor (RCP.in₁ {X} {Y}))) Q
in₁-extract {X} {Y} {Q} =
  ⊑-trans 𝐂-[]⁻¹
  (⊑-trans (𝐂-isClosure .IsClosureOp.mono raw-in₁-extract) (CPm.Predicate.closed Q))

in₂-extract : ∀ {X Y : RML.Obj} {Q : CS.Predicate (G .fobj Y)} →
              CS._⊑_ (CS._[_] (CS._⟨_⟩ Q (G .fmor (RCP.in₂ {X} {Y})))
                              (G .fmor (RCP.in₂ {X} {Y}))) Q
in₂-extract {X} {Y} {Q} =
  ⊑-trans 𝐂-[]⁻¹
  (⊑-trans (𝐂-isClosure .IsClosureOp.mono raw-in₂-extract) (CPm.Predicate.closed Q))

disjoint₁ : ∀ {X Y : RML.Obj} {Q : CS.Predicate (G .fobj Y)}
            (x : Setoid.Carrier (RML.idx X))
            {S : CS.Predicate (G .fobj RML.simple[ PS.𝟙 , X .RML.fam .RML.fm x ])} →
            CS._⊑_ (CS._[_] (CS._⟨_⟩ Q (G .fmor (RCP.in₂ {X} {Y})))
                            (G .fmor (RootedMu.elem-in (RCP.coprod X Y) (inj₁ x)))) S
disjoint₁ {X} {Y} {Q} x {S} =
  ⊑-trans 𝐂-[]⁻¹
  (⊑-trans (𝐂-isClosure .IsClosureOp.mono (raw-disjoint₁ x))
  (⊑-trans (𝐂-isClosure .IsClosureOp.closed) (CPm.Predicate.closed S)))

disjoint₂ : ∀ {X Y : RML.Obj} {Q : CS.Predicate (G .fobj X)}
            (y : Setoid.Carrier (RML.idx Y))
            {S : CS.Predicate (G .fobj RML.simple[ PS.𝟙 , Y .RML.fam .RML.fm y ])} →
            CS._⊑_ (CS._[_] (CS._⟨_⟩ Q (G .fmor (RCP.in₁ {X} {Y})))
                            (G .fmor (RootedMu.elem-in (RCP.coprod X Y) (inj₂ y)))) S
disjoint₂ {X} {Y} {Q} y {S} =
  ⊑-trans 𝐂-[]⁻¹
  (⊑-trans (𝐂-isClosure .IsClosureOp.mono (raw-disjoint₂ y))
  (⊑-trans (𝐂-isClosure .IsClosureOp.closed) (CPm.Predicate.closed S)))

sing-split : ∀ {X : RML.Obj} {Q : CS.Predicate (G .fobj X)} →
             CS._⊑_ Q (CS.⋁ (Setoid.Carrier (RML.idx X))
                         (λ x → CS._⟨_⟩ (CS._[_] Q (G .fmor (RootedMu.elem-in X x)))
                                        (G .fmor (RootedMu.elem-in X x))))
sing-split {X} {Q} =
  ⊑-trans raw-sing-split
    (𝐂-isClosure .IsClosureOp.mono
      (IsBigJoin.least ⋁-isJoin _ _ _
        (λ i → ⊑-trans (𝐂-isClosure .IsClosureOp.unit) (IsBigJoin.upper ⋁-isJoin _ _ i))))

Rt-iso : ∀ {C D : RML.Obj} (h : RML.Mor C D)
         (hinv : ∀ x → RML._⇒_ (D .RML.fam .RML.fm (h .RML.idxf .PS._⇒_.func x))
                                (C .RML.fam .RML.fm x)) →
         (∀ x → RML._≈_ (RML._∘_ (h .RML.famf ._⇒f_.transf x) (hinv x)) (RML.id _)) →
         (∀ x → RML._≈_ (RML._∘_ (hinv x) (h .RML.famf ._⇒f_.transf x)) (RML.id _)) →
         CS._⊑_ (Rt C) (CS._[_] (Rt D) (G .fmor (RML.Lf-map h)))
Rt-iso {C} {D} h hinv e₁ e₂ =
  ⊑-trans (RtDown C)
          (⊑-trans (raw-Rt-iso h hinv e₁ e₂) (RtUp D [ G .fmor (RML.Lf-map h) ]m))

Rt-iso⁻ : ∀ {C D : RML.Obj} (h : RML.Mor C D)
          (hinv : ∀ x → RML._⇒_ (D .RML.fam .RML.fm (h .RML.idxf .PS._⇒_.func x))
                                 (C .RML.fam .RML.fm x)) →
          (∀ x → RML._≈_ (RML._∘_ (h .RML.famf ._⇒f_.transf x) (hinv x)) (RML.id _)) →
          (∀ x → RML._≈_ (RML._∘_ (hinv x) (h .RML.famf ._⇒f_.transf x)) (RML.id _)) →
          CS._⊑_ (CS._[_] (Rt D) (G .fmor (RML.Lf-map h))) (Rt C)
Rt-iso⁻ {C} {D} h hinv e₁ e₂ =
  ⊑-trans (RtDown D [ G .fmor (RML.Lf-map h) ]m)
          (⊑-trans (raw-Rt-iso⁻ h hinv e₁ e₂) (RtUp C))

-- The singleton at a tree factors through that tree's own fibre. An element of the join over trees
-- at a stage factors through the inclusion of one tree only after the stage has been refined to a
-- fibre, where the index part of the factorisation is a bisimilarity between that tree and the one
-- selected; the fibre transports move the predicate along it.
module _ {k} (δ₀ : Fin k → RML.Obj) (δP₀ : ∀ i → CS.Predicate (G .fobj (δ₀ i)))
         (Q : RML.Poly (suc k)) (pQ : RootedMu.PolyPred Q) where

  private
    module Mδ = RootedMu.MuPred δ₀ δP₀
    module Tδ = RML.Tree δ₀
    module MT = Mδ.Transport Rt-iso

    open RootedMu.Gl.Obj renaming (carrier to gcar; pred to gpred)
    open RootedMu.Gl._=>_ using () renaming (morph to gmorph; presv to gpresv)

    dc : ∀ (i : Fin k) → Tδ.DecoAssign (inj₁ i)
    dc i = lift ttS

    pc : ∀ (i : Fin k) → Mδ.DecoAssignPred (inj₁ i) (dc i)
    pc i = lift ttS

    fibGl : Tδ.W RML.∣ Q ∣ (λ i → inj₁ i) → RootedMu.Gl.Obj
    fibGl t = Mδ.fib-Gl Q dc pQ pc t

    tgt : (t : Tδ.W RML.∣ Q ∣ (λ i → inj₁ i)) →
          Predicate (G .fobj RML.simple[ PS.𝟙 , RML.μObj Q δ₀ .RML.fam .RML.fm t ])
    tgt t = CPm.Predicate.pred (gpred (fibGl t)) [ G .fmor (Mδ.tree-out Q pQ t) ]

    raw-step : (t' t : Tδ.W RML.∣ Q ∣ (λ i → inj₁ i)) →
               ((CPm.Predicate.pred (gpred (fibGl t')) ⟨ G .fmor (Mδ.tree-in Q pQ t') ⟩)
                  [ G .fmor (RootedMu.elem-in (RML.μObj Q δ₀) t) ])
                 ⊑ 𝐂 (tgt t)
    raw-step t' t .*⊑* a .*⊑* (lift w) hyp = CvM.node cov xs ts eqs
      where
      SIMP = G .fobj RML.simple[ PS.𝟙 , RML.μObj Q δ₀ .RML.fam .RML.fm t ]

      src : Predicate SIMP
      src = (CPm.Predicate.pred (gpred (fibGl t')) ⟨ G .fmor (Mδ.tree-in Q pQ t') ⟩)
              [ G .fmor (RootedMu.elem-in (RML.μObj Q δ₀) t) ]

      cvr : CF.Rel.IdxCover a
      cvr .CF.Rel.IdxCover.S = FamC.Obj.idx a
      cvr .CF.Rel.IdxCover.D = FC.fibres a
      cvr .CF.Rel.IdxCover.iso = FC.fib-iso a

      cov : CF.Rel.Cover a
      cov = CF.Rel.idx cvr

      xs : ∀ s → Setoid.Carrier (SIMP .fobj (CF.Rel.cDom cov s))
      xs s = SIMP .fmor (CF.Rel.cInj cov s) .PS._⇒_.func (lift w)

      eqs : ∀ s → Setoid._≈_ (SIMP .fobj (CF.Rel.cDom cov s)) (xs s)
                    (SIMP .fmor (CF.Rel.cInj cov s) .PS._⇒_.func (lift w))
      eqs s = Setoid.refl (SIMP .fobj (CF.Rel.cDom cov s))

      ts : ∀ s → CvM.Context SIMP (tgt t) (CF.Rel.cDom cov s) (xs s)
      ts (lift v) = CvM.leaf (go (src .pred-mor (CF.Rel.cInj cov (lift v)) .*⊑* (lift w) hyp))
        where
        wv : RML.Mor (CF.FamF .fobj (CF.Rel.cDom cov (lift v)))
                     RML.simple[ PS.𝟙 , RML.μObj Q δ₀ .RML.fam .RML.fm t ]
        wv = FD._∘_ w (CF.FamF .fmor (CF.Rel.cInj cov (lift v)))

        go : src .pred (CF.Rel.cDom cov (lift v)) .pred (xs (lift v)) →
             tgt t .pred (CF.Rel.cDom cov (lift v)) .pred (xs (lift v))
        go (lift nn , qn , lift eqn) =
          CPm.Predicate.pred (gpred (fibGl t)) .pred (CF.Rel.cDom cov (lift v)) .pred-≃ (lift sq)
            (MT.subst-fib Q dc pQ pc {t'} {t} p .RootedMu.mor .gpresv
               .*⊑* (CF.Rel.cDom cov (lift v)) .*⊑* (lift nn) qn)
          where
          p : Tδ.W-≈ t' t
          p = eqn .RML._≃_.idxf-eq .PS._≃m_.func-eq {lift ttS} {lift ttS} tt

          σ : RML.Mor (fibGl t' .gcar) (fibGl t .gcar)
          σ = MT.subst-fib Q dc pQ pc {t'} {t} p .RootedMu.mor .gmorph

          sq : FD._≈_ (FD._∘_ σ (FD._∘_ nn (FD.id _)))
                      (FD._∘_ (Mδ.tree-out Q pQ t) (FD._∘_ wv (FD.id _)))
          sq .RML._≃_.idxf-eq .PS._≃m_.func-eq _ = Mδ.fib-ix-uniq Q dc pQ pc t _
          sq .RML._≃_.famf-eq ._≃f_.transf-eq {i} =
            RML.≈-trans (RML.∘-cong RML.≈-refl (strip-f S N))
              (RML.≈-trans main (RML.≈-sym (strip-f O Wf)))
            where
            ι = nn .RML.idxf .PS._⇒_.func i
            N = nn .RML.famf ._⇒f_.transf i
            S = σ .RML.famf ._⇒f_.transf ι
            Wf = wv .RML.famf ._⇒f_.transf i
            ix = Mδ.fib-ix Q dc pQ pc t
            O = Mδ.out-fib Q dc pQ pc t ix

            ixe : Setoid._≈_ (RML.idx (fibGl t .gcar)) (σ .RML.idxf .PS._⇒_.func ι) ix
            ixe = Mδ.fib-ix-uniq Q dc pQ pc t _

            sub = fibGl t .gcar .RML.fam .RML.subst ixe

            H : RML._≈_ (RML._∘_ (Tδ.fib-subst Q dc {t'} {t} p)
                                 (RML._∘_ (Mδ.in-fib Q dc pQ pc t' ι) N))
                        Wf
            H = RML.≈-trans
                  (RML.≈-sym (RML.∘-cong RML.≈-refl (strip-f (Mδ.in-fib Q dc pQ pc t' ι) N)))
                  (RML.≈-trans (eqn .RML._≃_.famf-eq ._≃f_.transf-eq {i}) (strip Wf))

            main : RML._≈_ (RML._∘_ sub (RML._∘_ S N)) (RML._∘_ O Wf)
            main = begin
                RML._∘_ sub (RML._∘_ S N)
              ≈˘⟨ RML.id-left ⟩
                RML._∘_ (RML.id _) (RML._∘_ sub (RML._∘_ S N))
              ≈˘⟨ RML.∘-cong (Mδ.out-in-fib Q dc pQ pc t ix) RML.≈-refl ⟩
                RML._∘_ (RML._∘_ O (Mδ.in-fib Q dc pQ pc t ix)) (RML._∘_ sub (RML._∘_ S N))
              ≈⟨ RML.assoc _ _ _ ⟩
                RML._∘_ O (RML._∘_ (Mδ.in-fib Q dc pQ pc t ix) (RML._∘_ sub (RML._∘_ S N)))
              ≈˘⟨ RML.∘-cong RML.≈-refl (RML.assoc _ _ _) ⟩
                RML._∘_ O (RML._∘_ (RML._∘_ (Mδ.in-fib Q dc pQ pc t ix) sub) (RML._∘_ S N))
              ≈⟨ RML.∘-cong RML.≈-refl
                   (RML.∘-cong (Mδ.in-fib-natural Q dc pQ pc t ixe) RML.≈-refl) ⟩
                RML._∘_ O (RML._∘_ (Mδ.in-fib Q dc pQ pc t (σ .RML.idxf .PS._⇒_.func ι))
                                   (RML._∘_ S N))
              ≈˘⟨ RML.∘-cong RML.≈-refl (RML.assoc _ _ _) ⟩
                RML._∘_ O (RML._∘_ (RML._∘_ (Mδ.in-fib Q dc pQ pc t
                                               (σ .RML.idxf .PS._⇒_.func ι)) S) N)
              ≈⟨ RML.∘-cong RML.≈-refl
                   (RML.∘-cong (MT.subst-fib-in Q dc pQ pc {t'} {t} p ι) RML.≈-refl) ⟩
                RML._∘_ O (RML._∘_ (RML._∘_ (Tδ.fib-subst Q dc {t'} {t} p)
                                            (Mδ.in-fib Q dc pQ pc t' ι)) N)
              ≈⟨ RML.∘-cong RML.≈-refl (RML.assoc _ _ _) ⟩
                RML._∘_ O (RML._∘_ (Tδ.fib-subst Q dc {t'} {t} p)
                                   (RML._∘_ (Mδ.in-fib Q dc pQ pc t' ι) N))
              ≈⟨ RML.∘-cong RML.≈-refl H ⟩
                RML._∘_ O Wf
              ∎
              where open ≈-Reasoning RML.isEquiv

  -- The join over trees, restricted along the singleton at a tree, lands in that tree's disjunct.
  sing-extract : (t : Tδ.W RML.∣ Q ∣ (λ i → inj₁ i)) →
                 CS._⊑_ (CS._[_] (gpred (Mδ.μ-Gl Q pQ))
                                 (G .fmor (RootedMu.elem-in (RML.μObj Q δ₀) t)))
                        (CS._[_] (gpred (fibGl t)) (G .fmor (Mδ.tree-out Q pQ t)))
  sing-extract t =
    ⊑-trans 𝐂-[]⁻¹
    (⊑-trans (𝐂-isClosure .IsClosureOp.mono ([]-⋁ {I = Tδ.W RML.∣ Q ∣ (λ i → inj₁ i)}
                                                  {P = joins} {f = ein}))
    (⊑-trans (𝐂-isClosure .IsClosureOp.mono
               (IsBigJoin.least ⋁-isJoin (Tδ.W RML.∣ Q ∣ (λ i → inj₁ i))
                                (λ t' → joins t' [ ein ]) (𝐂 (tgt t)) step))
    (⊑-trans (𝐂-isClosure .IsClosureOp.closed)
             (CPm.Predicate.closed
                (CS._[_] (gpred (fibGl t)) (G .fmor (Mδ.tree-out Q pQ t)))))))
    where
    ein = G .fmor (RootedMu.elem-in (RML.μObj Q δ₀) t)

    -- The disjuncts of the μ-decoration, at the raw level: the closed direct image of each
    -- fibre's predicate along that fibre's inclusion.
    joins : Tδ.W RML.∣ Q ∣ (λ i → inj₁ i) → Predicate (G .fobj (RML.μObj Q δ₀))
    joins t' = 𝐂 (CPm.Predicate.pred (gpred (fibGl t'))
                    ⟨ G .fmor (Mδ.tree-in Q pQ t') ⟩)

    step : ∀ t' → (joins t' [ ein ]) ⊑ 𝐂 (tgt t)
    step t' =
      ⊑-trans 𝐂-[]⁻¹
      (⊑-trans (𝐂-isClosure .IsClosureOp.mono (raw-step t' t))
               (𝐂-isClosure .IsClosureOp.closed))
