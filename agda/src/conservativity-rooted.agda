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
open import Data.Unit using () renaming (tt to ttS)
open import prop using (Prf; ∃; ∃ₛ; _∧_; _,_; LiftP; lift; ⊥-elim; tt)
open import Data.Sum using (inj₁; inj₂)
open import prop-setoid as PS using (Setoid; module ≈-Reasoning)
open import basics using (IsBigJoin; IsClosureOp)
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

open CF.Rel using (G; PSh⟨𝒞⟩; PSh⟨𝒞⟩-products; PSh⟨𝒞⟩-system; closureOp;
                   &&-++-distrib; &&-⋁-distrib; &&-⟨⟩-frobenius; ⟨⟩-[]-BC)

-- The rooted structure on the same category of families.
module RML = fam-mu-lifting.laws 0ℓ 0ℓ 𝒟₀T CM' BP' Lft'

open PredicateSystem PSh⟨𝒞⟩-system
open ClosureOp closureOp using (𝐂; 𝐂-isClosure; 𝐂-[]; 𝐂-[]⁻¹)

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

in₁-extract : ∀ {X Y : RML.Obj} {Q : Predicate (G .fobj X)} →
              ((Q ⟨ G .fmor (RCP.in₁ {X} {Y}) ⟩) [ G .fmor (RCP.in₁ {X} {Y}) ]) ⊑ Q
in₁-extract {X} {Y} {Q} .*⊑* a .*⊑* (lift u) (lift u' , qu' , lift eq) =
  Q .pred a .pred-≃ (lift mono) qu'
  where
  mono : FD._≈_ u' u
  mono .RML._≃_.idxf-eq .PS._≃m_.func-eq p = eq .RML._≃_.idxf-eq .PS._≃m_.func-eq p
  mono .RML._≃_.famf-eq ._≃f_.transf-eq {i} =
    RML.≈-trans (RML.∘-cong RML.≈-refl (RML.≈-sym (strip (u' .RML.famf ._⇒f_.transf i))))
                (RML.≈-trans (eq .RML._≃_.famf-eq ._≃f_.transf-eq)
                             (strip (u .RML.famf ._⇒f_.transf i)))

in₂-extract : ∀ {X Y : RML.Obj} {Q : Predicate (G .fobj Y)} →
              ((Q ⟨ G .fmor (RCP.in₂ {X} {Y}) ⟩) [ G .fmor (RCP.in₂ {X} {Y}) ]) ⊑ Q
in₂-extract {X} {Y} {Q} .*⊑* a .*⊑* (lift u) (lift u' , qu' , lift eq) =
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

Rt : ∀ (C : RML.Obj) → Predicate (G .fobj (RML.Lf C))
Rt C = 𝐂 (RtJoin C)

-- The glued rooted μ interface at the family-level nerve.
module RootedMu =
  fam-mu-lifting.glued-interface 𝒟₀T CM' BP' Lft'
    PSh⟨𝒞⟩ PSh⟨𝒞⟩-products PSh⟨𝒞⟩-system G Rt closureOp

sing-split : ∀ {X : RML.Obj} {Q : Predicate (G .fobj X)} →
             Q ⊑ 𝐂 (⋁ (Setoid.Carrier (RML.idx X))
                      (λ x → (Q [ G .fmor (RootedMu.elem-in X x) ])
                               ⟨ G .fmor (RootedMu.elem-in X x) ⟩))
sing-split {X} {Q} .*⊑* a .*⊑* (lift m) qm = CvM.node cov xs ts eqs
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

Rt-iso : ∀ {C D : RML.Obj} (h : RML.Mor C D)
         (hinv : ∀ x → RML._⇒_ (D .RML.fam .RML.fm (h .RML.idxf .PS._⇒_.func x))
                                (C .RML.fam .RML.fm x)) →
         (∀ x → RML._≈_ (RML._∘_ (h .RML.famf ._⇒f_.transf x) (hinv x)) (RML.id _)) →
         (∀ x → RML._≈_ (RML._∘_ (hinv x) (h .RML.famf ._⇒f_.transf x)) (RML.id _)) →
         Rt C ⊑ (Rt D [ G .fmor (RML.Lf-map h) ])
Rt-iso {C} {D} h hinv e₁ e₂ =
  ⊑-trans (IsClosureOp.mono 𝐂-isClosure (IsBigJoin.least ⋁-isJoin _ _ _ step)) 𝐂-[]
  where
  step : ∀ i → (TT ⟨ G .fmor (root-mor C i) ⟩) ⊑ (RtJoin D [ G .fmor (RML.Lf-map h) ])
  step i =
    adjoint₂
      (⊑-trans (adjoint₁ (IsBigJoin.upper ⋁-isJoin _ _ (h .RML.idxf .PS._⇒_.func i)))
      (⊑-trans ([]-cong (G .fmor-cong (root-square h i)))
      (⊑-trans ([]-cong (G .fmor-comp _ _)) ([]-comp⁻¹ _ _))))

Rt-iso⁻ : ∀ {C D : RML.Obj} (h : RML.Mor C D)
          (hinv : ∀ x → RML._⇒_ (D .RML.fam .RML.fm (h .RML.idxf .PS._⇒_.func x))
                                 (C .RML.fam .RML.fm x)) →
          (∀ x → RML._≈_ (RML._∘_ (h .RML.famf ._⇒f_.transf x) (hinv x)) (RML.id _)) →
          (∀ x → RML._≈_ (RML._∘_ (hinv x) (h .RML.famf ._⇒f_.transf x)) (RML.id _)) →
          (Rt D [ G .fmor (RML.Lf-map h) ]) ⊑ Rt C
Rt-iso⁻ {C} {D} h hinv e₁ e₂ =
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

disjoint₁ : ∀ {X Y : RML.Obj} {Q : Predicate (G .fobj Y)} (x : Setoid.Carrier (RML.idx X))
            {C : RML.Obj}
            (h : RML.Mor RML.simple[ PS.𝟙 , X .RML.fam .RML.fm x ] (RML.Lf C)) →
            ((Q ⟨ G .fmor (RCP.in₂ {X} {Y}) ⟩)
               [ G .fmor (RootedMu.elem-in (RCP.coprod X Y) (inj₁ x)) ])
              ⊑ (Rt C [ G .fmor h ])
disjoint₁ {X} {Y} {Q} x {C} h .*⊑* a .*⊑* (lift w) hyp = CvM.node cov xs ts eqs
  where
  src : Predicate (G .fobj RML.simple[ PS.𝟙 , X .RML.fam .RML.fm x ])
  src = (Q ⟨ G .fmor (RCP.in₂ {X} {Y}) ⟩)
          [ G .fmor (RootedMu.elem-in (RCP.coprod X Y) (inj₁ x)) ]

  z : Setoid.Carrier (G .fobj (RML.Lf C) .fobj a)
  z = G .fmor h .transf a .PS._⇒_.func (lift w)

  cvr : CF.Rel.IdxCover a
  cvr .CF.Rel.IdxCover.S = FamC.Obj.idx a
  cvr .CF.Rel.IdxCover.D = FC.fibres a
  cvr .CF.Rel.IdxCover.iso = FC.fib-iso a

  cov : CF.Rel.Cover a
  cov = CF.Rel.idx cvr

  xs : ∀ s → Setoid.Carrier (G .fobj (RML.Lf C) .fobj (CF.Rel.cDom cov s))
  xs s = G .fobj (RML.Lf C) .fmor (CF.Rel.cInj cov s) .PS._⇒_.func z

  eqs : ∀ s → Setoid._≈_ (G .fobj (RML.Lf C) .fobj (CF.Rel.cDom cov s)) (xs s)
                (G .fobj (RML.Lf C) .fmor (CF.Rel.cInj cov s) .PS._⇒_.func z)
  eqs s = Setoid.refl (G .fobj (RML.Lf C) .fobj (CF.Rel.cDom cov s))

  ts : ∀ s → CvM.Context (G .fobj (RML.Lf C)) (RtJoin C) (CF.Rel.cDom cov s) (xs s)
  ts (lift v) = CvM.leaf (go (src .pred-mor (CF.Rel.cInj cov (lift v)) .*⊑* (lift w) hyp))
    where
    go : src .pred (CF.Rel.cDom cov (lift v)) .pred
           (G .fobj RML.simple[ PS.𝟙 , X .RML.fam .RML.fm x ]
              .fmor (CF.Rel.cInj cov (lift v)) .PS._⇒_.func (lift w)) →
         RtJoin C .pred (CF.Rel.cDom cov (lift v)) .pred (xs (lift v))
    go (lift u , qu , lift eqv) =
      ⊥-elim (eqv .RML._≃_.idxf-eq .PS._≃m_.func-eq {lift ttS} {lift ttS} tt)

disjoint₂ : ∀ {X Y : RML.Obj} {Q : Predicate (G .fobj X)} (y : Setoid.Carrier (RML.idx Y))
            {C : RML.Obj}
            (h : RML.Mor RML.simple[ PS.𝟙 , Y .RML.fam .RML.fm y ] (RML.Lf C)) →
            ((Q ⟨ G .fmor (RCP.in₁ {X} {Y}) ⟩)
               [ G .fmor (RootedMu.elem-in (RCP.coprod X Y) (inj₂ y)) ])
              ⊑ (Rt C [ G .fmor h ])
disjoint₂ {X} {Y} {Q} y {C} h .*⊑* a .*⊑* (lift w) hyp = CvM.node cov xs ts eqs
  where
  src : Predicate (G .fobj RML.simple[ PS.𝟙 , Y .RML.fam .RML.fm y ])
  src = (Q ⟨ G .fmor (RCP.in₁ {X} {Y}) ⟩)
          [ G .fmor (RootedMu.elem-in (RCP.coprod X Y) (inj₂ y)) ]

  z : Setoid.Carrier (G .fobj (RML.Lf C) .fobj a)
  z = G .fmor h .transf a .PS._⇒_.func (lift w)

  cvr : CF.Rel.IdxCover a
  cvr .CF.Rel.IdxCover.S = FamC.Obj.idx a
  cvr .CF.Rel.IdxCover.D = FC.fibres a
  cvr .CF.Rel.IdxCover.iso = FC.fib-iso a

  cov : CF.Rel.Cover a
  cov = CF.Rel.idx cvr

  xs : ∀ s → Setoid.Carrier (G .fobj (RML.Lf C) .fobj (CF.Rel.cDom cov s))
  xs s = G .fobj (RML.Lf C) .fmor (CF.Rel.cInj cov s) .PS._⇒_.func z

  eqs : ∀ s → Setoid._≈_ (G .fobj (RML.Lf C) .fobj (CF.Rel.cDom cov s)) (xs s)
                (G .fobj (RML.Lf C) .fmor (CF.Rel.cInj cov s) .PS._⇒_.func z)
  eqs s = Setoid.refl (G .fobj (RML.Lf C) .fobj (CF.Rel.cDom cov s))

  ts : ∀ s → CvM.Context (G .fobj (RML.Lf C)) (RtJoin C) (CF.Rel.cDom cov s) (xs s)
  ts (lift v) = CvM.leaf (go (src .pred-mor (CF.Rel.cInj cov (lift v)) .*⊑* (lift w) hyp))
    where
    go : src .pred (CF.Rel.cDom cov (lift v)) .pred
           (G .fobj RML.simple[ PS.𝟙 , Y .RML.fam .RML.fm y ]
              .fmor (CF.Rel.cInj cov (lift v)) .PS._⇒_.func (lift w)) →
         RtJoin C .pred (CF.Rel.cDom cov (lift v)) .pred (xs (lift v))
    go (lift u , qu , lift eqv) =
      ⊥-elim (eqv .RML._≃_.idxf-eq .PS._≃m_.func-eq {lift ttS} {lift ttS} tt)

dist : ∀ {V} {Pp Q S : Predicate V} → (Pp && (Q ++ S)) ⊑ ((Pp && Q) ++ (Pp && S))
dist = &&-++-distrib

dist-⋁ : ∀ {V} {I : Set 0ℓ} {Pp : Predicate V} {Qs : I → Predicate V} →
         (Pp && ⋁ I Qs) ⊑ ⋁ I (λ i → Pp && Qs i)
dist-⋁ = &&-⋁-distrib

frob : ∀ {V V'} {Pp : Predicate V'} {Q : Predicate V} {α : V PSh⟨𝒞⟩C.⇒ V'} →
       (Pp && (Q ⟨ α ⟩)) ⊑ (((Pp [ α ]) && Q) ⟨ α ⟩)
frob = &&-⟨⟩-frobenius

BC : ∀ {W U V : RML.Obj} (h : RML.Mor U V) {Q : Predicate (G .fobj U)} →
     ((Q ⟨ G .fmor h ⟩) [ G .fmor (FDP.p₂ {W} {V}) ])
       ⊑ ((Q [ G .fmor (FDP.p₂ {W} {U}) ])
            ⟨ G .fmor (FDP.pair FDP.p₁ (FD._∘_ h FDP.p₂)) ⟩)
BC {W} {U} {V} h {Q} = ⟨⟩-[]-BC lft
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
