{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- The rooted logical relations: Kripke predicates whose stages are families, with the rooted
-- μ-types glued on top. Stages are taken at the family level because a stage's own fibre
-- decomposition is then a cover of it, which is what splitting a family into its fibres needs. The
-- model side is already the category of families the rooted machinery is built over, so the nerve
-- serves as the glueing functor unchanged. The root predicate picks out
-- the definable root selections: the maps into a lifted family that factor
-- through a bare root at some index, up to cover refinement.
------------------------------------------------------------------------------

open import Level using (Level; 0ℓ; lift)
open import Data.Nat using (suc)
import Data.Fin as Fin
open Fin using (Fin)
open import Data.Product using (_,_; proj₁)
open import Data.Unit using () renaming (tt to ttS)
open import prop using (∃; _∧_; _,_; LiftP; lift; ⊥-elim; tt)
open import Data.Sum using (inj₁; inj₂)
open import prop-setoid as PS using (Setoid; module ≈-Reasoning)
open import basics using (IsPreorder; IsMeet; IsJoin; IsBigJoin; IsClosureOp)
open import categories using (Category; HasTerminal; HasCoproducts)
open import cmon-enriched using (CMonEnriched; Biproduct)
open import commutative-monoid using (CommutativeMonoid)
open import lifting using (Lifting)
open import functor using (Functor; NatTrans)
open import indexed-family using (_⇒f_; _≃f_)
open import predicate-system using (PredicateSystem; ClosureOp)
import fam
import setoid-predicate
import closure-predicate
import fam-fibre-cover
import fam-functor
import fam-stable-indexed
import conservativity-base
import fam-mu-lifting.laws
import fam-mu-lifting.glued-interface

module conservativity-rooted {o₁ o₂ m e}
  {𝒞₀ : Category o₁ m e}
  {𝒟₀ : Category o₂ m e} (𝒟₀T : HasTerminal 𝒟₀)
  (CM' : CMonEnriched 𝒟₀) (BP' : ∀ x y → Biproduct CM' x y)
  {𝟙d : Category.obj 𝒟₀} (Lft' : Lifting CM' 𝟙d)
  (F₀ : Functor 𝒞₀ 𝒟₀)
  where

open Functor

private
  module Fam𝒞 = fam.CategoryOfFamilies 0ℓ 0ℓ 𝒞₀
  module Fam𝒟 = fam.CategoryOfFamilies 0ℓ 0ℓ 𝒟₀

FamF : Functor Fam𝒞.cat Fam𝒟.cat
FamF = fam-functor.FamF 0ℓ 0ℓ F₀

module CB = conservativity-base
  Fam𝒞.cat Fam𝒞.bigCoproducts (fam-stable-indexed.fam-stable-indexed 𝒞₀) Fam𝒟.cat FamF

open CB using (G; PSh⟨𝒞⟩; PSh⟨𝒞⟩-products; PSh⟨𝒞⟩-system; closureOp; system;
                   &&-++-distrib; &&-⋁-distrib; &&-⟨⟩-frobenius; ⟨⟩-[]-BC)

-- The rooted structure on the same category of families.
module RML = fam-mu-lifting.laws 0ℓ 0ℓ 𝒟₀T CM' BP' Lft'

open PredicateSystem PSh⟨𝒞⟩-system
open ClosureOp closureOp using (𝐂; 𝐂-isClosure; 𝐂-[]; 𝐂-[]⁻¹; 𝐂-strong; 𝐂-strongʳ)

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
open CB.PShPredicate
open CB._⊑_
open setoid-predicate.Predicate
open setoid-predicate._⊑_

private
  module FD = Category RML.cat
  module FDP = RML.Fam𝒞-P
  module PSh⟨𝒞⟩C = Category PSh⟨𝒞⟩
  module FamC = fam.CategoryOfFamilies 0ℓ 0ℓ 𝒞₀
  module FC = fam-fibre-cover 0ℓ 0ℓ 𝒞₀
  module CvM = CB.CvM
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

  strip-π : ∀ {A B C : RML.obj} (f : RML._⇒_ B C) (t : RML._⇒_ A B) →
            RML._≈_ (RML._∘_ (RML.id _)
                       (RML._∘_ f
                         (RML._∘_ (RML.id _)
                           (RML._∘_ (RML._∘_ (RML.id _)
                                       (RML._∘_ (RML.id _)
                                         (RML._∘_ (RML.id _) (RML._∘_ t (RML.id _)))))
                                    (RML.id _)))))
                    (RML._∘_ f t)
  strip-π f t = RML.≈-trans (strip-f f _) (RML.∘-cong RML.≈-refl (strip t))

  module CPm = closure-predicate PSh⟨𝒞⟩-system closureOp
  module CPd = CPm.distributive &&-++-distrib &&-⟨⟩-frobenius

  -- The canonical cover of a stage by its own fibres.
  fibcov : ∀ (a : FamC.Obj) → CB.Cover a
  fibcov a = CB.idx cvr
    where
    cvr : CB.IdxCover a
    cvr .CB.IdxCover.S = FamC.Obj.idx a
    cvr .CB.IdxCover.D = FC.fibres a
    cvr .CB.IdxCover.iso = FC.fib-iso a

  -- Membership in the cover closure can be established fibrewise: a predicate covers an element as
  -- soon as it holds of the element's restriction to every fibre of the stage.
  by-fibres : ∀ {V : PSh⟨𝒞⟩C.obj} {Src T : Predicate V} →
              (∀ a (x : Setoid.Carrier (V .fobj a)) → Src .pred a .pred x →
               ∀ (v : CB.CIx (fibcov a)) →
                 T .pred (CB.cDom (fibcov a) v) .pred
                   (V .fmor (CB.cInj (fibcov a) v) .PS._⇒_.func x)) →
              Src ⊑ 𝐂 T
  by-fibres {V} {Src} {T} go .*⊑* a .*⊑* x hyp =
    CvM.node (fibcov a)
             (λ s → V .fmor (CB.cInj (fibcov a) s) .PS._⇒_.func x)
             (λ s → CvM.leaf (go a x hyp s))
             (λ s → Setoid.refl (V .fobj (CB.cDom (fibcov a) s)))

  -- A map into a product with the lifting's unit whose first index component is constant
  -- transports to the singleton at that index.
  to-sing : ∀ {a : FamC.Obj} {C : RML.Obj}
            (u : RML.Mor (FamF .fobj a) (FDP.prod C RML.𝟙L))
            {x : Setoid.Carrier (RML.idx C)}
            (ex : ∀ i → Setoid._≈_ (RML.idx C) (proj₁ (u .RML.idxf .PS._⇒_.func i)) x) →
            RML.Mor (FamF .fobj a) RML.simple[ PS.𝟙 , RML.prod (C .RML.fam .RML.fm x) 𝟙d ]
  to-sing {a} {C} u {x} ex .RML.idxf = PS.to-𝟙
  to-sing {a} {C} u {x} ex .RML.famf ._⇒f_.transf i =
    RML._∘_ (RML.prod-m (C .RML.fam .RML.subst (ex i)) (RML.id 𝟙d))
            (u .RML.famf ._⇒f_.transf i)
  to-sing {a} {C} u {x} ex .RML.famf ._⇒f_.natural p =
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

  push-𝐂 : ∀ {V W : PSh⟨𝒞⟩C.obj} {Pp : Predicate W} {Q : Predicate V} {f : W PSh⟨𝒞⟩C.⇒ V} →
           (Pp && ((𝐂 Q) [ f ])) ⊑ 𝐂 (Pp && (Q [ f ]))
  push-𝐂 = ⊑-trans (IsMeet.mono &&-isMeet (⊑-isPreorder .IsPreorder.refl) 𝐂-[]⁻¹) 𝐂-strongʳ

  -- Restriction along a monic morphism extracts the direct image.
  raw-monic-extract : ∀ {X Y : RML.Obj} (h : RML.Mor X Y) →
                      (∀ {A : RML.Obj} {u u' : RML.Mor A X} →
                       FD._≈_ (FD._∘_ h u') (FD._∘_ h u) → FD._≈_ u' u) →
                      ∀ {Q : Predicate (G .fobj X)} →
                      ((Q ⟨ G .fmor h ⟩) [ G .fmor h ]) ⊑ Q
  raw-monic-extract h monic {Q} .*⊑* a .*⊑* (lift u) (lift u' , qu' , lift eq) =
    Q .pred a .pred-≃
      (lift (monic (FD.≈-trans (FD.∘-cong FD.≈-refl (FD.≈-sym FD.id-right))
                   (FD.≈-trans eq (FD.∘-cong FD.≈-refl FD.id-right)))))
      qu'

  in₁-monic : ∀ {X Y A : RML.Obj} {u u' : RML.Mor A X} →
              FD._≈_ (FD._∘_ (RCP.in₁ {X} {Y}) u') (FD._∘_ (RCP.in₁ {X} {Y}) u) →
              FD._≈_ u' u
  in₁-monic eq .RML._≃_.idxf-eq .PS._≃m_.func-eq p = eq .RML._≃_.idxf-eq .PS._≃m_.func-eq p
  in₁-monic eq .RML._≃_.famf-eq ._≃f_.transf-eq =
    RML.≈-trans (RML.∘-cong RML.≈-refl (RML.≈-sym (RML.≈-trans RML.id-left RML.id-left)))
      (RML.≈-trans (eq .RML._≃_.famf-eq ._≃f_.transf-eq)
                   (RML.≈-trans RML.id-left RML.id-left))

  in₂-monic : ∀ {X Y A : RML.Obj} {u u' : RML.Mor A Y} →
              FD._≈_ (FD._∘_ (RCP.in₂ {X} {Y}) u') (FD._∘_ (RCP.in₂ {X} {Y}) u) →
              FD._≈_ u' u
  in₂-monic eq .RML._≃_.idxf-eq .PS._≃m_.func-eq p = eq .RML._≃_.idxf-eq .PS._≃m_.func-eq p
  in₂-monic eq .RML._≃_.famf-eq ._≃f_.transf-eq =
    RML.≈-trans (RML.∘-cong RML.≈-refl (RML.≈-sym (RML.≈-trans RML.id-left RML.id-left)))
      (RML.≈-trans (eq .RML._≃_.famf-eq ._≃f_.transf-eq)
                   (RML.≈-trans RML.id-left RML.id-left))

-- The bare root of a lifted family at an index.
root-mor : ∀ (C : RML.Obj) (i : Setoid.Carrier (RML.idx C)) → RML.Mor RML.𝟙L (RML.Lf C)
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
Rt C = CPm.embed (RtJoin C)

-- The glued rooted μ interface at the family-level nerve.
module RootedMu =
  fam-mu-lifting.glued-interface 𝒟₀T CM' BP' Lft'
    PSh⟨𝒞⟩ PSh⟨𝒞⟩-products system G Rt idCl

open RootedMu.Gl.Obj renaming (carrier to gcar; pred to gpred)
open RootedMu.Gl._=>_ using () renaming (morph to gmorph; presv to gpresv)

raw-sing-split : ∀ {X : RML.Obj} {Q : Predicate (G .fobj X)} →
             Q ⊑ 𝐂 (⋁ (Setoid.Carrier (RML.idx X))
                      (λ x → (Q [ G .fmor (RootedMu.elem-in X x) ])
                               ⟨ G .fmor (RootedMu.elem-in X x) ⟩))
raw-sing-split {X} {Q} = by-fibres go
  where
  go : ∀ a (x : Setoid.Carrier (G .fobj X .fobj a)) → Q .pred a .pred x →
       ∀ (v : CB.CIx (fibcov a)) →
       ⋁ (Setoid.Carrier (RML.idx X))
         (λ x' → (Q [ G .fmor (RootedMu.elem-in X x') ])
                   ⟨ G .fmor (RootedMu.elem-in X x') ⟩)
         .pred (CB.cDom (fibcov a) v) .pred
         (G .fobj X .fmor (CB.cInj (fibcov a) v) .PS._⇒_.func x)
  go a (lift m) qm v = xv , (lift wv , (qw , ew))
    where
    cd = CB.cDom (fibcov a) v
    cj = CB.cInj (fibcov a) v

    mj : RML.Mor (FamF .fobj cd) X
    mj = FD._∘_ m (FamF .fmor cj)

    xv : Setoid.Carrier (RML.idx X)
    xv = mj .RML.idxf .PS._⇒_.func (lift ttS)

    wv : RML.Mor (FamF .fobj cd) RML.simple[ PS.𝟙 , X .RML.fam .RML.fm xv ]
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

    ew : Setoid._≈_ (G .fobj X .fobj cd)
           (G .fmor (RootedMu.elem-in X xv) .transf cd .PS._⇒_.func (lift wv))
           (G .fobj X .fmor cj .PS._⇒_.func (lift m))
    ew = lift sq

    qw : (Q [ G .fmor (RootedMu.elem-in X xv) ]) .pred cd .pred (lift wv)
    qw = Q .pred cd .pred-≃
           (Setoid.sym (G .fobj X .fobj cd) ew)
           (Q .pred-mor cj .*⊑* (lift m) qm)

private
  root-square : ∀ {C D : RML.Obj} (h : RML.Mor C D) (i : Setoid.Carrier (RML.idx C)) →
                FD._≈_ (root-mor D (h .RML.idxf .PS._⇒_.func i))
                       (FD._∘_ (RML.Lf-map h) (root-mor C i))
  root-square {C} {D} h i .RML._≃_.idxf-eq .PS._≃m_.func-eq _ = Setoid.refl (RML.idx D)
  root-square {C} {D} h i .RML._≃_.famf-eq ._≃f_.transf-eq =
    RML.≈-trans (RML.Lmap-root _)
                (RML.≈-sym (RML.≈-trans RML.id-left (RML.Lmap-root _)))

raw-Rt-iso : ∀ {C D : RML.Obj} (h : RML.Mor C D) →
         RtRaw C ⊑ (RtRaw D [ G .fmor (RML.Lf-map h) ])
raw-Rt-iso {C} {D} h =
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
          (∀ x → RML._≈_ (RML._∘_ (hinv x) (h .RML.famf ._⇒f_.transf x)) (RML.id _)) →
          (RtRaw D [ G .fmor (RML.Lf-map h) ]) ⊑ RtRaw C
raw-Rt-iso⁻ {C} {D} h hinv e₂ =
  ⊑-trans 𝐂-[]⁻¹
          (⊑-trans (IsClosureOp.mono 𝐂-isClosure ψ) (IsClosureOp.closed 𝐂-isClosure))
  where
  src : Predicate (G .fobj (RML.Lf C))
  src = RtJoin D [ G .fmor (RML.Lf-map h) ]

  ψ : src ⊑ 𝐂 (RtJoin C)
  ψ = by-fibres step
    where
    step : ∀ a (x : Setoid.Carrier (G .fobj (RML.Lf C) .fobj a)) → src .pred a .pred x →
           ∀ (v : CB.CIx (fibcov a)) →
           RtJoin C .pred (CB.cDom (fibcov a) v) .pred
             (G .fobj (RML.Lf C) .fmor (CB.cInj (fibcov a) v) .PS._⇒_.func x)
    step a (lift w) hyp v = go (src .pred-mor cj .*⊑* (lift w) hyp)
      where
      cd = CB.cDom (fibcov a) v
      cj = CB.cInj (fibcov a) v

      wv : RML.Mor (FamF .fobj cd) (RML.Lf C)
      wv = FD._∘_ w (FamF .fmor cj)

      iv : Setoid.Carrier (RML.idx C)
      iv = wv .RML.idxf .PS._⇒_.func (lift ttS)

      go : src .pred cd .pred (G .fobj (RML.Lf C) .fmor cj .PS._⇒_.func (lift w)) →
           RtJoin C .pred cd .pred (G .fobj (RML.Lf C) .fmor cj .PS._⇒_.func (lift w))
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
raw-disjoint₁ {X} {Y} {Q} x {T} = by-fibres step
  where
  SIMP = G .fobj RML.simple[ PS.𝟙 , X .RML.fam .RML.fm x ]

  src : Predicate SIMP
  src = (Q ⟨ G .fmor (RCP.in₂ {X} {Y}) ⟩)
          [ G .fmor (RootedMu.elem-in (RCP.coprod X Y) (inj₁ x)) ]

  step : ∀ a (w : Setoid.Carrier (SIMP .fobj a)) → src .pred a .pred w →
         ∀ (v : CB.CIx (fibcov a)) →
         T .pred (CB.cDom (fibcov a) v) .pred
           (SIMP .fmor (CB.cInj (fibcov a) v) .PS._⇒_.func w)
  step a (lift w) hyp v = go (src .pred-mor cj .*⊑* (lift w) hyp)
    where
    cd = CB.cDom (fibcov a) v
    cj = CB.cInj (fibcov a) v

    go : src .pred cd .pred (SIMP .fmor cj .PS._⇒_.func (lift w)) →
         T .pred cd .pred (SIMP .fmor cj .PS._⇒_.func (lift w))
    go (lift u , qu , lift eqv) =
      ⊥-elim (eqv .RML._≃_.idxf-eq .PS._≃m_.func-eq {lift ttS} {lift ttS} tt)

raw-disjoint₂ : ∀ {X Y : RML.Obj} {Q : Predicate (G .fobj X)}
                (y : Setoid.Carrier (RML.idx Y))
                {T : Predicate (G .fobj RML.simple[ PS.𝟙 , Y .RML.fam .RML.fm y ])} →
                ((Q ⟨ G .fmor (RCP.in₁ {X} {Y}) ⟩)
                   [ G .fmor (RootedMu.elem-in (RCP.coprod X Y) (inj₂ y)) ])
                  ⊑ 𝐂 T
raw-disjoint₂ {X} {Y} {Q} y {T} = by-fibres step
  where
  SIMP = G .fobj RML.simple[ PS.𝟙 , Y .RML.fam .RML.fm y ]

  src : Predicate SIMP
  src = (Q ⟨ G .fmor (RCP.in₁ {X} {Y}) ⟩)
          [ G .fmor (RootedMu.elem-in (RCP.coprod X Y) (inj₂ y)) ]

  step : ∀ a (w : Setoid.Carrier (SIMP .fobj a)) → src .pred a .pred w →
         ∀ (v : CB.CIx (fibcov a)) →
         T .pred (CB.cDom (fibcov a) v) .pred
           (SIMP .fmor (CB.cInj (fibcov a) v) .PS._⇒_.func w)
  step a (lift w) hyp v = go (src .pred-mor cj .*⊑* (lift w) hyp)
    where
    cd = CB.cDom (fibcov a) v
    cj = CB.cInj (fibcov a) v

    go : src .pred cd .pred (SIMP .fmor cj .PS._⇒_.func (lift w)) →
         T .pred cd .pred (SIMP .fmor cj .PS._⇒_.func (lift w))
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

    w : RML.Mor (FamF .fobj a) SING
    w = to-sing u ex

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

dist : ∀ {V} {Pp Q S : CS.Predicate V} →
       CS._⊑_ (CS._&&_ Pp (CS._++_ Q S)) (CS._++_ (CS._&&_ Pp Q) (CS._&&_ Pp S))
dist {V} {Pp} {Q} {S} = CPd.&&-++-distrib {V} {Pp} {Q} {S}

dist-⋁ : ∀ {V} {I : Set 0ℓ} {Pp : CS.Predicate V} {Qs : I → CS.Predicate V} →
         CS._⊑_ (CS._&&_ Pp (CS.⋁ I Qs)) (CS.⋁ I (λ i → CS._&&_ Pp (Qs i)))
dist-⋁ = ⊑-trans 𝐂-strongʳ (𝐂-isClosure .IsClosureOp.mono &&-⋁-distrib)

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
  (⊑-trans (𝐂-isClosure .IsClosureOp.mono
             (raw-monic-extract (RCP.in₁ {X} {Y}) in₁-monic))
           (CPm.Predicate.closed Q))

in₂-extract : ∀ {X Y : RML.Obj} {Q : CS.Predicate (G .fobj Y)} →
              CS._⊑_ (CS._[_] (CS._⟨_⟩ Q (G .fmor (RCP.in₂ {X} {Y})))
                              (G .fmor (RCP.in₂ {X} {Y}))) Q
in₂-extract {X} {Y} {Q} =
  ⊑-trans 𝐂-[]⁻¹
  (⊑-trans (𝐂-isClosure .IsClosureOp.mono
             (raw-monic-extract (RCP.in₂ {X} {Y}) in₂-monic))
           (CPm.Predicate.closed Q))

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
Rt-iso {C} {D} h hinv e₁ e₂ = raw-Rt-iso h

Rt-iso⁻ : ∀ {C D : RML.Obj} (h : RML.Mor C D)
          (hinv : ∀ x → RML._⇒_ (D .RML.fam .RML.fm (h .RML.idxf .PS._⇒_.func x))
                                 (C .RML.fam .RML.fm x)) →
          (∀ x → RML._≈_ (RML._∘_ (h .RML.famf ._⇒f_.transf x) (hinv x)) (RML.id _)) →
          (∀ x → RML._≈_ (RML._∘_ (hinv x) (h .RML.famf ._⇒f_.transf x)) (RML.id _)) →
          CS._⊑_ (CS._[_] (Rt D) (G .fmor (RML.Lf-map h))) (Rt C)
Rt-iso⁻ {C} {D} h hinv e₁ e₂ = raw-Rt-iso⁻ h hinv e₂

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
    raw-step t' t = by-fibres go
      where
      SIMP = G .fobj RML.simple[ PS.𝟙 , RML.μObj Q δ₀ .RML.fam .RML.fm t ]

      src : Predicate SIMP
      src = (CPm.Predicate.pred (gpred (fibGl t')) ⟨ G .fmor (Mδ.tree-in Q pQ t') ⟩)
              [ G .fmor (RootedMu.elem-in (RML.μObj Q δ₀) t) ]

      go : ∀ a (x : Setoid.Carrier (SIMP .fobj a)) → src .pred a .pred x →
           ∀ (v : CB.CIx (fibcov a)) →
           tgt t .pred (CB.cDom (fibcov a) v) .pred
             (SIMP .fmor (CB.cInj (fibcov a) v) .PS._⇒_.func x)
      go a (lift w) hyp v = inner (src .pred-mor cj .*⊑* (lift w) hyp)
        where
        cd = CB.cDom (fibcov a) v
        cj = CB.cInj (fibcov a) v

        wv : RML.Mor (FamF .fobj cd)
                     RML.simple[ PS.𝟙 , RML.μObj Q δ₀ .RML.fam .RML.fm t ]
        wv = FD._∘_ w (FamF .fmor cj)

        inner : src .pred cd .pred (SIMP .fmor cj .PS._⇒_.func (lift w)) →
                tgt t .pred cd .pred (SIMP .fmor cj .PS._⇒_.func (lift w))
        inner (lift nn , qn , lift eqn) =
          CPm.Predicate.pred (gpred (fibGl t)) .pred cd .pred-≃ (lift sq)
            (MT.subst-fib Q dc pQ pc {t'} {t} p .RootedMu.mor .gpresv
               .*⊑* cd .*⊑* (lift nn) qn)
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

-- The additive obligations of the fold's lifted nodes. Eliminating an assembled argument gives the
-- assembly of the eliminated payload with the root that argument carried, joined with the support
-- the elimination charges at it, so both branches land in the payload disjunct.
module _ (Γg Xg Yg : RootedMu.Gl.Obj)
         (γ : Setoid.Carrier (RML.idx (gcar Γg)))
         (ι : Setoid.Carrier (RML.idx (gcar Xg)))
         (hs : RML.Mor RML.simple[ PS.𝟙 , RML.prod (gcar Γg .RML.fam .RML.fm γ)
                                                   (gcar Xg .RML.fam .RML.fm ι) ]
                       (gcar Yg))
         (HYP : CS._⊑_ (CS._[_] (gpred (Γg RootedMu.[×] Xg))
                                (G .fmor (RootedMu.elem-in (FDP.prod (gcar Γg) (gcar Xg))
                                                           (γ , ι))))
                       (CS._[_] (gpred Yg) (G .fmor hs)))
         where

  private
    module CME' = CMonEnriched CM'

    Γc = gcar Γg
    Xc = gcar Xg
    Yc = gcar Yg
    Γp = CPm.Predicate.pred (gpred Γg)
    Xp = CPm.Predicate.pred (gpred Xg)
    Yp = CPm.Predicate.pred (gpred Yg)

    esing = RootedMu.elem-in (FDP.prod Γc (RML.Lf Xc)) (γ , ι)
    epair = RootedMu.elem-in (FDP.prod Γc Xc) (γ , ι)
    sur = RootedMu.sing-under-root hs

    payY : Predicate (G .fobj (RML.Lf Yc))
    payY = (Yp [ G .fmor (FDP.p₁ {Yc} {RML.𝟙L}) ]) ⟨ G .fmor (RML.assembleF {Yc}) ⟩

    -- The payload branch, at the element level.
    core : (((Γp [ G .fmor (FDP.p₁ {Γc} {RML.Lf Xc}) ])
              && (((Xp [ G .fmor (FDP.p₁ {Xc} {RML.𝟙L}) ]) ⟨ G .fmor (RML.assembleF {Xc}) ⟩)
                    [ G .fmor (FDP.p₂ {Γc} {RML.Lf Xc}) ]))
             [ G .fmor esing ])
             ⊑ (payY [ G .fmor sur ])
    core .*⊑* a .*⊑* (lift m) (hΓ , (lift n , hX , lift sq)) = lift k , (hY , lift eqk)
      where
      M : ∀ i → _
      M i = m .RML.famf ._⇒f_.transf i

      exι : ∀ i → Setoid._≈_ (RML.idx Xc) (proj₁ (n .RML.idxf .PS._⇒_.func i)) ι
      exι i = sq .RML._≃_.idxf-eq .PS._≃m_.func-eq (Setoid.refl (FamC.Obj.idx a) {i})

      -- The argument transported to the singleton at ι.
      n̂ : RML.Mor (FamF .fobj a)
                  RML.simple[ PS.𝟙 , RML.prod (Xc .RML.fam .RML.fm ι) 𝟙d ]
      n̂ = to-sing n exι

      N̂ : ∀ i → _
      N̂ i = n̂ .RML.famf ._⇒f_.transf i

      -- The context paired with the transported payload, which the hypothesis reads.
      v : RML.Mor (FamF .fobj a)
                  RML.simple[ PS.𝟙 , RML.prod (Γc .RML.fam .RML.fm γ) (Xc .RML.fam .RML.fm ι) ]
      v .RML.idxf = PS.to-𝟙
      v .RML.famf ._⇒f_.transf i =
        RML.pair (RML._∘_ RML.p₁ (M i)) (RML._∘_ RML.p₁ (N̂ i))
      v .RML.famf ._⇒f_.natural p =
        RML.≈-trans (RML.pair-natural _ _ _)
          (RML.≈-trans
            (RML.pair-cong
              (RML.≈-trans (RML.assoc _ _ _)
                (RML.∘-cong RML.≈-refl
                  (RML.≈-trans (m .RML.famf ._⇒f_.natural p) RML.id-left)))
              (RML.≈-trans (RML.assoc _ _ _)
                (RML.∘-cong RML.≈-refl
                  (RML.≈-trans (n̂ .RML.famf ._⇒f_.natural p) RML.id-left))))
            (RML.≈-sym RML.id-left))

      -- The root the assembly carried, joined with the support charged at the payload.
      sup : RML.Mor (FamF .fobj a) RML.𝟙L
      sup .RML.idxf = PS.to-𝟙
      sup .RML.famf ._⇒f_.transf i =
        CME'._+m_ (RML._∘_ RML.spt (RML._∘_ RML.p₁ (N̂ i))) (RML._∘_ RML.p₂ (N̂ i))
      sup .RML.famf ._⇒f_.natural p =
        RML.≈-trans (CME'.comp-bilinear₁ _ _ _)
          (RML.≈-trans
            (CME'.homCM _ _ .CommutativeMonoid.+-cong
              (RML.≈-trans (RML.assoc _ _ _)
                (RML.∘-cong RML.≈-refl
                  (RML.≈-trans (RML.assoc _ _ _)
                    (RML.∘-cong RML.≈-refl
                      (RML.≈-trans (n̂ .RML.famf ._⇒f_.natural p) RML.id-left)))))
              (RML.≈-trans (RML.assoc _ _ _)
                (RML.∘-cong RML.≈-refl
                  (RML.≈-trans (n̂ .RML.famf ._⇒f_.natural p) RML.id-left))))
            (RML.≈-sym RML.id-left))

      k : RML.Mor (FamF .fobj a) (FDP.prod Yc RML.𝟙L)
      k = FDP.pair (FD._∘_ hs v) sup

      -- The hypothesis applies at the pairing of the context with the transported payload.
      hΓv : (Γp [ G .fmor (FDP.p₁ {Γc} {Xc}) ]) .pred a .pred
              (G .fmor epair .transf a .PS._⇒_.func (lift v))
      hΓv = Γp .pred a .pred-≃ (lift sqΓ) hΓ
        where
        sqΓ : FD._≈_ (FD._∘_ FDP.p₁ (FD._∘_ (FD._∘_ esing (FD._∘_ m (FD.id _))) (FD.id _)))
                     (FD._∘_ FDP.p₁ (FD._∘_ (FD._∘_ epair (FD._∘_ v (FD.id _)))
                                                        (FD.id _)))
        sqΓ .RML._≃_.idxf-eq .PS._≃m_.func-eq _ = Setoid.refl (RML.idx Γc)
        sqΓ .RML._≃_.famf-eq ._≃f_.transf-eq {i} =
          RML.≈-trans (RML.∘-cong (Γc .RML.fam .RML.refl*) RML.≈-refl)
          (RML.≈-trans RML.id-left
          (RML.≈-trans (strip-π RML.p₁ (M i))
          (RML.≈-trans (RML.≈-sym (RML.pair-p₁ _ _))
                       (RML.≈-sym (strip-π RML.p₁ (v .RML.famf ._⇒f_.transf i))))))

      hXv : (Xp [ G .fmor (FDP.p₂ {Γc} {Xc}) ]) .pred a .pred
              (G .fmor epair .transf a .PS._⇒_.func (lift v))
      hXv = Xp .pred a .pred-≃ (lift sqX) hX
        where
        sqX : FD._≈_ (FD._∘_ FDP.p₁ (FD._∘_ n (FD.id _)))
                     (FD._∘_ FDP.p₂ (FD._∘_ (FD._∘_ epair (FD._∘_ v (FD.id _)))
                                                        (FD.id _)))
        sqX .RML._≃_.idxf-eq .PS._≃m_.func-eq {i₁} {i₂} _ = exι i₁
        sqX .RML._≃_.famf-eq ._≃f_.transf-eq {i} =
          RML.≈-trans (RML.∘-cong RML.≈-refl (strip-f RML.p₁ (n .RML.famf ._⇒f_.transf i)))
          (RML.≈-trans (RML.≈-sym (RML.assoc _ _ _))
          (RML.≈-trans (RML.∘-cong (RML.≈-sym (RML.pair-p₁ _ _)) RML.≈-refl)
          (RML.≈-trans (RML.assoc _ _ _)
          (RML.≈-trans (RML.≈-sym (RML.pair-p₂ _ _))
                       (RML.≈-sym (strip-π RML.p₂ (v .RML.famf ._⇒f_.transf i)))))))

      hY : Yp .pred a .pred (lift (FD._∘_ FDP.p₁ (FD._∘_ k (FD.id _))))
      hY = Yp .pred a .pred-≃ (lift sqY) (HYP .*⊑* a .*⊑* (lift v) (hΓv , hXv))
        where
        sqY : FD._≈_ (FD._∘_ hs (FD._∘_ v (FD.id _)))
                     (FD._∘_ FDP.p₁ (FD._∘_ k (FD.id _)))
        sqY .RML._≃_.idxf-eq .PS._≃m_.func-eq _ = hs .RML.idxf .PS._⇒_.func-resp-≈ tt
        sqY .RML._≃_.famf-eq ._≃f_.transf-eq {i} =
          RML.≈-trans (RML.∘-cong (Yc .RML.fam .RML.refl*) RML.≈-refl)
          (RML.≈-trans RML.id-left
          (RML.≈-trans (strip-f (hs .RML.famf ._⇒f_.transf (lift ttS))
                                (v .RML.famf ._⇒f_.transf i))
          (RML.≈-trans (RML.≈-sym RML.id-left)
          (RML.≈-trans (RML.≈-sym (RML.pair-p₁ _ _))
                       (RML.≈-sym (strip-f RML.p₁ (k .RML.famf ._⇒f_.transf i)))))))

      eqk : FD._≈_ (FD._∘_ RML.assembleF (FD._∘_ k (FD.id _)))
                   (FD._∘_ sur (FD._∘_ m (FD.id _)))
      eqk .RML._≃_.idxf-eq .PS._≃m_.func-eq _ = hs .RML.idxf .PS._⇒_.func-resp-≈ tt
      eqk .RML._≃_.famf-eq ._≃f_.transf-eq {i} =
        RML.≈-trans (RML.∘-cong (RML.Lf Yc .RML.fam .RML.refl*) RML.≈-refl)
          (RML.≈-trans RML.id-left
            (RML.≈-trans (strip-f (RML.cop RML.inj RML.root) (k .RML.famf ._⇒f_.transf i))
              (RML.≈-trans MAIN
                (RML.≈-sym (strip-f (RML.under-root (hs .RML.famf ._⇒f_.transf (lift ttS)))
                                    (M i))))))
        where
        HYPN : RML._≈_ (RML._∘_ (RML.cop RML.inj RML.root) (N̂ i))
                       (RML._∘_ RML.p₂ (M i))
        HYPN =
          RML.≈-trans (RML.≈-sym (RML.assoc _ _ _))
          (RML.≈-trans
            (RML.∘-cong
              (RML.≈-sym (RML.Lmap-assemble (RML.fam-subst-iso₁ (Xc .RML.fam) (exι i))
                                            (RML.fam-subst-iso₂ (Xc .RML.fam) (exι i))))
              RML.≈-refl)
          (RML.≈-trans (RML.assoc _ _ _)
          (RML.≈-trans
            (RML.≈-sym (RML.∘-cong RML.≈-refl
                         (strip-f (RML.cop RML.inj RML.root)
                                  (n .RML.famf ._⇒f_.transf i))))
          (RML.≈-trans (sq .RML._≃_.famf-eq ._≃f_.transf-eq {i})
                       (strip-π RML.p₂ (M i))))))

        MAIN : RML._≈_ (RML._∘_ (RML.cop RML.inj RML.root)
                          (k .RML.famf ._⇒f_.transf i))
                       (RML._∘_ (RML.under-root (hs .RML.famf ._⇒f_.transf (lift ttS))) (M i))
        MAIN =
          RML.≈-trans
            (RML.∘-cong RML.≈-refl
              (RML.pair-cong (RML.≈-trans RML.id-left RML.≈-refl) RML.≈-refl))
          (RML.≈-trans
            (RML.≈-sym (RML.under-root-pair (hs .RML.famf ._⇒f_.transf (lift ttS))
                          (RML._∘_ RML.p₁ (M i)) (RML._∘_ RML.p₁ (N̂ i))
                          (RML._∘_ RML.p₂ (N̂ i))))
            (RML.∘-cong RML.≈-refl
              (RML.≈-trans
                (RML.pair-cong RML.≈-refl
                  (RML.≈-trans (RML.∘-cong RML.≈-refl (RML.pair-ext (N̂ i))) HYPN))
                (RML.pair-ext (M i)))))

  payload-sing : CS._⊑_
                   (CS._[_] (CS._&&_ (CS._[_] (gpred Γg) (G .fmor (FDP.p₁ {Γc} {RML.Lf Xc})))
                                     (CS._[_] (CS._⟨_⟩ (CS._[_] (gpred Xg)
                                                          (G .fmor (FDP.p₁ {Xc} {RML.𝟙L})))
                                                       (G .fmor (RML.assembleF {Xc})))
                                              (G .fmor (FDP.p₂ {Γc} {RML.Lf Xc}))))
                            (G .fmor esing))
                   (CS._[_] (gpred (RootedMu.Lf-Gl Yg)) (G .fmor sur))
  payload-sing =
    ⊑-trans (push-𝐂 [ G .fmor esing ]m)
    (⊑-trans 𝐂-[]⁻¹
    (⊑-trans (𝐂-isClosure .IsClosureOp.mono
               (⊑-trans core
                        ((⊑-trans (𝐂-isClosure .IsClosureOp.unit)
                                  (++-isJoin .IsJoin.inl)) [ G .fmor sur ]m)))
             𝐂-[]))

  private
    -- The root branch, at the element level and at one root index: the argument is a bare root, so
    -- the eliminated payload is the context against the zero, and the root passes through.
    core-root : RootedMu.Zeroed Xg → (i₀ : Setoid.Carrier (RML.idx Xc)) →
                (((Γp [ G .fmor (FDP.p₁ {Γc} {RML.Lf Xc}) ])
                   && ((TT ⟨ G .fmor (root-mor Xc i₀) ⟩)
                         [ G .fmor (FDP.p₂ {Γc} {RML.Lf Xc}) ]))
                  [ G .fmor esing ])
                  ⊑ (payY [ G .fmor sur ])
    core-root zX i₀ .*⊑* a .*⊑* (lift m) (hΓ , (lift w , _ , lift sq)) =
      lift k , (hY , lift eqk)
      where
      M : ∀ i → _
      M i = m .RML.famf ._⇒f_.transf i

      W : ∀ i → _
      W i = w .RML.famf ._⇒f_.transf i

      -- The context against the zero payload, which the hypothesis reads.
      v₀ : RML.Mor (FamF .fobj a)
                   RML.simple[ PS.𝟙 , RML.prod (Γc .RML.fam .RML.fm γ) (Xc .RML.fam .RML.fm ι) ]
      v₀ .RML.idxf = PS.to-𝟙
      v₀ .RML.famf ._⇒f_.transf i = RML.pair (RML._∘_ RML.p₁ (M i)) CME'.εm
      v₀ .RML.famf ._⇒f_.natural p =
        RML.≈-trans (RML.pair-natural _ _ _)
          (RML.≈-trans
            (RML.pair-cong
              (RML.≈-trans (RML.assoc _ _ _)
                (RML.∘-cong RML.≈-refl
                  (RML.≈-trans (m .RML.famf ._⇒f_.natural p) RML.id-left)))
              (CME'.comp-bilinear-ε₁ _))
            (RML.≈-sym RML.id-left))

      k : RML.Mor (FamF .fobj a) (FDP.prod Yc RML.𝟙L)
      k = FDP.pair (FD._∘_ hs v₀) w

      hΓv : (Γp [ G .fmor (FDP.p₁ {Γc} {Xc}) ]) .pred a .pred
              (G .fmor epair .transf a .PS._⇒_.func (lift v₀))
      hΓv = Γp .pred a .pred-≃ (lift sqΓ) hΓ
        where
        sqΓ : FD._≈_ (FD._∘_ FDP.p₁ (FD._∘_ (FD._∘_ esing (FD._∘_ m (FD.id _))) (FD.id _)))
                     (FD._∘_ FDP.p₁ (FD._∘_ (FD._∘_ epair (FD._∘_ v₀ (FD.id _)))
                                            (FD.id _)))
        sqΓ .RML._≃_.idxf-eq .PS._≃m_.func-eq _ = Setoid.refl (RML.idx Γc)
        sqΓ .RML._≃_.famf-eq ._≃f_.transf-eq {i} =
          RML.≈-trans (RML.∘-cong (Γc .RML.fam .RML.refl*) RML.≈-refl)
          (RML.≈-trans RML.id-left
          (RML.≈-trans (strip-π RML.p₁ (M i))
          (RML.≈-trans (RML.≈-sym (RML.pair-p₁ _ _))
                       (RML.≈-sym (strip-π RML.p₁ (v₀ .RML.famf ._⇒f_.transf i))))))

      hXv : (Xp [ G .fmor (FDP.p₂ {Γc} {Xc}) ]) .pred a .pred
              (G .fmor epair .transf a .PS._⇒_.func (lift v₀))
      hXv = Xp .pred a .pred-≃ (lift sqX)
              (zX {FamF .fobj a} ι .*⊑* a .*⊑* (lift (FD.id _)) tt)
        where
        sqX : FD._≈_ (FD._∘_ (RML.zeroF ι) (FD._∘_ (FD.id _) (FD.id _)))
                     (FD._∘_ FDP.p₂ (FD._∘_ (FD._∘_ epair (FD._∘_ v₀ (FD.id _)))
                                            (FD.id _)))
        sqX .RML._≃_.idxf-eq .PS._≃m_.func-eq _ = Setoid.refl (RML.idx Xc)
        sqX .RML._≃_.famf-eq ._≃f_.transf-eq {i} =
          RML.≈-trans (RML.∘-cong (Xc .RML.fam .RML.refl*) RML.≈-refl)
          (RML.≈-trans (RML.≈-trans RML.id-left RML.id-left)
          (RML.≈-trans (RML.≈-trans (RML.∘-cong RML.≈-refl
                                      (RML.≈-trans RML.id-left RML.id-left)) RML.id-right)
          (RML.≈-trans (RML.≈-sym (RML.pair-p₂ _ _))
                       (RML.≈-sym (strip-π RML.p₂ (v₀ .RML.famf ._⇒f_.transf i))))))

      hY : Yp .pred a .pred (lift (FD._∘_ FDP.p₁ (FD._∘_ k (FD.id _))))
      hY = Yp .pred a .pred-≃ (lift sqY) (HYP .*⊑* a .*⊑* (lift v₀) (hΓv , hXv))
        where
        sqY : FD._≈_ (FD._∘_ hs (FD._∘_ v₀ (FD.id _)))
                     (FD._∘_ FDP.p₁ (FD._∘_ k (FD.id _)))
        sqY .RML._≃_.idxf-eq .PS._≃m_.func-eq _ = hs .RML.idxf .PS._⇒_.func-resp-≈ tt
        sqY .RML._≃_.famf-eq ._≃f_.transf-eq {i} =
          RML.≈-trans (RML.∘-cong (Yc .RML.fam .RML.refl*) RML.≈-refl)
          (RML.≈-trans RML.id-left
          (RML.≈-trans (strip-f (hs .RML.famf ._⇒f_.transf (lift ttS))
                                (v₀ .RML.famf ._⇒f_.transf i))
          (RML.≈-trans (RML.≈-sym RML.id-left)
          (RML.≈-trans (RML.≈-sym (RML.pair-p₁ _ _))
                       (RML.≈-sym (strip-f RML.p₁ (k .RML.famf ._⇒f_.transf i)))))))

      eqk : FD._≈_ (FD._∘_ RML.assembleF (FD._∘_ k (FD.id _)))
                   (FD._∘_ sur (FD._∘_ m (FD.id _)))
      eqk .RML._≃_.idxf-eq .PS._≃m_.func-eq _ = hs .RML.idxf .PS._⇒_.func-resp-≈ tt
      eqk .RML._≃_.famf-eq ._≃f_.transf-eq {i} =
        RML.≈-trans (RML.∘-cong (RML.Lf Yc .RML.fam .RML.refl*) RML.≈-refl)
          (RML.≈-trans RML.id-left
            (RML.≈-trans (strip-f (RML.cop RML.inj RML.root) (k .RML.famf ._⇒f_.transf i))
              (RML.≈-trans MAIN
                (RML.≈-sym (strip-f (RML.under-root (hs .RML.famf ._⇒f_.transf (lift ttS)))
                                    (M i))))))
        where
        -- The argument is the root the factorisation exhibits.
        ROOT : RML._≈_ (RML._∘_ RML.root (W i)) (RML._∘_ RML.p₂ (M i))
        ROOT =
          RML.≈-trans (RML.≈-sym (RML.∘-cong (RML.Lmap-root _) RML.≈-refl))
          (RML.≈-trans (RML.assoc _ _ _)
          (RML.≈-trans (RML.≈-sym (RML.∘-cong RML.≈-refl (strip-f RML.root (W i))))
          (RML.≈-trans (sq .RML._≃_.famf-eq ._≃f_.transf-eq {i})
                       (strip-π RML.p₂ (M i)))))

        ZERO : RML._≈_ (RML._∘_ (RML.cop RML.inj RML.root) (RML.pair CME'.εm (W i)))
                       (RML._∘_ RML.p₂ (M i))
        ZERO =
          RML.≈-trans (RML.cop-pair _ _ _ _)
          (RML.≈-trans (CME'.homCM _ _ .CommutativeMonoid.+-cong
                         (CME'.comp-bilinear-ε₂ _) RML.≈-refl)
          (RML.≈-trans (CME'.homCM _ _ .CommutativeMonoid.+-lunit) ROOT))

        MAIN : RML._≈_ (RML._∘_ (RML.cop RML.inj RML.root) (k .RML.famf ._⇒f_.transf i))
                       (RML._∘_ (RML.under-root (hs .RML.famf ._⇒f_.transf (lift ttS))) (M i))
        MAIN =
          RML.≈-trans
            (RML.∘-cong RML.≈-refl
              (RML.pair-cong RML.id-left
                (RML.≈-sym
                  (RML.≈-trans (CME'.homCM _ _ .CommutativeMonoid.+-cong
                                 (CME'.comp-bilinear-ε₂ _) RML.≈-refl)
                               (CME'.homCM _ _ .CommutativeMonoid.+-lunit)))))
          (RML.≈-trans
            (RML.≈-sym (RML.under-root-pair (hs .RML.famf ._⇒f_.transf (lift ttS))
                          (RML._∘_ RML.p₁ (M i)) CME'.εm (W i)))
            (RML.∘-cong RML.≈-refl
              (RML.≈-trans (RML.pair-cong RML.≈-refl ZERO) (RML.pair-ext (M i)))))

  root-sing : RootedMu.Zeroed Xg →
              CS._⊑_
                (CS._[_] (CS._&&_ (CS._[_] (gpred Γg) (G .fmor (FDP.p₁ {Γc} {RML.Lf Xc})))
                                  (CS._[_] (Rt Xc) (G .fmor (FDP.p₂ {Γc} {RML.Lf Xc}))))
                         (G .fmor esing))
                (CS._[_] (gpred (RootedMu.Lf-Gl Yg)) (G .fmor sur))
  root-sing zX =
    ⊑-trans (push-𝐂 [ G .fmor esing ]m)
    (⊑-trans 𝐂-[]⁻¹
    (⊑-trans (𝐂-isClosure .IsClosureOp.mono inner)
    (⊑-trans (𝐂-isClosure .IsClosureOp.closed) 𝐂-[])))
    where
    A = Γp [ G .fmor (FDP.p₁ {Γc} {RML.Lf Xc}) ]

    B : Setoid.Carrier (RML.idx Xc) → Predicate (G .fobj (RML.Lf Xc))
    B i₀ = TT ⟨ G .fmor (root-mor Xc i₀) ⟩

    into-target : (payY [ G .fmor sur ])
                    ⊑ ((𝐂 payY ++ CPm.Predicate.pred (Rt Yc)) [ G .fmor sur ])
    into-target =
      (⊑-trans (𝐂-isClosure .IsClosureOp.unit) (++-isJoin .IsJoin.inl)) [ G .fmor sur ]m

    perI : ∀ i₀ → (((A && (B i₀ [ G .fmor (FDP.p₂ {Γc} {RML.Lf Xc}) ])) [ G .fmor esing ]))
                    ⊑ 𝐂 ((𝐂 payY ++ CPm.Predicate.pred (Rt Yc)) [ G .fmor sur ])
    perI i₀ =
      ⊑-trans (core-root zX i₀)
              (⊑-trans into-target (𝐂-isClosure .IsClosureOp.unit))

    inner : ((A && ((⋁ (Setoid.Carrier (RML.idx Xc)) B)
                      [ G .fmor (FDP.p₂ {Γc} {RML.Lf Xc}) ])) [ G .fmor esing ])
              ⊑ 𝐂 ((𝐂 payY ++ CPm.Predicate.pred (Rt Yc)) [ G .fmor sur ])
    inner =
      ⊑-trans ((⊑-trans (IsMeet.mono &&-isMeet (⊑-isPreorder .IsPreorder.refl) []-⋁)
                        &&-⋁-distrib)
                 [ G .fmor esing ]m)
      (⊑-trans []-⋁ (IsBigJoin.least ⋁-isJoin _ _ _ perI))

-- Every obligation of the glued rooted μ-types, at the family-level nerve.
private
  module Ob = RootedMu.GlMuObligations

obligations : RootedMu.GlMuObligations
obligations .Ob.Rt-iso {C} {D} = Rt-iso {C} {D}
obligations .Ob.Rt-iso⁻ {C} {D} = Rt-iso⁻ {C} {D}
obligations .Ob.in₁-extract {X} {Y} {Q} = in₁-extract {X} {Y} {Q}
obligations .Ob.in₂-extract {X} {Y} {Q} = in₂-extract {X} {Y} {Q}
obligations .Ob.disjoint₁ {X} {Y} {Q} x {S} = disjoint₁ {X} {Y} {Q} x {S}
obligations .Ob.disjoint₂ {X} {Y} {Q} y {S} = disjoint₂ {X} {Y} {Q} y {S}
obligations .Ob.BC-assemble {C} {Qp} x = BC-assemble {C} {Qp} x
obligations .Ob.sing-extract = sing-extract
obligations .Ob.sing-split {X} {Q} = sing-split {X} {Q}
obligations .Ob.payload-sing = payload-sing
obligations .Ob.root-sing = root-sing
obligations .Ob.dist {V} {Pp} {Q} {S} = dist {V} {Pp} {Q} {S}
obligations .Ob.dist-⋁ {V} {I} {Pp} {Qs} = dist-⋁ {V} {I} {Pp} {Qs}
obligations .Ob.frob {V} {V'} {Pp} {Q} {α} = frob {V} {V'} {Pp} {Q} {α}
obligations .Ob.BC {W} {U} {V} h {Q} = BC {W} {U} {V} h {Q}

-- The decorated μ-carrier with its algebra map and catamorphism, at every polynomial and
-- environment.
module RootedMuGl = RootedMu.GlMu obligations
