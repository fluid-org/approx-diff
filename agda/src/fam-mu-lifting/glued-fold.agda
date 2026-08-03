{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- The glued catamorphism: an algebra that preserves the glued interpretation
-- folds a decorated μ-carrier into a closed target. Every lifted node of the
-- fold is an elimination at the root constant, so the node cases route
-- through the glued eliminator; the additive obligations (absorbing the root
-- the payload injection creates, and the image of a bare root) are instance
-- parameters, quantified over the recursive morphism.
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
import fam-mu-lifting.glued-in-map

module fam-mu-lifting.glued-fold {o m e} {𝒞 : Category o m e}
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

open fam-mu-lifting.glued-in-map T CM BP Lft 𝒫 𝒫P system G Rt Cl public

open R hiding (fobj)
open Gl.Obj
open Gl._=>_
open ClosureOp Cl

private
  module 𝒫C' = Category 𝒫

-- Extend a predicate assignment with a predicate for the fresh variable.
extend-pred : ∀ {k} (δ₀ : Fin k → Obj) (δP₀ : ∀ i → Predicate (G .fobj (δ₀ i)))
              (A : Obj) (Ap : Predicate (G .fobj A)) →
              ∀ i → Predicate (G .fobj (extend δ₀ A i))
extend-pred δ₀ δP₀ A Ap Fin.zero    = Ap
extend-pred δ₀ δP₀ A Ap (Fin.suc i) = δP₀ i

-- Transport of a singleton morphism across the lifting: the context-paired
-- fibre map passes under the root.
sing-under-root : ∀ {Gf Xf : obj} {Y : Obj}
                  (hs : Mor simple[ PS.𝟙 , prod Gf Xf ] Y) →
                  Mor simple[ PS.𝟙 , prod Gf (L Xf) ] (Lf Y)
sing-under-root hs .idxf = hs .idxf
sing-under-root hs .famf ._⇒f_.transf t = under-root (hs .famf ._⇒f_.transf t)
sing-under-root {Y = Y} hs .famf ._⇒f_.natural {t₁} {t₂} e =
  ≈-trans id-right
    (≈-sym (≈-trans (under-root-post
                      (fam-subst-iso₁ (Y .fam) (hs .idxf .PS._⇒_.func-resp-≈ e))
                      (fam-subst-iso₂ (Y .fam) (hs .idxf .PS._⇒_.func-resp-≈ e))
                      (hs .famf ._⇒f_.transf t₁))
             (under-root-cong
               (≈-trans (≈-sym (hs .famf ._⇒f_.natural e)) id-right))))

-- The glued fold, at a fixed μ-polynomial, environment, glued context and
-- glued target with a closed predicate. The additive instance obligations
-- are quantified over the recursive morphism and its preservation.
module GlFold {n} (P : Poly (suc n)) (pP : PolyPred P)
    (δ : Fin n → Obj) (δP : ∀ i → Predicate (G .fobj (δ i)))
    (Γg Ag : Gl.Obj)
    (alg : Mor (Fam𝒞-P.prod (Γg .carrier) (R.fobj μObj P (extend δ (Ag .carrier))))
               (Ag .carrier))
    (payload-sing : ∀ (Xg Yg : Gl.Obj) (γ : Γg .carrier .idx .Carrier)
                    (ι : Xg .carrier .idx .Carrier)
                    (hs : Mor simple[ PS.𝟙 , prod (Γg .carrier .fam .fm γ)
                                              (Xg .carrier .fam .fm ι) ]
                              (Yg .carrier)) →
                    (((Γg [×] Xg) .pred
                        [ G .fmor (elem-in (Fam𝒞-P.prod (Γg .carrier) (Xg .carrier))
                                           (γ , ι)) ])
                      ⊑ (Yg .pred [ G .fmor hs ])) →
                    ((((Γg .pred [ G .fmor Fam𝒞-P.p₁ ])
                        && ((Xg .pred ⟨ G .fmor (injF {Xg .carrier}) ⟩)
                              [ G .fmor Fam𝒞-P.p₂ ]))
                        [ G .fmor (elem-in (Fam𝒞-P.prod (Γg .carrier) (Lf (Xg .carrier)))
                                           (γ , ι)) ])
                      ⊑ (Lf-Gl Yg .pred [ G .fmor (sing-under-root hs) ])))
    (root-sing : ∀ (Xg Yg : Gl.Obj) (γ : Γg .carrier .idx .Carrier)
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
                   ⊑ (Lf-Gl Yg .pred [ G .fmor (sing-under-root hs) ])))
    (sing-split : ∀ {X : Obj} {Q : Predicate (G .fobj X)} →
                  Q ⊑ 𝐂 (⋁ (X .idx .Carrier)
                          (λ x → (Q [ G .fmor (elem-in X x) ]) ⟨ G .fmor (elem-in X x) ⟩)))
    (dist : ∀ {V} {Pp Q S : Predicate V} → (Pp && (Q ++ S)) ⊑ ((Pp && Q) ++ (Pp && S)))
    (dist-⋁ : ∀ {V} {I : Set 0ℓ} {Pp : Predicate V} {Qs : I → Predicate V} →
              (Pp && ⋁ I Qs) ⊑ ⋁ I (λ i → Pp && Qs i))
    (frob : ∀ {V V'} {Pp : Predicate V'} {Q : Predicate V} {α : V 𝒫C'.⇒ V'} →
            (Pp && (Q ⟨ α ⟩)) ⊑ (((Pp [ α ]) && Q) ⟨ α ⟩))
    (BC : ∀ {W U V : Obj} (h : Mor U V) {Q : Predicate (G .fobj U)} →
          ((Q ⟨ G .fmor h ⟩) [ G .fmor (Fam𝒞-P.p₂ {W} {V}) ])
            ⊑ ((Q [ G .fmor (Fam𝒞-P.p₂ {W} {U}) ])
                 ⟨ G .fmor (Fam𝒞-P.pair Fam𝒞-P.p₁ (Fam𝒞._∘_ h Fam𝒞-P.p₂)) ⟩))
    (A-closed : 𝐂 (Ag .pred) ⊑ Ag .pred)
    where

  private
    module Mδ = MuPred δ δP
    module Tδ = Tree δ
    module FD = FoldDef {n} {Γg .carrier} {Ag .carrier} {P} {δ} alg

  δPA⁺ : ∀ i → Predicate (G .fobj (extend δ (Ag .carrier) i))
  δPA⁺ = extend-pred δ δP (Ag .carrier) (Ag .pred)

  private
    dP : ∀ i → Tδ.DecoAssign (Sh.η₀ ∣ P ∣ i)
    dP = Tδ.deco-ext P (λ i → lift tt)

    pdP : ∀ i → Mδ.DecoAssignPred (Sh.η₀ ∣ P ∣ i) (dP i)
    pdP = Mδ.deco-ext-pred P pP (λ i → lift tt)

  -- The fold packaged as a morphism out of each fibre's glued carrier, at a
  -- fixed shape or tree, through the carrier inclusion.
  fold-shape-mor : ∀ (Q : Poly (suc n)) (pQ : PolyPred Q)
                   (x : Tδ.⟦ ∣ Q ∣ ⟧shape (Sh.η₀ ∣ P ∣)) →
                   Mor (Fam𝒞-P.prod (Γg .carrier) (Mδ.fib-shape-Gl Q dP pQ pdP x .carrier))
                       (R.fobj μObj Q (extend δ (Ag .carrier)))
  fold-shape-mor Q pQ x .idxf .PS._⇒_.func (γ , ι) = FD.fold-shape-idx Q γ x
  fold-shape-mor Q pQ x .idxf .PS._⇒_.func-resp-≈ (γ≈ , ι≈) =
    FD.fold-shape-idx-resp Q γ≈ (Tδ.shape≈-refl ∣ Q ∣ (Sh.η₀ ∣ P ∣) x)
  fold-shape-mor Q pQ x .famf ._⇒f_.transf (γ , ι) =
    FD.fold-shape-fam Q γ x ∘ prod-m (id _) (Mδ.in-shape Q dP pQ pdP x ι)
  fold-shape-mor Q pQ x .famf ._⇒f_.natural {γ₁ , ι₁} {γ₂ , ι₂} (γ≈ , ι≈) =
    ≈-trans (assoc _ _ _)
    (≈-trans (∘-cong ≈-refl (≈-sym (prod-m-comp _ _ _ _)))
    (≈-trans (∘-cong ≈-refl
               (prod-m-cong id-left (Mδ.in-shape-natural Q dP pQ pdP x ι≈)))
    (≈-trans (∘-cong ≈-refl
               (prod-m-cong (≈-sym id-right)
                 (≈-sym (≈-trans (∘-cong (Tδ.fib-shape-refl* Q dP x) ≈-refl) id-left))))
    (≈-trans (∘-cong ≈-refl (prod-m-comp _ _ _ _))
    (≈-trans (≈-sym (assoc _ _ _))
    (≈-trans (∘-cong (FD.fold-shape-fam-natural Q γ≈
                       (Tδ.shape≈-refl ∣ Q ∣ (Sh.η₀ ∣ P ∣) x)) ≈-refl)
             (assoc _ _ _)))))))

  fold-mor : ∀ (t : Tδ.W ∣ P ∣ (λ i → inj₁ i)) →
             Mor (Fam𝒞-P.prod (Γg .carrier)
                    (Mδ.fib-Gl P (λ i → lift tt) pP (λ i → lift tt) t .carrier))
                 (Ag .carrier)
  fold-mor t .idxf .PS._⇒_.func (γ , ι) = FD.fold-idx γ t
  fold-mor t .idxf .PS._⇒_.func-resp-≈ {γ₁ , ι₁} {γ₂ , ι₂} (γ≈ , ι≈) =
    FD.fold-idx-resp γ≈ {t} {t} (Tδ.W-≈-refl t)
  fold-mor t .famf ._⇒f_.transf (γ , ι) =
    FD.fold-fam γ t ∘ prod-m (id _) (Mδ.in-fib P (λ i → lift tt) pP (λ i → lift tt) t ι)
  fold-mor t .famf ._⇒f_.natural {γ₁ , ι₁} {γ₂ , ι₂} (γ≈ , ι≈) =
    ≈-trans (assoc _ _ _)
    (≈-trans (∘-cong ≈-refl (≈-sym (prod-m-comp _ _ _ _)))
    (≈-trans (∘-cong ≈-refl
               (prod-m-cong id-left
                 (Mδ.in-fib-natural P (λ i → lift tt) pP (λ i → lift tt) t ι≈)))
    (≈-trans (∘-cong ≈-refl
               (prod-m-cong (≈-sym id-right)
                 (≈-sym (≈-trans (∘-cong (Tδ.fib-refl* P (λ i → lift tt) t) ≈-refl) id-left))))
    (≈-trans (∘-cong ≈-refl (prod-m-comp _ _ _ _))
    (≈-trans (≈-sym (assoc _ _ _))
    (≈-trans (∘-cong (FD.fold-fam-natural γ≈ {t} {t} (Tδ.W-≈-refl t)) ≈-refl)
             (assoc _ _ _)))))))

  private
    δA' : Fin (suc n) → Obj
    δA' = extend δ (Ag .carrier)

    module MA' = MuPred δA' δPA⁺

    Γc : Obj
    Γc = Γg .carrier

    prodC : Obj → Obj
    prodC Z = Fam𝒞-P.prod Γc Z

    ℓF : Level
    ℓF = o ⊔ m ⊔ e ⊔ lsuc 0ℓ ⊔ lsuc o₂ ⊔ lsuc m₂ ⊔ lsuc e₂

  -- Predicate decorations tracking the fold's reindex morphism.
  data PredF : ∀ {k} {ρ : Fin k → Fin n ⊎ Sort n}
               {ρ' : Fin k → Fin (suc n) ⊎ Sort (suc n)}
               {d : ∀ v → Tδ.DecoAssign (ρ v)} {d' : ∀ v → FD.TA'.DecoAssign (ρ' v)} →
               FD.FMor ρ ρ' d d' →
               (∀ v → Mδ.DecoAssignPred (ρ v) (d v)) →
               (∀ v → MA'.DecoAssignPred (ρ' v) (d' v)) → Set ℓF where
    pfbase : PredF FD.fbase pdP (λ v → lift tt)
    pfbind : ∀ {k} {ρ : Fin k → Fin n ⊎ Sort n}
             {ρ' : Fin k → Fin (suc n) ⊎ Sort (suc n)}
             {d : ∀ v → Tδ.DecoAssign (ρ v)} {d' : ∀ v → FD.TA'.DecoAssign (ρ' v)}
             {fm : FD.FMor ρ ρ' d d'} {pd pd'}
             (Q : Poly (suc k)) (pQ : PolyPred Q) →
             PredF fm pd pd' →
             PredF (FD.fbind Q fm) (Mδ.deco-ext-pred Q pQ pd) (MA'.deco-ext-pred Q pQ pd')

  private
    -- Reindexing distributes over the meet.
    []-&&-dist : ∀ {V V'} {A B : Predicate V'} {f : V 𝒫C'.⇒ V'} →
                 ((A && B) [ f ]) ⊑ ((A [ f ]) && (B [ f ]))
    []-&&-dist {f = f} =
      &&-isMeet .IsMeet.⟨_,_⟩ ((&&-isMeet .IsMeet.π₁) [ f ]m)
                              ((&&-isMeet .IsMeet.π₂) [ f ]m)

    -- The node step at a lifted glued object, per singleton: split into the
    -- payload and root branches and discharge each by its obligation.
    node-sing : ∀ (Xg Yg : Gl.Obj) (γ : Γc .idx .Carrier) (ι : Xg .carrier .idx .Carrier)
                (hs : Mor simple[ PS.𝟙 , prod (Γc .fam .fm γ) (Xg .carrier .fam .fm ι) ]
                          (Yg .carrier)) →
                (((Γg [×] Xg) .pred [ G .fmor (elem-in (prodC (Xg .carrier)) (γ , ι)) ])
                  ⊑ (Yg .pred [ G .fmor hs ])) →
                (((Γg [×] Lf-Gl Xg) .pred
                    [ G .fmor (elem-in (prodC (Lf (Xg .carrier))) (γ , ι)) ])
                  ⊑ (Lf-Gl Yg .pred [ G .fmor (sing-under-root hs) ]))
    node-sing Xg Yg γ ι hs HYP =
      ⊑-trans ((⊑-trans (IsMeet.mono &&-isMeet (IsPreorder.refl ⊑-isPreorder) []-++) dist)
                 [ G .fmor (elem-in (prodC (Lf (Xg .carrier))) (γ , ι)) ]m)
      (⊑-trans []-++
               (++-isJoin .IsJoin.[_,_] (payload-sing Xg Yg γ ι hs HYP)
                                        (root-sing Xg Yg γ ι hs HYP)))

    -- At the recursion slot the packaged shape morphism is the tree fold.
    vz-mor : ∀ (pQ : PolyPred {suc n} (var Fin.zero)) (t' : Tδ.W ∣ P ∣ (λ i → inj₁ i)) →
             Fam𝒞._≈_ (fold-shape-mor (var Fin.zero) pQ t') (fold-mor t')
    vz-mor pQ t' ._≃_.idxf-eq .PS._≃m_.func-eq (γ≈ , ι≈) =
      FD.fold-idx-resp γ≈ {t'} {t'} (Tδ.W-≈-refl t')
    vz-mor pQ t' ._≃_.famf-eq .indexed-family._≃f_.transf-eq =
      ≈-trans (∘-cong (Ag .carrier .fam .refl*) ≈-refl) id-left
