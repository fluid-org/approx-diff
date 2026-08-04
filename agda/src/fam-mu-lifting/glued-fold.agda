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

private
  module GIM = fam-mu-lifting.glued-in-map T CM BP Lft 𝒫 𝒫P system G Rt Cl

open GIM
open GIM public
  using (module Gl; module GlInMap; module MuPred; Lf-Gl; Zeroed; _[×]_; mor; elem-in;
         PolyPred; glue; fobj-Gl; sing-assemble; sing-under-root)

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
                        && (((Xg .pred [ G .fmor (Fam𝒞-P.p₁ {Xg .carrier} {𝟙L}) ])
                               ⟨ G .fmor (assembleF {Xg .carrier}) ⟩)
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
                 Zeroed Xg →
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
    (δZ : ∀ i → Zeroed (glue (δ i) (δP i)))
    where

  private
    module Mδ = MuPred δ δP
    module MZ = Mδ.MuZero δZ
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
                Zeroed Xg →
                (((Γg [×] Lf-Gl Xg) .pred
                    [ G .fmor (elem-in (prodC (Lf (Xg .carrier))) (γ , ι)) ])
                  ⊑ (Lf-Gl Yg .pred [ G .fmor (sing-under-root hs) ]))
    node-sing Xg Yg γ ι hs HYP zX =
      ⊑-trans ((⊑-trans (IsMeet.mono &&-isMeet (IsPreorder.refl ⊑-isPreorder) []-++) dist)
                 [ G .fmor (elem-in (prodC (Lf (Xg .carrier))) (γ , ι)) ]m)
      (⊑-trans []-++
               (++-isJoin .IsJoin.[_,_] (payload-sing Xg Yg γ ι hs HYP)
                                        (root-sing Xg Yg γ ι hs HYP zX)))

    -- At the recursion slot the packaged shape morphism is the tree fold.
    vz-mor : ∀ (pQ : PolyPred {suc n} (var Fin.zero)) (t' : Tδ.W ∣ P ∣ (λ i → inj₁ i)) →
             Fam𝒞._≈_ (fold-shape-mor (var Fin.zero) pQ t') (fold-mor t')
    vz-mor pQ t' ._≃_.idxf-eq .PS._≃m_.func-eq (γ≈ , ι≈) =
      FD.fold-idx-resp γ≈ {t'} {t'} (Tδ.W-≈-refl t')
    vz-mor pQ t' ._≃_.famf-eq .indexed-family._≃f_.transf-eq =
      ≈-trans (∘-cong (Ag .carrier .fam .refl*) ≈-refl) id-left

    -- The strong product action fuses with a payload-only reindexing.
    spm-fusion : ∀ {w x₁ x₂ y₁ y₂ x₁' x₂'} (a : prod w x₁ ⇒ y₁) (b : prod w x₂ ⇒ y₂)
                 (c : x₁' ⇒ x₁) (d : x₂' ⇒ x₂) →
                 (strong-prod-m a b ∘ prod-m (id _) (prod-m c d))
                   ≈ strong-prod-m (a ∘ prod-m (id _) c) (b ∘ prod-m (id _) d)
    spm-fusion a b c d =
      ≈-trans (pair-natural _ _ _)
      (≈-trans (pair-cong (≈-trans (assoc _ _ _) (∘-cong ≈-refl SP1L))
                          (≈-trans (assoc _ _ _) (∘-cong ≈-refl SP2L)))
      (≈-sym (pair-cong (≈-trans (assoc _ _ _) (∘-cong ≈-refl SP1R))
                        (≈-trans (assoc _ _ _) (∘-cong ≈-refl SP2R)))))
      where
        SP1L : (strong-p₁ ∘ prod-m (id _) (prod-m c d)) ≈ pair p₁ (c ∘ (p₁ ∘ p₂))
        SP1L =
          ≈-trans (pair-natural _ _ _)
          (pair-cong (≈-trans (pair-p₁ _ _) id-left)
            (≈-trans (assoc _ _ _)
            (≈-trans (∘-cong ≈-refl (pair-p₂ _ _))
            (≈-trans (≈-sym (assoc _ _ _))
            (≈-trans (∘-cong (pair-p₁ _ _) ≈-refl) (assoc _ _ _))))))
        SP2L : (strong-p₂ ∘ prod-m (id _) (prod-m c d)) ≈ pair p₁ (d ∘ (p₂ ∘ p₂))
        SP2L =
          ≈-trans (pair-natural _ _ _)
          (pair-cong (≈-trans (pair-p₁ _ _) id-left)
            (≈-trans (assoc _ _ _)
            (≈-trans (∘-cong ≈-refl (pair-p₂ _ _))
            (≈-trans (≈-sym (assoc _ _ _))
            (≈-trans (∘-cong (pair-p₂ _ _) ≈-refl) (assoc _ _ _))))))
        SP1R : (prod-m (id _) c ∘ strong-p₁) ≈ pair p₁ (c ∘ (p₁ ∘ p₂))
        SP1R =
          ≈-trans (pair-natural _ _ _)
          (pair-cong (≈-trans (∘-cong id-left ≈-refl) (pair-p₁ _ _))
                     (≈-trans (assoc _ _ _) (∘-cong ≈-refl (pair-p₂ _ _))))
        SP2R : (prod-m (id _) d ∘ strong-p₂) ≈ pair p₁ (d ∘ (p₂ ∘ p₂))
        SP2R =
          ≈-trans (pair-natural _ _ _)
          (pair-cong (≈-trans (∘-cong id-left ≈-refl) (pair-p₁ _ _))
                     (≈-trans (assoc _ _ _) (∘-cong ≈-refl (pair-p₂ _ _))))

    -- Projecting a strong singleton onto one component of a glued product.
    sing-strong-proj₁ : ∀ (X Y : Gl.Obj) (γ : Γc .idx .Carrier)
      (ι₁ : X .carrier .idx .Carrier) (ι₂ : Y .carrier .idx .Carrier) →
      (((Γg [×] (X [×] Y)) .pred)
         [ G .fmor (elem-in (prodC (Fam𝒞-P.prod (X .carrier) (Y .carrier)))
                            (γ , (ι₁ , ι₂))) ])
      ⊑ (((Γg [×] X) .pred)
           [ G .fmor (Fam𝒞._∘_ (elem-in (prodC (X .carrier)) (γ , ι₁))
                               simplef[ PS.idS PS.𝟙 , prod-m (id _) p₁ ]) ])
    sing-strong-proj₁ X Y γ ι₁ ι₂ =
      ⊑-trans []-&&-dist
      (⊑-trans (&&-isMeet .IsMeet.⟨_,_⟩
                 (⊑-trans (&&-isMeet .IsMeet.π₁) legΓ)
                 (⊑-trans (&&-isMeet .IsMeet.π₂) legX))
               []-&&)
      where
        e× = elem-in (prodC (Fam𝒞-P.prod (X .carrier) (Y .carrier))) (γ , (ι₁ , ι₂))
        cmp = Fam𝒞._∘_ (elem-in (prodC (X .carrier)) (γ , ι₁))
                       simplef[ PS.idS PS.𝟙 , prod-m (id _) p₁ ]
        sqΓ : Fam𝒞._≈_ (Fam𝒞._∘_ Fam𝒞-P.p₁ e×) (Fam𝒞._∘_ Fam𝒞-P.p₁ cmp)
        sqΓ ._≃_.idxf-eq .PS._≃m_.func-eq _ = Γc .idx .isEquivalence .refl
        sqΓ ._≃_.famf-eq .indexed-family._≃f_.transf-eq =
          ≈-trans (∘-cong (Γc .fam .refl*) (≈-trans id-left id-right))
          (≈-trans id-left
          (≈-sym (≈-trans id-left
                 (≈-trans (∘-cong ≈-refl (≈-trans id-left id-left))
                          (≈-trans (pair-p₁ _ _) id-left)))))
        sqX : Fam𝒞._≈_ (Fam𝒞._∘_ (Fam𝒞-P.p₁ {X .carrier} {Y .carrier})
                                 (Fam𝒞._∘_ Fam𝒞-P.p₂ e×))
                       (Fam𝒞._∘_ (Fam𝒞-P.p₂ {Γc} {X .carrier}) cmp)
        sqX ._≃_.idxf-eq .PS._≃m_.func-eq _ = X .carrier .idx .isEquivalence .refl
        sqX ._≃_.famf-eq .indexed-family._≃f_.transf-eq =
          ≈-trans (∘-cong (X .carrier .fam .refl*)
                          (≈-trans id-left (∘-cong ≈-refl (≈-trans id-left id-right))))
          (≈-trans id-left
          (≈-sym (≈-trans id-left
                 (≈-trans (∘-cong ≈-refl (≈-trans id-left id-left))
                          (pair-p₂ _ _)))))
        legΓ : ((Γg .pred [ G .fmor Fam𝒞-P.p₁ ]) [ G .fmor e× ])
               ⊑ ((Γg .pred [ G .fmor Fam𝒞-P.p₁ ]) [ G .fmor cmp ])
        legΓ =
          ⊑-trans ([]-comp _ _)
          (⊑-trans ([]-cong (𝒫C'.≈-sym (G .fmor-comp _ _)))
          (⊑-trans ([]-cong (G .fmor-cong sqΓ))
          (⊑-trans ([]-cong (G .fmor-comp _ _)) ([]-comp⁻¹ _ _))))
        legX : ((((X .pred [ G .fmor Fam𝒞-P.p₁ ]) && (Y .pred [ G .fmor Fam𝒞-P.p₂ ]))
                   [ G .fmor Fam𝒞-P.p₂ ]) [ G .fmor e× ])
               ⊑ ((X .pred [ G .fmor Fam𝒞-P.p₂ ]) [ G .fmor cmp ])
        legX =
          ⊑-trans ([]-comp _ _)
          (⊑-trans ([]-cong (𝒫C'.≈-sym (G .fmor-comp _ _)))
          (⊑-trans []-&&-dist
          (⊑-trans (&&-isMeet .IsMeet.π₁)
          (⊑-trans ([]-comp _ _)
          (⊑-trans ([]-cong (𝒫C'.≈-sym (G .fmor-comp _ _)))
          (⊑-trans ([]-cong (G .fmor-cong sqX))
          (⊑-trans ([]-cong (G .fmor-comp _ _)) ([]-comp⁻¹ _ _))))))))

    sing-strong-proj₂ : ∀ (X Y : Gl.Obj) (γ : Γc .idx .Carrier)
      (ι₁ : X .carrier .idx .Carrier) (ι₂ : Y .carrier .idx .Carrier) →
      (((Γg [×] (X [×] Y)) .pred)
         [ G .fmor (elem-in (prodC (Fam𝒞-P.prod (X .carrier) (Y .carrier)))
                            (γ , (ι₁ , ι₂))) ])
      ⊑ (((Γg [×] Y) .pred)
           [ G .fmor (Fam𝒞._∘_ (elem-in (prodC (Y .carrier)) (γ , ι₂))
                               simplef[ PS.idS PS.𝟙 , prod-m (id _) p₂ ]) ])
    sing-strong-proj₂ X Y γ ι₁ ι₂ =
      ⊑-trans []-&&-dist
      (⊑-trans (&&-isMeet .IsMeet.⟨_,_⟩
                 (⊑-trans (&&-isMeet .IsMeet.π₁) legΓ)
                 (⊑-trans (&&-isMeet .IsMeet.π₂) legY))
               []-&&)
      where
        e× = elem-in (prodC (Fam𝒞-P.prod (X .carrier) (Y .carrier))) (γ , (ι₁ , ι₂))
        cmp = Fam𝒞._∘_ (elem-in (prodC (Y .carrier)) (γ , ι₂))
                       simplef[ PS.idS PS.𝟙 , prod-m (id _) p₂ ]
        sqΓ : Fam𝒞._≈_ (Fam𝒞._∘_ Fam𝒞-P.p₁ e×) (Fam𝒞._∘_ Fam𝒞-P.p₁ cmp)
        sqΓ ._≃_.idxf-eq .PS._≃m_.func-eq _ = Γc .idx .isEquivalence .refl
        sqΓ ._≃_.famf-eq .indexed-family._≃f_.transf-eq =
          ≈-trans (∘-cong (Γc .fam .refl*) (≈-trans id-left id-right))
          (≈-trans id-left
          (≈-sym (≈-trans id-left
                 (≈-trans (∘-cong ≈-refl (≈-trans id-left id-left))
                          (≈-trans (pair-p₁ _ _) id-left)))))
        sqY : Fam𝒞._≈_ (Fam𝒞._∘_ (Fam𝒞-P.p₂ {X .carrier} {Y .carrier})
                                 (Fam𝒞._∘_ Fam𝒞-P.p₂ e×))
                       (Fam𝒞._∘_ (Fam𝒞-P.p₂ {Γc} {Y .carrier}) cmp)
        sqY ._≃_.idxf-eq .PS._≃m_.func-eq _ = Y .carrier .idx .isEquivalence .refl
        sqY ._≃_.famf-eq .indexed-family._≃f_.transf-eq =
          ≈-trans (∘-cong (Y .carrier .fam .refl*)
                          (≈-trans id-left (∘-cong ≈-refl (≈-trans id-left id-right))))
          (≈-trans id-left
          (≈-sym (≈-trans id-left
                 (≈-trans (∘-cong ≈-refl (≈-trans id-left id-left))
                          (pair-p₂ _ _)))))
        legΓ : ((Γg .pred [ G .fmor Fam𝒞-P.p₁ ]) [ G .fmor e× ])
               ⊑ ((Γg .pred [ G .fmor Fam𝒞-P.p₁ ]) [ G .fmor cmp ])
        legΓ =
          ⊑-trans ([]-comp _ _)
          (⊑-trans ([]-cong (𝒫C'.≈-sym (G .fmor-comp _ _)))
          (⊑-trans ([]-cong (G .fmor-cong sqΓ))
          (⊑-trans ([]-cong (G .fmor-comp _ _)) ([]-comp⁻¹ _ _))))
        legY : ((((X .pred [ G .fmor Fam𝒞-P.p₁ ]) && (Y .pred [ G .fmor Fam𝒞-P.p₂ ]))
                   [ G .fmor Fam𝒞-P.p₂ ]) [ G .fmor e× ])
               ⊑ ((Y .pred [ G .fmor Fam𝒞-P.p₂ ]) [ G .fmor cmp ])
        legY =
          ⊑-trans ([]-comp _ _)
          (⊑-trans ([]-cong (𝒫C'.≈-sym (G .fmor-comp _ _)))
          (⊑-trans []-&&-dist
          (⊑-trans (&&-isMeet .IsMeet.π₂)
          (⊑-trans ([]-comp _ _)
          (⊑-trans ([]-cong (𝒫C'.≈-sym (G .fmor-comp _ _)))
          (⊑-trans ([]-cong (G .fmor-cong sqY))
          (⊑-trans ([]-cong (G .fmor-comp _ _)) ([]-comp⁻¹ _ _))))))))

    -- The strong pairing of two singleton fold hypotheses.
    strong-pair-sing : ∀ (X₁ X₂ Y₁ Y₂ : Gl.Obj) (γ : Γc .idx .Carrier)
      (ι₁ : X₁ .carrier .idx .Carrier) (ι₂ : X₂ .carrier .idx .Carrier)
      (hs₁ : Mor simple[ PS.𝟙 , prod (Γc .fam .fm γ) (X₁ .carrier .fam .fm ι₁) ]
                 (Y₁ .carrier))
      (hs₂ : Mor simple[ PS.𝟙 , prod (Γc .fam .fm γ) (X₂ .carrier .fam .fm ι₂) ]
                 (Y₂ .carrier)) →
      (((Γg [×] X₁) .pred [ G .fmor (elem-in (prodC (X₁ .carrier)) (γ , ι₁)) ])
        ⊑ (Y₁ .pred [ G .fmor hs₁ ])) →
      (((Γg [×] X₂) .pred [ G .fmor (elem-in (prodC (X₂ .carrier)) (γ , ι₂)) ])
        ⊑ (Y₂ .pred [ G .fmor hs₂ ])) →
      (((Γg [×] (X₁ [×] X₂)) .pred
          [ G .fmor (elem-in (prodC (Fam𝒞-P.prod (X₁ .carrier) (X₂ .carrier)))
                             (γ , (ι₁ , ι₂))) ])
        ⊑ ((Y₁ [×] Y₂) .pred
             [ G .fmor (Fam𝒞-P.pair
                          (Fam𝒞._∘_ hs₁ simplef[ PS.idS PS.𝟙 , prod-m (id _) p₁ ])
                          (Fam𝒞._∘_ hs₂ simplef[ PS.idS PS.𝟙 , prod-m (id _) p₂ ])) ]))
    strong-pair-sing X₁ X₂ Y₁ Y₂ γ ι₁ ι₂ hs₁ hs₂ HYP₁ HYP₂ =
      ⊑-trans (&&-isMeet .IsMeet.⟨_,_⟩ leg₁ leg₂) []-&&
      where
        leg₁ = ⊑-trans (sing-strong-proj₁ X₁ X₂ γ ι₁ ι₂)
               (⊑-trans ([]-cong (G .fmor-comp _ _))
               (⊑-trans ([]-comp⁻¹ _ _)
               (⊑-trans (HYP₁ [ G .fmor simplef[ PS.idS PS.𝟙 , prod-m (id _) p₁ ] ]m)
               (⊑-trans ([]-comp _ _)
               (⊑-trans ([]-cong (𝒫C'.≈-sym (G .fmor-comp _ _)))
               (⊑-trans ([]-cong (G .fmor-cong (Fam𝒞.≈-sym (Fam𝒞-P.pair-p₁ _ _))))
               (⊑-trans ([]-cong (G .fmor-comp _ _)) ([]-comp⁻¹ _ _))))))))
        leg₂ = ⊑-trans (sing-strong-proj₂ X₁ X₂ γ ι₁ ι₂)
               (⊑-trans ([]-cong (G .fmor-comp _ _))
               (⊑-trans ([]-comp⁻¹ _ _)
               (⊑-trans (HYP₂ [ G .fmor simplef[ PS.idS PS.𝟙 , prod-m (id _) p₂ ] ]m)
               (⊑-trans ([]-comp _ _)
               (⊑-trans ([]-cong (𝒫C'.≈-sym (G .fmor-comp _ _)))
               (⊑-trans ([]-cong (G .fmor-cong (Fam𝒞.≈-sym (Fam𝒞-P.pair-p₂ _ _))))
               (⊑-trans ([]-cong (G .fmor-comp _ _)) ([]-comp⁻¹ _ _))))))))

    -- A parallel action after the strong action fuses componentwise.
    pm-spm : ∀ {w x₁ x₂ y₁ y₂ z₁ z₂} (h : y₁ ⇒ z₁) (k : y₂ ⇒ z₂)
             (u : prod w x₁ ⇒ y₁) (v : prod w x₂ ⇒ y₂) →
             (prod-m h k ∘ strong-prod-m u v) ≈ strong-prod-m (h ∘ u) (k ∘ v)
    pm-spm h k u v =
      ≈-trans (pair-natural _ _ _)
      (pair-cong
        (≈-trans (assoc _ _ _)
                 (≈-trans (∘-cong ≈-refl (pair-p₁ _ _)) (≈-sym (assoc _ _ _))))
        (≈-trans (assoc _ _ _)
                 (≈-trans (∘-cong ≈-refl (pair-p₂ _ _)) (≈-sym (assoc _ _ _)))))

    module GlCP = Gl.coproducts coproducts
    module CP = HasCoproducts coproducts

  -- The singleton fold preservation: five mutually recursive inclusions,
  -- mirroring the fold's own recursion, each at a fixed index of the paired
  -- carrier so that the γ-dependent targets of the reindexing layer are fixed.
  module presv
      (algP : (Γg [×] fobj-Gl P pP δA' δPA⁺) .pred ⊑ (Ag .pred [ G .fmor alg ]))
      where

    fold-sing : ∀ (t : Tδ.W ∣ P ∣ (λ i → inj₁ i)) (γ : Γc .idx .Carrier)
                (ι : Mδ.fib-Gl P (λ i → lift tt) pP (λ i → lift tt) t .carrier .idx .Carrier) →
                ((Γg [×] Mδ.fib-Gl P (λ i → lift tt) pP (λ i → lift tt) t) .pred
                   [ G .fmor (elem-in (prodC (Mδ.fib-Gl P (λ i → lift tt) pP (λ i → lift tt) t
                                                .carrier)) (γ , ι)) ])
                ⊑ (Ag .pred
                     [ G .fmor (Fam𝒞._∘_ (fold-mor t)
                                 (elem-in (prodC (Mδ.fib-Gl P (λ i → lift tt) pP
                                                    (λ i → lift tt) t .carrier)) (γ , ι))) ])

    fold-shape-sing : ∀ (Q : Poly (suc n)) (pQ : PolyPred Q)
                      (x : Tδ.⟦ ∣ Q ∣ ⟧shape (Sh.η₀ ∣ P ∣)) (γ : Γc .idx .Carrier)
                      (ι : Mδ.fib-shape-Gl Q dP pQ pdP x .carrier .idx .Carrier) →
                      ((Γg [×] Mδ.fib-shape-Gl Q dP pQ pdP x) .pred
                         [ G .fmor (elem-in (prodC (Mδ.fib-shape-Gl Q dP pQ pdP x .carrier))
                                            (γ , ι)) ])
                      ⊑ (fobj-Gl Q pQ δA' δPA⁺ .pred
                           [ G .fmor (Fam𝒞._∘_ (fold-shape-mor Q pQ x)
                                       (elem-in (prodC (Mδ.fib-shape-Gl Q dP pQ pdP x .carrier))
                                                (γ , ι))) ])

    fold-reindex-sing : ∀ {k} (Q : Poly (suc k)) {ρ : Fin k → Fin n ⊎ Sort n}
                        {ρ' : Fin k → Fin (suc n) ⊎ Sort (suc n)}
                        {d : ∀ v → Tδ.DecoAssign (ρ v)} {d' : ∀ v → FD.TA'.DecoAssign (ρ' v)}
                        {fm : FD.FMor ρ ρ' d d'} (pQ : PolyPred Q) {pd pd'}
                        (pmf : PredF fm pd pd') (t : Tδ.W ∣ Q ∣ ρ) (γ : Γc .idx .Carrier)
                        (ι : Mδ.fib-Gl Q d pQ pd t .carrier .idx .Carrier) →
                        ((Γg [×] Mδ.fib-Gl Q d pQ pd t) .pred
                           [ G .fmor (elem-in (prodC (Mδ.fib-Gl Q d pQ pd t .carrier)) (γ , ι)) ])
                        ⊑ (MA'.fib-Gl Q d' pQ pd' (FD.fold-reindex γ fm t) .pred
                             [ G .fmor (Fam𝒞._∘_
                                 (MA'.fib-out Q d' pQ pd' (FD.fold-reindex γ fm t))
                                 simplef[ PS.idS PS.𝟙 ,
                                          FD.fold-reindex-fam γ fm t
                                            ∘ prod-m (id _) (Mδ.in-fib Q d pQ pd t ι) ]) ])

    fold-reindex-shape-sing : ∀ {j} (R : Poly j) {ηA : Fin j → Fin n ⊎ Sort n}
                              {ηB : Fin j → Fin (suc n) ⊎ Sort (suc n)}
                              {dA : ∀ v → Tδ.DecoAssign (ηA v)}
                              {dB : ∀ v → FD.TA'.DecoAssign (ηB v)}
                              {fm : FD.FMor ηA ηB dA dB} (pR : PolyPred R) {pdA pdB}
                              (pmf : PredF fm pdA pdB) (a : Tδ.⟦ ∣ R ∣ ⟧shape ηA)
                              (γ : Γc .idx .Carrier)
                              (ι : Mδ.fib-shape-Gl R dA pR pdA a .carrier .idx .Carrier) →
                              ((Γg [×] Mδ.fib-shape-Gl R dA pR pdA a) .pred
                                 [ G .fmor (elem-in (prodC (Mδ.fib-shape-Gl R dA pR pdA a
                                                              .carrier)) (γ , ι)) ])
                              ⊑ (MA'.fib-shape-Gl R dB pR pdB (FD.fold-reindex-shape γ R fm a)
                                   .pred
                                   [ G .fmor (Fam𝒞._∘_
                                       (MA'.shape-out R dB pR pdB
                                         (FD.fold-reindex-shape γ R fm a))
                                       simplef[ PS.idS PS.𝟙 ,
                                                FD.fold-reindex-shape-fam γ R fm a
                                                  ∘ prod-m (id _)
                                                      (Mδ.in-shape R dA pR pdA a ι) ]) ])

    fold-apply-sing : ∀ {k} {ρ : Fin k → Fin n ⊎ Sort n}
                      {ρ' : Fin k → Fin (suc n) ⊎ Sort (suc n)}
                      {d : ∀ v → Tδ.DecoAssign (ρ v)} {d' : ∀ v → FD.TA'.DecoAssign (ρ' v)}
                      {fm : FD.FMor ρ ρ' d d'} {pd pd'}
                      (pmf : PredF fm pd pd') (v : Fin k) (a : Tδ.El (ρ v))
                      (γ : Γc .idx .Carrier)
                      (ι : Mδ.fib-el-Gl (ρ v) (d v) (pd v) a .carrier .idx .Carrier) →
                      ((Γg [×] Mδ.fib-el-Gl (ρ v) (d v) (pd v) a) .pred
                         [ G .fmor (elem-in (prodC (Mδ.fib-el-Gl (ρ v) (d v) (pd v) a
                                                      .carrier)) (γ , ι)) ])
                      ⊑ (MA'.fib-el-Gl (ρ' v) (d' v) (pd' v) (FD.fold-apply γ fm v a) .pred
                           [ G .fmor (Fam𝒞._∘_
                               (MA'.el-out (ρ' v) (d' v) (pd' v) (FD.fold-apply γ fm v a))
                               simplef[ PS.idS PS.𝟙 ,
                                        FD.fold-apply-fam γ fm v a
                                          ∘ prod-m (id _) (Mδ.in-el (ρ v) (d v) (pd v) a ι) ]) ])

    fold-sing (Tδ.sup x) γ ι =
      ⊑-trans (&&-isMeet .IsMeet.⟨_,_⟩ legΓ legF)
      (⊑-trans []-&&
      (⊑-trans (algP [ G .fmor pe ]m)
      (⊑-trans ([]-comp _ _)
      (⊑-trans ([]-cong (𝒫C'.≈-sym (G .fmor-comp _ _)))
               ([]-cong (G .fmor-cong finsq))))))
      where
        esing = elem-in (prodC (Mδ.fib-Gl P (λ i → lift tt) pP (λ i → lift tt) (Tδ.sup x)
                                  .carrier)) (γ , ι)
        pe = Fam𝒞._∘_ (Fam𝒞-P.pair Fam𝒞-P.p₁ (fold-shape-mor P pP x)) esing
        legΓ = ⊑-trans []-&&-dist
               (⊑-trans (&&-isMeet .IsMeet.π₁)
               (⊑-trans ([]-comp _ _)
               (⊑-trans ([]-cong (𝒫C'.≈-sym (G .fmor-comp _ _)))
               (⊑-trans ([]-cong (G .fmor-cong
                           (Fam𝒞.≈-trans
                             (Fam𝒞.∘-cong (Fam𝒞.≈-sym (Fam𝒞-P.pair-p₁ _ _)) Fam𝒞.≈-refl)
                             (Fam𝒞.assoc _ _ _))))
               (⊑-trans ([]-cong (G .fmor-comp _ _)) ([]-comp⁻¹ _ _))))))
        legF = ⊑-trans (fold-shape-sing P pP x γ ι)
               (⊑-trans ([]-cong (G .fmor-cong
                           (Fam𝒞.≈-trans
                             (Fam𝒞.∘-cong (Fam𝒞.≈-sym (Fam𝒞-P.pair-p₂ _ _)) Fam𝒞.≈-refl)
                             (Fam𝒞.assoc _ _ _))))
               (⊑-trans ([]-cong (G .fmor-comp _ _)) ([]-comp⁻¹ _ _)))
        sup-sq : Fam𝒞._≈_ (Fam𝒞._∘_ alg (Fam𝒞-P.pair Fam𝒞-P.p₁ (fold-shape-mor P pP x)))
                          (fold-mor (Tδ.sup x))
        sup-sq ._≃_.idxf-eq .PS._≃m_.func-eq (γ≈ , ι≈) =
          FD.fold-idx-resp γ≈ {Tδ.sup x} {Tδ.sup x}
            (Tδ.W-≈-refl {Q = ∣ P ∣} {ρ = λ i → inj₁ i} (Tδ.sup x))
        sup-sq ._≃_.famf-eq .indexed-family._≃f_.transf-eq =
          ≈-trans (∘-cong (Ag .carrier .fam .refl*) id-left)
          (≈-trans id-left
          (≈-sym (≈-trans (assoc _ _ _)
                 (≈-trans (∘-cong ≈-refl (pair-natural _ _ _))
                          (∘-cong ≈-refl
                            (pair-cong (≈-trans (pair-p₁ _ _) id-left) ≈-refl))))))
        finsq = Fam𝒞.≈-trans (Fam𝒞.≈-sym (Fam𝒞.assoc _ _ _)) (Fam𝒞.∘-cong sup-sq Fam𝒞.≈-refl)

    fold-shape-sing (const A') pA' a γ ι =
      ⊑-trans ((&&-isMeet .IsMeet.π₂)
                 [ G .fmor (elem-in (prodC (Mδ.fib-shape-Gl (const A') dP pA' pdP a .carrier))
                                    (γ , ι)) ]m)
      (⊑-trans ([]-comp _ _)
      (⊑-trans ([]-cong (𝒫C'.≈-sym (G .fmor-comp _ _)))
      (⊑-trans ([]-comp _ _)
      (⊑-trans ([]-cong (𝒫C'.≈-sym (G .fmor-comp _ _)))
               ([]-cong (G .fmor-cong SQc))))))
      where
        SQc : Fam𝒞._≈_ (Fam𝒞._∘_ (elem-in A' a)
                          (Fam𝒞._∘_ Fam𝒞-P.p₂
                            (elem-in (prodC (Mδ.fib-shape-Gl (const A') dP pA' pdP a .carrier))
                                     (γ , ι))))
                       (Fam𝒞._∘_ (fold-shape-mor (const A') pA' a)
                          (elem-in (prodC (Mδ.fib-shape-Gl (const A') dP pA' pdP a .carrier))
                                   (γ , ι)))
        SQc ._≃_.idxf-eq .PS._≃m_.func-eq _ = A' .idx .isEquivalence .refl
        SQc ._≃_.famf-eq .indexed-family._≃f_.transf-eq =
          ≈-trans (∘-cong (A' .fam .refl*)
                          (≈-trans id-left (≈-trans id-left (≈-trans id-left id-right))))
          (≈-trans id-left
          (≈-sym (≈-trans id-left
                 (≈-trans id-right (≈-trans (∘-cong ≈-refl prod-m-id) id-right)))))

    fold-shape-sing (var Fin.zero) pQ t' γ ι =
      ⊑-trans (fold-sing t' γ ι)
              ([]-cong (G .fmor-cong
                (Fam𝒞.∘-cong (Fam𝒞.≈-sym (vz-mor pQ t')) Fam𝒞.≈-refl)))

    fold-shape-sing (var (Fin.suc i)) pQ a γ ι =
      ⊑-trans ((&&-isMeet .IsMeet.π₂)
                 [ G .fmor (elem-in (prodC (Mδ.fib-shape-Gl (var (Fin.suc i)) dP pQ pdP a
                                              .carrier)) (γ , ι)) ]m)
      (⊑-trans ([]-comp _ _)
      (⊑-trans ([]-cong (𝒫C'.≈-sym (G .fmor-comp _ _)))
      (⊑-trans ([]-comp _ _)
      (⊑-trans ([]-cong (𝒫C'.≈-sym (G .fmor-comp _ _)))
               ([]-cong (G .fmor-cong SQvs))))))
      where
        SQvs : Fam𝒞._≈_ (Fam𝒞._∘_ (elem-in (δ i) a)
                           (Fam𝒞._∘_ Fam𝒞-P.p₂
                             (elem-in (prodC (Mδ.fib-shape-Gl (var (Fin.suc i)) dP pQ pdP a
                                                .carrier)) (γ , ι))))
                        (Fam𝒞._∘_ (fold-shape-mor (var (Fin.suc i)) pQ a)
                           (elem-in (prodC (Mδ.fib-shape-Gl (var (Fin.suc i)) dP pQ pdP a
                                              .carrier)) (γ , ι)))
        SQvs ._≃_.idxf-eq .PS._≃m_.func-eq _ = δ i .idx .isEquivalence .refl
        SQvs ._≃_.famf-eq .indexed-family._≃f_.transf-eq =
          ≈-trans (∘-cong (δ i .fam .refl*)
                          (≈-trans id-left (≈-trans id-left (≈-trans id-left id-right))))
          (≈-trans id-left
          (≈-sym (≈-trans id-left
                 (≈-trans id-right (≈-trans (∘-cong ≈-refl prod-m-id) id-right)))))

    fold-shape-sing (Q₁ + Q₂) (pQ₁ , pQ₂) (inj₁ x) γ ι =
      ⊑-trans (node-sing (Mδ.fib-shape-Gl Q₁ dP pQ₁ pdP x) (fobj-Gl Q₁ pQ₁ δA' δPA⁺) γ ι
                 (Fam𝒞._∘_ (fold-shape-mor Q₁ pQ₁ x)
                    (elem-in (prodC (Mδ.fib-shape-Gl Q₁ dP pQ₁ pdP x .carrier)) (γ , ι)))
                 (fold-shape-sing Q₁ pQ₁ x γ ι)
                 (MZ.fib-shape-Gl-zero Q₁ dP pQ₁ pdP x))
      (⊑-trans ((GlCP.in₁ {Lf-Gl (fobj-Gl Q₁ pQ₁ δA' δPA⁺)} {Lf-Gl (fobj-Gl Q₂ pQ₂ δA' δPA⁺)}
                   .presv)
                  [ G .fmor (sing-under-root
                      (Fam𝒞._∘_ (fold-shape-mor Q₁ pQ₁ x)
                         (elem-in (prodC (Mδ.fib-shape-Gl Q₁ dP pQ₁ pdP x .carrier))
                                  (γ , ι)))) ]m)
      (⊑-trans ([]-comp _ _)
      (⊑-trans ([]-cong (𝒫C'.≈-sym (G .fmor-comp _ _)))
               ([]-cong (G .fmor-cong SQp₁)))))
      where
        SQp₁ : Fam𝒞._≈_ (Fam𝒞._∘_ CP.in₁
                           (sing-under-root
                             (Fam𝒞._∘_ (fold-shape-mor Q₁ pQ₁ x)
                                (elem-in (prodC (Mδ.fib-shape-Gl Q₁ dP pQ₁ pdP x .carrier))
                                         (γ , ι)))))
                        (Fam𝒞._∘_ (fold-shape-mor (Q₁ + Q₂) (pQ₁ , pQ₂) (inj₁ x))
                           (elem-in (prodC (Mδ.fib-shape-Gl (Q₁ + Q₂) dP (pQ₁ , pQ₂) pdP
                                              (inj₁ x) .carrier)) (γ , ι)))
        SQp₁ ._≃_.idxf-eq .PS._≃m_.func-eq _ =
          R.fobj μObj Q₁ (extend δ (Ag .carrier)) .idx .isEquivalence .refl
        SQp₁ ._≃_.famf-eq .indexed-family._≃f_.transf-eq =
          ≈-trans (∘-cong (≈-trans (Lmap-cong (R.fobj μObj Q₁ (extend δ (Ag .carrier))
                                                 .fam .refl*)) Lmap-id)
                          (≈-trans id-left id-left))
          (≈-trans id-left
          (≈-trans (under-root-cong (≈-trans id-left id-right))
          (≈-sym (≈-trans id-left
                 (≈-trans id-right
                          (under-root-pre (id _)
                            (Mδ.in-out-shape Q₁ dP pQ₁ pdP x ι)
                            (Mδ.out-in-shape Q₁ dP pQ₁ pdP x ι)
                            (FD.fold-shape-fam Q₁ γ x)))))))

    fold-shape-sing (Q₁ + Q₂) (pQ₁ , pQ₂) (inj₂ y) γ ι =
      ⊑-trans (node-sing (Mδ.fib-shape-Gl Q₂ dP pQ₂ pdP y) (fobj-Gl Q₂ pQ₂ δA' δPA⁺) γ ι
                 (Fam𝒞._∘_ (fold-shape-mor Q₂ pQ₂ y)
                    (elem-in (prodC (Mδ.fib-shape-Gl Q₂ dP pQ₂ pdP y .carrier)) (γ , ι)))
                 (fold-shape-sing Q₂ pQ₂ y γ ι)
                 (MZ.fib-shape-Gl-zero Q₂ dP pQ₂ pdP y))
      (⊑-trans ((GlCP.in₂ {Lf-Gl (fobj-Gl Q₁ pQ₁ δA' δPA⁺)} {Lf-Gl (fobj-Gl Q₂ pQ₂ δA' δPA⁺)}
                   .presv)
                  [ G .fmor (sing-under-root
                      (Fam𝒞._∘_ (fold-shape-mor Q₂ pQ₂ y)
                         (elem-in (prodC (Mδ.fib-shape-Gl Q₂ dP pQ₂ pdP y .carrier))
                                  (γ , ι)))) ]m)
      (⊑-trans ([]-comp _ _)
      (⊑-trans ([]-cong (𝒫C'.≈-sym (G .fmor-comp _ _)))
               ([]-cong (G .fmor-cong SQp₂)))))
      where
        SQp₂ : Fam𝒞._≈_ (Fam𝒞._∘_ CP.in₂
                           (sing-under-root
                             (Fam𝒞._∘_ (fold-shape-mor Q₂ pQ₂ y)
                                (elem-in (prodC (Mδ.fib-shape-Gl Q₂ dP pQ₂ pdP y .carrier))
                                         (γ , ι)))))
                        (Fam𝒞._∘_ (fold-shape-mor (Q₁ + Q₂) (pQ₁ , pQ₂) (inj₂ y))
                           (elem-in (prodC (Mδ.fib-shape-Gl (Q₁ + Q₂) dP (pQ₁ , pQ₂) pdP
                                              (inj₂ y) .carrier)) (γ , ι)))
        SQp₂ ._≃_.idxf-eq .PS._≃m_.func-eq _ =
          R.fobj μObj Q₂ (extend δ (Ag .carrier)) .idx .isEquivalence .refl
        SQp₂ ._≃_.famf-eq .indexed-family._≃f_.transf-eq =
          ≈-trans (∘-cong (≈-trans (Lmap-cong (R.fobj μObj Q₂ (extend δ (Ag .carrier))
                                                 .fam .refl*)) Lmap-id)
                          (≈-trans id-left id-left))
          (≈-trans id-left
          (≈-trans (under-root-cong (≈-trans id-left id-right))
          (≈-sym (≈-trans id-left
                 (≈-trans id-right
                          (under-root-pre (id _)
                            (Mδ.in-out-shape Q₂ dP pQ₂ pdP y ι)
                            (Mδ.out-in-shape Q₂ dP pQ₂ pdP y ι)
                            (FD.fold-shape-fam Q₂ γ y)))))))

    fold-shape-sing (Q₁ × Q₂) (pQ₁ , pQ₂) (x , y) γ (ι₁ , ι₂) =
      ⊑-trans (node-sing (Mδ.fib-shape-Gl Q₁ dP pQ₁ pdP x [×] Mδ.fib-shape-Gl Q₂ dP pQ₂ pdP y)
                 (fobj-Gl Q₁ pQ₁ δA' δPA⁺ [×] fobj-Gl Q₂ pQ₂ δA' δPA⁺) γ (ι₁ , ι₂) hs×
                 (strong-pair-sing (Mδ.fib-shape-Gl Q₁ dP pQ₁ pdP x)
                                   (Mδ.fib-shape-Gl Q₂ dP pQ₂ pdP y)
                                   (fobj-Gl Q₁ pQ₁ δA' δPA⁺) (fobj-Gl Q₂ pQ₂ δA' δPA⁺)
                                   γ ι₁ ι₂ hs₁ hs₂
                                   (fold-shape-sing Q₁ pQ₁ x γ ι₁)
                                   (fold-shape-sing Q₂ pQ₂ y γ ι₂))
                 (Zeroed-[×] {Mδ.fib-shape-Gl Q₁ dP pQ₁ pdP x}
                             {Mδ.fib-shape-Gl Q₂ dP pQ₂ pdP y}
                             (MZ.fib-shape-Gl-zero Q₁ dP pQ₁ pdP x)
                             (MZ.fib-shape-Gl-zero Q₂ dP pQ₂ pdP y)))
              ([]-cong (G .fmor-cong SQ×))
      where
        hs₁ = Fam𝒞._∘_ (fold-shape-mor Q₁ pQ₁ x)
                       (elem-in (prodC (Mδ.fib-shape-Gl Q₁ dP pQ₁ pdP x .carrier)) (γ , ι₁))
        hs₂ = Fam𝒞._∘_ (fold-shape-mor Q₂ pQ₂ y)
                       (elem-in (prodC (Mδ.fib-shape-Gl Q₂ dP pQ₂ pdP y .carrier)) (γ , ι₂))
        hs× = Fam𝒞-P.pair (Fam𝒞._∘_ hs₁ simplef[ PS.idS PS.𝟙 , prod-m (id _) p₁ ])
                          (Fam𝒞._∘_ hs₂ simplef[ PS.idS PS.𝟙 , prod-m (id _) p₂ ])
        SQ× : Fam𝒞._≈_ (sing-under-root hs×)
                       (Fam𝒞._∘_ (fold-shape-mor (Q₁ × Q₂) (pQ₁ , pQ₂) (x , y))
                          (elem-in (prodC (Mδ.fib-shape-Gl (Q₁ × Q₂) dP (pQ₁ , pQ₂) pdP
                                             (x , y) .carrier)) (γ , (ι₁ , ι₂))))
        SQ× ._≃_.idxf-eq .PS._≃m_.func-eq _ =
          R.fobj μObj Q₁ (extend δ (Ag .carrier)) .idx .isEquivalence .refl ,
          R.fobj μObj Q₂ (extend δ (Ag .carrier)) .idx .isEquivalence .refl
        SQ× ._≃_.famf-eq .indexed-family._≃f_.transf-eq =
          ≈-trans (∘-cong
                    (≈-trans (Lmap-cong
                       (≈-trans (prod-m-cong
                                  (R.fobj μObj Q₁ (extend δ (Ag .carrier)) .fam .refl*)
                                  (R.fobj μObj Q₂ (extend δ (Ag .carrier)) .fam .refl*))
                                prod-m-id))
                       Lmap-id)
                    (under-root-cong
                      (pair-cong
                        (≈-trans id-left (∘-cong (≈-trans id-left id-right)
                                                 (pair-cong id-left ≈-refl)))
                        (≈-trans id-left (∘-cong (≈-trans id-left id-right)
                                                 (pair-cong id-left ≈-refl))))))
          (≈-trans id-left
          (≈-sym (≈-trans id-left
                 (≈-trans id-right
                 (≈-trans (under-root-pre (id _)
                            (pm-iso (Mδ.in-out-shape Q₁ dP pQ₁ pdP x ι₁)
                                    (Mδ.in-out-shape Q₂ dP pQ₂ pdP y ι₂))
                            (pm-iso (Mδ.out-in-shape Q₁ dP pQ₁ pdP x ι₁)
                                    (Mδ.out-in-shape Q₂ dP pQ₂ pdP y ι₂))
                            (strong-prod-m (FD.fold-shape-fam Q₁ γ x)
                                           (FD.fold-shape-fam Q₂ γ y)))
                          (under-root-cong
                            (spm-fusion (FD.fold-shape-fam Q₁ γ x) (FD.fold-shape-fam Q₂ γ y)
                                        (Mδ.in-shape Q₁ dP pQ₁ pdP x ι₁)
                                        (Mδ.in-shape Q₂ dP pQ₂ pdP y ι₂))))))))

    fold-shape-sing (μ Q'') pQ'' t γ ι =
      ⊑-trans (fold-reindex-sing Q'' pQ'' pfbase t γ ι)
      (⊑-trans ((unit (G .fmor (MA'.tree-in Q'' pQ'' (FD.fold-reindex γ FD.fbase t))))
                  [ G .fmor u3 ]m)
      (⊑-trans ([]-comp _ _)
      (⊑-trans ([]-cong (𝒫C'.≈-sym (G .fmor-comp _ _)))
      (⊑-trans ((⊑-trans (⋁-isJoin .IsBigJoin.upper _ _ (FD.fold-reindex γ FD.fbase t))
                         (𝐂-isClosure .IsClosureOp.unit))
                  [ G .fmor (Fam𝒞._∘_ (MA'.tree-in Q'' pQ'' (FD.fold-reindex γ FD.fbase t))
                                      u3) ]m)
               ([]-cong (G .fmor-cong SQμ))))))
      where
        u3 = Fam𝒞._∘_ (MA'.fib-out Q'' (λ v → lift tt) pQ'' (λ v → lift tt)
                         (FD.fold-reindex γ FD.fbase t))
                      simplef[ PS.idS PS.𝟙 ,
                               FD.fold-reindex-fam γ FD.fbase t
                                 ∘ prod-m (id _)
                                     (Mδ.in-fib Q'' dP pQ'' pdP t ι) ]
        SQμ : Fam𝒞._≈_ (Fam𝒞._∘_ (MA'.tree-in Q'' pQ'' (FD.fold-reindex γ FD.fbase t)) u3)
                       (Fam𝒞._∘_ (fold-shape-mor (μ Q'') pQ'' t)
                          (elem-in (prodC (Mδ.fib-shape-Gl (μ Q'') dP pQ'' pdP t .carrier))
                                   (γ , ι)))
        SQμ ._≃_.idxf-eq .PS._≃m_.func-eq _ =
          FD.TA'.W-≈-refl (FD.fold-reindex γ FD.fbase t)
        SQμ ._≃_.famf-eq .indexed-family._≃f_.transf-eq =
          ≈-trans (∘-cong (FD.TA'.fib-refl* Q'' (λ v → lift tt) (FD.fold-reindex γ FD.fbase t))
                          (≈-trans id-left
                          (≈-trans (∘-cong ≈-refl id-left)
                          (≈-trans (≈-sym (assoc _ _ _))
                          (≈-trans (∘-cong (MA'.in-out-fib Q'' (λ v → lift tt) pQ''
                                             (λ v → lift tt) (FD.fold-reindex γ FD.fbase t) _)
                                           ≈-refl)
                                   id-left)))))
          (≈-trans id-left (≈-sym (≈-trans id-left id-right)))

    fold-reindex-sing Q {d' = d'} {fm = fm} pQ {pd' = pd'} pmf (Tδ.sup x) γ ι =
      ⊑-trans (fold-reindex-shape-sing Q pQ (pfbind Q pQ pmf) x γ ι)
              ([]-cong (G .fmor-cong
                (Fam𝒞.∘-cong
                  (Fam𝒞.≈-sym (MA'.fib-shape-out Q d' pQ pd'
                                 (FD.fold-reindex-shape γ Q (FD.fbind Q fm) x)))
                  Fam𝒞.≈-refl)))

    fold-reindex-shape-sing (const A') {dA = dA} {dB = dB} {fm = fm} pA'
                            {pdA = pdA} {pdB = pdB} pmf a γ ι =
      ⊑-trans ((&&-isMeet .IsMeet.π₂)
                 [ G .fmor (elem-in (prodC (Mδ.fib-shape-Gl (const A') dA pA' pdA a .carrier))
                                    (γ , ι)) ]m)
      (⊑-trans ([]-comp _ _)
      (⊑-trans ([]-cong (𝒫C'.≈-sym (G .fmor-comp _ _)))
               ([]-cong (G .fmor-cong SQ4c))))
      where
        SQ4c : Fam𝒞._≈_ (Fam𝒞._∘_ Fam𝒞-P.p₂
                           (elem-in (prodC (Mδ.fib-shape-Gl (const A') dA pA' pdA a .carrier))
                                    (γ , ι)))
                        (Fam𝒞._∘_ (MA'.shape-out (const A') dB pA' pdB a)
                           simplef[ PS.idS PS.𝟙 ,
                                    FD.fold-reindex-shape-fam γ (const A') fm a
                                      ∘ prod-m (id _)
                                          (Mδ.in-shape (const A') dA pA' pdA a ι) ])
        SQ4c ._≃_.idxf-eq .PS._≃m_.func-eq e = e
        SQ4c ._≃_.famf-eq .indexed-family._≃f_.transf-eq =
          ≈-trans (≈-trans id-left (≈-trans id-left id-right))
          (≈-sym (≈-trans id-left
                 (≈-trans id-left (≈-trans (∘-cong ≈-refl prod-m-id) id-right))))

    fold-reindex-shape-sing (var v) {dB = dB} {fm = fm} pR {pdB = pdB} pmf a γ ι =
      ⊑-trans (fold-apply-sing pmf v a γ ι)
              ([]-cong (G .fmor-cong
                (Fam𝒞.∘-cong
                  (Fam𝒞.≈-sym (MA'.shape-el-out v dB pR pdB (FD.fold-apply γ fm v a)))
                  Fam𝒞.≈-refl)))

    fold-reindex-shape-sing (P' + Q') {dA = dA} {dB = dB} {fm = fm} (pP' , pQ')
                            {pdA = pdA} {pdB = pdB} pmf (inj₁ a) γ ι =
      ⊑-trans (node-sing (Mδ.fib-shape-Gl P' dA pP' pdA a)
                 (MA'.fib-shape-Gl P' dB pP' pdB (FD.fold-reindex-shape γ P' fm a)) γ ι hs
                 (fold-reindex-shape-sing P' pP' pmf a γ ι)
                 (MZ.fib-shape-Gl-zero P' dA pP' pdA a))
              ([]-cong (G .fmor-cong SQ4p₁))
      where
        hs = Fam𝒞._∘_ (MA'.shape-out P' dB pP' pdB (FD.fold-reindex-shape γ P' fm a))
                      simplef[ PS.idS PS.𝟙 ,
                               FD.fold-reindex-shape-fam γ P' fm a
                                 ∘ prod-m (id _) (Mδ.in-shape P' dA pP' pdA a ι) ]
        SQ4p₁ : Fam𝒞._≈_ (sing-under-root hs)
                         (Fam𝒞._∘_ (MA'.shape-out (P' + Q') dB (pP' , pQ') pdB
                                      (inj₁ (FD.fold-reindex-shape γ P' fm a)))
                            simplef[ PS.idS PS.𝟙 ,
                                     FD.fold-reindex-shape-fam γ (P' + Q') fm (inj₁ a)
                                       ∘ prod-m (id _)
                                           (Mδ.in-shape (P' + Q') dA (pP' , pQ') pdA
                                              (inj₁ a) ι) ])
        SQ4p₁ ._≃_.idxf-eq .PS._≃m_.func-eq _ =
          MA'.fib-shape-Gl P' dB pP' pdB (FD.fold-reindex-shape γ P' fm a)
            .carrier .idx .isEquivalence .refl
        SQ4p₁ ._≃_.famf-eq .indexed-family._≃f_.transf-eq =
          ≈-trans (∘-cong (≈-trans (Lmap-cong (MA'.fib-shape-Gl P' dB pP' pdB
                                                 (FD.fold-reindex-shape γ P' fm a)
                                                 .carrier .fam .refl*))
                                   Lmap-id)
                          (under-root-cong id-left))
          (≈-trans id-left
          (≈-sym (≈-trans id-left
                 (≈-trans (∘-cong ≈-refl
                            (under-root-pre (id _)
                              (Mδ.in-out-shape P' dA pP' pdA a ι)
                              (Mδ.out-in-shape P' dA pP' pdA a ι)
                              (FD.fold-reindex-shape-fam γ P' fm a)))
                          (under-root-post
                            (MA'.out-in-shape P' dB pP' pdB
                              (FD.fold-reindex-shape γ P' fm a)
                              (MA'.shape-ix P' dB pP' pdB (FD.fold-reindex-shape γ P' fm a)))
                            (MA'.in-out-shape P' dB pP' pdB
                              (FD.fold-reindex-shape γ P' fm a)
                              (MA'.shape-ix P' dB pP' pdB (FD.fold-reindex-shape γ P' fm a)))
                            _)))))

    fold-reindex-shape-sing (P' + Q') {dA = dA} {dB = dB} {fm = fm} (pP' , pQ')
                            {pdA = pdA} {pdB = pdB} pmf (inj₂ b) γ ι =
      ⊑-trans (node-sing (Mδ.fib-shape-Gl Q' dA pQ' pdA b)
                 (MA'.fib-shape-Gl Q' dB pQ' pdB (FD.fold-reindex-shape γ Q' fm b)) γ ι hs
                 (fold-reindex-shape-sing Q' pQ' pmf b γ ι)
                 (MZ.fib-shape-Gl-zero Q' dA pQ' pdA b))
              ([]-cong (G .fmor-cong SQ4p₂))
      where
        hs = Fam𝒞._∘_ (MA'.shape-out Q' dB pQ' pdB (FD.fold-reindex-shape γ Q' fm b))
                      simplef[ PS.idS PS.𝟙 ,
                               FD.fold-reindex-shape-fam γ Q' fm b
                                 ∘ prod-m (id _) (Mδ.in-shape Q' dA pQ' pdA b ι) ]
        SQ4p₂ : Fam𝒞._≈_ (sing-under-root hs)
                         (Fam𝒞._∘_ (MA'.shape-out (P' + Q') dB (pP' , pQ') pdB
                                      (inj₂ (FD.fold-reindex-shape γ Q' fm b)))
                            simplef[ PS.idS PS.𝟙 ,
                                     FD.fold-reindex-shape-fam γ (P' + Q') fm (inj₂ b)
                                       ∘ prod-m (id _)
                                           (Mδ.in-shape (P' + Q') dA (pP' , pQ') pdA
                                              (inj₂ b) ι) ])
        SQ4p₂ ._≃_.idxf-eq .PS._≃m_.func-eq _ =
          MA'.fib-shape-Gl Q' dB pQ' pdB (FD.fold-reindex-shape γ Q' fm b)
            .carrier .idx .isEquivalence .refl
        SQ4p₂ ._≃_.famf-eq .indexed-family._≃f_.transf-eq =
          ≈-trans (∘-cong (≈-trans (Lmap-cong (MA'.fib-shape-Gl Q' dB pQ' pdB
                                                 (FD.fold-reindex-shape γ Q' fm b)
                                                 .carrier .fam .refl*))
                                   Lmap-id)
                          (under-root-cong id-left))
          (≈-trans id-left
          (≈-sym (≈-trans id-left
                 (≈-trans (∘-cong ≈-refl
                            (under-root-pre (id _)
                              (Mδ.in-out-shape Q' dA pQ' pdA b ι)
                              (Mδ.out-in-shape Q' dA pQ' pdA b ι)
                              (FD.fold-reindex-shape-fam γ Q' fm b)))
                          (under-root-post
                            (MA'.out-in-shape Q' dB pQ' pdB
                              (FD.fold-reindex-shape γ Q' fm b)
                              (MA'.shape-ix Q' dB pQ' pdB (FD.fold-reindex-shape γ Q' fm b)))
                            (MA'.in-out-shape Q' dB pQ' pdB
                              (FD.fold-reindex-shape γ Q' fm b)
                              (MA'.shape-ix Q' dB pQ' pdB (FD.fold-reindex-shape γ Q' fm b)))
                            _)))))

    fold-reindex-shape-sing (P' × Q') {dA = dA} {dB = dB} {fm = fm} (pP' , pQ')
                            {pdA = pdA} {pdB = pdB} pmf (a , b) γ (ι₁ , ι₂) =
      ⊑-trans (node-sing (Mδ.fib-shape-Gl P' dA pP' pdA a [×] Mδ.fib-shape-Gl Q' dA pQ' pdA b)
                 (MA'.fib-shape-Gl P' dB pP' pdB (FD.fold-reindex-shape γ P' fm a)
                    [×] MA'.fib-shape-Gl Q' dB pQ' pdB (FD.fold-reindex-shape γ Q' fm b))
                 γ (ι₁ , ι₂) hs×
                 (strong-pair-sing (Mδ.fib-shape-Gl P' dA pP' pdA a)
                                   (Mδ.fib-shape-Gl Q' dA pQ' pdA b)
                                   (MA'.fib-shape-Gl P' dB pP' pdB
                                      (FD.fold-reindex-shape γ P' fm a))
                                   (MA'.fib-shape-Gl Q' dB pQ' pdB
                                      (FD.fold-reindex-shape γ Q' fm b))
                                   γ ι₁ ι₂ hsP hsQ
                                   (fold-reindex-shape-sing P' pP' pmf a γ ι₁)
                                   (fold-reindex-shape-sing Q' pQ' pmf b γ ι₂))
                 (Zeroed-[×] {Mδ.fib-shape-Gl P' dA pP' pdA a}
                             {Mδ.fib-shape-Gl Q' dA pQ' pdA b}
                             (MZ.fib-shape-Gl-zero P' dA pP' pdA a)
                             (MZ.fib-shape-Gl-zero Q' dA pQ' pdA b)))
              ([]-cong (G .fmor-cong SQ4×))
      where
        hsP = Fam𝒞._∘_ (MA'.shape-out P' dB pP' pdB (FD.fold-reindex-shape γ P' fm a))
                       simplef[ PS.idS PS.𝟙 ,
                                FD.fold-reindex-shape-fam γ P' fm a
                                  ∘ prod-m (id _) (Mδ.in-shape P' dA pP' pdA a ι₁) ]
        hsQ = Fam𝒞._∘_ (MA'.shape-out Q' dB pQ' pdB (FD.fold-reindex-shape γ Q' fm b))
                       simplef[ PS.idS PS.𝟙 ,
                                FD.fold-reindex-shape-fam γ Q' fm b
                                  ∘ prod-m (id _) (Mδ.in-shape Q' dA pQ' pdA b ι₂) ]
        hs× = Fam𝒞-P.pair (Fam𝒞._∘_ hsP simplef[ PS.idS PS.𝟙 , prod-m (id _) p₁ ])
                          (Fam𝒞._∘_ hsQ simplef[ PS.idS PS.𝟙 , prod-m (id _) p₂ ])
        SQ4× : Fam𝒞._≈_ (sing-under-root hs×)
                        (Fam𝒞._∘_ (MA'.shape-out (P' × Q') dB (pP' , pQ') pdB
                                     (FD.fold-reindex-shape γ P' fm a ,
                                      FD.fold-reindex-shape γ Q' fm b))
                           simplef[ PS.idS PS.𝟙 ,
                                    FD.fold-reindex-shape-fam γ (P' × Q') fm (a , b)
                                      ∘ prod-m (id _)
                                          (Mδ.in-shape (P' × Q') dA (pP' , pQ') pdA
                                             (a , b) (ι₁ , ι₂)) ])
        SQ4× ._≃_.idxf-eq .PS._≃m_.func-eq _ =
          MA'.fib-shape-Gl P' dB pP' pdB (FD.fold-reindex-shape γ P' fm a)
            .carrier .idx .isEquivalence .refl ,
          MA'.fib-shape-Gl Q' dB pQ' pdB (FD.fold-reindex-shape γ Q' fm b)
            .carrier .idx .isEquivalence .refl
        SQ4× ._≃_.famf-eq .indexed-family._≃f_.transf-eq =
          ≈-trans (∘-cong (≈-trans (Lmap-cong
                             (≈-trans (prod-m-cong
                                        (MA'.fib-shape-Gl P' dB pP' pdB
                                           (FD.fold-reindex-shape γ P' fm a)
                                           .carrier .fam .refl*)
                                        (MA'.fib-shape-Gl Q' dB pQ' pdB
                                           (FD.fold-reindex-shape γ Q' fm b)
                                           .carrier .fam .refl*))
                                      prod-m-id))
                             Lmap-id)
                          (under-root-cong
                            (pair-cong
                              (≈-trans id-left (∘-cong id-left (pair-cong id-left ≈-refl)))
                              (≈-trans id-left (∘-cong id-left (pair-cong id-left ≈-refl))))))
          (≈-trans id-left
          (≈-sym (≈-trans id-left
                 (≈-trans (∘-cong ≈-refl
                            (under-root-pre (id _)
                              (pm-iso (Mδ.in-out-shape P' dA pP' pdA a ι₁)
                                      (Mδ.in-out-shape Q' dA pQ' pdA b ι₂))
                              (pm-iso (Mδ.out-in-shape P' dA pP' pdA a ι₁)
                                      (Mδ.out-in-shape Q' dA pQ' pdA b ι₂))
                              (strong-prod-m (FD.fold-reindex-shape-fam γ P' fm a)
                                             (FD.fold-reindex-shape-fam γ Q' fm b))))
                 (≈-trans (under-root-post
                            (pm-iso (MA'.out-in-shape P' dB pP' pdB
                                       (FD.fold-reindex-shape γ P' fm a)
                                       (MA'.shape-ix P' dB pP' pdB
                                          (FD.fold-reindex-shape γ P' fm a)))
                                    (MA'.out-in-shape Q' dB pQ' pdB
                                       (FD.fold-reindex-shape γ Q' fm b)
                                       (MA'.shape-ix Q' dB pQ' pdB
                                          (FD.fold-reindex-shape γ Q' fm b))))
                            (pm-iso (MA'.in-out-shape P' dB pP' pdB
                                       (FD.fold-reindex-shape γ P' fm a)
                                       (MA'.shape-ix P' dB pP' pdB
                                          (FD.fold-reindex-shape γ P' fm a)))
                                    (MA'.in-out-shape Q' dB pQ' pdB
                                       (FD.fold-reindex-shape γ Q' fm b)
                                       (MA'.shape-ix Q' dB pQ' pdB
                                          (FD.fold-reindex-shape γ Q' fm b))))
                            _)
                 (under-root-cong
                   (≈-trans (∘-cong ≈-refl
                              (spm-fusion (FD.fold-reindex-shape-fam γ P' fm a)
                                          (FD.fold-reindex-shape-fam γ Q' fm b)
                                          (Mδ.in-shape P' dA pP' pdA a ι₁)
                                          (Mδ.in-shape Q' dA pQ' pdA b ι₂)))
                            (pm-spm _ _ _ _))))))))

    fold-reindex-shape-sing (μ Q₀) {dB = dB} {fm = fm} pQ₀ {pdB = pdB} pmf t γ ι =
      ⊑-trans (fold-reindex-sing Q₀ pQ₀ pmf t γ ι)
              ([]-cong (G .fmor-cong
                (Fam𝒞.∘-cong
                  (Fam𝒞.≈-sym (MA'.shape-fib-out Q₀ dB pQ₀ pdB (FD.fold-reindex γ fm t)))
                  Fam𝒞.≈-refl)))

    fold-apply-sing pfbase Fin.zero a γ ι =
      ⊑-trans (fold-sing a γ ι)
      (⊑-trans ([]-cong (G .fmor-cong (Fam𝒞.≈-sym SQ50)))
      (⊑-trans ([]-cong (G .fmor-comp _ _)) ([]-comp⁻¹ _ _)))
      where
        uE = Fam𝒞._∘_ (MA'.el-out (inj₁ Fin.zero) (lift tt) (lift tt) (FD.fold-idx γ a))
                      simplef[ PS.idS PS.𝟙 ,
                               FD.fold-apply-fam γ FD.fbase Fin.zero a
                                 ∘ prod-m (id _)
                                     (Mδ.in-el (Sh.η₀ ∣ P ∣ Fin.zero) (dP Fin.zero)
                                        (pdP Fin.zero) a ι) ]
        SQ50 : Fam𝒞._≈_ (Fam𝒞._∘_ (elem-in (Ag .carrier) (FD.fold-idx γ a)) uE)
                        (Fam𝒞._∘_ (fold-mor a)
                           (elem-in (prodC (Mδ.fib-Gl P (λ i → lift tt) pP (λ i → lift tt) a
                                              .carrier)) (γ , ι)))
        SQ50 ._≃_.idxf-eq .PS._≃m_.func-eq _ = Ag .carrier .idx .isEquivalence .refl
        SQ50 ._≃_.famf-eq .indexed-family._≃f_.transf-eq =
          ≈-trans (∘-cong (Ag .carrier .fam .refl*)
                          (≈-trans id-left (≈-trans id-left (≈-trans id-left id-left))))
          (≈-trans id-left (≈-sym (≈-trans id-left id-right)))

    fold-apply-sing pfbase (Fin.suc i) a γ ι =
      ⊑-trans ((&&-isMeet .IsMeet.π₂)
                 [ G .fmor (elem-in (prodC (Mδ.fib-el-Gl (Sh.η₀ ∣ P ∣ (Fin.suc i))
                                              (dP (Fin.suc i)) (pdP (Fin.suc i)) a
                                              .carrier)) (γ , ι)) ]m)
      (⊑-trans ([]-comp _ _)
      (⊑-trans ([]-cong (𝒫C'.≈-sym (G .fmor-comp _ _)))
      (⊑-trans ([]-comp _ _)
      (⊑-trans ([]-cong (𝒫C'.≈-sym (G .fmor-comp _ _)))
      (⊑-trans ([]-cong (G .fmor-cong (Fam𝒞.∘-cong Fam𝒞.≈-refl SQ5s)))
      (⊑-trans ([]-cong (G .fmor-comp _ _)) ([]-comp⁻¹ _ _)))))))
      where
        SQ5s : Fam𝒞._≈_ (Fam𝒞._∘_ Fam𝒞-P.p₂
                           (elem-in (prodC (Mδ.fib-el-Gl (Sh.η₀ ∣ P ∣ (Fin.suc i))
                                              (dP (Fin.suc i)) (pdP (Fin.suc i)) a
                                              .carrier)) (γ , ι)))
                        (Fam𝒞._∘_ (MA'.el-out (inj₁ (Fin.suc i)) (lift tt) (lift tt) a)
                           simplef[ PS.idS PS.𝟙 ,
                                    FD.fold-apply-fam γ FD.fbase (Fin.suc i) a
                                      ∘ prod-m (id _)
                                          (Mδ.in-el (Sh.η₀ ∣ P ∣ (Fin.suc i))
                                             (dP (Fin.suc i)) (pdP (Fin.suc i)) a ι) ])
        SQ5s ._≃_.idxf-eq .PS._≃m_.func-eq e = e
        SQ5s ._≃_.famf-eq .indexed-family._≃f_.transf-eq =
          ≈-trans (≈-trans id-left (≈-trans id-left id-right))
          (≈-sym (≈-trans id-left
                 (≈-trans id-left (≈-trans (∘-cong ≈-refl prod-m-id) id-right))))

    fold-apply-sing (pfbind {d' = d'i} {fm = fm'} {pd' = pd'i} Q pQ' pmf) Fin.zero a γ ι =
      ⊑-trans (fold-reindex-sing Q pQ' pmf a γ ι)
              ([]-cong (G .fmor-cong
                (Fam𝒞.∘-cong
                  (Fam𝒞.≈-sym (MA'.el-fib-out Q d'i pQ' pd'i (FD.fold-reindex γ fm' a)))
                  Fam𝒞.≈-refl)))

    fold-apply-sing (pfbind Q pQ' pmf) (Fin.suc v) a γ ι = fold-apply-sing pmf v a γ ι

    -- The glued catamorphism: the closed join splits into its trees, each
    -- tree into its singletons, and each singleton folds by the recursion;
    -- the closure collapses into the closed target.
    fold-Gl : (Γg [×] Mδ.μ-Gl P pP) .pred ⊑ (Ag .pred [ G .fmor FD.foldMor ])
    fold-Gl =
      ⊑-trans (IsMeet.mono &&-isMeet (IsPreorder.refl ⊑-isPreorder) 𝐂-[]⁻¹)
      (⊑-trans (IsMeet.comm &&-isMeet)
      (⊑-trans 𝐂-strong
      (⊑-trans (𝐂-isClosure .IsClosureOp.mono
                 (⊑-trans (IsMeet.comm &&-isMeet)
                 (⊑-trans (IsMeet.mono &&-isMeet (IsPreorder.refl ⊑-isPreorder) []-⋁)
                 (⊑-trans dist-⋁ (⋁-isJoin .IsBigJoin.least _ _ _ perT)))))
      (⊑-trans 𝐂-[] (A-closed [ G .fmor FD.foldMor ]m)))))
      where
        perT : ∀ (t : Tδ.W ∣ P ∣ (λ i → inj₁ i)) →
               ((Γg .pred [ G .fmor Fam𝒞-P.p₁ ])
                 && ((Mδ.fib-Gl P (λ i → lift tt) pP (λ i → lift tt) t .pred
                        ⟨ G .fmor (Mδ.tree-in P pP t) ⟩) [ G .fmor Fam𝒞-P.p₂ ]))
               ⊑ (Ag .pred [ G .fmor FD.foldMor ])
        perT t =
          ⊑-trans (IsMeet.mono &&-isMeet (IsPreorder.refl ⊑-isPreorder)
                    (BC (Mδ.tree-in P pP t)))
          (⊑-trans frob
          (⊑-trans ((IsMeet.mono &&-isMeet ΓFIX (IsPreorder.refl ⊑-isPreorder))
                      ⟨ G .fmor w ⟩m)
                   (adjoint₂ INNER)))
          where
            w = Fam𝒞-P.pair Fam𝒞-P.p₁ (Fam𝒞._∘_ (Mδ.tree-in P pP t) Fam𝒞-P.p₂)
            ΓFIX = ⊑-trans ([]-comp _ _)
                   (⊑-trans ([]-cong (𝒫C'.≈-sym (G .fmor-comp _ _)))
                            ([]-cong (G .fmor-cong (Fam𝒞-P.pair-p₁ _ _))))
            SQw : Fam𝒞._≈_ (Fam𝒞._∘_ FD.foldMor w) (fold-mor t)
            SQw ._≃_.idxf-eq .PS._≃m_.func-eq (γ≈ , ι≈) =
              FD.fold-idx-resp γ≈ {t} {t}
                (Tδ.W-≈-refl {Q = ∣ P ∣} {ρ = λ i → inj₁ i} t)
            SQw ._≃_.famf-eq .indexed-family._≃f_.transf-eq =
              ≈-trans (∘-cong (Ag .carrier .fam .refl*) id-left)
              (≈-trans id-left
                       (∘-cong ≈-refl (pair-cong (≈-sym id-left) id-left)))
            perS : ∀ (q : prodC (Mδ.fib-Gl P (λ i → lift tt) pP (λ i → lift tt) t .carrier)
                            .idx .Carrier) →
                   (((Γg [×] Mδ.fib-Gl P (λ i → lift tt) pP (λ i → lift tt) t) .pred
                       [ G .fmor (elem-in (prodC (Mδ.fib-Gl P (λ i → lift tt) pP
                                                    (λ i → lift tt) t .carrier)) q) ])
                     ⟨ G .fmor (elem-in (prodC (Mδ.fib-Gl P (λ i → lift tt) pP
                                                  (λ i → lift tt) t .carrier)) q) ⟩)
                   ⊑ ((Ag .pred [ G .fmor FD.foldMor ]) [ G .fmor w ])
            perS (γ , ι) =
              ⊑-trans ((⊑-trans (fold-sing t γ ι)
                       (⊑-trans ([]-cong (G .fmor-cong
                                   (Fam𝒞.∘-cong (Fam𝒞.≈-sym SQw) Fam𝒞.≈-refl)))
                       (⊑-trans ([]-cong (G .fmor-comp _ _))
                       (⊑-trans ([]-comp⁻¹ _ _)
                                ((⊑-trans ([]-cong (G .fmor-comp _ _)) ([]-comp⁻¹ _ _))
                                   [ G .fmor (elem-in (prodC (Mδ.fib-Gl P (λ i → lift tt) pP
                                                                (λ i → lift tt) t .carrier))
                                                      (γ , ι)) ]m)))))
                         ⟨ G .fmor (elem-in (prodC (Mδ.fib-Gl P (λ i → lift tt) pP
                                                      (λ i → lift tt) t .carrier))
                                            (γ , ι)) ⟩m)
                      (counit _)
            INNER = ⊑-trans sing-split
                    (⊑-trans (𝐂-isClosure .IsClosureOp.mono
                               (⋁-isJoin .IsBigJoin.least _ _ _ perS))
                    (⊑-trans 𝐂-[]
                             ((⊑-trans 𝐂-[] (A-closed [ G .fmor FD.foldMor ]m))
                                [ G .fmor w ]m)))
