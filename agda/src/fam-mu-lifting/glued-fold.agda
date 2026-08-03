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
open import basics using (IsJoin; IsMeet; IsBigJoin; IsClosureOp)
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

-- The glued fold, at a fixed μ-polynomial, environment, glued context and
-- glued target with a closed predicate. The additive instance obligations
-- are quantified over the recursive morphism and its preservation.
module GlFold {n} (P : Poly (suc n)) (pP : PolyPred P)
    (δ : Fin n → Obj) (δP : ∀ i → Predicate (G .fobj (δ i)))
    (Γg Ag : Gl.Obj)
    (alg : Mor (Fam𝒞-P.prod (Γg .carrier) (R.fobj μObj P (extend δ (Ag .carrier))))
               (Ag .carrier))
    (payload-absorb : ∀ {X Yg : Gl.Obj}
                      (h : Mor (Fam𝒞-P.prod (Γg .carrier) (X .carrier)) (Yg .carrier)) →
                      ((Γg [×] X) .pred ⊑ (Yg .pred [ G .fmor h ])) →
                      ((Γg [×] X) .pred
                        ⊑ (Lf-Gl Yg .pred
                             [ G .fmor (elim-inj root-pointed (Fam𝒞._∘_ injF h)) ])))
    (root-under : ∀ {X Yg : Gl.Obj}
                  (h : Mor (Fam𝒞-P.prod (Γg .carrier) (X .carrier)) (Yg .carrier)) →
                  ((Γg [×] X) .pred ⊑ (Yg .pred [ G .fmor h ])) →
                  (((Γg .pred [ G .fmor Fam𝒞-P.p₁ ])
                     && (Rt (X .carrier) [ G .fmor Fam𝒞-P.p₂ ]))
                    ⊑ (Lf-Gl Yg .pred
                         [ G .fmor (elimF root-pointed (Fam𝒞._∘_ injF h)) ])))
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
