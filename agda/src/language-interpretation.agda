{-# OPTIONS --prop --postfix-projections --safe #-}

-- The interpretation of the language in a category of families: every value former is
-- lifted. Sums are coproducts of lifted summands, products are lifted products, μ-types the
-- carriers, and function spaces are lifted weak exponentials, so a closure carries a root like any
-- other cell. Constructors inject their payload under the injection, whose root is zero: a cell
-- the program itself constructs depends on nothing. Eliminators, including application, send the
-- scrutinee's root to the result type's unit section scaled by the control weight; the unit
-- section is built by the same induction as the interpretation, from assumed sections at the
-- unit type, the sorts and the exponentials.
-- The empty environment for the μ-carriers is a parameter because functions out of
-- Fin 0 agree only propositionally, and the comparison with a change of base needs the
-- μ-carriers' environment to be the image environment definitionally.

import Data.Fin as Fin
open Fin using (Fin; splitAt)
open import Level using (Level; lift)
open import Data.Nat using (zero; suc; _+_)
open import Data.Unit using (tt)
import Data.Product as DP
open import Data.Sum using (_⊎_; [_,_]; inj₁; inj₂; map₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import categories
  using (Category; HasTerminal; HasProducts; HasCoproducts; HasStrongCoproducts;
         HasExponentials; strong-coproducts→coproducts; coKleisli-prod)
open import cmon-enriched using (CMonEnriched; Biproduct)
open import signature using (Signature; Model; PointedFPCat; PFPC[_,_,_,_])
open import polynomial-functor using (Poly)
open import prop-setoid using (module ≈-Reasoning)
import fam-mu-lifting
import language-syntax

module language-interpretation
  {ℓ} (Sig : Signature ℓ)
  {o m e} (os es : Level) {𝒞 : Category o m e} (let module 𝒞 = Category 𝒞)
  (T : HasTerminal 𝒞) (CM : CMonEnriched 𝒞) (BP : ∀ x y → Biproduct CM x y)
  (𝟙𝒞 : 𝒞.obj)
  (let module Fam⟨𝒞⟩μ = fam-mu-lifting os es CM BP 𝟙𝒞)
  (𝒞E : HasExponentials Fam⟨𝒞⟩μ.cat Fam⟨𝒞⟩μ.products)
  (δ∅ : Fin 0 → Fam⟨𝒞⟩μ.Obj)
  (𝟙ty : Fam⟨𝒞⟩μ.Obj)
  (unit-pt : Fam⟨𝒞⟩μ.Mor (HasTerminal.witness (Fam⟨𝒞⟩μ.terminal T)) 𝟙ty)
  (let Bool = HasCoproducts.coprod Fam⟨𝒞⟩μ.coproducts (Fam⟨𝒞⟩μ.Lf 𝟙ty) (Fam⟨𝒞⟩μ.Lf 𝟙ty))
  (Int : Model PFPC[ Fam⟨𝒞⟩μ.cat , Fam⟨𝒞⟩μ.terminal T , Fam⟨𝒞⟩μ.products , Bool ] Sig)
  (ctrl-w : 𝟙𝒞 𝒞.⇒ 𝟙𝒞)
  (exp-section : ∀ {X Y : Fam⟨𝒞⟩μ.Obj} → Fam⟨𝒞⟩μ.Section (HasExponentials.exp 𝒞E X Y))
  (𝟙ty-section : Fam⟨𝒞⟩μ.Section 𝟙ty)
  (sort-section : ∀ s → Fam⟨𝒞⟩μ.Section (Model.⟦sort⟧ Int s))
  where

open import language-type-interpretation Sig os es T CM BP 𝟙𝒞 𝒞E δ∅ 𝟙ty unit-pt Int ctrl-w
  (λ {X} {Y} → exp-section {X} {Y}) 𝟙ty-section sort-section public

preserves-sub-lift-pw : ∀ {Δ Δ'} (σ : TySub Δ Δ') {δ : Fin Δ' → obj} (δc : ∀ i → Section (δ i))
  {X : obj} (cX : Section X) (i : Fin (suc Δ)) →
  preserves-section (≡-to-⇒ (sub-lift-pw σ δ X i))
    (unit-section (sub-lift σ i) (concat (extend {0} δ∅ X) δ)
      (concat-section {n = 1} (extend-section (λ ()) cX) δc))
    (concat-section {n = 1} (extend-section (λ ()) cX) (λ j → unit-section (σ j) δ δc) i)
preserves-sub-lift-pw σ δc cX Fin.zero = preserves-section-id cX
preserves-sub-lift-pw σ δc cX (Fin.suc j) =
  preserves-as-poly-ren Fin.suc (σ j)
    (concat-section {n = 1} (extend-section (λ ()) cX) δc) (λ ())

preserves-subst-fwd : ∀ {Δ Δ'} (σ : TySub Δ Δ') (τ : type Δ) {δ : Fin Δ' → obj}
  (δc : ∀ i → Section (δ i)) →
  preserves-section (subst-fwd σ τ δ)
    (unit-section (sub σ τ) δ δc)
    (unit-section τ (λ i → ⟦ σ i ⟧ty δ) (λ i → unit-section (σ i) δ δc))
preserves-subst-fwd σ (var i)     {δ} δc = preserves-section-id (unit-section (σ i) δ δc)
preserves-subst-fwd σ unit        δc = preserves-section-id 𝟙ty-section
preserves-subst-fwd σ (base s)    δc = preserves-section-id (sort-section s)
preserves-subst-fwd σ (τ₁ [+] τ₂) {δ} δc =
  preserves-coprod-m
    (preserves-Lf-map {c = u₁} {d = v₁} (preserves-subst-fwd σ τ₁ δc))
    (preserves-Lf-map {c = u₂} {d = v₂} (preserves-subst-fwd σ τ₂ δc))
  where
  u₁ = unit-section (sub σ τ₁) δ δc
  u₂ = unit-section (sub σ τ₂) δ δc
  v₁ = unit-section τ₁ (λ i → ⟦ σ i ⟧ty δ) (λ i → unit-section (σ i) δ δc)
  v₂ = unit-section τ₂ (λ i → ⟦ σ i ⟧ty δ) (λ i → unit-section (σ i) δ δc)
preserves-subst-fwd σ (τ₁ [×] τ₂) {δ} δc =
  preserves-Lf-map {c = prod-section u₁ u₂} {d = prod-section v₁ v₂}
    (preserves-prod-m (preserves-subst-fwd σ τ₁ δc) (preserves-subst-fwd σ τ₂ δc))
  where
  u₁ = unit-section (sub σ τ₁) δ δc
  u₂ = unit-section (sub σ τ₂) δ δc
  v₁ = unit-section τ₁ (λ i → ⟦ σ i ⟧ty δ) (λ i → unit-section (σ i) δ δc)
  v₂ = unit-section τ₂ (λ i → ⟦ σ i ⟧ty δ) (λ i → unit-section (σ i) δ δc)
preserves-subst-fwd σ (τ₁ [→] τ₂) δc = preserves-section-id (Lf-section exp-section)
preserves-subst-fwd {Δ} {Δ'} σ (μ τ) {δ} δc =
  preserves-μ-map (as-poly {Δ'} {1} (sub (sub-lift σ) τ) δ) δ∅
    (as-poly {Δ} {1} τ (λ i → ⟦ σ i ⟧ty δ)) δ∅
    (λ ()) (λ ())
    (as-poly-section {Δ'} {1} (sub (sub-lift σ) τ) δ δc)
    (as-poly-section {Δ} {1} τ (λ i → ⟦ σ i ⟧ty δ) (λ i → unit-section (σ i) δ δc))
    (subst-fwd-body σ τ δ M)
    (preserves-section-∘
      (preserves-section-∘
        (preserves-section-∘
          (preserves-apply-fwd {n = 1} τ (λ i → unit-section (σ i) δ δc)
            (extend-section (λ ()) μM))
          (preserves-as-poly-map τ (λ i → preserves-sub-lift-pw σ δc μM i) δ∅ (λ ())))
        (preserves-subst-fwd (sub-lift σ) τ
          (concat-section {n = 1} (extend-section (λ ()) μM) δc)))
      (preserves-apply-bwd {n = 1} (sub (sub-lift σ) τ) δc (extend-section (λ ()) μM)))
  where
  M  = μ-obj (as-poly {Δ} {1} τ (λ i → ⟦ σ i ⟧ty δ)) δ∅
  μM = unit-section (μ τ) (λ i → ⟦ σ i ⟧ty δ) (λ i → unit-section (σ i) δ δc)

push-pw : ∀ (τ' : type 0) (i : Fin 1) → ⟦ push τ' i ⟧ty (λ ()) ≡ concat (extend {0} δ∅ (⟦ τ' ⟧ty (λ ()))) (λ ()) i
push-pw τ' Fin.zero = refl

private
  ∅ : Fin 0 → obj
  ∅ = λ ()

  strong-env-pw-natural : ∀ {Δ n} {Γ' : Obj} {δ δ' : Fin Δ → obj} (ks : ∀ i → prod Γ' (δ i) ⇒ δ' i)
                          {δ₀ δ₀' : Fin n → obj} (hs : ∀ i → prod Γ' (δ₀ i) ⇒ δ₀' i)
                          {X X' : obj} (kc : prod Γ' X ⇒ X') (i : Fin (suc (n + Δ))) →
                          (strong-concat-mor (strong-extend-mor hs kc) ks i ∘co (≡-to-⇒ (env-pw δ δ₀ X i) ∘ p₂))
                            ≈ ((≡-to-⇒ (env-pw δ' δ₀' X' i) ∘ p₂)
                               ∘co strong-concat-mor {n = 1} (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ j → p₂) kc) (strong-concat-mor hs ks) i)
  strong-env-pw-natural ks hs kc Fin.zero = ≈-trans (co-unitᵣ kc) (≈-sym (co-unitₗ kc))
  strong-env-pw-natural {Δ} {n} {δ = δ} {δ'} ks {δ₀} {δ₀'} hs {X} {X'} kc (Fin.suc j) = go (splitAt n j)
    where
    go : (s : Fin n ⊎ Fin Δ) →
         (strong-concat-mor-split (strong-extend-mor hs kc) ks (map₁ Fin.suc s) ∘co (≡-to-⇒ (env-pw-suc δ δ₀ X s) ∘ p₂))
           ≈ ((≡-to-⇒ (env-pw-suc δ' δ₀' X' s) ∘ p₂) ∘co strong-concat-mor-split hs ks s)
    go (inj₁ l) = ≈-trans (co-unitᵣ (hs l)) (≈-sym (co-unitₗ (hs l)))
    go (inj₂ l) = ≈-trans (co-unitᵣ (ks l)) (≈-sym (co-unitₗ (ks l)))

mutual
  strong-apply-fwd-natural : ∀ {Δ n} (τ : type (n + Δ)) {Γ' : Obj} {δ δ' : Fin Δ → obj}
    (ks : ∀ i → prod Γ' (δ i) ⇒ δ' i) {δ₀ δ₀' : Fin n → obj} (hs : ∀ i → prod Γ' (δ₀ i) ⇒ δ₀' i) →
    (strong-fmor (as-poly {Δ} {n} τ δ') hs
       ∘co (strong-as-poly-map τ ks δ₀ ∘co (apply-fwd τ δ δ₀ ∘ p₂)))
      ≈ ((apply-fwd τ δ' δ₀' ∘ p₂) ∘co strong-as-poly-map τ (strong-concat-mor hs ks) δ∅)
  strong-apply-fwd-natural {n = n} (var i) ks hs with splitAt n i
  ... | inj₁ j = ≈-trans (∘-cong ≈-refl (pair-cong ≈-refl (pair-p₂ _ _)))
                 (≈-trans (co-unitᵣ (hs j)) (≈-sym (co-unitₗ (hs j))))
  ... | inj₂ k = ≈-trans (pair-p₂ _ _) (≈-trans (co-unitᵣ (ks k)) (≈-sym (co-unitₗ (ks k))))
  strong-apply-fwd-natural unit ks hs =
    ≈-trans (pair-p₂ _ _) (≈-trans (pair-p₂ _ _) (≈-sym (≈-trans (∘-cong ≈-refl pair-ext0) id-right)))
  strong-apply-fwd-natural (base s) ks hs =
    ≈-trans (pair-p₂ _ _) (≈-trans (pair-p₂ _ _) (≈-sym (≈-trans (∘-cong ≈-refl pair-ext0) id-right)))
  strong-apply-fwd-natural (σ [→] τ₂) ks hs =
    ≈-trans (pair-p₂ _ _) (≈-trans (pair-p₂ _ _) (≈-sym (≈-trans (∘-cong ≈-refl pair-ext0) id-right)))
  strong-apply-fwd-natural {Δ} {n} (σ [+] τ₂) {Γ'} {δ} {δ'} ks {δ₀} {δ₀'} hs =
    ≈-trans (coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl (≈-sym (scopair-weaken (Lf-map fσ) (Lf-map fτ)))))
    (≈-trans (coKl.∘-cong ≈-refl (copair-comp _ _ _ _))
    (≈-trans (copair-comp _ _ _ _)
    (≈-trans (scopair-cong (∘-cong ≈-refl comp₁) (∘-cong ≈-refl comp₂))
             (≈-sym rhs-eq))))
    where
    fσ  = apply-fwd σ δ δ₀
    fτ  = apply-fwd τ₂ δ δ₀
    fσ' = apply-fwd σ δ' δ₀'
    fτ' = apply-fwd τ₂ δ' δ₀'
    comp₁ = ≈-trans (coKl.∘-cong ≈-refl (≈-trans (coKl.∘-cong ≈-refl (≈-sym (sL-weaken fσ)))
                                                (strong-Lf-map-comp _ _)))
            (≈-trans (strong-Lf-map-comp _ _)
            (≈-trans (strong-Lf-map-cong (strong-apply-fwd-natural σ ks hs))
            (≈-trans (strong-Lf-map-cong (lift-post fσ' _))
                     (≈-sym (strong-Lf-map-post fσ' _)))))
    comp₂ = ≈-trans (coKl.∘-cong ≈-refl (≈-trans (coKl.∘-cong ≈-refl (≈-sym (sL-weaken fτ)))
                                                (strong-Lf-map-comp _ _)))
            (≈-trans (strong-Lf-map-comp _ _)
            (≈-trans (strong-Lf-map-cong (strong-apply-fwd-natural τ₂ ks hs))
            (≈-trans (strong-Lf-map-cong (lift-post fτ' _))
                     (≈-sym (strong-Lf-map-post fτ' _)))))
    rhs-eq =
      ≈-trans (lift-post (coprod-m (Lf-map fσ') (Lf-map fτ')) _)
      (≈-trans (scopair-post (coprod-m (Lf-map fσ') (Lf-map fτ')) _ _)
               (scopair-cong (head-cong-assoc (copair-in₁ _ _))
                             (head-cong-assoc (copair-in₂ _ _))))
  strong-apply-fwd-natural {Δ} {n} (σ [×] τ₂) {Γ'} {δ} {δ'} ks {δ₀} {δ₀'} hs =
    ≈-trans (coKl.∘-cong ≈-refl (≈-trans (coKl.∘-cong ≈-refl (≈-sym (sL-weaken (prod-m fσ fτ))))
                                        (strong-Lf-map-comp _ _)))
    (≈-trans (strong-Lf-map-comp _ _)
    (≈-trans (strong-Lf-map-cong inner)
    (≈-trans (≈-sym (strong-Lf-map-post (prod-m fσ' fτ') _))
             (≈-sym (lift-post (Lf-map (prod-m fσ' fτ')) _)))))
    where
    fσ  = apply-fwd σ δ δ₀
    fτ  = apply-fwd τ₂ δ δ₀
    fσ' = apply-fwd σ δ' δ₀'
    fτ' = apply-fwd τ₂ δ' δ₀'
    SAMσ' = strong-as-poly-map σ (strong-concat-mor hs ks) δ∅
    SAMτ' = strong-as-poly-map τ₂ (strong-concat-mor hs ks) δ∅
    inner = ≈-trans (coKl.∘-cong ≈-refl (≈-trans (coKl.∘-cong ≈-refl (≈-sym (prod-m-weaken fσ fτ)))
                                                (strong-prod-m-comp _ _ _ _)))
            (≈-trans (strong-prod-m-comp _ _ _ _)
            (≈-trans (strong-prod-m-cong
                       (≈-trans (strong-apply-fwd-natural σ ks hs) (lift-post fσ' _))
                       (≈-trans (strong-apply-fwd-natural τ₂ ks hs) (lift-post fτ' _)))
                     (≈-sym (strong-prod-m-post fσ' fτ' SAMσ' SAMτ'))))
  strong-apply-fwd-natural {Δ} {n} (μ τ₂) {Γ'} {δ} {δ'} ks {δ₀} {δ₀'} hs = main
    where
    A   = as-poly {Δ} {suc n} τ₂ δ
    A'  = as-poly {Δ} {suc n} τ₂ δ'
    P   = as-poly {n + Δ} {1} τ₂ (concat δ₀ δ)
    P'' = as-poly {n + Δ} {1} τ₂ (concat δ₀' δ')
    MA' = μ-obj A' δ₀
    Mf  = μ-obj A' δ₀'
    bodyMA = apply-fwd-body τ₂ δ δ₀ (μ-obj A δ₀)
    body'  = apply-fwd-body τ₂ δ δ₀ MA'
    body'' = apply-fwd-body τ₂ δ δ₀ Mf
    bodyf  = apply-fwd-body τ₂ δ' δ₀' Mf
    μm   = μ-map P δ∅ A δ₀ bodyMA
    μm'' = μ-map P'' δ∅ A' δ₀' bodyf
    SFμ   : prod Γ' (μ-obj A' δ₀) ⇒ μ-obj A' δ₀'
    SFμ   = strong-fmor (as-poly {Δ} {n} (μ τ₂) δ') hs
    SAMμ  : prod Γ' (μ-obj A δ₀) ⇒ μ-obj A' δ₀
    SAMμ  = strong-as-poly-map {Δ} {n} (μ τ₂) ks δ₀
    SAMμP : prod Γ' (μ-obj P δ∅) ⇒ μ-obj P'' δ∅
    SAMμP = strong-as-poly-map (μ τ₂) (strong-concat-mor hs ks) δ∅
    algPA : prod Γ' (fobj μ-obj P (extend δ∅ (μ-obj A δ₀))) ⇒ μ-obj A δ₀
    algPA = (inMap A δ₀ ∘ bodyMA) ∘ p₂
    SAM-A-X   = strong-as-poly-map {Δ} {suc n} τ₂ ks (extend δ₀ MA')
    SAM-A-Mf  = strong-as-poly-map {Δ} {suc n} τ₂ ks (extend δ₀ Mf)
    SF-A'-ext = strong-fmor A' (strong-extend-mor hs (p₂ {Γ'} {Mf}))
    algM : prod Γ' (fobj μ-obj P (extend δ∅ MA')) ⇒ MA'
    algM = (inMap A' δ₀ ∘ SAM-A-X) ∘co (body' ∘ p₂)
    alg⋆ : prod Γ' (fobj μ-obj P (extend δ∅ Mf)) ⇒ Mf
    alg⋆ = (inMap A' δ₀' ∘ SF-A'-ext) ∘co (SAM-A-Mf ∘co (body'' ∘ p₂))
    SAM-P-Mf = strong-as-poly-map {n + Δ} {1} τ₂ (strong-concat-mor hs ks) (extend δ∅ Mf)
    SAM-P-MP = strong-as-poly-map {n + Δ} {1} τ₂ (strong-concat-mor hs ks) (extend δ∅ (μ-obj P'' δ∅))
    algP  = inMap P'' δ∅ ∘ SAM-P-MP
    cataB : prod Γ' (μ-obj P'' δ∅) ⇒ Mf
    cataB = ⦅_⦆ {P = P''} {δ = δ∅} ((inMap A' δ₀' ∘ bodyf) ∘ p₂)

    collapse-Pʳ : ∀ {C : obj} {Z : obj} (w : prod Γ' (fobj μ-obj P (extend δ∅ C)) ⇒ Z) →
                  (w ∘co strong-as-poly-map {n + Δ} {1} τ₂ (strong-concat-mor {δ₀ = δ₀} {δ₀' = δ₀} {δ = δ} {δ' = δ} (λ i → p₂) (λ i → p₂)) (extend δ∅ C)) ≈ w
    collapse-Pʳ {C = C} w =
      ≈-trans (coKl.∘-cong ≈-refl (≈-trans (strong-as-poly-map-cong {n + Δ} {1} τ₂ (λ i → strong-concat-mor-p₂ {δ₀ = δ₀} {δ = δ} i) (extend δ∅ C))
                                          (strong-as-poly-map-p₂ {n + Δ} {1} τ₂ (extend δ∅ C))))
              coKl.id-right

    premL2 : (SAMμ ∘co algPA) ≈ (algM ∘co strong-fmor P (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) SAMμ))
    premL2 = begin
        SAMμ ∘co ((inMap A δ₀ ∘ bodyMA) ∘ p₂)
      ≈⟨ coKl.∘-cong ≈-refl (assoc _ _ _) ⟩
        SAMμ ∘co (inMap A δ₀ ∘ (bodyMA ∘ p₂))
      ≈˘⟨ ∘co-push SAMμ (inMap A δ₀) (bodyMA ∘ p₂) ⟩
        (SAMμ ∘co (inMap A δ₀ ∘ p₂)) ∘co (bodyMA ∘ p₂)
      ≈⟨ coKl.∘-cong (⦅⦆-β {P = A} {δ = δ₀} (inMap A' δ₀ ∘ SAM-A-X)) ≈-refl ⟩
        ((inMap A' δ₀ ∘ SAM-A-X) ∘co strong-fmor A (strong-extend-mor {δ = δ₀} {δ' = δ₀} (λ i → p₂) SAMμ)) ∘co (bodyMA ∘ p₂)
      ≈⟨ coKl.assoc _ _ _ ⟩
        (inMap A' δ₀ ∘ SAM-A-X) ∘co (strong-fmor A (strong-extend-mor {δ = δ₀} {δ' = δ₀} (λ i → p₂) SAMμ) ∘co (bodyMA ∘ p₂))
      ≈˘⟨ coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl (≈-trans (coKl.∘-cong (strong-as-poly-map-p₂ {n = suc n} τ₂ {δ = δ} (extend δ₀ (μ-obj A δ₀))) ≈-refl) coKl.id-left)) ⟩
        (inMap A' δ₀ ∘ SAM-A-X) ∘co (strong-fmor A (strong-extend-mor {δ = δ₀} {δ' = δ₀} (λ i → p₂) SAMμ)
          ∘co (strong-as-poly-map {Δ} {suc n} τ₂ {δ = δ} {δ' = δ} (λ i → p₂) (extend δ₀ (μ-obj A δ₀)) ∘co (bodyMA ∘ p₂)))
      ≈⟨ coKl.∘-cong ≈-refl (strong-apply-fwd-body-natural τ₂ {δ = δ} {δ' = δ} (λ i → p₂) {δ₀ = δ₀} {δ₀' = δ₀} (λ i → p₂) SAMμ) ⟩
        (inMap A' δ₀ ∘ SAM-A-X) ∘co ((body' ∘ p₂)
          ∘co (strong-fmor P (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) SAMμ)
               ∘co strong-as-poly-map {n + Δ} {1} τ₂ (strong-concat-mor {δ₀ = δ₀} {δ₀' = δ₀} {δ = δ} {δ' = δ} (λ i → p₂) (λ i → p₂)) (extend δ∅ (μ-obj A δ₀))))
      ≈⟨ coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl (collapse-Pʳ (strong-fmor P (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) SAMμ)))) ⟩
        (inMap A' δ₀ ∘ SAM-A-X) ∘co ((body' ∘ p₂) ∘co strong-fmor P (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) SAMμ))
      ≈˘⟨ coKl.assoc _ _ _ ⟩
        ((inMap A' δ₀ ∘ SAM-A-X) ∘co (body' ∘ p₂)) ∘co strong-fmor P (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) SAMμ)
      ∎
      where open ≈-Reasoning isEquiv

    premL3 : (SFμ ∘co algM) ≈ (alg⋆ ∘co strong-fmor P (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) SFμ))
    premL3 = begin
        SFμ ∘co ((inMap A' δ₀ ∘ SAM-A-X) ∘co (body' ∘ p₂))
      ≈˘⟨ coKl.assoc _ _ _ ⟩
        (SFμ ∘co (inMap A' δ₀ ∘ SAM-A-X)) ∘co (body' ∘ p₂)
      ≈˘⟨ coKl.∘-cong (∘co-push SFμ (inMap A' δ₀) SAM-A-X) ≈-refl ⟩
        ((SFμ ∘co (inMap A' δ₀ ∘ p₂)) ∘co SAM-A-X) ∘co (body' ∘ p₂)
      ≈⟨ coKl.∘-cong (coKl.∘-cong (⦅⦆-β {P = A'} {δ = δ₀} (inMap A' δ₀' ∘ SF-A'-ext)) ≈-refl) ≈-refl ⟩
        (((inMap A' δ₀' ∘ SF-A'-ext) ∘co strong-fmor A' (strong-extend-mor {δ = δ₀} {δ' = δ₀} (λ i → p₂) SFμ)) ∘co SAM-A-X) ∘co (body' ∘ p₂)
      ≈⟨ coKl.∘-cong (coKl.assoc _ _ _) ≈-refl ⟩
        ((inMap A' δ₀' ∘ SF-A'-ext) ∘co (strong-fmor A' (strong-extend-mor {δ = δ₀} {δ' = δ₀} (λ i → p₂) SFμ) ∘co SAM-A-X)) ∘co (body' ∘ p₂)
      ≈⟨ coKl.∘-cong (coKl.∘-cong ≈-refl (strong-as-poly-map-natural {n = suc n} τ₂ ks (strong-extend-mor {δ = δ₀} {δ' = δ₀} (λ i → p₂) SFμ))) ≈-refl ⟩
        ((inMap A' δ₀' ∘ SF-A'-ext) ∘co (SAM-A-Mf ∘co strong-fmor A (strong-extend-mor {δ = δ₀} {δ' = δ₀} (λ i → p₂) SFμ))) ∘co (body' ∘ p₂)
      ≈⟨ coKl.assoc _ _ _ ⟩
        (inMap A' δ₀' ∘ SF-A'-ext) ∘co ((SAM-A-Mf ∘co strong-fmor A (strong-extend-mor {δ = δ₀} {δ' = δ₀} (λ i → p₂) SFμ)) ∘co (body' ∘ p₂))
      ≈⟨ coKl.∘-cong ≈-refl (coKl.assoc _ _ _) ⟩
        (inMap A' δ₀' ∘ SF-A'-ext) ∘co (SAM-A-Mf ∘co (strong-fmor A (strong-extend-mor {δ = δ₀} {δ' = δ₀} (λ i → p₂) SFμ) ∘co (body' ∘ p₂)))
      ≈˘⟨ coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl (≈-trans (coKl.∘-cong (strong-as-poly-map-p₂ {n = suc n} τ₂ {δ = δ} (extend δ₀ MA')) ≈-refl) coKl.id-left))) ⟩
        (inMap A' δ₀' ∘ SF-A'-ext) ∘co (SAM-A-Mf ∘co (strong-fmor A (strong-extend-mor {δ = δ₀} {δ' = δ₀} (λ i → p₂) SFμ)
          ∘co (strong-as-poly-map {Δ} {suc n} τ₂ {δ = δ} {δ' = δ} (λ i → p₂) (extend δ₀ MA') ∘co (body' ∘ p₂))))
      ≈⟨ coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl (strong-apply-fwd-body-natural τ₂ {δ = δ} {δ' = δ} (λ i → p₂) {δ₀ = δ₀} {δ₀' = δ₀} (λ i → p₂) SFμ)) ⟩
        (inMap A' δ₀' ∘ SF-A'-ext) ∘co (SAM-A-Mf ∘co ((body'' ∘ p₂)
          ∘co (strong-fmor P (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) SFμ)
               ∘co strong-as-poly-map {n + Δ} {1} τ₂ (strong-concat-mor {δ₀ = δ₀} {δ₀' = δ₀} {δ = δ} {δ' = δ} (λ i → p₂) (λ i → p₂)) (extend δ∅ MA'))))
      ≈⟨ coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl (collapse-Pʳ (strong-fmor P (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) SFμ))))) ⟩
        (inMap A' δ₀' ∘ SF-A'-ext) ∘co (SAM-A-Mf ∘co ((body'' ∘ p₂) ∘co strong-fmor P (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) SFμ)))
      ≈˘⟨ coKl.∘-cong ≈-refl (coKl.assoc _ _ _) ⟩
        (inMap A' δ₀' ∘ SF-A'-ext) ∘co ((SAM-A-Mf ∘co (body'' ∘ p₂)) ∘co strong-fmor P (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) SFμ))
      ≈˘⟨ coKl.assoc _ _ _ ⟩
        ((inMap A' δ₀' ∘ SF-A'-ext) ∘co (SAM-A-Mf ∘co (body'' ∘ p₂))) ∘co strong-fmor P (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) SFμ)
      ∎
      where open ≈-Reasoning isEquiv

    alg-eq : (((inMap A' δ₀' ∘ bodyf) ∘ p₂) ∘co SAM-P-Mf) ≈ alg⋆
    alg-eq = ≈-sym (begin
        (inMap A' δ₀' ∘ SF-A'-ext) ∘co (SAM-A-Mf ∘co (body'' ∘ p₂))
      ≈⟨ assoc _ _ _ ⟩
        inMap A' δ₀' ∘ (SF-A'-ext ∘co (SAM-A-Mf ∘co (body'' ∘ p₂)))
      ≈⟨ ∘-cong ≈-refl (strong-apply-fwd-body-natural τ₂ ks hs (p₂ {Γ'} {Mf})) ⟩
        inMap A' δ₀' ∘ ((bodyf ∘ p₂)
          ∘co (strong-fmor P'' (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) (p₂ {Γ'} {Mf})) ∘co SAM-P-Mf))
      ≈⟨ ∘-cong ≈-refl (coKl.∘-cong ≈-refl (≈-trans (coKl.∘-cong (≈-trans (strong-fmor-cong P'' eqP) (strong-fmor-p₂ P'')) ≈-refl) coKl.id-left)) ⟩
        inMap A' δ₀' ∘ ((bodyf ∘ p₂) ∘co SAM-P-Mf)
      ≈⟨ ∘-cong ≈-refl (lift-post bodyf SAM-P-Mf) ⟩
        inMap A' δ₀' ∘ (bodyf ∘ SAM-P-Mf)
      ≈˘⟨ assoc _ _ _ ⟩
        (inMap A' δ₀' ∘ bodyf) ∘ SAM-P-Mf
      ≈˘⟨ lift-post (inMap A' δ₀' ∘ bodyf) SAM-P-Mf ⟩
        ((inMap A' δ₀' ∘ bodyf) ∘ p₂) ∘co SAM-P-Mf
      ∎)
      where
      open ≈-Reasoning isEquiv
      eqP : ∀ i → strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ j → p₂) (p₂ {Γ'} {Mf}) i ≈ p₂
      eqP Fin.zero    = ≈-refl
      eqP (Fin.suc ())

    premR : (cataB ∘co algP) ≈ (alg⋆ ∘co strong-fmor P (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) cataB))
    premR = begin
        cataB ∘co (inMap P'' δ∅ ∘ SAM-P-MP)
      ≈˘⟨ ∘co-push cataB (inMap P'' δ∅) SAM-P-MP ⟩
        (cataB ∘co (inMap P'' δ∅ ∘ p₂)) ∘co SAM-P-MP
      ≈⟨ coKl.∘-cong (⦅⦆-β {P = P''} {δ = δ∅} ((inMap A' δ₀' ∘ bodyf) ∘ p₂)) ≈-refl ⟩
        ((((inMap A' δ₀' ∘ bodyf) ∘ p₂) ∘co strong-fmor P'' (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) cataB)) ∘co SAM-P-MP)
      ≈⟨ coKl.assoc _ _ _ ⟩
        (((inMap A' δ₀' ∘ bodyf) ∘ p₂) ∘co (strong-fmor P'' (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) cataB) ∘co SAM-P-MP))
      ≈⟨ coKl.∘-cong ≈-refl (strong-as-poly-map-natural {n = 1} τ₂ (strong-concat-mor hs ks) (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) cataB)) ⟩
        (((inMap A' δ₀' ∘ bodyf) ∘ p₂) ∘co (SAM-P-Mf ∘co strong-fmor P (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) cataB)))
      ≈˘⟨ coKl.assoc _ _ _ ⟩
        ((((inMap A' δ₀' ∘ bodyf) ∘ p₂) ∘co SAM-P-Mf) ∘co strong-fmor P (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) cataB))
      ≈⟨ coKl.∘-cong alg-eq ≈-refl ⟩
        alg⋆ ∘co strong-fmor P (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) cataB)
      ∎
      where open ≈-Reasoning isEquiv

    main : (SFμ ∘co (SAMμ ∘co (μm ∘ p₂))) ≈ ((μm'' ∘ p₂) ∘co SAMμP)
    main = begin
        SFμ ∘co (SAMμ ∘co (μm ∘ p₂))
      ≈˘⟨ coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl (μ-map-weaken P δ∅ A δ₀ bodyMA)) ⟩
        SFμ ∘co (SAMμ ∘co ⦅_⦆ {P = P} {δ = δ∅} algPA)
      ≈⟨ coKl.∘-cong ≈-refl (fusion {P = P} {δ = δ∅} algPA algM SAMμ premL2) ⟩
        SFμ ∘co ⦅_⦆ {P = P} {δ = δ∅} algM
      ≈⟨ fusion {P = P} {δ = δ∅} algM alg⋆ SFμ premL3 ⟩
        ⦅_⦆ {P = P} {δ = δ∅} alg⋆
      ≈˘⟨ fusion {P = P} {δ = δ∅} algP alg⋆ cataB premR ⟩
        cataB ∘co SAMμP
      ≈⟨ coKl.∘-cong (μ-map-weaken P'' δ∅ A' δ₀' bodyf) ≈-refl ⟩
        (μm'' ∘ p₂) ∘co SAMμP
      ∎
      where open ≈-Reasoning isEquiv

  strong-apply-bwd-natural : ∀ {Δ n} (τ : type (n + Δ)) {Γ' : Obj} {δ δ' : Fin Δ → obj}
    (ks : ∀ i → prod Γ' (δ i) ⇒ δ' i) {δ₀ δ₀' : Fin n → obj} (hs : ∀ i → prod Γ' (δ₀ i) ⇒ δ₀' i) →
    (strong-as-poly-map τ (strong-concat-mor hs ks) δ∅ ∘co (apply-bwd τ δ δ₀ ∘ p₂))
      ≈ ((apply-bwd τ δ' δ₀' ∘ p₂)
         ∘co (strong-fmor (as-poly {Δ} {n} τ δ') hs ∘co strong-as-poly-map τ ks δ₀))
  strong-apply-bwd-natural τ {δ = δ} {δ'} ks {δ₀} {δ₀'} hs =
    ≈-trans (≈-sym coKl.id-left)
    (≈-trans (coKl.∘-cong (≈-sym iso-fact) ≈-refl)
    (≈-trans (coKl.assoc _ _ _)
    (≈-trans (coKl.∘-cong ≈-refl (≈-sym (coKl.assoc _ _ _)))
    (≈-trans (coKl.∘-cong ≈-refl (coKl.∘-cong (≈-sym (strong-apply-fwd-natural τ ks hs)) ≈-refl))
    (≈-trans (coKl.∘-cong ≈-refl (coKl.assoc _ _ _))
    (≈-trans (coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl (coKl.assoc _ _ _)))
    (≈-trans (coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl fwd-bwd-fact)))
             (coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl coKl.id-right)))))))))
    where
    iso-fact : ((apply-bwd τ δ' δ₀' ∘ p₂) ∘co (apply-fwd τ δ' δ₀' ∘ p₂)) ≈ p₂
    iso-fact = ≈-trans (≈-sym (lift-comp _ _)) (≈-trans (∘-cong (apply-bwd-fwd τ δ' δ₀') ≈-refl) id-left)
    fwd-bwd-fact : ((apply-fwd τ δ δ₀ ∘ p₂) ∘co (apply-bwd τ δ δ₀ ∘ p₂)) ≈ p₂
    fwd-bwd-fact = ≈-trans (≈-sym (lift-comp _ _)) (≈-trans (∘-cong (apply-fwd-bwd τ δ δ₀) ≈-refl) id-left)

  strong-apply-fwd-body-natural : ∀ {Δ n} (τ : type (suc n + Δ)) {Γ' : Obj} {δ δ' : Fin Δ → obj}
    (ks : ∀ i → prod Γ' (δ i) ⇒ δ' i) {δ₀ δ₀' : Fin n → obj} (hs : ∀ i → prod Γ' (δ₀ i) ⇒ δ₀' i)
    {X X' : obj} (kc : prod Γ' X ⇒ X') →
    (strong-fmor (as-poly {Δ} {suc n} τ δ') (strong-extend-mor hs kc)
       ∘co (strong-as-poly-map {Δ} {suc n} τ ks (extend δ₀ X) ∘co (apply-fwd-body τ δ δ₀ X ∘ p₂)))
      ≈ ((apply-fwd-body τ δ' δ₀' X' ∘ p₂)
         ∘co (strong-fmor (as-poly {n + Δ} {1} τ (concat δ₀' δ')) (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) kc)
              ∘co strong-as-poly-map {n + Δ} {1} τ (strong-concat-mor hs ks) (extend δ∅ X)))
  strong-apply-fwd-body-natural {Δ} {n} τ {Γ'} {δ} {δ'} ks {δ₀} {δ₀'} hs {X} {X'} kc = main
    where
    SF    = strong-fmor (as-poly {Δ} {suc n} τ δ') (strong-extend-mor hs kc)
    SAM-X = strong-as-poly-map {Δ} {suc n} τ ks (extend δ₀ X)
    af   = apply-fwd τ δ (extend δ₀ X)
    af'  = apply-fwd τ δ' (extend δ₀' X')
    Rs   = as-poly-map τ (λ i → ≡-to-⇒ (env-pw δ δ₀ X i)) δ∅
    Rs'  = as-poly-map τ (λ i → ≡-to-⇒ (env-pw δ' δ₀' X' i)) δ∅
    ab   = apply-bwd {n = 1} τ (concat δ₀ δ) (extend δ∅ X)
    ab'  = apply-bwd {n = 1} τ (concat δ₀' δ') (extend δ∅ X')
    af₁  = apply-fwd {n = 1} τ (concat δ₀ δ) (extend δ∅ X)
    af₁' = apply-fwd {n = 1} τ (concat δ₀' δ') (extend δ∅ X')
    F₁ = strong-concat-mor {n = 1} (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ j → p₂) kc) (strong-concat-mor hs ks)
    SAM-1 = strong-as-poly-map τ F₁ δ∅
    SF-P' = strong-fmor (as-poly {n + Δ} {1} τ (concat δ₀' δ')) (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) kc)
    SAM-P = strong-as-poly-map {n + Δ} {1} τ (strong-concat-mor hs ks) (extend δ∅ X)
    SAM-full = strong-as-poly-map τ (strong-concat-mor (strong-extend-mor hs kc) ks) δ∅
    cast-step : (SAM-full ∘co (Rs ∘ p₂)) ≈ ((Rs' ∘ p₂) ∘co SAM-1)
    cast-step =
      strong-as-poly-map-square τ (λ i → ≡-to-⇒ (env-pw δ δ₀ X i)) (λ i → ≡-to-⇒ (env-pw δ' δ₀' X' i)) F₁
                                (strong-concat-mor (strong-extend-mor hs kc) ks) δ∅ (strong-env-pw-natural ks hs kc)
    ab-step : (SAM-1 ∘co (ab ∘ p₂)) ≈ ((ab' ∘ p₂) ∘co (SF-P' ∘co SAM-P))
    ab-step =
      strong-apply-bwd-natural {n = 1} τ (strong-concat-mor hs ks)
                               (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ j → p₂) kc)

    main : (SF ∘co (SAM-X ∘co (((af ∘ Rs) ∘ ab) ∘ p₂))) ≈ ((((af' ∘ Rs') ∘ ab') ∘ p₂) ∘co (SF-P' ∘co SAM-P))
    main = begin
        SF ∘co (SAM-X ∘co (((af ∘ Rs) ∘ ab) ∘ p₂))
      ≈⟨ coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl (≈-trans (lift-comp (af ∘ Rs) ab) (coKl.∘-cong (lift-comp af Rs) ≈-refl))) ⟩
        SF ∘co (SAM-X ∘co (((af ∘ p₂) ∘co (Rs ∘ p₂)) ∘co (ab ∘ p₂)))
      ≈⟨ coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl (coKl.assoc _ _ _)) ⟩
        SF ∘co (SAM-X ∘co ((af ∘ p₂) ∘co ((Rs ∘ p₂) ∘co (ab ∘ p₂))))
      ≈˘⟨ coKl.∘-cong ≈-refl (coKl.assoc _ _ _) ⟩
        SF ∘co ((SAM-X ∘co (af ∘ p₂)) ∘co ((Rs ∘ p₂) ∘co (ab ∘ p₂)))
      ≈˘⟨ coKl.assoc _ _ _ ⟩
        (SF ∘co (SAM-X ∘co (af ∘ p₂))) ∘co ((Rs ∘ p₂) ∘co (ab ∘ p₂))
      ≈⟨ coKl.∘-cong (strong-apply-fwd-natural {n = suc n} τ ks (strong-extend-mor hs kc)) ≈-refl ⟩
        ((af' ∘ p₂) ∘co SAM-full) ∘co ((Rs ∘ p₂) ∘co (ab ∘ p₂))
      ≈⟨ coKl.assoc _ _ _ ⟩
        (af' ∘ p₂) ∘co (SAM-full ∘co ((Rs ∘ p₂) ∘co (ab ∘ p₂)))
      ≈˘⟨ coKl.∘-cong ≈-refl (coKl.assoc _ _ _) ⟩
        (af' ∘ p₂) ∘co ((SAM-full ∘co (Rs ∘ p₂)) ∘co (ab ∘ p₂))
      ≈⟨ coKl.∘-cong ≈-refl (coKl.∘-cong cast-step ≈-refl) ⟩
        (af' ∘ p₂) ∘co (((Rs' ∘ p₂) ∘co SAM-1) ∘co (ab ∘ p₂))
      ≈⟨ coKl.∘-cong ≈-refl (coKl.assoc _ _ _) ⟩
        (af' ∘ p₂) ∘co ((Rs' ∘ p₂) ∘co (SAM-1 ∘co (ab ∘ p₂)))
      ≈⟨ coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl ab-step) ⟩
        (af' ∘ p₂) ∘co ((Rs' ∘ p₂) ∘co ((ab' ∘ p₂) ∘co (SF-P' ∘co SAM-P)))
      ≈˘⟨ coKl.∘-cong ≈-refl (coKl.assoc _ _ _) ⟩
        (af' ∘ p₂) ∘co (((Rs' ∘ p₂) ∘co (ab' ∘ p₂)) ∘co (SF-P' ∘co SAM-P))
      ≈˘⟨ coKl.assoc _ _ _ ⟩
        ((af' ∘ p₂) ∘co ((Rs' ∘ p₂) ∘co (ab' ∘ p₂))) ∘co (SF-P' ∘co SAM-P)
      ≈˘⟨ coKl.∘-cong (coKl.∘-cong ≈-refl (lift-comp Rs' ab')) ≈-refl ⟩
        ((af' ∘ p₂) ∘co ((Rs' ∘ ab') ∘ p₂)) ∘co (SF-P' ∘co SAM-P)
      ≈˘⟨ coKl.∘-cong (lift-comp af' (Rs' ∘ ab')) ≈-refl ⟩
        ((af' ∘ (Rs' ∘ ab')) ∘ p₂) ∘co (SF-P' ∘co SAM-P)
      ≈˘⟨ coKl.∘-cong (∘-cong (assoc _ _ _) ≈-refl) ≈-refl ⟩
        (((af' ∘ Rs') ∘ ab') ∘ p₂) ∘co (SF-P' ∘co SAM-P)
      ∎
      where open ≈-Reasoning isEquiv

private
  strong-sub-lift-pw-natural : ∀ {Δ Δ'} (σ : TySub Δ Δ') {Γ' : Obj} {δ δ' : Fin Δ' → obj}
    (gs : ∀ i → prod Γ' (δ i) ⇒ δ' i) {X X' : obj} (kc : prod Γ' X ⇒ X') (i : Fin (suc Δ)) →
    (strong-concat-mor {n = 1} (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ j → p₂) kc) (λ j → strong-as-poly-map (σ j) gs δ∅) i
       ∘co (≡-to-⇒ (sub-lift-pw σ δ X i) ∘ p₂))
      ≈ ((≡-to-⇒ (sub-lift-pw σ δ' X' i) ∘ p₂)
         ∘co strong-as-poly-map (sub-lift σ i)
               (strong-concat-mor {n = 1} (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ j → p₂) kc) gs) δ∅)
  strong-sub-lift-pw-natural σ gs kc Fin.zero    = ≈-trans (co-unitᵣ kc) (≈-sym (co-unitₗ kc))
  strong-sub-lift-pw-natural σ gs kc (Fin.suc j) =
    ≈-sym (strong-as-poly-map-ren {n = 0} Fin.suc (σ j)
             (strong-concat-mor {n = 1} (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) kc) gs) δ∅)

mutual
  strong-subst-fwd-natural : ∀ {Δ Δ'} (σ : TySub Δ Δ') (τ : type Δ) {Γ' : Obj} {δ δ' : Fin Δ' → obj}
    (gs : ∀ i → prod Γ' (δ i) ⇒ δ' i) →
    (strong-as-poly-map τ (λ i → strong-as-poly-map (σ i) gs δ∅) δ∅
       ∘co (subst-fwd σ τ δ ∘ p₂))
      ≈ ((subst-fwd σ τ δ' ∘ p₂) ∘co strong-as-poly-map (sub σ τ) gs δ∅)
  strong-subst-fwd-natural σ (var i) gs =
    ≈-trans (co-unitᵣ (strong-as-poly-map (σ i) gs δ∅)) (≈-sym (co-unitₗ (strong-as-poly-map (σ i) gs δ∅)))
  strong-subst-fwd-natural σ unit gs =
    ≈-trans (pair-p₂ _ _) (≈-sym (≈-trans (∘-cong ≈-refl pair-ext0) id-right))
  strong-subst-fwd-natural σ (base s) gs =
    ≈-trans (pair-p₂ _ _) (≈-sym (≈-trans (∘-cong ≈-refl pair-ext0) id-right))
  strong-subst-fwd-natural σ (τ₁ [→] τ₂) gs =
    ≈-trans (pair-p₂ _ _) (≈-sym (≈-trans (∘-cong ≈-refl pair-ext0) id-right))
  strong-subst-fwd-natural {Δ} {Δ'} σ (τ₁ [+] τ₂) {Γ'} {δ} {δ'} gs =
    ≈-trans (coKl.∘-cong ≈-refl (≈-sym (scopair-weaken (Lf-map f₁) (Lf-map f₂))))
    (≈-trans (copair-comp _ _ _ _)
    (≈-trans (scopair-cong (∘-cong ≈-refl leg₁) (∘-cong ≈-refl leg₂))
             (≈-sym rhs-eq)))
    where
    f₁  = subst-fwd σ τ₁ δ
    f₂  = subst-fwd σ τ₂ δ
    f₁' = subst-fwd σ τ₁ δ'
    f₂' = subst-fwd σ τ₂ δ'
    M₁  = strong-as-poly-map τ₁ (λ i → strong-as-poly-map (σ i) gs δ∅) δ∅
    M₂  = strong-as-poly-map τ₂ (λ i → strong-as-poly-map (σ i) gs δ∅) δ∅
    N₁  = strong-as-poly-map (sub σ τ₁) gs δ∅
    N₂  = strong-as-poly-map (sub σ τ₂) gs δ∅
    leg₁ : (strong-Lf-map M₁ ∘co (Lf-map f₁ ∘ p₂)) ≈ ((Lf-map f₁' ∘ p₂) ∘co strong-Lf-map N₁)
    leg₁ = ≈-trans (coKl.∘-cong ≈-refl (≈-sym (sL-weaken f₁)))
           (≈-trans (strong-Lf-map-comp _ _)
           (≈-trans (strong-Lf-map-cong (strong-subst-fwd-natural σ τ₁ gs))
           (≈-trans (≈-sym (strong-Lf-map-comp _ _))
                    (coKl.∘-cong (sL-weaken f₁') ≈-refl))))
    leg₂ : (strong-Lf-map M₂ ∘co (Lf-map f₂ ∘ p₂)) ≈ ((Lf-map f₂' ∘ p₂) ∘co strong-Lf-map N₂)
    leg₂ = ≈-trans (coKl.∘-cong ≈-refl (≈-sym (sL-weaken f₂)))
           (≈-trans (strong-Lf-map-comp _ _)
           (≈-trans (strong-Lf-map-cong (strong-subst-fwd-natural σ τ₂ gs))
           (≈-trans (≈-sym (strong-Lf-map-comp _ _))
                    (coKl.∘-cong (sL-weaken f₂') ≈-refl))))
    rhs-eq : (([+]-map f₁' f₂' ∘ p₂) ∘co scopair (in₁ ∘ strong-Lf-map N₁) (in₂ ∘ strong-Lf-map N₂))
               ≈ scopair (in₁ ∘ ((Lf-map f₁' ∘ p₂) ∘co strong-Lf-map N₁)) (in₂ ∘ ((Lf-map f₂' ∘ p₂) ∘co strong-Lf-map N₂))
    rhs-eq = ≈-trans (coKl.∘-cong (≈-sym (scopair-weaken (Lf-map f₁') (Lf-map f₂'))) ≈-refl)
                     (copair-comp _ _ _ _)
  strong-subst-fwd-natural {Δ} {Δ'} σ (τ₁ [×] τ₂) {Γ'} {δ} {δ'} gs =
    ≈-trans (coKl.∘-cong ≈-refl (≈-sym (sL-weaken (prod-m f₁ f₂))))
    (≈-trans (strong-Lf-map-comp _ _)
    (≈-trans (strong-Lf-map-cong inner)
    (≈-trans (≈-sym (strong-Lf-map-comp _ _))
             (coKl.∘-cong (sL-weaken (prod-m f₁' f₂')) ≈-refl))))
    where
    f₁  = subst-fwd σ τ₁ δ
    f₂  = subst-fwd σ τ₂ δ
    f₁' = subst-fwd σ τ₁ δ'
    f₂' = subst-fwd σ τ₂ δ'
    M₁  = strong-as-poly-map τ₁ (λ i → strong-as-poly-map (σ i) gs δ∅) δ∅
    M₂  = strong-as-poly-map τ₂ (λ i → strong-as-poly-map (σ i) gs δ∅) δ∅
    N₁  = strong-as-poly-map (sub σ τ₁) gs δ∅
    N₂  = strong-as-poly-map (sub σ τ₂) gs δ∅
    inner : (strong-prod-m M₁ M₂ ∘co (prod-m f₁ f₂ ∘ p₂)) ≈ ((prod-m f₁' f₂' ∘ p₂) ∘co strong-prod-m N₁ N₂)
    inner = ≈-trans (coKl.∘-cong ≈-refl (≈-sym (prod-m-weaken f₁ f₂)))
            (≈-trans (strong-prod-m-comp _ _ _ _)
            (≈-trans (strong-prod-m-cong (strong-subst-fwd-natural σ τ₁ gs) (strong-subst-fwd-natural σ τ₂ gs))
            (≈-trans (≈-sym (strong-prod-m-comp _ _ _ _))
                     (coKl.∘-cong (prod-m-weaken f₁' f₂') ≈-refl))))
  strong-subst-fwd-natural {Δ} {Δ'} σ (μ τ) {Γ'} {δ} {δ'} gs = main
    where
    A  = as-poly {Δ} {1} τ (λ i → ⟦ σ i ⟧ty δ)
    A' = as-poly {Δ} {1} τ (λ i → ⟦ σ i ⟧ty δ')
    P  = as-poly {Δ'} {1} (sub (sub-lift σ) τ) δ
    P' = as-poly {Δ'} {1} (sub (sub-lift σ) τ) δ'
    M  = μ-obj A δ∅
    M' = μ-obj A' δ∅
    N' = μ-obj P' δ∅
    body   = subst-fwd-body σ τ δ M
    bodyM' = subst-fwd-body σ τ δ M'
    body'  = subst-fwd-body σ τ δ' M'
    SAMμ : prod Γ' M ⇒ M'
    SAMμ = strong-as-poly-map {Δ} {0} (μ τ) (λ i → strong-as-poly-map (σ i) gs δ∅) δ∅
    SAMμP : prod Γ' (μ-obj P δ∅) ⇒ N'
    SAMμP = strong-as-poly-map {Δ'} {0} (sub σ (μ τ)) gs δ∅
    SAM-A = strong-as-poly-map {Δ} {1} τ (λ i → strong-as-poly-map (σ i) gs δ∅) (extend δ∅ M')
    SAM-P-M' = strong-as-poly-map {Δ'} {1} (sub (sub-lift σ) τ) gs (extend δ∅ M')
    SAM-P-N' = strong-as-poly-map {Δ'} {1} (sub (sub-lift σ) τ) gs (extend δ∅ N')
    SAM-triv = strong-as-poly-map {Δ} {1} τ (λ i → strong-as-poly-map (σ i) {δ = δ} {δ' = δ} (λ j → p₂) δ∅) (extend δ∅ M)
    SAM-P-triv = strong-as-poly-map {Δ'} {1} (sub (sub-lift σ) τ) {δ = δ} {δ' = δ} (λ i → p₂) (extend δ∅ M)
    cataB : prod Γ' N' ⇒ M'
    cataB = ⦅_⦆ {P = P'} {δ = δ∅} ((inMap A' δ∅ ∘ body') ∘ p₂)
    alg⋆ : prod Γ' (fobj μ-obj P (extend δ∅ M')) ⇒ M'
    alg⋆ = (inMap A' δ∅ ∘ SAM-A) ∘co (bodyM' ∘ p₂)

    collapse-triv : SAM-triv ≈ p₂
    collapse-triv =
      ≈-trans (strong-as-poly-map-cong τ (λ i → strong-as-poly-map-p₂ (σ i) {δ = δ} δ∅) (extend δ∅ M))
              (strong-as-poly-map-p₂ {Δ} {1} τ (extend δ∅ M))

    premL : (SAMμ ∘co ((inMap A δ∅ ∘ body) ∘ p₂))
              ≈ (alg⋆ ∘co strong-fmor P (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) SAMμ))
    premL = begin
        SAMμ ∘co ((inMap A δ∅ ∘ body) ∘ p₂)
      ≈⟨ coKl.∘-cong ≈-refl (assoc _ _ _) ⟩
        SAMμ ∘co (inMap A δ∅ ∘ (body ∘ p₂))
      ≈˘⟨ ∘co-push SAMμ (inMap A δ∅) (body ∘ p₂) ⟩
        (SAMμ ∘co (inMap A δ∅ ∘ p₂)) ∘co (body ∘ p₂)
      ≈⟨ coKl.∘-cong (⦅⦆-β {P = A} {δ = δ∅} (inMap A' δ∅ ∘ SAM-A)) ≈-refl ⟩
        ((inMap A' δ∅ ∘ SAM-A) ∘co strong-fmor A (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) SAMμ)) ∘co (body ∘ p₂)
      ≈⟨ coKl.assoc _ _ _ ⟩
        (inMap A' δ∅ ∘ SAM-A) ∘co (strong-fmor A (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) SAMμ) ∘co (body ∘ p₂))
      ≈˘⟨ coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl (≈-trans (coKl.∘-cong collapse-triv ≈-refl) coKl.id-left)) ⟩
        (inMap A' δ∅ ∘ SAM-A) ∘co (strong-fmor A (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) SAMμ)
          ∘co (SAM-triv ∘co (body ∘ p₂)))
      ≈⟨ coKl.∘-cong ≈-refl (strong-subst-fwd-body-natural σ τ {δ = δ} {δ' = δ} (λ i → p₂) SAMμ) ⟩
        (inMap A' δ∅ ∘ SAM-A) ∘co ((bodyM' ∘ p₂)
          ∘co (strong-fmor P (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) SAMμ) ∘co SAM-P-triv))
      ≈⟨ coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl (≈-trans (coKl.∘-cong ≈-refl (strong-as-poly-map-p₂ {Δ'} {1} (sub (sub-lift σ) τ) {δ = δ} (extend δ∅ M))) coKl.id-right)) ⟩
        (inMap A' δ∅ ∘ SAM-A) ∘co ((bodyM' ∘ p₂) ∘co strong-fmor P (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) SAMμ))
      ≈˘⟨ coKl.assoc _ _ _ ⟩
        ((inMap A' δ∅ ∘ SAM-A) ∘co (bodyM' ∘ p₂)) ∘co strong-fmor P (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) SAMμ)
      ∎
      where open ≈-Reasoning isEquiv

    alg-eq : (((inMap A' δ∅ ∘ body') ∘ p₂) ∘co SAM-P-M') ≈ alg⋆
    alg-eq = ≈-sym (begin
        (inMap A' δ∅ ∘ SAM-A) ∘co (bodyM' ∘ p₂)
      ≈⟨ assoc _ _ _ ⟩
        inMap A' δ∅ ∘ (SAM-A ∘co (bodyM' ∘ p₂))
      ≈˘⟨ ∘-cong ≈-refl (≈-trans (coKl.∘-cong (≈-trans (strong-fmor-cong A' eqP) (strong-fmor-p₂ A')) ≈-refl) coKl.id-left) ⟩
        inMap A' δ∅ ∘ (strong-fmor A' (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) (p₂ {Γ'} {M'}))
          ∘co (SAM-A ∘co (bodyM' ∘ p₂)))
      ≈⟨ ∘-cong ≈-refl (strong-subst-fwd-body-natural σ τ gs (p₂ {Γ'} {M'})) ⟩
        inMap A' δ∅ ∘ ((body' ∘ p₂)
          ∘co (strong-fmor P' (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) (p₂ {Γ'} {M'})) ∘co SAM-P-M'))
      ≈⟨ ∘-cong ≈-refl (coKl.∘-cong ≈-refl (≈-trans (coKl.∘-cong (≈-trans (strong-fmor-cong P' eqP) (strong-fmor-p₂ P')) ≈-refl) coKl.id-left)) ⟩
        inMap A' δ∅ ∘ ((body' ∘ p₂) ∘co SAM-P-M')
      ≈⟨ ∘-cong ≈-refl (lift-post body' SAM-P-M') ⟩
        inMap A' δ∅ ∘ (body' ∘ SAM-P-M')
      ≈˘⟨ assoc _ _ _ ⟩
        (inMap A' δ∅ ∘ body') ∘ SAM-P-M'
      ≈˘⟨ lift-post (inMap A' δ∅ ∘ body') SAM-P-M' ⟩
        ((inMap A' δ∅ ∘ body') ∘ p₂) ∘co SAM-P-M'
      ∎)
      where
      open ≈-Reasoning isEquiv
      eqP : ∀ i → strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ j → p₂) (p₂ {Γ'} {M'}) i ≈ p₂
      eqP Fin.zero    = ≈-refl
      eqP (Fin.suc ())

    premR : (cataB ∘co (inMap P' δ∅ ∘ SAM-P-N'))
              ≈ (alg⋆ ∘co strong-fmor P (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) cataB))
    premR = begin
        cataB ∘co (inMap P' δ∅ ∘ SAM-P-N')
      ≈˘⟨ ∘co-push cataB (inMap P' δ∅) SAM-P-N' ⟩
        (cataB ∘co (inMap P' δ∅ ∘ p₂)) ∘co SAM-P-N'
      ≈⟨ coKl.∘-cong (⦅⦆-β {P = P'} {δ = δ∅} ((inMap A' δ∅ ∘ body') ∘ p₂)) ≈-refl ⟩
        ((((inMap A' δ∅ ∘ body') ∘ p₂) ∘co strong-fmor P' (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) cataB)) ∘co SAM-P-N')
      ≈⟨ coKl.assoc _ _ _ ⟩
        (((inMap A' δ∅ ∘ body') ∘ p₂) ∘co (strong-fmor P' (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) cataB) ∘co SAM-P-N'))
      ≈⟨ coKl.∘-cong ≈-refl (strong-as-poly-map-natural {n = 1} (sub (sub-lift σ) τ) gs (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) cataB)) ⟩
        (((inMap A' δ∅ ∘ body') ∘ p₂) ∘co (SAM-P-M' ∘co strong-fmor P (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) cataB)))
      ≈˘⟨ coKl.assoc _ _ _ ⟩
        ((((inMap A' δ∅ ∘ body') ∘ p₂) ∘co SAM-P-M') ∘co strong-fmor P (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) cataB))
      ≈⟨ coKl.∘-cong alg-eq ≈-refl ⟩
        alg⋆ ∘co strong-fmor P (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) cataB)
      ∎
      where open ≈-Reasoning isEquiv

    main : (SAMμ ∘co (μ-map P δ∅ A δ∅ body ∘ p₂)) ≈ ((μ-map P' δ∅ A' δ∅ body' ∘ p₂) ∘co SAMμP)
    main = begin
        SAMμ ∘co (μ-map P δ∅ A δ∅ body ∘ p₂)
      ≈˘⟨ coKl.∘-cong ≈-refl (μ-map-weaken P δ∅ A δ∅ body) ⟩
        SAMμ ∘co ⦅_⦆ {P = P} {δ = δ∅} ((inMap A δ∅ ∘ body) ∘ p₂)
      ≈⟨ fusion {P = P} {δ = δ∅} ((inMap A δ∅ ∘ body) ∘ p₂) alg⋆ SAMμ premL ⟩
        ⦅_⦆ {P = P} {δ = δ∅} alg⋆
      ≈˘⟨ fusion {P = P} {δ = δ∅} (inMap P' δ∅ ∘ SAM-P-N') alg⋆ cataB premR ⟩
        cataB ∘co SAMμP
      ≈⟨ coKl.∘-cong (μ-map-weaken P' δ∅ A' δ∅ body') ≈-refl ⟩
        (μ-map P' δ∅ A' δ∅ body' ∘ p₂) ∘co SAMμP
      ∎
      where open ≈-Reasoning isEquiv

  strong-subst-fwd-body-natural : ∀ {Δ Δ'} (σ : TySub Δ Δ') (τ : type (suc Δ)) {Γ' : Obj} {δ δ' : Fin Δ' → obj}
    (gs : ∀ i → prod Γ' (δ i) ⇒ δ' i) {X X' : obj} (kc : prod Γ' X ⇒ X') →
    (strong-fmor (as-poly {Δ} {1} τ (λ i → ⟦ σ i ⟧ty δ')) (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) kc)
       ∘co (strong-as-poly-map {Δ} {1} τ (λ i → strong-as-poly-map (σ i) gs δ∅) (extend δ∅ X)
            ∘co (subst-fwd-body σ τ δ X ∘ p₂)))
      ≈ ((subst-fwd-body σ τ δ' X' ∘ p₂)
         ∘co (strong-fmor (as-poly {Δ'} {1} (sub (sub-lift σ) τ) δ') (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) kc)
              ∘co strong-as-poly-map {Δ'} {1} (sub (sub-lift σ) τ) gs (extend δ∅ X)))
  strong-subst-fwd-body-natural {Δ} {Δ'} σ τ {Γ'} {δ} {δ'} gs {X} {X'} kc = main
    where
    SF    = strong-fmor (as-poly {Δ} {1} τ (λ i → ⟦ σ i ⟧ty δ')) (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) kc)
    SAM-X = strong-as-poly-map {Δ} {1} τ (λ i → strong-as-poly-map (σ i) gs δ∅) (extend δ∅ X)
    af   = apply-fwd {n = 1} τ (λ i → ⟦ σ i ⟧ty δ) (extend δ∅ X)
    af'  = apply-fwd {n = 1} τ (λ i → ⟦ σ i ⟧ty δ') (extend δ∅ X')
    Rs   = as-poly-map τ (λ i → ≡-to-⇒ (sub-lift-pw σ δ X i)) δ∅
    Rs'  = as-poly-map τ (λ i → ≡-to-⇒ (sub-lift-pw σ δ' X' i)) δ∅
    S    = subst-fwd (sub-lift σ) τ (concat (extend {0} δ∅ X) δ)
    S'   = subst-fwd (sub-lift σ) τ (concat (extend {0} δ∅ X') δ')
    ab   = apply-bwd {n = 1} (sub (sub-lift σ) τ) δ (extend δ∅ X)
    ab'  = apply-bwd {n = 1} (sub (sub-lift σ) τ) δ' (extend δ∅ X')
    af₁  = apply-fwd {n = 1} (sub (sub-lift σ) τ) δ (extend δ∅ X)
    af₁' = apply-fwd {n = 1} (sub (sub-lift σ) τ) δ' (extend δ∅ X')
    Kδ = strong-concat-mor {n = 1} (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ j → p₂) kc) gs
    SAM-full = strong-as-poly-map τ
                 (strong-concat-mor {n = 1} (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ j → p₂) kc)
                    (λ j → strong-as-poly-map (σ j) gs δ∅)) δ∅
    SAM-1 = strong-as-poly-map τ (λ j → strong-as-poly-map (sub-lift σ j) Kδ δ∅) δ∅
    SAM-sub = strong-as-poly-map (sub (sub-lift σ) τ) Kδ δ∅
    SF-P' = strong-fmor (as-poly {Δ'} {1} (sub (sub-lift σ) τ) δ') (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) kc)
    SAM-P = strong-as-poly-map {Δ'} {1} (sub (sub-lift σ) τ) gs (extend δ∅ X)

    split-step : ((((af ∘ Rs) ∘ S) ∘ ab) ∘ p₂) ≈ ((af ∘ p₂) ∘co ((Rs ∘ p₂) ∘co ((S ∘ p₂) ∘co (ab ∘ p₂))))
    split-step =
      ≈-trans (lift-comp ((af ∘ Rs) ∘ S) ab)
      (≈-trans (coKl.∘-cong (lift-comp (af ∘ Rs) S) ≈-refl)
      (≈-trans (coKl.assoc _ _ _)
      (≈-trans (coKl.∘-cong (lift-comp af Rs) ≈-refl)
               (coKl.assoc _ _ _))))

    cast-step : (SAM-full ∘co (Rs ∘ p₂)) ≈ ((Rs' ∘ p₂) ∘co SAM-1)
    cast-step =
      strong-as-poly-map-square τ (λ i → ≡-to-⇒ (sub-lift-pw σ δ X i)) (λ i → ≡-to-⇒ (sub-lift-pw σ δ' X' i))
                                (λ j → strong-as-poly-map (sub-lift σ j) Kδ δ∅)
                                (strong-concat-mor {n = 1} (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ j → p₂) kc)
                                                   (λ j → strong-as-poly-map (σ j) gs δ∅))
                                δ∅ (strong-sub-lift-pw-natural σ gs kc)

    ab-step : (SAM-sub ∘co (ab ∘ p₂)) ≈ ((ab' ∘ p₂) ∘co (SF-P' ∘co SAM-P))
    ab-step =
      strong-apply-bwd-natural {n = 1} (sub (sub-lift σ) τ) gs
                               (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ j → p₂) kc)

    main : (SF ∘co (SAM-X ∘co ((((af ∘ Rs) ∘ S) ∘ ab) ∘ p₂)))
             ≈ (((((af' ∘ Rs') ∘ S') ∘ ab') ∘ p₂) ∘co (SF-P' ∘co SAM-P))
    main = begin
        SF ∘co (SAM-X ∘co ((((af ∘ Rs) ∘ S) ∘ ab) ∘ p₂))
      ≈⟨ coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl split-step) ⟩
        SF ∘co (SAM-X ∘co ((af ∘ p₂) ∘co ((Rs ∘ p₂) ∘co ((S ∘ p₂) ∘co (ab ∘ p₂)))))
      ≈˘⟨ coKl.∘-cong ≈-refl (coKl.assoc _ _ _) ⟩
        SF ∘co ((SAM-X ∘co (af ∘ p₂)) ∘co ((Rs ∘ p₂) ∘co ((S ∘ p₂) ∘co (ab ∘ p₂))))
      ≈˘⟨ coKl.assoc _ _ _ ⟩
        (SF ∘co (SAM-X ∘co (af ∘ p₂))) ∘co ((Rs ∘ p₂) ∘co ((S ∘ p₂) ∘co (ab ∘ p₂)))
      ≈⟨ coKl.∘-cong (strong-apply-fwd-natural {n = 1} τ (λ j → strong-as-poly-map (σ j) gs δ∅) (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ j → p₂) kc)) ≈-refl ⟩
        ((af' ∘ p₂) ∘co SAM-full) ∘co ((Rs ∘ p₂) ∘co ((S ∘ p₂) ∘co (ab ∘ p₂)))
      ≈⟨ coKl.assoc _ _ _ ⟩
        (af' ∘ p₂) ∘co (SAM-full ∘co ((Rs ∘ p₂) ∘co ((S ∘ p₂) ∘co (ab ∘ p₂))))
      ≈˘⟨ coKl.∘-cong ≈-refl (coKl.assoc _ _ _) ⟩
        (af' ∘ p₂) ∘co ((SAM-full ∘co (Rs ∘ p₂)) ∘co ((S ∘ p₂) ∘co (ab ∘ p₂)))
      ≈⟨ coKl.∘-cong ≈-refl (coKl.∘-cong cast-step ≈-refl) ⟩
        (af' ∘ p₂) ∘co (((Rs' ∘ p₂) ∘co SAM-1) ∘co ((S ∘ p₂) ∘co (ab ∘ p₂)))
      ≈⟨ coKl.∘-cong ≈-refl (coKl.assoc _ _ _) ⟩
        (af' ∘ p₂) ∘co ((Rs' ∘ p₂) ∘co (SAM-1 ∘co ((S ∘ p₂) ∘co (ab ∘ p₂))))
      ≈˘⟨ coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl (coKl.assoc _ _ _)) ⟩
        (af' ∘ p₂) ∘co ((Rs' ∘ p₂) ∘co ((SAM-1 ∘co (S ∘ p₂)) ∘co (ab ∘ p₂)))
      ≈⟨ coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl (coKl.∘-cong (strong-subst-fwd-natural (sub-lift σ) τ Kδ) ≈-refl)) ⟩
        (af' ∘ p₂) ∘co ((Rs' ∘ p₂) ∘co (((S' ∘ p₂) ∘co SAM-sub) ∘co (ab ∘ p₂)))
      ≈⟨ coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl (coKl.assoc _ _ _)) ⟩
        (af' ∘ p₂) ∘co ((Rs' ∘ p₂) ∘co ((S' ∘ p₂) ∘co (SAM-sub ∘co (ab ∘ p₂))))
      ≈⟨ coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl ab-step)) ⟩
        (af' ∘ p₂) ∘co ((Rs' ∘ p₂) ∘co ((S' ∘ p₂) ∘co ((ab' ∘ p₂) ∘co (SF-P' ∘co SAM-P))))
      ≈˘⟨ coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl (coKl.assoc _ _ _)) ⟩
        (af' ∘ p₂) ∘co ((Rs' ∘ p₂) ∘co (((S' ∘ p₂) ∘co (ab' ∘ p₂)) ∘co (SF-P' ∘co SAM-P)))
      ≈˘⟨ coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl (coKl.∘-cong (lift-comp S' ab') ≈-refl)) ⟩
        (af' ∘ p₂) ∘co ((Rs' ∘ p₂) ∘co (((S' ∘ ab') ∘ p₂) ∘co (SF-P' ∘co SAM-P)))
      ≈˘⟨ coKl.∘-cong ≈-refl (coKl.assoc _ _ _) ⟩
        (af' ∘ p₂) ∘co (((Rs' ∘ p₂) ∘co ((S' ∘ ab') ∘ p₂)) ∘co (SF-P' ∘co SAM-P))
      ≈˘⟨ coKl.∘-cong ≈-refl (coKl.∘-cong (lift-comp Rs' (S' ∘ ab')) ≈-refl) ⟩
        (af' ∘ p₂) ∘co (((Rs' ∘ (S' ∘ ab')) ∘ p₂) ∘co (SF-P' ∘co SAM-P))
      ≈˘⟨ coKl.assoc _ _ _ ⟩
        ((af' ∘ p₂) ∘co ((Rs' ∘ (S' ∘ ab')) ∘ p₂)) ∘co (SF-P' ∘co SAM-P)
      ≈˘⟨ coKl.∘-cong (lift-comp af' (Rs' ∘ (S' ∘ ab'))) ≈-refl ⟩
        ((af' ∘ (Rs' ∘ (S' ∘ ab'))) ∘ p₂) ∘co (SF-P' ∘co SAM-P)
      ≈˘⟨ coKl.∘-cong (∘-cong (≈-trans (assoc _ _ _) (assoc _ _ _)) ≈-refl) ≈-refl ⟩
        ((((af' ∘ Rs') ∘ S') ∘ ab') ∘ p₂) ∘co (SF-P' ∘co SAM-P)
      ∎
      where open ≈-Reasoning isEquiv

sub-as-apply-fwd : (τ : type 1) (τ' : type 0) →
                   ⟦ τ [ τ' ] ⟧ty (λ ()) ⇒ fobj μ-obj (as-poly {0} {1} τ (λ ())) (extend δ∅ (⟦ τ' ⟧ty (λ ())))
sub-as-apply-fwd τ τ' =
  apply-fwd {0} {1} τ (λ ()) (extend δ∅ (⟦ τ' ⟧ty (λ ())))
    ∘ as-poly-map τ (λ i → ≡-to-⇒ (push-pw τ' i)) δ∅
    ∘ subst-fwd (push τ') τ (λ ())

sub-as-apply-bwd : (τ : type 1) (τ' : type 0) →
                   fobj μ-obj (as-poly {0} {1} τ (λ ())) (extend δ∅ (⟦ τ' ⟧ty (λ ()))) ⇒ ⟦ τ [ τ' ] ⟧ty (λ ())
sub-as-apply-bwd τ τ' =
  subst-bwd (push τ') τ (λ ())
    ∘ as-poly-map τ (λ i → ≡-to-⇒ (sym (push-pw τ' i))) δ∅
    ∘ apply-bwd {0} {1} τ (λ ()) (extend δ∅ (⟦ τ' ⟧ty (λ ())))

sub-as-apply-bwd-fwd : (τ : type 1) (τ' : type 0) → (sub-as-apply-bwd τ τ' ∘ sub-as-apply-fwd τ τ') ≈ id _
sub-as-apply-bwd-fwd τ τ' = begin
    ((sb ∘ T⁻) ∘ ab) ∘ ((af ∘ Rs) ∘ sf)
  ≈⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
    ((sb ∘ T⁻) ∘ ab) ∘ (af ∘ (Rs ∘ sf))
  ≈˘⟨ assoc _ _ _ ⟩
    (((sb ∘ T⁻) ∘ ab) ∘ af) ∘ (Rs ∘ sf)
  ≈⟨ ∘-cong (tail-cancel (apply-bwd-fwd {0} {1} τ (λ ()) (extend δ∅ (⟦ τ' ⟧ty (λ ()))))) ≈-refl ⟩
    (sb ∘ T⁻) ∘ (Rs ∘ sf)
  ≈˘⟨ assoc _ _ _ ⟩
    ((sb ∘ T⁻) ∘ Rs) ∘ sf
  ≈⟨ ∘-cong (tail-cancel (as-poly-map-cast-inv τ (push-pw τ') δ∅)) ≈-refl ⟩
    sb ∘ sf
  ≈⟨ subst-bwd-fwd (push τ') τ (λ ()) ⟩
    id _
  ∎
  where
    open ≈-Reasoning isEquiv
    sf = subst-fwd (push τ') τ (λ ())
    sb = subst-bwd (push τ') τ (λ ())
    af = apply-fwd {0} {1} τ (λ ()) (extend δ∅ (⟦ τ' ⟧ty (λ ())))
    ab = apply-bwd {0} {1} τ (λ ()) (extend δ∅ (⟦ τ' ⟧ty (λ ())))
    Rs = as-poly-map τ (λ i → ≡-to-⇒ (push-pw τ' i)) δ∅
    T⁻ = as-poly-map τ (λ i → ≡-to-⇒ (sym (push-pw τ' i))) δ∅

sub-as-apply-fwd-bwd : (τ : type 1) (τ' : type 0) → (sub-as-apply-fwd τ τ' ∘ sub-as-apply-bwd τ τ') ≈ id _
sub-as-apply-fwd-bwd τ τ' = begin
    ((af ∘ Rs) ∘ sf) ∘ ((sb ∘ T⁻) ∘ ab)
  ≈⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
    ((af ∘ Rs) ∘ sf) ∘ (sb ∘ (T⁻ ∘ ab))
  ≈˘⟨ assoc _ _ _ ⟩
    (((af ∘ Rs) ∘ sf) ∘ sb) ∘ (T⁻ ∘ ab)
  ≈⟨ ∘-cong (tail-cancel (subst-fwd-bwd (push τ') τ (λ ()))) ≈-refl ⟩
    (af ∘ Rs) ∘ (T⁻ ∘ ab)
  ≈˘⟨ assoc _ _ _ ⟩
    ((af ∘ Rs) ∘ T⁻) ∘ ab
  ≈⟨ ∘-cong (tail-cancel (as-poly-map-cast-inv' τ (push-pw τ') δ∅)) ≈-refl ⟩
    af ∘ ab
  ≈⟨ apply-fwd-bwd {0} {1} τ (λ ()) (extend δ∅ (⟦ τ' ⟧ty (λ ()))) ⟩
    id _
  ∎
  where
    open ≈-Reasoning isEquiv
    sf = subst-fwd (push τ') τ (λ ())
    sb = subst-bwd (push τ') τ (λ ())
    af = apply-fwd {0} {1} τ (λ ()) (extend δ∅ (⟦ τ' ⟧ty (λ ())))
    ab = apply-bwd {0} {1} τ (λ ()) (extend δ∅ (⟦ τ' ⟧ty (λ ())))
    Rs = as-poly-map τ (λ i → ≡-to-⇒ (push-pw τ' i)) δ∅
    T⁻ = as-poly-map τ (λ i → ≡-to-⇒ (sym (push-pw τ' i))) δ∅

sub-as-apply-fwd-μ-body : ∀ (τ' : type 2) (ρ : type 0) (X : obj) →
                          fobj μ-obj (as-poly {0} {1} (τ' [ ρ ]₁) (λ ())) (extend δ∅ X) ⇒
                          fobj μ-obj (as-poly {0} {2} τ' (λ ())) (extend (extend δ∅ (⟦ ρ ⟧ty (λ ()))) X)
sub-as-apply-fwd-μ-body τ' ρ X =
  apply-fwd-body τ' (λ ()) (extend δ∅ (⟦ ρ ⟧ty (λ ()))) X
    ∘ as-poly-map {1} {1} τ' (λ i → ≡-to-⇒ (push-pw ρ i)) (extend δ∅ X)
    ∘ subst-fwd-body (push ρ) τ' (λ ()) X

sub-as-apply-fwd-μ : ∀ (τ' : type 2) (ρ : type 0) →
                     sub-as-apply-fwd (μ τ') ρ
                       ≈ μ-map (as-poly {0} {1} (τ' [ ρ ]₁) (λ ())) δ∅
                           (as-poly {0} {2} τ' (λ ())) (extend δ∅ (⟦ ρ ⟧ty (λ ())))
                           (sub-as-apply-fwd-μ-body τ' ρ (μ-obj (as-poly {0} {2} τ' (λ ())) (extend δ∅ (⟦ ρ ⟧ty (λ ())))))
sub-as-apply-fwd-μ τ' ρ = begin
    sub-as-apply-fwd (μ τ') ρ
  ≈⟨ assoc _ _ _ ⟩
    apply-fwd {0} {1} (μ τ') (λ ()) δr ∘ (as-poly-map {1} {0} (μ τ') cs δ∅ ∘ subst-fwd (push ρ) (μ τ') (λ ()))
  ≈⟨ ∘-cong ≈-refl (μ-map-comp P₁ δ∅ P₂ δ∅ P₃ δ∅ (u₁ (μ-obj P₂ δ∅)) (u₂ M₃) (u₁ M₃)
       (subst-fwd-body-carrier (push ρ) τ' (λ ()) (as-poly-map {1} {0} (μ τ') cs δ∅))) ⟩
    apply-fwd {0} {1} (μ τ') (λ ()) δr ∘ μ-map P₁ δ∅ P₃ δ∅ (u₂ M₃ ∘ u₁ M₃)
  ≈⟨ μ-map-comp P₁ δ∅ P₃ δ∅ Q δr (u₂ M₃ ∘ u₁ M₃) (apply-fwd-body τ' (λ ()) δr Mq) (u₂ Mq ∘ u₁ Mq) sq ⟩
    μ-map P₁ δ∅ Q δr (apply-fwd-body τ' (λ ()) δr Mq ∘ (u₂ Mq ∘ u₁ Mq))
  ≈˘⟨ μ-map-cong P₁ δ∅ Q δr (assoc _ _ _) ⟩
    μ-map P₁ δ∅ Q δr (sub-as-apply-fwd-μ-body τ' ρ Mq)
  ∎
  where
  open ≈-Reasoning isEquiv
  δr = extend δ∅ (⟦ ρ ⟧ty (λ ()))
  cs = λ i → ≡-to-⇒ (push-pw ρ i)
  P₁ = as-poly {0} {1} (τ' [ ρ ]₁) (λ ())
  P₂ = as-poly {1} {1} τ' (λ i → ⟦ push ρ i ⟧ty (λ ()))
  P₃ = as-poly {1} {1} τ' (λ i → concat δr (λ ()) i)
  Q  = as-poly {0} {2} τ' (λ ())
  M₃ = μ-obj P₃ δ∅
  Mq = μ-obj Q δr
  u₁ = subst-fwd-body (push ρ) τ' (λ ())
  u₂ = λ X → as-poly-map {1} {1} τ' cs (extend δ∅ X)
  af = apply-fwd {0} {1} (μ τ') (λ ()) δr
  E  = extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) af
  sq : (fmor P₃ E ∘ (u₂ M₃ ∘ u₁ M₃)) ≈ ((u₂ Mq ∘ u₁ Mq) ∘ fmor P₁ E)
  sq = ≈-trans (head-cong (as-poly-map-natural {1} {1} τ' cs E))
       (tail-cong-assoc (subst-fwd-body-carrier (push ρ) τ' (λ ()) af))

sub-as-apply-fwd-μ-in : ∀ (τ' : type 2) (ρ : type 0) →
  (sub-as-apply-fwd (μ τ') ρ
     ∘ (inMap (as-poly {0} {1} (τ' [ ρ ]₁) (λ ())) δ∅
        ∘ sub-as-apply-fwd (τ' [ ρ ]₁) (μ (τ' [ ρ ]₁))))
    ≈ (inMap (as-poly {0} {2} τ' (λ ())) (extend δ∅ (⟦ ρ ⟧ty (λ ())))
       ∘ (sub-as-apply-fwd-μ-body τ' ρ (μ-obj (as-poly {0} {2} τ' (λ ())) (extend δ∅ (⟦ ρ ⟧ty (λ ()))))
          ∘ (fmor (as-poly {0} {1} (τ' [ ρ ]₁) (λ ()))
               (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) (sub-as-apply-fwd (μ τ') ρ))
             ∘ sub-as-apply-fwd (τ' [ ρ ]₁) (μ (τ' [ ρ ]₁)))))
sub-as-apply-fwd-μ-in τ' ρ = begin
    saf ∘ (inMap P₁ δ∅ ∘ sf)
  ≈˘⟨ assoc _ _ _ ⟩
    (saf ∘ inMap P₁ δ∅) ∘ sf
  ≈⟨ ∘-cong (∘-cong (sub-as-apply-fwd-μ τ' ρ) ≈-refl) ≈-refl ⟩
    (μ-map P₁ δ∅ Q δr b ∘ inMap P₁ δ∅) ∘ sf
  ≈⟨ ∘-cong (μ-map-in P₁ δ∅ Q δr b) ≈-refl ⟩
    (inMap Q δr ∘ (b ∘ fmor P₁ (extend-mor (λ i → id _) (μ-map P₁ δ∅ Q δr b)))) ∘ sf
  ≈⟨ ∘-cong (∘-cong ≈-refl (∘-cong ≈-refl (fmor-cong P₁ eqs))) ≈-refl ⟩
    (inMap Q δr ∘ (b ∘ fmor P₁ E)) ∘ sf
  ≈⟨ assoc _ _ _ ⟩
    inMap Q δr ∘ ((b ∘ fmor P₁ E) ∘ sf)
  ≈⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
    inMap Q δr ∘ (b ∘ (fmor P₁ E ∘ sf))
  ∎
  where
  open ≈-Reasoning isEquiv
  A  = τ' [ ρ ]₁
  δr = extend δ∅ (⟦ ρ ⟧ty (λ ()))
  P₁ = as-poly {0} {1} A (λ ())
  Q  = as-poly {0} {2} τ' (λ ())
  b  = sub-as-apply-fwd-μ-body τ' ρ (μ-obj Q δr)
  saf = sub-as-apply-fwd (μ τ') ρ
  sf  = sub-as-apply-fwd A (μ A)
  E  = extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) saf
  eqs : ∀ i → extend-mor {δ = δ∅} {δ' = δ∅} (λ j → id _) (μ-map P₁ δ∅ Q δr b) i ≈ E i
  eqs Fin.zero    = ≈-sym (sub-as-apply-fwd-μ τ' ρ)
  eqs (Fin.suc ())

private
  concat-emp-pw : ∀ {δ₀ : Fin 1 → obj} (i : Fin 1) → δ₀ i ≡ concat δ₀ (λ ()) i
  concat-emp-pw Fin.zero = refl

unfold-pw : ∀ (τ' : type 2) (X : obj) (i : Fin 2) →
            ⟦ unfold₁-sub τ' i ⟧ty (extend δ∅ X) ⇒
            concat (extend (extend δ∅ X) (μ-obj (as-poly {0} {2} τ' (λ ())) (extend δ∅ X))) (λ ()) i
unfold-pw τ' X Fin.zero =
  apply-fwd {0} {1} (μ τ') (λ ()) (extend δ∅ X) ∘ ≡-to-⇒ (ty-cong (μ τ') concat-emp-pw)
unfold-pw τ' X (Fin.suc Fin.zero) = id X
unfold-pw τ' X (Fin.suc (Fin.suc ()))

unfold-as-apply-fwd : ∀ (τ' : type 2) (X : obj) →
                      fobj μ-obj (as-poly {0} {1} (unfold₁ τ') (λ ())) (extend δ∅ X) ⇒
                      fobj μ-obj (as-poly {0} {2} τ' (λ ()))
                        (extend (extend δ∅ X) (μ-obj (as-poly {0} {2} τ' (λ ())) (extend δ∅ X)))
unfold-as-apply-fwd τ' X =
  apply-fwd {0} {2} τ' (λ ()) (extend (extend δ∅ X) (μ-obj (as-poly {0} {2} τ' (λ ())) (extend δ∅ X)))
    ∘ as-poly-map {2} {0} τ' (unfold-pw τ' X) δ∅
    ∘ subst-fwd (unfold₁-sub τ') τ' (extend δ∅ X)
    ∘ ≡-to-⇒ (ty-cong (unfold₁ τ') (λ i → sym (concat-emp-pw i)))
    ∘ apply-bwd {0} {1} (unfold₁ τ') (λ ()) (extend δ∅ X)

unfold-as-apply-fwd-inst : ∀ (τ' : type 2) (ρ : type 0) →
  (sub-as-apply-fwd-μ-body τ' ρ (μ-obj (as-poly {0} {2} τ' (λ ())) (extend δ∅ (⟦ ρ ⟧ty (λ ()))))
     ∘ (fmor (as-poly {0} {1} (τ' [ ρ ]₁) (λ ()))
             (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) (sub-as-apply-fwd (μ τ') ρ))
        ∘ (sub-as-apply-fwd (τ' [ ρ ]₁) (μ (τ' [ ρ ]₁))
           ∘ ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty (λ ())) (unfold₁-inst τ' ρ)))))
    ≈ (unfold-as-apply-fwd τ' (⟦ ρ ⟧ty (λ ())) ∘ sub-as-apply-fwd (unfold₁ τ') ρ)
unfold-as-apply-fwd-inst τ' ρ =
  ≈-trans lhs (≈-trans (∘-cong ≈-refl (∘-cong (as-poly-map-cong τ' pw-step δ∅) ≈-refl)) (≈-sym rhs))
  where
  open ≈-Reasoning isEquiv
  A  = τ' [ ρ ]₁
  Xρ = ⟦ ρ ⟧ty ∅
  δr = extend δ∅ Xρ
  σp = push ρ
  σL = sub-lift σp
  σu = unfold₁-sub τ'
  σm = push (μ A)
  σa = λ i → sub σp (σu i)
  σb = λ i → sub σm (σL i)
  δp = λ i → ⟦ σp i ⟧ty ∅
  δm = λ i → ⟦ σm i ⟧ty ∅
  Q  = as-poly {0} {2} τ' ∅
  P₁ = as-poly {0} {1} A ∅
  MQ = μ-obj Q δr
  Mμ = μ-obj P₁ δ∅
  γ' = concat (extend {0} δ∅ MQ) ∅
  pwu : ∀ i → σa i ≡ σb i
  pwu Fin.zero    = refl
  pwu (Fin.suc Fin.zero) = sym (trans (sub-ren σm Fin.suc ρ) (trans (sub-cong ρ λ ()) (sub-id ρ)))
  pwu (Fin.suc (Fin.suc ()))
  e-ss  = sub-sub σm σL τ'
  e-ss' = sub-sub σp σu τ'
  e-c   = sub-cong τ' pwu
  e-id  = sym (pwu (Fin.suc Fin.zero))
  Cρ  = ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty ∅) (unfold₁-inst τ' ρ))
  Ca  = ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty ∅) e-ss')
  Cb  = ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty ∅) e-c)
  Cc  = ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty ∅) (sym e-ss))
  Css = ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty ∅) e-ss)
  saf = sub-as-apply-fwd (μ τ') ρ
  E   = extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) saf
  fmE = fmor P₁ E
  Ts  = subst-fwd σm A ∅
  Rs  = as-poly-map A (λ i → ≡-to-⇒ (push-pw (μ A) i)) δ∅
  Fs  = apply-fwd {0} {1} A ∅ (extend δ∅ Mμ)
  FsQ = apply-fwd {0} {1} A ∅ (extend δ∅ MQ)
  gρ  = λ i → ≡-to-⇒ (push-pw ρ i)
  F'  = apply-fwd {n = 1} τ' δp (extend δ∅ MQ)
  FQ' = apply-fwd {n = 1} τ' (concat δr ∅) (extend δ∅ MQ)
  L'fam = λ i → ≡-to-⇒ (sub-lift-pw σp ∅ MQ i)
  L'  = as-poly-map τ' L'fam δ∅
  S'  = subst-fwd σL τ' γ'
  B'  = apply-bwd {n = 1} A ∅ (extend δ∅ MQ)
  Mb  = as-poly-map {1} {1} τ' gρ (extend δ∅ MQ)
  Fq  = apply-fwd {0} {2} τ' ∅ (extend δr MQ)
  Ebfam = λ i → ≡-to-⇒ (env-pw ∅ δr MQ i)
  Eb  = as-poly-map τ' Ebfam δ∅
  Bb  = apply-bwd {n = 1} τ' (concat δr ∅) (extend δ∅ MQ)
  Tu  = subst-fwd σp (unfold₁ τ') ∅
  Ru  = as-poly-map (unfold₁ τ') gρ δ∅
  Fu  = apply-fwd {0} {1} (unfold₁ τ') ∅ δr
  Bu  = apply-bwd {0} {1} (unfold₁ τ') ∅ δr
  Cu  = ≡-to-⇒ (ty-cong (unfold₁ τ') (λ i → sym (concat-emp-pw {δ₀ = δr} i)))
  Su  = subst-fwd σu τ' δr
  Sup = subst-fwd σu τ' δp
  Mu  = as-poly-map {2} {0} τ' (unfold-pw τ' Xρ) δ∅
  KAfam = concat-mor {n = 1} {δ₀ = extend {0} δ∅ Mμ} {δ = ∅} {δ' = ∅} E (λ i → id _)
  KA  = as-poly-map A KAfam δ∅
  krfam : ∀ i → δm i ⇒ γ' i
  krfam = λ i → KAfam i ∘ ≡-to-⇒ (push-pw (μ A) i)
  Kr  = as-poly-map A krfam δ∅
  NLfam = λ i → as-poly-map (σL i) krfam δ∅
  NL  = as-poly-map τ' NLfam δ∅
  SL  = subst-fwd σL τ' δm
  Wmfam = λ i → subst-fwd σm (σL i) ∅
  Wm  = as-poly-map τ' Wmfam δ∅
  Sb  = subst-fwd σb τ' ∅
  Sa  = subst-fwd σa τ' ∅
  Pwfam = λ i → ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty ∅) (pwu i))
  Pw  = as-poly-map τ' Pwfam δ∅
  Kρfam = concat-mor {n = 1} {δ₀ = extend {0} δ∅ MQ} (λ i → id _) gρ
  Kρ  = as-poly-map τ' Kρfam δ∅
  cu : ∀ i → δp i ⇒ δr i
  cu = λ i → ≡-to-⇒ (sym (concat-emp-pw {δ₀ = δr} i)) ∘ ≡-to-⇒ (push-pw ρ i)
  Cu' = as-poly-map (unfold₁ τ') (λ i → ≡-to-⇒ (sym (concat-emp-pw {δ₀ = δr} i))) δ∅
  CR  = as-poly-map (unfold₁ τ') cu δ∅
  Nufam = λ i → as-poly-map (σu i) cu δ∅
  Nu  = as-poly-map τ' Nufam δ∅
  Wufam = λ i → subst-fwd σp (σu i) ∅
  Wu  = as-poly-map τ' Wufam δ∅
  famL : ∀ i → ⟦ σa i ⟧ty ∅ ⇒ concat (extend δr MQ) ∅ i
  famL = λ i → Ebfam i ∘ (Kρfam i ∘ (L'fam i ∘ (NLfam i ∘ (Wmfam i ∘ Pwfam i))))
  famR : ∀ i → ⟦ σa i ⟧ty ∅ ⇒ concat (extend δr MQ) ∅ i
  famR = λ i → unfold-pw τ' Xρ i ∘ (Nufam i ∘ Wufam i)
  cast-split : Cρ ≈ (Cc ∘ (Cb ∘ Ca))
  cast-split =
    ≈-sym (≈-trans (∘-cong ≈-refl (≡-to-⇒-comp (cong (λ υ → ⟦ υ ⟧ty ∅) e-ss') (cong (λ υ → ⟦ υ ⟧ty ∅) e-c)))
          (≈-trans (≡-to-⇒-comp (trans (cong (λ υ → ⟦ υ ⟧ty ∅) e-ss') (cong (λ υ → ⟦ υ ⟧ty ∅) e-c))
                                (cong (λ υ → ⟦ υ ⟧ty ∅) (sym e-ss)))
                   (≡-to-⇒-irr (trans (trans (cong (λ υ → ⟦ υ ⟧ty ∅) e-ss') (cong (λ υ → ⟦ υ ⟧ty ∅) e-c))
                                      (cong (λ υ → ⟦ υ ⟧ty ∅) (sym e-ss)))
                               (cong (λ υ → ⟦ υ ⟧ty ∅) (unfold₁-inst τ' ρ)))))
  cast-cancel : (Css ∘ Cc) ≈ id _
  cast-cancel =
    ≈-trans (≡-to-⇒-comp (cong (λ υ → ⟦ υ ⟧ty ∅) (sym e-ss)) (cong (λ υ → ⟦ υ ⟧ty ∅) e-ss))
            (≡-to-⇒-irr (trans (cong (λ υ → ⟦ υ ⟧ty ∅) (sym e-ss)) (cong (λ υ → ⟦ υ ⟧ty ∅) e-ss)) refl)
  closed : ∀ {δ : Fin 0 → obj} (gs : ∀ i → δ i ⇒ δ i) → as-poly-map ρ gs δ∅ ≈ id _
  closed gs = ≈-trans (as-poly-map-cong ρ (λ ()) δ∅) (as-poly-map-id ρ δ∅)
  lm-wm : (≡-to-⇒ (ty-ren Fin.suc ρ δm) ∘ subst-fwd σm (Fin.suc *ᵗ ρ) ∅) ≈ ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty ∅) e-id)
  lm-wm =
    ≈-trans (∘-cong (≈-sym id-left) ≈-refl)
    (≈-trans (∘-cong (∘-cong (≈-sym (closed _)) ≈-refl) ≈-refl)
             (subst-fwd-ren-id Fin.suc σm (λ ()) ρ e-id ∅))
  pw-cu : ∀ i → (≡-to-⇒ (concat-emp-pw {δ₀ = δr} i) ∘ cu i) ≈ gρ i
  pw-cu Fin.zero = ≈-trans id-left id-left
  cμnμ : (≡-to-⇒ (ty-cong (μ τ') (concat-emp-pw {δ₀ = δr})) ∘ as-poly-map (μ τ') cu δ∅)
           ≈ as-poly-map (μ τ') gρ δ∅
  cμnμ =
    ≈-trans (∘-cong (cast-as-poly-cong {n = 0} (μ τ') (concat-emp-pw {δ₀ = δr}) δ∅) ≈-refl)
    (≈-trans (as-poly-map-comp (μ τ') (λ i → ≡-to-⇒ (concat-emp-pw {δ₀ = δr} i)) cu δ∅)
             (as-poly-map-cong (μ τ') pw-cu δ∅))
  pw-step : ∀ i → famL i ≈ famR i
  pw-step Fin.zero =
    ≈-trans id-left (≈-trans id-left (≈-trans id-left (≈-trans (∘-cong ≈-refl id-left) (≈-trans id-right
    (≈-trans id-right
    (≈-sym (tail-cong-assoc (head-cong cμnμ))))))))
  pw-step (Fin.suc Fin.zero) =
    ≈-trans id-left (≈-trans id-left
    (≈-trans (head-cong (≈-trans (as-poly-map-ren Fin.suc ρ krfam δ∅)
                                 (≈-trans (∘-cong (closed (λ i → krfam (Fin.suc i))) ≈-refl)
                                          id-left)))
     (≈-trans (head-cong lm-wm)
      (≈-trans (≡-to-⇒-comp (cong (λ υ → ⟦ υ ⟧ty ∅) (pwu (Fin.suc Fin.zero))) (cong (λ υ → ⟦ υ ⟧ty ∅) e-id))
      (≈-trans (≡-to-⇒-irr (trans (cong (λ υ → ⟦ υ ⟧ty ∅) (pwu (Fin.suc Fin.zero))) (cong (λ υ → ⟦ υ ⟧ty ∅) e-id)) refl)
               (≈-sym (≈-trans id-left (≈-trans id-right id-left))))))))
  pw-step (Fin.suc (Fin.suc ()))
  lhs : (((((Fq ∘ Eb) ∘ Bb) ∘ Mb) ∘ (((F' ∘ L') ∘ S') ∘ B')) ∘ (fmE ∘ (((Fs ∘ Rs) ∘ Ts) ∘ Cρ)))
          ≈ (Fq ∘ (as-poly-map τ' famL δ∅ ∘ (Sa ∘ Ca)))
  lhs = begin
      ((((Fq ∘ Eb) ∘ Bb) ∘ Mb) ∘ (((F' ∘ L') ∘ S') ∘ B')) ∘ (fmE ∘ (((Fs ∘ Rs) ∘ Ts) ∘ Cρ))
    ≈⟨ ≈-trans (assoc _ _ _) (≈-trans (assoc _ _ _) (≈-trans (assoc _ _ _)
       (tail-cong (∘-cong₂ (∘-cong₂ (∘-cong₂
         (≈-trans (assoc _ _ _) (≈-trans (assoc _ _ _) (assoc _ _ _))))))))) ⟩
      Fq ∘ (Eb ∘ (Bb ∘ (Mb ∘ (F' ∘ (L' ∘ (S' ∘ (B' ∘ (fmE ∘ (((Fs ∘ Rs) ∘ Ts) ∘ Cρ)))))))))
    ≈⟨ ∘-cong₂ (∘-cong₂ (∘-cong₂ (∘-cong₂ (∘-cong₂ (∘-cong₂ (∘-cong₂ (∘-cong₂ (∘-cong₂
       (≈-trans (assoc _ _ _) (tail-cong (∘-cong₂ (∘-cong₂ cast-split)))))))))))) ⟩
      Fq ∘ (Eb ∘ (Bb ∘ (Mb ∘ (F' ∘ (L' ∘ (S' ∘ (B' ∘ (fmE ∘ (Fs ∘ (Rs ∘ (Ts ∘ (Cc ∘ (Cb ∘ Ca)))))))))))))
    ≈⟨ ∘-cong₂ (∘-cong₂ (∘-cong₂ (∘-cong₂ (∘-cong₂ (∘-cong₂ (∘-cong₂ (∘-cong₂
       (head-cong-assoc (apply-fwd-natural A ∅ E))))))))) ⟩
      Fq ∘ (Eb ∘ (Bb ∘ (Mb ∘ (F' ∘ (L' ∘ (S' ∘ (B' ∘ (FsQ ∘ (KA ∘ (Rs ∘ (Ts ∘ (Cc ∘ (Cb ∘ Ca)))))))))))))
    ≈⟨ ∘-cong₂ (∘-cong₂ (∘-cong₂ (∘-cong₂ (∘-cong₂ (∘-cong₂ (∘-cong₂
       (head-cancel (apply-bwd-fwd {n = 1} A ∅ (extend δ∅ MQ))))))))) ⟩
      Fq ∘ (Eb ∘ (Bb ∘ (Mb ∘ (F' ∘ (L' ∘ (S' ∘ (KA ∘ (Rs ∘ (Ts ∘ (Cc ∘ (Cb ∘ Ca)))))))))))
    ≈⟨ ∘-cong₂ (∘-cong₂ (∘-cong₂ (∘-cong₂ (∘-cong₂ (∘-cong₂ (∘-cong₂
       (head-cong (as-poly-map-comp A KAfam (λ i → ≡-to-⇒ (push-pw (μ A) i)) δ∅)))))))) ⟩
      Fq ∘ (Eb ∘ (Bb ∘ (Mb ∘ (F' ∘ (L' ∘ (S' ∘ (Kr ∘ (Ts ∘ (Cc ∘ (Cb ∘ Ca))))))))))
    ≈⟨ ∘-cong₂ (∘-cong₂ (∘-cong₂ (∘-cong₂ (∘-cong₂ (∘-cong₂ (head-cong-assoc (≈-sym (subst-fwd-natural σL τ' krfam)))))))) ⟩
      Fq ∘ (Eb ∘ (Bb ∘ (Mb ∘ (F' ∘ (L' ∘ (NL ∘ (SL ∘ (Ts ∘ (Cc ∘ (Cb ∘ Ca))))))))))
    ≈⟨ ∘-cong₂ (∘-cong₂ (∘-cong₂ (∘-cong₂ (∘-cong₂ (∘-cong₂ (∘-cong₂
       (≈-trans (head-cong-assoc (subst-fwd-sub σL σm τ' e-ss ∅)) (assoc _ _ _)))))))) ⟩
      Fq ∘ (Eb ∘ (Bb ∘ (Mb ∘ (F' ∘ (L' ∘ (NL ∘ (Wm ∘ (Sb ∘ (Css ∘ (Cc ∘ (Cb ∘ Ca)))))))))))
    ≈⟨ ∘-cong₂ (∘-cong₂ (∘-cong₂ (∘-cong₂ (∘-cong₂ (∘-cong₂ (∘-cong₂ (∘-cong₂ (∘-cong₂
       (head-cancel cast-cancel))))))))) ⟩
      Fq ∘ (Eb ∘ (Bb ∘ (Mb ∘ (F' ∘ (L' ∘ (NL ∘ (Wm ∘ (Sb ∘ (Cb ∘ Ca)))))))))
    ≈⟨ ∘-cong₂ (∘-cong₂ (∘-cong₂ (∘-cong₂ (∘-cong₂ (∘-cong₂ (∘-cong₂ (∘-cong₂
       (head-cong-assoc (≈-sym (subst-fwd-cong τ' pwu e-c ∅)))))))))) ⟩
      Fq ∘ (Eb ∘ (Bb ∘ (Mb ∘ (F' ∘ (L' ∘ (NL ∘ (Wm ∘ (Pw ∘ (Sa ∘ Ca)))))))))
    ≈⟨ ∘-cong₂ (∘-cong₂ (∘-cong₂ (head-cong-assoc (≈-sym (apply-fwd-map {n = 1} τ' gρ (extend δ∅ MQ)))))) ⟩
      Fq ∘ (Eb ∘ (Bb ∘ (FQ' ∘ (Kρ ∘ (L' ∘ (NL ∘ (Wm ∘ (Pw ∘ (Sa ∘ Ca)))))))))
    ≈⟨ ∘-cong₂ (∘-cong₂ (head-cancel (apply-bwd-fwd {n = 1} τ' (concat δr ∅) (extend δ∅ MQ)))) ⟩
      Fq ∘ (Eb ∘ (Kρ ∘ (L' ∘ (NL ∘ (Wm ∘ (Pw ∘ (Sa ∘ Ca)))))))
    ≈⟨ ∘-cong₂ (≈-trans (∘-cong₂ (≈-trans (∘-cong₂ (≈-trans (∘-cong₂ (≈-trans (∘-cong₂
         (head-cong (as-poly-map-comp τ' Wmfam Pwfam δ∅)))
         (head-cong (as-poly-map-comp τ' NLfam (λ i → Wmfam i ∘ Pwfam i) δ∅))))
         (head-cong (as-poly-map-comp τ' L'fam (λ i → NLfam i ∘ (Wmfam i ∘ Pwfam i)) δ∅))))
         (head-cong (as-poly-map-comp τ' Kρfam (λ i → L'fam i ∘ (NLfam i ∘ (Wmfam i ∘ Pwfam i))) δ∅))))
         (head-cong (as-poly-map-comp τ' Ebfam (λ i → Kρfam i ∘ (L'fam i ∘ (NLfam i ∘ (Wmfam i ∘ Pwfam i)))) δ∅))) ⟩
      Fq ∘ (as-poly-map τ' famL δ∅ ∘ (Sa ∘ Ca))
    ∎
  rhs : (((((Fq ∘ Mu) ∘ Su) ∘ Cu) ∘ Bu) ∘ ((Fu ∘ Ru) ∘ Tu)) ≈ (Fq ∘ (as-poly-map τ' famR δ∅ ∘ (Sa ∘ Ca)))
  rhs = begin
      ((((Fq ∘ Mu) ∘ Su) ∘ Cu) ∘ Bu) ∘ ((Fu ∘ Ru) ∘ Tu)
    ≈⟨ ≈-trans (assoc _ _ _) (≈-trans (assoc _ _ _) (≈-trans (assoc _ _ _)
       (tail-cong (∘-cong₂ (∘-cong₂ (∘-cong₂ (∘-cong₂ (assoc _ _ _)))))))) ⟩
      Fq ∘ (Mu ∘ (Su ∘ (Cu ∘ (Bu ∘ (Fu ∘ (Ru ∘ Tu))))))
    ≈⟨ ∘-cong₂ (∘-cong₂ (∘-cong₂ (∘-cong₂ (head-cancel (apply-bwd-fwd {0} {1} (unfold₁ τ') ∅ δr))))) ⟩
      Fq ∘ (Mu ∘ (Su ∘ (Cu ∘ (Ru ∘ Tu))))
    ≈⟨ ∘-cong₂ (∘-cong₂ (∘-cong₂ (∘-cong₁ (cast-as-poly-cong {n = 0} (unfold₁ τ') (λ i → sym (concat-emp-pw {δ₀ = δr} i)) δ∅)))) ⟩
      Fq ∘ (Mu ∘ (Su ∘ (Cu' ∘ (Ru ∘ Tu))))
    ≈⟨ ∘-cong₂ (∘-cong₂ (∘-cong₂
       (head-cong (as-poly-map-comp (unfold₁ τ') (λ i → ≡-to-⇒ (sym (concat-emp-pw {δ₀ = δr} i))) gρ δ∅)))) ⟩
      Fq ∘ (Mu ∘ (Su ∘ (CR ∘ Tu)))
    ≈⟨ ∘-cong₂ (∘-cong₂ (head-cong-assoc (≈-sym (subst-fwd-natural σu τ' cu)))) ⟩
      Fq ∘ (Mu ∘ (Nu ∘ (Sup ∘ Tu)))
    ≈⟨ ∘-cong₂ (∘-cong₂ (∘-cong₂ (≈-trans (subst-fwd-sub σu σp τ' e-ss' ∅) (assoc _ _ _)))) ⟩
      Fq ∘ (Mu ∘ (Nu ∘ (Wu ∘ (Sa ∘ Ca))))
    ≈⟨ ∘-cong₂ (≈-trans (∘-cong₂ (head-cong (as-poly-map-comp τ' Nufam Wufam δ∅)))
                        (head-cong (as-poly-map-comp τ' (unfold-pw τ' Xρ) (λ i → Nufam i ∘ Wufam i) δ∅))) ⟩
      Fq ∘ (as-poly-map τ' famR δ∅ ∘ (Sa ∘ Ca))
    ∎

private
  module UnfoldStrong (τ' : type 2) {Γ' : Obj} {Xμ Xσ : obj} (K : prod Γ' Xμ ⇒ Xσ) where
    Q = as-poly {0} {2} τ' ∅
    δ⁺ = λ (X : obj) → extend (extend δ∅ X) (μ-obj Q (extend δ∅ X))
    hsK : ∀ i → prod Γ' (extend δ∅ Xμ i) ⇒ extend δ∅ Xσ i
    hsK = strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ ()) K
    Hs : ∀ i → prod Γ' (δ⁺ Xμ i) ⇒ δ⁺ Xσ i
    Hs = strong-extend-mor hsK (strong-fmor (as-poly {0} {1} (μ τ') ∅) hsK)
    p₂s : ∀ i → prod Γ' (∅ i) ⇒ ∅ i
    p₂s = λ i → p₂
    HC1 = strong-concat-mor {n = 1} hsK p₂s
    F = λ (X : obj) → apply-fwd {0} {2} τ' ∅ (δ⁺ X)
    M = λ (X : obj) → as-poly-map {2} {0} τ' (unfold-pw τ' X) δ∅
    S = λ (X : obj) → subst-fwd (unfold₁-sub τ') τ' (extend δ∅ X)
    C = λ (X : obj) → ≡-to-⇒ (ty-cong (unfold₁ τ') (λ i → sym (concat-emp-pw {δ₀ = extend δ∅ X} i)))
    B = λ (X : obj) → apply-bwd {0} {1} (unfold₁ τ') ∅ (extend δ∅ X)

    unit-K : (K ∘co (id _ ∘ p₂)) ≈ ((id _ ∘ p₂) ∘co K)
    unit-K = ≈-trans (co-unitᵣ K) (≈-sym (co-unitₗ K))

    nat-F : ∀ {n} (τ : type (n + 0)) {δ₀ δ₀' : Fin n → obj} (hs : ∀ i → prod Γ' (δ₀ i) ⇒ δ₀' i) →
            (strong-fmor (as-poly {0} {n} τ ∅) hs ∘co (apply-fwd {0} {n} τ ∅ δ₀ ∘ p₂))
              ≈ ((apply-fwd {0} {n} τ ∅ δ₀' ∘ p₂) ∘co strong-as-poly-map τ (strong-concat-mor hs p₂s) δ∅)
    nat-F τ {δ₀} hs =
      ≈-trans (coKl.∘-cong ≈-refl (≈-sym (≈-trans (coKl.∘-cong (strong-as-poly-map-p₂ τ δ₀) ≈-refl) coKl.id-left)))
              (strong-apply-fwd-natural τ {δ = ∅} {δ' = ∅} p₂s hs)

    nat-cast : ∀ (τ : type 1) {δ₁ δ₁' δ₂ δ₂' : Fin 1 → obj} (h₁ : ∀ i → δ₁ i ≡ δ₁' i) (h₂ : ∀ i → δ₂ i ≡ δ₂' i)
               (hs₁ : ∀ i → prod Γ' (δ₁ i) ⇒ δ₂ i) (hs₂ : ∀ i → prod Γ' (δ₁' i) ⇒ δ₂' i) →
               (∀ i → (hs₂ i ∘co (≡-to-⇒ (h₁ i) ∘ p₂)) ≈ ((≡-to-⇒ (h₂ i) ∘ p₂) ∘co hs₁ i)) →
               (strong-as-poly-map τ hs₂ δ∅ ∘co (≡-to-⇒ (ty-cong τ h₁) ∘ p₂))
                 ≈ ((≡-to-⇒ (ty-cong τ h₂) ∘ p₂) ∘co strong-as-poly-map τ hs₁ δ∅)
    nat-cast τ h₁ h₂ hs₁ hs₂ pw =
      ≈-trans (coKl.∘-cong ≈-refl (∘-cong (cast-as-poly-cong {n = 0} τ h₁ δ∅) ≈-refl))
      (≈-trans (strong-as-poly-map-square τ (λ i → ≡-to-⇒ (h₁ i)) (λ i → ≡-to-⇒ (h₂ i)) hs₁ hs₂ δ∅ pw)
               (coKl.∘-cong (∘-cong (≈-sym (cast-as-poly-cong {n = 0} τ h₂ δ∅)) ≈-refl) ≈-refl))

    pw-M : ∀ i → (strong-concat-mor {n = 2} Hs p₂s i ∘co (unfold-pw τ' Xμ i ∘ p₂))
                   ≈ ((unfold-pw τ' Xσ i ∘ p₂) ∘co strong-as-poly-map (unfold₁-sub τ' i) hsK δ∅)
    pw-M Fin.zero =
      ≈-trans (coKl.∘-cong ≈-refl (lift-comp _ _))
      (≈-trans (≈-sym (coKl.assoc _ _ _))
      (≈-trans (coKl.∘-cong (nat-F {n = 1} (μ τ') hsK) ≈-refl)
      (≈-trans (coKl.assoc _ _ _)
      (≈-trans (coKl.∘-cong ≈-refl (nat-cast (μ τ') (concat-emp-pw {δ₀ = extend δ∅ Xμ}) (concat-emp-pw {δ₀ = extend δ∅ Xσ})
                                            hsK HC1 (λ { Fin.zero → unit-K })))
      (≈-trans (≈-sym (coKl.assoc _ _ _))
               (coKl.∘-cong (≈-sym (lift-comp _ _)) ≈-refl))))))
    pw-M (Fin.suc Fin.zero) = unit-K
    pw-M (Fin.suc (Fin.suc ()))

    sq-M : (strong-as-poly-map τ' (strong-concat-mor {n = 2} Hs p₂s) δ∅ ∘co (M Xμ ∘ p₂))
             ≈ ((M Xσ ∘ p₂) ∘co strong-as-poly-map τ' (λ i → strong-as-poly-map (unfold₁-sub τ' i) hsK δ∅) δ∅)
    sq-M =
      strong-as-poly-map-square τ' (unfold-pw τ' Xμ) (unfold-pw τ' Xσ)
                                (λ i → strong-as-poly-map (unfold₁-sub τ' i) hsK δ∅) (strong-concat-mor {n = 2} Hs p₂s)
                                δ∅ pw-M

    sq-C : (strong-as-poly-map (unfold₁ τ') hsK δ∅ ∘co (C Xμ ∘ p₂))
             ≈ ((C Xσ ∘ p₂) ∘co strong-as-poly-map (unfold₁ τ') HC1 δ∅)
    sq-C = nat-cast (unfold₁ τ') (λ i → sym (concat-emp-pw {δ₀ = extend δ∅ Xμ} i))
                    (λ i → sym (concat-emp-pw {δ₀ = extend δ∅ Xσ} i)) HC1 hsK (λ { Fin.zero → unit-K })

    sq-B : (strong-as-poly-map (unfold₁ τ') HC1 δ∅ ∘co (B Xμ ∘ p₂))
             ≈ ((B Xσ ∘ p₂) ∘co strong-fmor (as-poly {0} {1} (unfold₁ τ') ∅) hsK)
    sq-B =
      ≈-trans (coKl.∘-cong (≈-sym coKl.id-left) ≈-refl)
      (≈-trans (coKl.∘-cong (coKl.∘-cong bf ≈-refl) ≈-refl)
      (≈-trans (coKl.∘-cong (coKl.assoc _ _ _) ≈-refl)
      (≈-trans (coKl.∘-cong (coKl.∘-cong ≈-refl (≈-sym (nat-F {n = 1} (unfold₁ τ') hsK))) ≈-refl)
      (≈-trans (coKl.assoc _ _ _)
      (≈-trans (coKl.∘-cong ≈-refl (coKl.assoc _ _ _))
      (≈-trans (coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl (≈-sym (lift-comp _ _))))
      (≈-trans (coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl (∘-cong (apply-fwd-bwd {0} {1} (unfold₁ τ') ∅ (extend δ∅ Xμ)) ≈-refl)))
               (coKl.∘-cong ≈-refl (co-unitᵣ _)))))))))
      where
        bf : p₂ ≈ ((B Xσ ∘ p₂) ∘co (apply-fwd {0} {1} (unfold₁ τ') ∅ (extend δ∅ Xσ) ∘ p₂))
        bf = ≈-sym (≈-trans (≈-sym (lift-comp _ _))
                   (≈-trans (∘-cong (apply-bwd-fwd {0} {1} (unfold₁ τ') ∅ (extend δ∅ Xσ)) ≈-refl) id-left))

    split : ∀ X → (unfold-as-apply-fwd τ' X ∘ p₂ {x = Γ'})
                    ≈ ((F X ∘ p₂) ∘co ((M X ∘ p₂) ∘co ((S X ∘ p₂) ∘co ((C X ∘ p₂) ∘co (B X ∘ p₂)))))
    split X =
      ≈-trans (lift-comp _ _)
      (≈-trans (coKl.∘-cong (lift-comp _ _) ≈-refl)
      (≈-trans (coKl.assoc _ _ _)
      (≈-trans (coKl.∘-cong (lift-comp _ _) ≈-refl)
      (≈-trans (coKl.assoc _ _ _)
      (≈-trans (coKl.∘-cong (lift-comp _ _) ≈-refl)
               (coKl.assoc _ _ _))))))

    square : (strong-fmor Q Hs ∘co (unfold-as-apply-fwd τ' Xμ ∘ p₂))
               ≈ ((unfold-as-apply-fwd τ' Xσ ∘ p₂) ∘co strong-fmor (as-poly {0} {1} (unfold₁ τ') ∅) hsK)
    square =
      ≈-trans (coKl.∘-cong ≈-refl (split Xμ))
      (≈-trans (≈-sym (coKl.assoc _ _ _))
      (≈-trans (coKl.∘-cong (nat-F {n = 2} τ' Hs) ≈-refl)
      (≈-trans (coKl.assoc _ _ _)
      (≈-trans (coKl.∘-cong ≈-refl (≈-sym (coKl.assoc _ _ _)))
      (≈-trans (coKl.∘-cong ≈-refl (coKl.∘-cong sq-M ≈-refl))
      (≈-trans (coKl.∘-cong ≈-refl (coKl.assoc _ _ _))
      (≈-trans (coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl (≈-sym (coKl.assoc _ _ _))))
      (≈-trans (coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl (coKl.∘-cong (strong-subst-fwd-natural (unfold₁-sub τ') τ' hsK) ≈-refl)))
      (≈-trans (coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl (coKl.assoc _ _ _)))
      (≈-trans (coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl (≈-sym (coKl.assoc _ _ _)))))
      (≈-trans (coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl (coKl.∘-cong sq-C ≈-refl))))
      (≈-trans (coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl (coKl.assoc _ _ _))))
      (≈-trans (coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl sq-B))))
      (≈-trans (coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl (≈-sym (coKl.assoc _ _ _)))))
      (≈-trans (coKl.∘-cong ≈-refl (coKl.∘-cong ≈-refl (≈-sym (coKl.assoc _ _ _))))
      (≈-trans (coKl.∘-cong ≈-refl (≈-sym (coKl.assoc _ _ _)))
      (≈-trans (≈-sym (coKl.assoc _ _ _))
               (coKl.∘-cong (≈-sym (split Xσ)) ≈-refl))))))))))))))))))

abstract
  roll-mor : (τ : type 1) → ⟦ τ [ μ τ ] ⟧ty (λ ()) ⇒ ⟦ μ τ ⟧ty (λ ())
  roll-mor τ = inMap (as-poly τ (λ ())) δ∅ ∘ sub-as-apply-fwd τ (μ τ)

  unroll-mor : (τ : type 1) → ⟦ μ τ ⟧ty (λ ()) ⇒ ⟦ τ [ μ τ ] ⟧ty (λ ())
  unroll-mor τ = sub-as-apply-bwd τ (μ τ) ∘ Fam⟨𝒞⟩μ.LambekDef.outMor (as-poly τ (λ ())) δ∅

  unroll-roll : (τ : type 1) → (unroll-mor τ ∘ roll-mor τ) ≈ id _
  unroll-roll τ =
    ≈-trans (tail-cong (head-cancel (Fam⟨𝒞⟩μ.LambekDef.outMor-inMor (as-poly τ (λ ())) δ∅)))
             (sub-as-apply-bwd-fwd τ (μ τ))

  roll-unroll : (τ : type 1) → (roll-mor τ ∘ unroll-mor τ) ≈ id _
  roll-unroll τ =
    ≈-trans (tail-cong (head-cancel (sub-as-apply-fwd-bwd τ (μ τ))))
             (Fam⟨𝒞⟩μ.LambekDef.inMor-outMor (as-poly τ (λ ())) δ∅)

  sub-as-apply-fwd-roll : ∀ (τ' : type 2) (ρ : type 0) →
    (sub-as-apply-fwd (μ τ') ρ ∘ roll-mor (τ' [ ρ ]₁))
      ≈ (inMap (as-poly {0} {2} τ' (λ ())) (extend δ∅ (⟦ ρ ⟧ty (λ ())))
         ∘ (sub-as-apply-fwd-μ-body τ' ρ (μ-obj (as-poly {0} {2} τ' (λ ())) (extend δ∅ (⟦ ρ ⟧ty (λ ()))))
            ∘ (fmor (as-poly {0} {1} (τ' [ ρ ]₁) (λ ()))
                 (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) (sub-as-apply-fwd (μ τ') ρ))
               ∘ sub-as-apply-fwd (τ' [ ρ ]₁) (μ (τ' [ ρ ]₁)))))
  sub-as-apply-fwd-roll τ' ρ = sub-as-apply-fwd-μ-in τ' ρ

  preserves-sub-as-apply-fwd : ∀ (τ : type 1) (τ' : type 0) →
    preserves-section (sub-as-apply-fwd τ τ')
      (unit-section (τ [ τ' ]) (λ ()) (λ ()))
      (poly-section (as-poly {0} {1} τ (λ ())) (as-poly-section {0} {1} τ (λ ()) (λ ()))
        (extend-section (λ ()) (unit-section τ' (λ ()) (λ ()))))
  preserves-sub-as-apply-fwd τ τ' =
    preserves-section-∘
      (preserves-section-∘
        (preserves-apply-fwd {n = 1} τ (λ ())
          (extend-section (λ ()) (unit-section τ' (λ ()) (λ ()))))
        (preserves-as-poly-map τ (λ { Fin.zero → preserves-section-id (unit-section τ' (λ ()) (λ ())) }) δ∅ (λ ())))
      (preserves-subst-fwd (push τ') τ (λ ()))

  preserves-sub-as-apply-bwd : ∀ (τ : type 1) (τ' : type 0) →
    preserves-section (sub-as-apply-bwd τ τ')
      (poly-section (as-poly {0} {1} τ (λ ())) (as-poly-section {0} {1} τ (λ ()) (λ ()))
        (extend-section (λ ()) (unit-section τ' (λ ()) (λ ()))))
      (unit-section (τ [ τ' ]) (λ ()) (λ ()))
  preserves-sub-as-apply-bwd τ τ' =
    preserves-section-inv (sub-as-apply-fwd-bwd τ τ') (sub-as-apply-bwd-fwd τ τ')
      (preserves-sub-as-apply-fwd τ τ')

  preserves-unroll-ctrl-dep : ∀ (τ : type 1) →
    preserves-section (unroll-mor τ) (ctrl-dep (μ τ)) (ctrl-dep (τ [ μ τ ]))
  preserves-unroll-ctrl-dep τ =
    preserves-scale {w = ctrl-w}
      {c = unit-section (μ τ) (λ ()) (λ ())} {d = unit-section (τ [ μ τ ]) (λ ()) (λ ())}
      (preserves-section-∘ (preserves-sub-as-apply-bwd τ (μ τ))
        (preserves-outMor (as-poly {0} {1} τ (λ ())) δ∅ (λ ()) (as-poly-section {0} {1} τ (λ ()) (λ ()))))

-- Interpretation-side counterpart of the evaluation's Map judgement.
fold-alg : ∀ (τ₀ : type 1) (σ : type 0) {Γ' : Obj} →
           prod Γ' (⟦ τ₀ [ σ ] ⟧ty (λ ())) ⇒ ⟦ σ ⟧ty (λ ()) →
           prod Γ' (fobj μ-obj (as-poly {0} {1} τ₀ (λ ())) (extend δ∅ (⟦ σ ⟧ty (λ ())))) ⇒
             ⟦ σ ⟧ty (λ ())
fold-alg τ₀ σ B = B ∘ prod-m (id _) (sub-as-apply-bwd τ₀ σ)

fold-map : ∀ (τ₀ : type 1) (σ : type 0) (σ' : type 1) {Γ' : Obj} →
           prod Γ' (⟦ τ₀ [ σ ] ⟧ty (λ ())) ⇒ ⟦ σ ⟧ty (λ ()) →
           prod Γ' (⟦ σ' [ μ τ₀ ] ⟧ty (λ ())) ⇒ ⟦ σ' [ σ ] ⟧ty (λ ())
fold-map τ₀ σ σ' B =
  sub-as-apply-bwd σ' σ
    ∘ strong-fmor (as-poly {0} {1} σ' (λ ()))
        (strong-extend-mor (λ ()) (⦅ fold-alg τ₀ σ B ⦆))
    ∘ ⟨ p₁ , sub-as-apply-fwd σ' (μ τ₀) ∘ p₂ ⟩

fold-map-var : ∀ (τ₀ : type 1) (σ : type 0) {Γ' : Obj}
               (B : prod Γ' (⟦ τ₀ [ σ ] ⟧ty (λ ())) ⇒ ⟦ σ ⟧ty (λ ())) →
               fold-map τ₀ σ (var Fin.zero) B ≈ ⦅ fold-alg τ₀ σ B ⦆
fold-map-var τ₀ σ B =
  ≈-trans (∘-cong (∘-cong bwd-id ≈-refl) (pair-cong ≈-refl (∘-cong fwd-id ≈-refl)))
  (≈-trans (∘-cong id-left (pair-cong ≈-refl id-left))
  (≈-trans (∘-cong ≈-refl pair-ext0) id-right))
  where
  bwd-id : sub-as-apply-bwd (var Fin.zero) σ ≈ id _
  bwd-id = ≈-trans (∘-cong id-left ≈-refl) id-left
  fwd-id : sub-as-apply-fwd (var Fin.zero) (μ τ₀) ≈ id _
  fwd-id = ≈-trans (∘-cong id-left ≈-refl) id-left

abstract
  fold-map-rec : ∀ (τ₀ : type 1) (σ : type 0) {Γ' : Obj}
                 (B : prod Γ' (⟦ τ₀ [ σ ] ⟧ty (λ ())) ⇒ ⟦ σ ⟧ty (λ ())) →
                 (fold-map τ₀ σ (var Fin.zero) B ∘ ⟨ p₁ , roll-mor τ₀ ∘ p₂ ⟩) ≈ (B ∘ ⟨ p₁ , fold-map τ₀ σ τ₀ B ⟩)
  fold-map-rec τ₀ σ {Γ'} B = begin
      fold-map τ₀ σ (var Fin.zero) B ∘ ⟨ p₁ , roll-mor τ₀ ∘ p₂ ⟩
    ≈⟨ coKl.∘-cong (fold-map-var τ₀ σ B) (lift-comp (inMap (as-poly {0} {1} τ₀ (λ ())) δ∅) (sub-as-apply-fwd τ₀ (μ τ₀))) ⟩
      ⦅ fold-alg τ₀ σ B ⦆ ∘co ((inMap (as-poly {0} {1} τ₀ (λ ())) δ∅ ∘ p₂) ∘co (sub-as-apply-fwd τ₀ (μ τ₀) ∘ p₂))
    ≈˘⟨ coKl.assoc _ _ _ ⟩
      (⦅ fold-alg τ₀ σ B ⦆ ∘co (inMap (as-poly {0} {1} τ₀ (λ ())) δ∅ ∘ p₂)) ∘co (sub-as-apply-fwd τ₀ (μ τ₀) ∘ p₂)
    ≈⟨ coKl.∘-cong (⦅⦆-β {P = as-poly {0} {1} τ₀ (λ ())} {δ = δ∅} (fold-alg τ₀ σ B)) ≈-refl ⟩
      (fold-alg τ₀ σ B ∘co strong-fmor (as-poly {0} {1} τ₀ (λ ())) (strong-extend-mor (λ i → p₂) ⦅ fold-alg τ₀ σ B ⦆))
        ∘co (sub-as-apply-fwd τ₀ (μ τ₀) ∘ p₂)
    ≈⟨ coKl.assoc _ _ _ ⟩
      fold-alg τ₀ σ B
        ∘co (strong-fmor (as-poly {0} {1} τ₀ (λ ())) (strong-extend-mor (λ i → p₂) ⦅ fold-alg τ₀ σ B ⦆) ∘co (sub-as-apply-fwd τ₀ (μ τ₀) ∘ p₂))
    ≈⟨ assoc _ _ _ ⟩
      B ∘ (prod-m (id _) (sub-as-apply-bwd τ₀ σ)
           ∘ ⟨ p₁ , strong-fmor (as-poly {0} {1} τ₀ (λ ())) (strong-extend-mor (λ i → p₂) ⦅ fold-alg τ₀ σ B ⦆) ∘co (sub-as-apply-fwd τ₀ (μ τ₀) ∘ p₂) ⟩)
    ≈⟨ ∘-cong ≈-refl (pair-compose _ _ _ _) ⟩
      B ∘ ⟨ id _ ∘ p₁ ,
            sub-as-apply-bwd τ₀ σ
              ∘ (strong-fmor (as-poly {0} {1} τ₀ (λ ())) (strong-extend-mor (λ i → p₂) ⦅ fold-alg τ₀ σ B ⦆) ∘co (sub-as-apply-fwd τ₀ (μ τ₀) ∘ p₂)) ⟩
    ≈⟨ ∘-cong ≈-refl (pair-cong id-left (≈-trans (∘-cong ≈-refl (∘-cong (strong-fmor-cong (as-poly {0} {1} τ₀ (λ ())) pw) ≈-refl))
                                                 (≈-sym (assoc _ _ _)))) ⟩
      B ∘ ⟨ p₁ , fold-map τ₀ σ τ₀ B ⟩
    ∎
    where
    open ≈-Reasoning isEquiv
    pw : ∀ i → strong-extend-mor (λ i → p₂) (⦅_⦆ {P = as-poly {0} {1} τ₀ (λ ())} {δ = δ∅} (fold-alg τ₀ σ B)) i
               ≈ strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ ()) (⦅_⦆ {P = as-poly {0} {1} τ₀ (λ ())} {δ = δ∅} (fold-alg τ₀ σ B)) i
    pw Fin.zero = ≈-refl
    pw (Fin.suc ())

private
  fold-map-const : ∀ {Γ' X : Obj} (f g : X ⇒ X) → f ≈ id X → g ≈ id X →
                   ((f ∘ p₂ {Γ'}) ∘ ⟨ p₁ , g ∘ p₂ ⟩) ≈ p₂
  fold-map-const f g bwd-id fwd-id =
    ≈-trans (∘-cong (∘-cong bwd-id ≈-refl) (pair-cong ≈-refl (∘-cong fwd-id ≈-refl)))
            (≈-trans (∘-cong id-left (pair-cong ≈-refl id-left)) (pair-p₂ _ _))

fold-map-unit : ∀ (τ₀ : type 1) (σ : type 0) {Γ' : Obj}
                (B : prod Γ' (⟦ τ₀ [ σ ] ⟧ty (λ ())) ⇒ ⟦ σ ⟧ty (λ ())) →
                fold-map τ₀ σ unit B ≈ p₂
fold-map-unit τ₀ σ B =
  fold-map-const (sub-as-apply-bwd unit σ) (sub-as-apply-fwd unit (μ τ₀))
                 (≈-trans (∘-cong id-left ≈-refl) id-left) (≈-trans (∘-cong id-left ≈-refl) id-left)

fold-map-base : ∀ (τ₀ : type 1) (σ : type 0) b {Γ' : Obj}
                (B : prod Γ' (⟦ τ₀ [ σ ] ⟧ty (λ ())) ⇒ ⟦ σ ⟧ty (λ ())) →
                fold-map τ₀ σ (base b) B ≈ p₂
fold-map-base τ₀ σ b B =
  fold-map-const (sub-as-apply-bwd (base b) σ) (sub-as-apply-fwd (base b) (μ τ₀))
                 (≈-trans (∘-cong id-left ≈-refl) id-left) (≈-trans (∘-cong id-left ≈-refl) id-left)

fold-map-arrow : ∀ (τ₀ : type 1) (σ : type 0) (σ₁ σ₂ : type 0) {Γ' : Obj}
                 (B : prod Γ' (⟦ τ₀ [ σ ] ⟧ty (λ ())) ⇒ ⟦ σ ⟧ty (λ ())) →
                 fold-map τ₀ σ (σ₁ [→] σ₂) B ≈ p₂
fold-map-arrow τ₀ σ σ₁ σ₂ B =
  fold-map-const (sub-as-apply-bwd (σ₁ [→] σ₂) σ) (sub-as-apply-fwd (σ₁ [→] σ₂) (μ τ₀))
                 (≈-trans (∘-cong id-left ≈-refl) id-left) (≈-trans (∘-cong id-left ≈-refl) id-left)

private
  sub-as-apply-fwd-[+] : ∀ (σ₁ σ₂ : type 1) (τ' : type 0) →
    sub-as-apply-fwd (σ₁ [+] σ₂) τ' ≈ [+]-map (sub-as-apply-fwd σ₁ τ') (sub-as-apply-fwd σ₂ τ')
  sub-as-apply-fwd-[+] σ₁ σ₂ τ' =
    ≈-trans (∘-cong ([+]-map-comp _ _ _ _) ≈-refl) ([+]-map-comp _ _ _ _)

  sub-as-apply-bwd-[+] : ∀ (σ₁ σ₂ : type 1) (τ' : type 0) →
    sub-as-apply-bwd (σ₁ [+] σ₂) τ' ≈ [+]-map (sub-as-apply-bwd σ₁ τ') (sub-as-apply-bwd σ₂ τ')
  sub-as-apply-bwd-[+] σ₁ σ₂ τ' = ≈-trans (∘-cong ([+]-map-comp _ _ _ _) ≈-refl) ([+]-map-comp _ _ _ _)

  sub-as-apply-fwd-[×] : ∀ (σ₁ σ₂ : type 1) (τ' : type 0) →
    sub-as-apply-fwd (σ₁ [×] σ₂) τ' ≈ [×]-map (sub-as-apply-fwd σ₁ τ') (sub-as-apply-fwd σ₂ τ')
  sub-as-apply-fwd-[×] σ₁ σ₂ τ' = ≈-trans (∘-cong ([×]-map-comp _ _ _ _) ≈-refl) ([×]-map-comp _ _ _ _)

  sub-as-apply-bwd-[×] : ∀ (σ₁ σ₂ : type 1) (τ' : type 0) →
    sub-as-apply-bwd (σ₁ [×] σ₂) τ' ≈ [×]-map (sub-as-apply-bwd σ₁ τ') (sub-as-apply-bwd σ₂ τ')
  sub-as-apply-bwd-[×] σ₁ σ₂ τ' = ≈-trans (∘-cong ([×]-map-comp _ _ _ _) ≈-refl) ([×]-map-comp _ _ _ _)

private
  fold-strong : ∀ (τ₀ : type 1) (σ : type 0) (σ' : type 1) {Γ' : Obj} →
                prod Γ' (⟦ τ₀ [ σ ] ⟧ty (λ ())) ⇒ ⟦ σ ⟧ty (λ ()) →
                prod Γ' (fobj μ-obj (as-poly {0} {1} σ' (λ ())) (extend δ∅ (⟦ μ τ₀ ⟧ty (λ ()))))
                  ⇒ fobj μ-obj (as-poly {0} {1} σ' (λ ())) (extend δ∅ (⟦ σ ⟧ty (λ ())))
  fold-strong τ₀ σ σ' B = strong-fmor (as-poly {0} {1} σ' (λ ())) (strong-extend-mor (λ ()) (⦅ fold-alg τ₀ σ B ⦆))

  fold-through : ∀ {Γ' : Obj} {X X' Y Y' Z Z' W W' : obj}
                 (b : Z ⇒ W) (S : prod Γ' Y ⇒ Z) (f : X ⇒ Y) (b' : Z' ⇒ W') (S' : prod Γ' Y' ⇒ Z') (f' : X' ⇒ Y')
                 (c : X' ⇒ X) (c₁ : Y' ⇒ Y) (c₂ : Z' ⇒ Z) (c' : W' ⇒ W) →
                 (f ∘ c) ≈ (c₁ ∘ f') → (S ∘co (c₁ ∘ p₂)) ≈ (c₂ ∘ S') → (b ∘ c₂) ≈ (c' ∘ b') →
                 (((b ∘ S) ∘co (f ∘ p₂)) ∘co (c ∘ p₂)) ≈ (c' ∘ ((b' ∘ S') ∘co (f' ∘ p₂)))
  fold-through b S f b' S' f' c c₁ c₂ c' nf nS nb =
    ≈-trans (∘co-push (b ∘ S) f (c ∘ p₂))
    (≈-trans (coKl.∘-cong ≈-refl (≈-trans (head-cong nf) (lift-comp c₁ f')))
    (≈-trans (≈-sym (coKl.assoc _ _ _))
    (≈-trans (coKl.∘-cong (≈-trans (tail-cong nS)
                          (head-cong-assoc nb)) ≈-refl)
             (assoc _ _ _))))

  strong-Lf-map-fold : ∀ {Γ' : Obj} {X Y Z W : obj} (b : Z ⇒ W) (S : prod Γ' Y ⇒ Z) (f : X ⇒ Y) →
                       ((Lf-map b ∘ strong-Lf-map S) ∘co (Lf-map f ∘ p₂)) ≈ strong-Lf-map ((b ∘ S) ∘co (f ∘ p₂))
  strong-Lf-map-fold b S f =
    ≈-trans (∘-cong (strong-Lf-map-post b S) (pair-cong (≈-sym id-left) ≈-refl))
    (≈-trans (strong-Lf-map-pre (id _) (b ∘ S) f)
             (strong-Lf-map-cong (∘-cong ≈-refl (pair-cong id-left ≈-refl))))

  strong-prod-m-fold : ∀ {Γ' : Obj} {X₁ X₂ Y₁ Y₂ Z₁ Z₂ W₁ W₂ : obj}
                       (b₁ : Z₁ ⇒ W₁) (b₂ : Z₂ ⇒ W₂) (S₁ : prod Γ' Y₁ ⇒ Z₁) (S₂ : prod Γ' Y₂ ⇒ Z₂)
                       (f₁ : X₁ ⇒ Y₁) (f₂ : X₂ ⇒ Y₂) →
                       ((prod-m b₁ b₂ ∘ strong-prod-m S₁ S₂) ∘co (prod-m f₁ f₂ ∘ p₂))
                         ≈ strong-prod-m ((b₁ ∘ S₁) ∘co (f₁ ∘ p₂)) ((b₂ ∘ S₂) ∘co (f₂ ∘ p₂))
  strong-prod-m-fold b₁ b₂ S₁ S₂ f₁ f₂ =
    ≈-trans (∘-cong (strong-prod-m-post b₁ b₂ S₁ S₂) (pair-cong (≈-sym id-left) ≈-refl))
    (≈-trans (strong-prod-m-pre (b₁ ∘ S₁) (b₂ ∘ S₂) (id _) f₁ f₂)
             (strong-prod-m-cong (∘-cong ≈-refl (pair-cong id-left ≈-refl))
                                 (∘-cong ≈-refl (pair-cong id-left ≈-refl))))

fold-map-inl : ∀ (τ₀ : type 1) (σ : type 0) (σ₁ σ₂ : type 1) {Γ' : Obj}
               (B : prod Γ' (⟦ τ₀ [ σ ] ⟧ty (λ ())) ⇒ ⟦ σ ⟧ty (λ ())) →
               (fold-map τ₀ σ (σ₁ [+] σ₂) B ∘ ⟨ p₁ , (in₁ ∘ injF) ∘ p₂ ⟩)
                 ≈ ((in₁ ∘ injF) ∘ fold-map τ₀ σ σ₁ B)
fold-map-inl τ₀ σ σ₁ σ₂ B =
  fold-through b⁺ S⁺ f⁺ b₁ S₁ f₁ (in₁ ∘ injF) (in₁ ∘ injF) (in₁ ∘ injF) (in₁ ∘ injF)
    (≈-trans (∘-cong (sub-as-apply-fwd-[+] σ₁ σ₂ (μ τ₀)) ≈-refl) ([+]-map-inj₁ f₁ (sub-as-apply-fwd σ₂ (μ τ₀))))
    (≈-trans (coKl.∘-cong ≈-refl (lift-comp in₁ injF))
    (≈-trans (≈-sym (coKl.assoc _ _ _))
    (≈-trans (coKl.∘-cong (scopair-in₁ _ _) ≈-refl)
    (tail-cong-assoc (strong-Lf-map-injF S₁)))))
    (≈-trans (∘-cong (sub-as-apply-bwd-[+] σ₁ σ₂ σ) ≈-refl) ([+]-map-inj₁ b₁ (sub-as-apply-bwd σ₂ σ)))
  where
  f⁺ = sub-as-apply-fwd (σ₁ [+] σ₂) (μ τ₀)
  b⁺ = sub-as-apply-bwd (σ₁ [+] σ₂) σ
  S⁺ = fold-strong τ₀ σ (σ₁ [+] σ₂) B
  f₁ = sub-as-apply-fwd σ₁ (μ τ₀)
  b₁ = sub-as-apply-bwd σ₁ σ
  S₁ = fold-strong τ₀ σ σ₁ B

fold-map-inr : ∀ (τ₀ : type 1) (σ : type 0) (σ₁ σ₂ : type 1) {Γ' : Obj}
               (B : prod Γ' (⟦ τ₀ [ σ ] ⟧ty (λ ())) ⇒ ⟦ σ ⟧ty (λ ())) →
               (fold-map τ₀ σ (σ₁ [+] σ₂) B ∘ ⟨ p₁ , (in₂ ∘ injF) ∘ p₂ ⟩)
                 ≈ ((in₂ ∘ injF) ∘ fold-map τ₀ σ σ₂ B)
fold-map-inr τ₀ σ σ₁ σ₂ B =
  fold-through b⁺ S⁺ f⁺ b₂ S₂ f₂ (in₂ ∘ injF) (in₂ ∘ injF) (in₂ ∘ injF) (in₂ ∘ injF)
    (≈-trans (∘-cong (sub-as-apply-fwd-[+] σ₁ σ₂ (μ τ₀)) ≈-refl) ([+]-map-inj₂ (sub-as-apply-fwd σ₁ (μ τ₀)) f₂))
    (≈-trans (coKl.∘-cong ≈-refl (lift-comp in₂ injF))
    (≈-trans (≈-sym (coKl.assoc _ _ _))
    (≈-trans (coKl.∘-cong (scopair-in₂ _ _) ≈-refl)
    (tail-cong-assoc (strong-Lf-map-injF S₂)))))
    (≈-trans (∘-cong (sub-as-apply-bwd-[+] σ₁ σ₂ σ) ≈-refl) ([+]-map-inj₂ (sub-as-apply-bwd σ₁ σ) b₂))
  where
  f⁺ = sub-as-apply-fwd (σ₁ [+] σ₂) (μ τ₀)
  b⁺ = sub-as-apply-bwd (σ₁ [+] σ₂) σ
  S⁺ = fold-strong τ₀ σ (σ₁ [+] σ₂) B
  f₂ = sub-as-apply-fwd σ₂ (μ τ₀)
  b₂ = sub-as-apply-bwd σ₂ σ
  S₂ = fold-strong τ₀ σ σ₂ B

fold-map-inl-L : ∀ (τ₀ : type 1) (σ : type 0) (σ₁ σ₂ : type 1) {Γ' : Obj}
                 (B : prod Γ' (⟦ τ₀ [ σ ] ⟧ty (λ ())) ⇒ ⟦ σ ⟧ty (λ ())) →
                 (fold-map τ₀ σ (σ₁ [+] σ₂) B ∘ ⟨ p₁ , in₁ ∘ p₂ ⟩)
                   ≈ (in₁ ∘ strong-Lf-map (fold-map τ₀ σ σ₁ B))
fold-map-inl-L τ₀ σ σ₁ σ₂ B =
  ≈-trans (fold-through b⁺ S⁺ f⁺ (Lf-map b₁) (strong-Lf-map S₁) (Lf-map f₁) in₁ in₁ in₁ in₁
             (≈-trans (∘-cong (sub-as-apply-fwd-[+] σ₁ σ₂ (μ τ₀)) ≈-refl) ([+]-map-in₁ f₁ (sub-as-apply-fwd σ₂ (μ τ₀))))
             (scopair-in₁ _ _)
             (≈-trans (∘-cong (sub-as-apply-bwd-[+] σ₁ σ₂ σ) ≈-refl) ([+]-map-in₁ b₁ (sub-as-apply-bwd σ₂ σ))))
          (∘-cong ≈-refl (strong-Lf-map-fold b₁ S₁ f₁))
  where
  f⁺ = sub-as-apply-fwd (σ₁ [+] σ₂) (μ τ₀)
  b⁺ = sub-as-apply-bwd (σ₁ [+] σ₂) σ
  S⁺ = fold-strong τ₀ σ (σ₁ [+] σ₂) B
  f₁ = sub-as-apply-fwd σ₁ (μ τ₀)
  b₁ = sub-as-apply-bwd σ₁ σ
  S₁ = fold-strong τ₀ σ σ₁ B

fold-map-inr-L : ∀ (τ₀ : type 1) (σ : type 0) (σ₁ σ₂ : type 1) {Γ' : Obj}
                 (B : prod Γ' (⟦ τ₀ [ σ ] ⟧ty (λ ())) ⇒ ⟦ σ ⟧ty (λ ())) →
                 (fold-map τ₀ σ (σ₁ [+] σ₂) B ∘ ⟨ p₁ , in₂ ∘ p₂ ⟩)
                   ≈ (in₂ ∘ strong-Lf-map (fold-map τ₀ σ σ₂ B))
fold-map-inr-L τ₀ σ σ₁ σ₂ B =
  ≈-trans (fold-through b⁺ S⁺ f⁺ (Lf-map b₂) (strong-Lf-map S₂) (Lf-map f₂) in₂ in₂ in₂ in₂
             (≈-trans (∘-cong (sub-as-apply-fwd-[+] σ₁ σ₂ (μ τ₀)) ≈-refl) ([+]-map-in₂ (sub-as-apply-fwd σ₁ (μ τ₀)) f₂))
             (scopair-in₂ _ _)
             (≈-trans (∘-cong (sub-as-apply-bwd-[+] σ₁ σ₂ σ) ≈-refl) ([+]-map-in₂ (sub-as-apply-bwd σ₁ σ) b₂)))
          (∘-cong ≈-refl (strong-Lf-map-fold b₂ S₂ f₂))
  where
  f⁺ = sub-as-apply-fwd (σ₁ [+] σ₂) (μ τ₀)
  b⁺ = sub-as-apply-bwd (σ₁ [+] σ₂) σ
  S⁺ = fold-strong τ₀ σ (σ₁ [+] σ₂) B
  f₂ = sub-as-apply-fwd σ₂ (μ τ₀)
  b₂ = sub-as-apply-bwd σ₂ σ
  S₂ = fold-strong τ₀ σ σ₂ B

fold-map-pair : ∀ (τ₀ : type 1) (σ : type 0) (σ₁ σ₂ : type 1) {Γ' : Obj}
                (B : prod Γ' (⟦ τ₀ [ σ ] ⟧ty (λ ())) ⇒ ⟦ σ ⟧ty (λ ())) →
                (fold-map τ₀ σ (σ₁ [×] σ₂) B ∘ ⟨ p₁ , injF ∘ p₂ ⟩)
                  ≈ (injF ∘ strong-prod-m (fold-map τ₀ σ σ₁ B) (fold-map τ₀ σ σ₂ B))
fold-map-pair τ₀ σ σ₁ σ₂ B =
  ≈-trans (fold-through b× S× f× (prod-m b₁ b₂) (strong-prod-m S₁ S₂) (prod-m f₁ f₂) injF injF injF injF
             (≈-trans (∘-cong (sub-as-apply-fwd-[×] σ₁ σ₂ (μ τ₀)) ≈-refl) (injF-natural (prod-m f₁ f₂)))
             (strong-Lf-map-injF (strong-prod-m S₁ S₂))
             (≈-trans (∘-cong (sub-as-apply-bwd-[×] σ₁ σ₂ σ) ≈-refl) (injF-natural (prod-m b₁ b₂))))
          (∘-cong ≈-refl (strong-prod-m-fold b₁ b₂ S₁ S₂ f₁ f₂))
  where
  f× = sub-as-apply-fwd (σ₁ [×] σ₂) (μ τ₀)
  b× = sub-as-apply-bwd (σ₁ [×] σ₂) σ
  S× = fold-strong τ₀ σ (σ₁ [×] σ₂) B
  f₁ = sub-as-apply-fwd σ₁ (μ τ₀)
  f₂ = sub-as-apply-fwd σ₂ (μ τ₀)
  b₁ = sub-as-apply-bwd σ₁ σ
  b₂ = sub-as-apply-bwd σ₂ σ
  S₁ = fold-strong τ₀ σ σ₁ B
  S₂ = fold-strong τ₀ σ σ₂ B

fold-map-pair-L : ∀ (τ₀ : type 1) (σ : type 0) (σ₁ σ₂ : type 1) {Γ' : Obj}
                  (B : prod Γ' (⟦ τ₀ [ σ ] ⟧ty (λ ())) ⇒ ⟦ σ ⟧ty (λ ())) →
                  fold-map τ₀ σ (σ₁ [×] σ₂) B
                    ≈ strong-Lf-map (strong-prod-m (fold-map τ₀ σ σ₁ B) (fold-map τ₀ σ σ₂ B))
fold-map-pair-L τ₀ σ σ₁ σ₂ B =
  ≈-trans (coKl.∘-cong (∘-cong (sub-as-apply-bwd-[×] σ₁ σ₂ σ) ≈-refl) (∘-cong (sub-as-apply-fwd-[×] σ₁ σ₂ (μ τ₀)) ≈-refl))
  (≈-trans (strong-Lf-map-fold (prod-m b₁ b₂) (strong-prod-m S₁ S₂) (prod-m f₁ f₂))
           (strong-Lf-map-cong (strong-prod-m-fold b₁ b₂ S₁ S₂ f₁ f₂)))
  where
  f₁ = sub-as-apply-fwd σ₁ (μ τ₀)
  f₂ = sub-as-apply-fwd σ₂ (μ τ₀)
  b₁ = sub-as-apply-bwd σ₁ σ
  b₂ = sub-as-apply-bwd σ₂ σ
  S₁ = fold-strong τ₀ σ σ₁ B
  S₂ = fold-strong τ₀ σ σ₂ B

fold-map-mu : ∀ (τ₀ : type 1) (σ : type 0) (τ' : type 2) {Γ' : Obj}
              (B : prod Γ' (⟦ τ₀ [ σ ] ⟧ty (λ ())) ⇒ ⟦ σ ⟧ty (λ ())) →
              (fold-map τ₀ σ (μ τ') B
                 ∘ ⟨ p₁ , (roll-mor (τ' [ μ τ₀ ]₁)
                            ∘ ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty (λ ())) (unfold₁-inst τ' (μ τ₀)))) ∘ p₂ ⟩)
                ≈ ((roll-mor (τ' [ σ ]₁)
                      ∘ ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty (λ ())) (unfold₁-inst τ' σ)))
                   ∘ fold-map τ₀ σ (unfold₁ τ') B)
fold-map-mu τ₀ σ τ' {Γ'} B =
  ≈-trans (coKl.assoc _ _ _)
  (≈-trans (coKl.∘-cong ≈-refl (≈-sym (lift-comp _ _)))
  (≈-trans (tail-cong core)
   (head-cancel (sub-as-apply-bwd-fwd (μ τ') σ))))
  where
  open ≈-Reasoning isEquiv
  Q = as-poly {0} {2} τ' ∅
  hsK = strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ ()) (⦅ fold-alg τ₀ σ B ⦆)
  rc = λ (ρ : type 0) → roll-mor (τ' [ ρ ]₁) ∘ ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty ∅) (unfold₁-inst τ' ρ))
  rollcast : ∀ (ρ : type 0) →
             (sub-as-apply-fwd (μ τ') ρ ∘ rc ρ)
               ≈ (inMap Q (extend δ∅ (⟦ ρ ⟧ty ∅)) ∘ (unfold-as-apply-fwd τ' (⟦ ρ ⟧ty ∅) ∘ sub-as-apply-fwd (unfold₁ τ') ρ))
  rollcast ρ =
    ≈-trans (head-cong (sub-as-apply-fwd-roll τ' ρ))
    (tail-cong (≈-trans (tail-cong (assoc _ _ _))
                         (unfold-as-apply-fwd-inst τ' ρ)))
  beta : (strong-fmor (as-poly {0} {1} (μ τ') ∅) hsK ∘co (inMap Q (extend δ∅ (⟦ μ τ₀ ⟧ty ∅)) ∘ p₂))
           ≈ ((inMap Q (extend δ∅ (⟦ σ ⟧ty ∅)) ∘ p₂)
              ∘co strong-fmor Q (strong-extend-mor hsK (strong-fmor (as-poly {0} {1} (μ τ') ∅) hsK)))
  beta =
    ≈-trans (⦅⦆-β {P = Q} {δ = extend δ∅ (⟦ μ τ₀ ⟧ty ∅)}
                  (inMap Q (extend δ∅ (⟦ σ ⟧ty ∅)) ∘ strong-fmor Q (strong-extend-mor hsK p₂)))
    (≈-trans (tail-cong (≈-trans (strong-fmor-comp Q _ _)
                                 (strong-fmor-cong Q (strong-extend-mor-comp (λ i → coKl.id-right) coKl.id-left))))
              (≈-sym (lift-post _ _)))
  core : (strong-fmor (as-poly {0} {1} (μ τ') ∅) hsK ∘co ((sub-as-apply-fwd (μ τ') (μ τ₀) ∘ rc (μ τ₀)) ∘ p₂))
           ≈ (sub-as-apply-fwd (μ τ') σ ∘ (rc σ ∘ fold-map τ₀ σ (unfold₁ τ') B))
  core = begin
      strong-fmor (as-poly {0} {1} (μ τ') ∅) hsK ∘co ((sub-as-apply-fwd (μ τ') (μ τ₀) ∘ rc (μ τ₀)) ∘ p₂)
    ≈⟨ coKl.∘-cong ≈-refl (∘-cong (rollcast (μ τ₀)) ≈-refl) ⟩
      strong-fmor (as-poly {0} {1} (μ τ') ∅) hsK
        ∘co ((inMap Q (extend δ∅ (⟦ μ τ₀ ⟧ty ∅)) ∘ (unfold-as-apply-fwd τ' (⟦ μ τ₀ ⟧ty ∅) ∘ sub-as-apply-fwd (unfold₁ τ') (μ τ₀))) ∘ p₂)
    ≈⟨ coKl.∘-cong ≈-refl (≈-trans (lift-comp _ _) (coKl.∘-cong ≈-refl (lift-comp _ _))) ⟩
      strong-fmor (as-poly {0} {1} (μ τ') ∅) hsK
        ∘co ((inMap Q (extend δ∅ (⟦ μ τ₀ ⟧ty ∅)) ∘ p₂)
             ∘co ((unfold-as-apply-fwd τ' (⟦ μ τ₀ ⟧ty ∅) ∘ p₂) ∘co (sub-as-apply-fwd (unfold₁ τ') (μ τ₀) ∘ p₂)))
    ≈˘⟨ coKl.assoc _ _ _ ⟩
      (strong-fmor (as-poly {0} {1} (μ τ') ∅) hsK ∘co (inMap Q (extend δ∅ (⟦ μ τ₀ ⟧ty ∅)) ∘ p₂))
        ∘co ((unfold-as-apply-fwd τ' (⟦ μ τ₀ ⟧ty ∅) ∘ p₂) ∘co (sub-as-apply-fwd (unfold₁ τ') (μ τ₀) ∘ p₂))
    ≈⟨ coKl.∘-cong beta ≈-refl ⟩
      ((inMap Q (extend δ∅ (⟦ σ ⟧ty ∅)) ∘ p₂)
         ∘co strong-fmor Q (strong-extend-mor hsK (strong-fmor (as-poly {0} {1} (μ τ') ∅) hsK)))
        ∘co ((unfold-as-apply-fwd τ' (⟦ μ τ₀ ⟧ty ∅) ∘ p₂) ∘co (sub-as-apply-fwd (unfold₁ τ') (μ τ₀) ∘ p₂))
    ≈⟨ ≈-trans (coKl.assoc _ _ _) (coKl.∘-cong ≈-refl (≈-sym (coKl.assoc _ _ _))) ⟩
      (inMap Q (extend δ∅ (⟦ σ ⟧ty ∅)) ∘ p₂)
        ∘co ((strong-fmor Q (strong-extend-mor hsK (strong-fmor (as-poly {0} {1} (μ τ') ∅) hsK))
                ∘co (unfold-as-apply-fwd τ' (⟦ μ τ₀ ⟧ty ∅) ∘ p₂))
             ∘co (sub-as-apply-fwd (unfold₁ τ') (μ τ₀) ∘ p₂))
    ≈⟨ coKl.∘-cong ≈-refl (coKl.∘-cong (UnfoldStrong.square τ' (⦅ fold-alg τ₀ σ B ⦆)) ≈-refl) ⟩
      (inMap Q (extend δ∅ (⟦ σ ⟧ty ∅)) ∘ p₂)
        ∘co (((unfold-as-apply-fwd τ' (⟦ σ ⟧ty ∅) ∘ p₂) ∘co strong-fmor (as-poly {0} {1} (unfold₁ τ') ∅) hsK)
             ∘co (sub-as-apply-fwd (unfold₁ τ') (μ τ₀) ∘ p₂))
    ≈⟨ ≈-trans (coKl.∘-cong ≈-refl (coKl.assoc _ _ _)) (≈-sym (coKl.assoc _ _ _)) ⟩
      ((inMap Q (extend δ∅ (⟦ σ ⟧ty ∅)) ∘ p₂) ∘co (unfold-as-apply-fwd τ' (⟦ σ ⟧ty ∅) ∘ p₂))
        ∘co (strong-fmor (as-poly {0} {1} (unfold₁ τ') ∅) hsK ∘co (sub-as-apply-fwd (unfold₁ τ') (μ τ₀) ∘ p₂))
    ≈˘⟨ coKl.∘-cong (lift-comp _ _) ≈-refl ⟩
      ((inMap Q (extend δ∅ (⟦ σ ⟧ty ∅)) ∘ unfold-as-apply-fwd τ' (⟦ σ ⟧ty ∅)) ∘ p₂)
        ∘co (strong-fmor (as-poly {0} {1} (unfold₁ τ') ∅) hsK ∘co (sub-as-apply-fwd (unfold₁ τ') (μ τ₀) ∘ p₂))
    ≈˘⟨ coKl.assoc _ _ _ ⟩
      (((inMap Q (extend δ∅ (⟦ σ ⟧ty ∅)) ∘ unfold-as-apply-fwd τ' (⟦ σ ⟧ty ∅)) ∘ p₂)
         ∘co strong-fmor (as-poly {0} {1} (unfold₁ τ') ∅) hsK)
        ∘co (sub-as-apply-fwd (unfold₁ τ') (μ τ₀) ∘ p₂)
    ≈⟨ coKl.∘-cong (lift-post _ _) ≈-refl ⟩
      ((inMap Q (extend δ∅ (⟦ σ ⟧ty ∅)) ∘ unfold-as-apply-fwd τ' (⟦ σ ⟧ty ∅)) ∘ strong-fmor (as-poly {0} {1} (unfold₁ τ') ∅) hsK)
        ∘co (sub-as-apply-fwd (unfold₁ τ') (μ τ₀) ∘ p₂)
    ≈˘⟨ ∘-cong (tail-cong-assoc (tail-cong (head-cancel (sub-as-apply-fwd-bwd (unfold₁ τ') σ)))) ≈-refl ⟩
      ((inMap Q (extend δ∅ (⟦ σ ⟧ty ∅)) ∘ (unfold-as-apply-fwd τ' (⟦ σ ⟧ty ∅) ∘ sub-as-apply-fwd (unfold₁ τ') σ))
         ∘ (sub-as-apply-bwd (unfold₁ τ') σ ∘ strong-fmor (as-poly {0} {1} (unfold₁ τ') ∅) hsK))
        ∘co (sub-as-apply-fwd (unfold₁ τ') (μ τ₀) ∘ p₂)
    ≈˘⟨ ∘-cong (∘-cong (rollcast σ) ≈-refl) ≈-refl ⟩
      ((sub-as-apply-fwd (μ τ') σ ∘ rc σ)
         ∘ (sub-as-apply-bwd (unfold₁ τ') σ ∘ strong-fmor (as-poly {0} {1} (unfold₁ τ') ∅) hsK))
        ∘co (sub-as-apply-fwd (unfold₁ τ') (μ τ₀) ∘ p₂)
    ≈⟨ ≈-trans (assoc _ _ _) (assoc _ _ _) ⟩
      sub-as-apply-fwd (μ τ') σ ∘ (rc σ ∘ fold-map τ₀ σ (unfold₁ τ') B)
    ∎

⟦_⟧ctxt : ctxt → obj
⟦ emp ⟧ctxt   = 𝟙
⟦ Γ , τ ⟧ctxt = prod ⟦ Γ ⟧ctxt (⟦ τ ⟧ty (λ ()))

⟦_⟧var : ∀ {Γ τ} → Γ ∋ τ → ⟦ Γ ⟧ctxt ⇒ ⟦ τ ⟧ty (λ ())
⟦ zero ⟧var   = p₂
⟦ succ x ⟧var = ⟦ x ⟧var ∘ p₁

open import Data.List.Relation.Unary.All using ([]; _∷_) renaming (All to Every)
open PointedFPCat PFPC[ Fam⟨𝒞⟩μ.cat , Fam⟨𝒞⟩μ.terminal T , Fam⟨𝒞⟩μ.products , Bool ] using (list→product)

mutual
  ⟦_⟧tm : ∀ {Γ τ} → Γ ⊢ τ → ⟦ Γ ⟧ctxt ⇒ ⟦ τ ⟧ty (λ ())
  ⟦ var x ⟧tm           = ⟦ x ⟧var
  ⟦ unit ⟧tm            = unit-pt ∘ to-terminal
  ⟦ inl M ⟧tm           = in₁ ∘ injF ∘ ⟦ M ⟧tm
  ⟦ inr M ⟧tm           = in₂ ∘ injF ∘ ⟦ M ⟧tm
  ⟦ case {τ = τ} M M₁ M₂ ⟧tm =
    scopair (elimF (ctrl-dep τ) ⟦ M₁ ⟧tm) (elimF (ctrl-dep τ) ⟦ M₂ ⟧tm)
      ∘ ⟨ id _ , ⟦ M ⟧tm ⟩
  ⟦ pair M N ⟧tm        = injF ∘ ⟨ ⟦ M ⟧tm , ⟦ N ⟧tm ⟩
  ⟦ fst {τ₁ = τ₁} M ⟧tm = elimF (ctrl-dep τ₁) (p₁ ∘ p₂) ∘ ⟨ id _ , ⟦ M ⟧tm ⟩
  ⟦ snd {τ₂ = τ₂} M ⟧tm = elimF (ctrl-dep τ₂) (p₂ ∘ p₂) ∘ ⟨ id _ , ⟦ M ⟧tm ⟩
  ⟦ lam M ⟧tm           = injF ∘ lambda ⟦ M ⟧tm
  ⟦ app {τ = τ} M N ⟧tm =
    elimF (ctrl-dep τ) (eval ∘ ⟨ p₂ , ⟦ N ⟧tm ∘ p₁ ⟩) ∘ ⟨ id _ , ⟦ M ⟧tm ⟩
  ⟦ bop ω Ms ⟧tm        = ⟦op⟧ ω ∘ ⟦ Ms ⟧tms
  ⟦ brel r Ms ⟧tm       = ⟦rel⟧ r ∘ ⟦ Ms ⟧tms
  ⟦ roll {τ = τ} M ⟧tm  = roll-mor τ ∘ ⟦ M ⟧tm
  ⟦ fold {τ = τ} {σ = σ} alg M ⟧tm =
    ⦅ ⟦ alg ⟧tm ∘ prod-m (id _) (sub-as-apply-bwd τ σ) ⦆ ∘ ⟨ id _ , ⟦ M ⟧tm ⟩

  ⟦_⟧tms : ∀ {Γ σs} → Every (λ σ → Γ ⊢ base σ) σs → ⟦ Γ ⟧ctxt ⇒ list→product ⟦sort⟧ σs
  ⟦ [] ⟧tms     = to-terminal
  ⟦ M ∷ Ms ⟧tms = ⟨ ⟦ M ⟧tm , ⟦ Ms ⟧tms ⟩
