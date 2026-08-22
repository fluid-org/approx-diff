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
  {o m e} (os es : Level) {𝒞 : Category o m e}
  (T : HasTerminal 𝒞) (CM : CMonEnriched 𝒞) (BP : ∀ x y → Biproduct CM x y)
  (𝟙c : Category.obj 𝒞)
  (let module R = fam-mu-lifting os es CM BP 𝟙c)
  (𝒞E : HasExponentials R.cat R.products)
  (δ∅ : Fin 0 → R.Obj)
  (𝟙ty : R.Obj)
  (unit-pt : R.Mor (HasTerminal.witness (R.terminal T)) 𝟙ty)
  (let Bool = HasCoproducts.coprod R.coproducts (R.Lf 𝟙ty) (R.Lf 𝟙ty))
  (Int : Model PFPC[ R.cat , R.terminal T , R.products , Bool ] Sig)
  (ctrl-w : Category._⇒_ 𝒞 𝟙c 𝟙c)
  (exp-section : ∀ {X Y : R.Obj} → R.Section (HasExponentials.exp 𝒞E X Y))
  (𝟙ty-section : R.Section 𝟙ty)
  (sort-section : ∀ s → R.Section (Model.⟦sort⟧ Int s))
  where

open R using (Obj; Lf; Lf-map; Lf-map-cong; Lf-map-id; Lf-map-comp; injF; injF-natural;
              strong-Lf-map; strong-Lf-map-cong; strong-Lf-map-comp; strong-Lf-map-p₂;
              strong-Lf-map-pre; strong-Lf-map-post; strong-Lf-map-injF;
              extend; extend-mor; fobj; HasMu; hasMu; HasMuLaws; hasMuLaws; _∘co_;
              Section; elimF; scale-section; Lf-section; coprod-section; prod-section; PolySection;
              poly-section; extend-section; preserves-section; preserves-section-id;
              preserves-section-∘; preserves-section-resp; preserves-section-inv;
              preserves-coprod-m; preserves-prod-m; preserves-Lf-map; preserves-scale;
              preserves-inMap; preserves-outMor)
open R.WithTerminal T
  using (fmor; μ-map;
         fmor-cong; fmor-id; fmor-comp; fmor-const; fmor-var; fmor-+; fmor-×; fmor-μ;
         μ-map-cong; μ-map-id; μ-map-in; μ-map-comp; strong-fmor-weaken; μ-map-weaken; preserves-μ-map)
open Category R.cat
open HasTerminal (R.terminal T) renaming (witness to 𝟙)
open HasProducts R.products renaming (pair to ⟨_,_⟩)

open HasCoproducts R.coproducts using (coprod; coprod-m; coprod-m-cong; coprod-m-comp; coprod-m-id; in₁; in₂;
                                       copair-cong; copair-in₁; copair-in₂; copair-ext)
open HasStrongCoproducts R.strongCoproducts
  using () renaming (copair to scopair; copair-cong to scopair-cong;
                     copair-in₁ to scopair-in₁; copair-in₂ to scopair-in₂;
                     copair-ext to scopair-ext; copair-ext0 to scopair-ext0)
open HasExponentials 𝒞E using (lambda; eval) renaming (exp to _⟦→⟧_)
open language-syntax Sig
import language-operational.type-substitution
open language-operational.type-substitution Sig using (unfold₁-sub; unfold₁; ren-ren; sub-ren-comm)
open HasMu hasMu
open HasMuLaws hasMuLaws
  using (⦅⦆-cong; ⦅⦆-β; ⦅⦆-reflect; fusion; ∘co-push; copair-comp;
         strong-fmor-comp; strong-fmor-cong; strong-fmor-p₂; strong-extend-mor-comp)

private
  module CoK {Γ' : Obj} = Category (coKleisli-prod R.products Γ')
open Model Int

open import language-type-interpretation Sig os es T CM BP 𝟙c 𝒞E δ∅ 𝟙ty unit-pt Int ctrl-w
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

preserves-subst-bwd : ∀ {Δ Δ'} (σ : TySub Δ Δ') (τ : type Δ) {δ : Fin Δ' → obj}
  (δc : ∀ i → Section (δ i)) →
  preserves-section (subst-bwd σ τ δ)
    (unit-section τ (λ i → ⟦ σ i ⟧ty δ) (λ i → unit-section (σ i) δ δc))
    (unit-section (sub σ τ) δ δc)
preserves-subst-bwd σ τ {δ} δc =
  preserves-section-inv (subst-fwd-bwd σ τ δ) (subst-bwd-fwd σ τ δ) (preserves-subst-fwd σ τ δc)

-- The single substitution push τ', read pointwise as an environment.
push-pw : ∀ (τ' : type 0) (i : Fin 1) → ⟦ push τ' i ⟧ty (λ ()) ≡ concat (extend {0} δ∅ (⟦ τ' ⟧ty (λ ()))) (λ ()) i
push-pw τ' Fin.zero = refl

preserves-push-pw : ∀ (τ' : type 0) (i : Fin 1) →
  preserves-section (≡-to-⇒ (push-pw τ' i))
    (unit-section (push τ' i) (λ ()) (λ ()))
    (concat-section {n = 1} (extend-section (λ ()) (unit-section τ' (λ ()) (λ ()))) (λ ()) i)
preserves-push-pw τ' Fin.zero = preserves-section-id (unit-section τ' (λ ()) (λ ()))

preserves-push-pw⁻ : ∀ (τ' : type 0) (i : Fin 1) →
  preserves-section (≡-to-⇒ (sym (push-pw τ' i)))
    (concat-section {n = 1} (extend-section (λ ()) (unit-section τ' (λ ()) (λ ()))) (λ ()) i)
    (unit-section (push τ' i) (λ ()) (λ ()))
preserves-push-pw⁻ τ' Fin.zero = preserves-section-id (unit-section τ' (λ ()) (λ ()))

private
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
    ≈-trans (CoK.∘-cong ≈-refl (CoK.∘-cong ≈-refl (≈-sym (scopair-weaken (Lf-map fσ) (Lf-map fτ)))))
    (≈-trans (CoK.∘-cong ≈-refl (copair-comp _ _ _ _))
    (≈-trans (copair-comp _ _ _ _)
    (≈-trans (scopair-cong (∘-cong ≈-refl comp₁) (∘-cong ≈-refl comp₂))
             (≈-sym rhs-eq))))
    where
    fσ  = apply-fwd σ δ δ₀
    fτ  = apply-fwd τ₂ δ δ₀
    fσ' = apply-fwd σ δ' δ₀'
    fτ' = apply-fwd τ₂ δ' δ₀'
    comp₁ = ≈-trans (CoK.∘-cong ≈-refl (≈-trans (CoK.∘-cong ≈-refl (≈-sym (sL-weaken fσ)))
                                                (strong-Lf-map-comp _ _)))
            (≈-trans (strong-Lf-map-comp _ _)
            (≈-trans (strong-Lf-map-cong (strong-apply-fwd-natural σ ks hs))
            (≈-trans (strong-Lf-map-cong (lift-post fσ' _))
                     (≈-sym (strong-Lf-map-post fσ' _)))))
    comp₂ = ≈-trans (CoK.∘-cong ≈-refl (≈-trans (CoK.∘-cong ≈-refl (≈-sym (sL-weaken fτ)))
                                                (strong-Lf-map-comp _ _)))
            (≈-trans (strong-Lf-map-comp _ _)
            (≈-trans (strong-Lf-map-cong (strong-apply-fwd-natural τ₂ ks hs))
            (≈-trans (strong-Lf-map-cong (lift-post fτ' _))
                     (≈-sym (strong-Lf-map-post fτ' _)))))
    rhs-eq =
      ≈-trans (lift-post (coprod-m (Lf-map fσ') (Lf-map fτ')) _)
      (≈-trans (scopair-post (coprod-m (Lf-map fσ') (Lf-map fτ')) _ _)
               (scopair-cong (≈-trans (≈-sym (assoc _ _ _)) (≈-trans (∘-cong (copair-in₁ _ _) ≈-refl) (assoc _ _ _)))
                             (≈-trans (≈-sym (assoc _ _ _)) (≈-trans (∘-cong (copair-in₂ _ _) ≈-refl) (assoc _ _ _)))))
  strong-apply-fwd-natural {Δ} {n} (σ [×] τ₂) {Γ'} {δ} {δ'} ks {δ₀} {δ₀'} hs =
    ≈-trans (CoK.∘-cong ≈-refl (≈-trans (CoK.∘-cong ≈-refl (≈-sym (sL-weaken (prod-m fσ fτ))))
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
    inner = ≈-trans (CoK.∘-cong ≈-refl (≈-trans (CoK.∘-cong ≈-refl (≈-sym (prod-m-weaken fσ fτ)))
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
      ≈-trans (CoK.∘-cong ≈-refl (≈-trans (strong-as-poly-map-cong {n + Δ} {1} τ₂ (λ i → strong-concat-mor-p₂ {δ₀ = δ₀} {δ = δ} i) (extend δ∅ C))
                                          (strong-as-poly-map-p₂ {n + Δ} {1} τ₂ (extend δ∅ C))))
              CoK.id-right

    premL2 : (SAMμ ∘co algPA) ≈ (algM ∘co strong-fmor P (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) SAMμ))
    premL2 = begin
        SAMμ ∘co ((inMap A δ₀ ∘ bodyMA) ∘ p₂)
      ≈⟨ CoK.∘-cong ≈-refl (assoc _ _ _) ⟩
        SAMμ ∘co (inMap A δ₀ ∘ (bodyMA ∘ p₂))
      ≈˘⟨ ∘co-push SAMμ (inMap A δ₀) (bodyMA ∘ p₂) ⟩
        (SAMμ ∘co (inMap A δ₀ ∘ p₂)) ∘co (bodyMA ∘ p₂)
      ≈⟨ CoK.∘-cong (⦅⦆-β {P = A} {δ = δ₀} (inMap A' δ₀ ∘ SAM-A-X)) ≈-refl ⟩
        ((inMap A' δ₀ ∘ SAM-A-X) ∘co strong-fmor A (strong-extend-mor {δ = δ₀} {δ' = δ₀} (λ i → p₂) SAMμ)) ∘co (bodyMA ∘ p₂)
      ≈⟨ CoK.assoc _ _ _ ⟩
        (inMap A' δ₀ ∘ SAM-A-X) ∘co (strong-fmor A (strong-extend-mor {δ = δ₀} {δ' = δ₀} (λ i → p₂) SAMμ) ∘co (bodyMA ∘ p₂))
      ≈˘⟨ CoK.∘-cong ≈-refl (CoK.∘-cong ≈-refl (≈-trans (CoK.∘-cong (strong-as-poly-map-p₂ {n = suc n} τ₂ {δ = δ} (extend δ₀ (μ-obj A δ₀))) ≈-refl) CoK.id-left)) ⟩
        (inMap A' δ₀ ∘ SAM-A-X) ∘co (strong-fmor A (strong-extend-mor {δ = δ₀} {δ' = δ₀} (λ i → p₂) SAMμ)
          ∘co (strong-as-poly-map {Δ} {suc n} τ₂ {δ = δ} {δ' = δ} (λ i → p₂) (extend δ₀ (μ-obj A δ₀)) ∘co (bodyMA ∘ p₂)))
      ≈⟨ CoK.∘-cong ≈-refl (strong-apply-fwd-body-natural τ₂ {δ = δ} {δ' = δ} (λ i → p₂) {δ₀ = δ₀} {δ₀' = δ₀} (λ i → p₂) SAMμ) ⟩
        (inMap A' δ₀ ∘ SAM-A-X) ∘co ((body' ∘ p₂)
          ∘co (strong-fmor P (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) SAMμ)
               ∘co strong-as-poly-map {n + Δ} {1} τ₂ (strong-concat-mor {δ₀ = δ₀} {δ₀' = δ₀} {δ = δ} {δ' = δ} (λ i → p₂) (λ i → p₂)) (extend δ∅ (μ-obj A δ₀))))
      ≈⟨ CoK.∘-cong ≈-refl (CoK.∘-cong ≈-refl (collapse-Pʳ (strong-fmor P (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) SAMμ)))) ⟩
        (inMap A' δ₀ ∘ SAM-A-X) ∘co ((body' ∘ p₂) ∘co strong-fmor P (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) SAMμ))
      ≈˘⟨ CoK.assoc _ _ _ ⟩
        ((inMap A' δ₀ ∘ SAM-A-X) ∘co (body' ∘ p₂)) ∘co strong-fmor P (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) SAMμ)
      ∎
      where open ≈-Reasoning isEquiv

    premL3 : (SFμ ∘co algM) ≈ (alg⋆ ∘co strong-fmor P (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) SFμ))
    premL3 = begin
        SFμ ∘co ((inMap A' δ₀ ∘ SAM-A-X) ∘co (body' ∘ p₂))
      ≈˘⟨ CoK.assoc _ _ _ ⟩
        (SFμ ∘co (inMap A' δ₀ ∘ SAM-A-X)) ∘co (body' ∘ p₂)
      ≈˘⟨ CoK.∘-cong (∘co-push SFμ (inMap A' δ₀) SAM-A-X) ≈-refl ⟩
        ((SFμ ∘co (inMap A' δ₀ ∘ p₂)) ∘co SAM-A-X) ∘co (body' ∘ p₂)
      ≈⟨ CoK.∘-cong (CoK.∘-cong (⦅⦆-β {P = A'} {δ = δ₀} (inMap A' δ₀' ∘ SF-A'-ext)) ≈-refl) ≈-refl ⟩
        (((inMap A' δ₀' ∘ SF-A'-ext) ∘co strong-fmor A' (strong-extend-mor {δ = δ₀} {δ' = δ₀} (λ i → p₂) SFμ)) ∘co SAM-A-X) ∘co (body' ∘ p₂)
      ≈⟨ CoK.∘-cong (CoK.assoc _ _ _) ≈-refl ⟩
        ((inMap A' δ₀' ∘ SF-A'-ext) ∘co (strong-fmor A' (strong-extend-mor {δ = δ₀} {δ' = δ₀} (λ i → p₂) SFμ) ∘co SAM-A-X)) ∘co (body' ∘ p₂)
      ≈⟨ CoK.∘-cong (CoK.∘-cong ≈-refl (strong-as-poly-map-natural {n = suc n} τ₂ ks (strong-extend-mor {δ = δ₀} {δ' = δ₀} (λ i → p₂) SFμ))) ≈-refl ⟩
        ((inMap A' δ₀' ∘ SF-A'-ext) ∘co (SAM-A-Mf ∘co strong-fmor A (strong-extend-mor {δ = δ₀} {δ' = δ₀} (λ i → p₂) SFμ))) ∘co (body' ∘ p₂)
      ≈⟨ CoK.assoc _ _ _ ⟩
        (inMap A' δ₀' ∘ SF-A'-ext) ∘co ((SAM-A-Mf ∘co strong-fmor A (strong-extend-mor {δ = δ₀} {δ' = δ₀} (λ i → p₂) SFμ)) ∘co (body' ∘ p₂))
      ≈⟨ CoK.∘-cong ≈-refl (CoK.assoc _ _ _) ⟩
        (inMap A' δ₀' ∘ SF-A'-ext) ∘co (SAM-A-Mf ∘co (strong-fmor A (strong-extend-mor {δ = δ₀} {δ' = δ₀} (λ i → p₂) SFμ) ∘co (body' ∘ p₂)))
      ≈˘⟨ CoK.∘-cong ≈-refl (CoK.∘-cong ≈-refl (CoK.∘-cong ≈-refl (≈-trans (CoK.∘-cong (strong-as-poly-map-p₂ {n = suc n} τ₂ {δ = δ} (extend δ₀ MA')) ≈-refl) CoK.id-left))) ⟩
        (inMap A' δ₀' ∘ SF-A'-ext) ∘co (SAM-A-Mf ∘co (strong-fmor A (strong-extend-mor {δ = δ₀} {δ' = δ₀} (λ i → p₂) SFμ)
          ∘co (strong-as-poly-map {Δ} {suc n} τ₂ {δ = δ} {δ' = δ} (λ i → p₂) (extend δ₀ MA') ∘co (body' ∘ p₂))))
      ≈⟨ CoK.∘-cong ≈-refl (CoK.∘-cong ≈-refl (strong-apply-fwd-body-natural τ₂ {δ = δ} {δ' = δ} (λ i → p₂) {δ₀ = δ₀} {δ₀' = δ₀} (λ i → p₂) SFμ)) ⟩
        (inMap A' δ₀' ∘ SF-A'-ext) ∘co (SAM-A-Mf ∘co ((body'' ∘ p₂)
          ∘co (strong-fmor P (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) SFμ)
               ∘co strong-as-poly-map {n + Δ} {1} τ₂ (strong-concat-mor {δ₀ = δ₀} {δ₀' = δ₀} {δ = δ} {δ' = δ} (λ i → p₂) (λ i → p₂)) (extend δ∅ MA'))))
      ≈⟨ CoK.∘-cong ≈-refl (CoK.∘-cong ≈-refl (CoK.∘-cong ≈-refl (collapse-Pʳ (strong-fmor P (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) SFμ))))) ⟩
        (inMap A' δ₀' ∘ SF-A'-ext) ∘co (SAM-A-Mf ∘co ((body'' ∘ p₂) ∘co strong-fmor P (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) SFμ)))
      ≈˘⟨ CoK.∘-cong ≈-refl (CoK.assoc _ _ _) ⟩
        (inMap A' δ₀' ∘ SF-A'-ext) ∘co ((SAM-A-Mf ∘co (body'' ∘ p₂)) ∘co strong-fmor P (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) SFμ))
      ≈˘⟨ CoK.assoc _ _ _ ⟩
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
      ≈⟨ ∘-cong ≈-refl (CoK.∘-cong ≈-refl (≈-trans (CoK.∘-cong (≈-trans (strong-fmor-cong P'' eqP) (strong-fmor-p₂ P'')) ≈-refl) CoK.id-left)) ⟩
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
      ≈⟨ CoK.∘-cong (⦅⦆-β {P = P''} {δ = δ∅} ((inMap A' δ₀' ∘ bodyf) ∘ p₂)) ≈-refl ⟩
        ((((inMap A' δ₀' ∘ bodyf) ∘ p₂) ∘co strong-fmor P'' (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) cataB)) ∘co SAM-P-MP)
      ≈⟨ CoK.assoc _ _ _ ⟩
        (((inMap A' δ₀' ∘ bodyf) ∘ p₂) ∘co (strong-fmor P'' (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) cataB) ∘co SAM-P-MP))
      ≈⟨ CoK.∘-cong ≈-refl (strong-as-poly-map-natural {n = 1} τ₂ (strong-concat-mor hs ks) (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) cataB)) ⟩
        (((inMap A' δ₀' ∘ bodyf) ∘ p₂) ∘co (SAM-P-Mf ∘co strong-fmor P (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) cataB)))
      ≈˘⟨ CoK.assoc _ _ _ ⟩
        ((((inMap A' δ₀' ∘ bodyf) ∘ p₂) ∘co SAM-P-Mf) ∘co strong-fmor P (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) cataB))
      ≈⟨ CoK.∘-cong alg-eq ≈-refl ⟩
        alg⋆ ∘co strong-fmor P (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) cataB)
      ∎
      where open ≈-Reasoning isEquiv


    main : (SFμ ∘co (SAMμ ∘co (μm ∘ p₂))) ≈ ((μm'' ∘ p₂) ∘co SAMμP)
    main = begin
        SFμ ∘co (SAMμ ∘co (μm ∘ p₂))
      ≈˘⟨ CoK.∘-cong ≈-refl (CoK.∘-cong ≈-refl (μ-map-weaken P δ∅ A δ₀ bodyMA)) ⟩
        SFμ ∘co (SAMμ ∘co ⦅_⦆ {P = P} {δ = δ∅} algPA)
      ≈⟨ CoK.∘-cong ≈-refl (fusion {P = P} {δ = δ∅} algPA algM SAMμ premL2) ⟩
        SFμ ∘co ⦅_⦆ {P = P} {δ = δ∅} algM
      ≈⟨ fusion {P = P} {δ = δ∅} algM alg⋆ SFμ premL3 ⟩
        ⦅_⦆ {P = P} {δ = δ∅} alg⋆
      ≈˘⟨ fusion {P = P} {δ = δ∅} algP alg⋆ cataB premR ⟩
        cataB ∘co SAMμP
      ≈⟨ CoK.∘-cong (μ-map-weaken P'' δ∅ A' δ₀' bodyf) ≈-refl ⟩
        (μm'' ∘ p₂) ∘co SAMμP
      ∎
      where open ≈-Reasoning isEquiv

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
      ≈-trans (CoK.∘-cong ≈-refl (≈-sym (strong-as-poly-map-weaken τ (λ i → ≡-to-⇒ (env-pw δ δ₀ X i)) δ∅)))
      (≈-trans (strong-as-poly-map-comp τ (strong-concat-mor (strong-extend-mor hs kc) ks)
                                          (λ i → ≡-to-⇒ (env-pw δ δ₀ X i) ∘ p₂) δ∅)
      (≈-trans (strong-as-poly-map-cong τ (λ i → strong-env-pw-natural ks hs kc i) δ∅)
      (≈-trans (≈-sym (strong-as-poly-map-comp τ (λ i → ≡-to-⇒ (env-pw δ' δ₀' X' i) ∘ p₂) F₁ δ∅))
               (CoK.∘-cong (strong-as-poly-map-weaken τ (λ i → ≡-to-⇒ (env-pw δ' δ₀' X' i)) δ∅) ≈-refl))))
    ab-step : (SAM-1 ∘co (ab ∘ p₂)) ≈ ((ab' ∘ p₂) ∘co (SF-P' ∘co SAM-P))
    ab-step = begin
        SAM-1 ∘co (ab ∘ p₂)
      ≈˘⟨ CoK.id-left ⟩
        p₂ ∘co (SAM-1 ∘co (ab ∘ p₂))
      ≈˘⟨ CoK.∘-cong iso-fact ≈-refl ⟩
        ((ab' ∘ p₂) ∘co (af₁' ∘ p₂)) ∘co (SAM-1 ∘co (ab ∘ p₂))
      ≈⟨ CoK.assoc _ _ _ ⟩
        (ab' ∘ p₂) ∘co ((af₁' ∘ p₂) ∘co (SAM-1 ∘co (ab ∘ p₂)))
      ≈˘⟨ CoK.∘-cong ≈-refl (CoK.assoc _ _ _) ⟩
        (ab' ∘ p₂) ∘co (((af₁' ∘ p₂) ∘co SAM-1) ∘co (ab ∘ p₂))
      ≈˘⟨ CoK.∘-cong ≈-refl (CoK.∘-cong (strong-apply-fwd-natural {n = 1} τ (strong-concat-mor hs ks) (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ j → p₂) kc)) ≈-refl) ⟩
        (ab' ∘ p₂) ∘co ((SF-P' ∘co (SAM-P ∘co (af₁ ∘ p₂))) ∘co (ab ∘ p₂))
      ≈⟨ CoK.∘-cong ≈-refl (CoK.assoc _ _ _) ⟩
        (ab' ∘ p₂) ∘co (SF-P' ∘co ((SAM-P ∘co (af₁ ∘ p₂)) ∘co (ab ∘ p₂)))
      ≈⟨ CoK.∘-cong ≈-refl (CoK.∘-cong ≈-refl (CoK.assoc _ _ _)) ⟩
        (ab' ∘ p₂) ∘co (SF-P' ∘co (SAM-P ∘co ((af₁ ∘ p₂) ∘co (ab ∘ p₂))))
      ≈⟨ CoK.∘-cong ≈-refl (CoK.∘-cong ≈-refl (CoK.∘-cong ≈-refl fwd-bwd-fact)) ⟩
        (ab' ∘ p₂) ∘co (SF-P' ∘co (SAM-P ∘co p₂))
      ≈⟨ CoK.∘-cong ≈-refl (CoK.∘-cong ≈-refl CoK.id-right) ⟩
        (ab' ∘ p₂) ∘co (SF-P' ∘co SAM-P)
      ∎
      where
      open ≈-Reasoning isEquiv
      iso-fact : ((ab' ∘ p₂) ∘co (af₁' ∘ p₂)) ≈ p₂
      iso-fact = ≈-trans (≈-sym (lift-comp ab' af₁'))
                 (≈-trans (∘-cong (apply-bwd-fwd {n = 1} τ (concat δ₀' δ') (extend δ∅ X')) ≈-refl) id-left)
      fwd-bwd-fact : ((af₁ ∘ p₂) ∘co (ab ∘ p₂)) ≈ p₂
      fwd-bwd-fact = ≈-trans (≈-sym (lift-comp af₁ ab))
                     (≈-trans (∘-cong (apply-fwd-bwd {n = 1} τ (concat δ₀ δ) (extend δ∅ X)) ≈-refl) id-left)


    main : (SF ∘co (SAM-X ∘co (((af ∘ Rs) ∘ ab) ∘ p₂)))
           ≈ ((((af' ∘ Rs') ∘ ab') ∘ p₂) ∘co (SF-P' ∘co SAM-P))
    main = begin
        SF ∘co (SAM-X ∘co (((af ∘ Rs) ∘ ab) ∘ p₂))
      ≈⟨ CoK.∘-cong ≈-refl (CoK.∘-cong ≈-refl (≈-trans (lift-comp (af ∘ Rs) ab) (CoK.∘-cong (lift-comp af Rs) ≈-refl))) ⟩
        SF ∘co (SAM-X ∘co (((af ∘ p₂) ∘co (Rs ∘ p₂)) ∘co (ab ∘ p₂)))
      ≈⟨ CoK.∘-cong ≈-refl (CoK.∘-cong ≈-refl (CoK.assoc _ _ _)) ⟩
        SF ∘co (SAM-X ∘co ((af ∘ p₂) ∘co ((Rs ∘ p₂) ∘co (ab ∘ p₂))))
      ≈˘⟨ CoK.∘-cong ≈-refl (CoK.assoc _ _ _) ⟩
        SF ∘co ((SAM-X ∘co (af ∘ p₂)) ∘co ((Rs ∘ p₂) ∘co (ab ∘ p₂)))
      ≈˘⟨ CoK.assoc _ _ _ ⟩
        (SF ∘co (SAM-X ∘co (af ∘ p₂))) ∘co ((Rs ∘ p₂) ∘co (ab ∘ p₂))
      ≈⟨ CoK.∘-cong (strong-apply-fwd-natural {n = suc n} τ ks (strong-extend-mor hs kc)) ≈-refl ⟩
        ((af' ∘ p₂) ∘co SAM-full) ∘co ((Rs ∘ p₂) ∘co (ab ∘ p₂))
      ≈⟨ CoK.assoc _ _ _ ⟩
        (af' ∘ p₂) ∘co (SAM-full ∘co ((Rs ∘ p₂) ∘co (ab ∘ p₂)))
      ≈˘⟨ CoK.∘-cong ≈-refl (CoK.assoc _ _ _) ⟩
        (af' ∘ p₂) ∘co ((SAM-full ∘co (Rs ∘ p₂)) ∘co (ab ∘ p₂))
      ≈⟨ CoK.∘-cong ≈-refl (CoK.∘-cong cast-step ≈-refl) ⟩
        (af' ∘ p₂) ∘co (((Rs' ∘ p₂) ∘co SAM-1) ∘co (ab ∘ p₂))
      ≈⟨ CoK.∘-cong ≈-refl (CoK.assoc _ _ _) ⟩
        (af' ∘ p₂) ∘co ((Rs' ∘ p₂) ∘co (SAM-1 ∘co (ab ∘ p₂)))
      ≈⟨ CoK.∘-cong ≈-refl (CoK.∘-cong ≈-refl ab-step) ⟩
        (af' ∘ p₂) ∘co ((Rs' ∘ p₂) ∘co ((ab' ∘ p₂) ∘co (SF-P' ∘co SAM-P)))
      ≈˘⟨ CoK.∘-cong ≈-refl (CoK.assoc _ _ _) ⟩
        (af' ∘ p₂) ∘co (((Rs' ∘ p₂) ∘co (ab' ∘ p₂)) ∘co (SF-P' ∘co SAM-P))
      ≈˘⟨ CoK.assoc _ _ _ ⟩
        ((af' ∘ p₂) ∘co ((Rs' ∘ p₂) ∘co (ab' ∘ p₂))) ∘co (SF-P' ∘co SAM-P)
      ≈˘⟨ CoK.∘-cong (CoK.∘-cong ≈-refl (lift-comp Rs' ab')) ≈-refl ⟩
        ((af' ∘ p₂) ∘co ((Rs' ∘ ab') ∘ p₂)) ∘co (SF-P' ∘co SAM-P)
      ≈˘⟨ CoK.∘-cong (lift-comp af' (Rs' ∘ ab')) ≈-refl ⟩
        ((af' ∘ (Rs' ∘ ab')) ∘ p₂) ∘co (SF-P' ∘co SAM-P)
      ≈˘⟨ CoK.∘-cong (∘-cong (assoc _ _ _) ≈-refl) ≈-refl ⟩
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
    ≈-trans (CoK.∘-cong ≈-refl (≈-sym (scopair-weaken (Lf-map f₁) (Lf-map f₂))))
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
    leg₁ = ≈-trans (CoK.∘-cong ≈-refl (≈-sym (sL-weaken f₁)))
           (≈-trans (strong-Lf-map-comp _ _)
           (≈-trans (strong-Lf-map-cong (strong-subst-fwd-natural σ τ₁ gs))
           (≈-trans (≈-sym (strong-Lf-map-comp _ _))
                    (CoK.∘-cong (sL-weaken f₁') ≈-refl))))
    leg₂ : (strong-Lf-map M₂ ∘co (Lf-map f₂ ∘ p₂)) ≈ ((Lf-map f₂' ∘ p₂) ∘co strong-Lf-map N₂)
    leg₂ = ≈-trans (CoK.∘-cong ≈-refl (≈-sym (sL-weaken f₂)))
           (≈-trans (strong-Lf-map-comp _ _)
           (≈-trans (strong-Lf-map-cong (strong-subst-fwd-natural σ τ₂ gs))
           (≈-trans (≈-sym (strong-Lf-map-comp _ _))
                    (CoK.∘-cong (sL-weaken f₂') ≈-refl))))
    rhs-eq : (([+]-map f₁' f₂' ∘ p₂) ∘co scopair (in₁ ∘ strong-Lf-map N₁) (in₂ ∘ strong-Lf-map N₂))
               ≈ scopair (in₁ ∘ ((Lf-map f₁' ∘ p₂) ∘co strong-Lf-map N₁)) (in₂ ∘ ((Lf-map f₂' ∘ p₂) ∘co strong-Lf-map N₂))
    rhs-eq = ≈-trans (CoK.∘-cong (≈-sym (scopair-weaken (Lf-map f₁') (Lf-map f₂'))) ≈-refl)
                     (copair-comp _ _ _ _)
  strong-subst-fwd-natural {Δ} {Δ'} σ (τ₁ [×] τ₂) {Γ'} {δ} {δ'} gs =
    ≈-trans (CoK.∘-cong ≈-refl (≈-sym (sL-weaken (prod-m f₁ f₂))))
    (≈-trans (strong-Lf-map-comp _ _)
    (≈-trans (strong-Lf-map-cong inner)
    (≈-trans (≈-sym (strong-Lf-map-comp _ _))
             (CoK.∘-cong (sL-weaken (prod-m f₁' f₂')) ≈-refl))))
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
    inner = ≈-trans (CoK.∘-cong ≈-refl (≈-sym (prod-m-weaken f₁ f₂)))
            (≈-trans (strong-prod-m-comp _ _ _ _)
            (≈-trans (strong-prod-m-cong (strong-subst-fwd-natural σ τ₁ gs) (strong-subst-fwd-natural σ τ₂ gs))
            (≈-trans (≈-sym (strong-prod-m-comp _ _ _ _))
                     (CoK.∘-cong (prod-m-weaken f₁' f₂') ≈-refl))))
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
      ≈⟨ CoK.∘-cong ≈-refl (assoc _ _ _) ⟩
        SAMμ ∘co (inMap A δ∅ ∘ (body ∘ p₂))
      ≈˘⟨ ∘co-push SAMμ (inMap A δ∅) (body ∘ p₂) ⟩
        (SAMμ ∘co (inMap A δ∅ ∘ p₂)) ∘co (body ∘ p₂)
      ≈⟨ CoK.∘-cong (⦅⦆-β {P = A} {δ = δ∅} (inMap A' δ∅ ∘ SAM-A)) ≈-refl ⟩
        ((inMap A' δ∅ ∘ SAM-A) ∘co strong-fmor A (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) SAMμ)) ∘co (body ∘ p₂)
      ≈⟨ CoK.assoc _ _ _ ⟩
        (inMap A' δ∅ ∘ SAM-A) ∘co (strong-fmor A (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) SAMμ) ∘co (body ∘ p₂))
      ≈˘⟨ CoK.∘-cong ≈-refl (CoK.∘-cong ≈-refl (≈-trans (CoK.∘-cong collapse-triv ≈-refl) CoK.id-left)) ⟩
        (inMap A' δ∅ ∘ SAM-A) ∘co (strong-fmor A (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) SAMμ)
          ∘co (SAM-triv ∘co (body ∘ p₂)))
      ≈⟨ CoK.∘-cong ≈-refl (strong-subst-fwd-body-natural σ τ {δ = δ} {δ' = δ} (λ i → p₂) SAMμ) ⟩
        (inMap A' δ∅ ∘ SAM-A) ∘co ((bodyM' ∘ p₂)
          ∘co (strong-fmor P (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) SAMμ) ∘co SAM-P-triv))
      ≈⟨ CoK.∘-cong ≈-refl (CoK.∘-cong ≈-refl (≈-trans (CoK.∘-cong ≈-refl (strong-as-poly-map-p₂ {Δ'} {1} (sub (sub-lift σ) τ) {δ = δ} (extend δ∅ M))) CoK.id-right)) ⟩
        (inMap A' δ∅ ∘ SAM-A) ∘co ((bodyM' ∘ p₂) ∘co strong-fmor P (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) SAMμ))
      ≈˘⟨ CoK.assoc _ _ _ ⟩
        ((inMap A' δ∅ ∘ SAM-A) ∘co (bodyM' ∘ p₂)) ∘co strong-fmor P (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) SAMμ)
      ∎
      where open ≈-Reasoning isEquiv

    alg-eq : (((inMap A' δ∅ ∘ body') ∘ p₂) ∘co SAM-P-M') ≈ alg⋆
    alg-eq = ≈-sym (begin
        (inMap A' δ∅ ∘ SAM-A) ∘co (bodyM' ∘ p₂)
      ≈⟨ assoc _ _ _ ⟩
        inMap A' δ∅ ∘ (SAM-A ∘co (bodyM' ∘ p₂))
      ≈˘⟨ ∘-cong ≈-refl (≈-trans (CoK.∘-cong (≈-trans (strong-fmor-cong A' eqP) (strong-fmor-p₂ A')) ≈-refl) CoK.id-left) ⟩
        inMap A' δ∅ ∘ (strong-fmor A' (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) (p₂ {Γ'} {M'}))
          ∘co (SAM-A ∘co (bodyM' ∘ p₂)))
      ≈⟨ ∘-cong ≈-refl (strong-subst-fwd-body-natural σ τ gs (p₂ {Γ'} {M'})) ⟩
        inMap A' δ∅ ∘ ((body' ∘ p₂)
          ∘co (strong-fmor P' (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) (p₂ {Γ'} {M'})) ∘co SAM-P-M'))
      ≈⟨ ∘-cong ≈-refl (CoK.∘-cong ≈-refl (≈-trans (CoK.∘-cong (≈-trans (strong-fmor-cong P' eqP) (strong-fmor-p₂ P')) ≈-refl) CoK.id-left)) ⟩
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
      ≈⟨ CoK.∘-cong (⦅⦆-β {P = P'} {δ = δ∅} ((inMap A' δ∅ ∘ body') ∘ p₂)) ≈-refl ⟩
        ((((inMap A' δ∅ ∘ body') ∘ p₂) ∘co strong-fmor P' (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) cataB)) ∘co SAM-P-N')
      ≈⟨ CoK.assoc _ _ _ ⟩
        (((inMap A' δ∅ ∘ body') ∘ p₂) ∘co (strong-fmor P' (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) cataB) ∘co SAM-P-N'))
      ≈⟨ CoK.∘-cong ≈-refl (strong-as-poly-map-natural {n = 1} (sub (sub-lift σ) τ) gs (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) cataB)) ⟩
        (((inMap A' δ∅ ∘ body') ∘ p₂) ∘co (SAM-P-M' ∘co strong-fmor P (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) cataB)))
      ≈˘⟨ CoK.assoc _ _ _ ⟩
        ((((inMap A' δ∅ ∘ body') ∘ p₂) ∘co SAM-P-M') ∘co strong-fmor P (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) cataB))
      ≈⟨ CoK.∘-cong alg-eq ≈-refl ⟩
        alg⋆ ∘co strong-fmor P (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ i → p₂) cataB)
      ∎
      where open ≈-Reasoning isEquiv

    main : (SAMμ ∘co (μ-map P δ∅ A δ∅ body ∘ p₂)) ≈ ((μ-map P' δ∅ A' δ∅ body' ∘ p₂) ∘co SAMμP)
    main = begin
        SAMμ ∘co (μ-map P δ∅ A δ∅ body ∘ p₂)
      ≈˘⟨ CoK.∘-cong ≈-refl (μ-map-weaken P δ∅ A δ∅ body) ⟩
        SAMμ ∘co ⦅_⦆ {P = P} {δ = δ∅} ((inMap A δ∅ ∘ body) ∘ p₂)
      ≈⟨ fusion {P = P} {δ = δ∅} ((inMap A δ∅ ∘ body) ∘ p₂) alg⋆ SAMμ premL ⟩
        ⦅_⦆ {P = P} {δ = δ∅} alg⋆
      ≈˘⟨ fusion {P = P} {δ = δ∅} (inMap P' δ∅ ∘ SAM-P-N') alg⋆ cataB premR ⟩
        cataB ∘co SAMμP
      ≈⟨ CoK.∘-cong (μ-map-weaken P' δ∅ A' δ∅ body') ≈-refl ⟩
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
      (≈-trans (CoK.∘-cong (lift-comp (af ∘ Rs) S) ≈-refl)
      (≈-trans (CoK.assoc _ _ _)
      (≈-trans (CoK.∘-cong (lift-comp af Rs) ≈-refl)
               (CoK.assoc _ _ _))))

    cast-step : (SAM-full ∘co (Rs ∘ p₂)) ≈ ((Rs' ∘ p₂) ∘co SAM-1)
    cast-step =
      ≈-trans (CoK.∘-cong ≈-refl (≈-sym (strong-as-poly-map-weaken τ (λ i → ≡-to-⇒ (sub-lift-pw σ δ X i)) δ∅)))
      (≈-trans (strong-as-poly-map-comp τ
                  (strong-concat-mor {n = 1} (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ j → p₂) kc)
                     (λ j → strong-as-poly-map (σ j) gs δ∅))
                  (λ i → ≡-to-⇒ (sub-lift-pw σ δ X i) ∘ p₂) δ∅)
      (≈-trans (strong-as-poly-map-cong τ (λ i → strong-sub-lift-pw-natural σ gs kc i) δ∅)
      (≈-trans (≈-sym (strong-as-poly-map-comp τ (λ i → ≡-to-⇒ (sub-lift-pw σ δ' X' i) ∘ p₂)
                        (λ j → strong-as-poly-map (sub-lift σ j) Kδ δ∅) δ∅))
               (CoK.∘-cong (strong-as-poly-map-weaken τ (λ i → ≡-to-⇒ (sub-lift-pw σ δ' X' i)) δ∅) ≈-refl))))

    ab-step : (SAM-sub ∘co (ab ∘ p₂)) ≈ ((ab' ∘ p₂) ∘co (SF-P' ∘co SAM-P))
    ab-step = begin
        SAM-sub ∘co (ab ∘ p₂)
      ≈˘⟨ CoK.id-left ⟩
        p₂ ∘co (SAM-sub ∘co (ab ∘ p₂))
      ≈˘⟨ CoK.∘-cong iso-fact ≈-refl ⟩
        ((ab' ∘ p₂) ∘co (af₁' ∘ p₂)) ∘co (SAM-sub ∘co (ab ∘ p₂))
      ≈⟨ CoK.assoc _ _ _ ⟩
        (ab' ∘ p₂) ∘co ((af₁' ∘ p₂) ∘co (SAM-sub ∘co (ab ∘ p₂)))
      ≈˘⟨ CoK.∘-cong ≈-refl (CoK.assoc _ _ _) ⟩
        (ab' ∘ p₂) ∘co (((af₁' ∘ p₂) ∘co SAM-sub) ∘co (ab ∘ p₂))
      ≈˘⟨ CoK.∘-cong ≈-refl (CoK.∘-cong (strong-apply-fwd-natural {n = 1} (sub (sub-lift σ) τ) gs (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ j → p₂) kc)) ≈-refl) ⟩
        (ab' ∘ p₂) ∘co ((SF-P' ∘co (SAM-P ∘co (af₁ ∘ p₂))) ∘co (ab ∘ p₂))
      ≈⟨ CoK.∘-cong ≈-refl (CoK.assoc _ _ _) ⟩
        (ab' ∘ p₂) ∘co (SF-P' ∘co ((SAM-P ∘co (af₁ ∘ p₂)) ∘co (ab ∘ p₂)))
      ≈⟨ CoK.∘-cong ≈-refl (CoK.∘-cong ≈-refl (CoK.assoc _ _ _)) ⟩
        (ab' ∘ p₂) ∘co (SF-P' ∘co (SAM-P ∘co ((af₁ ∘ p₂) ∘co (ab ∘ p₂))))
      ≈⟨ CoK.∘-cong ≈-refl (CoK.∘-cong ≈-refl (CoK.∘-cong ≈-refl fwd-bwd-fact)) ⟩
        (ab' ∘ p₂) ∘co (SF-P' ∘co (SAM-P ∘co p₂))
      ≈⟨ CoK.∘-cong ≈-refl (CoK.∘-cong ≈-refl CoK.id-right) ⟩
        (ab' ∘ p₂) ∘co (SF-P' ∘co SAM-P)
      ∎
      where
      open ≈-Reasoning isEquiv
      iso-fact : ((ab' ∘ p₂) ∘co (af₁' ∘ p₂)) ≈ p₂
      iso-fact = ≈-trans (≈-sym (lift-comp ab' af₁'))
                 (≈-trans (∘-cong (apply-bwd-fwd {n = 1} (sub (sub-lift σ) τ) δ' (extend δ∅ X')) ≈-refl) id-left)
      fwd-bwd-fact : ((af₁ ∘ p₂) ∘co (ab ∘ p₂)) ≈ p₂
      fwd-bwd-fact = ≈-trans (≈-sym (lift-comp af₁ ab))
                     (≈-trans (∘-cong (apply-fwd-bwd {n = 1} (sub (sub-lift σ) τ) δ (extend δ∅ X)) ≈-refl) id-left)

    main : (SF ∘co (SAM-X ∘co ((((af ∘ Rs) ∘ S) ∘ ab) ∘ p₂)))
             ≈ (((((af' ∘ Rs') ∘ S') ∘ ab') ∘ p₂) ∘co (SF-P' ∘co SAM-P))
    main = begin
        SF ∘co (SAM-X ∘co ((((af ∘ Rs) ∘ S) ∘ ab) ∘ p₂))
      ≈⟨ CoK.∘-cong ≈-refl (CoK.∘-cong ≈-refl split-step) ⟩
        SF ∘co (SAM-X ∘co ((af ∘ p₂) ∘co ((Rs ∘ p₂) ∘co ((S ∘ p₂) ∘co (ab ∘ p₂)))))
      ≈˘⟨ CoK.∘-cong ≈-refl (CoK.assoc _ _ _) ⟩
        SF ∘co ((SAM-X ∘co (af ∘ p₂)) ∘co ((Rs ∘ p₂) ∘co ((S ∘ p₂) ∘co (ab ∘ p₂))))
      ≈˘⟨ CoK.assoc _ _ _ ⟩
        (SF ∘co (SAM-X ∘co (af ∘ p₂))) ∘co ((Rs ∘ p₂) ∘co ((S ∘ p₂) ∘co (ab ∘ p₂)))
      ≈⟨ CoK.∘-cong (strong-apply-fwd-natural {n = 1} τ (λ j → strong-as-poly-map (σ j) gs δ∅) (strong-extend-mor {δ = δ∅} {δ' = δ∅} (λ j → p₂) kc)) ≈-refl ⟩
        ((af' ∘ p₂) ∘co SAM-full) ∘co ((Rs ∘ p₂) ∘co ((S ∘ p₂) ∘co (ab ∘ p₂)))
      ≈⟨ CoK.assoc _ _ _ ⟩
        (af' ∘ p₂) ∘co (SAM-full ∘co ((Rs ∘ p₂) ∘co ((S ∘ p₂) ∘co (ab ∘ p₂))))
      ≈˘⟨ CoK.∘-cong ≈-refl (CoK.assoc _ _ _) ⟩
        (af' ∘ p₂) ∘co ((SAM-full ∘co (Rs ∘ p₂)) ∘co ((S ∘ p₂) ∘co (ab ∘ p₂)))
      ≈⟨ CoK.∘-cong ≈-refl (CoK.∘-cong cast-step ≈-refl) ⟩
        (af' ∘ p₂) ∘co (((Rs' ∘ p₂) ∘co SAM-1) ∘co ((S ∘ p₂) ∘co (ab ∘ p₂)))
      ≈⟨ CoK.∘-cong ≈-refl (CoK.assoc _ _ _) ⟩
        (af' ∘ p₂) ∘co ((Rs' ∘ p₂) ∘co (SAM-1 ∘co ((S ∘ p₂) ∘co (ab ∘ p₂))))
      ≈˘⟨ CoK.∘-cong ≈-refl (CoK.∘-cong ≈-refl (CoK.assoc _ _ _)) ⟩
        (af' ∘ p₂) ∘co ((Rs' ∘ p₂) ∘co ((SAM-1 ∘co (S ∘ p₂)) ∘co (ab ∘ p₂)))
      ≈⟨ CoK.∘-cong ≈-refl (CoK.∘-cong ≈-refl (CoK.∘-cong (strong-subst-fwd-natural (sub-lift σ) τ Kδ) ≈-refl)) ⟩
        (af' ∘ p₂) ∘co ((Rs' ∘ p₂) ∘co (((S' ∘ p₂) ∘co SAM-sub) ∘co (ab ∘ p₂)))
      ≈⟨ CoK.∘-cong ≈-refl (CoK.∘-cong ≈-refl (CoK.assoc _ _ _)) ⟩
        (af' ∘ p₂) ∘co ((Rs' ∘ p₂) ∘co ((S' ∘ p₂) ∘co (SAM-sub ∘co (ab ∘ p₂))))
      ≈⟨ CoK.∘-cong ≈-refl (CoK.∘-cong ≈-refl (CoK.∘-cong ≈-refl ab-step)) ⟩
        (af' ∘ p₂) ∘co ((Rs' ∘ p₂) ∘co ((S' ∘ p₂) ∘co ((ab' ∘ p₂) ∘co (SF-P' ∘co SAM-P))))
      ≈˘⟨ CoK.∘-cong ≈-refl (CoK.∘-cong ≈-refl (CoK.assoc _ _ _)) ⟩
        (af' ∘ p₂) ∘co ((Rs' ∘ p₂) ∘co (((S' ∘ p₂) ∘co (ab' ∘ p₂)) ∘co (SF-P' ∘co SAM-P)))
      ≈˘⟨ CoK.∘-cong ≈-refl (CoK.∘-cong ≈-refl (CoK.∘-cong (lift-comp S' ab') ≈-refl)) ⟩
        (af' ∘ p₂) ∘co ((Rs' ∘ p₂) ∘co (((S' ∘ ab') ∘ p₂) ∘co (SF-P' ∘co SAM-P)))
      ≈˘⟨ CoK.∘-cong ≈-refl (CoK.assoc _ _ _) ⟩
        (af' ∘ p₂) ∘co (((Rs' ∘ p₂) ∘co ((S' ∘ ab') ∘ p₂)) ∘co (SF-P' ∘co SAM-P))
      ≈˘⟨ CoK.∘-cong ≈-refl (CoK.∘-cong (lift-comp Rs' (S' ∘ ab')) ≈-refl) ⟩
        (af' ∘ p₂) ∘co (((Rs' ∘ (S' ∘ ab')) ∘ p₂) ∘co (SF-P' ∘co SAM-P))
      ≈˘⟨ CoK.assoc _ _ _ ⟩
        ((af' ∘ p₂) ∘co ((Rs' ∘ (S' ∘ ab')) ∘ p₂)) ∘co (SF-P' ∘co SAM-P)
      ≈˘⟨ CoK.∘-cong (lift-comp af' (Rs' ∘ (S' ∘ ab'))) ≈-refl ⟩
        ((af' ∘ (Rs' ∘ (S' ∘ ab'))) ∘ p₂) ∘co (SF-P' ∘co SAM-P)
      ≈˘⟨ CoK.∘-cong (∘-cong (≈-trans (assoc _ _ _) (assoc _ _ _)) ≈-refl) ≈-refl ⟩
        ((((af' ∘ Rs') ∘ S') ∘ ab') ∘ p₂) ∘co (SF-P' ∘co SAM-P)
      ∎
      where open ≈-Reasoning isEquiv

-- Syntactic substitution is functor application.
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
  ≈⟨ ∘-cong (≈-trans (assoc _ _ _) (≈-trans (∘-cong ≈-refl (apply-bwd-fwd {0} {1} τ (λ ()) (extend δ∅ (⟦ τ' ⟧ty (λ ()))))) id-right)) ≈-refl ⟩
    (sb ∘ T⁻) ∘ (Rs ∘ sf)
  ≈˘⟨ assoc _ _ _ ⟩
    ((sb ∘ T⁻) ∘ Rs) ∘ sf
  ≈⟨ ∘-cong (≈-trans (assoc _ _ _) (≈-trans (∘-cong ≈-refl (as-poly-map-cast-inv τ (push-pw τ') δ∅)) id-right)) ≈-refl ⟩
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
  ≈⟨ ∘-cong (≈-trans (assoc _ _ _) (≈-trans (∘-cong ≈-refl (subst-fwd-bwd (push τ') τ (λ ()))) id-right)) ≈-refl ⟩
    (af ∘ Rs) ∘ (T⁻ ∘ ab)
  ≈˘⟨ assoc _ _ _ ⟩
    ((af ∘ Rs) ∘ T⁻) ∘ ab
  ≈⟨ ∘-cong (≈-trans (assoc _ _ _) (≈-trans (∘-cong ≈-refl (as-poly-map-cast-inv' τ (push-pw τ') δ∅)) id-right)) ≈-refl ⟩
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
                          fobj μ-obj (as-poly {0} {1} (sub (sub-lift (push ρ)) τ') (λ ())) (extend δ∅ X) ⇒
                          fobj μ-obj (as-poly {0} {2} τ' (λ ())) (extend (extend δ∅ (⟦ ρ ⟧ty (λ ()))) X)
sub-as-apply-fwd-μ-body τ' ρ X =
  apply-fwd-body τ' (λ ()) (extend δ∅ (⟦ ρ ⟧ty (λ ()))) X
    ∘ as-poly-map {1} {1} τ' (λ i → ≡-to-⇒ (push-pw ρ i)) (extend δ∅ X)
    ∘ subst-fwd-body (push ρ) τ' (λ ()) X

sub-as-apply-fwd-μ : ∀ (τ' : type 2) (ρ : type 0) →
                     sub-as-apply-fwd (μ τ') ρ
                       ≈ μ-map (as-poly {0} {1} (sub (sub-lift (push ρ)) τ') (λ ())) δ∅
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
  P₁ = as-poly {0} {1} (sub (sub-lift (push ρ)) τ') (λ ())
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
  sq = ≈-trans (≈-sym (assoc _ _ _))
       (≈-trans (∘-cong (as-poly-map-natural {1} {1} τ' cs E) ≈-refl)
       (≈-trans (assoc _ _ _)
       (≈-trans (∘-cong ≈-refl (subst-fwd-body-carrier (push ρ) τ' (λ ()) af))
                (≈-sym (assoc _ _ _)))))

sub-as-apply-fwd-μ-in : ∀ (τ' : type 2) (ρ : type 0) →
  (sub-as-apply-fwd (μ τ') ρ
     ∘ (inMap (as-poly {0} {1} (sub (sub-lift (push ρ)) τ') (λ ())) δ∅
        ∘ sub-as-apply-fwd (sub (sub-lift (push ρ)) τ') (μ (sub (sub-lift (push ρ)) τ'))))
    ≈ (inMap (as-poly {0} {2} τ' (λ ())) (extend δ∅ (⟦ ρ ⟧ty (λ ())))
       ∘ (sub-as-apply-fwd-μ-body τ' ρ (μ-obj (as-poly {0} {2} τ' (λ ())) (extend δ∅ (⟦ ρ ⟧ty (λ ()))))
          ∘ (fmor (as-poly {0} {1} (sub (sub-lift (push ρ)) τ') (λ ()))
               (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) (sub-as-apply-fwd (μ τ') ρ))
             ∘ sub-as-apply-fwd (sub (sub-lift (push ρ)) τ') (μ (sub (sub-lift (push ρ)) τ')))))
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
  A  = sub (sub-lift (push ρ)) τ'
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

abstract
  roll-mor : (τ : type 1) → ⟦ τ [ μ τ ] ⟧ty (λ ()) ⇒ ⟦ μ τ ⟧ty (λ ())
  roll-mor τ = inMap (as-poly τ (λ ())) δ∅ ∘ sub-as-apply-fwd τ (μ τ)

  unroll-mor : (τ : type 1) → ⟦ μ τ ⟧ty (λ ()) ⇒ ⟦ τ [ μ τ ] ⟧ty (λ ())
  unroll-mor τ = sub-as-apply-bwd τ (μ τ) ∘ R.LambekDef.outMor (as-poly τ (λ ())) δ∅

  unroll-roll : (τ : type 1) → (unroll-mor τ ∘ roll-mor τ) ≈ id _
  unroll-roll τ = begin
      (sb ∘ outm) ∘ (inm ∘ sf)
    ≈⟨ ≈-trans (assoc _ _ _) (∘-cong ≈-refl (≈-sym (assoc _ _ _))) ⟩
      sb ∘ ((outm ∘ inm) ∘ sf)
    ≈⟨ ∘-cong ≈-refl (≈-trans (∘-cong (R.LambekDef.outMor-inMor (as-poly τ (λ ())) δ∅) ≈-refl) id-left) ⟩
      sb ∘ sf
    ≈⟨ sub-as-apply-bwd-fwd τ (μ τ) ⟩
      id _
    ∎
    where
      open ≈-Reasoning isEquiv
      F₀ : Obj
      F₀ = fobj μ-obj (as-poly {0} {1} τ (λ ())) (extend δ∅ (⟦ μ τ ⟧ty (λ ())))
      sf : ⟦ τ [ μ τ ] ⟧ty (λ ()) ⇒ F₀
      sf   = sub-as-apply-fwd τ (μ τ)
      sb : F₀ ⇒ ⟦ τ [ μ τ ] ⟧ty (λ ())
      sb   = sub-as-apply-bwd τ (μ τ)
      inm : F₀ ⇒ ⟦ μ τ ⟧ty (λ ())
      inm  = inMap (as-poly τ (λ ())) δ∅
      outm : ⟦ μ τ ⟧ty (λ ()) ⇒ F₀
      outm = R.LambekDef.outMor (as-poly τ (λ ())) δ∅

  roll-unroll : (τ : type 1) → (roll-mor τ ∘ unroll-mor τ) ≈ id _
  roll-unroll τ = begin
      (inm ∘ sf) ∘ (sb ∘ outm)
    ≈⟨ ≈-trans (assoc _ _ _) (∘-cong ≈-refl (≈-sym (assoc _ _ _))) ⟩
      inm ∘ ((sf ∘ sb) ∘ outm)
    ≈⟨ ∘-cong ≈-refl (≈-trans (∘-cong (sub-as-apply-fwd-bwd τ (μ τ)) ≈-refl) id-left) ⟩
      inm ∘ outm
    ≈⟨ R.LambekDef.inMor-outMor (as-poly τ (λ ())) δ∅ ⟩
      id _
    ∎
    where
      open ≈-Reasoning isEquiv
      F₀ : Obj
      F₀ = fobj μ-obj (as-poly {0} {1} τ (λ ())) (extend δ∅ (⟦ μ τ ⟧ty (λ ())))
      sf : ⟦ τ [ μ τ ] ⟧ty (λ ()) ⇒ F₀
      sf   = sub-as-apply-fwd τ (μ τ)
      sb : F₀ ⇒ ⟦ τ [ μ τ ] ⟧ty (λ ())
      sb   = sub-as-apply-bwd τ (μ τ)
      inm : F₀ ⇒ ⟦ μ τ ⟧ty (λ ())
      inm  = inMap (as-poly τ (λ ())) δ∅
      outm : ⟦ μ τ ⟧ty (λ ()) ⇒ F₀
      outm = R.LambekDef.outMor (as-poly τ (λ ())) δ∅

  sub-as-apply-fwd-roll : ∀ (τ' : type 2) (ρ : type 0) →
    (sub-as-apply-fwd (μ τ') ρ ∘ roll-mor (sub (sub-lift (push ρ)) τ'))
      ≈ (inMap (as-poly {0} {2} τ' (λ ())) (extend δ∅ (⟦ ρ ⟧ty (λ ())))
         ∘ (sub-as-apply-fwd-μ-body τ' ρ (μ-obj (as-poly {0} {2} τ' (λ ())) (extend δ∅ (⟦ ρ ⟧ty (λ ()))))
            ∘ (fmor (as-poly {0} {1} (sub (sub-lift (push ρ)) τ') (λ ()))
                 (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) (sub-as-apply-fwd (μ τ') ρ))
               ∘ sub-as-apply-fwd (sub (sub-lift (push ρ)) τ') (μ (sub (sub-lift (push ρ)) τ')))))
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
        (preserves-as-poly-map τ (λ i → preserves-push-pw τ' i) δ∅ (λ ())))
      (preserves-subst-fwd (push τ') τ (λ ()))

  preserves-sub-as-apply-bwd : ∀ (τ : type 1) (τ' : type 0) →
    preserves-section (sub-as-apply-bwd τ τ')
      (poly-section (as-poly {0} {1} τ (λ ())) (as-poly-section {0} {1} τ (λ ()) (λ ()))
        (extend-section (λ ()) (unit-section τ' (λ ()) (λ ()))))
      (unit-section (τ [ τ' ]) (λ ()) (λ ()))
  preserves-sub-as-apply-bwd τ τ' =
    preserves-section-inv (sub-as-apply-fwd-bwd τ τ') (sub-as-apply-bwd-fwd τ τ')
      (preserves-sub-as-apply-fwd τ τ')

  preserves-roll-mor : ∀ (τ : type 1) →
    preserves-section (roll-mor τ)
      (unit-section (τ [ μ τ ]) (λ ()) (λ ())) (unit-section (μ τ) (λ ()) (λ ()))
  preserves-roll-mor τ =
    preserves-section-∘
      (preserves-inMap (as-poly {0} {1} τ (λ ())) δ∅ (λ ())
        (as-poly-section {0} {1} τ (λ ()) (λ ())))
      (preserves-sub-as-apply-fwd τ (μ τ))

  preserves-unroll-mor : ∀ (τ : type 1) →
    preserves-section (unroll-mor τ)
      (unit-section (μ τ) (λ ()) (λ ())) (unit-section (τ [ μ τ ]) (λ ()) (λ ()))
  preserves-unroll-mor τ =
    preserves-section-∘
      (preserves-sub-as-apply-bwd τ (μ τ))
      (preserves-outMor (as-poly {0} {1} τ (λ ())) δ∅ (λ ())
        (as-poly-section {0} {1} τ (λ ()) (λ ())))

  preserves-unroll-ctrl-dep : ∀ (τ : type 1) →
    preserves-section (unroll-mor τ) (ctrl-dep (μ τ)) (ctrl-dep (τ [ μ τ ]))
  preserves-unroll-ctrl-dep τ =
    preserves-scale {w = ctrl-w}
      {c = unit-section (μ τ) (λ ()) (λ ())} {d = unit-section (τ [ μ τ ]) (λ ()) (λ ())}
      (preserves-unroll-mor τ)

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

fold-map-unit : ∀ (τ₀ : type 1) (σ : type 0) {Γ' : Obj}
                (B : prod Γ' (⟦ τ₀ [ σ ] ⟧ty (λ ())) ⇒ ⟦ σ ⟧ty (λ ())) →
                fold-map τ₀ σ unit B ≈ p₂
fold-map-unit τ₀ σ B =
  ≈-trans (∘-cong (∘-cong bwd-id ≈-refl) (pair-cong ≈-refl (∘-cong fwd-id ≈-refl)))
  (≈-trans (∘-cong id-left (pair-cong ≈-refl id-left)) (pair-p₂ _ _))
  where
  bwd-id : sub-as-apply-bwd unit σ ≈ id _
  bwd-id = ≈-trans (∘-cong id-left ≈-refl) id-left
  fwd-id : sub-as-apply-fwd unit (μ τ₀) ≈ id _
  fwd-id = ≈-trans (∘-cong id-left ≈-refl) id-left

fold-map-base : ∀ (τ₀ : type 1) (σ : type 0) b {Γ' : Obj}
                (B : prod Γ' (⟦ τ₀ [ σ ] ⟧ty (λ ())) ⇒ ⟦ σ ⟧ty (λ ())) →
                fold-map τ₀ σ (base b) B ≈ p₂
fold-map-base τ₀ σ b B =
  ≈-trans (∘-cong (∘-cong bwd-id ≈-refl) (pair-cong ≈-refl (∘-cong fwd-id ≈-refl)))
  (≈-trans (∘-cong id-left (pair-cong ≈-refl id-left)) (pair-p₂ _ _))
  where
  bwd-id : sub-as-apply-bwd (base b) σ ≈ id _
  bwd-id = ≈-trans (∘-cong id-left ≈-refl) id-left
  fwd-id : sub-as-apply-fwd (base b) (μ τ₀) ≈ id _
  fwd-id = ≈-trans (∘-cong id-left ≈-refl) id-left

fold-map-arrow : ∀ (τ₀ : type 1) (σ : type 0) (σ₁ σ₂ : type 0) {Γ' : Obj}
                 (B : prod Γ' (⟦ τ₀ [ σ ] ⟧ty (λ ())) ⇒ ⟦ σ ⟧ty (λ ())) →
                 fold-map τ₀ σ (σ₁ [→] σ₂) B ≈ p₂
fold-map-arrow τ₀ σ σ₁ σ₂ B =
  ≈-trans (∘-cong (∘-cong bwd-id ≈-refl) (pair-cong ≈-refl (∘-cong fwd-id ≈-refl)))
  (≈-trans (∘-cong id-left (pair-cong ≈-refl id-left)) (pair-p₂ _ _))
  where
  bwd-id : sub-as-apply-bwd (σ₁ [→] σ₂) σ ≈ id _
  bwd-id = ≈-trans (∘-cong id-left ≈-refl) id-left
  fwd-id : sub-as-apply-fwd (σ₁ [→] σ₂) (μ τ₀) ≈ id _
  fwd-id = ≈-trans (∘-cong id-left ≈-refl) id-left

private
  pair-p₁-comp : ∀ {Γ X Y Z : Obj} (u : Y ⇒ Z) (v : X ⇒ Y) →
                 (⟨ p₁ {Γ} , u ∘ p₂ ⟩ ∘ ⟨ p₁ , v ∘ p₂ ⟩) ≈ ⟨ p₁ , (u ∘ v) ∘ p₂ ⟩
  pair-p₁-comp u v =
    ≈-trans (pair-natural _ _ _)
    (pair-cong (pair-p₁ _ _)
      (≈-trans (assoc _ _ _) (≈-trans (∘-cong ≈-refl (pair-p₂ _ _)) (≈-sym (assoc _ _ _)))))

  sub-as-apply-fwd-[+] : ∀ (σ₁ σ₂ : type 1) (τ' : type 0) →
    sub-as-apply-fwd (σ₁ [+] σ₂) τ' ≈ [+]-map (sub-as-apply-fwd σ₁ τ') (sub-as-apply-fwd σ₂ τ')
  sub-as-apply-fwd-[+] σ₁ σ₂ τ' =
    ≈-trans (∘-cong ([+]-map-comp _ _ _ _) ≈-refl) ([+]-map-comp _ _ _ _)

  sub-as-apply-bwd-[+] : ∀ (σ₁ σ₂ : type 1) (τ' : type 0) →
    sub-as-apply-bwd (σ₁ [+] σ₂) τ' ≈ [+]-map (sub-as-apply-bwd σ₁ τ') (sub-as-apply-bwd σ₂ τ')
  sub-as-apply-bwd-[+] σ₁ σ₂ τ' =
    ≈-trans (∘-cong ([+]-map-comp _ _ _ _) ≈-refl) ([+]-map-comp _ _ _ _)

  sub-as-apply-fwd-[×] : ∀ (σ₁ σ₂ : type 1) (τ' : type 0) →
    sub-as-apply-fwd (σ₁ [×] σ₂) τ' ≈ [×]-map (sub-as-apply-fwd σ₁ τ') (sub-as-apply-fwd σ₂ τ')
  sub-as-apply-fwd-[×] σ₁ σ₂ τ' =
    ≈-trans (∘-cong ([×]-map-comp _ _ _ _) ≈-refl) ([×]-map-comp _ _ _ _)

  sub-as-apply-bwd-[×] : ∀ (σ₁ σ₂ : type 1) (τ' : type 0) →
    sub-as-apply-bwd (σ₁ [×] σ₂) τ' ≈ [×]-map (sub-as-apply-bwd σ₁ τ') (sub-as-apply-bwd σ₂ τ')
  sub-as-apply-bwd-[×] σ₁ σ₂ τ' =
    ≈-trans (∘-cong ([×]-map-comp _ _ _ _) ≈-refl) ([×]-map-comp _ _ _ _)

fold-map-inl : ∀ (τ₀ : type 1) (σ : type 0) (σ₁ σ₂ : type 1) {Γ' : Obj}
               (B : prod Γ' (⟦ τ₀ [ σ ] ⟧ty (λ ())) ⇒ ⟦ σ ⟧ty (λ ())) →
               (fold-map τ₀ σ (σ₁ [+] σ₂) B ∘ ⟨ p₁ , (in₁ ∘ injF) ∘ p₂ ⟩)
                 ≈ ((in₁ ∘ injF) ∘ fold-map τ₀ σ σ₁ B)
fold-map-inl τ₀ σ σ₁ σ₂ {Γ'} B = begin
    ((b⁺ ∘ S⁺) ∘ ⟨ p₁ , f⁺ ∘ p₂ ⟩) ∘ ⟨ p₁ , (in₁ ∘ injF) ∘ p₂ ⟩
  ≈⟨ assoc _ _ _ ⟩
    (b⁺ ∘ S⁺) ∘ (⟨ p₁ , f⁺ ∘ p₂ ⟩ ∘ ⟨ p₁ , (in₁ ∘ injF) ∘ p₂ ⟩)
  ≈⟨ ∘-cong ≈-refl (pair-p₁-comp f⁺ (in₁ ∘ injF)) ⟩
    (b⁺ ∘ S⁺) ∘ ⟨ p₁ , (f⁺ ∘ (in₁ ∘ injF)) ∘ p₂ ⟩
  ≈⟨ ∘-cong ≈-refl (pair-cong ≈-refl (∘-cong
       (≈-trans (∘-cong (sub-as-apply-fwd-[+] σ₁ σ₂ (μ τ₀)) ≈-refl)
         ([+]-map-inj₁ f₁ (sub-as-apply-fwd σ₂ (μ τ₀)))) ≈-refl)) ⟩
    (b⁺ ∘ S⁺) ∘ ⟨ p₁ , ((in₁ ∘ injF) ∘ f₁) ∘ p₂ ⟩
  ≈˘⟨ ∘-cong ≈-refl (pair-p₁-comp (in₁ ∘ injF) f₁) ⟩
    (b⁺ ∘ S⁺) ∘ (⟨ p₁ , (in₁ ∘ injF) ∘ p₂ ⟩ ∘ ⟨ p₁ , f₁ ∘ p₂ ⟩)
  ≈˘⟨ ∘-cong ≈-refl (∘-cong (pair-p₁-comp in₁ injF) ≈-refl) ⟩
    (b⁺ ∘ S⁺) ∘ ((⟨ p₁ , in₁ ∘ p₂ ⟩ ∘ ⟨ p₁ , injF ∘ p₂ ⟩) ∘ ⟨ p₁ , f₁ ∘ p₂ ⟩)
  ≈˘⟨ assoc _ _ _ ⟩
    ((b⁺ ∘ S⁺) ∘ (⟨ p₁ , in₁ ∘ p₂ ⟩ ∘ ⟨ p₁ , injF ∘ p₂ ⟩)) ∘ ⟨ p₁ , f₁ ∘ p₂ ⟩
  ≈˘⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
    (((b⁺ ∘ S⁺) ∘ ⟨ p₁ , in₁ ∘ p₂ ⟩) ∘ ⟨ p₁ , injF ∘ p₂ ⟩) ∘ ⟨ p₁ , f₁ ∘ p₂ ⟩
  ≈⟨ ∘-cong (∘-cong (≈-trans (assoc _ _ _) (∘-cong ≈-refl (scopair-in₁ _ _))) ≈-refl) ≈-refl ⟩
    ((b⁺ ∘ (in₁ ∘ strong-Lf-map S₁)) ∘ ⟨ p₁ , injF ∘ p₂ ⟩) ∘ ⟨ p₁ , f₁ ∘ p₂ ⟩
  ≈⟨ ∘-cong (≈-trans (assoc _ _ _) (∘-cong ≈-refl
       (≈-trans (assoc _ _ _) (∘-cong ≈-refl (strong-Lf-map-injF S₁))))) ≈-refl ⟩
    (b⁺ ∘ (in₁ ∘ (injF ∘ S₁))) ∘ ⟨ p₁ , f₁ ∘ p₂ ⟩
  ≈˘⟨ ∘-cong (∘-cong ≈-refl (assoc _ _ _)) ≈-refl ⟩
    (b⁺ ∘ ((in₁ ∘ injF) ∘ S₁)) ∘ ⟨ p₁ , f₁ ∘ p₂ ⟩
  ≈˘⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
    ((b⁺ ∘ (in₁ ∘ injF)) ∘ S₁) ∘ ⟨ p₁ , f₁ ∘ p₂ ⟩
  ≈⟨ ∘-cong (∘-cong (≈-trans (∘-cong (sub-as-apply-bwd-[+] σ₁ σ₂ σ) ≈-refl)
       ([+]-map-inj₁ b₁ (sub-as-apply-bwd σ₂ σ))) ≈-refl) ≈-refl ⟩
    (((in₁ ∘ injF) ∘ b₁) ∘ S₁) ∘ ⟨ p₁ , f₁ ∘ p₂ ⟩
  ≈⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
    ((in₁ ∘ injF) ∘ (b₁ ∘ S₁)) ∘ ⟨ p₁ , f₁ ∘ p₂ ⟩
  ≈⟨ assoc _ _ _ ⟩
    (in₁ ∘ injF) ∘ ((b₁ ∘ S₁) ∘ ⟨ p₁ , f₁ ∘ p₂ ⟩)
  ∎
  where
  open ≈-Reasoning isEquiv
  f⁺ = sub-as-apply-fwd (σ₁ [+] σ₂) (μ τ₀)
  f₁ = sub-as-apply-fwd σ₁ (μ τ₀)
  b⁺ = sub-as-apply-bwd (σ₁ [+] σ₂) σ
  b₁ = sub-as-apply-bwd σ₁ σ
  S⁺ : prod Γ' (fobj μ-obj (as-poly {0} {1} (σ₁ [+] σ₂) (λ ())) (extend δ∅ (⟦ μ τ₀ ⟧ty (λ ()))))
       ⇒ fobj μ-obj (as-poly {0} {1} (σ₁ [+] σ₂) (λ ())) (extend δ∅ (⟦ σ ⟧ty (λ ())))
  S⁺ = strong-fmor (as-poly {0} {1} (σ₁ [+] σ₂) (λ ())) (strong-extend-mor (λ ()) (⦅ fold-alg τ₀ σ B ⦆))
  S₁ : prod Γ' (fobj μ-obj (as-poly {0} {1} σ₁ (λ ())) (extend δ∅ (⟦ μ τ₀ ⟧ty (λ ()))))
       ⇒ fobj μ-obj (as-poly {0} {1} σ₁ (λ ())) (extend δ∅ (⟦ σ ⟧ty (λ ())))
  S₁ = strong-fmor (as-poly {0} {1} σ₁ (λ ())) (strong-extend-mor (λ ()) (⦅ fold-alg τ₀ σ B ⦆))

fold-map-inr : ∀ (τ₀ : type 1) (σ : type 0) (σ₁ σ₂ : type 1) {Γ' : Obj}
               (B : prod Γ' (⟦ τ₀ [ σ ] ⟧ty (λ ())) ⇒ ⟦ σ ⟧ty (λ ())) →
               (fold-map τ₀ σ (σ₁ [+] σ₂) B ∘ ⟨ p₁ , (in₂ ∘ injF) ∘ p₂ ⟩)
                 ≈ ((in₂ ∘ injF) ∘ fold-map τ₀ σ σ₂ B)
fold-map-inr τ₀ σ σ₁ σ₂ {Γ'} B = begin
    ((b⁺ ∘ S⁺) ∘ ⟨ p₁ , f⁺ ∘ p₂ ⟩) ∘ ⟨ p₁ , (in₂ ∘ injF) ∘ p₂ ⟩
  ≈⟨ assoc _ _ _ ⟩
    (b⁺ ∘ S⁺) ∘ (⟨ p₁ , f⁺ ∘ p₂ ⟩ ∘ ⟨ p₁ , (in₂ ∘ injF) ∘ p₂ ⟩)
  ≈⟨ ∘-cong ≈-refl (pair-p₁-comp f⁺ (in₂ ∘ injF)) ⟩
    (b⁺ ∘ S⁺) ∘ ⟨ p₁ , (f⁺ ∘ (in₂ ∘ injF)) ∘ p₂ ⟩
  ≈⟨ ∘-cong ≈-refl (pair-cong ≈-refl (∘-cong
       (≈-trans (∘-cong (sub-as-apply-fwd-[+] σ₁ σ₂ (μ τ₀)) ≈-refl)
         ([+]-map-inj₂ (sub-as-apply-fwd σ₁ (μ τ₀)) f₂)) ≈-refl)) ⟩
    (b⁺ ∘ S⁺) ∘ ⟨ p₁ , ((in₂ ∘ injF) ∘ f₂) ∘ p₂ ⟩
  ≈˘⟨ ∘-cong ≈-refl (pair-p₁-comp (in₂ ∘ injF) f₂) ⟩
    (b⁺ ∘ S⁺) ∘ (⟨ p₁ , (in₂ ∘ injF) ∘ p₂ ⟩ ∘ ⟨ p₁ , f₂ ∘ p₂ ⟩)
  ≈˘⟨ ∘-cong ≈-refl (∘-cong (pair-p₁-comp in₂ injF) ≈-refl) ⟩
    (b⁺ ∘ S⁺) ∘ ((⟨ p₁ , in₂ ∘ p₂ ⟩ ∘ ⟨ p₁ , injF ∘ p₂ ⟩) ∘ ⟨ p₁ , f₂ ∘ p₂ ⟩)
  ≈˘⟨ assoc _ _ _ ⟩
    ((b⁺ ∘ S⁺) ∘ (⟨ p₁ , in₂ ∘ p₂ ⟩ ∘ ⟨ p₁ , injF ∘ p₂ ⟩)) ∘ ⟨ p₁ , f₂ ∘ p₂ ⟩
  ≈˘⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
    (((b⁺ ∘ S⁺) ∘ ⟨ p₁ , in₂ ∘ p₂ ⟩) ∘ ⟨ p₁ , injF ∘ p₂ ⟩) ∘ ⟨ p₁ , f₂ ∘ p₂ ⟩
  ≈⟨ ∘-cong (∘-cong (≈-trans (assoc _ _ _) (∘-cong ≈-refl (scopair-in₂ _ _))) ≈-refl) ≈-refl ⟩
    ((b⁺ ∘ (in₂ ∘ strong-Lf-map S₂)) ∘ ⟨ p₁ , injF ∘ p₂ ⟩) ∘ ⟨ p₁ , f₂ ∘ p₂ ⟩
  ≈⟨ ∘-cong (≈-trans (assoc _ _ _) (∘-cong ≈-refl
       (≈-trans (assoc _ _ _) (∘-cong ≈-refl (strong-Lf-map-injF S₂))))) ≈-refl ⟩
    (b⁺ ∘ (in₂ ∘ (injF ∘ S₂))) ∘ ⟨ p₁ , f₂ ∘ p₂ ⟩
  ≈˘⟨ ∘-cong (∘-cong ≈-refl (assoc _ _ _)) ≈-refl ⟩
    (b⁺ ∘ ((in₂ ∘ injF) ∘ S₂)) ∘ ⟨ p₁ , f₂ ∘ p₂ ⟩
  ≈˘⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
    ((b⁺ ∘ (in₂ ∘ injF)) ∘ S₂) ∘ ⟨ p₁ , f₂ ∘ p₂ ⟩
  ≈⟨ ∘-cong (∘-cong (≈-trans (∘-cong (sub-as-apply-bwd-[+] σ₁ σ₂ σ) ≈-refl)
       ([+]-map-inj₂ (sub-as-apply-bwd σ₁ σ) b₂)) ≈-refl) ≈-refl ⟩
    (((in₂ ∘ injF) ∘ b₂) ∘ S₂) ∘ ⟨ p₁ , f₂ ∘ p₂ ⟩
  ≈⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
    ((in₂ ∘ injF) ∘ (b₂ ∘ S₂)) ∘ ⟨ p₁ , f₂ ∘ p₂ ⟩
  ≈⟨ assoc _ _ _ ⟩
    (in₂ ∘ injF) ∘ ((b₂ ∘ S₂) ∘ ⟨ p₁ , f₂ ∘ p₂ ⟩)
  ∎
  where
  open ≈-Reasoning isEquiv
  f⁺ = sub-as-apply-fwd (σ₁ [+] σ₂) (μ τ₀)
  f₂ = sub-as-apply-fwd σ₂ (μ τ₀)
  b⁺ = sub-as-apply-bwd (σ₁ [+] σ₂) σ
  b₂ = sub-as-apply-bwd σ₂ σ
  S⁺ : prod Γ' (fobj μ-obj (as-poly {0} {1} (σ₁ [+] σ₂) (λ ())) (extend δ∅ (⟦ μ τ₀ ⟧ty (λ ()))))
       ⇒ fobj μ-obj (as-poly {0} {1} (σ₁ [+] σ₂) (λ ())) (extend δ∅ (⟦ σ ⟧ty (λ ())))
  S⁺ = strong-fmor (as-poly {0} {1} (σ₁ [+] σ₂) (λ ())) (strong-extend-mor (λ ()) (⦅ fold-alg τ₀ σ B ⦆))
  S₂ : prod Γ' (fobj μ-obj (as-poly {0} {1} σ₂ (λ ())) (extend δ∅ (⟦ μ τ₀ ⟧ty (λ ()))))
       ⇒ fobj μ-obj (as-poly {0} {1} σ₂ (λ ())) (extend δ∅ (⟦ σ ⟧ty (λ ())))
  S₂ = strong-fmor (as-poly {0} {1} σ₂ (λ ())) (strong-extend-mor (λ ()) (⦅ fold-alg τ₀ σ B ⦆))

fold-map-pair : ∀ (τ₀ : type 1) (σ : type 0) (σ₁ σ₂ : type 1) {Γ' : Obj}
                (B : prod Γ' (⟦ τ₀ [ σ ] ⟧ty (λ ())) ⇒ ⟦ σ ⟧ty (λ ())) →
                (fold-map τ₀ σ (σ₁ [×] σ₂) B ∘ ⟨ p₁ , injF ∘ p₂ ⟩)
                  ≈ (injF ∘ strong-prod-m (fold-map τ₀ σ σ₁ B) (fold-map τ₀ σ σ₂ B))
fold-map-pair τ₀ σ σ₁ σ₂ {Γ'} B = begin
    ((b× ∘ S×) ∘ ⟨ p₁ , f× ∘ p₂ ⟩) ∘ ⟨ p₁ , injF ∘ p₂ ⟩
  ≈⟨ assoc _ _ _ ⟩
    (b× ∘ S×) ∘ (⟨ p₁ , f× ∘ p₂ ⟩ ∘ ⟨ p₁ , injF ∘ p₂ ⟩)
  ≈⟨ ∘-cong ≈-refl (pair-p₁-comp f× injF) ⟩
    (b× ∘ S×) ∘ ⟨ p₁ , (f× ∘ injF) ∘ p₂ ⟩
  ≈⟨ ∘-cong ≈-refl (pair-cong ≈-refl (∘-cong
       (≈-trans (∘-cong (sub-as-apply-fwd-[×] σ₁ σ₂ (μ τ₀)) ≈-refl)
         (injF-natural (prod-m f₁ f₂))) ≈-refl)) ⟩
    (b× ∘ S×) ∘ ⟨ p₁ , (injF ∘ prod-m f₁ f₂) ∘ p₂ ⟩
  ≈˘⟨ ∘-cong ≈-refl (pair-p₁-comp injF (prod-m f₁ f₂)) ⟩
    (b× ∘ S×) ∘ (⟨ p₁ , injF ∘ p₂ ⟩ ∘ ⟨ p₁ , prod-m f₁ f₂ ∘ p₂ ⟩)
  ≈˘⟨ assoc _ _ _ ⟩
    ((b× ∘ S×) ∘ ⟨ p₁ , injF ∘ p₂ ⟩) ∘ ⟨ p₁ , prod-m f₁ f₂ ∘ p₂ ⟩
  ≈⟨ ∘-cong (≈-trans (assoc _ _ _)
       (∘-cong ≈-refl (strong-Lf-map-injF (strong-prod-m S₁ S₂)))) ≈-refl ⟩
    (b× ∘ (injF ∘ strong-prod-m S₁ S₂)) ∘ ⟨ p₁ , prod-m f₁ f₂ ∘ p₂ ⟩
  ≈˘⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
    ((b× ∘ injF) ∘ strong-prod-m S₁ S₂) ∘ ⟨ p₁ , prod-m f₁ f₂ ∘ p₂ ⟩
  ≈⟨ ∘-cong (∘-cong (≈-trans (∘-cong (sub-as-apply-bwd-[×] σ₁ σ₂ σ) ≈-refl)
       (injF-natural (prod-m b₁ b₂))) ≈-refl) ≈-refl ⟩
    ((injF ∘ prod-m b₁ b₂) ∘ strong-prod-m S₁ S₂) ∘ ⟨ p₁ , prod-m f₁ f₂ ∘ p₂ ⟩
  ≈⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
    (injF ∘ (prod-m b₁ b₂ ∘ strong-prod-m S₁ S₂)) ∘ ⟨ p₁ , prod-m f₁ f₂ ∘ p₂ ⟩
  ≈⟨ ∘-cong (∘-cong ≈-refl (strong-prod-m-post b₁ b₂ S₁ S₂)) ≈-refl ⟩
    (injF ∘ strong-prod-m (b₁ ∘ S₁) (b₂ ∘ S₂)) ∘ ⟨ p₁ , prod-m f₁ f₂ ∘ p₂ ⟩
  ≈⟨ assoc _ _ _ ⟩
    injF ∘ (strong-prod-m (b₁ ∘ S₁) (b₂ ∘ S₂) ∘ ⟨ p₁ , prod-m f₁ f₂ ∘ p₂ ⟩)
  ≈⟨ ∘-cong ≈-refl (≈-trans (∘-cong ≈-refl (pair-cong (≈-sym id-left) ≈-refl))
       (≈-trans (strong-prod-m-pre (b₁ ∘ S₁) (b₂ ∘ S₂) (id _) f₁ f₂)
         (strong-prod-m-cong (∘-cong ≈-refl (pair-cong id-left ≈-refl))
                             (∘-cong ≈-refl (pair-cong id-left ≈-refl))))) ⟩
    injF ∘ strong-prod-m ((b₁ ∘ S₁) ∘ ⟨ p₁ , f₁ ∘ p₂ ⟩) ((b₂ ∘ S₂) ∘ ⟨ p₁ , f₂ ∘ p₂ ⟩)
  ∎
  where
  open ≈-Reasoning isEquiv
  f× = sub-as-apply-fwd (σ₁ [×] σ₂) (μ τ₀)
  f₁ = sub-as-apply-fwd σ₁ (μ τ₀)
  f₂ = sub-as-apply-fwd σ₂ (μ τ₀)
  b× = sub-as-apply-bwd (σ₁ [×] σ₂) σ
  b₁ = sub-as-apply-bwd σ₁ σ
  b₂ = sub-as-apply-bwd σ₂ σ
  S× : prod Γ' (fobj μ-obj (as-poly {0} {1} (σ₁ [×] σ₂) (λ ())) (extend δ∅ (⟦ μ τ₀ ⟧ty (λ ()))))
       ⇒ fobj μ-obj (as-poly {0} {1} (σ₁ [×] σ₂) (λ ())) (extend δ∅ (⟦ σ ⟧ty (λ ())))
  S× = strong-fmor (as-poly {0} {1} (σ₁ [×] σ₂) (λ ())) (strong-extend-mor (λ ()) (⦅ fold-alg τ₀ σ B ⦆))
  S₁ : prod Γ' (fobj μ-obj (as-poly {0} {1} σ₁ (λ ())) (extend δ∅ (⟦ μ τ₀ ⟧ty (λ ()))))
       ⇒ fobj μ-obj (as-poly {0} {1} σ₁ (λ ())) (extend δ∅ (⟦ σ ⟧ty (λ ())))
  S₁ = strong-fmor (as-poly {0} {1} σ₁ (λ ())) (strong-extend-mor (λ ()) (⦅ fold-alg τ₀ σ B ⦆))
  S₂ : prod Γ' (fobj μ-obj (as-poly {0} {1} σ₂ (λ ())) (extend δ∅ (⟦ μ τ₀ ⟧ty (λ ()))))
       ⇒ fobj μ-obj (as-poly {0} {1} σ₂ (λ ())) (extend δ∅ (⟦ σ ⟧ty (λ ())))
  S₂ = strong-fmor (as-poly {0} {1} σ₂ (λ ())) (strong-extend-mor (λ ()) (⦅ fold-alg τ₀ σ B ⦆))

⟦_⟧ctxt : ctxt → obj
⟦ emp ⟧ctxt   = 𝟙
⟦ Γ , τ ⟧ctxt = prod ⟦ Γ ⟧ctxt (⟦ τ ⟧ty (λ ()))

⟦_⟧var : ∀ {Γ τ} → Γ ∋ τ → ⟦ Γ ⟧ctxt ⇒ ⟦ τ ⟧ty (λ ())
⟦ zero ⟧var   = p₂
⟦ succ x ⟧var = ⟦ x ⟧var ∘ p₁

open import every using (Every; []; _∷_)
open PointedFPCat PFPC[ R.cat , R.terminal T , R.products , Bool ] using (list→product)

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
