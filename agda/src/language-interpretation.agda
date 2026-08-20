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
              strong-Lf-map; strong-Lf-map-cong; strong-Lf-map-comp; strong-Lf-map-injF;
              extend; extend-mor; fobj; HasMu; hasMu; HasMuLaws; hasMuLaws; _∘co_;
              Section; elimF; scale-section; Lf-section; coprod-section; prod-section; PolySection;
              poly-section; extend-section; preserves-section; preserves-section-id;
              preserves-section-∘; preserves-section-resp; preserves-section-inv;
              preserves-coprod-m; preserves-prod-m; preserves-Lf-map; preserves-scale;
              preserves-inMap; preserves-outMor)
open R.WithTerminal T
  using (fmor; μ-map;
         fmor-cong; fmor-id; fmor-comp; fmor-const; fmor-var; fmor-+; fmor-×; fmor-μ;
         μ-map-cong; μ-map-id; μ-map-in; μ-map-comp; preserves-μ-map)
open Category R.cat
open HasTerminal (R.terminal T) renaming (witness to 𝟙)
open HasProducts R.products renaming (pair to ⟨_,_⟩)

open HasCoproducts R.coproducts using (coprod; coprod-m; coprod-m-cong; coprod-m-comp; coprod-m-id; in₁; in₂;
                                       copair-cong; copair-in₁; copair-in₂; copair-ext)
open HasStrongCoproducts R.strongCoproducts
  using () renaming (copair to scopair; copair-cong to scopair-cong;
                     copair-in₁ to scopair-in₁; copair-in₂ to scopair-in₂)
open HasExponentials 𝒞E using (lambda; eval) renaming (exp to _⟦→⟧_)
open language-syntax Sig
open HasMu hasMu
open HasMuLaws hasMuLaws
  using (⦅⦆-cong; ⦅⦆-β; fusion; ∘co-push; copair-comp;
         strong-fmor-comp; strong-fmor-cong; strong-extend-mor-comp)

private
  module CoK {Γ' : Obj} = Category (coKleisli-prod R.products Γ')
open Model Int

-- A type is interpreted as its polynomial, with the variables frozen at the environment, applied
-- at the empty environment; under a μ, the bound variables stay free.
mutual
  ⟦_⟧ty : ∀ {Δ} → type Δ → (Fin Δ → obj) → obj
  ⟦ τ ⟧ty δ = fobj μ-obj (as-poly {n = 0} τ δ) δ∅

  as-poly : ∀ {Δ n} → type (n + Δ) → (Fin Δ → obj) → Poly R.cat n
  as-poly {Δ} {n} (var i) δ = [ Poly.var , (λ j → Poly.const (δ j)) ] (splitAt n i)
  as-poly unit            δ = Poly.const 𝟙ty
  as-poly (base s)        δ = Poly.const (⟦sort⟧ s)
  as-poly (σ [+] τ)       δ = as-poly σ δ Poly.+ as-poly τ δ
  as-poly (σ [×] τ)       δ = as-poly σ δ Poly.× as-poly τ δ
  as-poly (σ [→] τ)       δ = Poly.const (Lf (⟦ σ ⟧ty (λ ()) ⟦→⟧ ⟦ τ ⟧ty (λ ())))
  as-poly (μ τ)           δ = Poly.μ (as-poly τ δ)

as-poly-var-section : ∀ {Δ n} (δ : Fin Δ → obj) → (∀ i → Section (δ i)) → (s : Fin n ⊎ Fin Δ) →
                      PolySection ([_,_] {C = λ _ → Poly R.cat n} Poly.var (λ j → Poly.const (δ j)) s)
as-poly-var-section δ δc (inj₁ k) = lift tt
as-poly-var-section δ δc (inj₂ j) = δc j

-- Sections for a type's polynomial: the assumed sections at the constant leaves.
as-poly-section : ∀ {Δ n} (τ : type (n + Δ)) (δ : Fin Δ → obj) → (∀ i → Section (δ i)) →
                PolySection (as-poly {Δ} {n} τ δ)
as-poly-section (var i)   δ δc = as-poly-var-section δ δc (splitAt _ i)
as-poly-section unit      δ δc = 𝟙ty-section
as-poly-section (base s)  δ δc = sort-section s
as-poly-section (σ [+] τ) δ δc = DP._,_ (as-poly-section σ δ δc) (as-poly-section τ δ δc)
as-poly-section (σ [×] τ) δ δc = DP._,_ (as-poly-section σ δ δc) (as-poly-section τ δ δc)
as-poly-section (σ [→] τ) δ δc = Lf-section exp-section
as-poly-section (μ τ)     δ δc = as-poly-section τ δ δc

-- The unit section of a type's interpretation.
unit-section : ∀ {Δ} (τ : type Δ) (δ : Fin Δ → obj) → (∀ i → Section (δ i)) → Section (⟦ τ ⟧ty δ)
unit-section τ δ δc = R.poly-section (as-poly τ δ) (as-poly-section τ δ δc) (λ ())

-- The control dependence an eliminator writes: the result type's unit section scaled by the control
-- weight.
ctrl-dep : ∀ (τ : type 0) → Section (⟦ τ ⟧ty (λ ()))
ctrl-dep τ = scale-section ctrl-w (unit-section τ (λ ()) (λ ()))

-- Combined context: the first n variables from δ₀ (the Poly variables), the rest from δ.
concat : ∀ {n Δ} → (Fin n → obj) → (Fin Δ → obj) → Fin (n + Δ) → obj
concat {n} δ₀ δ i = [ δ₀ , δ ] (splitAt n i)

-- Both as-poly and ⟦_⟧ty respect pointwise-equal environments.
as-poly-cong : ∀ {Δ n} (τ : type (n + Δ)) {δ δ' : Fin Δ → obj} → (∀ i → δ i ≡ δ' i) → as-poly τ δ ≡ as-poly τ δ'
as-poly-cong {Δ} {n} (var i) {δ} {δ'} h = go (splitAt n i)
  where
    go : (s : Fin n ⊎ Fin Δ) → [ Poly.var , (λ j → Poly.const (δ j)) ] s ≡ [ Poly.var , (λ j → Poly.const (δ' j)) ] s
    go (inj₁ k) = refl
    go (inj₂ j) = cong Poly.const (h j)
as-poly-cong unit      h = refl
as-poly-cong (base s)  h = refl
as-poly-cong (σ [+] τ) h = cong₂ Poly._+_ (as-poly-cong σ h) (as-poly-cong τ h)
as-poly-cong (σ [×] τ) h = cong₂ Poly._×_ (as-poly-cong σ h) (as-poly-cong τ h)
as-poly-cong (σ [→] τ) h = refl
as-poly-cong (μ τ)     h = cong Poly.μ (as-poly-cong τ h)

ty-cong : ∀ {Δ} (τ : type Δ) {δ δ' : Fin Δ → obj} → (∀ i → δ i ≡ δ' i) → ⟦ τ ⟧ty δ ≡ ⟦ τ ⟧ty δ'
ty-cong τ h = cong (λ P → fobj μ-obj P δ∅) (as-poly-cong τ h)

-- Renaming a type is reindexing its environment. extᵗⁿ leaves the first n (poly) variables alone,
-- so splitAt commutes with it.
splitAt-extᵗⁿ : ∀ {Δ₁ Δ₂} n (ρ : TyRen Δ₁ Δ₂) (i : Fin (n + Δ₁)) →
                splitAt n (extᵗⁿ n ρ i) ≡ [ inj₁ , (λ k → inj₂ (ρ k)) ] (splitAt n i)
splitAt-extᵗⁿ zero    ρ i           = refl
splitAt-extᵗⁿ (suc n) ρ Fin.zero    = refl
splitAt-extᵗⁿ {Δ₁} (suc n) ρ (Fin.suc i) =
  trans (cong (map₁ Fin.suc) (splitAt-extᵗⁿ n ρ i)) (go (splitAt n i))
  where
    go : (s : Fin n ⊎ Fin Δ₁) →
         map₁ Fin.suc ([ inj₁ , (λ k → inj₂ (ρ k)) ] s) ≡ [ inj₁ , (λ k → inj₂ (ρ k)) ] (map₁ Fin.suc s)
    go (inj₁ j) = refl
    go (inj₂ k) = refl

as-poly-ren : ∀ {Δ₁ Δ₂ n} (ρ : TyRen Δ₁ Δ₂) (τ : type (n + Δ₁)) (δ : Fin Δ₂ → obj) →
              as-poly {Δ₂} {n} (extᵗⁿ n ρ *ᵗ τ) δ ≡ as-poly {Δ₁} {n} τ (λ i → δ (ρ i))
as-poly-ren {Δ₁} {Δ₂} {n} ρ (var i) δ = go (splitAt n i) (splitAt n (extᵗⁿ n ρ i)) (splitAt-extᵗⁿ n ρ i)
  where
    go : (s : Fin n ⊎ Fin Δ₁) (s' : Fin n ⊎ Fin Δ₂) → s' ≡ [ inj₁ , (λ k → inj₂ (ρ k)) ] s →
         [ Poly.var , (λ j → Poly.const (δ j)) ] s' ≡ [ Poly.var , (λ j → Poly.const (δ (ρ j))) ] s
    go (inj₁ j) _ refl = refl
    go (inj₂ k) _ refl = refl
as-poly-ren ρ unit      δ = refl
as-poly-ren ρ (base s)  δ = refl
as-poly-ren ρ (σ [+] τ) δ = cong₂ Poly._+_ (as-poly-ren ρ σ δ) (as-poly-ren ρ τ δ)
as-poly-ren ρ (σ [×] τ) δ = cong₂ Poly._×_ (as-poly-ren ρ σ δ) (as-poly-ren ρ τ δ)
as-poly-ren ρ (σ [→] τ) δ = refl
as-poly-ren ρ (μ τ)     δ = cong Poly.μ (as-poly-ren ρ τ δ)

ty-ren : ∀ {Δ₁ Δ₂} (ρ : TyRen Δ₁ Δ₂) (τ : type Δ₁) (δ : Fin Δ₂ → obj) →
         ⟦ ρ *ᵗ τ ⟧ty δ ≡ ⟦ τ ⟧ty (λ i → δ (ρ i))
ty-ren ρ τ δ = cong (λ P → fobj μ-obj P δ∅) (as-poly-ren ρ τ δ)

private
  module CP = HasCoproducts (strong-coproducts→coproducts (R.terminal T) R.strongCoproducts)

coprod-m-strong : ∀ {X X' Y Y'} (f : X ⇒ X') (g : Y ⇒ Y') → coprod-m f g ≈ CP.coprod-m f g
coprod-m-strong f g = ≈-trans (copair-cong (≈-sym (CP.copair-in₁ _ _)) (≈-sym (CP.copair-in₂ _ _))) (copair-ext _)

[+]-map : ∀ {A A' B B' : obj} → A ⇒ A' → B ⇒ B' → coprod (Lf A) (Lf B) ⇒ coprod (Lf A') (Lf B')
[+]-map f g = coprod-m (Lf-map f) (Lf-map g)

[×]-map : ∀ {A A' B B' : obj} → A ⇒ A' → B ⇒ B' → Lf (prod A B) ⇒ Lf (prod A' B')
[×]-map f g = Lf-map (prod-m f g)

[+]-map-cong : ∀ {A A' B B' : obj} {f f' : A ⇒ A'} {g g' : B ⇒ B'} → f ≈ f' → g ≈ g' → [+]-map f g ≈ [+]-map f' g'
[+]-map-cong e₁ e₂ = coprod-m-cong (Lf-map-cong e₁) (Lf-map-cong e₂)

[+]-map-comp : ∀ {A A' A'' B B' B'' : obj} (f' : A' ⇒ A'') (f : A ⇒ A') (g' : B' ⇒ B'') (g : B ⇒ B') →
               ([+]-map f' g' ∘ [+]-map f g) ≈ [+]-map (f' ∘ f) (g' ∘ g)
[+]-map-comp f' f g' g = ≈-trans (≈-sym (coprod-m-comp _ _ _ _)) (coprod-m-cong (≈-sym (Lf-map-comp _ _)) (≈-sym (Lf-map-comp _ _)))

[+]-map-id : ∀ {A B : obj} → [+]-map (id A) (id B) ≈ id _
[+]-map-id = ≈-trans (coprod-m-cong Lf-map-id Lf-map-id) coprod-m-id

[+]-square : ∀ {A A' A'' A''' B B' B'' B''' : obj}
             {f : A ⇒ A'} {h : A' ⇒ A''} {h' : A ⇒ A'''} {f' : A''' ⇒ A''}
             {g : B ⇒ B'} {l : B' ⇒ B''} {l' : B ⇒ B'''} {g' : B''' ⇒ B''} →
             (h ∘ f) ≈ (f' ∘ h') → (l ∘ g) ≈ (g' ∘ l') → ([+]-map h l ∘ [+]-map f g) ≈ ([+]-map f' g' ∘ [+]-map h' l')
[+]-square e₁ e₂ = ≈-trans ([+]-map-comp _ _ _ _) (≈-trans ([+]-map-cong e₁ e₂) (≈-sym ([+]-map-comp _ _ _ _)))

[+]-inv : ∀ {A A' B B' : obj} {f : A ⇒ A'} {f' : A' ⇒ A} {g : B ⇒ B'} {g' : B' ⇒ B} →
          (f ∘ f') ≈ id _ → (g ∘ g') ≈ id _ → ([+]-map f g ∘ [+]-map f' g') ≈ id _
[+]-inv e₁ e₂ = ≈-trans ([+]-map-comp _ _ _ _) (≈-trans ([+]-map-cong e₁ e₂) [+]-map-id)

[+]-map-inj₁ : ∀ {A A' B B' : obj} (f : A ⇒ A') (g : B ⇒ B') →
               ([+]-map f g ∘ (in₁ ∘ injF)) ≈ ((in₁ ∘ injF) ∘ f)
[+]-map-inj₁ f g =
  ≈-trans (≈-sym (assoc _ _ _))
  (≈-trans (∘-cong (copair-in₁ _ _) ≈-refl)
  (≈-trans (assoc _ _ _)
  (≈-trans (∘-cong ≈-refl (injF-natural f)) (≈-sym (assoc _ _ _)))))

[+]-map-inj₂ : ∀ {A A' B B' : obj} (f : A ⇒ A') (g : B ⇒ B') →
               ([+]-map f g ∘ (in₂ ∘ injF)) ≈ ((in₂ ∘ injF) ∘ g)
[+]-map-inj₂ f g =
  ≈-trans (≈-sym (assoc _ _ _))
  (≈-trans (∘-cong (copair-in₂ _ _) ≈-refl)
  (≈-trans (assoc _ _ _)
  (≈-trans (∘-cong ≈-refl (injF-natural g)) (≈-sym (assoc _ _ _)))))

[×]-map-cong : ∀ {A A' B B' : obj} {f f' : A ⇒ A'} {g g' : B ⇒ B'} → f ≈ f' → g ≈ g' → [×]-map f g ≈ [×]-map f' g'
[×]-map-cong e₁ e₂ = Lf-map-cong (prod-m-cong e₁ e₂)

[×]-map-comp : ∀ {A A' A'' B B' B'' : obj} (f' : A' ⇒ A'') (f : A ⇒ A') (g' : B' ⇒ B'') (g : B ⇒ B') →
               ([×]-map f' g' ∘ [×]-map f g) ≈ [×]-map (f' ∘ f) (g' ∘ g)
[×]-map-comp f' f g' g = ≈-trans (≈-sym (Lf-map-comp _ _)) (Lf-map-cong (≈-sym (prod-m-comp _ _ _ _)))

[×]-map-id : ∀ {A B : obj} → [×]-map (id A) (id B) ≈ id _
[×]-map-id = ≈-trans (Lf-map-cong prod-m-id) Lf-map-id

[×]-square : ∀ {A A' A'' A''' B B' B'' B''' : obj}
             {f : A ⇒ A'} {h : A' ⇒ A''} {h' : A ⇒ A'''} {f' : A''' ⇒ A''}
             {g : B ⇒ B'} {l : B' ⇒ B''} {l' : B ⇒ B'''} {g' : B''' ⇒ B''} →
             (h ∘ f) ≈ (f' ∘ h') → (l ∘ g) ≈ (g' ∘ l') → ([×]-map h l ∘ [×]-map f g) ≈ ([×]-map f' g' ∘ [×]-map h' l')
[×]-square e₁ e₂ = ≈-trans ([×]-map-comp _ _ _ _) (≈-trans ([×]-map-cong e₁ e₂) (≈-sym ([×]-map-comp _ _ _ _)))

[×]-inv : ∀ {A A' B B' : obj} {f : A ⇒ A'} {f' : A' ⇒ A} {g : B ⇒ B'} {g' : B' ⇒ B} →
          (f ∘ f') ≈ id _ → (g ∘ g') ≈ id _ → ([×]-map f g ∘ [×]-map f' g') ≈ id _
[×]-inv e₁ e₂ = ≈-trans ([×]-map-comp _ _ _ _) (≈-trans ([×]-map-cong e₁ e₂) [×]-map-id)

fmor-[+] : ∀ {k} (P Q : Poly R.cat k) {δ δ' : Fin k → obj} (fs : ∀ i → δ i ⇒ δ' i) →
           fmor (P Poly.+ Q) fs ≈ [+]-map (fmor P fs) (fmor Q fs)
fmor-[+] P Q fs = ≈-trans (fmor-+ P Q fs) (≈-sym (coprod-m-strong _ _))

fmor-[×] : ∀ {k} (P Q : Poly R.cat k) {δ δ' : Fin k → obj} (fs : ∀ i → δ i ⇒ δ' i) →
           fmor (P Poly.× Q) fs ≈ [×]-map (fmor P fs) (fmor Q fs)
fmor-[×] = fmor-×

as-poly-var-map : ∀ {Δ n} {δ δ' : Fin Δ → obj} → (∀ i → δ i ⇒ δ' i) → (δ₀ : Fin n → obj) →
                  (s : Fin n ⊎ Fin Δ) →
                  fobj μ-obj ([ Poly.var , (λ j → Poly.const (δ j)) ] s) δ₀ ⇒
                    fobj μ-obj ([ Poly.var , (λ j → Poly.const (δ' j)) ] s) δ₀
as-poly-var-map gs δ₀ (inj₁ j) = id _
as-poly-var-map gs δ₀ (inj₂ k) = gs k

as-poly-map : ∀ {Δ n} (τ : type (n + Δ)) {δ δ' : Fin Δ → obj} → (∀ i → δ i ⇒ δ' i) → (δ₀ : Fin n → obj) →
              fobj μ-obj (as-poly {Δ} {n} τ δ) δ₀ ⇒ fobj μ-obj (as-poly {Δ} {n} τ δ') δ₀
as-poly-map {Δ} {n} (var i) gs δ₀ = as-poly-var-map gs δ₀ (splitAt n i)
as-poly-map unit      gs δ₀ = id _
as-poly-map (base s)  gs δ₀ = id _
as-poly-map (σ [+] τ) gs δ₀ = [+]-map (as-poly-map σ gs δ₀) (as-poly-map τ gs δ₀)
as-poly-map (σ [×] τ) gs δ₀ = [×]-map (as-poly-map σ gs δ₀) (as-poly-map τ gs δ₀)
as-poly-map (σ [→] τ) gs δ₀ = id _
as-poly-map (μ τ) {δ} {δ'} gs δ₀ =
  μ-map (as-poly τ δ) δ₀ (as-poly τ δ') δ₀ (as-poly-map τ gs (extend δ₀ (μ-obj (as-poly τ δ') δ₀)))

as-poly-map-cong : ∀ {Δ n} (τ : type (n + Δ)) {δ δ' : Fin Δ → obj} {gs gs' : ∀ i → δ i ⇒ δ' i} →
                   (∀ i → gs i ≈ gs' i) → (δ₀ : Fin n → obj) → as-poly-map τ gs δ₀ ≈ as-poly-map τ gs' δ₀
as-poly-map-cong {n = n} (var i) es δ₀ with splitAt n i
... | inj₁ j = ≈-refl
... | inj₂ k = es k
as-poly-map-cong unit      es δ₀ = ≈-refl
as-poly-map-cong (base s)  es δ₀ = ≈-refl
as-poly-map-cong (σ [+] τ) es δ₀ = [+]-map-cong (as-poly-map-cong σ es δ₀) (as-poly-map-cong τ es δ₀)
as-poly-map-cong (σ [×] τ) es δ₀ = [×]-map-cong (as-poly-map-cong σ es δ₀) (as-poly-map-cong τ es δ₀)
as-poly-map-cong (σ [→] τ) es δ₀ = ≈-refl
as-poly-map-cong {n = n} (μ τ) es δ₀ = μ-map-cong _ _ _ _ (as-poly-map-cong {n = suc n} τ es _)

as-poly-map-id : ∀ {Δ n} (τ : type (n + Δ)) {δ : Fin Δ → obj} (δ₀ : Fin n → obj) →
                 as-poly-map τ (λ i → id (δ i)) δ₀ ≈ id _
as-poly-map-id {n = n} (var i) δ₀ with splitAt n i
... | inj₁ j = ≈-refl
... | inj₂ k = ≈-refl
as-poly-map-id unit      δ₀ = ≈-refl
as-poly-map-id (base s)  δ₀ = ≈-refl
as-poly-map-id (σ [+] τ) δ₀ = ≈-trans ([+]-map-cong (as-poly-map-id σ δ₀) (as-poly-map-id τ δ₀)) [+]-map-id
as-poly-map-id (σ [×] τ) δ₀ = ≈-trans ([×]-map-cong (as-poly-map-id σ δ₀) (as-poly-map-id τ δ₀)) [×]-map-id
as-poly-map-id (σ [→] τ) δ₀ = ≈-refl
as-poly-map-id {n = n} (μ τ) δ₀ = ≈-trans (μ-map-cong _ _ _ _ (as-poly-map-id {n = suc n} τ _)) (μ-map-id _ _)

strong-as-poly-var-map : ∀ {Δ n} {Γ' : Obj} {δ δ' : Fin Δ → obj} → (∀ i → prod Γ' (δ i) ⇒ δ' i) →
                         (δ₀ : Fin n → obj) → (s : Fin n ⊎ Fin Δ) →
                         prod Γ' (fobj μ-obj ([ Poly.var , (λ j → Poly.const (δ j)) ] s) δ₀) ⇒
                           fobj μ-obj ([ Poly.var , (λ j → Poly.const (δ' j)) ] s) δ₀
strong-as-poly-var-map hs δ₀ (inj₁ j) = p₂
strong-as-poly-var-map hs δ₀ (inj₂ k) = hs k

strong-as-poly-map : ∀ {Δ n} (τ : type (n + Δ)) {Γ' : Obj} {δ δ' : Fin Δ → obj} →
                     (∀ i → prod Γ' (δ i) ⇒ δ' i) → (δ₀ : Fin n → obj) →
                     prod Γ' (fobj μ-obj (as-poly {Δ} {n} τ δ) δ₀) ⇒ fobj μ-obj (as-poly {Δ} {n} τ δ') δ₀
strong-as-poly-map {Δ} {n} (var i) hs δ₀ = strong-as-poly-var-map hs δ₀ (splitAt n i)
strong-as-poly-map unit      hs δ₀ = p₂
strong-as-poly-map (base s)  hs δ₀ = p₂
strong-as-poly-map (σ [+] τ) hs δ₀ =
  scopair (in₁ ∘ strong-Lf-map (strong-as-poly-map σ hs δ₀))
          (in₂ ∘ strong-Lf-map (strong-as-poly-map τ hs δ₀))
strong-as-poly-map (σ [×] τ) hs δ₀ =
  strong-Lf-map (strong-prod-m (strong-as-poly-map σ hs δ₀) (strong-as-poly-map τ hs δ₀))
strong-as-poly-map (σ [→] τ) hs δ₀ = p₂
strong-as-poly-map (μ τ) {δ' = δ'} hs δ₀ =
  ⦅ inMap (as-poly τ δ') δ₀ ∘ strong-as-poly-map τ hs (extend δ₀ (μ-obj (as-poly τ δ') δ₀)) ⦆

strong-as-poly-map-cong : ∀ {Δ n} (τ : type (n + Δ)) {Γ' : Obj} {δ δ' : Fin Δ → obj}
                          {hs hs' : ∀ i → prod Γ' (δ i) ⇒ δ' i} →
                          (∀ i → hs i ≈ hs' i) → (δ₀ : Fin n → obj) →
                          strong-as-poly-map τ hs δ₀ ≈ strong-as-poly-map τ hs' δ₀
strong-as-poly-map-cong {n = n} (var i) es δ₀ with splitAt n i
... | inj₁ j = ≈-refl
... | inj₂ k = es k
strong-as-poly-map-cong unit      es δ₀ = ≈-refl
strong-as-poly-map-cong (base s)  es δ₀ = ≈-refl
strong-as-poly-map-cong (σ [+] τ) es δ₀ =
  scopair-cong (∘-cong ≈-refl (strong-Lf-map-cong (strong-as-poly-map-cong σ es δ₀)))
               (∘-cong ≈-refl (strong-Lf-map-cong (strong-as-poly-map-cong τ es δ₀)))
strong-as-poly-map-cong (σ [×] τ) es δ₀ =
  strong-Lf-map-cong (strong-prod-m-cong (strong-as-poly-map-cong σ es δ₀) (strong-as-poly-map-cong τ es δ₀))
strong-as-poly-map-cong (σ [→] τ) es δ₀ = ≈-refl
strong-as-poly-map-cong {n = n} (μ τ) es δ₀ =
  ⦅⦆-cong _ _ (∘-cong ≈-refl (strong-as-poly-map-cong {n = suc n} τ es _))

strong-as-poly-map-natural : ∀ {Δ n} (τ : type (n + Δ)) {Γ' : Obj} {δ δ' : Fin Δ → obj}
  (hs : ∀ i → prod Γ' (δ i) ⇒ δ' i) {δ₀ δ₀' : Fin n → obj} (fs : ∀ i → prod Γ' (δ₀ i) ⇒ δ₀' i) →
  (strong-fmor (as-poly {Δ} {n} τ δ') fs ∘co strong-as-poly-map τ hs δ₀)
    ≈ (strong-as-poly-map τ hs δ₀' ∘co strong-fmor (as-poly {Δ} {n} τ δ) fs)
strong-as-poly-map-natural {Δ} {n} (var i) hs fs with splitAt n i
... | inj₁ j = ≈-trans (≈-trans (∘-cong ≈-refl pair-ext0) id-right) (≈-sym (pair-p₂ _ _))
... | inj₂ k = ≈-trans (pair-p₂ _ _) (≈-sym (≈-trans (∘-cong ≈-refl pair-ext0) id-right))
strong-as-poly-map-natural unit      hs fs = ≈-refl
strong-as-poly-map-natural (base s)  hs fs = ≈-refl
strong-as-poly-map-natural (σ [+] τ) hs fs =
  ≈-trans (copair-comp _ _ _ _)
  (≈-trans (scopair-cong
      (∘-cong ≈-refl (≈-trans (strong-Lf-map-comp _ _)
                        (strong-Lf-map-cong (strong-as-poly-map-natural σ hs fs))))
      (∘-cong ≈-refl (≈-trans (strong-Lf-map-comp _ _)
                        (strong-Lf-map-cong (strong-as-poly-map-natural τ hs fs)))))
    (≈-sym (≈-trans (copair-comp _ _ _ _)
      (scopair-cong (∘-cong ≈-refl (strong-Lf-map-comp _ _))
                    (∘-cong ≈-refl (strong-Lf-map-comp _ _))))))
strong-as-poly-map-natural (σ [×] τ) hs fs =
  ≈-trans (strong-Lf-map-comp _ _)
  (≈-trans (strong-Lf-map-cong (≈-trans (strong-prod-m-comp _ _ _ _)
     (≈-trans (strong-prod-m-cong (strong-as-poly-map-natural σ hs fs)
                                  (strong-as-poly-map-natural τ hs fs))
       (≈-sym (strong-prod-m-comp _ _ _ _)))))
    (≈-sym (strong-Lf-map-comp _ _)))
strong-as-poly-map-natural (σ [→] τ) hs fs = ≈-refl
strong-as-poly-map-natural {Δ} {n} (μ τ) {Γ'} {δ} {δ'} hs {δ₀} {δ₀'} fs =
  ≈-trans (fusion {P = P} {δ = δ₀} algA alg⋆ SFμ' prem₁)
          (≈-sym (fusion {P = P} {δ = δ₀} algF alg⋆ SAμ' prem₂))
  where
  P : Poly R.cat (suc n)
  P = as-poly {Δ} {suc n} τ δ
  Q : Poly R.cat (suc n)
  Q = as-poly {Δ} {suc n} τ δ'
  M₀  = μ-obj Q δ₀
  M₀' = μ-obj Q δ₀'
  N₀' = μ-obj P δ₀'
  SFbQ : prod Γ' (fobj μ-obj Q (extend δ₀ M₀')) ⇒ fobj μ-obj Q (extend δ₀' M₀')
  SFbQ = strong-fmor Q (strong-extend-mor fs p₂)
  SFbP : prod Γ' (fobj μ-obj P (extend δ₀ N₀')) ⇒ fobj μ-obj P (extend δ₀' N₀')
  SFbP = strong-fmor P (strong-extend-mor fs p₂)
  SFPfs : prod Γ' (fobj μ-obj P (extend δ₀ M₀')) ⇒ fobj μ-obj P (extend δ₀' M₀')
  SFPfs = strong-fmor P (strong-extend-mor fs p₂)
  SAB₀ = strong-as-poly-map τ hs (extend δ₀ M₀)
  SAB₁ = strong-as-poly-map τ hs (extend δ₀ M₀')
  SAB' = strong-as-poly-map τ hs (extend δ₀' M₀')
  SFμ' : prod Γ' (μ-obj Q δ₀) ⇒ M₀'
  SFμ' = ⦅ inMap Q δ₀' ∘ SFbQ ⦆
  SAμ' : prod Γ' (μ-obj P δ₀') ⇒ M₀'
  SAμ' = ⦅ inMap Q δ₀' ∘ SAB' ⦆
  algA = inMap Q δ₀ ∘ SAB₀
  algF = inMap P δ₀' ∘ SFbP
  alg⋆ : prod Γ' (fobj μ-obj P (extend δ₀ M₀')) ⇒ M₀'
  alg⋆ = inMap Q δ₀' ∘ (SAB' ∘co SFPfs)

  prem₁ : (SFμ' ∘co algA) ≈ (alg⋆ ∘co strong-fmor P (strong-extend-mor (λ i → p₂) SFμ'))
  prem₁ = begin
      SFμ' ∘co (inMap Q δ₀ ∘ SAB₀)
    ≈˘⟨ ∘co-push SFμ' (inMap Q δ₀) SAB₀ ⟩
      (SFμ' ∘co (inMap Q δ₀ ∘ p₂)) ∘co SAB₀
    ≈⟨ CoK.∘-cong (⦅⦆-β {P = Q} {δ = δ₀} (inMap Q δ₀' ∘ SFbQ)) ≈-refl ⟩
      ((inMap Q δ₀' ∘ SFbQ) ∘co strong-fmor Q (strong-extend-mor (λ i → p₂) SFμ')) ∘co SAB₀
    ≈⟨ CoK.assoc _ _ _ ⟩
      (inMap Q δ₀' ∘ SFbQ) ∘co (strong-fmor Q (strong-extend-mor (λ i → p₂) SFμ') ∘co SAB₀)
    ≈⟨ CoK.∘-cong ≈-refl (strong-as-poly-map-natural {n = suc n} τ hs (strong-extend-mor (λ i → p₂) SFμ')) ⟩
      (inMap Q δ₀' ∘ SFbQ) ∘co (SAB₁ ∘co strong-fmor P (strong-extend-mor (λ i → p₂) SFμ'))
    ≈˘⟨ CoK.assoc _ _ _ ⟩
      ((inMap Q δ₀' ∘ SFbQ) ∘co SAB₁) ∘co strong-fmor P (strong-extend-mor (λ i → p₂) SFμ')
    ≈⟨ CoK.∘-cong (≈-trans (assoc _ _ _)
         (∘-cong ≈-refl (strong-as-poly-map-natural {n = suc n} τ hs (strong-extend-mor fs p₂)))) ≈-refl ⟩
      (inMap Q δ₀' ∘ (SAB' ∘co SFPfs)) ∘co strong-fmor P (strong-extend-mor (λ i → p₂) SFμ')
    ∎
    where open ≈-Reasoning isEquiv

  prem₂ : (SAμ' ∘co algF) ≈ (alg⋆ ∘co strong-fmor P (strong-extend-mor (λ i → p₂) SAμ'))
  prem₂ = begin
      SAμ' ∘co (inMap P δ₀' ∘ SFbP)
    ≈˘⟨ ∘co-push SAμ' (inMap P δ₀') SFbP ⟩
      (SAμ' ∘co (inMap P δ₀' ∘ p₂)) ∘co SFbP
    ≈⟨ CoK.∘-cong (⦅⦆-β {P = P} {δ = δ₀'} (inMap Q δ₀' ∘ SAB')) ≈-refl ⟩
      ((inMap Q δ₀' ∘ SAB') ∘co strong-fmor P (strong-extend-mor (λ i → p₂) SAμ')) ∘co SFbP
    ≈⟨ CoK.assoc _ _ _ ⟩
      (inMap Q δ₀' ∘ SAB') ∘co (strong-fmor P (strong-extend-mor (λ i → p₂) SAμ') ∘co SFbP)
    ≈⟨ CoK.∘-cong ≈-refl (≈-trans (strong-fmor-comp P _ _)
         (strong-fmor-cong P (strong-extend-mor-comp (λ i → CoK.id-left) CoK.id-right))) ⟩
      (inMap Q δ₀' ∘ SAB') ∘co strong-fmor P (strong-extend-mor fs SAμ')
    ≈⟨ assoc _ _ _ ⟩
      inMap Q δ₀' ∘ (SAB' ∘co strong-fmor P (strong-extend-mor fs SAμ'))
    ≈˘⟨ ∘-cong ≈-refl (CoK.∘-cong ≈-refl (≈-trans (strong-fmor-comp P _ _)
          (strong-fmor-cong P (strong-extend-mor-comp (λ i → CoK.id-right) CoK.id-left)))) ⟩
      inMap Q δ₀' ∘ (SAB' ∘co (SFPfs ∘co strong-fmor P (strong-extend-mor (λ i → p₂) SAμ')))
    ≈˘⟨ ∘-cong ≈-refl (CoK.assoc _ _ _) ⟩
      inMap Q δ₀' ∘ ((SAB' ∘co SFPfs) ∘co strong-fmor P (strong-extend-mor (λ i → p₂) SAμ'))
    ≈˘⟨ assoc _ _ _ ⟩
      (inMap Q δ₀' ∘ (SAB' ∘co SFPfs)) ∘co strong-fmor P (strong-extend-mor (λ i → p₂) SAμ')
    ∎
    where open ≈-Reasoning isEquiv

preserves-as-poly-var-map : ∀ {Δ n} {δ δ' : Fin Δ → obj} {gs : ∀ i → δ i ⇒ δ' i}
  {δc : ∀ i → Section (δ i)} {δ'c : ∀ i → Section (δ' i)} →
  (∀ i → preserves-section (gs i) (δc i) (δ'c i)) →
  (δ₀ : Fin n → obj) (δ₀c : ∀ i → Section (δ₀ i)) (s : Fin n ⊎ Fin Δ) →
  preserves-section (as-poly-var-map gs δ₀ s)
    (poly-section ([_,_] {C = λ _ → Poly R.cat n} Poly.var (λ j → Poly.const (δ j)) s)
      (as-poly-var-section δ δc s) δ₀c)
    (poly-section ([_,_] {C = λ _ → Poly R.cat n} Poly.var (λ j → Poly.const (δ' j)) s)
      (as-poly-var-section δ' δ'c s) δ₀c)
preserves-as-poly-var-map hgs δ₀ δ₀c (inj₁ j) = preserves-section-id (δ₀c j)
preserves-as-poly-var-map hgs δ₀ δ₀c (inj₂ k) = hgs k

preserves-as-poly-map : ∀ {Δ n} (τ : type (n + Δ)) {δ δ' : Fin Δ → obj}
  {gs : ∀ i → δ i ⇒ δ' i} {δc : ∀ i → Section (δ i)} {δ'c : ∀ i → Section (δ' i)} →
  (∀ i → preserves-section (gs i) (δc i) (δ'c i)) →
  (δ₀ : Fin n → obj) (δ₀c : ∀ i → Section (δ₀ i)) →
  preserves-section (as-poly-map τ gs δ₀)
    (poly-section (as-poly τ δ) (as-poly-section τ δ δc) δ₀c)
    (poly-section (as-poly τ δ') (as-poly-section τ δ' δ'c) δ₀c)
preserves-as-poly-map {n = n} (var i) {gs = gs} {δc} {δ'c} hgs δ₀ δ₀c =
  preserves-as-poly-var-map {gs = gs} {δc} {δ'c} hgs δ₀ δ₀c (splitAt n i)
preserves-as-poly-map unit      hgs δ₀ δ₀c = preserves-section-id 𝟙ty-section
preserves-as-poly-map (base s)  hgs δ₀ δ₀c = preserves-section-id (sort-section s)
preserves-as-poly-map (σ [+] τ) {δ} {δ'} {gs} {δc} {δ'c} hgs δ₀ δ₀c =
  preserves-coprod-m
    (preserves-Lf-map {c = sσ} {d = sσ'} (preserves-as-poly-map σ hgs δ₀ δ₀c))
    (preserves-Lf-map {c = sτ} {d = sτ'} (preserves-as-poly-map τ hgs δ₀ δ₀c))
  where
  sσ  = poly-section (as-poly σ δ)  (as-poly-section σ δ δc)   δ₀c
  sσ' = poly-section (as-poly σ δ') (as-poly-section σ δ' δ'c) δ₀c
  sτ  = poly-section (as-poly τ δ)  (as-poly-section τ δ δc)   δ₀c
  sτ' = poly-section (as-poly τ δ') (as-poly-section τ δ' δ'c) δ₀c
preserves-as-poly-map (σ [×] τ) {δ} {δ'} {gs} {δc} {δ'c} hgs δ₀ δ₀c =
  preserves-Lf-map {c = prod-section sσ sτ} {d = prod-section sσ' sτ'}
    (preserves-prod-m (preserves-as-poly-map σ hgs δ₀ δ₀c)
                      (preserves-as-poly-map τ hgs δ₀ δ₀c))
  where
  sσ  = poly-section (as-poly σ δ)  (as-poly-section σ δ δc)   δ₀c
  sσ' = poly-section (as-poly σ δ') (as-poly-section σ δ' δ'c) δ₀c
  sτ  = poly-section (as-poly τ δ)  (as-poly-section τ δ δc)   δ₀c
  sτ' = poly-section (as-poly τ δ') (as-poly-section τ δ' δ'c) δ₀c
preserves-as-poly-map (σ [→] τ) hgs δ₀ δ₀c = preserves-section-id (Lf-section exp-section)
preserves-as-poly-map {n = n} (μ τ) {δ} {δ'} {gs} {δc} {δ'c} hgs δ₀ δ₀c =
  preserves-μ-map (as-poly τ δ) δ₀ (as-poly τ δ') δ₀ δ₀c δ₀c
    (as-poly-section τ δ δc) (as-poly-section τ δ' δ'c)
    (as-poly-map τ gs (extend δ₀ (μ-obj (as-poly τ δ') δ₀)))
    (preserves-as-poly-map {n = suc n} τ hgs (extend δ₀ (μ-obj (as-poly τ δ') δ₀))
      (extend-section δ₀c
        (poly-section (as-poly (μ τ) δ') (as-poly-section (μ τ) δ' δ'c) δ₀c)))

fmor-extend-swap : ∀ {k} (P : Poly R.cat (suc k)) {δ δ' : Fin k → obj} (fs : ∀ i → δ i ⇒ δ' i) {X Y : obj} (h : X ⇒ Y) →
                   (fmor P (extend-mor (λ i → id _) h) ∘ fmor P (extend-mor fs (id _)))
                     ≈ (fmor P (extend-mor fs (id _)) ∘ fmor P (extend-mor (λ i → id _) h))
fmor-extend-swap P fs h =
  ≈-trans (fmor-comp P _ _)
          (≈-trans (fmor-cong P (λ { Fin.zero → ≈-trans id-right (≈-sym id-left) ; (Fin.suc i) → ≈-trans id-left (≈-sym id-right) }))
                   (≈-sym (fmor-comp P _ _)))

mutual
  as-poly-map-comp : ∀ {Δ n} (τ : type (n + Δ)) {δ δ' δ'' : Fin Δ → obj}
                     (gs' : ∀ i → δ' i ⇒ δ'' i) (gs : ∀ i → δ i ⇒ δ' i) (δ₀ : Fin n → obj) →
                     (as-poly-map τ gs' δ₀ ∘ as-poly-map τ gs δ₀) ≈ as-poly-map τ (λ i → gs' i ∘ gs i) δ₀
  as-poly-map-comp {n = n} (var i) gs' gs δ₀ with splitAt n i
  ... | inj₁ j = id-left
  ... | inj₂ k = ≈-refl
  as-poly-map-comp unit      gs' gs δ₀ = id-left
  as-poly-map-comp (base s)  gs' gs δ₀ = id-left
  as-poly-map-comp (σ [+] τ) gs' gs δ₀ =
    ≈-trans ([+]-map-comp _ _ _ _) ([+]-map-cong (as-poly-map-comp σ gs' gs δ₀) (as-poly-map-comp τ gs' gs δ₀))
  as-poly-map-comp (σ [×] τ) gs' gs δ₀ =
    ≈-trans ([×]-map-comp _ _ _ _) ([×]-map-cong (as-poly-map-comp σ gs' gs δ₀) (as-poly-map-comp τ gs' gs δ₀))
  as-poly-map-comp (σ [→] τ) gs' gs δ₀ = id-left
  as-poly-map-comp {n = n} (μ τ) {δ} {δ'} {δ''} gs' gs δ₀ =
    ≈-trans (μ-map-comp (as-poly τ δ) δ₀ (as-poly τ δ') δ₀ (as-poly τ δ'') δ₀
                        (as-poly-map τ gs (extend δ₀ M')) (as-poly-map τ gs' (extend δ₀ M'')) (as-poly-map τ gs (extend δ₀ M''))
                        (as-poly-map-natural {n = suc n} τ gs (extend-mor (λ i → id _) k)))
            (μ-map-cong _ _ _ _ (as-poly-map-comp {n = suc n} τ gs' gs _))
    where
      M'  = μ-obj (as-poly τ δ') δ₀
      M'' = μ-obj (as-poly τ δ'') δ₀
      k   = μ-map (as-poly τ δ') δ₀ (as-poly τ δ'') δ₀ (as-poly-map τ gs' (extend δ₀ M''))

  as-poly-map-natural : ∀ {Δ n} (τ : type (n + Δ)) {δ δ' : Fin Δ → obj} (gs : ∀ i → δ i ⇒ δ' i)
                        {δ₀ δ₀' : Fin n → obj} (fs : ∀ i → δ₀ i ⇒ δ₀' i) →
                        (fmor (as-poly τ δ') fs ∘ as-poly-map τ gs δ₀) ≈ (as-poly-map τ gs δ₀' ∘ fmor (as-poly τ δ) fs)
  as-poly-map-natural {n = n} (var i) gs fs with splitAt n i
  ... | inj₁ j = ≈-sym id-swap
  ... | inj₂ k = ≈-trans (∘-cong (fmor-const fs) ≈-refl) (≈-trans id-left (≈-trans (≈-sym id-right) (∘-cong ≈-refl (≈-sym (fmor-const fs)))))
  as-poly-map-natural unit      gs fs = ≈-sym id-swap
  as-poly-map-natural (base s)  gs fs = ≈-sym id-swap
  as-poly-map-natural (σ [+] τ) {δ} {δ'} gs fs =
    ≈-trans (∘-cong (fmor-[+] (as-poly σ δ') (as-poly τ δ') fs) ≈-refl)
            (≈-trans ([+]-square (as-poly-map-natural σ gs fs) (as-poly-map-natural τ gs fs))
                     (∘-cong ≈-refl (≈-sym (fmor-[+] (as-poly σ δ) (as-poly τ δ) fs))))
  as-poly-map-natural (σ [×] τ) {δ} {δ'} gs fs =
    ≈-trans (∘-cong (fmor-[×] (as-poly σ δ') (as-poly τ δ') fs) ≈-refl)
            (≈-trans ([×]-square (as-poly-map-natural σ gs fs) (as-poly-map-natural τ gs fs))
                     (∘-cong ≈-refl (≈-sym (fmor-[×] (as-poly σ δ) (as-poly τ δ) fs))))
  as-poly-map-natural (σ [→] τ) gs fs = ≈-sym id-swap
  as-poly-map-natural {n = n} (μ τ) {δ} {δ'} gs {δ₀} {δ₀'} fs = begin
      fmor (Poly.μ (as-poly τ δ')) fs ∘ μ-map (as-poly τ δ) δ₀ (as-poly τ δ') δ₀ (as-poly-map τ gs (extend δ₀ M'))
    ≈⟨ ∘-cong (fmor-μ _ fs) ≈-refl ⟩
      μ-map (as-poly τ δ') δ₀ (as-poly τ δ') δ₀' (fmor (as-poly τ δ') (extend-mor fs (id _)))
        ∘ μ-map (as-poly τ δ) δ₀ (as-poly τ δ') δ₀ (as-poly-map τ gs (extend δ₀ M'))
    ≈⟨ μ-map-comp (as-poly τ δ) δ₀ (as-poly τ δ') δ₀ (as-poly τ δ') δ₀'
                  (as-poly-map τ gs (extend δ₀ M')) (fmor (as-poly τ δ') (extend-mor fs (id _))) (as-poly-map τ gs (extend δ₀ N'))
                  (as-poly-map-natural {n = suc n} τ gs (extend-mor (λ i → id _) (μ-map (as-poly τ δ') δ₀ (as-poly τ δ') δ₀' (fmor (as-poly τ δ') (extend-mor fs (id _)))))) ⟩
      μ-map (as-poly τ δ) δ₀ (as-poly τ δ') δ₀' (fmor (as-poly τ δ') (extend-mor fs (id _)) ∘ as-poly-map τ gs (extend δ₀ N'))
    ≈⟨ μ-map-cong _ _ _ _ (as-poly-map-natural {n = suc n} τ gs (extend-mor fs (id _))) ⟩
      μ-map (as-poly τ δ) δ₀ (as-poly τ δ') δ₀' (as-poly-map τ gs (extend δ₀' N') ∘ fmor (as-poly τ δ) (extend-mor fs (id _)))
    ≈˘⟨ μ-map-comp (as-poly τ δ) δ₀ (as-poly τ δ) δ₀' (as-poly τ δ') δ₀'
                   (fmor (as-poly τ δ) (extend-mor fs (id _))) (as-poly-map τ gs (extend δ₀' N')) (fmor (as-poly τ δ) (extend-mor fs (id _)))
                   (fmor-extend-swap (as-poly τ δ) fs _) ⟩
      μ-map (as-poly τ δ) δ₀' (as-poly τ δ') δ₀' (as-poly-map τ gs (extend δ₀' N'))
        ∘ μ-map (as-poly τ δ) δ₀ (as-poly τ δ) δ₀' (fmor (as-poly τ δ) (extend-mor fs (id _)))
    ≈˘⟨ ∘-cong ≈-refl (fmor-μ _ fs) ⟩
      as-poly-map (μ τ) gs δ₀' ∘ fmor (Poly.μ (as-poly τ δ)) fs
    ∎
    where
      open ≈-Reasoning isEquiv
      M' = μ-obj (as-poly τ δ') δ₀
      N' = μ-obj (as-poly τ δ') δ₀'

cast : ∀ {n} {P P' : Poly R.cat n} → P ≡ P' → (δ₀ : Fin n → obj) → fobj μ-obj P δ₀ ⇒ fobj μ-obj P' δ₀
cast e δ₀ = ≡-to-⇒ (cong (λ P → fobj μ-obj P δ₀) e)

cast-natural : ∀ {n} {P P' : Poly R.cat n} (e : P ≡ P') {δ₀ δ₀' : Fin n → obj} (fs : ∀ i → δ₀ i ⇒ δ₀' i) →
               (fmor P' fs ∘ cast e δ₀) ≈ (cast e δ₀' ∘ fmor P fs)
cast-natural refl fs = ≈-trans id-right (≈-sym id-left)

cast-+ : ∀ {n} {P P' Q Q' : Poly R.cat n} (e₁ : P ≡ P') (e₂ : Q ≡ Q') (δ₀ : Fin n → obj) →
         cast (cong₂ Poly._+_ e₁ e₂) δ₀ ≈ [+]-map (cast e₁ δ₀) (cast e₂ δ₀)
cast-+ refl refl δ₀ = ≈-sym [+]-map-id

cast-× : ∀ {n} {P P' Q Q' : Poly R.cat n} (e₁ : P ≡ P') (e₂ : Q ≡ Q') (δ₀ : Fin n → obj) →
         cast (cong₂ Poly._×_ e₁ e₂) δ₀ ≈ [×]-map (cast e₁ δ₀) (cast e₂ δ₀)
cast-× refl refl δ₀ = ≈-sym [×]-map-id

cast-μ : ∀ {n} {P P' : Poly R.cat (suc n)} (e : P ≡ P') (δ₀ : Fin n → obj) →
         cast (cong Poly.μ e) δ₀ ≈ μ-map P δ₀ P' δ₀ (cast e (extend δ₀ (μ-obj P' δ₀)))
cast-μ refl δ₀ = ≈-sym (μ-map-id _ _)

cast-irr : ∀ {n} {P Q : Poly R.cat n} (e e' : P ≡ Q) (δ₀ : Fin n → obj) → cast e δ₀ ≈ cast e' δ₀
cast-irr refl refl δ₀ = ≈-refl

as-poly-ren-var : ∀ {Δ₁ Δ₂ n} (ρ : TyRen Δ₁ Δ₂) (δ : Fin Δ₂ → obj)
  (s : Fin n ⊎ Fin Δ₁) (s' : Fin n ⊎ Fin Δ₂) → s' ≡ [ inj₁ , (λ k → inj₂ (ρ k)) ] s →
  [_,_] {C = λ _ → Poly R.cat n} Poly.var (λ j → Poly.const (δ j)) s'
    ≡ [_,_] {C = λ _ → Poly R.cat n} Poly.var (λ j → Poly.const (δ (ρ j))) s
as-poly-ren-var ρ δ (inj₁ j) _ refl = refl
as-poly-ren-var ρ δ (inj₂ k) _ refl = refl

preserves-as-poly-ren-var : ∀ {Δ₁ Δ₂ n} (ρ : TyRen Δ₁ Δ₂) {δ : Fin Δ₂ → obj}
  (δc : ∀ i → Section (δ i)) {δ₀ : Fin n → obj} (δ₀c : ∀ i → Section (δ₀ i))
  (s : Fin n ⊎ Fin Δ₁) (s' : Fin n ⊎ Fin Δ₂) (eq : s' ≡ [ inj₁ , (λ k → inj₂ (ρ k)) ] s) →
  preserves-section (cast (as-poly-ren-var ρ δ s s' eq) δ₀)
    (poly-section ([_,_] {C = λ _ → Poly R.cat n} Poly.var (λ j → Poly.const (δ j)) s')
      (as-poly-var-section δ δc s') δ₀c)
    (poly-section ([_,_] {C = λ _ → Poly R.cat n} Poly.var (λ j → Poly.const (δ (ρ j))) s)
      (as-poly-var-section (λ j → δ (ρ j)) (λ j → δc (ρ j)) s) δ₀c)
preserves-as-poly-ren-var ρ δc δ₀c (inj₁ j) _ refl = preserves-section-id (δ₀c j)
preserves-as-poly-ren-var ρ δc δ₀c (inj₂ k) _ refl = preserves-section-id (δc (ρ k))

preserves-as-poly-ren : ∀ {Δ₁ Δ₂ n} (ρ : TyRen Δ₁ Δ₂) (τ : type (n + Δ₁)) {δ : Fin Δ₂ → obj}
  (δc : ∀ i → Section (δ i)) {δ₀ : Fin n → obj} (δ₀c : ∀ i → Section (δ₀ i)) →
  preserves-section (cast (as-poly-ren ρ τ δ) δ₀)
    (poly-section (as-poly (extᵗⁿ n ρ *ᵗ τ) δ) (as-poly-section (extᵗⁿ n ρ *ᵗ τ) δ δc) δ₀c)
    (poly-section (as-poly τ (λ i → δ (ρ i)))
      (as-poly-section τ (λ i → δ (ρ i)) (λ i → δc (ρ i))) δ₀c)
preserves-as-poly-ren {n = n} ρ (var i) {δ} δc {δ₀} δ₀c =
  preserves-section-resp
    (cast-irr (as-poly-ren-var ρ δ (splitAt n i) (splitAt n (extᵗⁿ n ρ i)) (splitAt-extᵗⁿ n ρ i))
              (as-poly-ren ρ (var i) δ) δ₀)
    (preserves-as-poly-ren-var ρ δc δ₀c (splitAt n i) (splitAt n (extᵗⁿ n ρ i))
      (splitAt-extᵗⁿ n ρ i))
preserves-as-poly-ren ρ unit      δc δ₀c = preserves-section-id 𝟙ty-section
preserves-as-poly-ren ρ (base s)  δc δ₀c = preserves-section-id (sort-section s)
preserves-as-poly-ren {n = n} ρ (σ [+] τ) {δ} δc {δ₀} δ₀c =
  preserves-section-resp
    (≈-sym (cast-+ (as-poly-ren ρ σ δ) (as-poly-ren ρ τ δ) δ₀))
    (preserves-coprod-m
      (preserves-Lf-map {c = pσ'} {d = pσ} (preserves-as-poly-ren ρ σ δc δ₀c))
      (preserves-Lf-map {c = pτ'} {d = pτ} (preserves-as-poly-ren ρ τ δc δ₀c)))
  where
  pσ' = poly-section (as-poly (extᵗⁿ n ρ *ᵗ σ) δ) (as-poly-section (extᵗⁿ n ρ *ᵗ σ) δ δc) δ₀c
  pσ  = poly-section (as-poly σ (λ i → δ (ρ i))) (as-poly-section σ (λ i → δ (ρ i)) (λ i → δc (ρ i))) δ₀c
  pτ' = poly-section (as-poly (extᵗⁿ n ρ *ᵗ τ) δ) (as-poly-section (extᵗⁿ n ρ *ᵗ τ) δ δc) δ₀c
  pτ  = poly-section (as-poly τ (λ i → δ (ρ i))) (as-poly-section τ (λ i → δ (ρ i)) (λ i → δc (ρ i))) δ₀c
preserves-as-poly-ren {n = n} ρ (σ [×] τ) {δ} δc {δ₀} δ₀c =
  preserves-section-resp
    (≈-sym (cast-× (as-poly-ren ρ σ δ) (as-poly-ren ρ τ δ) δ₀))
    (preserves-Lf-map {c = prod-section pσ' pτ'} {d = prod-section pσ pτ}
      (preserves-prod-m (preserves-as-poly-ren ρ σ δc δ₀c) (preserves-as-poly-ren ρ τ δc δ₀c)))
  where
  pσ' = poly-section (as-poly (extᵗⁿ n ρ *ᵗ σ) δ) (as-poly-section (extᵗⁿ n ρ *ᵗ σ) δ δc) δ₀c
  pσ  = poly-section (as-poly σ (λ i → δ (ρ i))) (as-poly-section σ (λ i → δ (ρ i)) (λ i → δc (ρ i))) δ₀c
  pτ' = poly-section (as-poly (extᵗⁿ n ρ *ᵗ τ) δ) (as-poly-section (extᵗⁿ n ρ *ᵗ τ) δ δc) δ₀c
  pτ  = poly-section (as-poly τ (λ i → δ (ρ i))) (as-poly-section τ (λ i → δ (ρ i)) (λ i → δc (ρ i))) δ₀c
preserves-as-poly-ren ρ (σ [→] τ) δc δ₀c = preserves-section-id (Lf-section exp-section)
preserves-as-poly-ren {Δ₁} {Δ₂} {n} ρ (μ τ) {δ} δc {δ₀} δ₀c =
  preserves-section-resp
    (≈-sym (cast-μ (as-poly-ren ρ τ δ) δ₀))
    (preserves-μ-map (as-poly (extᵗⁿ (suc n) ρ *ᵗ τ) δ) δ₀ (as-poly τ (λ i → δ (ρ i))) δ₀
      δ₀c δ₀c
      (as-poly-section (extᵗⁿ (suc n) ρ *ᵗ τ) δ δc)
      (as-poly-section τ (λ i → δ (ρ i)) (λ i → δc (ρ i)))
      (cast (as-poly-ren ρ τ δ) (extend δ₀ M))
      (preserves-as-poly-ren ρ τ δc (extend-section δ₀c μM)))
  where
  M  = μ-obj (as-poly {Δ₁} {suc n} τ (λ i → δ (ρ i))) δ₀
  μM = poly-section (as-poly {Δ₁} {n} (μ τ) (λ i → δ (ρ i)))
         (as-poly-section {Δ₁} {n} (μ τ) (λ i → δ (ρ i)) (λ i → δc (ρ i))) δ₀c

as-poly-map-ren : ∀ {Δ₁ Δ₂ n} (ρ : TyRen Δ₁ Δ₂) (τ : type (n + Δ₁)) {δ δ' : Fin Δ₂ → obj} (gs : ∀ i → δ i ⇒ δ' i)
                  (δ₀ : Fin n → obj) →
                  (cast (as-poly-ren ρ τ δ') δ₀ ∘ as-poly-map (extᵗⁿ n ρ *ᵗ τ) gs δ₀)
                    ≈ (as-poly-map τ (λ i → gs (ρ i)) δ₀ ∘ cast (as-poly-ren ρ τ δ) δ₀)
as-poly-map-ren {n = n} ρ (var i) gs δ₀ with splitAt n i | splitAt n (extᵗⁿ n ρ i) | splitAt-extᵗⁿ n ρ i
... | inj₁ j | .(inj₁ j)     | refl = ≈-refl
... | inj₂ k | .(inj₂ (ρ k)) | refl = ≈-trans id-left (≈-sym id-right)
as-poly-map-ren ρ unit      gs δ₀ = ≈-refl
as-poly-map-ren ρ (base s)  gs δ₀ = ≈-refl
as-poly-map-ren ρ (σ [+] τ) {δ} {δ'} gs δ₀ =
  ≈-trans (∘-cong (cast-+ (as-poly-ren ρ σ δ') (as-poly-ren ρ τ δ') δ₀) ≈-refl)
          (≈-trans ([+]-square (as-poly-map-ren ρ σ gs δ₀) (as-poly-map-ren ρ τ gs δ₀))
                   (∘-cong ≈-refl (≈-sym (cast-+ (as-poly-ren ρ σ δ) (as-poly-ren ρ τ δ) δ₀))))
as-poly-map-ren ρ (σ [×] τ) {δ} {δ'} gs δ₀ =
  ≈-trans (∘-cong (cast-× (as-poly-ren ρ σ δ') (as-poly-ren ρ τ δ') δ₀) ≈-refl)
          (≈-trans ([×]-square (as-poly-map-ren ρ σ gs δ₀) (as-poly-map-ren ρ τ gs δ₀))
                   (∘-cong ≈-refl (≈-sym (cast-× (as-poly-ren ρ σ δ) (as-poly-ren ρ τ δ) δ₀))))
as-poly-map-ren ρ (σ [→] τ) gs δ₀ = ≈-refl
as-poly-map-ren {n = n} ρ (μ τ) {δ} {δ'} gs δ₀ = begin
    cast (cong Poly.μ eq') δ₀ ∘ μ-map Ar δ₀ Ar' δ₀ (as-poly-map (extᵗⁿ (suc n) ρ *ᵗ τ) gs (extend δ₀ (μ-obj Ar' δ₀)))
  ≈⟨ ∘-cong (cast-μ eq' δ₀) ≈-refl ⟩
    μ-map Ar' δ₀ A' δ₀ (cast eq' (extend δ₀ (μ-obj A' δ₀))) ∘ μ-map Ar δ₀ Ar' δ₀ (as-poly-map (extᵗⁿ (suc n) ρ *ᵗ τ) gs (extend δ₀ (μ-obj Ar' δ₀)))
  ≈⟨ μ-map-comp Ar δ₀ Ar' δ₀ A' δ₀
                (as-poly-map (extᵗⁿ (suc n) ρ *ᵗ τ) gs (extend δ₀ (μ-obj Ar' δ₀))) (cast eq' (extend δ₀ (μ-obj A' δ₀)))
                (as-poly-map (extᵗⁿ (suc n) ρ *ᵗ τ) gs (extend δ₀ (μ-obj A' δ₀)))
                (as-poly-map-natural {n = suc n} (extᵗⁿ (suc n) ρ *ᵗ τ) gs (extend-mor (λ i → id _) (μ-map Ar' δ₀ A' δ₀ (cast eq' (extend δ₀ (μ-obj A' δ₀)))))) ⟩
    μ-map Ar δ₀ A' δ₀ (cast eq' (extend δ₀ (μ-obj A' δ₀)) ∘ as-poly-map (extᵗⁿ (suc n) ρ *ᵗ τ) gs (extend δ₀ (μ-obj A' δ₀)))
  ≈⟨ μ-map-cong _ _ _ _ (as-poly-map-ren {n = suc n} ρ τ gs _) ⟩
    μ-map Ar δ₀ A' δ₀ (as-poly-map τ (λ i → gs (ρ i)) (extend δ₀ (μ-obj A' δ₀)) ∘ cast eq (extend δ₀ (μ-obj A' δ₀)))
  ≈˘⟨ μ-map-comp Ar δ₀ A δ₀ A' δ₀
                 (cast eq (extend δ₀ (μ-obj A δ₀))) (as-poly-map τ (λ i → gs (ρ i)) (extend δ₀ (μ-obj A' δ₀))) (cast eq (extend δ₀ (μ-obj A' δ₀)))
                 (cast-natural eq _) ⟩
    μ-map A δ₀ A' δ₀ (as-poly-map τ (λ i → gs (ρ i)) (extend δ₀ (μ-obj A' δ₀))) ∘ μ-map Ar δ₀ A δ₀ (cast eq (extend δ₀ (μ-obj A δ₀)))
  ≈˘⟨ ∘-cong ≈-refl (cast-μ eq δ₀) ⟩
    as-poly-map (μ τ) (λ i → gs (ρ i)) δ₀ ∘ cast (cong Poly.μ eq) δ₀
  ∎
  where
    open ≈-Reasoning isEquiv
    Ar  = as-poly (extᵗⁿ (suc n) ρ *ᵗ τ) δ
    Ar' = as-poly (extᵗⁿ (suc n) ρ *ᵗ τ) δ'
    A   = as-poly τ (λ i → δ (ρ i))
    A'  = as-poly τ (λ i → δ' (ρ i))
    eq  = as-poly-ren ρ τ δ
    eq' = as-poly-ren ρ τ δ'

concat-mor-split : ∀ {n Δ} {δ₀ δ₀' : Fin n → obj} {δ δ' : Fin Δ → obj} →
                   (∀ i → δ₀ i ⇒ δ₀' i) → (∀ i → δ i ⇒ δ' i) →
                   (s : Fin n ⊎ Fin Δ) → [ δ₀ , δ ] s ⇒ [ δ₀' , δ' ] s
concat-mor-split fs gs (inj₁ j) = fs j
concat-mor-split fs gs (inj₂ k) = gs k

concat-mor : ∀ {n Δ} {δ₀ δ₀' : Fin n → obj} {δ δ' : Fin Δ → obj} →
             (∀ i → δ₀ i ⇒ δ₀' i) → (∀ i → δ i ⇒ δ' i) → ∀ i → concat δ₀ δ i ⇒ concat δ₀' δ' i
concat-mor {n} fs gs i = concat-mor-split fs gs (splitAt n i)

concat-mor-cong : ∀ {n Δ} {δ₀ δ₀' : Fin n → obj} {δ δ' : Fin Δ → obj}
                  {fs fs' : ∀ i → δ₀ i ⇒ δ₀' i} {gs gs' : ∀ i → δ i ⇒ δ' i} →
                  (∀ i → fs i ≈ fs' i) → (∀ i → gs i ≈ gs' i) → ∀ i → concat-mor fs gs i ≈ concat-mor fs' gs' i
concat-mor-cong {n} es es' i with splitAt n i
... | inj₁ j = es j
... | inj₂ k = es' k

concat-mor-comp : ∀ {n Δ} {δ₀ δ₀' δ₀'' : Fin n → obj} {δ δ' δ'' : Fin Δ → obj}
                  (fs' : ∀ i → δ₀' i ⇒ δ₀'' i) (fs : ∀ i → δ₀ i ⇒ δ₀' i) (gs' : ∀ i → δ' i ⇒ δ'' i) (gs : ∀ i → δ i ⇒ δ' i) →
                  ∀ i → (concat-mor fs' gs' i ∘ concat-mor fs gs i) ≈ concat-mor (λ j → fs' j ∘ fs j) (λ j → gs' j ∘ gs j) i
concat-mor-comp {n} fs' fs gs' gs i with splitAt n i
... | inj₁ j = ≈-refl
... | inj₂ k = ≈-refl

concat-mor-id : ∀ {n Δ} {δ₀ : Fin n → obj} {δ : Fin Δ → obj} (i : Fin (n + Δ)) →
                concat-mor (λ j → id (δ₀ j)) (λ j → id (δ j)) i ≈ id _
concat-mor-id {n} i with splitAt n i
... | inj₁ j = ≈-refl
... | inj₂ k = ≈-refl

concat-mor-unit : ∀ {n Δ} {δ₀ δ₀' : Fin n → obj} {δ δ' : Fin Δ → obj} (fs : ∀ i → δ₀ i ⇒ δ₀' i) (gs : ∀ i → δ i ⇒ δ' i)
                  (i : Fin (n + Δ)) → concat-mor (λ j → id (δ₀' j) ∘ fs j) (λ j → gs j ∘ id (δ j)) i ≈ concat-mor fs gs i
concat-mor-unit {n} fs gs i = concat-mor-cong {n = n} (λ _ → id-left) (λ _ → id-right) i

extend-mor-id : ∀ {k} {δ : Fin k → obj} {X : obj} (i : Fin (suc k)) → extend-mor (λ j → id (δ j)) (id X) i ≈ id _
extend-mor-id Fin.zero    = ≈-refl
extend-mor-id (Fin.suc i) = ≈-refl

fmor-extend-id : ∀ {k} (P : Poly R.cat (suc k)) {δ : Fin k → obj} {X : obj} →
                 fmor P (extend-mor (λ j → id (δ j)) (id X)) ≈ id _
fmor-extend-id P = ≈-trans (fmor-cong P extend-mor-id) (fmor-id P)

-- Freezing the poly-variables δ₀ into the environment (with X at position 0) reshuffles the
-- combined context only up to pointwise equality.
env-pw-suc : ∀ {Δ n} (δ : Fin Δ → obj) (δ₀ : Fin n → obj) (X : obj) (s : Fin n ⊎ Fin Δ) →
             [_,_] {C = λ _ → obj} δ₀ δ s ≡ [_,_] {C = λ _ → obj} (extend δ₀ X) δ (map₁ Fin.suc s)
env-pw-suc δ δ₀ X (inj₁ k) = refl
env-pw-suc δ δ₀ X (inj₂ l) = refl

env-pw : ∀ {Δ n} (δ : Fin Δ → obj) (δ₀ : Fin n → obj) (X : obj) (i : Fin (suc (n + Δ))) →
         concat (extend {0} δ∅ X) (concat δ₀ δ) i ≡ concat (extend δ₀ X) δ i
env-pw δ δ₀ X Fin.zero    = refl
env-pw {Δ} {n} δ δ₀ X (Fin.suc j) = env-pw-suc δ δ₀ X (splitAt n j)

env-pw-natural : ∀ {Δ n} {δ δ' : Fin Δ → obj} (gs : ∀ i → δ i ⇒ δ' i) {δ₀ δ₀' : Fin n → obj} (fs : ∀ i → δ₀ i ⇒ δ₀' i)
                 {X X' : obj} (k : X ⇒ X') (i : Fin (suc (n + Δ))) →
                 (concat-mor (extend-mor fs k) gs i ∘ ≡-to-⇒ (env-pw δ δ₀ X i))
                   ≈ (≡-to-⇒ (env-pw δ' δ₀' X' i) ∘ concat-mor {n = 1} (extend-mor (λ j → id _) k) (concat-mor fs gs) i)
env-pw-natural gs fs k Fin.zero = ≈-trans id-right (≈-sym id-left)
env-pw-natural {Δ} {n} {δ} {δ'} gs {δ₀} {δ₀'} fs {X} {X'} k (Fin.suc j) = go (splitAt n j)
  where
  go : (s : Fin n ⊎ Fin Δ) →
       (concat-mor-split (extend-mor fs k) gs (map₁ Fin.suc s) ∘ ≡-to-⇒ (env-pw-suc δ δ₀ X s))
         ≈ (≡-to-⇒ (env-pw-suc δ' δ₀' X' s) ∘ concat-mor-split fs gs s)
  go (inj₁ l) = ≈-trans id-right (≈-sym id-left)
  go (inj₂ l) = ≈-trans id-right (≈-sym id-left)

env-pw-natural⁻ : ∀ {Δ n} {δ δ' : Fin Δ → obj} (gs : ∀ i → δ i ⇒ δ' i) {δ₀ δ₀' : Fin n → obj} (fs : ∀ i → δ₀ i ⇒ δ₀' i)
                  {X X' : obj} (k : X ⇒ X') (i : Fin (suc (n + Δ))) →
                  (concat-mor {n = 1} (extend-mor (λ j → id _) k) (concat-mor fs gs) i ∘ ≡-to-⇒ (sym (env-pw δ δ₀ X i)))
                    ≈ (≡-to-⇒ (sym (env-pw δ' δ₀' X' i)) ∘ concat-mor (extend-mor fs k) gs i)
env-pw-natural⁻ gs fs k Fin.zero = ≈-trans id-right (≈-sym id-left)
env-pw-natural⁻ {Δ} {n} {δ} {δ'} gs {δ₀} {δ₀'} fs {X} {X'} k (Fin.suc j) = go (splitAt n j)
  where
  go : (s : Fin n ⊎ Fin Δ) →
       (concat-mor-split fs gs s ∘ ≡-to-⇒ (sym (env-pw-suc δ δ₀ X s)))
         ≈ (≡-to-⇒ (sym (env-pw-suc δ' δ₀' X' s)) ∘ concat-mor-split (extend-mor fs k) gs (map₁ Fin.suc s))
  go (inj₁ l) = ≈-trans id-right (≈-sym id-left)
  go (inj₂ l) = ≈-trans id-right (≈-sym id-left)

concat-section : ∀ {n Δ} {δ₀ : Fin n → obj} {δ : Fin Δ → obj} →
                 (∀ i → Section (δ₀ i)) → (∀ i → Section (δ i)) → ∀ i → Section (concat δ₀ δ i)
concat-section {n = n} {δ₀ = δ₀} {δ = δ} δ₀c δc i =
  [_,_] {C = λ s → Section ([ δ₀ , δ ] s)} δ₀c δc (splitAt n i)

preserves-env-pw-suc : ∀ {Δ n} {δ : Fin Δ → obj} {δ₀ : Fin n → obj} {X : obj}
  (δc : ∀ i → Section (δ i)) (δ₀c : ∀ i → Section (δ₀ i)) (cX : Section X) (s : Fin n ⊎ Fin Δ) →
  preserves-section (≡-to-⇒ (env-pw-suc δ δ₀ X s))
    ([_,_] {C = λ s' → Section ([ δ₀ , δ ] s')} δ₀c δc s)
    ([_,_] {C = λ s' → Section ([ extend δ₀ X , δ ] s')} (extend-section δ₀c cX) δc (map₁ Fin.suc s))
preserves-env-pw-suc δc δ₀c cX (inj₁ k) = preserves-section-id (δ₀c k)
preserves-env-pw-suc δc δ₀c cX (inj₂ l) = preserves-section-id (δc l)

preserves-env-pw-suc⁻ : ∀ {Δ n} {δ : Fin Δ → obj} {δ₀ : Fin n → obj} {X : obj}
  (δc : ∀ i → Section (δ i)) (δ₀c : ∀ i → Section (δ₀ i)) (cX : Section X) (s : Fin n ⊎ Fin Δ) →
  preserves-section (≡-to-⇒ (sym (env-pw-suc δ δ₀ X s)))
    ([_,_] {C = λ s' → Section ([ extend δ₀ X , δ ] s')} (extend-section δ₀c cX) δc (map₁ Fin.suc s))
    ([_,_] {C = λ s' → Section ([ δ₀ , δ ] s')} δ₀c δc s)
preserves-env-pw-suc⁻ δc δ₀c cX (inj₁ k) = preserves-section-id (δ₀c k)
preserves-env-pw-suc⁻ δc δ₀c cX (inj₂ l) = preserves-section-id (δc l)

preserves-env-pw : ∀ {Δ n} {δ : Fin Δ → obj} {δ₀ : Fin n → obj} {X : obj}
  (δc : ∀ i → Section (δ i)) (δ₀c : ∀ i → Section (δ₀ i)) (cX : Section X) (i : Fin (suc (n + Δ))) →
  preserves-section (≡-to-⇒ (env-pw δ δ₀ X i))
    (concat-section {n = 1} (extend-section (λ ()) cX) (concat-section δ₀c δc) i)
    (concat-section {n = suc n} (extend-section δ₀c cX) δc i)
preserves-env-pw δc δ₀c cX Fin.zero = preserves-section-id cX
preserves-env-pw {n = n} δc δ₀c cX (Fin.suc j) = preserves-env-pw-suc δc δ₀c cX (splitAt n j)

preserves-env-pw⁻ : ∀ {Δ n} {δ : Fin Δ → obj} {δ₀ : Fin n → obj} {X : obj}
  (δc : ∀ i → Section (δ i)) (δ₀c : ∀ i → Section (δ₀ i)) (cX : Section X) (i : Fin (suc (n + Δ))) →
  preserves-section (≡-to-⇒ (sym (env-pw δ δ₀ X i)))
    (concat-section {n = suc n} (extend-section δ₀c cX) δc i)
    (concat-section {n = 1} (extend-section (λ ()) cX) (concat-section δ₀c δc) i)
preserves-env-pw⁻ δc δ₀c cX Fin.zero = preserves-section-id cX
preserves-env-pw⁻ {n = n} δc δ₀c cX (Fin.suc j) = preserves-env-pw-suc⁻ δc δ₀c cX (splitAt n j)

-- Applying the polynomial (as-poly τ δ) is the interpretation of τ, in each direction.
mutual
  apply-fwd : ∀ {Δ n} (τ : type (n + Δ)) (δ : Fin Δ → obj) (δ₀ : Fin n → obj) →
              ⟦ τ ⟧ty (concat δ₀ δ) ⇒ fobj μ-obj (as-poly {Δ} {n} τ δ) δ₀
  apply-fwd {n = n} (var i) δ δ₀ with splitAt n i
  ... | inj₁ j = id _
  ... | inj₂ k = id _
  apply-fwd unit      δ δ₀ = id _
  apply-fwd (base s)  δ δ₀ = id _
  apply-fwd (σ [+] τ) δ δ₀ = [+]-map (apply-fwd σ δ δ₀) (apply-fwd τ δ δ₀)
  apply-fwd (σ [×] τ) δ δ₀ = [×]-map (apply-fwd σ δ δ₀) (apply-fwd τ δ δ₀)
  apply-fwd (σ [→] τ) δ δ₀ = id _
  apply-fwd {Δ} {n} (μ τ) δ δ₀ =
    μ-map (as-poly {n + Δ} {1} τ (concat δ₀ δ)) δ∅ (as-poly {Δ} {suc n} τ δ) δ₀
      (apply-fwd-body τ δ δ₀ (μ-obj (as-poly {Δ} {suc n} τ δ) δ₀))

  apply-fwd-body : ∀ {Δ n} (τ : type (suc n + Δ)) (δ : Fin Δ → obj) (δ₀ : Fin n → obj) (X : obj) →
                   fobj μ-obj (as-poly {n + Δ} {1} τ (concat δ₀ δ)) (extend δ∅ X) ⇒ fobj μ-obj (as-poly {Δ} {suc n} τ δ) (extend δ₀ X)
  apply-fwd-body τ δ δ₀ X =
    apply-fwd τ δ (extend δ₀ X)
      ∘ as-poly-map τ (λ i → ≡-to-⇒ (env-pw δ δ₀ X i)) δ∅
      ∘ apply-bwd {n = 1} τ (concat δ₀ δ) (extend δ∅ X)

  apply-bwd : ∀ {Δ n} (τ : type (n + Δ)) (δ : Fin Δ → obj) (δ₀ : Fin n → obj) →
              fobj μ-obj (as-poly {Δ} {n} τ δ) δ₀ ⇒ ⟦ τ ⟧ty (concat δ₀ δ)
  apply-bwd {n = n} (var i) δ δ₀ with splitAt n i
  ... | inj₁ j = id _
  ... | inj₂ k = id _
  apply-bwd unit      δ δ₀ = id _
  apply-bwd (base s)  δ δ₀ = id _
  apply-bwd (σ [+] τ) δ δ₀ = [+]-map (apply-bwd σ δ δ₀) (apply-bwd τ δ δ₀)
  apply-bwd (σ [×] τ) δ δ₀ = [×]-map (apply-bwd σ δ δ₀) (apply-bwd τ δ δ₀)
  apply-bwd (σ [→] τ) δ δ₀ = id _
  apply-bwd {Δ} {n} (μ τ) δ δ₀ =
    μ-map (as-poly {Δ} {suc n} τ δ) δ₀ (as-poly {n + Δ} {1} τ (concat δ₀ δ)) δ∅
      (apply-bwd-body τ δ δ₀ (μ-obj (as-poly {n + Δ} {1} τ (concat δ₀ δ)) δ∅))

  apply-bwd-body : ∀ {Δ n} (τ : type (suc n + Δ)) (δ : Fin Δ → obj) (δ₀ : Fin n → obj) (X : obj) →
                   fobj μ-obj (as-poly {Δ} {suc n} τ δ) (extend δ₀ X) ⇒ fobj μ-obj (as-poly {n + Δ} {1} τ (concat δ₀ δ)) (extend δ∅ X)
  apply-bwd-body τ δ δ₀ X =
    apply-fwd {n = 1} τ (concat δ₀ δ) (extend δ∅ X)
      ∘ as-poly-map τ (λ i → ≡-to-⇒ (sym (env-pw δ δ₀ X i))) δ∅
      ∘ apply-bwd τ δ (extend δ₀ X)

as-poly-map-cast-inv : ∀ {Δ n} (τ : type (n + Δ)) {δ δ' : Fin Δ → obj} (h : ∀ i → δ i ≡ δ' i) (δ₀ : Fin n → obj) →
                       (as-poly-map τ (λ i → ≡-to-⇒ (sym (h i))) δ₀ ∘ as-poly-map τ (λ i → ≡-to-⇒ (h i)) δ₀) ≈ id _
as-poly-map-cast-inv τ h δ₀ =
  ≈-trans (as-poly-map-comp τ _ _ δ₀) (≈-trans (as-poly-map-cong τ (λ i → ≡-to-⇒-sym-l (h i)) δ₀) (as-poly-map-id τ δ₀))

as-poly-map-cast-inv' : ∀ {Δ n} (τ : type (n + Δ)) {δ δ' : Fin Δ → obj} (h : ∀ i → δ i ≡ δ' i) (δ₀ : Fin n → obj) →
                        (as-poly-map τ (λ i → ≡-to-⇒ (h i)) δ₀ ∘ as-poly-map τ (λ i → ≡-to-⇒ (sym (h i))) δ₀) ≈ id _
as-poly-map-cast-inv' τ h δ₀ =
  ≈-trans (as-poly-map-comp τ _ _ δ₀) (≈-trans (as-poly-map-cong τ (λ i → ≡-to-⇒-sym-r (h i)) δ₀) (as-poly-map-id τ δ₀))

mutual
  apply-fwd-natural : ∀ {Δ n} (τ : type (n + Δ)) (δ : Fin Δ → obj) {δ₀ δ₀' : Fin n → obj} (fs : ∀ i → δ₀ i ⇒ δ₀' i) →
                      (fmor (as-poly τ δ) fs ∘ apply-fwd τ δ δ₀) ≈ (apply-fwd τ δ δ₀' ∘ as-poly-map τ (concat-mor fs (λ i → id _)) δ∅)
  apply-fwd-natural {n = n} (var i) δ fs with splitAt n i
  ... | inj₁ j = ≈-trans id-right (≈-trans (fmor-var j fs) (≈-sym id-left))
  ... | inj₂ k = ≈-trans id-right (≈-trans (fmor-const fs) (≈-sym id-left))
  apply-fwd-natural unit      δ fs = ≈-trans id-right (≈-trans (fmor-const fs) (≈-sym id-left))
  apply-fwd-natural (base s)  δ fs = ≈-trans id-right (≈-trans (fmor-const fs) (≈-sym id-left))
  apply-fwd-natural (σ [+] τ) δ fs =
    ≈-trans (∘-cong (fmor-[+] (as-poly σ δ) (as-poly τ δ) fs) ≈-refl) ([+]-square (apply-fwd-natural σ δ fs) (apply-fwd-natural τ δ fs))
  apply-fwd-natural (σ [×] τ) δ fs =
    ≈-trans (∘-cong (fmor-[×] (as-poly σ δ) (as-poly τ δ) fs) ≈-refl) ([×]-square (apply-fwd-natural σ δ fs) (apply-fwd-natural τ δ fs))
  apply-fwd-natural (σ [→] τ) δ fs = ≈-trans id-right (≈-trans (fmor-const fs) (≈-sym id-left))
  apply-fwd-natural {Δ} {n} (μ τ) δ {δ₀} {δ₀'} fs = begin
      fmor (Poly.μ A) fs ∘ μ-map P δ∅ A δ₀ (apply-fwd-body τ δ δ₀ M)
    ≈⟨ ∘-cong (fmor-μ A fs) ≈-refl ⟩
      μ-map A δ₀ A δ₀' (fmor A (extend-mor fs (id _))) ∘ μ-map P δ∅ A δ₀ (apply-fwd-body τ δ δ₀ M)
    ≈⟨ μ-map-comp P δ∅ A δ₀ A δ₀' (apply-fwd-body τ δ δ₀ M) (fmor A (extend-mor fs (id _))) (apply-fwd-body τ δ δ₀ M')
                  (apply-fwd-body-carrier τ δ δ₀ k₁) ⟩
      μ-map P δ∅ A δ₀' (fmor A (extend-mor fs (id _)) ∘ apply-fwd-body τ δ δ₀ M')
    ≈⟨ μ-map-cong _ _ _ _ (apply-fwd-body-applied τ δ fs M') ⟩
      μ-map P δ∅ A δ₀' (apply-fwd-body τ δ δ₀' M' ∘ as-poly-map τ (concat-mor fs (λ i → id _)) (extend δ∅ M'))
    ≈˘⟨ μ-map-comp P δ∅ P' δ∅ A δ₀' (as-poly-map τ (concat-mor fs (λ i → id _)) (extend δ∅ (μ-obj P' δ∅)))
                   (apply-fwd-body τ δ δ₀' M') (as-poly-map τ (concat-mor fs (λ i → id _)) (extend δ∅ M'))
                   (as-poly-map-natural {n = 1} τ (concat-mor fs (λ i → id _)) (extend-mor (λ i → id _) k₂)) ⟩
      μ-map P' δ∅ A δ₀' (apply-fwd-body τ δ δ₀' M') ∘ μ-map P δ∅ P' δ∅ (as-poly-map τ (concat-mor fs (λ i → id _)) (extend δ∅ (μ-obj P' δ∅)))
    ∎
    where
      open ≈-Reasoning isEquiv
      A  = as-poly {Δ} {suc n} τ δ
      P  = as-poly {n + Δ} {1} τ (concat δ₀ δ)
      P' = as-poly {n + Δ} {1} τ (concat δ₀' δ)
      M  = μ-obj A δ₀
      M' = μ-obj A δ₀'
      k₁ = μ-map A δ₀ A δ₀' (fmor A (extend-mor fs (id _)))
      k₂ = μ-map P' δ∅ A δ₀' (apply-fwd-body τ δ δ₀' M')

  apply-fwd-map : ∀ {Δ n} (τ : type (n + Δ)) {δ δ' : Fin Δ → obj} (gs : ∀ i → δ i ⇒ δ' i) (δ₀ : Fin n → obj) →
                  (apply-fwd τ δ' δ₀ ∘ as-poly-map τ (concat-mor (λ i → id _) gs) δ∅) ≈ (as-poly-map τ gs δ₀ ∘ apply-fwd τ δ δ₀)
  apply-fwd-map {n = n} (var i) gs δ₀ with splitAt n i
  ... | inj₁ j = ≈-refl
  ... | inj₂ k = ≈-trans id-left (≈-sym id-right)
  apply-fwd-map unit      gs δ₀ = ≈-refl
  apply-fwd-map (base s)  gs δ₀ = ≈-refl
  apply-fwd-map (σ [+] τ) gs δ₀ = [+]-square (apply-fwd-map σ gs δ₀) (apply-fwd-map τ gs δ₀)
  apply-fwd-map (σ [×] τ) gs δ₀ = [×]-square (apply-fwd-map σ gs δ₀) (apply-fwd-map τ gs δ₀)
  apply-fwd-map (σ [→] τ) gs δ₀ = ≈-refl
  apply-fwd-map {Δ} {n} (μ τ) {δ} {δ'} gs δ₀ = begin
      μ-map P' δ∅ A' δ₀ (apply-fwd-body τ δ' δ₀ M') ∘ μ-map P δ∅ P' δ∅ (as-poly-map τ (concat-mor (λ i → id _) gs) (extend δ∅ (μ-obj P' δ∅)))
    ≈⟨ μ-map-comp P δ∅ P' δ∅ A' δ₀ (as-poly-map τ (concat-mor (λ i → id _) gs) (extend δ∅ (μ-obj P' δ∅)))
                  (apply-fwd-body τ δ' δ₀ M') (as-poly-map τ (concat-mor (λ i → id _) gs) (extend δ∅ M'))
                  (as-poly-map-natural {n = 1} τ (concat-mor (λ i → id _) gs) (extend-mor (λ i → id _) k₁)) ⟩
      μ-map P δ∅ A' δ₀ (apply-fwd-body τ δ' δ₀ M' ∘ as-poly-map τ (concat-mor (λ i → id _) gs) (extend δ∅ M'))
    ≈⟨ μ-map-cong _ _ _ _ (apply-fwd-body-frozen τ gs δ₀ M') ⟩
      μ-map P δ∅ A' δ₀ (as-poly-map τ gs (extend δ₀ M') ∘ apply-fwd-body τ δ δ₀ M')
    ≈˘⟨ μ-map-comp P δ∅ A δ₀ A' δ₀ (apply-fwd-body τ δ δ₀ M) (as-poly-map τ gs (extend δ₀ M')) (apply-fwd-body τ δ δ₀ M')
                   (apply-fwd-body-carrier τ δ δ₀ k₂) ⟩
      μ-map A δ₀ A' δ₀ (as-poly-map τ gs (extend δ₀ M')) ∘ μ-map P δ∅ A δ₀ (apply-fwd-body τ δ δ₀ M)
    ∎
    where
      open ≈-Reasoning isEquiv
      A  = as-poly {Δ} {suc n} τ δ
      A' = as-poly {Δ} {suc n} τ δ'
      P  = as-poly {n + Δ} {1} τ (concat δ₀ δ)
      P' = as-poly {n + Δ} {1} τ (concat δ₀ δ')
      M  = μ-obj A δ₀
      M' = μ-obj A' δ₀
      k₁ = μ-map P' δ∅ A' δ₀ (apply-fwd-body τ δ' δ₀ M')
      k₂ = μ-map A δ₀ A' δ₀ (as-poly-map τ gs (extend δ₀ M'))

  apply-bwd-natural : ∀ {Δ n} (τ : type (n + Δ)) (δ : Fin Δ → obj) {δ₀ δ₀' : Fin n → obj} (fs : ∀ i → δ₀ i ⇒ δ₀' i) →
                      (apply-bwd τ δ δ₀' ∘ fmor (as-poly τ δ) fs) ≈ (as-poly-map τ (concat-mor fs (λ i → id _)) δ∅ ∘ apply-bwd τ δ δ₀)
  apply-bwd-natural τ δ {δ₀} {δ₀'} fs = begin
      apply-bwd τ δ δ₀' ∘ fmor (as-poly τ δ) fs
    ≈˘⟨ id-right ⟩
      (apply-bwd τ δ δ₀' ∘ fmor (as-poly τ δ) fs) ∘ id _
    ≈˘⟨ ∘-cong ≈-refl (apply-fwd-bwd τ δ δ₀) ⟩
      (apply-bwd τ δ δ₀' ∘ fmor (as-poly τ δ) fs) ∘ (apply-fwd τ δ δ₀ ∘ apply-bwd τ δ δ₀)
    ≈⟨ ≈-trans (assoc _ _ _) (∘-cong ≈-refl (≈-sym (assoc _ _ _))) ⟩
      apply-bwd τ δ δ₀' ∘ ((fmor (as-poly τ δ) fs ∘ apply-fwd τ δ δ₀) ∘ apply-bwd τ δ δ₀)
    ≈⟨ ∘-cong ≈-refl (∘-cong (apply-fwd-natural τ δ fs) ≈-refl) ⟩
      apply-bwd τ δ δ₀' ∘ ((apply-fwd τ δ δ₀' ∘ as-poly-map τ (concat-mor fs (λ i → id _)) δ∅) ∘ apply-bwd τ δ δ₀)
    ≈⟨ ≈-trans (∘-cong ≈-refl (assoc _ _ _)) (≈-sym (assoc _ _ _)) ⟩
      (apply-bwd τ δ δ₀' ∘ apply-fwd τ δ δ₀') ∘ (as-poly-map τ (concat-mor fs (λ i → id _)) δ∅ ∘ apply-bwd τ δ δ₀)
    ≈⟨ ≈-trans (∘-cong (apply-bwd-fwd τ δ δ₀') ≈-refl) id-left ⟩
      as-poly-map τ (concat-mor fs (λ i → id _)) δ∅ ∘ apply-bwd τ δ δ₀
    ∎ where open ≈-Reasoning isEquiv

  apply-bwd-map : ∀ {Δ n} (τ : type (n + Δ)) {δ δ' : Fin Δ → obj} (gs : ∀ i → δ i ⇒ δ' i) (δ₀ : Fin n → obj) →
                  (apply-bwd τ δ' δ₀ ∘ as-poly-map τ gs δ₀) ≈ (as-poly-map τ (concat-mor (λ i → id _) gs) δ∅ ∘ apply-bwd τ δ δ₀)
  apply-bwd-map τ {δ} {δ'} gs δ₀ = begin
      apply-bwd τ δ' δ₀ ∘ as-poly-map τ gs δ₀
    ≈˘⟨ id-right ⟩
      (apply-bwd τ δ' δ₀ ∘ as-poly-map τ gs δ₀) ∘ id _
    ≈˘⟨ ∘-cong ≈-refl (apply-fwd-bwd τ δ δ₀) ⟩
      (apply-bwd τ δ' δ₀ ∘ as-poly-map τ gs δ₀) ∘ (apply-fwd τ δ δ₀ ∘ apply-bwd τ δ δ₀)
    ≈⟨ ≈-trans (assoc _ _ _) (∘-cong ≈-refl (≈-sym (assoc _ _ _))) ⟩
      apply-bwd τ δ' δ₀ ∘ ((as-poly-map τ gs δ₀ ∘ apply-fwd τ δ δ₀) ∘ apply-bwd τ δ δ₀)
    ≈˘⟨ ∘-cong ≈-refl (∘-cong (apply-fwd-map τ gs δ₀) ≈-refl) ⟩
      apply-bwd τ δ' δ₀ ∘ ((apply-fwd τ δ' δ₀ ∘ as-poly-map τ (concat-mor (λ i → id _) gs) δ∅) ∘ apply-bwd τ δ δ₀)
    ≈⟨ ≈-trans (∘-cong ≈-refl (assoc _ _ _)) (≈-sym (assoc _ _ _)) ⟩
      (apply-bwd τ δ' δ₀ ∘ apply-fwd τ δ' δ₀) ∘ (as-poly-map τ (concat-mor (λ i → id _) gs) δ∅ ∘ apply-bwd τ δ δ₀)
    ≈⟨ ≈-trans (∘-cong (apply-bwd-fwd τ δ' δ₀) ≈-refl) id-left ⟩
      as-poly-map τ (concat-mor (λ i → id _) gs) δ∅ ∘ apply-bwd τ δ δ₀
    ∎ where open ≈-Reasoning isEquiv

  apply-fwd-body-natural : ∀ {Δ n} (τ : type (suc n + Δ)) {δ δ' : Fin Δ → obj} (gs : ∀ i → δ i ⇒ δ' i)
                           {δ₀ δ₀' : Fin n → obj} (fs : ∀ i → δ₀ i ⇒ δ₀' i) {X X' : obj} (k : X ⇒ X') →
                           (as-poly-map τ gs (extend δ₀' X') ∘ fmor (as-poly τ δ) (extend-mor fs k) ∘ apply-fwd-body τ δ δ₀ X)
                             ≈ (apply-fwd-body τ δ' δ₀' X'
                                ∘ as-poly-map τ (concat-mor fs gs) (extend δ∅ X')
                                ∘ fmor (as-poly τ (concat δ₀ δ)) (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k))
  apply-fwd-body-natural {Δ} {n} τ {δ} {δ'} gs {δ₀} {δ₀'} fs {X} {X'} k = begin
      (pm ∘ F) ∘ ((af ∘ Rs) ∘ ab)
    ≈˘⟨ assoc _ _ _ ⟩
      ((pm ∘ F) ∘ (af ∘ Rs)) ∘ ab
    ≈˘⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
      (((pm ∘ F) ∘ af) ∘ Rs) ∘ ab
    ≈⟨ ∘-cong (∘-cong (assoc _ _ _) ≈-refl) ≈-refl ⟩
      ((pm ∘ (F ∘ af)) ∘ Rs) ∘ ab
    ≈⟨ ∘-cong (∘-cong (∘-cong ≈-refl (apply-fwd-natural {n = suc n} τ δ (extend-mor fs k))) ≈-refl) ≈-refl ⟩
      ((pm ∘ (af' ∘ Q₁)) ∘ Rs) ∘ ab
    ≈˘⟨ ∘-cong (∘-cong (assoc _ _ _) ≈-refl) ≈-refl ⟩
      (((pm ∘ af') ∘ Q₁) ∘ Rs) ∘ ab
    ≈˘⟨ ∘-cong (∘-cong (∘-cong (apply-fwd-map {n = suc n} τ gs (extend δ₀' X')) ≈-refl) ≈-refl) ≈-refl ⟩
      (((af'' ∘ Q₂) ∘ Q₁) ∘ Rs) ∘ ab
    ≈⟨ ∘-cong (∘-cong (assoc _ _ _) ≈-refl) ≈-refl ⟩
      ((af'' ∘ (Q₂ ∘ Q₁)) ∘ Rs) ∘ ab
    ≈⟨ ∘-cong (∘-cong (∘-cong ≈-refl step3) ≈-refl) ≈-refl ⟩
      ((af'' ∘ Q₃) ∘ Rs) ∘ ab
    ≈⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
      (af'' ∘ (Q₃ ∘ Rs)) ∘ ab
    ≈⟨ ∘-cong (∘-cong ≈-refl step4) ≈-refl ⟩
      (af'' ∘ (T' ∘ Q₄)) ∘ ab
    ≈˘⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
      ((af'' ∘ T') ∘ Q₄) ∘ ab
    ≈⟨ assoc _ _ _ ⟩
      (af'' ∘ T') ∘ (Q₄ ∘ ab)
    ≈⟨ ∘-cong ≈-refl (∘-cong step5 ≈-refl) ⟩
      (af'' ∘ T') ∘ ((Q₅ ∘ Q₆) ∘ ab)
    ≈⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
      (af'' ∘ T') ∘ (Q₅ ∘ (Q₆ ∘ ab))
    ≈˘⟨ ∘-cong ≈-refl (∘-cong ≈-refl (apply-bwd-natural {n = 1} τ (concat δ₀ δ) (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k))) ⟩
      (af'' ∘ T') ∘ (Q₅ ∘ (ab' ∘ Fp))
    ≈˘⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
      (af'' ∘ T') ∘ ((Q₅ ∘ ab') ∘ Fp)
    ≈˘⟨ ∘-cong ≈-refl (∘-cong (apply-bwd-map {n = 1} τ (concat-mor fs gs) (extend δ∅ X')) ≈-refl) ⟩
      (af'' ∘ T') ∘ ((ab'' ∘ pm₁) ∘ Fp)
    ≈⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
      (af'' ∘ T') ∘ (ab'' ∘ (pm₁ ∘ Fp))
    ≈˘⟨ assoc _ _ _ ⟩
      ((af'' ∘ T') ∘ ab'') ∘ (pm₁ ∘ Fp)
    ≈˘⟨ assoc _ _ _ ⟩
      (((af'' ∘ T') ∘ ab'') ∘ pm₁) ∘ Fp
    ∎
    where
      open ≈-Reasoning isEquiv
      A   = as-poly {Δ} {suc n} τ δ
      P   = as-poly {n + Δ} {1} τ (concat δ₀ δ)
      pm  = as-poly-map τ gs (extend δ₀' X')
      pm₁ = as-poly-map {n = 1} τ (concat-mor fs gs) (extend δ∅ X')
      F   = fmor A (extend-mor fs k)
      Fp  = fmor P (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k)
      af  = apply-fwd τ δ (extend δ₀ X)
      af' = apply-fwd τ δ (extend δ₀' X')
      af'' = apply-fwd τ δ' (extend δ₀' X')
      ab  = apply-bwd {n = 1} τ (concat δ₀ δ) (extend δ∅ X)
      ab' = apply-bwd {n = 1} τ (concat δ₀ δ) (extend δ∅ X')
      ab'' = apply-bwd {n = 1} τ (concat δ₀' δ') (extend δ∅ X')
      Rs   = as-poly-map τ (λ i → ≡-to-⇒ (env-pw δ δ₀ X i)) δ∅
      T'  = as-poly-map τ (λ i → ≡-to-⇒ (env-pw δ' δ₀' X' i)) δ∅
      ek  = extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k
      m₁  = concat-mor (extend-mor fs k) (λ i → id (δ i))
      m₂  = concat-mor (λ i → id (extend δ₀' X' i)) gs
      m₃  = concat-mor (extend-mor fs k) gs
      m₄  = concat-mor {n = 1} ek (concat-mor fs gs)
      m₅  = concat-mor {n = 1} (λ i → id (extend δ∅ X' i)) (concat-mor fs gs)
      m₆  = concat-mor {n = 1} ek (λ i → id (concat δ₀ δ i))
      Q₁  = as-poly-map τ m₁ δ∅
      Q₂  = as-poly-map τ m₂ δ∅
      Q₃  = as-poly-map τ m₃ δ∅
      Q₄  = as-poly-map τ m₄ δ∅
      Q₅  = as-poly-map τ m₅ δ∅
      Q₆  = as-poly-map τ m₆ δ∅
      eq3 : ∀ i → (m₂ i ∘ m₁ i) ≈ m₃ i
      eq3 i = ≈-trans (concat-mor-comp (λ i → id (extend δ₀' X' i)) (extend-mor fs k) gs (λ i → id (δ i)) i)
                      (concat-mor-unit (extend-mor fs k) gs i)
      step3 : (Q₂ ∘ Q₁) ≈ Q₃
      step3 = ≈-trans (as-poly-map-comp τ m₂ m₁ δ∅) (as-poly-map-cong τ eq3 δ∅)
      step4 : (Q₃ ∘ Rs) ≈ (T' ∘ Q₄)
      step4 = ≈-trans (as-poly-map-comp τ m₃ (λ i → ≡-to-⇒ (env-pw δ δ₀ X i)) δ∅)
                      (≈-trans (as-poly-map-cong τ (env-pw-natural gs fs k) δ∅)
                               (≈-sym (as-poly-map-comp τ (λ i → ≡-to-⇒ (env-pw δ' δ₀' X' i)) m₄ δ∅)))
      eq5 : ∀ i → (m₅ i ∘ m₆ i) ≈ m₄ i
      eq5 i = ≈-trans (concat-mor-comp (λ i → id (extend δ∅ X' i)) ek (concat-mor fs gs) (λ i → id (concat δ₀ δ i)) i)
                      (concat-mor-unit {n = 1} ek (concat-mor fs gs) i)
      step5 : Q₄ ≈ (Q₅ ∘ Q₆)
      step5 = ≈-sym (≈-trans (as-poly-map-comp τ m₅ m₆ δ∅) (as-poly-map-cong τ eq5 δ∅))

  apply-fwd-body-carrier : ∀ {Δ n} (τ : type (suc n + Δ)) (δ : Fin Δ → obj) (δ₀ : Fin n → obj) {X X' : obj} (k : X ⇒ X') →
                           (fmor (as-poly τ δ) (extend-mor (λ i → id _) k) ∘ apply-fwd-body τ δ δ₀ X)
                             ≈ (apply-fwd-body τ δ δ₀ X' ∘ fmor (as-poly τ (concat δ₀ δ)) (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k))
  apply-fwd-body-carrier {Δ} {n} τ δ δ₀ {X} {X'} k = begin
      F ∘ body
    ≈˘⟨ ≈-trans (∘-cong (as-poly-map-id τ (extend δ₀ X')) ≈-refl) id-left ⟩
      as-poly-map τ (λ i → id (δ i)) (extend δ₀ X') ∘ (F ∘ body)
    ≈˘⟨ assoc _ _ _ ⟩
      (as-poly-map τ (λ i → id (δ i)) (extend δ₀ X') ∘ F) ∘ body
    ≈⟨ apply-fwd-body-natural τ {δ} {δ} (λ i → id (δ i)) {δ₀} {δ₀} (λ i → id (δ₀ i)) k ⟩
      (body' ∘ as-poly-map τ (concat-mor (λ i → id (δ₀ i)) (λ i → id (δ i))) (extend δ∅ X')) ∘ Fp
    ≈⟨ ∘-cong (≈-trans (∘-cong ≈-refl (≈-trans (as-poly-map-cong τ (concat-mor-id {δ₀ = δ₀} {δ = δ}) (extend δ∅ X'))
                                                 (as-poly-map-id τ (extend δ∅ X'))))
                       id-right)
              ≈-refl ⟩
      body' ∘ Fp
    ∎
    where
      open ≈-Reasoning isEquiv
      F     = fmor (as-poly {Δ} {suc n} τ δ) (extend-mor (λ i → id (δ₀ i)) k)
      Fp    = fmor (as-poly {n + Δ} {1} τ (concat δ₀ δ)) (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k)
      body  = apply-fwd-body τ δ δ₀ X
      body' = apply-fwd-body τ δ δ₀ X'

  apply-fwd-body-frozen : ∀ {Δ n} (τ : type (suc n + Δ)) {δ δ' : Fin Δ → obj} (gs : ∀ i → δ i ⇒ δ' i) (δ₀ : Fin n → obj) (X : obj) →
                          (apply-fwd-body τ δ' δ₀ X ∘ as-poly-map τ (concat-mor (λ i → id _) gs) (extend δ∅ X))
                            ≈ (as-poly-map τ gs (extend δ₀ X) ∘ apply-fwd-body τ δ δ₀ X)
  apply-fwd-body-frozen τ {δ} {δ'} gs δ₀ X = begin
      body' ∘ pm₁
    ≈˘⟨ ≈-trans (∘-cong ≈-refl (fmor-extend-id (as-poly {n = 1} τ (concat δ₀ δ)) {δ = δ∅})) id-right ⟩
      (body' ∘ pm₁) ∘ fmor (as-poly τ (concat δ₀ δ)) (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) (id X))
    ≈˘⟨ apply-fwd-body-natural τ gs (λ i → id (δ₀ i)) (id X) ⟩
      (pm ∘ fmor (as-poly τ δ) (extend-mor (λ i → id (δ₀ i)) (id X))) ∘ body
    ≈⟨ ∘-cong (≈-trans (∘-cong ≈-refl (fmor-extend-id (as-poly τ δ) {δ = δ₀})) id-right) ≈-refl ⟩
      pm ∘ body
    ∎
    where
      open ≈-Reasoning isEquiv
      pm    = as-poly-map τ gs (extend δ₀ X)
      pm₁   = as-poly-map τ (concat-mor (λ i → id _) gs) (extend δ∅ X)
      body  = apply-fwd-body τ δ δ₀ X
      body' = apply-fwd-body τ δ' δ₀ X

  apply-fwd-body-applied : ∀ {Δ n} (τ : type (suc n + Δ)) (δ : Fin Δ → obj) {δ₀ δ₀' : Fin n → obj} (fs : ∀ i → δ₀ i ⇒ δ₀' i) (X : obj) →
                           (fmor (as-poly τ δ) (extend-mor fs (id _)) ∘ apply-fwd-body τ δ δ₀ X)
                             ≈ (apply-fwd-body τ δ δ₀' X ∘ as-poly-map τ (concat-mor fs (λ i → id _)) (extend δ∅ X))
  apply-fwd-body-applied τ δ {δ₀} {δ₀'} fs X = begin
      F ∘ body
    ≈˘⟨ ≈-trans (∘-cong (as-poly-map-id τ (extend δ₀' X)) ≈-refl) id-left ⟩
      as-poly-map τ (λ i → id (δ i)) (extend δ₀' X) ∘ (F ∘ body)
    ≈˘⟨ assoc _ _ _ ⟩
      (as-poly-map τ (λ i → id (δ i)) (extend δ₀' X) ∘ F) ∘ body
    ≈⟨ apply-fwd-body-natural τ (λ i → id (δ i)) fs (id X) ⟩
      (body' ∘ pm₁) ∘ fmor (as-poly τ (concat δ₀ δ)) (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) (id X))
    ≈⟨ ≈-trans (∘-cong ≈-refl (fmor-extend-id (as-poly {n = 1} τ (concat δ₀ δ)) {δ = δ∅})) id-right ⟩
      body' ∘ pm₁
    ∎
    where
      open ≈-Reasoning isEquiv
      F     = fmor (as-poly τ δ) (extend-mor fs (id _))
      pm₁   = as-poly-map τ (concat-mor fs (λ i → id _)) (extend δ∅ X)
      body  = apply-fwd-body τ δ δ₀ X
      body' = apply-fwd-body τ δ δ₀' X

  apply-bwd-body-carrier : ∀ {Δ n} (τ : type (suc n + Δ)) (δ : Fin Δ → obj) (δ₀ : Fin n → obj) {X X' : obj} (k : X ⇒ X') →
                           (fmor (as-poly τ (concat δ₀ δ)) (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k) ∘ apply-bwd-body τ δ δ₀ X)
                             ≈ (apply-bwd-body τ δ δ₀ X' ∘ fmor (as-poly τ δ) (extend-mor (λ i → id _) k))
  apply-bwd-body-carrier {Δ} {n} τ δ δ₀ {X} {X'} k = begin
      Fp ∘ ((af ∘ Rs) ∘ ab)
    ≈˘⟨ assoc _ _ _ ⟩
      (Fp ∘ (af ∘ Rs)) ∘ ab
    ≈˘⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
      ((Fp ∘ af) ∘ Rs) ∘ ab
    ≈⟨ ∘-cong (∘-cong (apply-fwd-natural {n = 1} τ (concat δ₀ δ) (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k)) ≈-refl) ≈-refl ⟩
      ((af' ∘ Q) ∘ Rs) ∘ ab
    ≈⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
      (af' ∘ (Q ∘ Rs)) ∘ ab
    ≈⟨ ∘-cong (∘-cong ≈-refl step) ≈-refl ⟩
      (af' ∘ (T' ∘ Q')) ∘ ab
    ≈˘⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
      ((af' ∘ T') ∘ Q') ∘ ab
    ≈⟨ assoc _ _ _ ⟩
      (af' ∘ T') ∘ (Q' ∘ ab)
    ≈˘⟨ ∘-cong ≈-refl (apply-bwd-natural {n = suc n} τ δ (extend-mor (λ i → id _) k)) ⟩
      (af' ∘ T') ∘ (ab' ∘ F)
    ≈˘⟨ assoc _ _ _ ⟩
      ((af' ∘ T') ∘ ab') ∘ F
    ∎
    where
      open ≈-Reasoning isEquiv
      F   = fmor (as-poly τ δ) (extend-mor (λ i → id _) k)
      Fp  = fmor (as-poly τ (concat δ₀ δ)) (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k)
      af  = apply-fwd {n = 1} τ (concat δ₀ δ) (extend δ∅ X)
      af' = apply-fwd {n = 1} τ (concat δ₀ δ) (extend δ∅ X')
      ab  = apply-bwd τ δ (extend δ₀ X)
      ab' = apply-bwd τ δ (extend δ₀ X')
      Rs   = as-poly-map τ (λ i → ≡-to-⇒ (sym (env-pw δ δ₀ X i))) δ∅
      T'  = as-poly-map τ (λ i → ≡-to-⇒ (sym (env-pw δ δ₀ X' i))) δ∅
      ek  = extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k
      mq  = concat-mor {n = 1} ek (λ i → id (concat δ₀ δ i))
      mq' = concat-mor {n = suc n} (extend-mor {δ = δ₀} {δ' = δ₀} (λ i → id _) k) (λ i → id (δ i))
      Q   = as-poly-map τ mq δ∅
      Q'  = as-poly-map τ mq' δ∅
      eq : ∀ i → (mq i ∘ ≡-to-⇒ (sym (env-pw δ δ₀ X i))) ≈ (≡-to-⇒ (sym (env-pw δ δ₀ X' i)) ∘ mq' i)
      eq i = ≈-trans (∘-cong (concat-mor-cong {n = 1} {fs = ek} {fs' = ek} {gs = λ i → id (concat δ₀ δ i)}
                                              {gs' = concat-mor (λ i → id (δ₀ i)) (λ i → id (δ i))}
                                              (λ _ → ≈-refl) (λ j → ≈-sym (concat-mor-id {δ₀ = δ₀} {δ = δ} j)) i)
                             ≈-refl)
                     (env-pw-natural⁻ (λ i → id (δ i)) (λ i → id (δ₀ i)) k i)
      step : (Q ∘ Rs) ≈ (T' ∘ Q')
      step = ≈-trans (as-poly-map-comp τ mq (λ i → ≡-to-⇒ (sym (env-pw δ δ₀ X i))) δ∅)
                     (≈-trans (as-poly-map-cong τ eq δ∅)
                              (≈-sym (as-poly-map-comp τ (λ i → ≡-to-⇒ (sym (env-pw δ δ₀ X' i))) mq' δ∅)))

  apply-body-bwd-fwd : ∀ {Δ n} (τ : type (suc n + Δ)) (δ : Fin Δ → obj) (δ₀ : Fin n → obj) (X : obj) →
                       (apply-bwd-body τ δ δ₀ X ∘ apply-fwd-body τ δ δ₀ X) ≈ id _
  apply-body-bwd-fwd {Δ} {n} τ δ δ₀ X = begin
      ((af ∘ T⁻) ∘ ab) ∘ ((af' ∘ Rs) ∘ ab')
    ≈⟨ ≈-trans (assoc _ _ _) (∘-cong ≈-refl (≈-trans (∘-cong ≈-refl (assoc _ _ _)) (≈-sym (assoc _ _ _)))) ⟩
      (af ∘ T⁻) ∘ ((ab ∘ af') ∘ (Rs ∘ ab'))
    ≈⟨ ∘-cong ≈-refl (≈-trans (∘-cong (apply-bwd-fwd {n = suc n} τ δ (extend δ₀ X)) ≈-refl) id-left) ⟩
      (af ∘ T⁻) ∘ (Rs ∘ ab')
    ≈⟨ ≈-trans (assoc _ _ _) (∘-cong ≈-refl (≈-sym (assoc _ _ _))) ⟩
      af ∘ ((T⁻ ∘ Rs) ∘ ab')
    ≈⟨ ∘-cong ≈-refl (≈-trans (∘-cong (as-poly-map-cast-inv τ (env-pw δ δ₀ X) δ∅) ≈-refl) id-left) ⟩
      af ∘ ab'
    ≈⟨ apply-fwd-bwd {n = 1} τ (concat δ₀ δ) (extend δ∅ X) ⟩
      id _
    ∎
    where
      open ≈-Reasoning isEquiv
      af  = apply-fwd {n = 1} τ (concat δ₀ δ) (extend δ∅ X)
      ab' = apply-bwd {n = 1} τ (concat δ₀ δ) (extend δ∅ X)
      af' = apply-fwd τ δ (extend δ₀ X)
      ab  = apply-bwd τ δ (extend δ₀ X)
      Rs   = as-poly-map τ (λ i → ≡-to-⇒ (env-pw δ δ₀ X i)) δ∅
      T⁻  = as-poly-map τ (λ i → ≡-to-⇒ (sym (env-pw δ δ₀ X i))) δ∅

  apply-body-fwd-bwd : ∀ {Δ n} (τ : type (suc n + Δ)) (δ : Fin Δ → obj) (δ₀ : Fin n → obj) (X : obj) →
                       (apply-fwd-body τ δ δ₀ X ∘ apply-bwd-body τ δ δ₀ X) ≈ id _
  apply-body-fwd-bwd {Δ} {n} τ δ δ₀ X = begin
      ((af ∘ Rs) ∘ ab) ∘ ((af' ∘ T⁻) ∘ ab')
    ≈⟨ ≈-trans (assoc _ _ _) (∘-cong ≈-refl (≈-trans (∘-cong ≈-refl (assoc _ _ _)) (≈-sym (assoc _ _ _)))) ⟩
      (af ∘ Rs) ∘ ((ab ∘ af') ∘ (T⁻ ∘ ab'))
    ≈⟨ ∘-cong ≈-refl (≈-trans (∘-cong (apply-bwd-fwd {n = 1} τ (concat δ₀ δ) (extend δ∅ X)) ≈-refl) id-left) ⟩
      (af ∘ Rs) ∘ (T⁻ ∘ ab')
    ≈⟨ ≈-trans (assoc _ _ _) (∘-cong ≈-refl (≈-sym (assoc _ _ _))) ⟩
      af ∘ ((Rs ∘ T⁻) ∘ ab')
    ≈⟨ ∘-cong ≈-refl (≈-trans (∘-cong (as-poly-map-cast-inv' τ (env-pw δ δ₀ X) δ∅) ≈-refl) id-left) ⟩
      af ∘ ab'
    ≈⟨ apply-fwd-bwd {n = suc n} τ δ (extend δ₀ X) ⟩
      id _
    ∎
    where
      open ≈-Reasoning isEquiv
      af  = apply-fwd τ δ (extend δ₀ X)
      ab' = apply-bwd τ δ (extend δ₀ X)
      af' = apply-fwd {n = 1} τ (concat δ₀ δ) (extend δ∅ X)
      ab  = apply-bwd {n = 1} τ (concat δ₀ δ) (extend δ∅ X)
      Rs   = as-poly-map τ (λ i → ≡-to-⇒ (env-pw δ δ₀ X i)) δ∅
      T⁻  = as-poly-map τ (λ i → ≡-to-⇒ (sym (env-pw δ δ₀ X i))) δ∅

  apply-bwd-fwd : ∀ {Δ n} (τ : type (n + Δ)) (δ : Fin Δ → obj) (δ₀ : Fin n → obj) → (apply-bwd τ δ δ₀ ∘ apply-fwd τ δ δ₀) ≈ id _
  apply-bwd-fwd {n = n} (var i) δ δ₀ with splitAt n i
  ... | inj₁ j = id-left
  ... | inj₂ k = id-left
  apply-bwd-fwd unit      δ δ₀ = id-left
  apply-bwd-fwd (base s)  δ δ₀ = id-left
  apply-bwd-fwd (σ [+] τ) δ δ₀ = [+]-inv (apply-bwd-fwd σ δ δ₀) (apply-bwd-fwd τ δ δ₀)
  apply-bwd-fwd (σ [×] τ) δ δ₀ = [×]-inv (apply-bwd-fwd σ δ δ₀) (apply-bwd-fwd τ δ δ₀)
  apply-bwd-fwd (σ [→] τ) δ δ₀ = id-left
  apply-bwd-fwd {Δ} {n} (μ τ) δ δ₀ = begin
      μ-map A δ₀ P δ∅ (apply-bwd-body τ δ δ₀ N) ∘ μ-map P δ∅ A δ₀ (apply-fwd-body τ δ δ₀ M)
    ≈⟨ μ-map-comp P δ∅ A δ₀ P δ∅ (apply-fwd-body τ δ δ₀ M) (apply-bwd-body τ δ δ₀ N) (apply-fwd-body τ δ δ₀ N)
                  (apply-fwd-body-carrier τ δ δ₀ (μ-map A δ₀ P δ∅ (apply-bwd-body τ δ δ₀ N))) ⟩
      μ-map P δ∅ P δ∅ (apply-bwd-body τ δ δ₀ N ∘ apply-fwd-body τ δ δ₀ N)
    ≈⟨ μ-map-cong _ _ _ _ (apply-body-bwd-fwd τ δ δ₀ N) ⟩
      μ-map P δ∅ P δ∅ (id _)
    ≈⟨ μ-map-id P δ∅ ⟩
      id _
    ∎
    where
      open ≈-Reasoning isEquiv
      A = as-poly {Δ} {suc n} τ δ
      P = as-poly {n + Δ} {1} τ (concat δ₀ δ)
      M = μ-obj A δ₀
      N = μ-obj P δ∅

  apply-fwd-bwd : ∀ {Δ n} (τ : type (n + Δ)) (δ : Fin Δ → obj) (δ₀ : Fin n → obj) → (apply-fwd τ δ δ₀ ∘ apply-bwd τ δ δ₀) ≈ id _
  apply-fwd-bwd {n = n} (var i) δ δ₀ with splitAt n i
  ... | inj₁ j = id-left
  ... | inj₂ k = id-left
  apply-fwd-bwd unit      δ δ₀ = id-left
  apply-fwd-bwd (base s)  δ δ₀ = id-left
  apply-fwd-bwd (σ [+] τ) δ δ₀ = [+]-inv (apply-fwd-bwd σ δ δ₀) (apply-fwd-bwd τ δ δ₀)
  apply-fwd-bwd (σ [×] τ) δ δ₀ = [×]-inv (apply-fwd-bwd σ δ δ₀) (apply-fwd-bwd τ δ δ₀)
  apply-fwd-bwd (σ [→] τ) δ δ₀ = id-left
  apply-fwd-bwd {Δ} {n} (μ τ) δ δ₀ = begin
      μ-map P δ∅ A δ₀ (apply-fwd-body τ δ δ₀ M) ∘ μ-map A δ₀ P δ∅ (apply-bwd-body τ δ δ₀ N)
    ≈⟨ μ-map-comp A δ₀ P δ∅ A δ₀ (apply-bwd-body τ δ δ₀ N) (apply-fwd-body τ δ δ₀ M) (apply-bwd-body τ δ δ₀ M)
                  (apply-bwd-body-carrier τ δ δ₀ (μ-map P δ∅ A δ₀ (apply-fwd-body τ δ δ₀ M))) ⟩
      μ-map A δ₀ A δ₀ (apply-fwd-body τ δ δ₀ M ∘ apply-bwd-body τ δ δ₀ M)
    ≈⟨ μ-map-cong _ _ _ _ (apply-body-fwd-bwd τ δ δ₀ M) ⟩
      μ-map A δ₀ A δ₀ (id _)
    ≈⟨ μ-map-id A δ₀ ⟩
      id _
    ∎
    where
      open ≈-Reasoning isEquiv
      A = as-poly {Δ} {suc n} τ δ
      P = as-poly {n + Δ} {1} τ (concat δ₀ δ)
      M = μ-obj A δ₀
      N = μ-obj P δ∅

apply-fwd-var : ∀ {Δ n} (δ : Fin Δ → obj) (δ₀ : Fin n → obj) (s : Fin n ⊎ Fin Δ) →
                [_,_] {C = λ _ → obj} δ₀ δ s ⇒
                  fobj μ-obj ([_,_] {C = λ _ → Poly R.cat n} Poly.var (λ j → Poly.const (δ j)) s) δ₀
apply-fwd-var δ δ₀ (inj₁ j) = id _
apply-fwd-var δ δ₀ (inj₂ k) = id _

apply-fwd-var-eq : ∀ {Δ n} (δ : Fin Δ → obj) (δ₀ : Fin n → obj) (i : Fin (n + Δ)) →
                   apply-fwd-var δ δ₀ (splitAt n i) ≈ apply-fwd (var i) δ δ₀
apply-fwd-var-eq {Δ} {n} δ δ₀ i with splitAt n i
... | inj₁ j = ≈-refl
... | inj₂ k = ≈-refl

preserves-apply-fwd-var : ∀ {Δ n} {δ : Fin Δ → obj} {δ₀ : Fin n → obj}
  (δc : ∀ i → Section (δ i)) (δ₀c : ∀ i → Section (δ₀ i)) (s : Fin n ⊎ Fin Δ) →
  preserves-section (apply-fwd-var δ δ₀ s)
    ([_,_] {C = λ s' → Section ([ δ₀ , δ ] s')} δ₀c δc s)
    (poly-section ([_,_] {C = λ _ → Poly R.cat n} Poly.var (λ j → Poly.const (δ j)) s)
      (as-poly-var-section δ δc s) δ₀c)
preserves-apply-fwd-var δc δ₀c (inj₁ j) = preserves-section-id (δ₀c j)
preserves-apply-fwd-var δc δ₀c (inj₂ k) = preserves-section-id (δc k)

mutual
  preserves-apply-fwd : ∀ {Δ n} (τ : type (n + Δ)) {δ : Fin Δ → obj} {δ₀ : Fin n → obj}
    (δc : ∀ i → Section (δ i)) (δ₀c : ∀ i → Section (δ₀ i)) →
    preserves-section (apply-fwd τ δ δ₀)
      (unit-section τ (concat δ₀ δ) (concat-section δ₀c δc))
      (poly-section (as-poly τ δ) (as-poly-section τ δ δc) δ₀c)
  preserves-apply-fwd {n = n} (var i) {δ} {δ₀} δc δ₀c =
    preserves-section-resp (apply-fwd-var-eq δ δ₀ i) (preserves-apply-fwd-var δc δ₀c (splitAt n i))
  preserves-apply-fwd unit      δc δ₀c = preserves-section-id 𝟙ty-section
  preserves-apply-fwd (base s)  δc δ₀c = preserves-section-id (sort-section s)
  preserves-apply-fwd (σ [+] τ) {δ} {δ₀} δc δ₀c =
    preserves-coprod-m
      (preserves-Lf-map {c = unit-section σ (concat δ₀ δ) (concat-section δ₀c δc)}
                        {d = poly-section (as-poly σ δ) (as-poly-section σ δ δc) δ₀c}
                        (preserves-apply-fwd σ δc δ₀c))
      (preserves-Lf-map {c = unit-section τ (concat δ₀ δ) (concat-section δ₀c δc)}
                        {d = poly-section (as-poly τ δ) (as-poly-section τ δ δc) δ₀c}
                        (preserves-apply-fwd τ δc δ₀c))
  preserves-apply-fwd (σ [×] τ) {δ} {δ₀} δc δ₀c =
    preserves-Lf-map
      {c = prod-section (unit-section σ (concat δ₀ δ) (concat-section δ₀c δc))
                        (unit-section τ (concat δ₀ δ) (concat-section δ₀c δc))}
      {d = prod-section (poly-section (as-poly σ δ) (as-poly-section σ δ δc) δ₀c)
                        (poly-section (as-poly τ δ) (as-poly-section τ δ δc) δ₀c)}
      (preserves-prod-m (preserves-apply-fwd σ δc δ₀c) (preserves-apply-fwd τ δc δ₀c))
  preserves-apply-fwd (σ [→] τ) δc δ₀c = preserves-section-id (Lf-section exp-section)
  preserves-apply-fwd {Δ} {n} (μ τ) {δ} {δ₀} δc δ₀c =
    preserves-μ-map (as-poly {n + Δ} {1} τ (concat δ₀ δ)) δ∅ (as-poly {Δ} {suc n} τ δ) δ₀
      (λ ()) δ₀c
      (as-poly-section {n + Δ} {1} τ (concat δ₀ δ) (concat-section δ₀c δc))
      (as-poly-section {Δ} {suc n} τ δ δc)
      (apply-fwd-body τ δ δ₀ M)
      (preserves-section-∘
        (preserves-section-∘
          (preserves-apply-fwd {n = suc n} τ δc (extend-section δ₀c μM))
          (preserves-as-poly-map τ (λ i → preserves-env-pw δc δ₀c μM i) δ∅ (λ ())))
        (preserves-apply-bwd {n = 1} τ (concat-section δ₀c δc) (extend-section (λ ()) μM)))
    where
    M  = μ-obj (as-poly {Δ} {suc n} τ δ) δ₀
    μM = poly-section (as-poly {Δ} {n} (μ τ) δ) (as-poly-section {Δ} {n} (μ τ) δ δc) δ₀c

  preserves-apply-bwd : ∀ {Δ n} (τ : type (n + Δ)) {δ : Fin Δ → obj} {δ₀ : Fin n → obj}
    (δc : ∀ i → Section (δ i)) (δ₀c : ∀ i → Section (δ₀ i)) →
    preserves-section (apply-bwd τ δ δ₀)
      (poly-section (as-poly τ δ) (as-poly-section τ δ δc) δ₀c)
      (unit-section τ (concat δ₀ δ) (concat-section δ₀c δc))
  preserves-apply-bwd τ {δ} {δ₀} δc δ₀c =
    preserves-section-inv (apply-fwd-bwd τ δ δ₀) (apply-bwd-fwd τ δ δ₀)
      (preserves-apply-fwd τ δc δ₀c)

-- Pointwise action of a lifted substitution on the extended environment: the new variable is mapped
-- to itself, and the (weakened) old ones ignore it.
sub-lift-pw : ∀ {Δ Δ'} (σ : TySub Δ Δ') (δ : Fin Δ' → obj) (X : obj) (i : Fin (suc Δ)) →
              ⟦ sub-lift σ i ⟧ty (concat (extend {0} δ∅ X) δ) ≡ concat (extend {0} δ∅ X) (λ j → ⟦ σ j ⟧ty δ) i
sub-lift-pw σ δ X Fin.zero    = refl
sub-lift-pw σ δ X (Fin.suc j) = ty-ren Fin.suc (σ j) (concat (extend {0} δ∅ X) δ)

-- Semantic substitution: substituting then interpreting maps to interpreting in the environment
-- that interprets the substituents (in each direction).
mutual
  subst-fwd : ∀ {Δ Δ'} (σ : TySub Δ Δ') (τ : type Δ) (δ : Fin Δ' → obj) →
              ⟦ sub σ τ ⟧ty δ ⇒ ⟦ τ ⟧ty (λ i → ⟦ σ i ⟧ty δ)
  subst-fwd σ (var i)     δ = id _
  subst-fwd σ unit        δ = id _
  subst-fwd σ (base s)    δ = id _
  subst-fwd σ (τ₁ [+] τ₂) δ = [+]-map (subst-fwd σ τ₁ δ) (subst-fwd σ τ₂ δ)
  subst-fwd σ (τ₁ [×] τ₂) δ = [×]-map (subst-fwd σ τ₁ δ) (subst-fwd σ τ₂ δ)
  subst-fwd σ (τ₁ [→] τ₂) δ = id _
  subst-fwd {Δ} {Δ'} σ (μ τ) δ =
    μ-map (as-poly {Δ'} {1} (sub (sub-lift σ) τ) δ) δ∅ (as-poly {Δ} {1} τ (λ i → ⟦ σ i ⟧ty δ)) δ∅
      (subst-fwd-body σ τ δ (μ-obj (as-poly {Δ} {1} τ (λ i → ⟦ σ i ⟧ty δ)) δ∅))

  subst-fwd-body : ∀ {Δ Δ'} (σ : TySub Δ Δ') (τ : type (suc Δ)) (δ : Fin Δ' → obj) (X : obj) →
                   fobj μ-obj (as-poly {Δ'} {1} (sub (sub-lift σ) τ) δ) (extend δ∅ X)
                     ⇒ fobj μ-obj (as-poly {Δ} {1} τ (λ i → ⟦ σ i ⟧ty δ)) (extend δ∅ X)
  subst-fwd-body σ τ δ X =
    apply-fwd {n = 1} τ (λ i → ⟦ σ i ⟧ty δ) (extend δ∅ X)
      ∘ as-poly-map τ (λ i → ≡-to-⇒ (sub-lift-pw σ δ X i)) δ∅
      ∘ subst-fwd (sub-lift σ) τ (concat (extend {0} δ∅ X) δ)
      ∘ apply-bwd {n = 1} (sub (sub-lift σ) τ) δ (extend δ∅ X)

  subst-bwd : ∀ {Δ Δ'} (σ : TySub Δ Δ') (τ : type Δ) (δ : Fin Δ' → obj) →
              ⟦ τ ⟧ty (λ i → ⟦ σ i ⟧ty δ) ⇒ ⟦ sub σ τ ⟧ty δ
  subst-bwd σ (var i)     δ = id _
  subst-bwd σ unit        δ = id _
  subst-bwd σ (base s)    δ = id _
  subst-bwd σ (τ₁ [+] τ₂) δ = [+]-map (subst-bwd σ τ₁ δ) (subst-bwd σ τ₂ δ)
  subst-bwd σ (τ₁ [×] τ₂) δ = [×]-map (subst-bwd σ τ₁ δ) (subst-bwd σ τ₂ δ)
  subst-bwd σ (τ₁ [→] τ₂) δ = id _
  subst-bwd {Δ} {Δ'} σ (μ τ) δ =
    μ-map (as-poly {Δ} {1} τ (λ i → ⟦ σ i ⟧ty δ)) δ∅ (as-poly {Δ'} {1} (sub (sub-lift σ) τ) δ) δ∅
      (subst-bwd-body σ τ δ (μ-obj (as-poly {Δ'} {1} (sub (sub-lift σ) τ) δ) δ∅))

  subst-bwd-body : ∀ {Δ Δ'} (σ : TySub Δ Δ') (τ : type (suc Δ)) (δ : Fin Δ' → obj) (X : obj) →
                   fobj μ-obj (as-poly {Δ} {1} τ (λ i → ⟦ σ i ⟧ty δ)) (extend δ∅ X)
                     ⇒ fobj μ-obj (as-poly {Δ'} {1} (sub (sub-lift σ) τ) δ) (extend δ∅ X)
  subst-bwd-body σ τ δ X =
    apply-fwd {n = 1} (sub (sub-lift σ) τ) δ (extend δ∅ X)
      ∘ subst-bwd (sub-lift σ) τ (concat (extend {0} δ∅ X) δ)
      ∘ as-poly-map τ (λ i → ≡-to-⇒ (sym (sub-lift-pw σ δ X i))) δ∅
      ∘ apply-bwd {n = 1} τ (λ i → ⟦ σ i ⟧ty δ) (extend δ∅ X)

sub-lift-pw-natural : ∀ {Δ Δ'} (σ : TySub Δ Δ') {δ δ' : Fin Δ' → obj} (gs : ∀ i → δ i ⇒ δ' i) {X X' : obj} (k : X ⇒ X')
                      (i : Fin (suc Δ)) →
                      (concat-mor {n = 1} (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k) (λ i → as-poly-map (σ i) gs δ∅) i
                         ∘ ≡-to-⇒ (sub-lift-pw σ δ X i))
                        ≈ (≡-to-⇒ (sub-lift-pw σ δ' X' i)
                           ∘ as-poly-map (sub-lift σ i) (concat-mor {n = 1} (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k) gs) δ∅)
sub-lift-pw-natural σ gs k Fin.zero    = ≈-trans id-right (≈-sym id-left)
sub-lift-pw-natural σ gs k (Fin.suc j) =
  ≈-sym (as-poly-map-ren {n = 0} Fin.suc (σ j) (concat-mor {n = 1} (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k) gs) δ∅)

mutual
  subst-fwd-natural : ∀ {Δ Δ'} (σ : TySub Δ Δ') (τ : type Δ) {δ δ' : Fin Δ' → obj} (gs : ∀ i → δ i ⇒ δ' i) →
                      (as-poly-map τ (λ i → as-poly-map (σ i) gs δ∅) δ∅ ∘ subst-fwd σ τ δ)
                        ≈ (subst-fwd σ τ δ' ∘ as-poly-map (sub σ τ) gs δ∅)
  subst-fwd-natural σ (var i)     gs = ≈-trans id-right (≈-sym id-left)
  subst-fwd-natural σ unit        gs = ≈-refl
  subst-fwd-natural σ (base s)    gs = ≈-refl
  subst-fwd-natural σ (τ₁ [+] τ₂) gs = [+]-square (subst-fwd-natural σ τ₁ gs) (subst-fwd-natural σ τ₂ gs)
  subst-fwd-natural σ (τ₁ [×] τ₂) gs = [×]-square (subst-fwd-natural σ τ₁ gs) (subst-fwd-natural σ τ₂ gs)
  subst-fwd-natural σ (τ₁ [→] τ₂) gs = ≈-refl
  subst-fwd-natural {Δ} {Δ'} σ (μ τ) {δ} {δ'} gs = begin
      μ-map A δ∅ A' δ∅ (as-poly-map {n = 1} τ gs' (extend δ∅ M')) ∘ μ-map P δ∅ A δ∅ (subst-fwd-body σ τ δ M)
    ≈⟨ μ-map-comp P δ∅ A δ∅ A' δ∅ (subst-fwd-body σ τ δ M) (as-poly-map {n = 1} τ gs' (extend δ∅ M')) (subst-fwd-body σ τ δ M')
                  (subst-fwd-body-carrier σ τ δ k₁) ⟩
      μ-map P δ∅ A' δ∅ (as-poly-map {n = 1} τ gs' (extend δ∅ M') ∘ subst-fwd-body σ τ δ M')
    ≈⟨ μ-map-cong _ _ _ _ (subst-fwd-body-applied σ τ gs M') ⟩
      μ-map P δ∅ A' δ∅ (subst-fwd-body σ τ δ' M' ∘ as-poly-map {n = 1} (sub (sub-lift σ) τ) gs (extend δ∅ M'))
    ≈˘⟨ μ-map-comp P δ∅ P' δ∅ A' δ∅ (as-poly-map {n = 1} (sub (sub-lift σ) τ) gs (extend δ∅ N'))
                   (subst-fwd-body σ τ δ' M') (as-poly-map {n = 1} (sub (sub-lift σ) τ) gs (extend δ∅ M'))
                   (as-poly-map-natural {n = 1} (sub (sub-lift σ) τ) gs (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k₂)) ⟩
      μ-map P' δ∅ A' δ∅ (subst-fwd-body σ τ δ' M') ∘ μ-map P δ∅ P' δ∅ (as-poly-map {n = 1} (sub (sub-lift σ) τ) gs (extend δ∅ N'))
    ∎
    where
      open ≈-Reasoning isEquiv
      A  = as-poly {Δ} {1} τ (λ i → ⟦ σ i ⟧ty δ)
      A' = as-poly {Δ} {1} τ (λ i → ⟦ σ i ⟧ty δ')
      P  = as-poly {Δ'} {1} (sub (sub-lift σ) τ) δ
      P' = as-poly {Δ'} {1} (sub (sub-lift σ) τ) δ'
      M  = μ-obj A δ∅
      M' = μ-obj A' δ∅
      N' = μ-obj P' δ∅
      gs' : ∀ i → ⟦ σ i ⟧ty δ ⇒ ⟦ σ i ⟧ty δ'
      gs' i = as-poly-map (σ i) gs δ∅
      k₁ = μ-map A δ∅ A' δ∅ (as-poly-map {n = 1} τ gs' (extend δ∅ M'))
      k₂ = μ-map P' δ∅ A' δ∅ (subst-fwd-body σ τ δ' M')

  subst-fwd-body-natural : ∀ {Δ Δ'} (σ : TySub Δ Δ') (τ : type (suc Δ)) {δ δ' : Fin Δ' → obj} (gs : ∀ i → δ i ⇒ δ' i)
                           {X X' : obj} (k : X ⇒ X') →
                           (as-poly-map {n = 1} τ (λ i → as-poly-map (σ i) gs δ∅) (extend δ∅ X')
                              ∘ fmor (as-poly {Δ} {1} τ (λ i → ⟦ σ i ⟧ty δ)) (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k)
                              ∘ subst-fwd-body σ τ δ X)
                             ≈ (subst-fwd-body σ τ δ' X'
                                ∘ as-poly-map {n = 1} (sub (sub-lift σ) τ) gs (extend δ∅ X')
                                ∘ fmor (as-poly {Δ'} {1} (sub (sub-lift σ) τ) δ) (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k))
  subst-fwd-body-natural {Δ} {Δ'} σ τ {δ} {δ'} gs {X} {X'} k = begin
      (pm ∘ F) ∘ (((af ∘ Rs) ∘ S) ∘ ab)
    ≈˘⟨ assoc _ _ _ ⟩
      ((pm ∘ F) ∘ ((af ∘ Rs) ∘ S)) ∘ ab
    ≈˘⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
      (((pm ∘ F) ∘ (af ∘ Rs)) ∘ S) ∘ ab
    ≈˘⟨ ∘-cong (∘-cong (assoc _ _ _) ≈-refl) ≈-refl ⟩
      ((((pm ∘ F) ∘ af) ∘ Rs) ∘ S) ∘ ab
    ≈⟨ ∘-cong (∘-cong (∘-cong (assoc _ _ _) ≈-refl) ≈-refl) ≈-refl ⟩
      (((pm ∘ (F ∘ af)) ∘ Rs) ∘ S) ∘ ab
    ≈⟨ ∘-cong (∘-cong (∘-cong (∘-cong ≈-refl (apply-fwd-natural {n = 1} τ (λ i → ⟦ σ i ⟧ty δ) ek)) ≈-refl) ≈-refl) ≈-refl ⟩
      (((pm ∘ (af' ∘ Q₁)) ∘ Rs) ∘ S) ∘ ab
    ≈˘⟨ ∘-cong (∘-cong (∘-cong (assoc _ _ _) ≈-refl) ≈-refl) ≈-refl ⟩
      ((((pm ∘ af') ∘ Q₁) ∘ Rs) ∘ S) ∘ ab
    ≈˘⟨ ∘-cong (∘-cong (∘-cong (∘-cong (apply-fwd-map {n = 1} τ gs' (extend δ∅ X')) ≈-refl) ≈-refl) ≈-refl) ≈-refl ⟩
      ((((af'' ∘ Q₂) ∘ Q₁) ∘ Rs) ∘ S) ∘ ab
    ≈⟨ ∘-cong (∘-cong (∘-cong (assoc _ _ _) ≈-refl) ≈-refl) ≈-refl ⟩
      (((af'' ∘ (Q₂ ∘ Q₁)) ∘ Rs) ∘ S) ∘ ab
    ≈⟨ ∘-cong (∘-cong (∘-cong (∘-cong ≈-refl step3) ≈-refl) ≈-refl) ≈-refl ⟩
      (((af'' ∘ Q₃) ∘ Rs) ∘ S) ∘ ab
    ≈⟨ ∘-cong (∘-cong (assoc _ _ _) ≈-refl) ≈-refl ⟩
      ((af'' ∘ (Q₃ ∘ Rs)) ∘ S) ∘ ab
    ≈⟨ ∘-cong (∘-cong (∘-cong ≈-refl step4) ≈-refl) ≈-refl ⟩
      ((af'' ∘ (T' ∘ Q₄)) ∘ S) ∘ ab
    ≈˘⟨ ∘-cong (∘-cong (assoc _ _ _) ≈-refl) ≈-refl ⟩
      (((af'' ∘ T') ∘ Q₄) ∘ S) ∘ ab
    ≈⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
      ((af'' ∘ T') ∘ (Q₄ ∘ S)) ∘ ab
    ≈⟨ ∘-cong (∘-cong ≈-refl (subst-fwd-natural (sub-lift σ) τ mk)) ≈-refl ⟩
      ((af'' ∘ T') ∘ (S' ∘ Q₇)) ∘ ab
    ≈˘⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
      (((af'' ∘ T') ∘ S') ∘ Q₇) ∘ ab
    ≈⟨ assoc _ _ _ ⟩
      ((af'' ∘ T') ∘ S') ∘ (Q₇ ∘ ab)
    ≈⟨ ∘-cong ≈-refl (∘-cong step5 ≈-refl) ⟩
      ((af'' ∘ T') ∘ S') ∘ ((Q₅ ∘ Q₆) ∘ ab)
    ≈⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
      ((af'' ∘ T') ∘ S') ∘ (Q₅ ∘ (Q₆ ∘ ab))
    ≈˘⟨ ∘-cong ≈-refl (∘-cong ≈-refl (apply-bwd-natural {n = 1} (sub (sub-lift σ) τ) δ ek)) ⟩
      ((af'' ∘ T') ∘ S') ∘ (Q₅ ∘ (ab' ∘ Fp))
    ≈˘⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
      ((af'' ∘ T') ∘ S') ∘ ((Q₅ ∘ ab') ∘ Fp)
    ≈˘⟨ ∘-cong ≈-refl (∘-cong (apply-bwd-map {n = 1} (sub (sub-lift σ) τ) gs (extend δ∅ X')) ≈-refl) ⟩
      ((af'' ∘ T') ∘ S') ∘ ((ab'' ∘ pm₁) ∘ Fp)
    ≈⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
      ((af'' ∘ T') ∘ S') ∘ (ab'' ∘ (pm₁ ∘ Fp))
    ≈˘⟨ assoc _ _ _ ⟩
      (((af'' ∘ T') ∘ S') ∘ ab'') ∘ (pm₁ ∘ Fp)
    ≈˘⟨ assoc _ _ _ ⟩
      ((((af'' ∘ T') ∘ S') ∘ ab'') ∘ pm₁) ∘ Fp
    ∎
    where
      open ≈-Reasoning isEquiv
      A    = as-poly {Δ} {1} τ (λ i → ⟦ σ i ⟧ty δ)
      P    = as-poly {Δ'} {1} (sub (sub-lift σ) τ) δ
      gs'  : ∀ i → ⟦ σ i ⟧ty δ ⇒ ⟦ σ i ⟧ty δ'
      gs' i = as-poly-map (σ i) gs δ∅
      ek   = extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k
      mk   = concat-mor {n = 1} ek gs
      pm   = as-poly-map {n = 1} τ gs' (extend δ∅ X')
      pm₁  = as-poly-map {n = 1} (sub (sub-lift σ) τ) gs (extend δ∅ X')
      F    = fmor A ek
      Fp   = fmor P ek
      af   = apply-fwd {n = 1} τ (λ i → ⟦ σ i ⟧ty δ) (extend δ∅ X)
      af'  = apply-fwd {n = 1} τ (λ i → ⟦ σ i ⟧ty δ) (extend δ∅ X')
      af'' = apply-fwd {n = 1} τ (λ i → ⟦ σ i ⟧ty δ') (extend δ∅ X')
      ab   = apply-bwd {n = 1} (sub (sub-lift σ) τ) δ (extend δ∅ X)
      ab'  = apply-bwd {n = 1} (sub (sub-lift σ) τ) δ (extend δ∅ X')
      ab'' = apply-bwd {n = 1} (sub (sub-lift σ) τ) δ' (extend δ∅ X')
      Rs   = as-poly-map τ (λ i → ≡-to-⇒ (sub-lift-pw σ δ X i)) δ∅
      T'   = as-poly-map τ (λ i → ≡-to-⇒ (sub-lift-pw σ δ' X' i)) δ∅
      S    = subst-fwd (sub-lift σ) τ (concat (extend {0} δ∅ X) δ)
      S'   = subst-fwd (sub-lift σ) τ (concat (extend {0} δ∅ X') δ')
      m₁   = concat-mor {n = 1} ek (λ i → id (⟦ σ i ⟧ty δ))
      m₂   = concat-mor {n = 1} (λ i → id (extend δ∅ X' i)) gs'
      m₃   = concat-mor {n = 1} ek gs'
      m₄   : ∀ i → ⟦ sub-lift σ i ⟧ty (concat (extend {0} δ∅ X) δ) ⇒ ⟦ sub-lift σ i ⟧ty (concat (extend {0} δ∅ X') δ')
      m₄ i = as-poly-map (sub-lift σ i) mk δ∅
      m₅   = concat-mor {n = 1} (λ i → id (extend δ∅ X' i)) gs
      m₆   = concat-mor {n = 1} ek (λ i → id (δ i))
      Q₁   = as-poly-map τ m₁ δ∅
      Q₂   = as-poly-map τ m₂ δ∅
      Q₃   = as-poly-map τ m₃ δ∅
      Q₄   = as-poly-map τ m₄ δ∅
      Q₅   = as-poly-map (sub (sub-lift σ) τ) m₅ δ∅
      Q₆   = as-poly-map (sub (sub-lift σ) τ) m₆ δ∅
      Q₇   = as-poly-map (sub (sub-lift σ) τ) mk δ∅
      eq3 : ∀ i → (m₂ i ∘ m₁ i) ≈ m₃ i
      eq3 i = ≈-trans (concat-mor-comp (λ i → id (extend δ∅ X' i)) ek gs' (λ i → id (⟦ σ i ⟧ty δ)) i)
                      (concat-mor-unit {n = 1} ek gs' i)
      step3 : (Q₂ ∘ Q₁) ≈ Q₃
      step3 = ≈-trans (as-poly-map-comp τ m₂ m₁ δ∅) (as-poly-map-cong τ eq3 δ∅)
      step4 : (Q₃ ∘ Rs) ≈ (T' ∘ Q₄)
      step4 = ≈-trans (as-poly-map-comp τ m₃ (λ i → ≡-to-⇒ (sub-lift-pw σ δ X i)) δ∅)
                      (≈-trans (as-poly-map-cong τ (sub-lift-pw-natural σ gs k) δ∅)
                               (≈-sym (as-poly-map-comp τ (λ i → ≡-to-⇒ (sub-lift-pw σ δ' X' i)) m₄ δ∅)))
      eq5 : ∀ i → (m₅ i ∘ m₆ i) ≈ mk i
      eq5 i = ≈-trans (concat-mor-comp (λ i → id (extend δ∅ X' i)) ek gs (λ i → id (δ i)) i)
                      (concat-mor-unit {n = 1} ek gs i)
      step5 : Q₇ ≈ (Q₅ ∘ Q₆)
      step5 = ≈-sym (≈-trans (as-poly-map-comp (sub (sub-lift σ) τ) m₅ m₆ δ∅) (as-poly-map-cong (sub (sub-lift σ) τ) eq5 δ∅))

  subst-fwd-body-carrier : ∀ {Δ Δ'} (σ : TySub Δ Δ') (τ : type (suc Δ)) (δ : Fin Δ' → obj) {X X' : obj} (k : X ⇒ X') →
                           (fmor (as-poly {Δ} {1} τ (λ i → ⟦ σ i ⟧ty δ)) (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k)
                              ∘ subst-fwd-body σ τ δ X)
                             ≈ (subst-fwd-body σ τ δ X'
                                ∘ fmor (as-poly {Δ'} {1} (sub (sub-lift σ) τ) δ) (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k))
  subst-fwd-body-carrier {Δ} {Δ'} σ τ δ {X} {X'} k = begin
      F ∘ body
    ≈˘⟨ ≈-trans (∘-cong (≈-trans (as-poly-map-cong τ (λ i → as-poly-map-id (σ i) δ∅) (extend δ∅ X'))
                                 (as-poly-map-id τ (extend δ∅ X')))
                        ≈-refl)
                id-left ⟩
      as-poly-map {n = 1} τ (λ i → as-poly-map (σ i) (λ i → id (δ i)) δ∅) (extend δ∅ X') ∘ (F ∘ body)
    ≈˘⟨ assoc _ _ _ ⟩
      (as-poly-map {n = 1} τ (λ i → as-poly-map (σ i) (λ i → id (δ i)) δ∅) (extend δ∅ X') ∘ F) ∘ body
    ≈⟨ subst-fwd-body-natural σ τ (λ i → id (δ i)) k ⟩
      (body' ∘ as-poly-map {n = 1} (sub (sub-lift σ) τ) (λ i → id (δ i)) (extend δ∅ X')) ∘ Fp
    ≈⟨ ∘-cong (≈-trans (∘-cong ≈-refl (as-poly-map-id (sub (sub-lift σ) τ) (extend δ∅ X'))) id-right) ≈-refl ⟩
      body' ∘ Fp
    ∎
    where
      open ≈-Reasoning isEquiv
      F     = fmor (as-poly {Δ} {1} τ (λ i → ⟦ σ i ⟧ty δ)) (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k)
      Fp    = fmor (as-poly {Δ'} {1} (sub (sub-lift σ) τ) δ) (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k)
      body  = subst-fwd-body σ τ δ X
      body' = subst-fwd-body σ τ δ X'

  subst-fwd-body-applied : ∀ {Δ Δ'} (σ : TySub Δ Δ') (τ : type (suc Δ)) {δ δ' : Fin Δ' → obj} (gs : ∀ i → δ i ⇒ δ' i) (X : obj) →
                           (as-poly-map {n = 1} τ (λ i → as-poly-map (σ i) gs δ∅) (extend δ∅ X) ∘ subst-fwd-body σ τ δ X)
                             ≈ (subst-fwd-body σ τ δ' X ∘ as-poly-map {n = 1} (sub (sub-lift σ) τ) gs (extend δ∅ X))
  subst-fwd-body-applied {Δ} {Δ'} σ τ {δ} {δ'} gs X = begin
      pm ∘ body
    ≈˘⟨ ∘-cong (≈-trans (∘-cong ≈-refl (fmor-extend-id (as-poly {Δ} {1} τ (λ i → ⟦ σ i ⟧ty δ)) {δ = δ∅})) id-right) ≈-refl ⟩
      (pm ∘ fmor (as-poly {Δ} {1} τ (λ i → ⟦ σ i ⟧ty δ)) (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) (id X))) ∘ body
    ≈⟨ subst-fwd-body-natural σ τ gs (id X) ⟩
      (body' ∘ pm₁) ∘ fmor (as-poly {Δ'} {1} (sub (sub-lift σ) τ) δ) (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) (id X))
    ≈⟨ ≈-trans (∘-cong ≈-refl (fmor-extend-id (as-poly {Δ'} {1} (sub (sub-lift σ) τ) δ) {δ = δ∅})) id-right ⟩
      body' ∘ pm₁
    ∎
    where
      open ≈-Reasoning isEquiv
      pm    = as-poly-map {n = 1} τ (λ i → as-poly-map (σ i) gs δ∅) (extend δ∅ X)
      pm₁   = as-poly-map {n = 1} (sub (sub-lift σ) τ) gs (extend δ∅ X)
      body  = subst-fwd-body σ τ δ X
      body' = subst-fwd-body σ τ δ' X


sub-lift-pw-natural⁻ : ∀ {Δ Δ'} (σ : TySub Δ Δ') {δ δ' : Fin Δ' → obj} (gs : ∀ i → δ i ⇒ δ' i) {X X' : obj} (k : X ⇒ X')
                       (i : Fin (suc Δ)) →
                       (as-poly-map (sub-lift σ i) (concat-mor {n = 1} (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k) gs) δ∅
                          ∘ ≡-to-⇒ (sym (sub-lift-pw σ δ X i)))
                         ≈ (≡-to-⇒ (sym (sub-lift-pw σ δ' X' i))
                            ∘ concat-mor {n = 1} (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k) (λ i → as-poly-map (σ i) gs δ∅) i)
sub-lift-pw-natural⁻ σ {δ} {δ'} gs {X} {X'} k i =
  ≡-to-⇒-conj (sub-lift-pw σ δ X i) (sub-lift-pw σ δ' X' i) (sub-lift-pw-natural σ gs k i)

mutual
  subst-bwd-fwd : ∀ {Δ Δ'} (σ : TySub Δ Δ') (τ : type Δ) (δ : Fin Δ' → obj) → (subst-bwd σ τ δ ∘ subst-fwd σ τ δ) ≈ id _
  subst-bwd-fwd σ (var i)     δ = id-left
  subst-bwd-fwd σ unit        δ = id-left
  subst-bwd-fwd σ (base s)    δ = id-left
  subst-bwd-fwd σ (τ₁ [+] τ₂) δ = [+]-inv (subst-bwd-fwd σ τ₁ δ) (subst-bwd-fwd σ τ₂ δ)
  subst-bwd-fwd σ (τ₁ [×] τ₂) δ = [×]-inv (subst-bwd-fwd σ τ₁ δ) (subst-bwd-fwd σ τ₂ δ)
  subst-bwd-fwd σ (τ₁ [→] τ₂) δ = id-left
  subst-bwd-fwd {Δ} {Δ'} σ (μ τ) δ = begin
      μ-map A δ∅ P δ∅ (subst-bwd-body σ τ δ N) ∘ μ-map P δ∅ A δ∅ (subst-fwd-body σ τ δ M)
    ≈⟨ μ-map-comp P δ∅ A δ∅ P δ∅ (subst-fwd-body σ τ δ M) (subst-bwd-body σ τ δ N) (subst-fwd-body σ τ δ N)
                  (subst-fwd-body-carrier σ τ δ (μ-map A δ∅ P δ∅ (subst-bwd-body σ τ δ N))) ⟩
      μ-map P δ∅ P δ∅ (subst-bwd-body σ τ δ N ∘ subst-fwd-body σ τ δ N)
    ≈⟨ μ-map-cong _ _ _ _ (subst-body-bwd-fwd σ τ δ N) ⟩
      μ-map P δ∅ P δ∅ (id _)
    ≈⟨ μ-map-id P δ∅ ⟩
      id _
    ∎
    where
      open ≈-Reasoning isEquiv
      A = as-poly {Δ} {1} τ (λ i → ⟦ σ i ⟧ty δ)
      P = as-poly {Δ'} {1} (sub (sub-lift σ) τ) δ
      M = μ-obj A δ∅
      N = μ-obj P δ∅

  subst-fwd-bwd : ∀ {Δ Δ'} (σ : TySub Δ Δ') (τ : type Δ) (δ : Fin Δ' → obj) → (subst-fwd σ τ δ ∘ subst-bwd σ τ δ) ≈ id _
  subst-fwd-bwd σ (var i)     δ = id-left
  subst-fwd-bwd σ unit        δ = id-left
  subst-fwd-bwd σ (base s)    δ = id-left
  subst-fwd-bwd σ (τ₁ [+] τ₂) δ = [+]-inv (subst-fwd-bwd σ τ₁ δ) (subst-fwd-bwd σ τ₂ δ)
  subst-fwd-bwd σ (τ₁ [×] τ₂) δ = [×]-inv (subst-fwd-bwd σ τ₁ δ) (subst-fwd-bwd σ τ₂ δ)
  subst-fwd-bwd σ (τ₁ [→] τ₂) δ = id-left
  subst-fwd-bwd {Δ} {Δ'} σ (μ τ) δ = begin
      μ-map P δ∅ A δ∅ (subst-fwd-body σ τ δ M) ∘ μ-map A δ∅ P δ∅ (subst-bwd-body σ τ δ N)
    ≈⟨ μ-map-comp A δ∅ P δ∅ A δ∅ (subst-bwd-body σ τ δ N) (subst-fwd-body σ τ δ M) (subst-bwd-body σ τ δ M)
                  (subst-bwd-body-carrier σ τ δ (μ-map P δ∅ A δ∅ (subst-fwd-body σ τ δ M))) ⟩
      μ-map A δ∅ A δ∅ (subst-fwd-body σ τ δ M ∘ subst-bwd-body σ τ δ M)
    ≈⟨ μ-map-cong _ _ _ _ (subst-body-fwd-bwd σ τ δ M) ⟩
      μ-map A δ∅ A δ∅ (id _)
    ≈⟨ μ-map-id A δ∅ ⟩
      id _
    ∎
    where
      open ≈-Reasoning isEquiv
      A = as-poly {Δ} {1} τ (λ i → ⟦ σ i ⟧ty δ)
      P = as-poly {Δ'} {1} (sub (sub-lift σ) τ) δ
      M = μ-obj A δ∅
      N = μ-obj P δ∅

  subst-body-bwd-fwd : ∀ {Δ Δ'} (σ : TySub Δ Δ') (τ : type (suc Δ)) (δ : Fin Δ' → obj) (X : obj) →
                       (subst-bwd-body σ τ δ X ∘ subst-fwd-body σ τ δ X) ≈ id _
  subst-body-bwd-fwd σ τ δ X = begin
      (((af₂ ∘ S⁻) ∘ T⁻) ∘ ab₁) ∘ (((af₁ ∘ Rs) ∘ S) ∘ ab₂)
    ≈⟨ ∘-cong ≈-refl (≈-trans (assoc _ _ _) (assoc _ _ _)) ⟩
      (((af₂ ∘ S⁻) ∘ T⁻) ∘ ab₁) ∘ (af₁ ∘ (Rs ∘ (S ∘ ab₂)))
    ≈˘⟨ assoc _ _ _ ⟩
      ((((af₂ ∘ S⁻) ∘ T⁻) ∘ ab₁) ∘ af₁) ∘ (Rs ∘ (S ∘ ab₂))
    ≈⟨ ∘-cong (≈-trans (assoc _ _ _) (≈-trans (∘-cong ≈-refl (apply-bwd-fwd {n = 1} τ (λ i → ⟦ σ i ⟧ty δ) (extend δ∅ X))) id-right)) ≈-refl ⟩
      ((af₂ ∘ S⁻) ∘ T⁻) ∘ (Rs ∘ (S ∘ ab₂))
    ≈˘⟨ assoc _ _ _ ⟩
      (((af₂ ∘ S⁻) ∘ T⁻) ∘ Rs) ∘ (S ∘ ab₂)
    ≈⟨ ∘-cong (≈-trans (assoc _ _ _) (≈-trans (∘-cong ≈-refl (as-poly-map-cast-inv τ (sub-lift-pw σ δ X) δ∅)) id-right)) ≈-refl ⟩
      (af₂ ∘ S⁻) ∘ (S ∘ ab₂)
    ≈˘⟨ assoc _ _ _ ⟩
      ((af₂ ∘ S⁻) ∘ S) ∘ ab₂
    ≈⟨ ∘-cong (≈-trans (assoc _ _ _) (≈-trans (∘-cong ≈-refl (subst-bwd-fwd (sub-lift σ) τ (concat (extend {0} δ∅ X) δ))) id-right)) ≈-refl ⟩
      af₂ ∘ ab₂
    ≈⟨ apply-fwd-bwd {n = 1} (sub (sub-lift σ) τ) δ (extend δ∅ X) ⟩
      id _
    ∎
    where
      open ≈-Reasoning isEquiv
      af₁ = apply-fwd {n = 1} τ (λ i → ⟦ σ i ⟧ty δ) (extend δ∅ X)
      ab₁ = apply-bwd {n = 1} τ (λ i → ⟦ σ i ⟧ty δ) (extend δ∅ X)
      af₂ = apply-fwd {n = 1} (sub (sub-lift σ) τ) δ (extend δ∅ X)
      ab₂ = apply-bwd {n = 1} (sub (sub-lift σ) τ) δ (extend δ∅ X)
      Rs  = as-poly-map τ (λ i → ≡-to-⇒ (sub-lift-pw σ δ X i)) δ∅
      T⁻  = as-poly-map τ (λ i → ≡-to-⇒ (sym (sub-lift-pw σ δ X i))) δ∅
      S   = subst-fwd (sub-lift σ) τ (concat (extend {0} δ∅ X) δ)
      S⁻  = subst-bwd (sub-lift σ) τ (concat (extend {0} δ∅ X) δ)

  subst-body-fwd-bwd : ∀ {Δ Δ'} (σ : TySub Δ Δ') (τ : type (suc Δ)) (δ : Fin Δ' → obj) (X : obj) →
                       (subst-fwd-body σ τ δ X ∘ subst-bwd-body σ τ δ X) ≈ id _
  subst-body-fwd-bwd σ τ δ X = begin
      (((af₁ ∘ Rs) ∘ S) ∘ ab₂) ∘ (((af₂ ∘ S⁻) ∘ T⁻) ∘ ab₁)
    ≈⟨ ∘-cong ≈-refl (≈-trans (assoc _ _ _) (assoc _ _ _)) ⟩
      (((af₁ ∘ Rs) ∘ S) ∘ ab₂) ∘ (af₂ ∘ (S⁻ ∘ (T⁻ ∘ ab₁)))
    ≈˘⟨ assoc _ _ _ ⟩
      ((((af₁ ∘ Rs) ∘ S) ∘ ab₂) ∘ af₂) ∘ (S⁻ ∘ (T⁻ ∘ ab₁))
    ≈⟨ ∘-cong (≈-trans (assoc _ _ _) (≈-trans (∘-cong ≈-refl (apply-bwd-fwd {n = 1} (sub (sub-lift σ) τ) δ (extend δ∅ X))) id-right)) ≈-refl ⟩
      ((af₁ ∘ Rs) ∘ S) ∘ (S⁻ ∘ (T⁻ ∘ ab₁))
    ≈˘⟨ assoc _ _ _ ⟩
      (((af₁ ∘ Rs) ∘ S) ∘ S⁻) ∘ (T⁻ ∘ ab₁)
    ≈⟨ ∘-cong (≈-trans (assoc _ _ _) (≈-trans (∘-cong ≈-refl (subst-fwd-bwd (sub-lift σ) τ (concat (extend {0} δ∅ X) δ))) id-right)) ≈-refl ⟩
      (af₁ ∘ Rs) ∘ (T⁻ ∘ ab₁)
    ≈˘⟨ assoc _ _ _ ⟩
      ((af₁ ∘ Rs) ∘ T⁻) ∘ ab₁
    ≈⟨ ∘-cong (≈-trans (assoc _ _ _) (≈-trans (∘-cong ≈-refl (as-poly-map-cast-inv' τ (sub-lift-pw σ δ X) δ∅)) id-right)) ≈-refl ⟩
      af₁ ∘ ab₁
    ≈⟨ apply-fwd-bwd {n = 1} τ (λ i → ⟦ σ i ⟧ty δ) (extend δ∅ X) ⟩
      id _
    ∎
    where
      open ≈-Reasoning isEquiv
      af₁ = apply-fwd {n = 1} τ (λ i → ⟦ σ i ⟧ty δ) (extend δ∅ X)
      ab₁ = apply-bwd {n = 1} τ (λ i → ⟦ σ i ⟧ty δ) (extend δ∅ X)
      af₂ = apply-fwd {n = 1} (sub (sub-lift σ) τ) δ (extend δ∅ X)
      ab₂ = apply-bwd {n = 1} (sub (sub-lift σ) τ) δ (extend δ∅ X)
      Rs  = as-poly-map τ (λ i → ≡-to-⇒ (sub-lift-pw σ δ X i)) δ∅
      T⁻  = as-poly-map τ (λ i → ≡-to-⇒ (sym (sub-lift-pw σ δ X i))) δ∅
      S   = subst-fwd (sub-lift σ) τ (concat (extend {0} δ∅ X) δ)
      S⁻  = subst-bwd (sub-lift σ) τ (concat (extend {0} δ∅ X) δ)

  subst-bwd-natural : ∀ {Δ Δ'} (σ : TySub Δ Δ') (τ : type Δ) {δ δ' : Fin Δ' → obj} (gs : ∀ i → δ i ⇒ δ' i) →
                      (as-poly-map (sub σ τ) gs δ∅ ∘ subst-bwd σ τ δ)
                        ≈ (subst-bwd σ τ δ' ∘ as-poly-map τ (λ i → as-poly-map (σ i) gs δ∅) δ∅)
  subst-bwd-natural σ τ {δ} {δ'} gs = begin
      pm ∘ sb
    ≈˘⟨ ≈-trans (∘-cong (subst-bwd-fwd σ τ δ') ≈-refl) id-left ⟩
      (sb' ∘ sf') ∘ (pm ∘ sb)
    ≈⟨ ≈-trans (assoc _ _ _) (∘-cong ≈-refl (≈-sym (assoc _ _ _))) ⟩
      sb' ∘ ((sf' ∘ pm) ∘ sb)
    ≈˘⟨ ∘-cong ≈-refl (∘-cong (subst-fwd-natural σ τ gs) ≈-refl) ⟩
      sb' ∘ ((pm' ∘ sf) ∘ sb)
    ≈⟨ ∘-cong ≈-refl (≈-trans (assoc _ _ _) (≈-trans (∘-cong ≈-refl (subst-fwd-bwd σ τ δ)) id-right)) ⟩
      sb' ∘ pm'
    ∎
    where
      open ≈-Reasoning isEquiv
      pm  = as-poly-map (sub σ τ) gs δ∅
      pm' = as-poly-map τ (λ i → as-poly-map (σ i) gs δ∅) δ∅
      sf  = subst-fwd σ τ δ
      sf' = subst-fwd σ τ δ'
      sb  = subst-bwd σ τ δ
      sb' = subst-bwd σ τ δ'

  subst-bwd-body-natural : ∀ {Δ Δ'} (σ : TySub Δ Δ') (τ : type (suc Δ)) {δ δ' : Fin Δ' → obj} (gs : ∀ i → δ i ⇒ δ' i)
                           {X X' : obj} (k : X ⇒ X') →
                           (as-poly-map {n = 1} (sub (sub-lift σ) τ) gs (extend δ∅ X')
                              ∘ fmor (as-poly {Δ'} {1} (sub (sub-lift σ) τ) δ) (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k)
                              ∘ subst-bwd-body σ τ δ X)
                             ≈ (subst-bwd-body σ τ δ' X'
                                ∘ as-poly-map {n = 1} τ (λ i → as-poly-map (σ i) gs δ∅) (extend δ∅ X')
                                ∘ fmor (as-poly {Δ} {1} τ (λ i → ⟦ σ i ⟧ty δ)) (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k))
  subst-bwd-body-natural {Δ} {Δ'} σ τ {δ} {δ'} gs {X} {X'} k = begin
      (pm₁ ∘ Fp) ∘ (((af₂ ∘ S⁻) ∘ T⁻) ∘ ab₁)
    ≈˘⟨ assoc _ _ _ ⟩
      ((pm₁ ∘ Fp) ∘ ((af₂ ∘ S⁻) ∘ T⁻)) ∘ ab₁
    ≈˘⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
      (((pm₁ ∘ Fp) ∘ (af₂ ∘ S⁻)) ∘ T⁻) ∘ ab₁
    ≈˘⟨ ∘-cong (∘-cong (assoc _ _ _) ≈-refl) ≈-refl ⟩
      ((((pm₁ ∘ Fp) ∘ af₂) ∘ S⁻) ∘ T⁻) ∘ ab₁
    ≈⟨ ∘-cong (∘-cong (∘-cong (assoc _ _ _) ≈-refl) ≈-refl) ≈-refl ⟩
      (((pm₁ ∘ (Fp ∘ af₂)) ∘ S⁻) ∘ T⁻) ∘ ab₁
    ≈⟨ ∘-cong (∘-cong (∘-cong (∘-cong ≈-refl (apply-fwd-natural {n = 1} (sub (sub-lift σ) τ) δ ek)) ≈-refl) ≈-refl) ≈-refl ⟩
      (((pm₁ ∘ (af₂' ∘ Q₆)) ∘ S⁻) ∘ T⁻) ∘ ab₁
    ≈˘⟨ ∘-cong (∘-cong (∘-cong (assoc _ _ _) ≈-refl) ≈-refl) ≈-refl ⟩
      ((((pm₁ ∘ af₂') ∘ Q₆) ∘ S⁻) ∘ T⁻) ∘ ab₁
    ≈˘⟨ ∘-cong (∘-cong (∘-cong (∘-cong (apply-fwd-map {n = 1} (sub (sub-lift σ) τ) gs (extend δ∅ X')) ≈-refl) ≈-refl) ≈-refl) ≈-refl ⟩
      ((((af₂'' ∘ Q₅) ∘ Q₆) ∘ S⁻) ∘ T⁻) ∘ ab₁
    ≈⟨ ∘-cong (∘-cong (∘-cong (assoc _ _ _) ≈-refl) ≈-refl) ≈-refl ⟩
      (((af₂'' ∘ (Q₅ ∘ Q₆)) ∘ S⁻) ∘ T⁻) ∘ ab₁
    ≈⟨ ∘-cong (∘-cong (∘-cong (∘-cong ≈-refl step5) ≈-refl) ≈-refl) ≈-refl ⟩
      (((af₂'' ∘ Q₇) ∘ S⁻) ∘ T⁻) ∘ ab₁
    ≈⟨ ∘-cong (∘-cong (assoc _ _ _) ≈-refl) ≈-refl ⟩
      ((af₂'' ∘ (Q₇ ∘ S⁻)) ∘ T⁻) ∘ ab₁
    ≈⟨ ∘-cong (∘-cong (∘-cong ≈-refl (subst-bwd-natural (sub-lift σ) τ mk)) ≈-refl) ≈-refl ⟩
      ((af₂'' ∘ (S⁻' ∘ Q₄)) ∘ T⁻) ∘ ab₁
    ≈˘⟨ ∘-cong (∘-cong (assoc _ _ _) ≈-refl) ≈-refl ⟩
      (((af₂'' ∘ S⁻') ∘ Q₄) ∘ T⁻) ∘ ab₁
    ≈⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
      ((af₂'' ∘ S⁻') ∘ (Q₄ ∘ T⁻)) ∘ ab₁
    ≈⟨ ∘-cong (∘-cong ≈-refl step4) ≈-refl ⟩
      ((af₂'' ∘ S⁻') ∘ (T⁻' ∘ Q₃)) ∘ ab₁
    ≈˘⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
      (((af₂'' ∘ S⁻') ∘ T⁻') ∘ Q₃) ∘ ab₁
    ≈⟨ assoc _ _ _ ⟩
      ((af₂'' ∘ S⁻') ∘ T⁻') ∘ (Q₃ ∘ ab₁)
    ≈˘⟨ ∘-cong ≈-refl (∘-cong step3 ≈-refl) ⟩
      ((af₂'' ∘ S⁻') ∘ T⁻') ∘ ((Q₂ ∘ Q₁) ∘ ab₁)
    ≈⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
      ((af₂'' ∘ S⁻') ∘ T⁻') ∘ (Q₂ ∘ (Q₁ ∘ ab₁))
    ≈˘⟨ ∘-cong ≈-refl (∘-cong ≈-refl (apply-bwd-natural {n = 1} τ (λ i → ⟦ σ i ⟧ty δ) ek)) ⟩
      ((af₂'' ∘ S⁻') ∘ T⁻') ∘ (Q₂ ∘ (ab₁' ∘ F))
    ≈˘⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
      ((af₂'' ∘ S⁻') ∘ T⁻') ∘ ((Q₂ ∘ ab₁') ∘ F)
    ≈˘⟨ ∘-cong ≈-refl (∘-cong (apply-bwd-map {n = 1} τ gs' (extend δ∅ X')) ≈-refl) ⟩
      ((af₂'' ∘ S⁻') ∘ T⁻') ∘ ((ab₁'' ∘ pm) ∘ F)
    ≈⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
      ((af₂'' ∘ S⁻') ∘ T⁻') ∘ (ab₁'' ∘ (pm ∘ F))
    ≈˘⟨ assoc _ _ _ ⟩
      (((af₂'' ∘ S⁻') ∘ T⁻') ∘ ab₁'') ∘ (pm ∘ F)
    ≈˘⟨ assoc _ _ _ ⟩
      ((((af₂'' ∘ S⁻') ∘ T⁻') ∘ ab₁'') ∘ pm) ∘ F
    ∎
    where
      open ≈-Reasoning isEquiv
      A    = as-poly {Δ} {1} τ (λ i → ⟦ σ i ⟧ty δ)
      P    = as-poly {Δ'} {1} (sub (sub-lift σ) τ) δ
      gs'  : ∀ i → ⟦ σ i ⟧ty δ ⇒ ⟦ σ i ⟧ty δ'
      gs' i = as-poly-map (σ i) gs δ∅
      ek   = extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k
      mk   = concat-mor {n = 1} ek gs
      pm   = as-poly-map {n = 1} τ gs' (extend δ∅ X')
      pm₁  = as-poly-map {n = 1} (sub (sub-lift σ) τ) gs (extend δ∅ X')
      F    = fmor A ek
      Fp   = fmor P ek
      af₂   = apply-fwd {n = 1} (sub (sub-lift σ) τ) δ (extend δ∅ X)
      af₂'  = apply-fwd {n = 1} (sub (sub-lift σ) τ) δ (extend δ∅ X')
      af₂'' = apply-fwd {n = 1} (sub (sub-lift σ) τ) δ' (extend δ∅ X')
      ab₁   = apply-bwd {n = 1} τ (λ i → ⟦ σ i ⟧ty δ) (extend δ∅ X)
      ab₁'  = apply-bwd {n = 1} τ (λ i → ⟦ σ i ⟧ty δ) (extend δ∅ X')
      ab₁'' = apply-bwd {n = 1} τ (λ i → ⟦ σ i ⟧ty δ') (extend δ∅ X')
      T⁻   = as-poly-map τ (λ i → ≡-to-⇒ (sym (sub-lift-pw σ δ X i))) δ∅
      T⁻'  = as-poly-map τ (λ i → ≡-to-⇒ (sym (sub-lift-pw σ δ' X' i))) δ∅
      S⁻   = subst-bwd (sub-lift σ) τ (concat (extend {0} δ∅ X) δ)
      S⁻'  = subst-bwd (sub-lift σ) τ (concat (extend {0} δ∅ X') δ')
      m₁   = concat-mor {n = 1} ek (λ i → id (⟦ σ i ⟧ty δ))
      m₂   = concat-mor {n = 1} (λ i → id (extend δ∅ X' i)) gs'
      m₃   = concat-mor {n = 1} ek gs'
      m₄   : ∀ i → ⟦ sub-lift σ i ⟧ty (concat (extend {0} δ∅ X) δ) ⇒ ⟦ sub-lift σ i ⟧ty (concat (extend {0} δ∅ X') δ')
      m₄ i = as-poly-map (sub-lift σ i) mk δ∅
      m₅   = concat-mor {n = 1} (λ i → id (extend δ∅ X' i)) gs
      m₆   = concat-mor {n = 1} ek (λ i → id (δ i))
      Q₁   = as-poly-map τ m₁ δ∅
      Q₂   = as-poly-map τ m₂ δ∅
      Q₃   = as-poly-map τ m₃ δ∅
      Q₄   = as-poly-map τ m₄ δ∅
      Q₅   = as-poly-map (sub (sub-lift σ) τ) m₅ δ∅
      Q₆   = as-poly-map (sub (sub-lift σ) τ) m₆ δ∅
      Q₇   = as-poly-map (sub (sub-lift σ) τ) mk δ∅
      eq3 : ∀ i → (m₂ i ∘ m₁ i) ≈ m₃ i
      eq3 i = ≈-trans (concat-mor-comp (λ i → id (extend δ∅ X' i)) ek gs' (λ i → id (⟦ σ i ⟧ty δ)) i)
                      (concat-mor-unit {n = 1} ek gs' i)
      step3 : (Q₂ ∘ Q₁) ≈ Q₃
      step3 = ≈-trans (as-poly-map-comp τ m₂ m₁ δ∅) (as-poly-map-cong τ eq3 δ∅)
      step4 : (Q₄ ∘ T⁻) ≈ (T⁻' ∘ Q₃)
      step4 = ≈-trans (as-poly-map-comp τ m₄ (λ i → ≡-to-⇒ (sym (sub-lift-pw σ δ X i))) δ∅)
                      (≈-trans (as-poly-map-cong τ (sub-lift-pw-natural⁻ σ gs k) δ∅)
                               (≈-sym (as-poly-map-comp τ (λ i → ≡-to-⇒ (sym (sub-lift-pw σ δ' X' i))) m₃ δ∅)))
      eq5 : ∀ i → (m₅ i ∘ m₆ i) ≈ mk i
      eq5 i = ≈-trans (concat-mor-comp (λ i → id (extend δ∅ X' i)) ek gs (λ i → id (δ i)) i)
                      (concat-mor-unit {n = 1} ek gs i)
      step5 : (Q₅ ∘ Q₆) ≈ Q₇
      step5 = ≈-trans (as-poly-map-comp (sub (sub-lift σ) τ) m₅ m₆ δ∅) (as-poly-map-cong (sub (sub-lift σ) τ) eq5 δ∅)

  subst-bwd-body-carrier : ∀ {Δ Δ'} (σ : TySub Δ Δ') (τ : type (suc Δ)) (δ : Fin Δ' → obj) {X X' : obj} (k : X ⇒ X') →
                           (fmor (as-poly {Δ'} {1} (sub (sub-lift σ) τ) δ) (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k)
                              ∘ subst-bwd-body σ τ δ X)
                             ≈ (subst-bwd-body σ τ δ X'
                                ∘ fmor (as-poly {Δ} {1} τ (λ i → ⟦ σ i ⟧ty δ)) (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k))
  subst-bwd-body-carrier {Δ} {Δ'} σ τ δ {X} {X'} k = begin
      Fp ∘ body
    ≈˘⟨ ≈-trans (∘-cong (as-poly-map-id (sub (sub-lift σ) τ) (extend δ∅ X')) ≈-refl) id-left ⟩
      as-poly-map {n = 1} (sub (sub-lift σ) τ) (λ i → id (δ i)) (extend δ∅ X') ∘ (Fp ∘ body)
    ≈˘⟨ assoc _ _ _ ⟩
      (as-poly-map {n = 1} (sub (sub-lift σ) τ) (λ i → id (δ i)) (extend δ∅ X') ∘ Fp) ∘ body
    ≈⟨ subst-bwd-body-natural σ τ (λ i → id (δ i)) k ⟩
      (body' ∘ as-poly-map {n = 1} τ (λ i → as-poly-map (σ i) (λ i → id (δ i)) δ∅) (extend δ∅ X')) ∘ F
    ≈⟨ ∘-cong (≈-trans (∘-cong ≈-refl (≈-trans (as-poly-map-cong τ (λ i → as-poly-map-id (σ i) δ∅) (extend δ∅ X'))
                                                 (as-poly-map-id τ (extend δ∅ X'))))
                       id-right)
              ≈-refl ⟩
      body' ∘ F
    ∎
    where
      open ≈-Reasoning isEquiv
      F     = fmor (as-poly {Δ} {1} τ (λ i → ⟦ σ i ⟧ty δ)) (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k)
      Fp    = fmor (as-poly {Δ'} {1} (sub (sub-lift σ) τ) δ) (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k)
      body  = subst-bwd-body σ τ δ X
      body' = subst-bwd-body σ τ δ X'


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
