{-# OPTIONS --prop --postfix-projections --safe #-}

-- The type layer of the interpretation: a type becomes a polynomial with its variables at the
-- environment, μ-types the carriers, and the comparison maps that relate interpreting a renamed or
-- substituted type to interpreting the type in the renamed or substituted environment.

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

module language-type-interpretation
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

-- The lifting again, bound here rather than in the telescope: names opened through a module the
-- telescope binds by let do not re-export.
module Fam = fam-mu-lifting os es CM BP 𝟙c

open Fam using (Obj; Lf; Lf-map; Lf-map-cong; Lf-map-id; Lf-map-comp; injF; injF-natural;
                strong-Lf-map; strong-Lf-map-cong; strong-Lf-map-comp; strong-Lf-map-p₂;
                strong-Lf-map-pre; strong-Lf-map-post; strong-Lf-map-injF;
                extend; extend-mor; fobj; HasMu; hasMu; HasMuLaws; hasMuLaws; _∘co_;
                Section; elimF; scale-section; Lf-section; coprod-section; prod-section; PolySection;
                poly-section; extend-section; preserves-section; preserves-section-id;
                preserves-section-∘; preserves-section-resp; preserves-section-inv;
                preserves-coprod-m; preserves-prod-m; preserves-Lf-map; preserves-scale;
                preserves-inMap; preserves-outMor) public
open Fam.WithTerminal T
  using (fmor; μ-map;
         fmor-cong; fmor-id; fmor-comp; fmor-const; fmor-var; fmor-+; fmor-×; fmor-μ;
         μ-map-cong; μ-map-id; μ-map-in; μ-map-comp; strong-fmor-weaken; μ-map-weaken; preserves-μ-map) public
open Category Fam.cat public
open HasTerminal (Fam.terminal T) renaming (witness to 𝟙) public
open HasProducts Fam.products renaming (pair to ⟨_,_⟩) public

open HasCoproducts Fam.coproducts using (coprod; coprod-m; coprod-m-cong; coprod-m-comp; coprod-m-id; in₁; in₂;
                                         copair-cong; copair-in₁; copair-in₂; copair-ext) public
open HasStrongCoproducts Fam.strongCoproducts
  using () renaming (copair to scopair; copair-cong to scopair-cong;
                     copair-in₁ to scopair-in₁; copair-in₂ to scopair-in₂;
                     copair-ext to scopair-ext; copair-ext0 to scopair-ext0) public
open HasExponentials 𝒞E using (lambda; eval) renaming (exp to _⟦→⟧_) public
open language-syntax Sig public
import language-operational.type-substitution
open language-operational.type-substitution Sig using (unfold₁-sub; unfold₁; unfold₁-inst; ren-ren; sub-ren; ren-sub; sub-sub; sub-id; sub-ren-comm) public
open HasMu hasMu public
open HasMuLaws hasMuLaws
  using (⦅⦆-cong; ⦅⦆-β; ⦅⦆-reflect; fusion; ∘co-push; copair-comp;
         strong-fmor-comp; strong-fmor-cong; strong-fmor-p₂; strong-extend-mor-comp) public

module CoK {Γ' : Obj} = Category (coKleisli-prod Fam.products Γ')
open Model Int public

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

as-poly-section : ∀ {Δ n} (τ : type (n + Δ)) (δ : Fin Δ → obj) → (∀ i → Section (δ i)) →
                PolySection (as-poly {Δ} {n} τ δ)
as-poly-section (var i)   δ δc = as-poly-var-section δ δc (splitAt _ i)
as-poly-section unit      δ δc = 𝟙ty-section
as-poly-section (base s)  δ δc = sort-section s
as-poly-section (σ [+] τ) δ δc = DP._,_ (as-poly-section σ δ δc) (as-poly-section τ δ δc)
as-poly-section (σ [×] τ) δ δc = DP._,_ (as-poly-section σ δ δc) (as-poly-section τ δ δc)
as-poly-section (σ [→] τ) δ δc = Lf-section exp-section
as-poly-section (μ τ)     δ δc = as-poly-section τ δ δc

unit-section : ∀ {Δ} (τ : type Δ) (δ : Fin Δ → obj) → (∀ i → Section (δ i)) → Section (⟦ τ ⟧ty δ)
unit-section τ δ δc = R.poly-section (as-poly τ δ) (as-poly-section τ δ δc) (λ ())

ctrl-dep : ∀ (τ : type 0) → Section (⟦ τ ⟧ty (λ ()))
ctrl-dep τ = scale-section ctrl-w (unit-section τ (λ ()) (λ ()))

concat : ∀ {n Δ} → (Fin n → obj) → (Fin Δ → obj) → Fin (n + Δ) → obj
concat {n} δ₀ δ i = [ δ₀ , δ ] (splitAt n i)

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

[+]-map-in₁ : ∀ {A A' B B' : obj} (f : A ⇒ A') (g : B ⇒ B') → ([+]-map f g ∘ in₁) ≈ (in₁ ∘ Lf-map f)
[+]-map-in₁ f g = copair-in₁ _ _

[+]-map-in₂ : ∀ {A A' B B' : obj} (f : A ⇒ A') (g : B ⇒ B') → ([+]-map f g ∘ in₂) ≈ (in₂ ∘ Lf-map g)
[+]-map-in₂ f g = copair-in₂ _ _

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

strong-as-poly-map-comp : ∀ {Δ n} (τ : type (n + Δ)) {Γ' : Obj} {δ δ' δ'' : Fin Δ → obj}
  (hs' : ∀ i → prod Γ' (δ' i) ⇒ δ'' i) (hs : ∀ i → prod Γ' (δ i) ⇒ δ' i) (δ₀ : Fin n → obj) →
  (strong-as-poly-map τ hs' δ₀ ∘co strong-as-poly-map τ hs δ₀)
    ≈ strong-as-poly-map τ (λ i → hs' i ∘co hs i) δ₀
strong-as-poly-map-comp {n = n} (var i) hs' hs δ₀ with splitAt n i
... | inj₁ j = CoK.id-left
... | inj₂ k = ≈-refl
strong-as-poly-map-comp unit      hs' hs δ₀ = CoK.id-left
strong-as-poly-map-comp (base s)  hs' hs δ₀ = CoK.id-left
strong-as-poly-map-comp (σ [+] τ) hs' hs δ₀ =
  ≈-trans (copair-comp _ _ _ _)
    (scopair-cong
      (∘-cong ≈-refl (≈-trans (strong-Lf-map-comp _ _)
                        (strong-Lf-map-cong (strong-as-poly-map-comp σ hs' hs δ₀))))
      (∘-cong ≈-refl (≈-trans (strong-Lf-map-comp _ _)
                        (strong-Lf-map-cong (strong-as-poly-map-comp τ hs' hs δ₀)))))
strong-as-poly-map-comp (σ [×] τ) hs' hs δ₀ =
  ≈-trans (strong-Lf-map-comp _ _)
    (strong-Lf-map-cong (≈-trans (strong-prod-m-comp _ _ _ _)
      (strong-prod-m-cong (strong-as-poly-map-comp σ hs' hs δ₀)
                          (strong-as-poly-map-comp τ hs' hs δ₀))))
strong-as-poly-map-comp (σ [→] τ) hs' hs δ₀ = CoK.id-left
strong-as-poly-map-comp {Δ} {n} (μ τ) {Γ'} {δ} {δ'} {δ''} hs' hs δ₀ =
  fusion {P = P} {δ = δ₀} (inMap Q' δ₀ ∘ SA₁) (inMap Q'' δ₀ ∘ SA₁₂) Sμ'' prem
  where
  P : Poly R.cat (suc n)
  P = as-poly {Δ} {suc n} τ δ
  Q' : Poly R.cat (suc n)
  Q' = as-poly {Δ} {suc n} τ δ'
  Q'' : Poly R.cat (suc n)
  Q'' = as-poly {Δ} {suc n} τ δ''
  M'  = μ-obj Q' δ₀
  M'' = μ-obj Q'' δ₀
  SA₁ : prod Γ' (fobj μ-obj P (extend δ₀ M')) ⇒ fobj μ-obj Q' (extend δ₀ M')
  SA₁ = strong-as-poly-map τ hs (extend δ₀ M')
  SA₁'' : prod Γ' (fobj μ-obj P (extend δ₀ M'')) ⇒ fobj μ-obj Q' (extend δ₀ M'')
  SA₁'' = strong-as-poly-map τ hs (extend δ₀ M'')
  SA₂ : prod Γ' (fobj μ-obj Q' (extend δ₀ M'')) ⇒ fobj μ-obj Q'' (extend δ₀ M'')
  SA₂ = strong-as-poly-map τ hs' (extend δ₀ M'')
  SA₁₂ : prod Γ' (fobj μ-obj P (extend δ₀ M'')) ⇒ fobj μ-obj Q'' (extend δ₀ M'')
  SA₁₂ = strong-as-poly-map τ (λ i → hs' i ∘co hs i) (extend δ₀ M'')
  Sμ'' : prod Γ' M' ⇒ M''
  Sμ'' = ⦅ inMap Q'' δ₀ ∘ SA₂ ⦆

  prem : (Sμ'' ∘co (inMap Q' δ₀ ∘ SA₁))
           ≈ ((inMap Q'' δ₀ ∘ SA₁₂) ∘co strong-fmor P (strong-extend-mor (λ i → p₂) Sμ''))
  prem = begin
      Sμ'' ∘co (inMap Q' δ₀ ∘ SA₁)
    ≈˘⟨ ∘co-push Sμ'' (inMap Q' δ₀) SA₁ ⟩
      (Sμ'' ∘co (inMap Q' δ₀ ∘ p₂)) ∘co SA₁
    ≈⟨ CoK.∘-cong (⦅⦆-β {P = Q'} {δ = δ₀} (inMap Q'' δ₀ ∘ SA₂)) ≈-refl ⟩
      ((inMap Q'' δ₀ ∘ SA₂) ∘co strong-fmor Q' (strong-extend-mor (λ i → p₂) Sμ'')) ∘co SA₁
    ≈⟨ CoK.assoc _ _ _ ⟩
      (inMap Q'' δ₀ ∘ SA₂) ∘co (strong-fmor Q' (strong-extend-mor (λ i → p₂) Sμ'') ∘co SA₁)
    ≈⟨ CoK.∘-cong ≈-refl (strong-as-poly-map-natural {n = suc n} τ hs (strong-extend-mor (λ i → p₂) Sμ'')) ⟩
      (inMap Q'' δ₀ ∘ SA₂) ∘co (SA₁'' ∘co strong-fmor P (strong-extend-mor (λ i → p₂) Sμ''))
    ≈˘⟨ CoK.assoc _ _ _ ⟩
      ((inMap Q'' δ₀ ∘ SA₂) ∘co SA₁'') ∘co strong-fmor P (strong-extend-mor (λ i → p₂) Sμ'')
    ≈⟨ CoK.∘-cong (≈-trans (assoc _ _ _)
         (∘-cong ≈-refl (strong-as-poly-map-comp {n = suc n} τ hs' hs (extend δ₀ M'')))) ≈-refl ⟩
      (inMap Q'' δ₀ ∘ SA₁₂) ∘co strong-fmor P (strong-extend-mor (λ i → p₂) Sμ'')
    ∎
    where open ≈-Reasoning isEquiv

strong-as-poly-map-p₂ : ∀ {Δ n} (τ : type (n + Δ)) {Γ' : Obj} {δ : Fin Δ → obj} (δ₀ : Fin n → obj) →
                        strong-as-poly-map τ {Γ'} {δ} {δ} (λ i → p₂) δ₀ ≈ p₂
strong-as-poly-map-p₂ {n = n} (var i) δ₀ with splitAt n i
... | inj₁ j = ≈-refl
... | inj₂ k = ≈-refl
strong-as-poly-map-p₂ unit      δ₀ = ≈-refl
strong-as-poly-map-p₂ (base s)  δ₀ = ≈-refl
strong-as-poly-map-p₂ (σ [+] τ) δ₀ =
  ≈-trans (scopair-cong (∘-cong ≈-refl (≈-trans (strong-Lf-map-cong (strong-as-poly-map-p₂ σ δ₀)) strong-Lf-map-p₂))
                        (∘-cong ≈-refl (≈-trans (strong-Lf-map-cong (strong-as-poly-map-p₂ τ δ₀)) strong-Lf-map-p₂)))
          scopair-ext0
strong-as-poly-map-p₂ (σ [×] τ) δ₀ =
  ≈-trans (strong-Lf-map-cong (≈-trans (strong-prod-m-cong (strong-as-poly-map-p₂ σ δ₀) (strong-as-poly-map-p₂ τ δ₀))
                                 (≈-trans (pair-cong (pair-p₂ _ _) (pair-p₂ _ _)) (pair-ext _))))
          strong-Lf-map-p₂
strong-as-poly-map-p₂ (σ [→] τ) δ₀ = ≈-refl
strong-as-poly-map-p₂ {Δ} {n} (μ τ) {Γ'} {δ} δ₀ =
  ≈-trans (⦅⦆-cong (as-poly {Δ} {suc n} τ δ) δ₀
            (∘-cong ≈-refl (strong-as-poly-map-p₂ {n = suc n} τ _)))
          (⦅⦆-reflect (as-poly {Δ} {suc n} τ δ) δ₀)

scopair-weaken : ∀ {Γ' : Obj} {x x' y y' : obj} (u : x ⇒ x') (v : y ⇒ y') →
                 scopair {w = Γ'} (in₁ ∘ (u ∘ p₂)) (in₂ ∘ (v ∘ p₂)) ≈ (coprod-m u v ∘ p₂)
scopair-weaken u v =
  ≈-trans (scopair-cong (≈-sym leg₁) (≈-sym leg₂)) (scopair-ext (coprod-m u v ∘ p₂))
  where
  leg₁ : ((coprod-m u v ∘ p₂) ∘ ⟨ p₁ , in₁ ∘ p₂ ⟩) ≈ (in₁ ∘ (u ∘ p₂))
  leg₁ = ≈-trans (assoc _ _ _)
         (≈-trans (∘-cong ≈-refl (pair-p₂ _ _))
         (≈-trans (≈-sym (assoc _ _ _))
         (≈-trans (∘-cong (copair-in₁ _ _) ≈-refl) (assoc _ _ _))))
  leg₂ : ((coprod-m u v ∘ p₂) ∘ ⟨ p₁ , in₂ ∘ p₂ ⟩) ≈ (in₂ ∘ (v ∘ p₂))
  leg₂ = ≈-trans (assoc _ _ _)
         (≈-trans (∘-cong ≈-refl (pair-p₂ _ _))
         (≈-trans (≈-sym (assoc _ _ _))
         (≈-trans (∘-cong (copair-in₂ _ _) ≈-refl) (assoc _ _ _))))

scopair-post : ∀ {Γ' : Obj} {x y z w : obj} (h : z ⇒ w) (a : prod Γ' x ⇒ z) (b : prod Γ' y ⇒ z) →
               (h ∘ scopair a b) ≈ scopair (h ∘ a) (h ∘ b)
scopair-post h a b =
  ≈-trans (≈-sym (scopair-ext (h ∘ scopair a b)))
          (scopair-cong (≈-trans (assoc _ _ _) (∘-cong ≈-refl (scopair-in₁ a b)))
                        (≈-trans (assoc _ _ _) (∘-cong ≈-refl (scopair-in₂ a b))))

co-unitₗ : ∀ {Γ' : Obj} {X Y : obj} (x : prod Γ' X ⇒ Y) → ((id _ ∘ p₂) ∘co x) ≈ x
co-unitₗ x = ≈-trans (∘-cong id-left ≈-refl) CoK.id-left

co-unitᵣ : ∀ {Γ' : Obj} {X Y : obj} (x : prod Γ' X ⇒ Y) → (x ∘co (id _ ∘ p₂)) ≈ x
co-unitᵣ x = ≈-trans (∘-cong ≈-refl (pair-cong ≈-refl id-left)) CoK.id-right

lift-comp : ∀ {Γ' : Obj} {X Y Z : obj} (f : Y ⇒ Z) (g : X ⇒ Y) →
            ((f ∘ g) ∘ p₂ {Γ'}) ≈ ((f ∘ p₂) ∘co (g ∘ p₂))
lift-comp f g =
  ≈-sym (≈-trans (assoc _ _ _) (≈-trans (∘-cong ≈-refl (pair-p₂ _ _)) (≈-sym (assoc _ _ _))))

sL-weaken : ∀ {Γ' : Obj} {X Y : obj} (c : X ⇒ Y) →
            strong-Lf-map {Γ'} (c ∘ p₂) ≈ (Lf-map c ∘ p₂)
sL-weaken c = ≈-trans (≈-sym (strong-Lf-map-post c p₂)) (∘-cong ≈-refl strong-Lf-map-p₂)

prod-m-weaken : ∀ {Γ' : Obj} {x₁ x₂ y₁ y₂ : obj} (a₁ : x₁ ⇒ y₁) (a₂ : x₂ ⇒ y₂) →
                strong-prod-m {w = Γ'} (a₁ ∘ p₂) (a₂ ∘ p₂) ≈ (prod-m a₁ a₂ ∘ p₂)
prod-m-weaken a₁ a₂ =
  ≈-trans (pair-cong (≈-trans (assoc _ _ _) (∘-cong ≈-refl (pair-p₂ _ _)))
                     (≈-trans (assoc _ _ _) (∘-cong ≈-refl (pair-p₂ _ _))))
  (≈-trans (pair-cong (≈-sym (assoc _ _ _)) (≈-sym (assoc _ _ _)))
           (≈-sym (pair-natural _ _ _)))

strong-as-poly-map-weaken : ∀ {Δ n} (τ : type (n + Δ)) {Γ' : Obj} {δ δ' : Fin Δ → obj}
                            (gs : ∀ i → δ i ⇒ δ' i) (δ₀ : Fin n → obj) →
                            strong-as-poly-map τ {Γ'} (λ i → gs i ∘ p₂) δ₀ ≈ (as-poly-map τ gs δ₀ ∘ p₂)
strong-as-poly-map-weaken {n = n} (var i) gs δ₀ with splitAt n i
... | inj₁ j = ≈-sym id-left
... | inj₂ k = ≈-refl
strong-as-poly-map-weaken unit      gs δ₀ = ≈-sym id-left
strong-as-poly-map-weaken (base s)  gs δ₀ = ≈-sym id-left
strong-as-poly-map-weaken (σ [→] τ) gs δ₀ = ≈-sym id-left
strong-as-poly-map-weaken (σ [+] τ) gs δ₀ =
  ≈-trans (scopair-cong
    (∘-cong ≈-refl (≈-trans (strong-Lf-map-cong (strong-as-poly-map-weaken σ gs δ₀))
                     (sL-weaken a₁)))
    (∘-cong ≈-refl (≈-trans (strong-Lf-map-cong (strong-as-poly-map-weaken τ gs δ₀))
                     (sL-weaken a₂))))
  (scopair-weaken (Lf-map a₁) (Lf-map a₂))
  where
  a₁ = as-poly-map σ gs δ₀
  a₂ = as-poly-map τ gs δ₀
strong-as-poly-map-weaken (σ [×] τ) gs δ₀ =
  ≈-trans (strong-Lf-map-cong
    (≈-trans (strong-prod-m-cong (strong-as-poly-map-weaken σ gs δ₀) (strong-as-poly-map-weaken τ gs δ₀))
             (prod-m-weaken a₁ a₂)))
  (sL-weaken (prod-m a₁ a₂))
  where
  a₁ = as-poly-map σ gs δ₀
  a₂ = as-poly-map τ gs δ₀
strong-as-poly-map-weaken {Δ} {n} (μ τ) {Γ'} {δ} {δ'} gs δ₀ =
  ≈-trans (⦅⦆-cong (as-poly {Δ} {suc n} τ δ) δ₀
            (≈-trans (∘-cong ≈-refl (strong-as-poly-map-weaken {n = suc n} τ gs
                                       (extend δ₀ (μ-obj (as-poly {Δ} {suc n} τ δ') δ₀))))
                     (≈-sym (assoc _ _ _))))
          (μ-map-weaken (as-poly {Δ} {suc n} τ δ) δ₀ (as-poly {Δ} {suc n} τ δ') δ₀
            (as-poly-map {n = suc n} τ gs (extend δ₀ (μ-obj (as-poly {Δ} {suc n} τ δ') δ₀))))

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

private
  cast-const : ∀ {n} {A A' : obj} (e : A ≡ A') (δ₀ : Fin n → obj) →
               cast {n} (cong Poly.const e) δ₀ ≈ ≡-to-⇒ e
  cast-const refl δ₀ = ≈-refl

cast-as-poly-cong : ∀ {Δ n} (τ : type (n + Δ)) {δ δ' : Fin Δ → obj} (h : ∀ i → δ i ≡ δ' i)
                    (δ₀ : Fin n → obj) →
                    cast (as-poly-cong τ h) δ₀ ≈ as-poly-map τ (λ i → ≡-to-⇒ (h i)) δ₀
cast-as-poly-cong {Δ} {n} (var i) h δ₀ with splitAt n i
... | inj₁ j = ≈-refl
... | inj₂ k = cast-const (h k) δ₀
cast-as-poly-cong unit      h δ₀ = ≈-refl
cast-as-poly-cong (base s)  h δ₀ = ≈-refl
cast-as-poly-cong (σ [+] τ) h δ₀ =
  ≈-trans (cast-+ (as-poly-cong σ h) (as-poly-cong τ h) δ₀)
          ([+]-map-cong (cast-as-poly-cong σ h δ₀) (cast-as-poly-cong τ h δ₀))
cast-as-poly-cong (σ [×] τ) h δ₀ =
  ≈-trans (cast-× (as-poly-cong σ h) (as-poly-cong τ h) δ₀)
          ([×]-map-cong (cast-as-poly-cong σ h δ₀) (cast-as-poly-cong τ h δ₀))
cast-as-poly-cong (σ [→] τ) h δ₀ = ≈-refl
cast-as-poly-cong {Δ} {n} (μ τ) {δ} {δ'} h δ₀ =
  ≈-trans (cast-μ (as-poly-cong {Δ} {suc n} τ h) δ₀)
          (μ-map-cong _ _ _ _ (cast-as-poly-cong {n = suc n} τ h (extend δ₀ (μ-obj (as-poly τ δ') δ₀))))

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

strong-concat-mor-split : ∀ {n Δ} {Γ' : Obj} {δ₀ δ₀' : Fin n → obj} {δ δ' : Fin Δ → obj} →
                          (∀ i → prod Γ' (δ₀ i) ⇒ δ₀' i) → (∀ i → prod Γ' (δ i) ⇒ δ' i) →
                          (s : Fin n ⊎ Fin Δ) → prod Γ' ([ δ₀ , δ ] s) ⇒ [ δ₀' , δ' ] s
strong-concat-mor-split fs gs (inj₁ j) = fs j
strong-concat-mor-split fs gs (inj₂ k) = gs k

strong-concat-mor : ∀ {n Δ} {Γ' : Obj} {δ₀ δ₀' : Fin n → obj} {δ δ' : Fin Δ → obj} →
                    (∀ i → prod Γ' (δ₀ i) ⇒ δ₀' i) → (∀ i → prod Γ' (δ i) ⇒ δ' i) →
                    ∀ i → prod Γ' (concat δ₀ δ i) ⇒ concat δ₀' δ' i
strong-concat-mor {n} fs gs i = strong-concat-mor-split fs gs (splitAt n i)

strong-concat-mor-p₂ : ∀ {n Δ} {Γ' : Obj} {δ₀ : Fin n → obj} {δ : Fin Δ → obj} (i : Fin (n + Δ)) →
                       strong-concat-mor {n} {Δ} {Γ'} {δ₀} {δ₀} {δ} {δ} (λ j → p₂) (λ j → p₂) i ≈ p₂
strong-concat-mor-p₂ {n} i with splitAt n i
... | inj₁ j = ≈-refl
... | inj₂ k = ≈-refl

lift-post : ∀ {Γ' : Obj} {X Y Z : obj} (b : Y ⇒ Z) (y : prod Γ' X ⇒ Y) →
            ((b ∘ p₂) ∘co y) ≈ (b ∘ y)
lift-post b y = ≈-trans (assoc _ _ _) (∘-cong ≈-refl (pair-p₂ _ _))

extend-mor-id : ∀ {k} {δ : Fin k → obj} {X : obj} (i : Fin (suc k)) → extend-mor (λ j → id (δ j)) (id X) i ≈ id _
extend-mor-id Fin.zero    = ≈-refl
extend-mor-id (Fin.suc i) = ≈-refl

strong-cast-natural : ∀ {n} {P P' : Poly R.cat n} (e : P ≡ P') {Γ' : Obj} {δ₀ δ₀' : Fin n → obj}
                      (fs : ∀ i → prod Γ' (δ₀ i) ⇒ δ₀' i) →
                      (strong-fmor P' fs ∘co (cast e δ₀ ∘ p₂)) ≈ ((cast e δ₀' ∘ p₂) ∘co strong-fmor P fs)
strong-cast-natural refl fs = ≈-trans (co-unitᵣ _) (≈-sym (co-unitₗ _))

strong-as-poly-map-ren : ∀ {Δ₁ Δ₂ n} (ρ : TyRen Δ₁ Δ₂) (τ : type (n + Δ₁)) {Γ' : Obj} {δ δ' : Fin Δ₂ → obj}
                         (gs : ∀ i → prod Γ' (δ i) ⇒ δ' i) (δ₀ : Fin n → obj) →
                         ((cast (as-poly-ren ρ τ δ') δ₀ ∘ p₂) ∘co strong-as-poly-map (extᵗⁿ n ρ *ᵗ τ) gs δ₀)
                           ≈ (strong-as-poly-map τ (λ i → gs (ρ i)) δ₀ ∘co (cast (as-poly-ren ρ τ δ) δ₀ ∘ p₂))
strong-as-poly-map-ren {n = n} ρ (var i) gs δ₀ with splitAt n i | splitAt n (extᵗⁿ n ρ i) | splitAt-extᵗⁿ n ρ i
... | inj₁ j | .(inj₁ j)     | refl =
  ≈-trans (≈-trans (∘-cong ≈-refl pair-ext0) id-right) (≈-sym (pair-p₂ _ _))
... | inj₂ k | .(inj₂ (ρ k)) | refl =
  ≈-trans (co-unitₗ (gs (ρ k))) (≈-sym (co-unitᵣ (gs (ρ k))))
strong-as-poly-map-ren ρ unit      gs δ₀ =
  ≈-trans (≈-trans (∘-cong ≈-refl pair-ext0) id-right) (≈-sym (pair-p₂ _ _))
strong-as-poly-map-ren ρ (base s)  gs δ₀ =
  ≈-trans (≈-trans (∘-cong ≈-refl pair-ext0) id-right) (≈-sym (pair-p₂ _ _))
strong-as-poly-map-ren ρ (σ [→] τ) gs δ₀ =
  ≈-trans (≈-trans (∘-cong ≈-refl pair-ext0) id-right) (≈-sym (pair-p₂ _ _))
strong-as-poly-map-ren {Δ₁} {Δ₂} {n} ρ (σ [+] τ) {Γ'} {δ} {δ'} gs δ₀ =
  ≈-trans (CoK.∘-cong (∘-cong (cast-+ (as-poly-ren ρ σ δ') (as-poly-ren ρ τ δ') δ₀) ≈-refl) ≈-refl)
  (≈-trans (CoK.∘-cong (≈-sym (scopair-weaken (Lf-map c₁') (Lf-map c₂'))) ≈-refl)
  (≈-trans (copair-comp _ _ _ _)
  (≈-trans (scopair-cong (∘-cong ≈-refl leg₁) (∘-cong ≈-refl leg₂))
           (≈-sym rhs-eq))))
  where
  c₁  = cast (as-poly-ren ρ σ δ) δ₀
  c₂  = cast (as-poly-ren ρ τ δ) δ₀
  c₁' = cast (as-poly-ren ρ σ δ') δ₀
  c₂' = cast (as-poly-ren ρ τ δ') δ₀
  S₁r = strong-as-poly-map (extᵗⁿ n ρ *ᵗ σ) gs δ₀
  S₂r = strong-as-poly-map (extᵗⁿ n ρ *ᵗ τ) gs δ₀
  S₁  = strong-as-poly-map σ (λ i → gs (ρ i)) δ₀
  S₂  = strong-as-poly-map τ (λ i → gs (ρ i)) δ₀
  leg₁ : ((Lf-map c₁' ∘ p₂) ∘co strong-Lf-map S₁r) ≈ (strong-Lf-map S₁ ∘co (Lf-map c₁ ∘ p₂))
  leg₁ = ≈-trans (CoK.∘-cong (≈-sym (sL-weaken c₁')) ≈-refl)
         (≈-trans (strong-Lf-map-comp _ _)
         (≈-trans (strong-Lf-map-cong (strong-as-poly-map-ren ρ σ gs δ₀))
         (≈-trans (≈-sym (strong-Lf-map-comp _ _))
                  (CoK.∘-cong ≈-refl (sL-weaken c₁)))))
  leg₂ : ((Lf-map c₂' ∘ p₂) ∘co strong-Lf-map S₂r) ≈ (strong-Lf-map S₂ ∘co (Lf-map c₂ ∘ p₂))
  leg₂ = ≈-trans (CoK.∘-cong (≈-sym (sL-weaken c₂')) ≈-refl)
         (≈-trans (strong-Lf-map-comp _ _)
         (≈-trans (strong-Lf-map-cong (strong-as-poly-map-ren ρ τ gs δ₀))
         (≈-trans (≈-sym (strong-Lf-map-comp _ _))
                  (CoK.∘-cong ≈-refl (sL-weaken c₂)))))
  rhs-eq : (scopair (in₁ ∘ strong-Lf-map S₁) (in₂ ∘ strong-Lf-map S₂) ∘co (cast (as-poly-ren ρ (σ [+] τ) δ) δ₀ ∘ p₂))
             ≈ scopair (in₁ ∘ (strong-Lf-map S₁ ∘co (Lf-map c₁ ∘ p₂))) (in₂ ∘ (strong-Lf-map S₂ ∘co (Lf-map c₂ ∘ p₂)))
  rhs-eq = ≈-trans (CoK.∘-cong ≈-refl (∘-cong (cast-+ (as-poly-ren ρ σ δ) (as-poly-ren ρ τ δ) δ₀) ≈-refl))
           (≈-trans (CoK.∘-cong ≈-refl (≈-sym (scopair-weaken (Lf-map c₁) (Lf-map c₂))))
                    (copair-comp _ _ _ _))
strong-as-poly-map-ren {Δ₁} {Δ₂} {n} ρ (σ [×] τ) {Γ'} {δ} {δ'} gs δ₀ =
  ≈-trans (CoK.∘-cong (∘-cong (cast-× (as-poly-ren ρ σ δ') (as-poly-ren ρ τ δ') δ₀) ≈-refl) ≈-refl)
  (≈-trans (CoK.∘-cong (≈-sym (sL-weaken (prod-m c₁' c₂'))) ≈-refl)
  (≈-trans (strong-Lf-map-comp _ _)
  (≈-trans (strong-Lf-map-cong inner)
  (≈-trans (≈-sym (strong-Lf-map-comp _ _))
  (≈-trans (CoK.∘-cong ≈-refl (sL-weaken (prod-m c₁ c₂)))
           (≈-sym (CoK.∘-cong ≈-refl (∘-cong (cast-× (as-poly-ren ρ σ δ) (as-poly-ren ρ τ δ) δ₀) ≈-refl))))))))
  where
  c₁  = cast (as-poly-ren ρ σ δ) δ₀
  c₂  = cast (as-poly-ren ρ τ δ) δ₀
  c₁' = cast (as-poly-ren ρ σ δ') δ₀
  c₂' = cast (as-poly-ren ρ τ δ') δ₀
  S₁r = strong-as-poly-map (extᵗⁿ n ρ *ᵗ σ) gs δ₀
  S₂r = strong-as-poly-map (extᵗⁿ n ρ *ᵗ τ) gs δ₀
  S₁  = strong-as-poly-map σ (λ i → gs (ρ i)) δ₀
  S₂  = strong-as-poly-map τ (λ i → gs (ρ i)) δ₀
  inner : ((prod-m c₁' c₂' ∘ p₂) ∘co strong-prod-m S₁r S₂r) ≈ (strong-prod-m S₁ S₂ ∘co (prod-m c₁ c₂ ∘ p₂))
  inner = ≈-trans (CoK.∘-cong (≈-sym (prod-m-weaken c₁' c₂')) ≈-refl)
          (≈-trans (strong-prod-m-comp _ _ _ _)
          (≈-trans (strong-prod-m-cong (strong-as-poly-map-ren ρ σ gs δ₀) (strong-as-poly-map-ren ρ τ gs δ₀))
          (≈-trans (≈-sym (strong-prod-m-comp _ _ _ _))
                   (CoK.∘-cong ≈-refl (prod-m-weaken c₁ c₂)))))
strong-as-poly-map-ren {Δ₁} {Δ₂} {n} ρ (μ τ) {Γ'} {δ} {δ'} gs δ₀ = main
  where
  Ar  = as-poly {Δ₂} {suc n} (extᵗⁿ (suc n) ρ *ᵗ τ) δ
  Ar' = as-poly {Δ₂} {suc n} (extᵗⁿ (suc n) ρ *ᵗ τ) δ'
  A   = as-poly {Δ₁} {suc n} τ (λ i → δ (ρ i))
  A'  = as-poly {Δ₁} {suc n} τ (λ i → δ' (ρ i))
  eq  = as-poly-ren ρ τ δ
  eq' = as-poly-ren ρ τ δ'
  MA  = μ-obj A δ₀
  MA' = μ-obj A' δ₀
  ce  = cast eq (extend δ₀ MA)
  ceM = cast eq (extend δ₀ MA')
  ce' = cast eq' (extend δ₀ MA')
  SAMr-M : prod Γ' (fobj μ-obj Ar (extend δ₀ (μ-obj Ar' δ₀))) ⇒ fobj μ-obj Ar' (extend δ₀ (μ-obj Ar' δ₀))
  SAMr-M = strong-as-poly-map {Δ₂} {suc n} (extᵗⁿ (suc n) ρ *ᵗ τ) gs (extend δ₀ (μ-obj Ar' δ₀))
  SAMr-A : prod Γ' (fobj μ-obj Ar (extend δ₀ MA')) ⇒ fobj μ-obj Ar' (extend δ₀ MA')
  SAMr-A = strong-as-poly-map {Δ₂} {suc n} (extᵗⁿ (suc n) ρ *ᵗ τ) gs (extend δ₀ MA')
  SAM-A : prod Γ' (fobj μ-obj A (extend δ₀ MA')) ⇒ fobj μ-obj A' (extend δ₀ MA')
  SAM-A = strong-as-poly-map {Δ₁} {suc n} τ (λ i → gs (ρ i)) (extend δ₀ MA')
  SAMμr : prod Γ' (μ-obj Ar δ₀) ⇒ μ-obj Ar' δ₀
  SAMμr = strong-as-poly-map {Δ₂} {n} (extᵗⁿ n ρ *ᵗ (μ τ)) gs δ₀
  SAMμA : prod Γ' MA ⇒ MA'
  SAMμA = strong-as-poly-map {Δ₁} {n} (μ τ) (λ i → gs (ρ i)) δ₀
  hL : prod Γ' (μ-obj Ar' δ₀) ⇒ MA'
  hL = ⦅_⦆ {P = Ar'} {δ = δ₀} ((inMap A' δ₀ ∘ ce') ∘ p₂)
  alg⋆ : prod Γ' (fobj μ-obj Ar (extend δ₀ MA')) ⇒ MA'
  alg⋆ = (inMap A' δ₀ ∘ SAM-A) ∘co (ceM ∘ p₂)

  step-mid : ((((inMap A' δ₀ ∘ ce') ∘ p₂) ∘co SAMr-A) ≈ alg⋆)
  step-mid = begin
      ((inMap A' δ₀ ∘ ce') ∘ p₂) ∘co SAMr-A
    ≈⟨ CoK.∘-cong (lift-comp (inMap A' δ₀) ce') ≈-refl ⟩
      ((inMap A' δ₀ ∘ p₂) ∘co (ce' ∘ p₂)) ∘co SAMr-A
    ≈⟨ CoK.assoc _ _ _ ⟩
      (inMap A' δ₀ ∘ p₂) ∘co ((ce' ∘ p₂) ∘co SAMr-A)
    ≈⟨ CoK.∘-cong ≈-refl (strong-as-poly-map-ren {n = suc n} ρ τ gs (extend δ₀ MA')) ⟩
      (inMap A' δ₀ ∘ p₂) ∘co (SAM-A ∘co (ceM ∘ p₂))
    ≈˘⟨ CoK.assoc _ _ _ ⟩
      ((inMap A' δ₀ ∘ p₂) ∘co SAM-A) ∘co (ceM ∘ p₂)
    ≈⟨ CoK.∘-cong (lift-post (inMap A' δ₀) SAM-A) ≈-refl ⟩
      (inMap A' δ₀ ∘ SAM-A) ∘co (ceM ∘ p₂)
    ∎
    where open ≈-Reasoning isEquiv

  premL : (hL ∘co (inMap Ar' δ₀ ∘ SAMr-M))
            ≈ (alg⋆ ∘co strong-fmor Ar (strong-extend-mor {δ = δ₀} {δ' = δ₀} (λ i → p₂) hL))
  premL = begin
      hL ∘co (inMap Ar' δ₀ ∘ SAMr-M)
    ≈˘⟨ ∘co-push hL (inMap Ar' δ₀) SAMr-M ⟩
      (hL ∘co (inMap Ar' δ₀ ∘ p₂)) ∘co SAMr-M
    ≈⟨ CoK.∘-cong (⦅⦆-β {P = Ar'} {δ = δ₀} ((inMap A' δ₀ ∘ ce') ∘ p₂)) ≈-refl ⟩
      ((((inMap A' δ₀ ∘ ce') ∘ p₂) ∘co strong-fmor Ar' (strong-extend-mor {δ = δ₀} {δ' = δ₀} (λ i → p₂) hL)) ∘co SAMr-M)
    ≈⟨ CoK.assoc _ _ _ ⟩
      (((inMap A' δ₀ ∘ ce') ∘ p₂) ∘co (strong-fmor Ar' (strong-extend-mor {δ = δ₀} {δ' = δ₀} (λ i → p₂) hL) ∘co SAMr-M))
    ≈⟨ CoK.∘-cong ≈-refl (strong-as-poly-map-natural {n = suc n} (extᵗⁿ (suc n) ρ *ᵗ τ) gs (strong-extend-mor {δ = δ₀} {δ' = δ₀} (λ i → p₂) hL)) ⟩
      (((inMap A' δ₀ ∘ ce') ∘ p₂) ∘co (SAMr-A ∘co strong-fmor Ar (strong-extend-mor {δ = δ₀} {δ' = δ₀} (λ i → p₂) hL)))
    ≈˘⟨ CoK.assoc _ _ _ ⟩
      ((((inMap A' δ₀ ∘ ce') ∘ p₂) ∘co SAMr-A) ∘co strong-fmor Ar (strong-extend-mor {δ = δ₀} {δ' = δ₀} (λ i → p₂) hL))
    ≈⟨ CoK.∘-cong step-mid ≈-refl ⟩
      alg⋆ ∘co strong-fmor Ar (strong-extend-mor {δ = δ₀} {δ' = δ₀} (λ i → p₂) hL)
    ∎
    where open ≈-Reasoning isEquiv

  premR : (SAMμA ∘co ((inMap A δ₀ ∘ ce) ∘ p₂))
            ≈ (alg⋆ ∘co strong-fmor Ar (strong-extend-mor {δ = δ₀} {δ' = δ₀} (λ i → p₂) SAMμA))
  premR = begin
      SAMμA ∘co ((inMap A δ₀ ∘ ce) ∘ p₂)
    ≈⟨ CoK.∘-cong ≈-refl (assoc _ _ _) ⟩
      SAMμA ∘co (inMap A δ₀ ∘ (ce ∘ p₂))
    ≈˘⟨ ∘co-push SAMμA (inMap A δ₀) (ce ∘ p₂) ⟩
      (SAMμA ∘co (inMap A δ₀ ∘ p₂)) ∘co (ce ∘ p₂)
    ≈⟨ CoK.∘-cong (⦅⦆-β {P = A} {δ = δ₀} (inMap A' δ₀ ∘ SAM-A)) ≈-refl ⟩
      (((inMap A' δ₀ ∘ SAM-A) ∘co strong-fmor A (strong-extend-mor {δ = δ₀} {δ' = δ₀} (λ i → p₂) SAMμA)) ∘co (ce ∘ p₂))
    ≈⟨ CoK.assoc _ _ _ ⟩
      ((inMap A' δ₀ ∘ SAM-A) ∘co (strong-fmor A (strong-extend-mor {δ = δ₀} {δ' = δ₀} (λ i → p₂) SAMμA) ∘co (ce ∘ p₂)))
    ≈⟨ CoK.∘-cong ≈-refl (strong-cast-natural eq (strong-extend-mor {δ = δ₀} {δ' = δ₀} (λ i → p₂) SAMμA)) ⟩
      ((inMap A' δ₀ ∘ SAM-A) ∘co ((ceM ∘ p₂) ∘co strong-fmor Ar (strong-extend-mor {δ = δ₀} {δ' = δ₀} (λ i → p₂) SAMμA)))
    ≈˘⟨ CoK.assoc _ _ _ ⟩
      (((inMap A' δ₀ ∘ SAM-A) ∘co (ceM ∘ p₂)) ∘co strong-fmor Ar (strong-extend-mor {δ = δ₀} {δ' = δ₀} (λ i → p₂) SAMμA))
    ∎
    where open ≈-Reasoning isEquiv

  main : ((cast (as-poly-ren ρ (μ τ) δ') δ₀ ∘ p₂) ∘co SAMμr)
           ≈ (SAMμA ∘co (cast (as-poly-ren ρ (μ τ) δ) δ₀ ∘ p₂))
  main = begin
      (cast (cong Poly.μ eq') δ₀ ∘ p₂) ∘co SAMμr
    ≈⟨ CoK.∘-cong (∘-cong (cast-μ eq' δ₀) ≈-refl) ≈-refl ⟩
      (μ-map Ar' δ₀ A' δ₀ ce' ∘ p₂) ∘co SAMμr
    ≈˘⟨ CoK.∘-cong (μ-map-weaken Ar' δ₀ A' δ₀ ce') ≈-refl ⟩
      hL ∘co SAMμr
    ≈⟨ fusion {P = Ar} {δ = δ₀} (inMap Ar' δ₀ ∘ SAMr-M) alg⋆ hL premL ⟩
      ⦅_⦆ {P = Ar} {δ = δ₀} alg⋆
    ≈˘⟨ fusion {P = Ar} {δ = δ₀} ((inMap A δ₀ ∘ ce) ∘ p₂) alg⋆ SAMμA premR ⟩
      SAMμA ∘co ⦅_⦆ {P = Ar} {δ = δ₀} ((inMap A δ₀ ∘ ce) ∘ p₂)
    ≈⟨ CoK.∘-cong ≈-refl (μ-map-weaken Ar δ₀ A δ₀ ce) ⟩
      SAMμA ∘co (μ-map Ar δ₀ A δ₀ ce ∘ p₂)
    ≈˘⟨ CoK.∘-cong ≈-refl (∘-cong (cast-μ eq δ₀) ≈-refl) ⟩
      SAMμA ∘co (cast (cong Poly.μ eq) δ₀ ∘ p₂)
    ∎
    where open ≈-Reasoning isEquiv

fmor-extend-id : ∀ {k} (P : Poly R.cat (suc k)) {δ : Fin k → obj} {X : obj} →
                 fmor P (extend-mor (λ j → id (δ j)) (id X)) ≈ id _
fmor-extend-id P = ≈-trans (fmor-cong P extend-mor-id) (fmor-id P)

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

preserves-env-pw : ∀ {Δ n} {δ : Fin Δ → obj} {δ₀ : Fin n → obj} {X : obj}
  (δc : ∀ i → Section (δ i)) (δ₀c : ∀ i → Section (δ₀ i)) (cX : Section X) (i : Fin (suc (n + Δ))) →
  preserves-section (≡-to-⇒ (env-pw δ δ₀ X i))
    (concat-section {n = 1} (extend-section (λ ()) cX) (concat-section δ₀c δc) i)
    (concat-section {n = suc n} (extend-section δ₀c cX) δc i)
preserves-env-pw δc δ₀c cX Fin.zero = preserves-section-id cX
preserves-env-pw {n = n} δc δ₀c cX (Fin.suc j) = preserves-env-pw-suc δc δ₀c cX (splitAt n j)

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
    ≈⟨ μ-map-cong _ _ _ _ (apply-fwd-body-env τ gs δ₀ M') ⟩
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

  apply-fwd-body-env : ∀ {Δ n} (τ : type (suc n + Δ)) {δ δ' : Fin Δ → obj} (gs : ∀ i → δ i ⇒ δ' i) (δ₀ : Fin n → obj) (X : obj) →
                          (apply-fwd-body τ δ' δ₀ X ∘ as-poly-map τ (concat-mor (λ i → id _) gs) (extend δ∅ X))
                            ≈ (as-poly-map τ gs (extend δ₀ X) ∘ apply-fwd-body τ δ δ₀ X)
  apply-fwd-body-env τ {δ} {δ'} gs δ₀ X = begin
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

sub-lift-pw : ∀ {Δ Δ'} (σ : TySub Δ Δ') (δ : Fin Δ' → obj) (X : obj) (i : Fin (suc Δ)) →
              ⟦ sub-lift σ i ⟧ty (concat (extend {0} δ∅ X) δ) ≡ concat (extend {0} δ∅ X) (λ j → ⟦ σ j ⟧ty δ) i
sub-lift-pw σ δ X Fin.zero    = refl
sub-lift-pw σ δ X (Fin.suc j) = ty-ren Fin.suc (σ j) (concat (extend {0} δ∅ X) δ)

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

≡-to-⇒-irr : ∀ {A B : obj} (e e' : A ≡ B) → ≡-to-⇒ e ≈ ≡-to-⇒ e'
≡-to-⇒-irr refl refl = ≈-refl

≡-to-⇒-comp : ∀ {A B C : obj} (e₁ : A ≡ B) (e₂ : B ≡ C) → (≡-to-⇒ e₂ ∘ ≡-to-⇒ e₁) ≈ ≡-to-⇒ (trans e₁ e₂)
≡-to-⇒-comp refl refl = id-left

private
  ty-square : ∀ {Δ} (F G : type Δ → obj) (h : ∀ υ → F υ ⇒ G υ) {υ υ' : type Δ} (e : υ ≡ υ') →
              (h υ' ∘ ≡-to-⇒ (cong F e)) ≈ (≡-to-⇒ (cong G e) ∘ h υ)
  ty-square F G h refl = ≈-trans id-right (≈-sym id-left)

  ty-cast-+ : ∀ {Δ} {τ₁ τ₁' τ₂ τ₂' : type Δ} (e₁ : τ₁ ≡ τ₁') (e₂ : τ₂ ≡ τ₂') (δ : Fin Δ → obj) →
              ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) (cong₂ _[+]_ e₁ e₂))
                ≈ [+]-map (≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) e₁)) (≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) e₂))
  ty-cast-+ refl refl δ = ≈-sym [+]-map-id

  ty-cast-× : ∀ {Δ} {τ₁ τ₁' τ₂ τ₂' : type Δ} (e₁ : τ₁ ≡ τ₁') (e₂ : τ₂ ≡ τ₂') (δ : Fin Δ → obj) →
              ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) (cong₂ _[×]_ e₁ e₂))
                ≈ [×]-map (≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) e₁)) (≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) e₂))
  ty-cast-× refl refl δ = ≈-sym [×]-map-id

  ty-cast-μ : ∀ {Δ} {τ τ' : type (suc Δ)} (e : τ ≡ τ') (δ : Fin Δ → obj) →
              ≡-to-⇒ (cong (λ υ → ⟦ μ υ ⟧ty δ) e)
                ≈ μ-map (as-poly {Δ} {1} τ δ) δ∅ (as-poly {Δ} {1} τ' δ) δ∅
                        (≡-to-⇒ (cong (λ υ → fobj μ-obj (as-poly {Δ} {1} υ δ)
                                                (extend δ∅ (μ-obj (as-poly {Δ} {1} τ' δ) δ∅))) e))
  ty-cast-μ refl δ = ≈-sym (μ-map-id _ _)

mutual
  subst-fwd-cong : ∀ {Δ Δ'} {σ σ' : TySub Δ Δ'} (τ : type Δ) (pw : ∀ i → σ i ≡ σ' i)
                   (e : sub σ τ ≡ sub σ' τ) (δ : Fin Δ' → obj) →
                   (as-poly-map τ (λ i → ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) (pw i))) δ∅ ∘ subst-fwd σ τ δ)
                     ≈ (subst-fwd σ' τ δ ∘ ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) e))
  subst-fwd-cong (var i) pw e δ =
    ≈-trans id-right
            (≈-trans (≡-to-⇒-irr (cong (λ υ → ⟦ υ ⟧ty δ) (pw i)) (cong (λ υ → ⟦ υ ⟧ty δ) e)) (≈-sym id-left))
  subst-fwd-cong unit pw e δ =
    ≈-trans id-left (≈-trans (≡-to-⇒-irr refl (cong (λ υ → ⟦ υ ⟧ty δ) e)) (≈-sym id-left))
  subst-fwd-cong (base s) pw e δ =
    ≈-trans id-left (≈-trans (≡-to-⇒-irr refl (cong (λ υ → ⟦ υ ⟧ty δ) e)) (≈-sym id-left))
  subst-fwd-cong (τ₁ [+] τ₂) pw e δ =
    ≈-trans ([+]-square (subst-fwd-cong τ₁ pw (sub-cong τ₁ pw) δ) (subst-fwd-cong τ₂ pw (sub-cong τ₂ pw) δ))
            (∘-cong ≈-refl
              (≈-sym (≈-trans (≡-to-⇒-irr (cong (λ υ → ⟦ υ ⟧ty δ) e)
                                          (cong (λ υ → ⟦ υ ⟧ty δ) (cong₂ _[+]_ (sub-cong τ₁ pw) (sub-cong τ₂ pw))))
                              (ty-cast-+ (sub-cong τ₁ pw) (sub-cong τ₂ pw) δ))))
  subst-fwd-cong (τ₁ [×] τ₂) pw e δ =
    ≈-trans ([×]-square (subst-fwd-cong τ₁ pw (sub-cong τ₁ pw) δ) (subst-fwd-cong τ₂ pw (sub-cong τ₂ pw) δ))
            (∘-cong ≈-refl
              (≈-sym (≈-trans (≡-to-⇒-irr (cong (λ υ → ⟦ υ ⟧ty δ) e)
                                          (cong (λ υ → ⟦ υ ⟧ty δ) (cong₂ _[×]_ (sub-cong τ₁ pw) (sub-cong τ₂ pw))))
                              (ty-cast-× (sub-cong τ₁ pw) (sub-cong τ₂ pw) δ))))
  subst-fwd-cong (τ₁ [→] τ₂) pw e δ =
    ≈-trans id-left (≈-trans (≡-to-⇒-irr refl (cong (λ υ → ⟦ υ ⟧ty δ) e)) (≈-sym id-left))
  subst-fwd-cong {Δ} {Δ'} {σ} {σ'} (μ τ) pw e δ = begin
      μ-map Aσ δ∅ Aσ' δ∅ (as-poly-map {n = 1} τ gs (extend δ∅ M')) ∘ μ-map P δ∅ Aσ δ∅ (subst-fwd-body σ τ δ M)
    ≈⟨ μ-map-comp P δ∅ Aσ δ∅ Aσ' δ∅ (subst-fwd-body σ τ δ M) (as-poly-map {n = 1} τ gs (extend δ∅ M'))
                  (subst-fwd-body σ τ δ M') (subst-fwd-body-carrier σ τ δ k₁) ⟩
      μ-map P δ∅ Aσ' δ∅ (as-poly-map {n = 1} τ gs (extend δ∅ M') ∘ subst-fwd-body σ τ δ M')
    ≈⟨ μ-map-cong _ _ _ _ (subst-fwd-cong-body τ pw eb δ M') ⟩
      μ-map P δ∅ Aσ' δ∅
        (subst-fwd-body σ' τ δ M' ∘ ≡-to-⇒ (cong (λ υ → fobj μ-obj (as-poly {Δ'} {1} υ δ) (extend δ∅ M')) eb))
    ≈˘⟨ μ-map-comp P δ∅ P' δ∅ Aσ' δ∅
                   (≡-to-⇒ (cong (λ υ → fobj μ-obj (as-poly {Δ'} {1} υ δ) (extend δ∅ (μ-obj P' δ∅))) eb))
                   (subst-fwd-body σ' τ δ M')
                   (≡-to-⇒ (cong (λ υ → fobj μ-obj (as-poly {Δ'} {1} υ δ) (extend δ∅ M')) eb))
                   (ty-square (λ υ → fobj μ-obj (as-poly {Δ'} {1} υ δ) (extend δ∅ (μ-obj P' δ∅)))
                              (λ υ → fobj μ-obj (as-poly {Δ'} {1} υ δ) (extend δ∅ M'))
                              (λ υ → fmor (as-poly {Δ'} {1} υ δ) (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k₂))
                              eb) ⟩
      μ-map P' δ∅ Aσ' δ∅ (subst-fwd-body σ' τ δ M')
        ∘ μ-map P δ∅ P' δ∅ (≡-to-⇒ (cong (λ υ → fobj μ-obj (as-poly {Δ'} {1} υ δ) (extend δ∅ (μ-obj P' δ∅))) eb))
    ≈˘⟨ ∘-cong ≈-refl (ty-cast-μ eb δ) ⟩
      μ-map P' δ∅ Aσ' δ∅ (subst-fwd-body σ' τ δ M') ∘ ≡-to-⇒ (cong (λ υ → ⟦ μ υ ⟧ty δ) eb)
    ≈⟨ ∘-cong ≈-refl (≡-to-⇒-irr (cong (λ υ → ⟦ μ υ ⟧ty δ) eb) (cong (λ υ → ⟦ υ ⟧ty δ) e)) ⟩
      μ-map P' δ∅ Aσ' δ∅ (subst-fwd-body σ' τ δ M') ∘ ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) e)
    ∎
    where
      open ≈-Reasoning isEquiv
      gs : ∀ i → ⟦ σ i ⟧ty δ ⇒ ⟦ σ' i ⟧ty δ
      gs = λ i → ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) (pw i))
      pw-lift : ∀ i → sub-lift σ i ≡ sub-lift σ' i
      pw-lift Fin.zero    = refl
      pw-lift (Fin.suc i) = cong (Fin.suc *ᵗ_) (pw i)
      eb : sub (sub-lift σ) τ ≡ sub (sub-lift σ') τ
      eb = sub-cong τ pw-lift
      P   = as-poly {Δ'} {1} (sub (sub-lift σ) τ) δ
      P'  = as-poly {Δ'} {1} (sub (sub-lift σ') τ) δ
      Aσ  = as-poly {Δ} {1} τ (λ i → ⟦ σ i ⟧ty δ)
      Aσ' = as-poly {Δ} {1} τ (λ i → ⟦ σ' i ⟧ty δ)
      M   = μ-obj Aσ δ∅
      M'  = μ-obj Aσ' δ∅
      k₁  = μ-map Aσ δ∅ Aσ' δ∅ (as-poly-map {n = 1} τ gs (extend δ∅ M'))
      k₂  = μ-map P' δ∅ Aσ' δ∅ (subst-fwd-body σ' τ δ M')

  subst-fwd-cong-body : ∀ {Δ Δ'} {σ σ' : TySub Δ Δ'} (τ : type (suc Δ)) (pw : ∀ i → σ i ≡ σ' i)
                        (e : sub (sub-lift σ) τ ≡ sub (sub-lift σ') τ) (δ : Fin Δ' → obj) (X : obj) →
                        (as-poly-map {n = 1} τ (λ i → ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) (pw i))) (extend δ∅ X)
                           ∘ subst-fwd-body σ τ δ X)
                          ≈ (subst-fwd-body σ' τ δ X
                             ∘ ≡-to-⇒ (cong (λ υ → fobj μ-obj (as-poly {Δ'} {1} υ δ) (extend δ∅ X)) e))
  subst-fwd-cong-body {Δ} {Δ'} {σ} {σ'} τ pw e δ X = begin
      as-poly-map {n = 1} τ gs (extend δ∅ X) ∘ (F ∘ L ∘ S ∘ B)
    ≈˘⟨ assoc _ _ _ ⟩
      (as-poly-map {n = 1} τ gs (extend δ∅ X) ∘ (F ∘ L ∘ S)) ∘ B
    ≈˘⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
      (as-poly-map {n = 1} τ gs (extend δ∅ X) ∘ (F ∘ L) ∘ S) ∘ B
    ≈˘⟨ ∘-cong (∘-cong (assoc _ _ _) ≈-refl) ≈-refl ⟩
      (as-poly-map {n = 1} τ gs (extend δ∅ X) ∘ F ∘ L ∘ S) ∘ B
    ≈˘⟨ ∘-cong (∘-cong (∘-cong (apply-fwd-map {n = 1} τ gs (extend δ∅ X)) ≈-refl) ≈-refl) ≈-refl ⟩
      ((F' ∘ K) ∘ L ∘ S) ∘ B
    ≈⟨ ∘-cong (∘-cong (assoc _ _ _) ≈-refl) ≈-refl ⟩
      (F' ∘ (K ∘ L) ∘ S) ∘ B
    ≈⟨ ∘-cong (∘-cong (∘-cong ≈-refl (≈-trans (as-poly-map-comp τ Kfam Lfam δ∅)
                                              (as-poly-map-cong τ pw-step δ∅))) ≈-refl) ≈-refl ⟩
      (F' ∘ as-poly-map τ (λ i → ≡-to-⇒ (sub-lift-pw σ' δ X i) ∘ ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty γ) (pw-lift i))) δ∅ ∘ S) ∘ B
    ≈˘⟨ ∘-cong (∘-cong (∘-cong ≈-refl (as-poly-map-comp τ L'fam PLfam δ∅)) ≈-refl) ≈-refl ⟩
      (F' ∘ (L' ∘ PL) ∘ S) ∘ B
    ≈˘⟨ ∘-cong (∘-cong (assoc _ _ _) ≈-refl) ≈-refl ⟩
      (F' ∘ L' ∘ PL ∘ S) ∘ B
    ≈⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
      ((F' ∘ L') ∘ (PL ∘ S)) ∘ B
    ≈⟨ ∘-cong (∘-cong ≈-refl (subst-fwd-cong τ pw-lift e γ)) ≈-refl ⟩
      ((F' ∘ L') ∘ (S' ∘ TC)) ∘ B
    ≈˘⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
      ((F' ∘ L' ∘ S') ∘ TC) ∘ B
    ≈⟨ assoc _ _ _ ⟩
      (F' ∘ L' ∘ S') ∘ (TC ∘ B)
    ≈⟨ ∘-cong ≈-refl (≈-sym (ty-square (λ υ → fobj μ-obj (as-poly {Δ'} {1} υ δ) (extend δ∅ X))
                                       (λ υ → ⟦ υ ⟧ty γ)
                                       (λ υ → apply-bwd {n = 1} υ δ (extend δ∅ X)) e)) ⟩
      (F' ∘ L' ∘ S') ∘ (B' ∘ C)
    ≈˘⟨ assoc _ _ _ ⟩
      (F' ∘ L' ∘ S' ∘ B') ∘ C
    ∎
    where
      open ≈-Reasoning isEquiv
      γ  = concat (extend {0} δ∅ X) δ
      gs : ∀ i → ⟦ σ i ⟧ty δ ⇒ ⟦ σ' i ⟧ty δ
      gs = λ i → ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) (pw i))
      pw-lift : ∀ i → sub-lift σ i ≡ sub-lift σ' i
      pw-lift Fin.zero    = refl
      pw-lift (Fin.suc i) = cong (Fin.suc *ᵗ_) (pw i)
      Kfam  = concat-mor {n = 1} {δ₀ = extend {0} δ∅ X} (λ i → id _) gs
      Lfam   = λ i → ≡-to-⇒ (sub-lift-pw σ δ X i)
      L'fam  = λ i → ≡-to-⇒ (sub-lift-pw σ' δ X i)
      PLfam  = λ i → ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty γ) (pw-lift i))
      F  = apply-fwd {n = 1} τ (λ i → ⟦ σ i ⟧ty δ) (extend δ∅ X)
      F' = apply-fwd {n = 1} τ (λ i → ⟦ σ' i ⟧ty δ) (extend δ∅ X)
      K = as-poly-map τ Kfam δ∅
      L  = as-poly-map τ Lfam δ∅
      L' = as-poly-map τ L'fam δ∅
      PL = as-poly-map τ PLfam δ∅
      S  = subst-fwd (sub-lift σ) τ γ
      S' = subst-fwd (sub-lift σ') τ γ
      B  = apply-bwd {n = 1} (sub (sub-lift σ) τ) δ (extend δ∅ X)
      B' = apply-bwd {n = 1} (sub (sub-lift σ') τ) δ (extend δ∅ X)
      TC = ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty γ) e)
      C  = ≡-to-⇒ (cong (λ υ → fobj μ-obj (as-poly {Δ'} {1} υ δ) (extend δ∅ X)) e)
      pw-step : ∀ i → (Kfam i ∘ ≡-to-⇒ (sub-lift-pw σ δ X i))
                        ≈ (≡-to-⇒ (sub-lift-pw σ' δ X i) ∘ ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty γ) (pw-lift i)))
      pw-step Fin.zero    = ≈-refl
      pw-step (Fin.suc j) =
        ≈-sym (≈-trans (∘-cong ≈-refl (≡-to-⇒-irr (cong (λ υ → ⟦ υ ⟧ty γ) (pw-lift (Fin.suc j)))
                                                  (cong (λ υ → ⟦ Fin.suc *ᵗ υ ⟧ty γ) (pw j))))
                       (ty-square (λ υ → ⟦ Fin.suc *ᵗ υ ⟧ty γ) (λ υ → ⟦ υ ⟧ty δ)
                                  (λ υ → ≡-to-⇒ (ty-ren Fin.suc υ γ)) (pw j)))

private
  concat-pw : ∀ {n Δ} {δ δ' : Fin Δ → obj} (δ₀ : Fin n → obj) → (∀ i → δ i ≡ δ' i) →
              ∀ i → concat δ₀ δ i ≡ concat δ₀ δ' i
  concat-pw {n} δ₀ h i with splitAt n i
  ... | inj₁ j = refl
  ... | inj₂ k = h k

apply-fwd-cong : ∀ {Δ n} (τ : type (n + Δ)) {δ δ' : Fin Δ → obj} (h : ∀ i → δ i ≡ δ' i)
                 (δ₀ : Fin n → obj) (E : ⟦ τ ⟧ty (concat δ₀ δ) ≡ ⟦ τ ⟧ty (concat δ₀ δ')) →
                 (apply-fwd τ δ' δ₀ ∘ ≡-to-⇒ E) ≈ (cast (as-poly-cong τ h) δ₀ ∘ apply-fwd τ δ δ₀)
apply-fwd-cong {Δ} {n} τ {δ} {δ'} h δ₀ E = begin
    apply-fwd τ δ' δ₀ ∘ ≡-to-⇒ E
  ≈⟨ ∘-cong ≈-refl (≡-to-⇒-irr E (cong (λ P → fobj μ-obj P δ∅) (as-poly-cong {n = 0} τ (concat-pw δ₀ h)))) ⟩
    apply-fwd τ δ' δ₀ ∘ cast (as-poly-cong {n = 0} τ (concat-pw δ₀ h)) δ∅
  ≈⟨ ∘-cong ≈-refl (cast-as-poly-cong {n = 0} τ (concat-pw δ₀ h) δ∅) ⟩
    apply-fwd τ δ' δ₀ ∘ as-poly-map τ (λ i → ≡-to-⇒ (concat-pw δ₀ h i)) δ∅
  ≈⟨ ∘-cong ≈-refl (as-poly-map-cong τ pw-match δ∅) ⟩
    apply-fwd τ δ' δ₀ ∘ as-poly-map τ (concat-mor {δ₀ = δ₀} (λ i → id _) (λ i → ≡-to-⇒ (h i))) δ∅
  ≈⟨ apply-fwd-map τ (λ i → ≡-to-⇒ (h i)) δ₀ ⟩
    as-poly-map τ (λ i → ≡-to-⇒ (h i)) δ₀ ∘ apply-fwd τ δ δ₀
  ≈˘⟨ ∘-cong (cast-as-poly-cong τ h δ₀) ≈-refl ⟩
    cast (as-poly-cong τ h) δ₀ ∘ apply-fwd τ δ δ₀
  ∎
  where
    open ≈-Reasoning isEquiv
    pw-match : ∀ i → ≡-to-⇒ (concat-pw δ₀ h i)
                       ≈ concat-mor {δ₀ = δ₀} (λ i → id _) (λ i → ≡-to-⇒ (h i)) i
    pw-match i with splitAt n i
    ... | inj₁ j = ≈-refl
    ... | inj₂ k = ≈-refl

apply-bwd-cong : ∀ {Δ n} (τ : type (n + Δ)) {δ δ' : Fin Δ → obj} (h : ∀ i → δ i ≡ δ' i)
                 (δ₀ : Fin n → obj) (E : ⟦ τ ⟧ty (concat δ₀ δ) ≡ ⟦ τ ⟧ty (concat δ₀ δ')) →
                 (≡-to-⇒ E ∘ apply-bwd τ δ δ₀) ≈ (apply-bwd τ δ' δ₀ ∘ cast (as-poly-cong τ h) δ₀)
apply-bwd-cong {Δ} {n} τ {δ} {δ'} h δ₀ E = begin
    ≡-to-⇒ E ∘ apply-bwd τ δ δ₀
  ≈˘⟨ id-left ⟩
    id _ ∘ (≡-to-⇒ E ∘ apply-bwd τ δ δ₀)
  ≈˘⟨ ∘-cong (apply-bwd-fwd τ δ' δ₀) ≈-refl ⟩
    (apply-bwd τ δ' δ₀ ∘ apply-fwd τ δ' δ₀) ∘ (≡-to-⇒ E ∘ apply-bwd τ δ δ₀)
  ≈⟨ assoc _ _ _ ⟩
    apply-bwd τ δ' δ₀ ∘ (apply-fwd τ δ' δ₀ ∘ (≡-to-⇒ E ∘ apply-bwd τ δ δ₀))
  ≈˘⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
    apply-bwd τ δ' δ₀ ∘ ((apply-fwd τ δ' δ₀ ∘ ≡-to-⇒ E) ∘ apply-bwd τ δ δ₀)
  ≈⟨ ∘-cong ≈-refl (∘-cong (apply-fwd-cong τ h δ₀ E) ≈-refl) ⟩
    apply-bwd τ δ' δ₀ ∘ ((cast (as-poly-cong τ h) δ₀ ∘ apply-fwd τ δ δ₀) ∘ apply-bwd τ δ δ₀)
  ≈⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
    apply-bwd τ δ' δ₀ ∘ (cast (as-poly-cong τ h) δ₀ ∘ (apply-fwd τ δ δ₀ ∘ apply-bwd τ δ δ₀))
  ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl (apply-fwd-bwd τ δ δ₀)) ⟩
    apply-bwd τ δ' δ₀ ∘ (cast (as-poly-cong τ h) δ₀ ∘ id _)
  ≈⟨ ∘-cong ≈-refl id-right ⟩
    apply-bwd τ δ' δ₀ ∘ cast (as-poly-cong τ h) δ₀
  ∎
  where open ≈-Reasoning isEquiv

private
  cast-trans : ∀ {n} {P Q R' : Poly R.cat n} (e₁ : P ≡ Q) (e₂ : Q ≡ R') (δ₀ : Fin n → obj) →
               cast (trans e₁ e₂) δ₀ ≈ (cast e₂ δ₀ ∘ cast e₁ δ₀)
  cast-trans refl refl δ₀ = ≈-sym id-left

  inv-conj : ∀ {A B A' B' : obj} {f : A ⇒ B} {g : B ⇒ A} {f' : A' ⇒ B'} {g' : B' ⇒ A'}
             {u : A ⇒ A'} {v : B ⇒ B'} →
             (f ∘ g) ≈ id _ → (g' ∘ f') ≈ id _ → (v ∘ f) ≈ (f' ∘ u) → (u ∘ g) ≈ (g' ∘ v)
  inv-conj {f = f} {g} {f'} {g'} {u} {v} fg g'f' sq = begin
      u ∘ g            ≈˘⟨ id-left ⟩
      id _ ∘ (u ∘ g)   ≈˘⟨ ∘-cong g'f' ≈-refl ⟩
      (g' ∘ f') ∘ (u ∘ g) ≈⟨ assoc _ _ _ ⟩
      g' ∘ (f' ∘ (u ∘ g)) ≈˘⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
      g' ∘ ((f' ∘ u) ∘ g) ≈˘⟨ ∘-cong ≈-refl (∘-cong sq ≈-refl) ⟩
      g' ∘ ((v ∘ f) ∘ g)  ≈⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
      g' ∘ (v ∘ (f ∘ g))  ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl fg) ⟩
      g' ∘ (v ∘ id _)     ≈⟨ ∘-cong ≈-refl id-right ⟩
      g' ∘ v ∎
    where open ≈-Reasoning isEquiv

  concat-ren-pw-go : ∀ {Δ₁ Δ₂ n} (ρ : TyRen Δ₁ Δ₂) (δ : Fin Δ₂ → obj) (δ₀ : Fin n → obj)
                     (s : Fin n ⊎ Fin Δ₁) (s' : Fin n ⊎ Fin Δ₂) → s' ≡ [ inj₁ , (λ k → inj₂ (ρ k)) ] s →
                     [_,_] {C = λ _ → obj} δ₀ δ s' ≡ [_,_] {C = λ _ → obj} δ₀ (λ k → δ (ρ k)) s
  concat-ren-pw-go ρ δ δ₀ (inj₁ j) _ refl = refl
  concat-ren-pw-go ρ δ δ₀ (inj₂ k) _ refl = refl

  concat-ren-pw : ∀ {Δ₁ Δ₂ n} (ρ : TyRen Δ₁ Δ₂) (δ : Fin Δ₂ → obj) (δ₀ : Fin n → obj) (i : Fin (n + Δ₁)) →
                  concat δ₀ δ (extᵗⁿ n ρ i) ≡ concat δ₀ (λ k → δ (ρ k)) i
  concat-ren-pw {n = n} ρ δ δ₀ i =
    concat-ren-pw-go ρ δ δ₀ (splitAt n i) (splitAt n (extᵗⁿ n ρ i)) (splitAt-extᵗⁿ n ρ i)

private
  apply-fwd-ren-mid : ∀ {Δ₁ Δ₂ n} (ρ : TyRen Δ₁ Δ₂) (τ : type (suc n + Δ₁)) (δ : Fin Δ₂ → obj)
                      (δ₀ : Fin n → obj) (X : obj) →
                      (cast (trans (as-poly-ren {n = 0} (extᵗⁿ (suc n) ρ) τ (concat (extend δ₀ X) δ))
                                   (as-poly-cong {n = 0} τ (concat-ren-pw ρ δ (extend δ₀ X)))) δ∅
                         ∘ as-poly-map (extᵗⁿ (suc n) ρ *ᵗ τ) (λ i → ≡-to-⇒ (env-pw δ δ₀ X i)) δ∅)
                        ≈ ((as-poly-map τ (λ i → ≡-to-⇒ (env-pw (λ k → δ (ρ k)) δ₀ X i)) δ∅
                             ∘ ≡-to-⇒ (cong (λ P → fobj μ-obj P δ∅)
                                             (as-poly-cong {n = 0} τ (concat-pw (extend {0} δ∅ X) (concat-ren-pw ρ δ δ₀)))))
                           ∘ cast (trans (as-poly-ren {n = 0} (extᵗⁿ (suc n) ρ) τ (concat (extend {0} δ∅ X) (concat δ₀ δ)))
                                         (as-poly-cong {n = 0} τ (concat-ren-pw (extᵗⁿ n ρ) (concat δ₀ δ) (extend {0} δ∅ X)))) δ∅)
  apply-fwd-ren-mid {Δ₁} {Δ₂} {n} ρ τ δ δ₀ X = begin
      cast (trans a⁺ b⁺) δ∅ ∘ L₁
    ≈⟨ ∘-cong (cast-trans a⁺ b⁺ δ∅) ≈-refl ⟩
      (cast b⁺ δ∅ ∘ cast a⁺ δ∅) ∘ L₁
    ≈⟨ assoc _ _ _ ⟩
      cast b⁺ δ∅ ∘ (cast a⁺ δ∅ ∘ L₁)
    ≈⟨ ∘-cong ≈-refl (as-poly-map-ren (extᵗⁿ (suc n) ρ) τ (λ i → ≡-to-⇒ (env-pw δ δ₀ X i)) δ∅) ⟩
      cast b⁺ δ∅ ∘ (Sh ∘ cast a₀ δ∅)
    ≈˘⟨ assoc _ _ _ ⟩
      (cast b⁺ δ∅ ∘ Sh) ∘ cast a₀ δ∅
    ≈⟨ ∘-cong (∘-cong (cast-as-poly-cong {n = 0} τ (concat-ren-pw ρ δ (extend δ₀ X)) δ∅) ≈-refl) ≈-refl ⟩
      (as-poly-map τ (λ i → ≡-to-⇒ (concat-ren-pw ρ δ (extend δ₀ X) i)) δ∅ ∘ Sh) ∘ cast a₀ δ∅
    ≈⟨ ∘-cong (as-poly-map-comp τ (λ i → ≡-to-⇒ (concat-ren-pw ρ δ (extend δ₀ X) i))
                                  (λ i → ≡-to-⇒ (env-pw δ δ₀ X (extᵗⁿ (suc n) ρ i))) δ∅) ≈-refl ⟩
      as-poly-map τ (λ i → ≡-to-⇒ (concat-ren-pw ρ δ (extend δ₀ X) i) ∘ ≡-to-⇒ (env-pw δ δ₀ X (extᵗⁿ (suc n) ρ i))) δ∅
        ∘ cast a₀ δ∅
    ≈⟨ ∘-cong (as-poly-map-cong τ pw-refactor δ∅) ≈-refl ⟩
      as-poly-map τ (λ i → (≡-to-⇒ (env-pw δρ δ₀ X i) ∘ ≡-to-⇒ (concat-pw X̂ (concat-ren-pw ρ δ δ₀) i))
                             ∘ ≡-to-⇒ (concat-ren-pw (extᵗⁿ n ρ) (concat δ₀ δ) X̂ i)) δ∅
        ∘ cast a₀ δ∅
    ≈˘⟨ ∘-cong (as-poly-map-comp τ (λ i → ≡-to-⇒ (env-pw δρ δ₀ X i) ∘ ≡-to-⇒ (concat-pw X̂ (concat-ren-pw ρ δ δ₀) i))
                                   (λ i → ≡-to-⇒ (concat-ren-pw (extᵗⁿ n ρ) (concat δ₀ δ) X̂ i)) δ∅) ≈-refl ⟩
      (as-poly-map τ (λ i → ≡-to-⇒ (env-pw δρ δ₀ X i) ∘ ≡-to-⇒ (concat-pw X̂ (concat-ren-pw ρ δ δ₀) i)) δ∅
         ∘ as-poly-map τ (λ i → ≡-to-⇒ (concat-ren-pw (extᵗⁿ n ρ) (concat δ₀ δ) X̂ i)) δ∅)
        ∘ cast a₀ δ∅
    ≈˘⟨ ∘-cong (∘-cong (as-poly-map-comp τ (λ i → ≡-to-⇒ (env-pw δρ δ₀ X i))
                                          (λ i → ≡-to-⇒ (concat-pw X̂ (concat-ren-pw ρ δ δ₀) i)) δ∅)
                       (cast-as-poly-cong {n = 0} τ (concat-ren-pw (extᵗⁿ n ρ) (concat δ₀ δ) X̂) δ∅)) ≈-refl ⟩
      ((L₂ ∘ as-poly-map τ (λ i → ≡-to-⇒ (concat-pw X̂ (concat-ren-pw ρ δ δ₀) i)) δ∅) ∘ cast cb₁ δ∅) ∘ cast a₀ δ∅
    ≈˘⟨ ∘-cong (∘-cong (∘-cong ≈-refl (cast-as-poly-cong {n = 0} τ (concat-pw X̂ (concat-ren-pw ρ δ δ₀)) δ∅)) ≈-refl) ≈-refl ⟩
      ((L₂ ∘ ≡-to-⇒ E) ∘ cast cb₁ δ∅) ∘ cast a₀ δ∅
    ≈⟨ assoc _ _ _ ⟩
      (L₂ ∘ ≡-to-⇒ E) ∘ (cast cb₁ δ∅ ∘ cast a₀ δ∅)
    ≈˘⟨ ∘-cong ≈-refl (cast-trans a₀ cb₁ δ∅) ⟩
      (L₂ ∘ ≡-to-⇒ E) ∘ cast (trans a₀ cb₁) δ∅
    ∎
    where
      open ≈-Reasoning isEquiv
      X̂  = extend {0} δ∅ X
      δρ : Fin Δ₁ → obj
      δρ = λ k → δ (ρ k)
      L₁ = as-poly-map (extᵗⁿ (suc n) ρ *ᵗ τ) (λ i → ≡-to-⇒ (env-pw δ δ₀ X i)) δ∅
      L₂ = as-poly-map τ (λ i → ≡-to-⇒ (env-pw δρ δ₀ X i)) δ∅
      a⁺ = as-poly-ren {n = 0} (extᵗⁿ (suc n) ρ) τ (concat (extend δ₀ X) δ)
      b⁺ = as-poly-cong {n = 0} τ (concat-ren-pw ρ δ (extend δ₀ X))
      a₀ = as-poly-ren {n = 0} (extᵗⁿ (suc n) ρ) τ (concat X̂ (concat δ₀ δ))
      cb₁ = as-poly-cong {n = 0} τ (concat-ren-pw (extᵗⁿ n ρ) (concat δ₀ δ) X̂)
      E  = cong (λ P → fobj μ-obj P δ∅) (as-poly-cong {n = 0} τ (concat-pw X̂ (concat-ren-pw ρ δ δ₀)))
      Sh = as-poly-map τ (λ i → ≡-to-⇒ (env-pw δ δ₀ X (extᵗⁿ (suc n) ρ i))) δ∅
      pw-refactor : ∀ i → (≡-to-⇒ (concat-ren-pw ρ δ (extend δ₀ X) i) ∘ ≡-to-⇒ (env-pw δ δ₀ X (extᵗⁿ (suc n) ρ i)))
                            ≈ ((≡-to-⇒ (env-pw δρ δ₀ X i) ∘ ≡-to-⇒ (concat-pw X̂ (concat-ren-pw ρ δ δ₀) i))
                               ∘ ≡-to-⇒ (concat-ren-pw (extᵗⁿ n ρ) (concat δ₀ δ) X̂ i))
      pw-refactor i =
        ≈-trans (≡-to-⇒-comp (env-pw δ δ₀ X (extᵗⁿ (suc n) ρ i)) (concat-ren-pw ρ δ (extend δ₀ X) i))
        (≈-trans (≡-to-⇒-irr (trans (env-pw δ δ₀ X (extᵗⁿ (suc n) ρ i)) (concat-ren-pw ρ δ (extend δ₀ X) i))
                             (trans (concat-ren-pw (extᵗⁿ n ρ) (concat δ₀ δ) X̂ i)
                                    (trans (concat-pw X̂ (concat-ren-pw ρ δ δ₀) i) (env-pw δρ δ₀ X i))))
                 (≈-sym (≈-trans (∘-cong (≡-to-⇒-comp (concat-pw X̂ (concat-ren-pw ρ δ δ₀) i) (env-pw δρ δ₀ X i)) ≈-refl)
                                 (≡-to-⇒-comp (concat-ren-pw (extᵗⁿ n ρ) (concat δ₀ δ) X̂ i)
                                              (trans (concat-pw X̂ (concat-ren-pw ρ δ δ₀) i) (env-pw δρ δ₀ X i))))))

mutual
  apply-fwd-ren : ∀ {Δ₁ Δ₂ n} (ρ : TyRen Δ₁ Δ₂) (τ : type (n + Δ₁)) (δ : Fin Δ₂ → obj) (δ₀ : Fin n → obj) →
                  (cast (as-poly-ren ρ τ δ) δ₀ ∘ apply-fwd (extᵗⁿ n ρ *ᵗ τ) δ δ₀)
                    ≈ (apply-fwd τ (λ k → δ (ρ k)) δ₀
                       ∘ cast (trans (as-poly-ren {n = 0} (extᵗⁿ n ρ) τ (concat δ₀ δ))
                                     (as-poly-cong {n = 0} τ (concat-ren-pw ρ δ δ₀))) δ∅)
  apply-fwd-ren {Δ₁} {Δ₂} {n} ρ (var i) δ δ₀ =
    go i (extᵗⁿ n ρ i) (splitAt-extᵗⁿ n ρ i) (as-poly-ren ρ (var i) δ)
       (trans (as-poly-ren {n = 0} (extᵗⁿ n ρ) (var i) (concat δ₀ δ))
              (as-poly-cong {n = 0} (var i) {δ = λ j → concat δ₀ δ (extᵗⁿ n ρ j)}
                            {δ' = concat δ₀ (λ k → δ (ρ k))} (concat-ren-pw ρ δ δ₀)))
    where
    go : ∀ (i' : Fin (n + Δ₁)) (m : Fin (n + Δ₂))
         (e : splitAt n m ≡ [ inj₁ , (λ k → inj₂ (ρ k)) ] (splitAt n i'))
         (p : as-poly {Δ₂} {n} (var m) δ ≡ as-poly {Δ₁} {n} (var i') (λ k → δ (ρ k)))
         (q : as-poly {n + Δ₂} {0} (var m) (concat δ₀ δ)
                ≡ as-poly {n + Δ₁} {0} (var i') (concat δ₀ (λ k → δ (ρ k)))) →
         (cast p δ₀ ∘ apply-fwd (var m) δ δ₀) ≈ (apply-fwd (var i') (λ k → δ (ρ k)) δ₀ ∘ cast q δ∅)
    go i' m e p q with splitAt n i' | splitAt n m | e
    ... | inj₁ j | .(inj₁ j)     | refl =
      ≈-trans id-right (≈-trans (cast-irr p refl δ₀) (≈-trans (≈-sym (cast-irr q refl δ∅)) (≈-sym id-left)))
    ... | inj₂ k | .(inj₂ (ρ k)) | refl =
      ≈-trans id-right (≈-trans (cast-irr p refl δ₀) (≈-trans (≈-sym (cast-irr q refl δ∅)) (≈-sym id-left)))
  apply-fwd-ren ρ unit      δ δ₀ = ≈-refl
  apply-fwd-ren ρ (base s)  δ δ₀ = ≈-refl
  apply-fwd-ren ρ (σ [→] τ) δ δ₀ = ≈-refl
  apply-fwd-ren {Δ₁} {Δ₂} {n} ρ (σ [+] τ) δ δ₀ =
    ≈-trans (∘-cong (cast-+ (as-poly-ren ρ σ δ) (as-poly-ren ρ τ δ) δ₀) ≈-refl)
            (≈-trans ([+]-square (apply-fwd-ren ρ σ δ δ₀) (apply-fwd-ren ρ τ δ δ₀))
                     (∘-cong ≈-refl
                       (≈-sym (≈-trans (cast-irr (trans (as-poly-ren {n = 0} (extᵗⁿ n ρ) (σ [+] τ) (concat δ₀ δ))
                                                        (as-poly-cong {n = 0} (σ [+] τ) (concat-ren-pw ρ δ δ₀)))
                                                 (cong₂ Poly._+_ (rσ σ) (rσ τ)) δ∅)
                                       (cast-+ (rσ σ) (rσ τ) δ∅)))))
    where
      rσ : (υ : type (n + Δ₁)) → as-poly {n + Δ₂} {0} (extᵗⁿ n ρ *ᵗ υ) (concat δ₀ δ)
                                   ≡ as-poly {n + Δ₁} {0} υ (concat δ₀ (λ k → δ (ρ k)))
      rσ υ = trans (as-poly-ren {n = 0} (extᵗⁿ n ρ) υ (concat δ₀ δ))
                   (as-poly-cong {n = 0} υ (concat-ren-pw ρ δ δ₀))
  apply-fwd-ren {Δ₁} {Δ₂} {n} ρ (σ [×] τ) δ δ₀ =
    ≈-trans (∘-cong (cast-× (as-poly-ren ρ σ δ) (as-poly-ren ρ τ δ) δ₀) ≈-refl)
            (≈-trans ([×]-square (apply-fwd-ren ρ σ δ δ₀) (apply-fwd-ren ρ τ δ δ₀))
                     (∘-cong ≈-refl
                       (≈-sym (≈-trans (cast-irr (trans (as-poly-ren {n = 0} (extᵗⁿ n ρ) (σ [×] τ) (concat δ₀ δ))
                                                        (as-poly-cong {n = 0} (σ [×] τ) (concat-ren-pw ρ δ δ₀)))
                                                 (cong₂ Poly._×_ (rσ σ) (rσ τ)) δ∅)
                                       (cast-× (rσ σ) (rσ τ) δ∅)))))
    where
      rσ : (υ : type (n + Δ₁)) → as-poly {n + Δ₂} {0} (extᵗⁿ n ρ *ᵗ υ) (concat δ₀ δ)
                                   ≡ as-poly {n + Δ₁} {0} υ (concat δ₀ (λ k → δ (ρ k)))
      rσ υ = trans (as-poly-ren {n = 0} (extᵗⁿ n ρ) υ (concat δ₀ δ))
                   (as-poly-cong {n = 0} υ (concat-ren-pw ρ δ δ₀))
  apply-fwd-ren {Δ₁} {Δ₂} {n} ρ (μ τ) δ δ₀ = begin
      cast (cong Poly.μ (as-poly-ren {n = suc n} ρ τ δ)) δ₀
        ∘ μ-map PB δ∅ AB δ₀ (apply-fwd-body (extᵗⁿ (suc n) ρ *ᵗ τ) δ δ₀ MB)
    ≈⟨ ∘-cong (cast-μ (as-poly-ren {n = suc n} ρ τ δ) δ₀) ≈-refl ⟩
      μ-map AB δ₀ Aρ δ₀ (cast (as-poly-ren {n = suc n} ρ τ δ) (extend δ₀ Mρ))
        ∘ μ-map PB δ∅ AB δ₀ (apply-fwd-body (extᵗⁿ (suc n) ρ *ᵗ τ) δ δ₀ MB)
    ≈⟨ μ-map-comp PB δ∅ AB δ₀ Aρ δ₀ (apply-fwd-body (extᵗⁿ (suc n) ρ *ᵗ τ) δ δ₀ MB)
                  (cast (as-poly-ren {n = suc n} ρ τ δ) (extend δ₀ Mρ))
                  (apply-fwd-body (extᵗⁿ (suc n) ρ *ᵗ τ) δ δ₀ Mρ)
                  (apply-fwd-body-carrier (extᵗⁿ (suc n) ρ *ᵗ τ) δ δ₀ k₁) ⟩
      μ-map PB δ∅ Aρ δ₀ (cast (as-poly-ren {n = suc n} ρ τ δ) (extend δ₀ Mρ)
                           ∘ apply-fwd-body (extᵗⁿ (suc n) ρ *ᵗ τ) δ δ₀ Mρ)
    ≈⟨ μ-map-cong _ _ _ _ (apply-fwd-ren-body ρ τ δ δ₀ Mρ) ⟩
      μ-map PB δ∅ Aρ δ₀ (apply-fwd-body τ (λ k → δ (ρ k)) δ₀ Mρ ∘ cast (trans aμ bμ) (extend δ∅ Mρ))
    ≈˘⟨ μ-map-comp PB δ∅ Pρ δ∅ Aρ δ₀ (cast (trans aμ bμ) (extend δ∅ (μ-obj Pρ δ∅)))
                   (apply-fwd-body τ (λ k → δ (ρ k)) δ₀ Mρ)
                   (cast (trans aμ bμ) (extend δ∅ Mρ))
                   (cast-natural (trans aμ bμ) (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k₂)) ⟩
      μ-map Pρ δ∅ Aρ δ₀ (apply-fwd-body τ (λ k → δ (ρ k)) δ₀ Mρ)
        ∘ μ-map PB δ∅ Pρ δ∅ (cast (trans aμ bμ) (extend δ∅ (μ-obj Pρ δ∅)))
    ≈˘⟨ ∘-cong ≈-refl (cast-μ (trans aμ bμ) δ∅) ⟩
      μ-map Pρ δ∅ Aρ δ₀ (apply-fwd-body τ (λ k → δ (ρ k)) δ₀ Mρ) ∘ cast (cong Poly.μ (trans aμ bμ)) δ∅
    ≈˘⟨ ∘-cong ≈-refl (cast-irr (trans (cong Poly.μ aμ) (cong Poly.μ bμ)) (cong Poly.μ (trans aμ bμ)) δ∅) ⟩
      μ-map Pρ δ∅ Aρ δ₀ (apply-fwd-body τ (λ k → δ (ρ k)) δ₀ Mρ)
        ∘ cast (trans (cong Poly.μ aμ) (cong Poly.μ bμ)) δ∅
    ∎
    where
      open ≈-Reasoning isEquiv
      PB = as-poly {n + Δ₂} {1} (extᵗⁿ (suc n) ρ *ᵗ τ) (concat δ₀ δ)
      AB = as-poly {Δ₂} {suc n} (extᵗⁿ (suc n) ρ *ᵗ τ) δ
      Aρ = as-poly {Δ₁} {suc n} τ (λ k → δ (ρ k))
      Pρ = as-poly {n + Δ₁} {1} τ (concat δ₀ (λ k → δ (ρ k)))
      MB = μ-obj AB δ₀
      Mρ = μ-obj Aρ δ₀
      aμ = as-poly-ren {n = 1} (extᵗⁿ n ρ) τ (concat δ₀ δ)
      bμ = as-poly-cong {n = 1} τ (concat-ren-pw ρ δ δ₀)
      k₁ = μ-map AB δ₀ Aρ δ₀ (cast (as-poly-ren {n = suc n} ρ τ δ) (extend δ₀ Mρ))
      k₂ = μ-map Pρ δ∅ Aρ δ₀ (apply-fwd-body τ (λ k → δ (ρ k)) δ₀ Mρ)

  apply-fwd-ren-body : ∀ {Δ₁ Δ₂ n} (ρ : TyRen Δ₁ Δ₂) (τ : type (suc n + Δ₁)) (δ : Fin Δ₂ → obj)
                       (δ₀ : Fin n → obj) (X : obj) →
                       (cast (as-poly-ren {n = suc n} ρ τ δ) (extend δ₀ X)
                          ∘ apply-fwd-body (extᵗⁿ (suc n) ρ *ᵗ τ) δ δ₀ X)
                         ≈ (apply-fwd-body τ (λ k → δ (ρ k)) δ₀ X
                            ∘ cast (trans (as-poly-ren {n = 1} (extᵗⁿ n ρ) τ (concat δ₀ δ))
                                          (as-poly-cong {n = 1} τ (concat-ren-pw ρ δ δ₀))) (extend δ∅ X))
  apply-fwd-ren-body {Δ₁} {Δ₂} {n} ρ τ δ δ₀ X = begin
      CA ∘ (F₁ ∘ L₁ ∘ B₁)
    ≈˘⟨ assoc _ _ _ ⟩
      (CA ∘ (F₁ ∘ L₁)) ∘ B₁
    ≈˘⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
      ((CA ∘ F₁) ∘ L₁) ∘ B₁
    ≈⟨ ∘-cong (∘-cong (apply-fwd-ren {n = suc n} ρ τ δ (extend δ₀ X)) ≈-refl) ≈-refl ⟩
      ((F₂ ∘ cast (trans a⁺ b⁺) δ∅) ∘ L₁) ∘ B₁
    ≈⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
      (F₂ ∘ (cast (trans a⁺ b⁺) δ∅ ∘ L₁)) ∘ B₁
    ≈⟨ ∘-cong (∘-cong ≈-refl (apply-fwd-ren-mid ρ τ δ δ₀ X)) ≈-refl ⟩
      (F₂ ∘ ((L₂ ∘ ≡-to-⇒ E) ∘ cast r₁ δ∅)) ∘ B₁
    ≈˘⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
      ((F₂ ∘ (L₂ ∘ ≡-to-⇒ E)) ∘ cast r₁ δ∅) ∘ B₁
    ≈⟨ assoc _ _ _ ⟩
      (F₂ ∘ (L₂ ∘ ≡-to-⇒ E)) ∘ (cast r₁ δ∅ ∘ B₁)
    ≈⟨ ∘-cong ≈-refl lemC ⟩
      (F₂ ∘ (L₂ ∘ ≡-to-⇒ E)) ∘ (B₁' ∘ cast a₁ X̂)
    ≈˘⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
      ((F₂ ∘ L₂) ∘ ≡-to-⇒ E) ∘ (B₁' ∘ cast a₁ X̂)
    ≈˘⟨ assoc _ _ _ ⟩
      (((F₂ ∘ L₂) ∘ ≡-to-⇒ E) ∘ B₁') ∘ cast a₁ X̂
    ≈⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
      ((F₂ ∘ L₂) ∘ (≡-to-⇒ E ∘ B₁')) ∘ cast a₁ X̂
    ≈⟨ ∘-cong (∘-cong ≈-refl (apply-bwd-cong τ (concat-ren-pw ρ δ δ₀) X̂ E)) ≈-refl ⟩
      ((F₂ ∘ L₂) ∘ (B₂ ∘ cast b₁ X̂)) ∘ cast a₁ X̂
    ≈˘⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
      (((F₂ ∘ L₂) ∘ B₂) ∘ cast b₁ X̂) ∘ cast a₁ X̂
    ≈⟨ assoc _ _ _ ⟩
      ((F₂ ∘ L₂) ∘ B₂) ∘ (cast b₁ X̂ ∘ cast a₁ X̂)
    ≈˘⟨ ∘-cong ≈-refl (cast-trans a₁ b₁ X̂) ⟩
      ((F₂ ∘ L₂) ∘ B₂) ∘ cast (trans a₁ b₁) X̂
    ∎
    where
      open ≈-Reasoning isEquiv
      X̂  = extend {0} δ∅ X
      δρ : Fin Δ₁ → obj
      δρ = λ k → δ (ρ k)
      CA = cast (as-poly-ren {n = suc n} ρ τ δ) (extend δ₀ X)
      F₁ = apply-fwd (extᵗⁿ (suc n) ρ *ᵗ τ) δ (extend δ₀ X)
      L₁ = as-poly-map (extᵗⁿ (suc n) ρ *ᵗ τ) (λ i → ≡-to-⇒ (env-pw δ δ₀ X i)) δ∅
      B₁ = apply-bwd {n = 1} (extᵗⁿ (suc n) ρ *ᵗ τ) (concat δ₀ δ) X̂
      F₂ = apply-fwd τ δρ (extend δ₀ X)
      L₂ = as-poly-map τ (λ i → ≡-to-⇒ (env-pw δρ δ₀ X i)) δ∅
      B₂ = apply-bwd {n = 1} τ (concat δ₀ δρ) X̂
      B₁' = apply-bwd {n = 1} τ (λ i → concat δ₀ δ (extᵗⁿ n ρ i)) X̂
      a⁺ = as-poly-ren {n = 0} (extᵗⁿ (suc n) ρ) τ (concat (extend δ₀ X) δ)
      b⁺ = as-poly-cong {n = 0} τ (concat-ren-pw ρ δ (extend δ₀ X))
      a₀ = as-poly-ren {n = 0} (extᵗⁿ (suc n) ρ) τ (concat X̂ (concat δ₀ δ))
      cb₁ = as-poly-cong {n = 0} τ (concat-ren-pw (extᵗⁿ n ρ) (concat δ₀ δ) X̂)
      r₁ = trans a₀ cb₁
      a₁ = as-poly-ren {n = 1} (extᵗⁿ n ρ) τ (concat δ₀ δ)
      b₁ = as-poly-cong {n = 1} τ (concat-ren-pw ρ δ δ₀)
      E  = cong (λ P → fobj μ-obj P δ∅) (as-poly-cong {n = 0} τ (concat-pw X̂ (concat-ren-pw ρ δ δ₀)))
      lemC : (cast r₁ δ∅ ∘ B₁) ≈ (B₁' ∘ cast a₁ X̂)
      lemC = inv-conj (apply-fwd-bwd {n = 1} (extᵗⁿ (suc n) ρ *ᵗ τ) (concat δ₀ δ) X̂)
                      (apply-bwd-fwd {n = 1} τ (λ i → concat δ₀ δ (extᵗⁿ n ρ i)) X̂)
                      (apply-fwd-ren {n = 1} (extᵗⁿ n ρ) τ (concat δ₀ δ) X̂)

apply-bwd-ren : ∀ {Δ₁ Δ₂ n} (ρ : TyRen Δ₁ Δ₂) (τ : type (n + Δ₁)) (δ : Fin Δ₂ → obj) (δ₀ : Fin n → obj) →
                (cast (trans (as-poly-ren {n = 0} (extᵗⁿ n ρ) τ (concat δ₀ δ))
                             (as-poly-cong {n = 0} τ (concat-ren-pw ρ δ δ₀))) δ∅
                   ∘ apply-bwd (extᵗⁿ n ρ *ᵗ τ) δ δ₀)
                  ≈ (apply-bwd τ (λ k → δ (ρ k)) δ₀ ∘ cast (as-poly-ren ρ τ δ) δ₀)
apply-bwd-ren {Δ₁} {Δ₂} {n} ρ τ δ δ₀ =
  inv-conj (apply-fwd-bwd (extᵗⁿ n ρ *ᵗ τ) δ δ₀) (apply-bwd-fwd τ (λ k → δ (ρ k)) δ₀)
           (apply-fwd-ren ρ τ δ δ₀)

mutual
  subst-fwd-ren-id : ∀ {Δ Δ'} (ρ : TyRen Δ Δ') (σ : TySub Δ' Δ) (pw : ∀ i → σ (ρ i) ≡ var i)
                     (τ : type Δ) (e : sub σ (ρ *ᵗ τ) ≡ τ) (δ : Fin Δ → obj) →
                     (as-poly-map τ (λ i → ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) (pw i))) δ∅
                        ∘ ≡-to-⇒ (ty-ren ρ τ (λ i → ⟦ σ i ⟧ty δ))
                        ∘ subst-fwd σ (ρ *ᵗ τ) δ)
                       ≈ ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) e)
  subst-fwd-ren-id ρ σ pw (var i) e δ =
    ≈-trans id-right
            (≈-trans (∘-cong ≈-refl (≡-to-⇒-irr (ty-ren ρ (var i) (λ j → ⟦ σ j ⟧ty δ)) refl))
                     (≈-trans id-right
                              (≡-to-⇒-irr (cong (λ υ → ⟦ υ ⟧ty δ) (pw i)) (cong (λ υ → ⟦ υ ⟧ty δ) e))))
  subst-fwd-ren-id ρ σ pw unit e δ =
    ≈-trans id-right (≈-trans id-left (≡-to-⇒-irr refl (cong (λ υ → ⟦ υ ⟧ty δ) e)))
  subst-fwd-ren-id ρ σ pw (base s) e δ =
    ≈-trans id-right (≈-trans id-left (≡-to-⇒-irr refl (cong (λ υ → ⟦ υ ⟧ty δ) e)))
  subst-fwd-ren-id ρ σ pw (τ₁ [→] τ₂) e δ =
    ≈-trans id-right (≈-trans id-left (≡-to-⇒-irr refl (cong (λ υ → ⟦ υ ⟧ty δ) e)))
  subst-fwd-ren-id ρ σ pw (τ₁ [+] τ₂) e δ = begin
      ([+]-map G₁ G₂ ∘ cast (cong₂ Poly._+_ a₁ a₂) δ∅) ∘ [+]-map S₁ S₂
    ≈⟨ ∘-cong (∘-cong ≈-refl (cast-+ a₁ a₂ δ∅)) ≈-refl ⟩
      ([+]-map G₁ G₂ ∘ [+]-map (cast a₁ δ∅) (cast a₂ δ∅)) ∘ [+]-map S₁ S₂
    ≈⟨ ∘-cong ([+]-map-comp _ _ _ _) ≈-refl ⟩
      [+]-map (G₁ ∘ cast a₁ δ∅) (G₂ ∘ cast a₂ δ∅) ∘ [+]-map S₁ S₂
    ≈⟨ [+]-map-comp _ _ _ _ ⟩
      [+]-map ((G₁ ∘ cast a₁ δ∅) ∘ S₁) ((G₂ ∘ cast a₂ δ∅) ∘ S₂)
    ≈⟨ [+]-map-cong (subst-fwd-ren-id ρ σ pw τ₁ (sub-ren-id τ₁ pw) δ)
                    (subst-fwd-ren-id ρ σ pw τ₂ (sub-ren-id τ₂ pw) δ) ⟩
      [+]-map (≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) (sub-ren-id τ₁ pw))) (≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) (sub-ren-id τ₂ pw)))
    ≈˘⟨ ty-cast-+ (sub-ren-id τ₁ pw) (sub-ren-id τ₂ pw) δ ⟩
      ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) (cong₂ _[+]_ (sub-ren-id τ₁ pw) (sub-ren-id τ₂ pw)))
    ≈⟨ ≡-to-⇒-irr (cong (λ υ → ⟦ υ ⟧ty δ) (cong₂ _[+]_ (sub-ren-id τ₁ pw) (sub-ren-id τ₂ pw)))
                  (cong (λ υ → ⟦ υ ⟧ty δ) e) ⟩
      ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) e)
    ∎
    where
      open ≈-Reasoning isEquiv
      δσ : Fin _ → obj
      δσ = λ i → ⟦ σ i ⟧ty δ
      a₁ = as-poly-ren {n = 0} ρ τ₁ δσ
      a₂ = as-poly-ren {n = 0} ρ τ₂ δσ
      G₁ = as-poly-map τ₁ (λ i → ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) (pw i))) δ∅
      G₂ = as-poly-map τ₂ (λ i → ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) (pw i))) δ∅
      S₁ = subst-fwd σ (ρ *ᵗ τ₁) δ
      S₂ = subst-fwd σ (ρ *ᵗ τ₂) δ
  subst-fwd-ren-id ρ σ pw (τ₁ [×] τ₂) e δ = begin
      ([×]-map G₁ G₂ ∘ cast (cong₂ Poly._×_ a₁ a₂) δ∅) ∘ [×]-map S₁ S₂
    ≈⟨ ∘-cong (∘-cong ≈-refl (cast-× a₁ a₂ δ∅)) ≈-refl ⟩
      ([×]-map G₁ G₂ ∘ [×]-map (cast a₁ δ∅) (cast a₂ δ∅)) ∘ [×]-map S₁ S₂
    ≈⟨ ∘-cong ([×]-map-comp _ _ _ _) ≈-refl ⟩
      [×]-map (G₁ ∘ cast a₁ δ∅) (G₂ ∘ cast a₂ δ∅) ∘ [×]-map S₁ S₂
    ≈⟨ [×]-map-comp _ _ _ _ ⟩
      [×]-map ((G₁ ∘ cast a₁ δ∅) ∘ S₁) ((G₂ ∘ cast a₂ δ∅) ∘ S₂)
    ≈⟨ [×]-map-cong (subst-fwd-ren-id ρ σ pw τ₁ (sub-ren-id τ₁ pw) δ)
                    (subst-fwd-ren-id ρ σ pw τ₂ (sub-ren-id τ₂ pw) δ) ⟩
      [×]-map (≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) (sub-ren-id τ₁ pw))) (≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) (sub-ren-id τ₂ pw)))
    ≈˘⟨ ty-cast-× (sub-ren-id τ₁ pw) (sub-ren-id τ₂ pw) δ ⟩
      ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) (cong₂ _[×]_ (sub-ren-id τ₁ pw) (sub-ren-id τ₂ pw)))
    ≈⟨ ≡-to-⇒-irr (cong (λ υ → ⟦ υ ⟧ty δ) (cong₂ _[×]_ (sub-ren-id τ₁ pw) (sub-ren-id τ₂ pw)))
                  (cong (λ υ → ⟦ υ ⟧ty δ) e) ⟩
      ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) e)
    ∎
    where
      open ≈-Reasoning isEquiv
      δσ : Fin _ → obj
      δσ = λ i → ⟦ σ i ⟧ty δ
      a₁ = as-poly-ren {n = 0} ρ τ₁ δσ
      a₂ = as-poly-ren {n = 0} ρ τ₂ δσ
      G₁ = as-poly-map τ₁ (λ i → ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) (pw i))) δ∅
      G₂ = as-poly-map τ₂ (λ i → ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) (pw i))) δ∅
      S₁ = subst-fwd σ (ρ *ᵗ τ₁) δ
      S₂ = subst-fwd σ (ρ *ᵗ τ₂) δ
  subst-fwd-ren-id {Δ} {Δ'} ρ σ pw (μ τ) e δ = begin
      (μ-map Aσρ δ∅ A δ∅ gbA ∘ cast (cong Poly.μ aρ) δ∅) ∘ μ-map P δ∅ Aρ δ∅ bρ
    ≈⟨ ∘-cong (∘-cong ≈-refl (cast-μ aρ δ∅)) ≈-refl ⟩
      (μ-map Aσρ δ∅ A δ∅ gbA ∘ μ-map Aρ δ∅ Aσρ δ∅ (cast aρ (extend δ∅ Mσρ))) ∘ μ-map P δ∅ Aρ δ∅ bρ
    ≈⟨ assoc _ _ _ ⟩
      μ-map Aσρ δ∅ A δ∅ gbA ∘ (μ-map Aρ δ∅ Aσρ δ∅ (cast aρ (extend δ∅ Mσρ)) ∘ μ-map P δ∅ Aρ δ∅ bρ)
    ≈⟨ ∘-cong ≈-refl (μ-map-comp P δ∅ Aρ δ∅ Aσρ δ∅ bρ (cast aρ (extend δ∅ Mσρ)) bσρ
                                 (subst-fwd-body-carrier σ (extᵗ ρ *ᵗ τ) δ k₁)) ⟩
      μ-map Aσρ δ∅ A δ∅ gbA ∘ μ-map P δ∅ Aσρ δ∅ (cast aρ (extend δ∅ Mσρ) ∘ bσρ)
    ≈⟨ μ-map-comp P δ∅ Aσρ δ∅ A δ∅ (cast aρ (extend δ∅ Mσρ) ∘ bσρ) gbA (cast aρ (extend δ∅ MA) ∘ bA) sq₂ ⟩
      μ-map P δ∅ A δ∅ (gbA ∘ (cast aρ (extend δ∅ MA) ∘ bA))
    ≈⟨ μ-map-cong _ _ _ _ (≈-trans (≈-sym (assoc _ _ _)) (subst-fwd-ren-id-body ρ σ pw τ e' δ MA)) ⟩
      μ-map P δ∅ A δ∅ (≡-to-⇒ (cong (λ υ → fobj μ-obj (as-poly {Δ} {1} υ δ) (extend δ∅ MA)) e'))
    ≈˘⟨ ty-cast-μ e' δ ⟩
      ≡-to-⇒ (cong (λ υ → ⟦ μ υ ⟧ty δ) e')
    ≈⟨ ≡-to-⇒-irr (cong (λ υ → ⟦ μ υ ⟧ty δ) e') (cong (λ υ → ⟦ υ ⟧ty δ) e) ⟩
      ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) e)
    ∎
    where
      open ≈-Reasoning isEquiv
      δσ : Fin Δ' → obj
      δσ = λ i → ⟦ σ i ⟧ty δ
      gs : ∀ i → ⟦ σ (ρ i) ⟧ty δ ⇒ δ i
      gs = λ i → ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) (pw i))
      pw-lift : ∀ i → sub-lift σ (extᵗ ρ i) ≡ var i
      pw-lift Fin.zero    = refl
      pw-lift (Fin.suc i) = cong (Fin.suc *ᵗ_) (pw i)
      e' : sub (sub-lift σ) (extᵗ ρ *ᵗ τ) ≡ τ
      e' = sub-ren-id τ pw-lift
      aρ  = as-poly-ren {n = 1} ρ τ δσ
      P   = as-poly {Δ} {1} (sub (sub-lift σ) (extᵗ ρ *ᵗ τ)) δ
      Aρ  = as-poly {Δ'} {1} (extᵗ ρ *ᵗ τ) δσ
      Aσρ = as-poly {Δ} {1} τ (λ i → ⟦ σ (ρ i) ⟧ty δ)
      A   = as-poly {Δ} {1} τ δ
      Mσρ = μ-obj Aσρ δ∅
      MA  = μ-obj A δ∅
      gbA = as-poly-map {n = 1} τ gs (extend δ∅ MA)
      bρ  = subst-fwd-body σ (extᵗ ρ *ᵗ τ) δ (μ-obj Aρ δ∅)
      bσρ = subst-fwd-body σ (extᵗ ρ *ᵗ τ) δ Mσρ
      bA  = subst-fwd-body σ (extᵗ ρ *ᵗ τ) δ MA
      k₁  = μ-map Aρ δ∅ Aσρ δ∅ (cast aρ (extend δ∅ Mσρ))
      k₂  = μ-map Aσρ δ∅ A δ∅ gbA
      sq₂ : (fmor Aσρ (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k₂) ∘ (cast aρ (extend δ∅ Mσρ) ∘ bσρ))
              ≈ ((cast aρ (extend δ∅ MA) ∘ bA) ∘ fmor P (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k₂))
      sq₂ = ≈-trans (≈-sym (assoc _ _ _))
            (≈-trans (∘-cong (cast-natural aρ (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k₂)) ≈-refl)
            (≈-trans (assoc _ _ _)
            (≈-trans (∘-cong ≈-refl (subst-fwd-body-carrier σ (extᵗ ρ *ᵗ τ) δ k₂))
                     (≈-sym (assoc _ _ _)))))

  subst-fwd-ren-id-body : ∀ {Δ Δ'} (ρ : TyRen Δ Δ') (σ : TySub Δ' Δ) (pw : ∀ i → σ (ρ i) ≡ var i)
                          (τ : type (suc Δ)) (e : sub (sub-lift σ) (extᵗ ρ *ᵗ τ) ≡ τ)
                          (δ : Fin Δ → obj) (X : obj) →
                          (as-poly-map {n = 1} τ (λ i → ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) (pw i))) (extend δ∅ X)
                             ∘ cast (as-poly-ren {n = 1} ρ τ (λ i → ⟦ σ i ⟧ty δ)) (extend δ∅ X)
                             ∘ subst-fwd-body σ (extᵗ ρ *ᵗ τ) δ X)
                            ≈ ≡-to-⇒ (cong (λ υ → fobj μ-obj (as-poly {Δ} {1} υ δ) (extend δ∅ X)) e)
  subst-fwd-ren-id-body {Δ} {Δ'} ρ σ pw τ e δ X = begin
      (G ∘ Cρ) ∘ (F ∘ L ∘ S ∘ B)
    ≈⟨ assoc _ _ _ ⟩
      G ∘ (Cρ ∘ (F ∘ L ∘ S ∘ B))
    ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl (≈-trans (∘-cong (assoc _ _ _) ≈-refl)
                                             (≈-trans (assoc _ _ _) (∘-cong ≈-refl (assoc _ _ _))))) ⟩
      G ∘ (Cρ ∘ (F ∘ (L ∘ (S ∘ B))))
    ≈˘⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
      G ∘ ((Cρ ∘ F) ∘ (L ∘ (S ∘ B)))
    ≈⟨ ∘-cong ≈-refl (∘-cong (apply-fwd-ren {n = 1} ρ τ δσ (extend δ∅ X)) ≈-refl) ⟩
      G ∘ ((F'' ∘ cast (trans a₁ b₁) δ∅) ∘ (L ∘ (S ∘ B)))
    ≈⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
      G ∘ (F'' ∘ (cast (trans a₁ b₁) δ∅ ∘ (L ∘ (S ∘ B))))
    ≈˘⟨ assoc _ _ _ ⟩
      (G ∘ F'') ∘ (cast (trans a₁ b₁) δ∅ ∘ (L ∘ (S ∘ B)))
    ≈˘⟨ ∘-cong (apply-fwd-map {n = 1} τ gs (extend δ∅ X)) ≈-refl ⟩
      (F' ∘ K) ∘ (cast (trans a₁ b₁) δ∅ ∘ (L ∘ (S ∘ B)))
    ≈⟨ assoc _ _ _ ⟩
      F' ∘ (K ∘ (cast (trans a₁ b₁) δ∅ ∘ (L ∘ (S ∘ B))))
    ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl (∘-cong (cast-trans a₁ b₁ δ∅) ≈-refl)) ⟩
      F' ∘ (K ∘ ((cast b₁ δ∅ ∘ cast a₁ δ∅) ∘ (L ∘ (S ∘ B))))
    ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl (assoc _ _ _)) ⟩
      F' ∘ (K ∘ (cast b₁ δ∅ ∘ (cast a₁ δ∅ ∘ (L ∘ (S ∘ B)))))
    ≈˘⟨ ∘-cong ≈-refl (∘-cong ≈-refl (∘-cong ≈-refl (assoc _ _ _))) ⟩
      F' ∘ (K ∘ (cast b₁ δ∅ ∘ ((cast a₁ δ∅ ∘ L) ∘ (S ∘ B))))
    ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl (∘-cong ≈-refl (∘-cong (as-poly-map-ren (extᵗ ρ) τ Lfam δ∅) ≈-refl))) ⟩
      F' ∘ (K ∘ (cast b₁ δ∅ ∘ ((Lρ ∘ cast aL δ∅) ∘ (S ∘ B))))
    ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl (∘-cong ≈-refl (assoc _ _ _))) ⟩
      F' ∘ (K ∘ (cast b₁ δ∅ ∘ (Lρ ∘ (cast aL δ∅ ∘ (S ∘ B)))))
    ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl (∘-cong (cast-as-poly-cong {n = 0} τ (concat-ren-pw ρ δσ (extend δ∅ X)) δ∅) ≈-refl)) ⟩
      F' ∘ (K ∘ (Hc ∘ (Lρ ∘ (cast aL δ∅ ∘ (S ∘ B)))))
    ≈˘⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
      F' ∘ ((K ∘ Hc) ∘ (Lρ ∘ (cast aL δ∅ ∘ (S ∘ B))))
    ≈˘⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
      F' ∘ (((K ∘ Hc) ∘ Lρ) ∘ (cast aL δ∅ ∘ (S ∘ B)))
    ≈⟨ ∘-cong ≈-refl (∘-cong (∘-cong (as-poly-map-comp τ Kfam hfam δ∅) ≈-refl) ≈-refl) ⟩
      F' ∘ ((as-poly-map τ (λ i → Kfam i ∘ hfam i) δ∅ ∘ Lρ) ∘ (cast aL δ∅ ∘ (S ∘ B)))
    ≈⟨ ∘-cong ≈-refl (∘-cong (as-poly-map-comp τ (λ i → Kfam i ∘ hfam i) (λ i → Lfam (extᵗ ρ i)) δ∅) ≈-refl) ⟩
      F' ∘ (as-poly-map τ (λ i → (Kfam i ∘ hfam i) ∘ Lfam (extᵗ ρ i)) δ∅ ∘ (cast aL δ∅ ∘ (S ∘ B)))
    ≈⟨ ∘-cong ≈-refl (∘-cong (as-poly-map-cong τ pw-step δ∅) ≈-refl) ⟩
      F' ∘ (PL ∘ (cast aL δ∅ ∘ (S ∘ B)))
    ≈˘⟨ ∘-cong ≈-refl (∘-cong ≈-refl (assoc _ _ _)) ⟩
      F' ∘ (PL ∘ ((cast aL δ∅ ∘ S) ∘ B))
    ≈˘⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
      F' ∘ ((PL ∘ (cast aL δ∅ ∘ S)) ∘ B)
    ≈˘⟨ ∘-cong ≈-refl (∘-cong (assoc _ _ _) ≈-refl) ⟩
      F' ∘ (((PL ∘ cast aL δ∅) ∘ S) ∘ B)
    ≈⟨ ∘-cong ≈-refl (∘-cong (subst-fwd-ren-id (extᵗ ρ) (sub-lift σ) pw-lift τ e γ) ≈-refl) ⟩
      F' ∘ (≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty γ) e) ∘ B)
    ≈˘⟨ ∘-cong ≈-refl (ty-square (λ υ → fobj μ-obj (as-poly {Δ} {1} υ δ) (extend δ∅ X)) (λ υ → ⟦ υ ⟧ty γ)
                                 (λ υ → apply-bwd {n = 1} υ δ (extend δ∅ X)) e) ⟩
      F' ∘ (apply-bwd {n = 1} τ δ (extend δ∅ X)
              ∘ ≡-to-⇒ (cong (λ υ → fobj μ-obj (as-poly {Δ} {1} υ δ) (extend δ∅ X)) e))
    ≈˘⟨ assoc _ _ _ ⟩
      (F' ∘ apply-bwd {n = 1} τ δ (extend δ∅ X))
        ∘ ≡-to-⇒ (cong (λ υ → fobj μ-obj (as-poly {Δ} {1} υ δ) (extend δ∅ X)) e)
    ≈⟨ ∘-cong (apply-fwd-bwd {n = 1} τ δ (extend δ∅ X)) ≈-refl ⟩
      id _ ∘ ≡-to-⇒ (cong (λ υ → fobj μ-obj (as-poly {Δ} {1} υ δ) (extend δ∅ X)) e)
    ≈⟨ id-left ⟩
      ≡-to-⇒ (cong (λ υ → fobj μ-obj (as-poly {Δ} {1} υ δ) (extend δ∅ X)) e)
    ∎
    where
      open ≈-Reasoning isEquiv
      γ  = concat (extend {0} δ∅ X) δ
      δσ : Fin Δ' → obj
      δσ = λ i → ⟦ σ i ⟧ty δ
      γσ = concat (extend {0} δ∅ X) δσ
      gs : ∀ i → ⟦ σ (ρ i) ⟧ty δ ⇒ δ i
      gs = λ i → ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) (pw i))
      pw-lift : ∀ i → sub-lift σ (extᵗ ρ i) ≡ var i
      pw-lift Fin.zero    = refl
      pw-lift (Fin.suc i) = cong (Fin.suc *ᵗ_) (pw i)
      a₁ = as-poly-ren {n = 0} (extᵗⁿ 1 ρ) τ γσ
      b₁ = as-poly-cong {n = 0} τ (concat-ren-pw ρ δσ (extend δ∅ X))
      aL = as-poly-ren {n = 0} (extᵗ ρ) τ (λ i → ⟦ sub-lift σ i ⟧ty γ)
      G  = as-poly-map {n = 1} τ gs (extend δ∅ X)
      Cρ = cast (as-poly-ren {n = 1} ρ τ δσ) (extend δ∅ X)
      F   = apply-fwd {n = 1} (extᵗ ρ *ᵗ τ) δσ (extend δ∅ X)
      F'  = apply-fwd {n = 1} τ δ (extend δ∅ X)
      F'' = apply-fwd {n = 1} τ (λ k → δσ (ρ k)) (extend δ∅ X)
      Kfam = concat-mor {n = 1} {δ₀ = extend {0} δ∅ X} (λ i → id _) gs
      K  = as-poly-map τ Kfam δ∅
      Lfam = λ i → ≡-to-⇒ (sub-lift-pw σ δ X i)
      L  = as-poly-map (extᵗ ρ *ᵗ τ) Lfam δ∅
      Lρ = as-poly-map τ (λ i → Lfam (extᵗ ρ i)) δ∅
      hfam = λ i → ≡-to-⇒ (concat-ren-pw ρ δσ (extend δ∅ X) i)
      Hc = as-poly-map τ hfam δ∅
      PLfam = λ i → ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty γ) (pw-lift i))
      PL = as-poly-map τ PLfam δ∅
      S  = subst-fwd (sub-lift σ) (extᵗ ρ *ᵗ τ) γ
      B  = apply-bwd {n = 1} (sub (sub-lift σ) (extᵗ ρ *ᵗ τ)) δ (extend δ∅ X)
      pw-step : ∀ i → ((Kfam i ∘ hfam i) ∘ Lfam (extᵗ ρ i)) ≈ PLfam i
      pw-step Fin.zero =
        ≈-trans id-right (≈-trans id-left (≡-to-⇒-irr (concat-ren-pw ρ δσ (extend δ∅ X) Fin.zero) refl))
      pw-step (Fin.suc j) =
        ≈-trans (∘-cong (≈-trans (∘-cong ≈-refl (≡-to-⇒-irr (concat-ren-pw ρ δσ (extend δ∅ X) (Fin.suc j)) refl))
                                 id-right)
                        ≈-refl)
        (≈-trans (≈-sym (ty-square (λ υ → ⟦ Fin.suc *ᵗ υ ⟧ty γ) (λ υ → ⟦ υ ⟧ty δ)
                                   (λ υ → ≡-to-⇒ (ty-ren Fin.suc υ γ)) (pw j)))
        (≈-trans (∘-cong (≡-to-⇒-irr (ty-ren Fin.suc (var j) γ) refl) ≈-refl)
        (≈-trans id-left
                 (≡-to-⇒-irr (cong (λ υ → ⟦ Fin.suc *ᵗ υ ⟧ty γ) (pw j))
                             (cong (λ υ → ⟦ υ ⟧ty γ) (pw-lift (Fin.suc j)))))))

mutual
  subst-fwd-ren-sub : ∀ {Δ₁ Δ₁' Δ₂ Δ₂'} (ρ : TyRen Δ₁ Δ₂) (ρ' : TyRen Δ₁' Δ₂')
                      (σ : TySub Δ₁ Δ₁') (σ' : TySub Δ₂ Δ₂') (pw : ∀ i → σ' (ρ i) ≡ ρ' *ᵗ σ i)
                      (τ : type Δ₁) (e : sub σ' (ρ *ᵗ τ) ≡ ρ' *ᵗ sub σ τ) (δ : Fin Δ₂' → obj) →
                      (as-poly-map τ (λ i → ≡-to-⇒ (ty-ren ρ' (σ i) δ)
                                              ∘ ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) (pw i))) δ∅
                         ∘ ≡-to-⇒ (ty-ren ρ τ (λ j → ⟦ σ' j ⟧ty δ))
                         ∘ subst-fwd σ' (ρ *ᵗ τ) δ)
                        ≈ (subst-fwd σ τ (λ k → δ (ρ' k))
                             ∘ ≡-to-⇒ (ty-ren ρ' (sub σ τ) δ)
                             ∘ ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) e))
  subst-fwd-ren-sub ρ ρ' σ σ' pw (var i) e δ =
    ≈-trans id-right
    (≈-trans (∘-cong ≈-refl (≡-to-⇒-irr (ty-ren ρ (var i) (λ j → ⟦ σ' j ⟧ty δ)) refl))
    (≈-trans id-right
    (≈-trans (∘-cong ≈-refl (≡-to-⇒-irr (cong (λ υ → ⟦ υ ⟧ty δ) (pw i)) (cong (λ υ → ⟦ υ ⟧ty δ) e)))
             (∘-cong (≈-sym id-left) ≈-refl))))
  subst-fwd-ren-sub ρ ρ' σ σ' pw unit e δ =
    ≈-trans (≈-trans id-right (≈-trans id-left (≡-to-⇒-irr (ty-ren ρ unit (λ j → ⟦ σ' j ⟧ty δ)) refl)))
            (≈-sym (≈-trans (∘-cong id-left ≈-refl)
                   (≈-trans (≡-to-⇒-comp (cong (λ υ → ⟦ υ ⟧ty δ) e) (ty-ren ρ' unit δ))
                            (≡-to-⇒-irr (trans (cong (λ υ → ⟦ υ ⟧ty δ) e) (ty-ren ρ' unit δ)) refl))))
  subst-fwd-ren-sub ρ ρ' σ σ' pw (base s) e δ =
    ≈-trans (≈-trans id-right (≈-trans id-left (≡-to-⇒-irr (ty-ren ρ (base s) (λ j → ⟦ σ' j ⟧ty δ)) refl)))
            (≈-sym (≈-trans (∘-cong id-left ≈-refl)
                   (≈-trans (≡-to-⇒-comp (cong (λ υ → ⟦ υ ⟧ty δ) e) (ty-ren ρ' (base s) δ))
                            (≡-to-⇒-irr (trans (cong (λ υ → ⟦ υ ⟧ty δ) e) (ty-ren ρ' (base s) δ)) refl))))
  subst-fwd-ren-sub ρ ρ' σ σ' pw (τ₁ [→] τ₂) e δ =
    ≈-trans (≈-trans id-right (≈-trans id-left (≡-to-⇒-irr (ty-ren ρ (τ₁ [→] τ₂) (λ j → ⟦ σ' j ⟧ty δ)) refl)))
            (≈-sym (≈-trans (∘-cong id-left ≈-refl)
                   (≈-trans (≡-to-⇒-comp (cong (λ υ → ⟦ υ ⟧ty δ) e) (ty-ren ρ' (τ₁ [→] τ₂) δ))
                            (≡-to-⇒-irr (trans (cong (λ υ → ⟦ υ ⟧ty δ) e) (ty-ren ρ' (τ₁ [→] τ₂) δ)) refl))))
  subst-fwd-ren-sub ρ ρ' σ σ' pw (τ₁ [+] τ₂) e δ = begin
      ([+]-map G₁ G₂ ∘ cast (cong₂ Poly._+_ a₁ a₂) δ∅) ∘ [+]-map S₁ S₂
    ≈⟨ ∘-cong (∘-cong ≈-refl (cast-+ a₁ a₂ δ∅)) ≈-refl ⟩
      ([+]-map G₁ G₂ ∘ [+]-map (cast a₁ δ∅) (cast a₂ δ∅)) ∘ [+]-map S₁ S₂
    ≈⟨ ∘-cong ([+]-map-comp _ _ _ _) ≈-refl ⟩
      [+]-map (G₁ ∘ cast a₁ δ∅) (G₂ ∘ cast a₂ δ∅) ∘ [+]-map S₁ S₂
    ≈⟨ [+]-map-comp _ _ _ _ ⟩
      [+]-map ((G₁ ∘ cast a₁ δ∅) ∘ S₁) ((G₂ ∘ cast a₂ δ∅) ∘ S₂)
    ≈⟨ [+]-map-cong (subst-fwd-ren-sub ρ ρ' σ σ' pw τ₁ e₁ δ) (subst-fwd-ren-sub ρ ρ' σ σ' pw τ₂ e₂ δ) ⟩
      [+]-map ((T₁ ∘ cast b₁ δ∅) ∘ E₁) ((T₂ ∘ cast b₂ δ∅) ∘ E₂)
    ≈˘⟨ [+]-map-comp _ _ _ _ ⟩
      [+]-map (T₁ ∘ cast b₁ δ∅) (T₂ ∘ cast b₂ δ∅) ∘ [+]-map E₁ E₂
    ≈˘⟨ ∘-cong ([+]-map-comp _ _ _ _) ≈-refl ⟩
      ([+]-map T₁ T₂ ∘ [+]-map (cast b₁ δ∅) (cast b₂ δ∅)) ∘ [+]-map E₁ E₂
    ≈˘⟨ ∘-cong (∘-cong ≈-refl (cast-+ b₁ b₂ δ∅)) ≈-refl ⟩
      ([+]-map T₁ T₂ ∘ cast (cong₂ Poly._+_ b₁ b₂) δ∅) ∘ [+]-map E₁ E₂
    ≈˘⟨ ∘-cong ≈-refl (ty-cast-+ e₁ e₂ δ) ⟩
      ([+]-map T₁ T₂ ∘ cast (cong₂ Poly._+_ b₁ b₂) δ∅) ∘ ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) (cong₂ _[+]_ e₁ e₂))
    ≈⟨ ∘-cong ≈-refl (≡-to-⇒-irr (cong (λ υ → ⟦ υ ⟧ty δ) (cong₂ _[+]_ e₁ e₂)) (cong (λ υ → ⟦ υ ⟧ty δ) e)) ⟩
      ([+]-map T₁ T₂ ∘ cast (cong₂ Poly._+_ b₁ b₂) δ∅) ∘ ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) e)
    ∎
    where
      open ≈-Reasoning isEquiv
      δσ' : Fin _ → obj
      δσ' = λ j → ⟦ σ' j ⟧ty δ
      δρ' : Fin _ → obj
      δρ' = λ k → δ (ρ' k)
      e₁ = sub-ren-comm ρ ρ' σ σ' pw τ₁
      e₂ = sub-ren-comm ρ ρ' σ σ' pw τ₂
      a₁ = as-poly-ren {n = 0} ρ τ₁ δσ'
      a₂ = as-poly-ren {n = 0} ρ τ₂ δσ'
      b₁ = as-poly-ren {n = 0} ρ' (sub σ τ₁) δ
      b₂ = as-poly-ren {n = 0} ρ' (sub σ τ₂) δ
      G₁ = as-poly-map τ₁ (λ i → ≡-to-⇒ (ty-ren ρ' (σ i) δ) ∘ ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) (pw i))) δ∅
      G₂ = as-poly-map τ₂ (λ i → ≡-to-⇒ (ty-ren ρ' (σ i) δ) ∘ ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) (pw i))) δ∅
      S₁ = subst-fwd σ' (ρ *ᵗ τ₁) δ
      S₂ = subst-fwd σ' (ρ *ᵗ τ₂) δ
      T₁ = subst-fwd σ τ₁ δρ'
      T₂ = subst-fwd σ τ₂ δρ'
      E₁ = ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) e₁)
      E₂ = ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) e₂)
  subst-fwd-ren-sub ρ ρ' σ σ' pw (τ₁ [×] τ₂) e δ = begin
      ([×]-map G₁ G₂ ∘ cast (cong₂ Poly._×_ a₁ a₂) δ∅) ∘ [×]-map S₁ S₂
    ≈⟨ ∘-cong (∘-cong ≈-refl (cast-× a₁ a₂ δ∅)) ≈-refl ⟩
      ([×]-map G₁ G₂ ∘ [×]-map (cast a₁ δ∅) (cast a₂ δ∅)) ∘ [×]-map S₁ S₂
    ≈⟨ ∘-cong ([×]-map-comp _ _ _ _) ≈-refl ⟩
      [×]-map (G₁ ∘ cast a₁ δ∅) (G₂ ∘ cast a₂ δ∅) ∘ [×]-map S₁ S₂
    ≈⟨ [×]-map-comp _ _ _ _ ⟩
      [×]-map ((G₁ ∘ cast a₁ δ∅) ∘ S₁) ((G₂ ∘ cast a₂ δ∅) ∘ S₂)
    ≈⟨ [×]-map-cong (subst-fwd-ren-sub ρ ρ' σ σ' pw τ₁ e₁ δ) (subst-fwd-ren-sub ρ ρ' σ σ' pw τ₂ e₂ δ) ⟩
      [×]-map ((T₁ ∘ cast b₁ δ∅) ∘ E₁) ((T₂ ∘ cast b₂ δ∅) ∘ E₂)
    ≈˘⟨ [×]-map-comp _ _ _ _ ⟩
      [×]-map (T₁ ∘ cast b₁ δ∅) (T₂ ∘ cast b₂ δ∅) ∘ [×]-map E₁ E₂
    ≈˘⟨ ∘-cong ([×]-map-comp _ _ _ _) ≈-refl ⟩
      ([×]-map T₁ T₂ ∘ [×]-map (cast b₁ δ∅) (cast b₂ δ∅)) ∘ [×]-map E₁ E₂
    ≈˘⟨ ∘-cong (∘-cong ≈-refl (cast-× b₁ b₂ δ∅)) ≈-refl ⟩
      ([×]-map T₁ T₂ ∘ cast (cong₂ Poly._×_ b₁ b₂) δ∅) ∘ [×]-map E₁ E₂
    ≈˘⟨ ∘-cong ≈-refl (ty-cast-× e₁ e₂ δ) ⟩
      ([×]-map T₁ T₂ ∘ cast (cong₂ Poly._×_ b₁ b₂) δ∅) ∘ ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) (cong₂ _[×]_ e₁ e₂))
    ≈⟨ ∘-cong ≈-refl (≡-to-⇒-irr (cong (λ υ → ⟦ υ ⟧ty δ) (cong₂ _[×]_ e₁ e₂)) (cong (λ υ → ⟦ υ ⟧ty δ) e)) ⟩
      ([×]-map T₁ T₂ ∘ cast (cong₂ Poly._×_ b₁ b₂) δ∅) ∘ ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) e)
    ∎
    where
      open ≈-Reasoning isEquiv
      δσ' : Fin _ → obj
      δσ' = λ j → ⟦ σ' j ⟧ty δ
      δρ' : Fin _ → obj
      δρ' = λ k → δ (ρ' k)
      e₁ = sub-ren-comm ρ ρ' σ σ' pw τ₁
      e₂ = sub-ren-comm ρ ρ' σ σ' pw τ₂
      a₁ = as-poly-ren {n = 0} ρ τ₁ δσ'
      a₂ = as-poly-ren {n = 0} ρ τ₂ δσ'
      b₁ = as-poly-ren {n = 0} ρ' (sub σ τ₁) δ
      b₂ = as-poly-ren {n = 0} ρ' (sub σ τ₂) δ
      G₁ = as-poly-map τ₁ (λ i → ≡-to-⇒ (ty-ren ρ' (σ i) δ) ∘ ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) (pw i))) δ∅
      G₂ = as-poly-map τ₂ (λ i → ≡-to-⇒ (ty-ren ρ' (σ i) δ) ∘ ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) (pw i))) δ∅
      S₁ = subst-fwd σ' (ρ *ᵗ τ₁) δ
      S₂ = subst-fwd σ' (ρ *ᵗ τ₂) δ
      T₁ = subst-fwd σ τ₁ δρ'
      T₂ = subst-fwd σ τ₂ δρ'
      E₁ = ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) e₁)
      E₂ = ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) e₂)
  subst-fwd-ren-sub {Δ₁} {Δ₁'} {Δ₂} {Δ₂'} ρ ρ' σ σ' pw (μ τ) e δ = begin
      (μ-map A δ∅ A' δ∅ gb ∘ cast (cong Poly.μ aρ) δ∅) ∘ μ-map P δ∅ Aρ δ∅ bρ
    ≈⟨ ∘-cong (∘-cong ≈-refl (cast-μ aρ δ∅)) ≈-refl ⟩
      (μ-map A δ∅ A' δ∅ gb ∘ μ-map Aρ δ∅ A δ∅ ca) ∘ μ-map P δ∅ Aρ δ∅ bρ
    ≈⟨ assoc _ _ _ ⟩
      μ-map A δ∅ A' δ∅ gb ∘ (μ-map Aρ δ∅ A δ∅ ca ∘ μ-map P δ∅ Aρ δ∅ bρ)
    ≈⟨ ∘-cong ≈-refl (μ-map-comp P δ∅ Aρ δ∅ A δ∅ bρ ca bA
                                 (subst-fwd-body-carrier σ' (extᵗ ρ *ᵗ τ) δ k₁)) ⟩
      μ-map A δ∅ A' δ∅ gb ∘ μ-map P δ∅ A δ∅ (ca ∘ bA)
    ≈⟨ μ-map-comp P δ∅ A δ∅ A' δ∅ (ca ∘ bA) gb (ca' ∘ bM') sq₂ ⟩
      μ-map P δ∅ A' δ∅ (gb ∘ (ca' ∘ bM'))
    ≈⟨ μ-map-cong _ _ _ _ (≈-trans (≈-sym (assoc _ _ _))
                                   (subst-fwd-ren-sub-body ρ ρ' σ σ' pw τ e° δ M')) ⟩
      μ-map P δ∅ A' δ∅ ((B' ∘ cb) ∘ Ce M')
    ≈⟨ μ-map-cong _ _ _ _ (assoc _ _ _) ⟩
      μ-map P δ∅ A' δ∅ (B' ∘ (cb ∘ Ce M'))
    ≈˘⟨ μ-map-comp P δ∅ Q δ∅ A' δ∅ (cbQ ∘ Ce MQ) B' (cb ∘ Ce M') sq₄ ⟩
      μ-map Q δ∅ A' δ∅ B' ∘ μ-map P δ∅ Q δ∅ (cbQ ∘ Ce MQ)
    ≈˘⟨ ∘-cong ≈-refl (μ-map-comp P δ∅ Rb δ∅ Q δ∅ (Ce MRb) cbQ (Ce MQ) sq₃) ⟩
      μ-map Q δ∅ A' δ∅ B' ∘ (μ-map Rb δ∅ Q δ∅ cbQ ∘ μ-map P δ∅ Rb δ∅ (Ce MRb))
    ≈˘⟨ assoc _ _ _ ⟩
      (μ-map Q δ∅ A' δ∅ B' ∘ μ-map Rb δ∅ Q δ∅ cbQ) ∘ μ-map P δ∅ Rb δ∅ (Ce MRb)
    ≈˘⟨ ∘-cong (∘-cong ≈-refl (cast-μ b δ∅)) ≈-refl ⟩
      (μ-map Q δ∅ A' δ∅ B' ∘ cast (cong Poly.μ b) δ∅) ∘ μ-map P δ∅ Rb δ∅ (Ce MRb)
    ≈˘⟨ ∘-cong ≈-refl (ty-cast-μ e° δ) ⟩
      (μ-map Q δ∅ A' δ∅ B' ∘ cast (cong Poly.μ b) δ∅) ∘ ≡-to-⇒ (cong (λ υ → ⟦ μ υ ⟧ty δ) e°)
    ≈⟨ ∘-cong ≈-refl (≡-to-⇒-irr (cong (λ υ → ⟦ μ υ ⟧ty δ) e°) (cong (λ υ → ⟦ υ ⟧ty δ) e)) ⟩
      (μ-map Q δ∅ A' δ∅ B' ∘ cast (cong Poly.μ b) δ∅) ∘ ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) e)
    ∎
    where
      open ≈-Reasoning isEquiv
      δσ' : Fin Δ₂ → obj
      δσ' = λ j → ⟦ σ' j ⟧ty δ
      δρ' : Fin Δ₁' → obj
      δρ' = λ k → δ (ρ' k)
      fam : ∀ i → ⟦ σ' (ρ i) ⟧ty δ ⇒ ⟦ σ i ⟧ty δρ'
      fam = λ i → ≡-to-⇒ (ty-ren ρ' (σ i) δ) ∘ ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) (pw i))
      pw-lift : ∀ i → sub-lift σ' (extᵗ ρ i) ≡ extᵗ ρ' *ᵗ sub-lift σ i
      pw-lift Fin.zero    = refl
      pw-lift (Fin.suc i) =
        trans (cong (Fin.suc *ᵗ_) (pw i))
              (trans (ren-ren Fin.suc ρ' (σ i)) (sym (ren-ren (extᵗ ρ') Fin.suc (σ i))))
      e° : sub (sub-lift σ') (extᵗ ρ *ᵗ τ) ≡ extᵗ ρ' *ᵗ sub (sub-lift σ) τ
      e° = sub-ren-comm (extᵗ ρ) (extᵗ ρ') (sub-lift σ) (sub-lift σ') pw-lift τ
      aρ = as-poly-ren {n = 1} ρ τ δσ'
      b  = as-poly-ren {n = 1} ρ' (sub (sub-lift σ) τ) δ
      P  = as-poly {Δ₂'} {1} (sub (sub-lift σ') (extᵗ ρ *ᵗ τ)) δ
      Aρ = as-poly {Δ₂} {1} (extᵗ ρ *ᵗ τ) δσ'
      A  = as-poly {Δ₁} {1} τ (λ i → ⟦ σ' (ρ i) ⟧ty δ)
      A' = as-poly {Δ₁} {1} τ (λ i → ⟦ σ i ⟧ty δρ')
      Rb = as-poly {Δ₂'} {1} (extᵗ ρ' *ᵗ sub (sub-lift σ) τ) δ
      Q  = as-poly {Δ₁'} {1} (sub (sub-lift σ) τ) δρ'
      MA  = μ-obj A δ∅
      M'  = μ-obj A' δ∅
      MQ  = μ-obj Q δ∅
      MRb = μ-obj Rb δ∅
      gb  = as-poly-map {n = 1} τ fam (extend δ∅ M')
      ca  = cast aρ (extend δ∅ MA)
      ca' = cast aρ (extend δ∅ M')
      cb  = cast b (extend δ∅ M')
      cbQ = cast b (extend δ∅ MQ)
      bρ  = subst-fwd-body σ' (extᵗ ρ *ᵗ τ) δ (μ-obj Aρ δ∅)
      bA  = subst-fwd-body σ' (extᵗ ρ *ᵗ τ) δ MA
      bM' = subst-fwd-body σ' (extᵗ ρ *ᵗ τ) δ M'
      B'  = subst-fwd-body σ τ δρ' M'
      Ce : (Y : obj) → fobj μ-obj P (extend δ∅ Y) ⇒ fobj μ-obj Rb (extend δ∅ Y)
      Ce Y = ≡-to-⇒ (cong (λ υ → fobj μ-obj (as-poly {Δ₂'} {1} υ δ) (extend δ∅ Y)) e°)
      k₁ = μ-map Aρ δ∅ A δ∅ ca
      k₂ = μ-map A δ∅ A' δ∅ gb
      k₃ = μ-map Rb δ∅ Q δ∅ cbQ
      k₄ = μ-map Q δ∅ A' δ∅ B'
      sq₂ : (fmor A (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k₂) ∘ (ca ∘ bA))
              ≈ ((ca' ∘ bM') ∘ fmor P (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k₂))
      sq₂ = ≈-trans (≈-sym (assoc _ _ _))
            (≈-trans (∘-cong (cast-natural aρ (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k₂)) ≈-refl)
            (≈-trans (assoc _ _ _)
            (≈-trans (∘-cong ≈-refl (subst-fwd-body-carrier σ' (extᵗ ρ *ᵗ τ) δ k₂))
                     (≈-sym (assoc _ _ _)))))
      sq₃ : (fmor Rb (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k₃) ∘ Ce MRb)
              ≈ (Ce MQ ∘ fmor P (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k₃))
      sq₃ = ty-square (λ υ → fobj μ-obj (as-poly {Δ₂'} {1} υ δ) (extend δ∅ MRb))
                      (λ υ → fobj μ-obj (as-poly {Δ₂'} {1} υ δ) (extend δ∅ MQ))
                      (λ υ → fmor (as-poly {Δ₂'} {1} υ δ)
                                  (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k₃)) e°
      sq₄ : (fmor Q (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k₄) ∘ (cbQ ∘ Ce MQ))
              ≈ ((cb ∘ Ce M') ∘ fmor P (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k₄))
      sq₄ = ≈-trans (≈-sym (assoc _ _ _))
            (≈-trans (∘-cong (cast-natural b (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k₄)) ≈-refl)
            (≈-trans (assoc _ _ _)
            (≈-trans (∘-cong ≈-refl
                             (ty-square (λ υ → fobj μ-obj (as-poly {Δ₂'} {1} υ δ) (extend δ∅ MQ))
                                        (λ υ → fobj μ-obj (as-poly {Δ₂'} {1} υ δ) (extend δ∅ M'))
                                        (λ υ → fmor (as-poly {Δ₂'} {1} υ δ)
                                                    (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k₄)) e°))
                     (≈-sym (assoc _ _ _)))))

  subst-fwd-ren-sub-body : ∀ {Δ₁ Δ₁' Δ₂ Δ₂'} (ρ : TyRen Δ₁ Δ₂) (ρ' : TyRen Δ₁' Δ₂')
                           (σ : TySub Δ₁ Δ₁') (σ' : TySub Δ₂ Δ₂') (pw : ∀ i → σ' (ρ i) ≡ ρ' *ᵗ σ i)
                           (τ : type (suc Δ₁))
                           (e : sub (sub-lift σ') (extᵗ ρ *ᵗ τ) ≡ extᵗ ρ' *ᵗ sub (sub-lift σ) τ)
                           (δ : Fin Δ₂' → obj) (X : obj) →
                           (as-poly-map {n = 1} τ (λ i → ≡-to-⇒ (ty-ren ρ' (σ i) δ)
                                                           ∘ ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) (pw i))) (extend δ∅ X)
                              ∘ cast (as-poly-ren {n = 1} ρ τ (λ j → ⟦ σ' j ⟧ty δ)) (extend δ∅ X)
                              ∘ subst-fwd-body σ' (extᵗ ρ *ᵗ τ) δ X)
                             ≈ (subst-fwd-body σ τ (λ k → δ (ρ' k)) X
                                  ∘ cast (as-poly-ren {n = 1} ρ' (sub (sub-lift σ) τ) δ) (extend δ∅ X)
                                  ∘ ≡-to-⇒ (cong (λ υ → fobj μ-obj (as-poly {Δ₂'} {1} υ δ) (extend δ∅ X)) e))
  subst-fwd-ren-sub-body {Δ₁} {Δ₁'} {Δ₂} {Δ₂'} ρ ρ' σ σ' pw τ e δ X = begin
      (G ∘ Cρ) ∘ (F ∘ L ∘ S ∘ B)
    ≈⟨ assoc _ _ _ ⟩
      G ∘ (Cρ ∘ (F ∘ L ∘ S ∘ B))
    ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl (≈-trans (∘-cong (assoc _ _ _) ≈-refl)
                                             (≈-trans (assoc _ _ _) (∘-cong ≈-refl (assoc _ _ _))))) ⟩
      G ∘ (Cρ ∘ (F ∘ (L ∘ (S ∘ B))))
    ≈˘⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
      G ∘ ((Cρ ∘ F) ∘ (L ∘ (S ∘ B)))
    ≈⟨ ∘-cong ≈-refl (∘-cong (apply-fwd-ren {n = 1} ρ τ δσ' (extend δ∅ X)) ≈-refl) ⟩
      G ∘ ((F'' ∘ cast (trans a₁ b₁) δ∅) ∘ (L ∘ (S ∘ B)))
    ≈⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
      G ∘ (F'' ∘ (cast (trans a₁ b₁) δ∅ ∘ (L ∘ (S ∘ B))))
    ≈˘⟨ assoc _ _ _ ⟩
      (G ∘ F'') ∘ (cast (trans a₁ b₁) δ∅ ∘ (L ∘ (S ∘ B)))
    ≈˘⟨ ∘-cong (apply-fwd-map {n = 1} τ fam (extend δ∅ X)) ≈-refl ⟩
      (F₀ ∘ K) ∘ (cast (trans a₁ b₁) δ∅ ∘ (L ∘ (S ∘ B)))
    ≈⟨ assoc _ _ _ ⟩
      F₀ ∘ (K ∘ (cast (trans a₁ b₁) δ∅ ∘ (L ∘ (S ∘ B))))
    ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl (∘-cong (cast-trans a₁ b₁ δ∅) ≈-refl)) ⟩
      F₀ ∘ (K ∘ ((cast b₁ δ∅ ∘ cast a₁ δ∅) ∘ (L ∘ (S ∘ B))))
    ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl (assoc _ _ _)) ⟩
      F₀ ∘ (K ∘ (cast b₁ δ∅ ∘ (cast a₁ δ∅ ∘ (L ∘ (S ∘ B)))))
    ≈˘⟨ ∘-cong ≈-refl (∘-cong ≈-refl (∘-cong ≈-refl (assoc _ _ _))) ⟩
      F₀ ∘ (K ∘ (cast b₁ δ∅ ∘ ((cast a₁ δ∅ ∘ L) ∘ (S ∘ B))))
    ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl (∘-cong ≈-refl (∘-cong (as-poly-map-ren (extᵗ ρ) τ Lfam δ∅) ≈-refl))) ⟩
      F₀ ∘ (K ∘ (cast b₁ δ∅ ∘ ((Lρ ∘ cast aL δ∅) ∘ (S ∘ B))))
    ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl (∘-cong ≈-refl (assoc _ _ _))) ⟩
      F₀ ∘ (K ∘ (cast b₁ δ∅ ∘ (Lρ ∘ (cast aL δ∅ ∘ (S ∘ B)))))
    ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl (∘-cong (cast-as-poly-cong {n = 0} τ (concat-ren-pw ρ δσ' (extend δ∅ X)) δ∅) ≈-refl)) ⟩
      F₀ ∘ (K ∘ (Hc ∘ (Lρ ∘ (cast aL δ∅ ∘ (S ∘ B)))))
    ≈˘⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
      F₀ ∘ ((K ∘ Hc) ∘ (Lρ ∘ (cast aL δ∅ ∘ (S ∘ B))))
    ≈˘⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
      F₀ ∘ (((K ∘ Hc) ∘ Lρ) ∘ (cast aL δ∅ ∘ (S ∘ B)))
    ≈⟨ ∘-cong ≈-refl (∘-cong (∘-cong (as-poly-map-comp τ Kfam hfam δ∅) ≈-refl) ≈-refl) ⟩
      F₀ ∘ ((as-poly-map τ (λ i → Kfam i ∘ hfam i) δ∅ ∘ Lρ) ∘ (cast aL δ∅ ∘ (S ∘ B)))
    ≈⟨ ∘-cong ≈-refl (∘-cong (as-poly-map-comp τ (λ i → Kfam i ∘ hfam i) (λ i → Lfam (extᵗ ρ i)) δ∅) ≈-refl) ⟩
      F₀ ∘ (as-poly-map τ (λ i → (Kfam i ∘ hfam i) ∘ Lfam (extᵗ ρ i)) δ∅ ∘ (cast aL δ∅ ∘ (S ∘ B)))
    ≈⟨ ∘-cong ≈-refl (∘-cong (as-poly-map-cong τ pw-step δ∅) ≈-refl) ⟩
      F₀ ∘ (as-poly-map τ (λ i → Mfam i ∘ PLfam i) δ∅ ∘ (cast aL δ∅ ∘ (S ∘ B)))
    ≈˘⟨ ∘-cong ≈-refl (∘-cong (as-poly-map-comp τ Mfam PLfam δ∅) ≈-refl) ⟩
      F₀ ∘ ((M ∘ PL) ∘ (cast aL δ∅ ∘ (S ∘ B)))
    ≈⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
      F₀ ∘ (M ∘ (PL ∘ (cast aL δ∅ ∘ (S ∘ B))))
    ≈˘⟨ ∘-cong ≈-refl (∘-cong ≈-refl (assoc _ _ _)) ⟩
      F₀ ∘ (M ∘ ((PL ∘ cast aL δ∅) ∘ (S ∘ B)))
    ≈˘⟨ ∘-cong ≈-refl (∘-cong ≈-refl (assoc _ _ _)) ⟩
      F₀ ∘ (M ∘ (((PL ∘ cast aL δ∅) ∘ S) ∘ B))
    ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl
                             (∘-cong (subst-fwd-ren-sub (extᵗ ρ) (extᵗ ρ') (sub-lift σ) (sub-lift σ') pw-lift τ e γ)
                                     ≈-refl)) ⟩
      F₀ ∘ (M ∘ (((Sρ' ∘ Cγ) ∘ Ceγ) ∘ B))
    ≈˘⟨ ∘-cong ≈-refl (∘-cong (as-poly-map-comp τ L₀fam M₂fam δ∅) ≈-refl) ⟩
      F₀ ∘ ((L₀ ∘ M₂) ∘ (((Sρ' ∘ Cγ) ∘ Ceγ) ∘ B))
    ≈⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
      F₀ ∘ (L₀ ∘ (M₂ ∘ (((Sρ' ∘ Cγ) ∘ Ceγ) ∘ B)))
    ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl (∘-cong ≈-refl (assoc _ _ _))) ⟩
      F₀ ∘ (L₀ ∘ (M₂ ∘ ((Sρ' ∘ Cγ) ∘ (Ceγ ∘ B))))
    ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl (∘-cong ≈-refl (assoc _ _ _))) ⟩
      F₀ ∘ (L₀ ∘ (M₂ ∘ (Sρ' ∘ (Cγ ∘ (Ceγ ∘ B)))))
    ≈˘⟨ ∘-cong ≈-refl (∘-cong ≈-refl (assoc _ _ _)) ⟩
      F₀ ∘ (L₀ ∘ ((M₂ ∘ Sρ') ∘ (Cγ ∘ (Ceγ ∘ B))))
    ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl (∘-cong (subst-fwd-natural (sub-lift σ) τ cfam) ≈-refl)) ⟩
      F₀ ∘ (L₀ ∘ ((S₀ ∘ Cc) ∘ (Cγ ∘ (Ceγ ∘ B))))
    ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl (assoc _ _ _)) ⟩
      F₀ ∘ (L₀ ∘ (S₀ ∘ (Cc ∘ (Cγ ∘ (Ceγ ∘ B)))))
    ≈˘⟨ ∘-cong ≈-refl (∘-cong ≈-refl (∘-cong ≈-refl (assoc _ _ _))) ⟩
      F₀ ∘ (L₀ ∘ (S₀ ∘ ((Cc ∘ Cγ) ∘ (Ceγ ∘ B))))
    ≈˘⟨ ∘-cong ≈-refl (∘-cong ≈-refl (∘-cong ≈-refl
                                             (∘-cong (∘-cong (cast-as-poly-cong {n = 0} (sub (sub-lift σ) τ)
                                                                                (concat-ren-pw ρ' δ (extend δ∅ X)) δ∅)
                                                             ≈-refl)
                                                     ≈-refl))) ⟩
      F₀ ∘ (L₀ ∘ (S₀ ∘ ((cast b₂ δ∅ ∘ Cγ) ∘ (Ceγ ∘ B))))
    ≈˘⟨ ∘-cong ≈-refl (∘-cong ≈-refl (∘-cong ≈-refl (∘-cong (cast-trans a₂ b₂ δ∅) ≈-refl))) ⟩
      F₀ ∘ (L₀ ∘ (S₀ ∘ (cast (trans a₂ b₂) δ∅ ∘ (Ceγ ∘ B))))
    ≈˘⟨ ∘-cong ≈-refl (∘-cong ≈-refl (∘-cong ≈-refl
                                             (∘-cong ≈-refl
                                                     (ty-square (λ υ → fobj μ-obj (as-poly {Δ₂'} {1} υ δ) (extend δ∅ X))
                                                                (λ υ → ⟦ υ ⟧ty γ)
                                                                (λ υ → apply-bwd {n = 1} υ δ (extend δ∅ X)) e)))) ⟩
      F₀ ∘ (L₀ ∘ (S₀ ∘ (cast (trans a₂ b₂) δ∅ ∘ (Bρ' ∘ Ce))))
    ≈˘⟨ ∘-cong ≈-refl (∘-cong ≈-refl (∘-cong ≈-refl (assoc _ _ _))) ⟩
      F₀ ∘ (L₀ ∘ (S₀ ∘ ((cast (trans a₂ b₂) δ∅ ∘ Bρ') ∘ Ce)))
    ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl (∘-cong ≈-refl (∘-cong bwd-ren ≈-refl))) ⟩
      F₀ ∘ (L₀ ∘ (S₀ ∘ ((B₀ ∘ Cρ') ∘ Ce)))
    ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl (∘-cong ≈-refl (assoc _ _ _))) ⟩
      F₀ ∘ (L₀ ∘ (S₀ ∘ (B₀ ∘ (Cρ' ∘ Ce))))
    ≈˘⟨ assoc _ _ _ ⟩
      (F₀ ∘ L₀) ∘ (S₀ ∘ (B₀ ∘ (Cρ' ∘ Ce)))
    ≈˘⟨ assoc _ _ _ ⟩
      ((F₀ ∘ L₀) ∘ S₀) ∘ (B₀ ∘ (Cρ' ∘ Ce))
    ≈˘⟨ assoc _ _ _ ⟩
      (((F₀ ∘ L₀) ∘ S₀) ∘ B₀) ∘ (Cρ' ∘ Ce)
    ≈˘⟨ assoc _ _ _ ⟩
      ((((F₀ ∘ L₀) ∘ S₀) ∘ B₀) ∘ Cρ') ∘ Ce
    ∎
    where
      open ≈-Reasoning isEquiv
      γ = concat (extend {0} δ∅ X) δ
      δσ' : Fin Δ₂ → obj
      δσ' = λ j → ⟦ σ' j ⟧ty δ
      δρ' : Fin Δ₁' → obj
      δρ' = λ k → δ (ρ' k)
      γσ' = concat (extend {0} δ∅ X) δσ'
      γ₀ = concat (extend {0} δ∅ X) δρ'
      γρ' : Fin (suc Δ₁') → obj
      γρ' = λ k → γ (extᵗ ρ' k)
      fam : ∀ i → ⟦ σ' (ρ i) ⟧ty δ ⇒ ⟦ σ i ⟧ty δρ'
      fam = λ i → ≡-to-⇒ (ty-ren ρ' (σ i) δ) ∘ ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) (pw i))
      cfam : ∀ k → γρ' k ⇒ γ₀ k
      cfam = λ k → ≡-to-⇒ (concat-ren-pw ρ' δ (extend δ∅ X) k)
      pw-lift : ∀ i → sub-lift σ' (extᵗ ρ i) ≡ extᵗ ρ' *ᵗ sub-lift σ i
      pw-lift Fin.zero    = refl
      pw-lift (Fin.suc i) =
        trans (cong (Fin.suc *ᵗ_) (pw i))
              (trans (ren-ren Fin.suc ρ' (σ i)) (sym (ren-ren (extᵗ ρ') Fin.suc (σ i))))
      a₁ = as-poly-ren {n = 0} (extᵗⁿ 1 ρ) τ γσ'
      b₁ = as-poly-cong {n = 0} τ (concat-ren-pw ρ δσ' (extend δ∅ X))
      a₂ = as-poly-ren {n = 0} (extᵗⁿ 1 ρ') (sub (sub-lift σ) τ) γ
      b₂ = as-poly-cong {n = 0} (sub (sub-lift σ) τ) (concat-ren-pw ρ' δ (extend δ∅ X))
      aL = as-poly-ren {n = 0} (extᵗ ρ) τ (λ i → ⟦ sub-lift σ' i ⟧ty γ)
      G   = as-poly-map {n = 1} τ fam (extend δ∅ X)
      Cρ  = cast (as-poly-ren {n = 1} ρ τ δσ') (extend δ∅ X)
      Cρ' = cast (as-poly-ren {n = 1} ρ' (sub (sub-lift σ) τ) δ) (extend δ∅ X)
      F   = apply-fwd {n = 1} (extᵗ ρ *ᵗ τ) δσ' (extend δ∅ X)
      F'' = apply-fwd {n = 1} τ (λ k → δσ' (ρ k)) (extend δ∅ X)
      F₀  = apply-fwd {n = 1} τ (λ i → ⟦ σ i ⟧ty δρ') (extend δ∅ X)
      Kfam = concat-mor {n = 1} {δ₀ = extend {0} δ∅ X} (λ i → id _) fam
      K  = as-poly-map τ Kfam δ∅
      Lfam = λ i → ≡-to-⇒ (sub-lift-pw σ' δ X i)
      L  = as-poly-map (extᵗ ρ *ᵗ τ) Lfam δ∅
      Lρ = as-poly-map τ (λ i → Lfam (extᵗ ρ i)) δ∅
      L₀fam = λ i → ≡-to-⇒ (sub-lift-pw σ δρ' X i)
      L₀ = as-poly-map τ L₀fam δ∅
      hfam = λ i → ≡-to-⇒ (concat-ren-pw ρ δσ' (extend δ∅ X) i)
      Hc = as-poly-map τ hfam δ∅
      M₂fam = λ i → as-poly-map (sub-lift σ i) cfam δ∅
      M₂ = as-poly-map τ M₂fam δ∅
      Mfam = λ i → L₀fam i ∘ M₂fam i
      M  = as-poly-map τ Mfam δ∅
      PLfam = λ i → ≡-to-⇒ (ty-ren (extᵗ ρ') (sub-lift σ i) γ)
                      ∘ ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty γ) (pw-lift i))
      PL = as-poly-map τ PLfam δ∅
      S   = subst-fwd (sub-lift σ') (extᵗ ρ *ᵗ τ) γ
      Sρ' = subst-fwd (sub-lift σ) τ γρ'
      S₀  = subst-fwd (sub-lift σ) τ γ₀
      B   = apply-bwd {n = 1} (sub (sub-lift σ') (extᵗ ρ *ᵗ τ)) δ (extend δ∅ X)
      Bρ' = apply-bwd {n = 1} (extᵗ ρ' *ᵗ sub (sub-lift σ) τ) δ (extend δ∅ X)
      B₀  = apply-bwd {n = 1} (sub (sub-lift σ) τ) δρ' (extend δ∅ X)
      Cγ  = ≡-to-⇒ (ty-ren (extᵗ ρ') (sub (sub-lift σ) τ) γ)
      Ceγ = ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty γ) e)
      Ce  = ≡-to-⇒ (cong (λ υ → fobj μ-obj (as-poly {Δ₂'} {1} υ δ) (extend δ∅ X)) e)
      Cc  = as-poly-map (sub (sub-lift σ) τ) cfam δ∅
      bwd-ren : (cast (trans a₂ b₂) δ∅ ∘ Bρ') ≈ (B₀ ∘ Cρ')
      bwd-ren = apply-bwd-ren {n = 1} ρ' (sub (sub-lift σ) τ) δ (extend δ∅ X)
      pw-step : ∀ i → ((Kfam i ∘ hfam i) ∘ Lfam (extᵗ ρ i)) ≈ (Mfam i ∘ PLfam i)
      pw-step Fin.zero =
        ≈-trans id-right
        (≈-trans id-left
        (≈-trans (≡-to-⇒-irr (concat-ren-pw ρ δσ' (extend δ∅ X) Fin.zero) refl)
                 (≈-sym (≈-trans (∘-cong id-left id-right)
                        (≈-trans (≡-to-⇒-comp (ty-ren (extᵗ ρ') (var Fin.zero) γ)
                                              (concat-ren-pw ρ' δ (extend δ∅ X) Fin.zero))
                                 (≡-to-⇒-irr (trans (ty-ren (extᵗ ρ') (var Fin.zero) γ)
                                                    (concat-ren-pw ρ' δ (extend δ∅ X) Fin.zero)) refl))))))
      pw-step (Fin.suc j) =
        ≈-trans (∘-cong (∘-cong ≈-refl (≡-to-⇒-irr (concat-ren-pw ρ δσ' (extend δ∅ X) (Fin.suc j)) refl)) ≈-refl)
        (≈-trans (∘-cong id-right ≈-refl)
        (≈-trans (assoc _ _ _)
        (≈-trans (∘-cong ≈-refl (≡-to-⇒-comp (ty-ren Fin.suc (σ' (ρ j)) γ) (cong (λ υ → ⟦ υ ⟧ty δ) (pw j))))
        (≈-trans (≡-to-⇒-comp (trans (ty-ren Fin.suc (σ' (ρ j)) γ) (cong (λ υ → ⟦ υ ⟧ty δ) (pw j)))
                              (ty-ren ρ' (σ j) δ))
        (≈-trans (≡-to-⇒-irr (trans (trans (ty-ren Fin.suc (σ' (ρ j)) γ) (cong (λ υ → ⟦ υ ⟧ty δ) (pw j)))
                                    (ty-ren ρ' (σ j) δ))
                             (trans q₁ q₂))
                 (≈-sym (≈-trans (∘-cong (∘-cong ≈-refl
                                                 (≈-sym (cast-as-poly-cong {n = 0} (Fin.suc *ᵗ σ j)
                                                                           (concat-ren-pw ρ' δ (extend δ∅ X)) δ∅)))
                                         ≈-refl)
                        (≈-trans (∘-cong (≡-to-⇒-comp c₂ c₁) (≡-to-⇒-comp d₂ d₁))
                                 (≡-to-⇒-comp q₁ q₂)))))))))
        where
          c₂ = cong (λ P → fobj μ-obj P δ∅)
                    (as-poly-cong {n = 0} (Fin.suc *ᵗ σ j) (concat-ren-pw ρ' δ (extend δ∅ X)))
          c₁ = sub-lift-pw σ δρ' X (Fin.suc j)
          d₂ = cong (λ υ → ⟦ υ ⟧ty γ) (pw-lift (Fin.suc j))
          d₁ = ty-ren (extᵗ ρ') (sub-lift σ (Fin.suc j)) γ
          q₂ = trans c₂ c₁
          q₁ = trans d₂ d₁

mutual
  subst-fwd-sub : ∀ {Δ₁ Δ₂ Δ₃} (σ₁ : TySub Δ₁ Δ₂) (σ₂ : TySub Δ₂ Δ₃) (τ : type Δ₁)
                  (e : sub σ₂ (sub σ₁ τ) ≡ sub (λ i → sub σ₂ (σ₁ i)) τ) (δ : Fin Δ₃ → obj) →
                  (subst-fwd σ₁ τ (λ j → ⟦ σ₂ j ⟧ty δ) ∘ subst-fwd σ₂ (sub σ₁ τ) δ)
                    ≈ (as-poly-map τ (λ i → subst-fwd σ₂ (σ₁ i) δ) δ∅
                         ∘ subst-fwd (λ i → sub σ₂ (σ₁ i)) τ δ
                         ∘ ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) e))
  subst-fwd-sub σ₁ σ₂ (var i) e δ =
    ≈-trans id-left
            (≈-sym (≈-trans (∘-cong ≈-refl (≡-to-⇒-irr (cong (λ υ → ⟦ υ ⟧ty δ) e) refl))
                            (≈-trans id-right id-right)))
  subst-fwd-sub σ₁ σ₂ unit e δ =
    ≈-trans id-left
            (≈-sym (≈-trans (∘-cong ≈-refl (≡-to-⇒-irr (cong (λ υ → ⟦ υ ⟧ty δ) e) refl))
                            (≈-trans id-right id-left)))
  subst-fwd-sub σ₁ σ₂ (base s) e δ =
    ≈-trans id-left
            (≈-sym (≈-trans (∘-cong ≈-refl (≡-to-⇒-irr (cong (λ υ → ⟦ υ ⟧ty δ) e) refl))
                            (≈-trans id-right id-left)))
  subst-fwd-sub σ₁ σ₂ (τ₁ [→] τ₂) e δ =
    ≈-trans id-left
            (≈-sym (≈-trans (∘-cong ≈-refl (≡-to-⇒-irr (cong (λ υ → ⟦ υ ⟧ty δ) e) refl))
                            (≈-trans id-right id-left)))
  subst-fwd-sub σ₁ σ₂ (τ₁ [+] τ₂) e δ = begin
      [+]-map T₁ T₂ ∘ [+]-map S₁ S₂
    ≈⟨ [+]-map-comp _ _ _ _ ⟩
      [+]-map (T₁ ∘ S₁) (T₂ ∘ S₂)
    ≈⟨ [+]-map-cong (subst-fwd-sub σ₁ σ₂ τ₁ e₁ δ) (subst-fwd-sub σ₁ σ₂ τ₂ e₂ δ) ⟩
      [+]-map ((G₁ ∘ U₁) ∘ E₁) ((G₂ ∘ U₂) ∘ E₂)
    ≈˘⟨ [+]-map-comp _ _ _ _ ⟩
      [+]-map (G₁ ∘ U₁) (G₂ ∘ U₂) ∘ [+]-map E₁ E₂
    ≈˘⟨ ∘-cong ([+]-map-comp _ _ _ _) ≈-refl ⟩
      ([+]-map G₁ G₂ ∘ [+]-map U₁ U₂) ∘ [+]-map E₁ E₂
    ≈˘⟨ ∘-cong ≈-refl (ty-cast-+ e₁ e₂ δ) ⟩
      ([+]-map G₁ G₂ ∘ [+]-map U₁ U₂) ∘ ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) (cong₂ _[+]_ e₁ e₂))
    ≈⟨ ∘-cong ≈-refl (≡-to-⇒-irr (cong (λ υ → ⟦ υ ⟧ty δ) (cong₂ _[+]_ e₁ e₂)) (cong (λ υ → ⟦ υ ⟧ty δ) e)) ⟩
      ([+]-map G₁ G₂ ∘ [+]-map U₁ U₂) ∘ ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) e)
    ∎
    where
      open ≈-Reasoning isEquiv
      δ₂ : Fin _ → obj
      δ₂ = λ j → ⟦ σ₂ j ⟧ty δ
      e₁ = sub-sub σ₂ σ₁ τ₁
      e₂ = sub-sub σ₂ σ₁ τ₂
      T₁ = subst-fwd σ₁ τ₁ δ₂
      T₂ = subst-fwd σ₁ τ₂ δ₂
      S₁ = subst-fwd σ₂ (sub σ₁ τ₁) δ
      S₂ = subst-fwd σ₂ (sub σ₁ τ₂) δ
      G₁ = as-poly-map τ₁ (λ i → subst-fwd σ₂ (σ₁ i) δ) δ∅
      G₂ = as-poly-map τ₂ (λ i → subst-fwd σ₂ (σ₁ i) δ) δ∅
      U₁ = subst-fwd (λ i → sub σ₂ (σ₁ i)) τ₁ δ
      U₂ = subst-fwd (λ i → sub σ₂ (σ₁ i)) τ₂ δ
      E₁ = ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) e₁)
      E₂ = ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) e₂)
  subst-fwd-sub σ₁ σ₂ (τ₁ [×] τ₂) e δ = begin
      [×]-map T₁ T₂ ∘ [×]-map S₁ S₂
    ≈⟨ [×]-map-comp _ _ _ _ ⟩
      [×]-map (T₁ ∘ S₁) (T₂ ∘ S₂)
    ≈⟨ [×]-map-cong (subst-fwd-sub σ₁ σ₂ τ₁ e₁ δ) (subst-fwd-sub σ₁ σ₂ τ₂ e₂ δ) ⟩
      [×]-map ((G₁ ∘ U₁) ∘ E₁) ((G₂ ∘ U₂) ∘ E₂)
    ≈˘⟨ [×]-map-comp _ _ _ _ ⟩
      [×]-map (G₁ ∘ U₁) (G₂ ∘ U₂) ∘ [×]-map E₁ E₂
    ≈˘⟨ ∘-cong ([×]-map-comp _ _ _ _) ≈-refl ⟩
      ([×]-map G₁ G₂ ∘ [×]-map U₁ U₂) ∘ [×]-map E₁ E₂
    ≈˘⟨ ∘-cong ≈-refl (ty-cast-× e₁ e₂ δ) ⟩
      ([×]-map G₁ G₂ ∘ [×]-map U₁ U₂) ∘ ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) (cong₂ _[×]_ e₁ e₂))
    ≈⟨ ∘-cong ≈-refl (≡-to-⇒-irr (cong (λ υ → ⟦ υ ⟧ty δ) (cong₂ _[×]_ e₁ e₂)) (cong (λ υ → ⟦ υ ⟧ty δ) e)) ⟩
      ([×]-map G₁ G₂ ∘ [×]-map U₁ U₂) ∘ ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) e)
    ∎
    where
      open ≈-Reasoning isEquiv
      δ₂ : Fin _ → obj
      δ₂ = λ j → ⟦ σ₂ j ⟧ty δ
      e₁ = sub-sub σ₂ σ₁ τ₁
      e₂ = sub-sub σ₂ σ₁ τ₂
      T₁ = subst-fwd σ₁ τ₁ δ₂
      T₂ = subst-fwd σ₁ τ₂ δ₂
      S₁ = subst-fwd σ₂ (sub σ₁ τ₁) δ
      S₂ = subst-fwd σ₂ (sub σ₁ τ₂) δ
      G₁ = as-poly-map τ₁ (λ i → subst-fwd σ₂ (σ₁ i) δ) δ∅
      G₂ = as-poly-map τ₂ (λ i → subst-fwd σ₂ (σ₁ i) δ) δ∅
      U₁ = subst-fwd (λ i → sub σ₂ (σ₁ i)) τ₁ δ
      U₂ = subst-fwd (λ i → sub σ₂ (σ₁ i)) τ₂ δ
      E₁ = ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) e₁)
      E₂ = ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) e₂)
  subst-fwd-sub {Δ₁} {Δ₂} {Δ₃} σ₁ σ₂ (μ τ) e δ = begin
      μ-map A₁ δ∅ A' δ∅ b₁ ∘ μ-map P δ∅ A₁ δ∅ b₂
    ≈⟨ μ-map-comp P δ∅ A₁ δ∅ A' δ∅ b₂ b₁ b₂' (subst-fwd-body-carrier σ₂ (sub (sub-lift σ₁) τ) δ k₁) ⟩
      μ-map P δ∅ A' δ∅ (b₁ ∘ b₂')
    ≈⟨ μ-map-cong _ _ _ _ (subst-fwd-sub-body σ₁ σ₂ τ e° δ M') ⟩
      μ-map P δ∅ A' δ∅ ((G ∘ u) ∘ Ce M')
    ≈⟨ μ-map-cong _ _ _ _ (assoc _ _ _) ⟩
      μ-map P δ∅ A' δ∅ (G ∘ (u ∘ Ce M'))
    ≈˘⟨ μ-map-comp P δ∅ A₁₂ δ∅ A' δ∅ (uA ∘ Ce MA₁₂) G (u ∘ Ce M') sq₄ ⟩
      μ-map A₁₂ δ∅ A' δ∅ G ∘ μ-map P δ∅ A₁₂ δ∅ (uA ∘ Ce MA₁₂)
    ≈˘⟨ ∘-cong ≈-refl (μ-map-comp P δ∅ Q δ∅ A₁₂ δ∅ (Ce MQ) uA (Ce MA₁₂) sq₃) ⟩
      μ-map A₁₂ δ∅ A' δ∅ G ∘ (μ-map Q δ∅ A₁₂ δ∅ uA ∘ μ-map P δ∅ Q δ∅ (Ce MQ))
    ≈˘⟨ assoc _ _ _ ⟩
      (μ-map A₁₂ δ∅ A' δ∅ G ∘ μ-map Q δ∅ A₁₂ δ∅ uA) ∘ μ-map P δ∅ Q δ∅ (Ce MQ)
    ≈˘⟨ ∘-cong ≈-refl (ty-cast-μ e° δ) ⟩
      (μ-map A₁₂ δ∅ A' δ∅ G ∘ μ-map Q δ∅ A₁₂ δ∅ uA) ∘ ≡-to-⇒ (cong (λ υ → ⟦ μ υ ⟧ty δ) e°)
    ≈⟨ ∘-cong ≈-refl (≡-to-⇒-irr (cong (λ υ → ⟦ μ υ ⟧ty δ) e°) (cong (λ υ → ⟦ υ ⟧ty δ) e)) ⟩
      (μ-map A₁₂ δ∅ A' δ∅ G ∘ μ-map Q δ∅ A₁₂ δ∅ uA) ∘ ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty δ) e)
    ∎
    where
      open ≈-Reasoning isEquiv
      σ₁₂ : TySub Δ₁ Δ₃
      σ₁₂ = λ i → sub σ₂ (σ₁ i)
      δ₂ : Fin Δ₂ → obj
      δ₂ = λ j → ⟦ σ₂ j ⟧ty δ
      gs : ∀ i → ⟦ σ₁₂ i ⟧ty δ ⇒ ⟦ σ₁ i ⟧ty δ₂
      gs = λ i → subst-fwd σ₂ (σ₁ i) δ
      pw-lift : ∀ i → sub (sub-lift σ₂) (sub-lift σ₁ i) ≡ sub-lift σ₁₂ i
      pw-lift Fin.zero    = refl
      pw-lift (Fin.suc i) = trans (sub-ren (sub-lift σ₂) Fin.suc (σ₁ i)) (sym (ren-sub Fin.suc σ₂ (σ₁ i)))
      e° : sub (sub-lift σ₂) (sub (sub-lift σ₁) τ) ≡ sub (sub-lift σ₁₂) τ
      e° = trans (sub-sub (sub-lift σ₂) (sub-lift σ₁) τ) (sub-cong τ pw-lift)
      P   = as-poly {Δ₃} {1} (sub (sub-lift σ₂) (sub (sub-lift σ₁) τ)) δ
      A₁  = as-poly {Δ₂} {1} (sub (sub-lift σ₁) τ) δ₂
      A'  = as-poly {Δ₁} {1} τ (λ i → ⟦ σ₁ i ⟧ty δ₂)
      A₁₂ = as-poly {Δ₁} {1} τ (λ i → ⟦ σ₁₂ i ⟧ty δ)
      Q   = as-poly {Δ₃} {1} (sub (sub-lift σ₁₂) τ) δ
      M'   = μ-obj A' δ∅
      MA₁₂ = μ-obj A₁₂ δ∅
      MQ   = μ-obj Q δ∅
      G   = as-poly-map {n = 1} τ gs (extend δ∅ M')
      b₂  = subst-fwd-body σ₂ (sub (sub-lift σ₁) τ) δ (μ-obj A₁ δ∅)
      b₂' = subst-fwd-body σ₂ (sub (sub-lift σ₁) τ) δ M'
      b₁  = subst-fwd-body σ₁ τ δ₂ M'
      u   = subst-fwd-body σ₁₂ τ δ M'
      uA  = subst-fwd-body σ₁₂ τ δ MA₁₂
      Ce : (Y : obj) → fobj μ-obj P (extend δ∅ Y) ⇒ fobj μ-obj Q (extend δ∅ Y)
      Ce Y = ≡-to-⇒ (cong (λ υ → fobj μ-obj (as-poly {Δ₃} {1} υ δ) (extend δ∅ Y)) e°)
      k₁ = μ-map A₁ δ∅ A' δ∅ b₁
      k₃ = μ-map Q δ∅ A₁₂ δ∅ uA
      k₄ = μ-map A₁₂ δ∅ A' δ∅ G
      sq₃ : (fmor Q (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k₃) ∘ Ce MQ)
              ≈ (Ce MA₁₂ ∘ fmor P (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k₃))
      sq₃ = ty-square (λ υ → fobj μ-obj (as-poly {Δ₃} {1} υ δ) (extend δ∅ MQ))
                      (λ υ → fobj μ-obj (as-poly {Δ₃} {1} υ δ) (extend δ∅ MA₁₂))
                      (λ υ → fmor (as-poly {Δ₃} {1} υ δ)
                                  (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k₃)) e°
      sq₄ : (fmor A₁₂ (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k₄) ∘ (uA ∘ Ce MA₁₂))
              ≈ ((u ∘ Ce M') ∘ fmor P (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k₄))
      sq₄ = ≈-trans (≈-sym (assoc _ _ _))
            (≈-trans (∘-cong (subst-fwd-body-carrier σ₁₂ τ δ k₄) ≈-refl)
            (≈-trans (assoc _ _ _)
            (≈-trans (∘-cong ≈-refl
                             (ty-square (λ υ → fobj μ-obj (as-poly {Δ₃} {1} υ δ) (extend δ∅ MA₁₂))
                                        (λ υ → fobj μ-obj (as-poly {Δ₃} {1} υ δ) (extend δ∅ M'))
                                        (λ υ → fmor (as-poly {Δ₃} {1} υ δ)
                                                    (extend-mor {δ = δ∅} {δ' = δ∅} (λ i → id _) k₄)) e°))
                     (≈-sym (assoc _ _ _)))))

  subst-fwd-sub-body : ∀ {Δ₁ Δ₂ Δ₃} (σ₁ : TySub Δ₁ Δ₂) (σ₂ : TySub Δ₂ Δ₃) (τ : type (suc Δ₁))
                       (e : sub (sub-lift σ₂) (sub (sub-lift σ₁) τ) ≡ sub (sub-lift (λ i → sub σ₂ (σ₁ i))) τ)
                       (δ : Fin Δ₃ → obj) (X : obj) →
                       (subst-fwd-body σ₁ τ (λ j → ⟦ σ₂ j ⟧ty δ) X ∘ subst-fwd-body σ₂ (sub (sub-lift σ₁) τ) δ X)
                         ≈ (as-poly-map {n = 1} τ (λ i → subst-fwd σ₂ (σ₁ i) δ) (extend δ∅ X)
                              ∘ subst-fwd-body (λ i → sub σ₂ (σ₁ i)) τ δ X
                              ∘ ≡-to-⇒ (cong (λ υ → fobj μ-obj (as-poly {Δ₃} {1} υ δ) (extend δ∅ X)) e))
  subst-fwd-sub-body {Δ₁} {Δ₂} {Δ₃} σ₁ σ₂ τ e δ X = begin
      (((F₁ ∘ L₁) ∘ S₁) ∘ B₁) ∘ (((F₂ ∘ L₂) ∘ S₂) ∘ B₂)
    ≈⟨ ≈-trans (assoc _ _ _) (≈-trans (assoc _ _ _) (assoc _ _ _)) ⟩
      F₁ ∘ (L₁ ∘ (S₁ ∘ (B₁ ∘ (((F₂ ∘ L₂) ∘ S₂) ∘ B₂))))
    ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl (∘-cong ≈-refl (∘-cong ≈-refl (≈-trans (assoc _ _ _) (assoc _ _ _))))) ⟩
      F₁ ∘ (L₁ ∘ (S₁ ∘ (B₁ ∘ (F₂ ∘ (L₂ ∘ (S₂ ∘ B₂))))))
    ≈˘⟨ ∘-cong ≈-refl (∘-cong ≈-refl (∘-cong ≈-refl (assoc _ _ _))) ⟩
      F₁ ∘ (L₁ ∘ (S₁ ∘ ((B₁ ∘ F₂) ∘ (L₂ ∘ (S₂ ∘ B₂)))))
    ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl (∘-cong ≈-refl
                                             (∘-cong (apply-bwd-fwd {n = 1} (sub (sub-lift σ₁) τ) δ₂ (extend δ∅ X)) ≈-refl))) ⟩
      F₁ ∘ (L₁ ∘ (S₁ ∘ (id _ ∘ (L₂ ∘ (S₂ ∘ B₂)))))
    ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl (∘-cong ≈-refl id-left)) ⟩
      F₁ ∘ (L₁ ∘ (S₁ ∘ (L₂ ∘ (S₂ ∘ B₂))))
    ≈˘⟨ ∘-cong ≈-refl (∘-cong ≈-refl (assoc _ _ _)) ⟩
      F₁ ∘ (L₁ ∘ ((S₁ ∘ L₂) ∘ (S₂ ∘ B₂)))
    ≈˘⟨ ∘-cong ≈-refl (∘-cong ≈-refl (∘-cong (subst-fwd-natural (sub-lift σ₁) τ L₂fam) ≈-refl)) ⟩
      F₁ ∘ (L₁ ∘ ((N ∘ S₁') ∘ (S₂ ∘ B₂)))
    ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl (assoc _ _ _)) ⟩
      F₁ ∘ (L₁ ∘ (N ∘ (S₁' ∘ (S₂ ∘ B₂))))
    ≈˘⟨ ∘-cong ≈-refl (∘-cong ≈-refl (∘-cong ≈-refl (assoc _ _ _))) ⟩
      F₁ ∘ (L₁ ∘ (N ∘ ((S₁' ∘ S₂) ∘ B₂)))
    ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl (∘-cong ≈-refl
                                             (∘-cong (subst-fwd-sub (sub-lift σ₁) (sub-lift σ₂) τ e' γ) ≈-refl))) ⟩
      F₁ ∘ (L₁ ∘ (N ∘ (((W ∘ S₁₂') ∘ Ce') ∘ B₂)))
    ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl (∘-cong ≈-refl (≈-trans (assoc _ _ _) (assoc _ _ _)))) ⟩
      F₁ ∘ (L₁ ∘ (N ∘ (W ∘ (S₁₂' ∘ (Ce' ∘ B₂)))))
    ≈˘⟨ ∘-cong ≈-refl (≈-trans (assoc _ _ _) (assoc _ _ _)) ⟩
      F₁ ∘ (((L₁ ∘ N) ∘ W) ∘ (S₁₂' ∘ (Ce' ∘ B₂)))
    ≈⟨ ∘-cong ≈-refl (∘-cong (∘-cong (as-poly-map-comp τ L₁fam Nfam δ∅) ≈-refl) ≈-refl) ⟩
      F₁ ∘ ((as-poly-map τ (λ i → L₁fam i ∘ Nfam i) δ∅ ∘ W) ∘ (S₁₂' ∘ (Ce' ∘ B₂)))
    ≈⟨ ∘-cong ≈-refl (∘-cong (as-poly-map-comp τ (λ i → L₁fam i ∘ Nfam i) Wfam δ∅) ≈-refl) ⟩
      F₁ ∘ (as-poly-map τ (λ i → (L₁fam i ∘ Nfam i) ∘ Wfam i) δ∅ ∘ (S₁₂' ∘ (Ce' ∘ B₂)))
    ≈⟨ ∘-cong ≈-refl (∘-cong (as-poly-map-cong τ pw-step δ∅) ≈-refl) ⟩
      F₁ ∘ (as-poly-map τ (λ i → (Kgfam i ∘ L₁₂fam i) ∘ Pcfam i) δ∅ ∘ (S₁₂' ∘ (Ce' ∘ B₂)))
    ≈˘⟨ ∘-cong ≈-refl (∘-cong (as-poly-map-comp τ (λ i → Kgfam i ∘ L₁₂fam i) Pcfam δ∅) ≈-refl) ⟩
      F₁ ∘ ((as-poly-map τ (λ i → Kgfam i ∘ L₁₂fam i) δ∅ ∘ Pc) ∘ (S₁₂' ∘ (Ce' ∘ B₂)))
    ≈˘⟨ ∘-cong ≈-refl (∘-cong (∘-cong (as-poly-map-comp τ Kgfam L₁₂fam δ∅) ≈-refl) ≈-refl) ⟩
      F₁ ∘ (((Kg ∘ L₁₂) ∘ Pc) ∘ (S₁₂' ∘ (Ce' ∘ B₂)))
    ≈⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
      F₁ ∘ ((Kg ∘ L₁₂) ∘ (Pc ∘ (S₁₂' ∘ (Ce' ∘ B₂))))
    ≈˘⟨ ∘-cong ≈-refl (∘-cong ≈-refl (assoc _ _ _)) ⟩
      F₁ ∘ ((Kg ∘ L₁₂) ∘ ((Pc ∘ S₁₂') ∘ (Ce' ∘ B₂)))
    ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl (∘-cong (subst-fwd-cong τ pw-lift e'' γ) ≈-refl)) ⟩
      F₁ ∘ ((Kg ∘ L₁₂) ∘ ((S₁₂ ∘ Ce'') ∘ (Ce' ∘ B₂)))
    ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl (assoc _ _ _)) ⟩
      F₁ ∘ ((Kg ∘ L₁₂) ∘ (S₁₂ ∘ (Ce'' ∘ (Ce' ∘ B₂))))
    ≈˘⟨ ∘-cong ≈-refl (∘-cong ≈-refl (∘-cong ≈-refl (assoc _ _ _))) ⟩
      F₁ ∘ ((Kg ∘ L₁₂) ∘ (S₁₂ ∘ ((Ce'' ∘ Ce') ∘ B₂)))
    ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl (∘-cong ≈-refl
                                             (∘-cong (≡-to-⇒-comp (cong (λ υ → ⟦ υ ⟧ty γ) e') (cong (λ υ → ⟦ υ ⟧ty γ) e''))
                                                     ≈-refl))) ⟩
      F₁ ∘ ((Kg ∘ L₁₂) ∘ (S₁₂ ∘ (≡-to-⇒ (trans (cong (λ υ → ⟦ υ ⟧ty γ) e') (cong (λ υ → ⟦ υ ⟧ty γ) e'')) ∘ B₂)))
    ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl (∘-cong ≈-refl
                                             (∘-cong (≡-to-⇒-irr (trans (cong (λ υ → ⟦ υ ⟧ty γ) e') (cong (λ υ → ⟦ υ ⟧ty γ) e''))
                                                                 (cong (λ υ → ⟦ υ ⟧ty γ) e))
                                                     ≈-refl))) ⟩
      F₁ ∘ ((Kg ∘ L₁₂) ∘ (S₁₂ ∘ (Ceγ ∘ B₂)))
    ≈˘⟨ ∘-cong ≈-refl (∘-cong ≈-refl (∘-cong ≈-refl
                                             (ty-square (λ υ → fobj μ-obj (as-poly {Δ₃} {1} υ δ) (extend δ∅ X))
                                                        (λ υ → ⟦ υ ⟧ty γ)
                                                        (λ υ → apply-bwd {n = 1} υ δ (extend δ∅ X)) e))) ⟩
      F₁ ∘ ((Kg ∘ L₁₂) ∘ (S₁₂ ∘ (B₁₂ ∘ Ce)))
    ≈˘⟨ assoc _ _ _ ⟩
      (F₁ ∘ (Kg ∘ L₁₂)) ∘ (S₁₂ ∘ (B₁₂ ∘ Ce))
    ≈˘⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
      ((F₁ ∘ Kg) ∘ L₁₂) ∘ (S₁₂ ∘ (B₁₂ ∘ Ce))
    ≈⟨ ∘-cong (∘-cong (apply-fwd-map {n = 1} τ gs (extend δ∅ X)) ≈-refl) ≈-refl ⟩
      ((G ∘ F₁₂) ∘ L₁₂) ∘ (S₁₂ ∘ (B₁₂ ∘ Ce))
    ≈⟨ ≈-trans (assoc _ _ _) (assoc _ _ _) ⟩
      G ∘ (F₁₂ ∘ (L₁₂ ∘ (S₁₂ ∘ (B₁₂ ∘ Ce))))
    ≈˘⟨ ∘-cong ≈-refl (≈-trans (assoc _ _ _) (≈-trans (assoc _ _ _) (assoc _ _ _))) ⟩
      G ∘ ((((F₁₂ ∘ L₁₂) ∘ S₁₂) ∘ B₁₂) ∘ Ce)
    ≈˘⟨ assoc _ _ _ ⟩
      (G ∘ (((F₁₂ ∘ L₁₂) ∘ S₁₂) ∘ B₁₂)) ∘ Ce
    ∎
    where
      open ≈-Reasoning isEquiv
      γ = concat (extend {0} δ∅ X) δ
      σ₁₂ : TySub Δ₁ Δ₃
      σ₁₂ = λ i → sub σ₂ (σ₁ i)
      σ₁₂' : TySub (suc Δ₁) (suc Δ₃)
      σ₁₂' = λ i → sub (sub-lift σ₂) (sub-lift σ₁ i)
      δ₂ : Fin Δ₂ → obj
      δ₂ = λ j → ⟦ σ₂ j ⟧ty δ
      γ₂ = concat (extend {0} δ∅ X) δ₂
      γσ₂ : Fin (suc Δ₂) → obj
      γσ₂ = λ i → ⟦ sub-lift σ₂ i ⟧ty γ
      δ₁ : Fin Δ₁ → obj
      δ₁ = λ i → ⟦ σ₁ i ⟧ty δ₂
      δ₁₂ : Fin Δ₁ → obj
      δ₁₂ = λ i → ⟦ σ₁₂ i ⟧ty δ
      gs : ∀ i → δ₁₂ i ⇒ δ₁ i
      gs = λ i → subst-fwd σ₂ (σ₁ i) δ
      pw-lift : ∀ i → σ₁₂' i ≡ sub-lift σ₁₂ i
      pw-lift Fin.zero    = refl
      pw-lift (Fin.suc i) = trans (sub-ren (sub-lift σ₂) Fin.suc (σ₁ i)) (sym (ren-sub Fin.suc σ₂ (σ₁ i)))
      e'  = sub-sub (sub-lift σ₂) (sub-lift σ₁) τ
      e'' = sub-cong τ pw-lift
      F₁  = apply-fwd {n = 1} τ δ₁ (extend δ∅ X)
      F₂  = apply-fwd {n = 1} (sub (sub-lift σ₁) τ) δ₂ (extend δ∅ X)
      F₁₂ = apply-fwd {n = 1} τ δ₁₂ (extend δ∅ X)
      L₁fam = λ i → ≡-to-⇒ (sub-lift-pw σ₁ δ₂ X i)
      L₁ = as-poly-map τ L₁fam δ∅
      L₂fam : ∀ i → γσ₂ i ⇒ γ₂ i
      L₂fam = λ i → ≡-to-⇒ (sub-lift-pw σ₂ δ X i)
      L₂ = as-poly-map (sub (sub-lift σ₁) τ) L₂fam δ∅
      L₁₂fam = λ i → ≡-to-⇒ (sub-lift-pw σ₁₂ δ X i)
      L₁₂ = as-poly-map τ L₁₂fam δ∅
      S₁   = subst-fwd (sub-lift σ₁) τ γ₂
      S₁'  = subst-fwd (sub-lift σ₁) τ γσ₂
      S₂   = subst-fwd (sub-lift σ₂) (sub (sub-lift σ₁) τ) γ
      S₁₂  = subst-fwd (sub-lift σ₁₂) τ γ
      S₁₂' = subst-fwd σ₁₂' τ γ
      B₁  = apply-bwd {n = 1} (sub (sub-lift σ₁) τ) δ₂ (extend δ∅ X)
      B₂  = apply-bwd {n = 1} (sub (sub-lift σ₂) (sub (sub-lift σ₁) τ)) δ (extend δ∅ X)
      B₁₂ = apply-bwd {n = 1} (sub (sub-lift σ₁₂) τ) δ (extend δ∅ X)
      G   = as-poly-map {n = 1} τ gs (extend δ∅ X)
      Nfam = λ i → as-poly-map (sub-lift σ₁ i) L₂fam δ∅
      N  = as-poly-map τ Nfam δ∅
      Wfam = λ i → subst-fwd (sub-lift σ₂) (sub-lift σ₁ i) γ
      W  = as-poly-map τ Wfam δ∅
      Kgfam = concat-mor {n = 1} {δ₀ = extend {0} δ∅ X} (λ i → id _) gs
      Kg = as-poly-map τ Kgfam δ∅
      Pcfam = λ i → ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty γ) (pw-lift i))
      Pc = as-poly-map τ Pcfam δ∅
      Ce   = ≡-to-⇒ (cong (λ υ → fobj μ-obj (as-poly {Δ₃} {1} υ δ) (extend δ∅ X)) e)
      Ce'  = ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty γ) e')
      Ce'' = ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty γ) e'')
      Ceγ  = ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty γ) e)
      pw-step : ∀ i → ((L₁fam i ∘ Nfam i) ∘ Wfam i) ≈ ((Kgfam i ∘ L₁₂fam i) ∘ Pcfam i)
      pw-step Fin.zero    = ≈-refl
      pw-step (Fin.suc j) =
        ≈-trans (∘-cong (as-poly-map-ren Fin.suc (σ₁ j) L₂fam δ∅) ≈-refl)
        (≈-trans (∘-cong (∘-cong (as-poly-map-cong (σ₁ j) (λ i → ≈-sym id-right) δ∅) ≈-refl) ≈-refl)
                 (subst-fwd-ren-sub Fin.suc Fin.suc σ₂ (sub-lift σ₂) (λ _ → refl) (σ₁ j) (pw-lift (Fin.suc j)) γ))
