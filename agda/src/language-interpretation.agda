{-# OPTIONS --prop --postfix-projections --safe #-}

-- The interpretation of the language in a category of families: every value former is
-- lifted. Sums are coproducts of lifted summands, products are lifted products, μ-types the
-- carriers, and function spaces are lifted weak exponentials, so a closure carries a root like any
-- other cell. Constructors inject their payload under the injection, whose root is zero: a cell
-- the program itself constructs depends on nothing. Eliminators, including application, send the
-- scrutinee's root to the result type's unit constant scaled by the elimination weight; the unit
-- constant is built by the same induction as the interpretation, from assumed constants at the
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
         HasWeakExponentials; strong-coproducts→coproducts)
open import cmon-enriched using (CMonEnriched; Biproduct)
open import signature using (Signature; Model; PointedFPCat; PFPC[_,_,_,_])
open import polynomial-functor using (Poly)
open import prop-setoid using (module ≈-Reasoning)
import fam-mu-lifting.mu-map
import language-syntax

module language-interpretation
  {ℓ} (Sig : Signature ℓ)
  {o m e} (os es : Level) {𝒞 : Category o m e}
  (T : HasTerminal 𝒞) (CM : CMonEnriched 𝒞) (BP : ∀ x y → Biproduct CM x y)
  (𝟙c : Category.obj 𝒞)
  (let module R = fam-mu-lifting.mu-map os es T CM BP 𝟙c)
  (𝒞E : HasWeakExponentials R.cat R.products)
  (δ∅ : Fin 0 → R.Obj)
  (𝟙ty : R.Obj)
  (unit-pt : R.Mor (HasTerminal.witness (R.terminal T)) 𝟙ty)
  (let Bool = HasCoproducts.coprod R.coproducts (R.Lf 𝟙ty) (R.Lf 𝟙ty))
  (Int : Model PFPC[ R.cat , R.terminal T , R.products , Bool ] Sig)
  (elim-w : Category._⇒_ 𝒞 𝟙c 𝟙c)
  (exp-const : ∀ {X Y : R.Obj} → R.Constant Y → R.Constant (HasWeakExponentials.exp 𝒞E X Y))
  (𝟙ty-const : R.Constant 𝟙ty)
  (sort-const : ∀ s → R.Constant (Model.⟦sort⟧ Int s))
  where

open R using (Obj; Lf; Lf-map; Lf-map-cong; Lf-map-id; Lf-map-comp; injF; extend; extend-mor; fobj; HasMu; hasMu; fmor; μ-map;
              Constant; elimF; scale-const; Lf-constant; coprod-constant; prod-constant; PolyConst;
              fmor-cong; fmor-id; fmor-comp; fmor-const; fmor-var; fmor-+; fmor-×; fmor-μ;
              μ-map-cong; μ-map-id; μ-map-in; μ-map-comp)
open Category R.cat
open HasTerminal (R.terminal T) renaming (witness to 𝟙)
open HasProducts R.products renaming (pair to ⟨_,_⟩)

open HasCoproducts R.coproducts using (coprod; coprod-m; coprod-m-cong; coprod-m-comp; coprod-m-id; in₁; in₂;
                                       copair-cong; copair-ext)
open HasStrongCoproducts R.strongCoproducts using () renaming (copair to scopair)
open HasWeakExponentials 𝒞E using (lambda; eval) renaming (exp to _⟦→⟧_)
open language-syntax Sig
open HasMu hasMu
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

-- The unit constant of each type's interpretation, by the same induction as the interpretation:
-- unit weight at every root, the assumed constants at the leaves, and a recursion over trees at
-- the μ-carriers.
private module Mu∅ = R.MuUnit δ∅ (λ ())

mutual
  ty-unit : ∀ {Δ} (τ : type Δ) (δ : Fin Δ → obj) → (∀ i → Constant (δ i)) → Constant (⟦ τ ⟧ty δ)
  ty-unit (var i)   δ δc = δc i
  ty-unit unit      δ δc = 𝟙ty-const
  ty-unit (base s)  δ δc = sort-const s
  ty-unit (σ [+] τ) δ δc =
    coprod-constant (Lf-constant (ty-unit σ δ δc)) (Lf-constant (ty-unit τ δ δc))
  ty-unit (σ [×] τ) δ δc = Lf-constant (prod-constant (ty-unit σ δ δc) (ty-unit τ δ δc))
  ty-unit (σ [→] τ) δ δc = Lf-constant (exp-const (ty-unit τ (λ ()) (λ ())))
  ty-unit (μ τ)     δ δc = Mu∅.μ-unit (as-poly τ δ) (as-poly-const τ δ δc)

  as-poly-const : ∀ {Δ n} (τ : type (n + Δ)) (δ : Fin Δ → obj) → (∀ i → Constant (δ i)) →
                  PolyConst (as-poly {Δ} {n} τ δ)
  as-poly-const {Δ} {n} (var i) δ δc = go (splitAt n i)
    where
      go : (s : Fin n ⊎ Fin Δ) →
           PolyConst ([_,_] {C = λ _ → Poly R.cat n} Poly.var (λ j → Poly.const (δ j)) s)
      go (inj₁ k) = lift tt
      go (inj₂ j) = δc j
  as-poly-const unit      δ δc = 𝟙ty-const
  as-poly-const (base s)  δ δc = sort-const s
  as-poly-const (σ [+] τ) δ δc = DP._,_ (as-poly-const σ δ δc) (as-poly-const τ δ δc)
  as-poly-const (σ [×] τ) δ δc = DP._,_ (as-poly-const σ δ δc) (as-poly-const τ δ δc)
  as-poly-const (σ [→] τ) δ δc = Lf-constant (exp-const (ty-unit τ (λ ()) (λ ())))
  as-poly-const (μ τ)     δ δc = as-poly-const τ δ δc

-- The constant an eliminator writes: the result type's unit constant scaled by the elimination
-- weight.
elim-const : ∀ (τ : type 0) → Constant (⟦ τ ⟧ty (λ ()))
elim-const τ = scale-const elim-w (ty-unit τ (λ ()) (λ ()))

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

as-poly-map : ∀ {Δ n} (τ : type (n + Δ)) {δ δ' : Fin Δ → obj} → (∀ i → δ i ⇒ δ' i) → (δ₀ : Fin n → obj) →
              fobj μ-obj (as-poly {Δ} {n} τ δ) δ₀ ⇒ fobj μ-obj (as-poly {Δ} {n} τ δ') δ₀
as-poly-map {Δ} {n} (var i) {δ} {δ'} gs δ₀ = go (splitAt n i)
  where
    go : (s : Fin n ⊎ Fin Δ) →
         fobj μ-obj ([ Poly.var , (λ j → Poly.const (δ j)) ] s) δ₀ ⇒ fobj μ-obj ([ Poly.var , (λ j → Poly.const (δ' j)) ] s) δ₀
    go (inj₁ j) = id _
    go (inj₂ k) = gs k
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

-- Freezing the poly-variables δ₀ into the environment (with X at position 0) reshuffles the
-- combined context only up to pointwise equality.
env-pw : ∀ {Δ n} (δ : Fin Δ → obj) (δ₀ : Fin n → obj) (X : obj) (i : Fin (suc (n + Δ))) →
         concat (extend {0} δ∅ X) (concat δ₀ δ) i ≡ concat (extend δ₀ X) δ i
env-pw δ δ₀ X Fin.zero    = refl
env-pw {n = n} δ δ₀ X (Fin.suc j) with splitAt n j
... | inj₁ k = refl
... | inj₂ l = refl

-- Applying the polynomial (as-poly τ δ) is the interpretation of τ, in each direction. Morphisms
-- suffice for the term semantics; the inverse laws are deferred.
mutual
  apply-fwd : ∀ {Δ n} (τ : type (n + Δ)) (δ : Fin Δ → obj) (δ₀ : Fin n → obj) →
              ⟦ τ ⟧ty (concat δ₀ δ) ⇒ fobj μ-obj (as-poly {Δ} {n} τ δ) δ₀
  apply-fwd {n = n} (var i) δ δ₀ with splitAt n i
  ... | inj₁ j = id _
  ... | inj₂ k = id _
  apply-fwd unit      δ δ₀ = id _
  apply-fwd (base s)  δ δ₀ = id _
  apply-fwd (σ [+] τ) δ δ₀ = coprod-m (Lf-map (apply-fwd σ δ δ₀)) (Lf-map (apply-fwd τ δ δ₀))
  apply-fwd (σ [×] τ) δ δ₀ = Lf-map (prod-m (apply-fwd σ δ δ₀) (apply-fwd τ δ δ₀))
  apply-fwd (σ [→] τ) δ δ₀ = id _
  apply-fwd {Δ} {n} (μ τ) δ δ₀ =
    μ-map (as-poly {n + Δ} {1} τ (concat δ₀ δ)) δ∅ (as-poly {Δ} {suc n} τ δ) δ₀
      (apply-fwd τ δ (extend δ₀ M) ∘ ≡-to-⇒ (ty-cong τ (env-pw δ δ₀ M)) ∘ apply-bwd {n = 1} τ (concat δ₀ δ) (extend δ∅ M))
    where M = μ-obj (as-poly {Δ} {suc n} τ δ) δ₀

  apply-bwd : ∀ {Δ n} (τ : type (n + Δ)) (δ : Fin Δ → obj) (δ₀ : Fin n → obj) →
              fobj μ-obj (as-poly {Δ} {n} τ δ) δ₀ ⇒ ⟦ τ ⟧ty (concat δ₀ δ)
  apply-bwd {n = n} (var i) δ δ₀ with splitAt n i
  ... | inj₁ j = id _
  ... | inj₂ k = id _
  apply-bwd unit      δ δ₀ = id _
  apply-bwd (base s)  δ δ₀ = id _
  apply-bwd (σ [+] τ) δ δ₀ = coprod-m (Lf-map (apply-bwd σ δ δ₀)) (Lf-map (apply-bwd τ δ δ₀))
  apply-bwd (σ [×] τ) δ δ₀ = Lf-map (prod-m (apply-bwd σ δ δ₀) (apply-bwd τ δ δ₀))
  apply-bwd (σ [→] τ) δ δ₀ = id _
  apply-bwd {Δ} {n} (μ τ) δ δ₀ =
    μ-map (as-poly {Δ} {suc n} τ δ) δ₀ (as-poly {n + Δ} {1} τ (concat δ₀ δ)) δ∅
      (apply-fwd {n = 1} τ (concat δ₀ δ) (extend δ∅ M) ∘ ≡-to-⇒ (sym (ty-cong τ (env-pw δ δ₀ M))) ∘ apply-bwd τ δ (extend δ₀ M))
    where M = μ-obj (as-poly {n + Δ} {1} τ (concat δ₀ δ)) δ∅

-- Pointwise action of a lifted substitution on the extended environment: the new variable is mapped
-- to itself, and the (weakened) old ones ignore it.
sub-lift-pw : ∀ {Δ Δ'} (σ : TySub Δ Δ') (δ : Fin Δ' → obj) (X : obj) (i : Fin (suc Δ)) →
              ⟦ sub-lift σ i ⟧ty (concat (extend {0} δ∅ X) δ) ≡ concat (extend {0} δ∅ X) (λ j → ⟦ σ j ⟧ty δ) i
sub-lift-pw σ δ X Fin.zero    = refl
sub-lift-pw σ δ X (Fin.suc j) = ty-ren Fin.suc (σ j) (concat (extend {0} δ∅ X) δ)

-- Semantic substitution: substituting then interpreting maps to interpreting in the environment
-- that interprets the substituents (in each direction).
subst-fwd : ∀ {Δ Δ'} (σ : TySub Δ Δ') (τ : type Δ) (δ : Fin Δ' → obj) →
            ⟦ sub σ τ ⟧ty δ ⇒ ⟦ τ ⟧ty (λ i → ⟦ σ i ⟧ty δ)
subst-fwd σ (var i)     δ = id _
subst-fwd σ unit        δ = id _
subst-fwd σ (base s)    δ = id _
subst-fwd σ (τ₁ [+] τ₂) δ = coprod-m (Lf-map (subst-fwd σ τ₁ δ)) (Lf-map (subst-fwd σ τ₂ δ))
subst-fwd σ (τ₁ [×] τ₂) δ = Lf-map (prod-m (subst-fwd σ τ₁ δ) (subst-fwd σ τ₂ δ))
subst-fwd σ (τ₁ [→] τ₂) δ = id _
subst-fwd {Δ} {Δ'} σ (μ τ) δ =
  μ-map (as-poly {Δ'} {1} (sub (sub-lift σ) τ) δ) δ∅ (as-poly {Δ} {1} τ (λ i → ⟦ σ i ⟧ty δ)) δ∅
    (apply-fwd {n = 1} τ (λ i → ⟦ σ i ⟧ty δ) (extend δ∅ M)
     ∘ ≡-to-⇒ (ty-cong τ (sub-lift-pw σ δ M))
     ∘ subst-fwd (sub-lift σ) τ (concat (extend {0} δ∅ M) δ)
     ∘ apply-bwd {n = 1} (sub (sub-lift σ) τ) δ (extend δ∅ M))
  where M = μ-obj (as-poly {Δ} {1} τ (λ i → ⟦ σ i ⟧ty δ)) δ∅

subst-bwd : ∀ {Δ Δ'} (σ : TySub Δ Δ') (τ : type Δ) (δ : Fin Δ' → obj) →
            ⟦ τ ⟧ty (λ i → ⟦ σ i ⟧ty δ) ⇒ ⟦ sub σ τ ⟧ty δ
subst-bwd σ (var i)     δ = id _
subst-bwd σ unit        δ = id _
subst-bwd σ (base s)    δ = id _
subst-bwd σ (τ₁ [+] τ₂) δ = coprod-m (Lf-map (subst-bwd σ τ₁ δ)) (Lf-map (subst-bwd σ τ₂ δ))
subst-bwd σ (τ₁ [×] τ₂) δ = Lf-map (prod-m (subst-bwd σ τ₁ δ) (subst-bwd σ τ₂ δ))
subst-bwd σ (τ₁ [→] τ₂) δ = id _
subst-bwd {Δ} {Δ'} σ (μ τ) δ =
  μ-map (as-poly {Δ} {1} τ (λ i → ⟦ σ i ⟧ty δ)) δ∅ (as-poly {Δ'} {1} (sub (sub-lift σ) τ) δ) δ∅
    (apply-fwd {n = 1} (sub (sub-lift σ) τ) δ (extend δ∅ M)
     ∘ subst-bwd (sub-lift σ) τ (concat (extend {0} δ∅ M) δ)
     ∘ ≡-to-⇒ (sym (ty-cong τ (sub-lift-pw σ δ M)))
     ∘ apply-bwd {n = 1} τ (λ i → ⟦ σ i ⟧ty δ) (extend δ∅ M))
  where M = μ-obj (as-poly {Δ'} {1} (sub (sub-lift σ) τ) δ) δ∅

-- The single substitution push τ', read pointwise as an environment.
push-pw : ∀ (τ' : type 0) (i : Fin 1) → ⟦ push τ' i ⟧ty (λ ()) ≡ concat (extend {0} δ∅ (⟦ τ' ⟧ty (λ ()))) (λ ()) i
push-pw τ' Fin.zero = refl

-- Syntactic substitution is functor application.
sub-as-apply-fwd : (τ : type 1) (τ' : type 0) →
                   ⟦ τ [ τ' ] ⟧ty (λ ()) ⇒ fobj μ-obj (as-poly {0} {1} τ (λ ())) (extend δ∅ (⟦ τ' ⟧ty (λ ())))
sub-as-apply-fwd τ τ' =
  apply-fwd {0} {1} τ (λ ()) (extend δ∅ (⟦ τ' ⟧ty (λ ()))) ∘
  ≡-to-⇒ (ty-cong τ (push-pw τ')) ∘ subst-fwd (push τ') τ (λ ())

sub-as-apply-bwd : (τ : type 1) (τ' : type 0) →
                   fobj μ-obj (as-poly {0} {1} τ (λ ())) (extend δ∅ (⟦ τ' ⟧ty (λ ()))) ⇒ ⟦ τ [ τ' ] ⟧ty (λ ())
sub-as-apply-bwd τ τ' =
  subst-bwd (push τ') τ (λ ()) ∘
  ≡-to-⇒ (sym (ty-cong τ (push-pw τ'))) ∘ apply-bwd {0} {1} τ (λ ()) (extend δ∅ (⟦ τ' ⟧ty (λ ())))

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
    scopair (elimF (elim-const τ) ⟦ M₁ ⟧tm) (elimF (elim-const τ) ⟦ M₂ ⟧tm)
      ∘ ⟨ id _ , ⟦ M ⟧tm ⟩
  ⟦ pair M N ⟧tm        = injF ∘ ⟨ ⟦ M ⟧tm , ⟦ N ⟧tm ⟩
  ⟦ fst {τ₁ = τ₁} M ⟧tm = elimF (elim-const τ₁) (p₁ ∘ p₂) ∘ ⟨ id _ , ⟦ M ⟧tm ⟩
  ⟦ snd {τ₂ = τ₂} M ⟧tm = elimF (elim-const τ₂) (p₂ ∘ p₂) ∘ ⟨ id _ , ⟦ M ⟧tm ⟩
  ⟦ lam M ⟧tm           = injF ∘ lambda ⟦ M ⟧tm
  ⟦ app {τ = τ} M N ⟧tm =
    elimF (elim-const τ) (eval ∘ ⟨ p₂ , ⟦ N ⟧tm ∘ p₁ ⟩) ∘ ⟨ id _ , ⟦ M ⟧tm ⟩
  ⟦ bop ω Ms ⟧tm        = ⟦op⟧ ω ∘ ⟦ Ms ⟧tms
  ⟦ brel r Ms ⟧tm       = ⟦rel⟧ r ∘ ⟦ Ms ⟧tms
  ⟦ roll {τ = τ} M ⟧tm  =
    inMap (as-poly τ (λ ())) δ∅ ∘ sub-as-apply-fwd τ (μ τ) ∘ ⟦ M ⟧tm
  ⟦ fold {τ = τ} {σ = σ} alg M ⟧tm =
    ⦅ ⟦ alg ⟧tm ∘ prod-m (id _) (sub-as-apply-bwd τ σ) ⦆ ∘ ⟨ id _ , ⟦ M ⟧tm ⟩

  ⟦_⟧tms : ∀ {Γ σs} → Every (λ σ → Γ ⊢ base σ) σs → ⟦ Γ ⟧ctxt ⇒ list→product ⟦sort⟧ σs
  ⟦ [] ⟧tms     = to-terminal
  ⟦ M ∷ Ms ⟧tms = ⟨ ⟦ M ⟧tm , ⟦ Ms ⟧tms ⟩
