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

concat-mor : ∀ {n Δ} {δ₀ δ₀' : Fin n → obj} {δ δ' : Fin Δ → obj} →
             (∀ i → δ₀ i ⇒ δ₀' i) → (∀ i → δ i ⇒ δ' i) → ∀ i → concat δ₀ δ i ⇒ concat δ₀' δ' i
concat-mor {n} {Δ} {δ₀} {δ₀'} {δ} {δ'} fs gs i = go (splitAt n i)
  where
    go : (s : Fin n ⊎ Fin Δ) → [ δ₀ , δ ] s ⇒ [ δ₀' , δ' ] s
    go (inj₁ j) = fs j
    go (inj₂ k) = gs k

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
env-pw : ∀ {Δ n} (δ : Fin Δ → obj) (δ₀ : Fin n → obj) (X : obj) (i : Fin (suc (n + Δ))) →
         concat (extend {0} δ∅ X) (concat δ₀ δ) i ≡ concat (extend δ₀ X) δ i
env-pw δ δ₀ X Fin.zero    = refl
env-pw {Δ} {n} δ δ₀ X (Fin.suc j) = go (splitAt n j)
  where
    go : (s : Fin n ⊎ Fin Δ) → [ δ₀ , δ ] s ≡ [ extend δ₀ X , δ ] (map₁ Fin.suc s)
    go (inj₁ k) = refl
    go (inj₂ l) = refl

env-pw-natural : ∀ {Δ n} {δ δ' : Fin Δ → obj} (gs : ∀ i → δ i ⇒ δ' i) {δ₀ δ₀' : Fin n → obj} (fs : ∀ i → δ₀ i ⇒ δ₀' i)
                 {X X' : obj} (k : X ⇒ X') (i : Fin (suc (n + Δ))) →
                 (concat-mor (extend-mor fs k) gs i ∘ ≡-to-⇒ (env-pw δ δ₀ X i))
                   ≈ (≡-to-⇒ (env-pw δ' δ₀' X' i) ∘ concat-mor {n = 1} (extend-mor (λ j → id _) k) (concat-mor fs gs) i)
env-pw-natural gs fs k Fin.zero = ≈-trans id-right (≈-sym id-left)
env-pw-natural {n = n} gs fs k (Fin.suc j) with splitAt n j
... | inj₁ l = ≈-trans id-right (≈-sym id-left)
... | inj₂ l = ≈-trans id-right (≈-sym id-left)

env-pw-natural⁻ : ∀ {Δ n} {δ δ' : Fin Δ → obj} (gs : ∀ i → δ i ⇒ δ' i) {δ₀ δ₀' : Fin n → obj} (fs : ∀ i → δ₀ i ⇒ δ₀' i)
                  {X X' : obj} (k : X ⇒ X') (i : Fin (suc (n + Δ))) →
                  (concat-mor {n = 1} (extend-mor (λ j → id _) k) (concat-mor fs gs) i ∘ ≡-to-⇒ (sym (env-pw δ δ₀ X i)))
                    ≈ (≡-to-⇒ (sym (env-pw δ' δ₀' X' i)) ∘ concat-mor (extend-mor fs k) gs i)
env-pw-natural⁻ gs fs k Fin.zero = ≈-trans id-right (≈-sym id-left)
env-pw-natural⁻ {n = n} gs fs k (Fin.suc j) with splitAt n j
... | inj₁ l = ≈-trans id-right (≈-sym id-left)
... | inj₂ l = ≈-trans id-right (≈-sym id-left)

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

env-pw-inv : ∀ {Δ n} (τ : type (suc n + Δ)) (δ : Fin Δ → obj) (δ₀ : Fin n → obj) (X : obj) →
             (as-poly-map τ (λ i → ≡-to-⇒ (sym (env-pw δ δ₀ X i))) δ∅ ∘ as-poly-map τ (λ i → ≡-to-⇒ (env-pw δ δ₀ X i)) δ∅) ≈ id _
env-pw-inv τ δ δ₀ X =
  ≈-trans (as-poly-map-comp τ _ _ δ∅) (≈-trans (as-poly-map-cong τ (λ i → ≡-to-⇒-sym-l (env-pw δ δ₀ X i)) δ∅) (as-poly-map-id τ δ∅))

env-pw-inv' : ∀ {Δ n} (τ : type (suc n + Δ)) (δ : Fin Δ → obj) (δ₀ : Fin n → obj) (X : obj) →
              (as-poly-map τ (λ i → ≡-to-⇒ (env-pw δ δ₀ X i)) δ∅ ∘ as-poly-map τ (λ i → ≡-to-⇒ (sym (env-pw δ δ₀ X i))) δ∅) ≈ id _
env-pw-inv' τ δ δ₀ X =
  ≈-trans (as-poly-map-comp τ _ _ δ∅) (≈-trans (as-poly-map-cong τ (λ i → ≡-to-⇒-sym-r (env-pw δ δ₀ X i)) δ∅) (as-poly-map-id τ δ∅))

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
    ≈⟨ ∘-cong ≈-refl (≈-trans (∘-cong (env-pw-inv τ δ δ₀ X) ≈-refl) id-left) ⟩
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
    ≈⟨ ∘-cong ≈-refl (≈-trans (∘-cong (env-pw-inv' τ δ δ₀ X) ≈-refl) id-left) ⟩
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


sub-lift-pw-inv : ∀ {Δ Δ'} (σ : TySub Δ Δ') (τ : type (suc Δ)) (δ : Fin Δ' → obj) (X : obj) →
                  (as-poly-map τ (λ i → ≡-to-⇒ (sym (sub-lift-pw σ δ X i))) δ∅ ∘ as-poly-map τ (λ i → ≡-to-⇒ (sub-lift-pw σ δ X i)) δ∅)
                    ≈ id _
sub-lift-pw-inv σ τ δ X =
  ≈-trans (as-poly-map-comp τ _ _ δ∅)
          (≈-trans (as-poly-map-cong τ (λ i → ≡-to-⇒-sym-l (sub-lift-pw σ δ X i)) δ∅) (as-poly-map-id τ δ∅))

sub-lift-pw-inv' : ∀ {Δ Δ'} (σ : TySub Δ Δ') (τ : type (suc Δ)) (δ : Fin Δ' → obj) (X : obj) →
                   (as-poly-map τ (λ i → ≡-to-⇒ (sub-lift-pw σ δ X i)) δ∅ ∘ as-poly-map τ (λ i → ≡-to-⇒ (sym (sub-lift-pw σ δ X i))) δ∅)
                     ≈ id _
sub-lift-pw-inv' σ τ δ X =
  ≈-trans (as-poly-map-comp τ _ _ δ∅)
          (≈-trans (as-poly-map-cong τ (λ i → ≡-to-⇒-sym-r (sub-lift-pw σ δ X i)) δ∅) (as-poly-map-id τ δ∅))

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
    ≈⟨ ∘-cong (≈-trans (assoc _ _ _) (≈-trans (∘-cong ≈-refl (sub-lift-pw-inv σ τ δ X)) id-right)) ≈-refl ⟩
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
    ≈⟨ ∘-cong (≈-trans (assoc _ _ _) (≈-trans (∘-cong ≈-refl (sub-lift-pw-inv' σ τ δ X)) id-right)) ≈-refl ⟩
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


-- The single substitution push τ', read pointwise as an environment.
push-pw : ∀ (τ' : type 0) (i : Fin 1) → ⟦ push τ' i ⟧ty (λ ()) ≡ concat (extend {0} δ∅ (⟦ τ' ⟧ty (λ ()))) (λ ()) i
push-pw τ' Fin.zero = refl

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
