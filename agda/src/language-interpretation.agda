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
         HasWeakExponentials)
open import cmon-enriched using (CMonEnriched; Biproduct)
open import signature using (Signature; Model; PointedFPCat; PFPC[_,_,_,_])
open import polynomial-functor using (Poly)
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

open R using (Obj; Lf; Lf-map; injF; extend; fobj; HasMu; hasMu; fmor; μ-map; Constant; elimF;
              scale-const; Lf-constant; coprod-constant; prod-constant; PolyConst;
              fmor-cong; fmor-id; fmor-comp; fmor-μ; μ-map-cong; μ-map-id; μ-map-in; μ-map-comp)
open Category R.cat
open HasTerminal (R.terminal T) renaming (witness to 𝟙)
open HasProducts R.products renaming (pair to ⟨_,_⟩)

open HasCoproducts R.coproducts using (coprod; coprod-m; in₁; in₂)
open HasStrongCoproducts R.strongCoproducts using () renaming (copair to scopair)
open HasWeakExponentials 𝒞E using (lambda; eval) renaming (exp to _⟦→⟧_)
open language-syntax Sig
open HasMu hasMu
open Model Int

mutual
  ⟦_⟧ty : ∀ {Δ} → type Δ → (Fin Δ → obj) → obj
  ⟦ var i ⟧ty     δ = δ i
  ⟦ unit ⟧ty      δ = 𝟙ty
  ⟦ base s ⟧ty    δ = ⟦sort⟧ s
  ⟦ σ [+] τ ⟧ty δ = coprod (Lf (⟦ σ ⟧ty δ)) (Lf (⟦ τ ⟧ty δ))
  ⟦ σ [×] τ ⟧ty δ = Lf (prod (⟦ σ ⟧ty δ) (⟦ τ ⟧ty δ))
  ⟦ σ [→] τ ⟧ty δ = Lf (⟦ σ ⟧ty (λ ()) ⟦→⟧ ⟦ τ ⟧ty (λ ()))
  ⟦ μ τ ⟧ty       δ = μ-obj (as-poly τ δ) δ∅

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
ty-cong (var i)   h = h i
ty-cong unit      h = refl
ty-cong (base s)  h = refl
ty-cong (σ [+] τ) h = cong₂ (λ A B → coprod (Lf A) (Lf B)) (ty-cong σ h) (ty-cong τ h)
ty-cong (σ [×] τ) h = cong₂ (λ A B → Lf (prod A B)) (ty-cong σ h) (ty-cong τ h)
ty-cong (σ [→] τ) h = refl
ty-cong (μ τ)     h = cong (λ (P : Poly R.cat 1) → μ-obj P δ∅) (as-poly-cong τ h)

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
ty-ren ρ (var i)   δ = refl
ty-ren ρ unit      δ = refl
ty-ren ρ (base s)  δ = refl
ty-ren ρ (σ [+] τ) δ = cong₂ (λ A B → coprod (Lf A) (Lf B)) (ty-ren ρ σ δ) (ty-ren ρ τ δ)
ty-ren ρ (σ [×] τ) δ = cong₂ (λ A B → Lf (prod A B)) (ty-ren ρ σ δ) (ty-ren ρ τ δ)
ty-ren ρ (σ [→] τ) δ = refl
ty-ren ρ (μ τ)     δ = cong (λ (P : Poly R.cat 1) → μ-obj P δ∅) (as-poly-ren ρ τ δ)

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
