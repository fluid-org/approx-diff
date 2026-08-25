{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (0ℓ)
open import Data.Nat using (suc; _+_)
open import Data.Fin using (zero)
open import Data.Product using (Σ; _,_; proj₁)
open import every using (Every; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import categories using (Category)
open import signature using (Signature)
open import signature.interpretation using (Interpretation)
import matrix

-- A term evaluates in at most one way: the value, the relation and the derivation are determined.
module language-operational.uniqueness
  {ℓ} (Sig : Signature ℓ)
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (ℐ : Interpretation S Sig) (ctrl-weight : Setoid.Carrier A) where

open Signature Sig
open Interpretation ℐ
open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.type-substitution Sig using (unfold₁-inst)
open import language-operational.evaluation Sig S ℐ ctrl-weight

private
  module M = matrix.Mat S
open Category M.cat using (_⇒_)

Derivation : ∀ {Γ τ} (γ : Env Γ) (t : Γ ⊢ τ) → Set ℓ
Derivation {τ = τ} γ t = Σ (Val τ) λ v → Σ (suc (width-env γ) ⇒ width v) λ R → γ , t ⇓ v [ R ]

Derivations : ∀ {Γ is} (γ : Env Γ) (Ms : Every (λ s → Γ ⊢ base s) is) → Set ℓ
Derivations {is = is} γ Ms =
  Σ (sort-vals is) λ vs → Σ (suc (width-env γ) ⇒ bases-width is) λ Rs → γ , Ms ⇓s vs [ Rs ]

MapDerivation : ∀ {Γ} (γ : Env Γ) (τ₀ : type 1) (σr : type 0) (s : Γ ▸ τ₀ [ σr ] ⊢ σr) (σ' : type 1) → Set ℓ
MapDerivation γ τ₀ σr s σ' =
  Σ (Val (σ' [ μ τ₀ ])) λ v → Σ (Val (σ' [ σr ])) λ v' →
  Σ ((suc (width-env γ) + width v) ⇒ width v') λ F → Map γ {τ₀} {σr} s σ' v v' F

private
  roll-inj : ∀ {τ : type 1} {v v' : Val (τ [ μ τ ])} → roll {τ} v ≡ roll v' → v ≡ v'
  roll-inj refl = refl

  subst-inj : ∀ {τ τ' : type 0} (e : τ ≡ τ') {v v' : Val τ} → subst Val e v ≡ subst Val e v' → v ≡ v'
  subst-inj refl p = p

unique : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v v' R R'} (D : γ , t ⇓ v [ R ]) (D' : γ , t ⇓ v' [ R' ]) →
         _≡_ {A = Derivation γ t} (v , R , D) (v' , R' , D')
unique-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs vs' Rs Rs'}
           (D : γ , Ms ⇓s vs [ Rs ]) (D' : γ , Ms ⇓s vs' [ Rs' ]) →
           _≡_ {A = Derivations γ Ms} (vs , Rs , D) (vs' , Rs' , D')
unique-map : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr} {σ' : type 1}
             {v v₂ v' v₂' F F'} (M : Map γ {τ₀} {σr} s σ' v v' F) (M' : Map γ {τ₀} {σr} s σ' v₂ v₂' F') →
             v ≡ v₂ → _≡_ {A = MapDerivation γ τ₀ σr s σ'} (v , v' , F , M) (v₂ , v₂' , F' , M')

unique (⇓-var x) (⇓-var _) = refl
unique ⇓-unit ⇓-unit = refl
unique (⇓-inl D) (⇓-inl D') with unique D D'
... | refl = refl
unique (⇓-inr D) (⇓-inr D') with unique D D'
... | refl = refl
unique (⇓-case-l D₁ D₂) (⇓-case-l D₁' D₂') with unique D₁ D₁'
... | refl with unique D₂ D₂'
...   | refl = refl
unique (⇓-case-l D₁ D₂) (⇓-case-r D₁' D₂') with unique D₁ D₁'
... | ()
unique (⇓-case-r D₁ D₂) (⇓-case-l D₁' D₂') with unique D₁ D₁'
... | ()
unique (⇓-case-r D₁ D₂) (⇓-case-r D₁' D₂') with unique D₁ D₁'
... | refl with unique D₂ D₂'
...   | refl = refl
unique (⇓-pair D₁ D₂) (⇓-pair D₁' D₂') with unique D₁ D₁' | unique D₂ D₂'
... | refl | refl = refl
unique (⇓-fst D) (⇓-fst D') with unique D D'
... | refl = refl
unique (⇓-snd D) (⇓-snd D') with unique D D'
... | refl = refl
unique ⇓-lam ⇓-lam = refl
unique (⇓-app D₁ D₂ D₃) (⇓-app D₁' D₂' D₃') with unique D₁ D₁' | unique D₂ D₂'
... | refl | refl with unique D₃ D₃'
...   | refl = refl
unique (⇓-bop D) (⇓-bop D') with unique-s D D'
... | refl = refl
unique (⇓-brel D) (⇓-brel D') with unique-s D D'
... | refl = refl
unique (⇓-roll D) (⇓-roll D') with unique D D'
... | refl = refl
unique (⇓-fold {τ = τ₀} {σ = σr} {s = s} D M) (⇓-fold D' M') with unique D D'
... | refl with unique-map {τ₀ = τ₀} {σr = σr} {s = s} M M' refl
...   | refl = refl

unique-s [] [] = refl
unique-s (D ∷ Ds) (D' ∷ Ds') with unique D D' | unique-s Ds Ds'
... | refl | refl = refl

unique-map {τ₀ = τ₀} {σr = σr} {s = s} (m-rec M D) (m-rec M' D') refl
  with unique-map {τ₀ = τ₀} {σr = σr} {s = s} M M' refl
... | refl with unique D D'
...   | refl = refl
unique-map m-unit m-unit refl = refl
unique-map m-base m-base refl = refl
unique-map m-arrow m-arrow refl = refl
unique-map {τ₀ = τ₀} {σr = σr} {s = s} (m-inl M) (m-inl M') refl
  with unique-map {τ₀ = τ₀} {σr = σr} {s = s} M M' refl
... | refl = refl
unique-map {τ₀ = τ₀} {σr = σr} {s = s} (m-inr M) (m-inr M') refl
  with unique-map {τ₀ = τ₀} {σr = σr} {s = s} M M' refl
... | refl = refl
unique-map {τ₀ = τ₀} {σr = σr} {s = s} (m-pair M₁ M₂) (m-pair M₁' M₂') refl
  with unique-map {τ₀ = τ₀} {σr = σr} {s = s} M₁ M₁' refl | unique-map {τ₀ = τ₀} {σr = σr} {s = s} M₂ M₂' refl
... | refl | refl = refl
unique-map {τ₀ = τ₀} {σr = σr} {s = s} (m-mu {τ' = τ'} M) (m-mu M') e
  with subst-inj (unfold₁-inst τ' (μ τ₀)) (roll-inj e)
... | refl with unique-map {τ₀ = τ₀} {σr = σr} {s = s} M M' refl
...   | refl = refl
