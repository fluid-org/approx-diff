{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (0ℓ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import every using (Every; []; _∷_)
open import signature using (Signature)
open import primitives using (Primitives)
import matrix
import cmon-enriched
open import categories using (Category; HasProducts; HasTerminal)

-- Evaluation threading a control source: a distinguished extra input position holding the last
-- eliminated constructor, initially the run itself. A terminal rule attaches the source to its
-- whole value; a constructor attaches it to the new root; an elimination points the consumed root
-- at the source and makes that root the source of its continuation. Restricting to the environment
-- columns is intended to recover the evaluation relation of language-operational.evaluation.
module language-operational.control {ℓ} (Sig : Signature ℓ)
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (𝒫 : Primitives S Sig) (elim-weight : Setoid.Carrier A) where

open Signature Sig
open Primitives 𝒫
open prop-setoid._⇒_ using (func)
open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.type-substitution Sig using (unfold₁; unfold₁-inst)
open import language-operational.evaluation Sig S 𝒫 elim-weight
  using (Val; Env; lookup; width; width-env; width-subst; proj-var; bool→val; ctrl-row; products)
open Val
open Env

private
  module M = matrix.Mat S

open Category M.cat using (_⇒_; _∘_) renaming (id to idm)
open HasTerminal M.terminal using (to-terminal)
open HasProducts products using (p₁; p₂) renaming (pair to ⟨_,_⟩)

-- Input selectors: the control source is the first input position.
src-col : ∀ {m} → suc m ⇒ 1
src-col {m} = p₁ {1} {m}

env-cols : ∀ {m} → suc m ⇒ m
env-cols {m} = p₂ {1} {m}

-- The control edge from the source to every position of the result.
wsrc : ∀ {m n} → suc m ⇒ n
wsrc = ctrl-row ∘ src-col

-- The source of an elimination's continuation: the consumed root, itself pointed at the source.
new-src : ∀ {m n} → suc m ⇒ suc n → suc m ⇒ 1
new-src R = (p₁ {1} ∘ R) M.+ₘ wsrc

-- A test's outcome is a fresh boolean: both positions carry the source, the root also the reading.
brel-src : ∀ {Γ} (γ : Env Γ) (d : suc (width-env γ) ⇒ 1) (b : ⊤ {0ℓ} ⊎ ⊤ {0ℓ}) →
           suc (width-env γ) ⇒ width (bool→val b)
brel-src γ d (inj₁ _) = ⟨ d M.+ₘ wsrc , wsrc ⟩
brel-src γ d (inj₂ _) = ⟨ d M.+ₘ wsrc , wsrc ⟩

mutual
  data _,_⇓_[_] : ∀ {Γ τ} (γ : Env Γ) (t : Γ ⊢ τ) (v : Val τ) →
                   suc (width-env γ) ⇒ width v → Set ℓ where
    ⇓-var    : ∀ {Γ τ} {γ : Env Γ} (x : Γ ∋ τ) →
               γ , var x ⇓ lookup x γ [ (proj-var x γ ∘ env-cols) M.+ₘ wsrc ]
    ⇓-unit   : ∀ {Γ} {γ : Env Γ} → γ , unit ⇓ unit [ wsrc ]
    ⇓-inl    : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₁} {v R} →
               γ , t ⇓ v [ R ] → γ , inl {τ₂ = τ₂} t ⇓ inl v [ ⟨ wsrc , R ⟩ ]
    ⇓-inr    : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₂} {v R} →
               γ , t ⇓ v [ R ] → γ , inr {τ₁ = τ₁} t ⇓ inr v [ ⟨ wsrc , R ⟩ ]
    ⇓-case-l : ∀ {Γ τ₁ τ₂ τ} {γ : Env Γ} {s : Γ ⊢ τ₁ [+] τ₂} {t₁ : Γ ▸ τ₁ ⊢ τ} {t₂ : Γ ▸ τ₂ ⊢ τ}
               {v u R T} →
               γ , s ⇓ inl v [ R ] → γ · v , t₁ ⇓ u [ T ] →
               γ , case s t₁ t₂ ⇓ u [ T ∘ ⟨ new-src R , ⟨ env-cols {width-env γ} , p₂ {1} ∘ R ⟩ ⟩ ]
    ⇓-case-r : ∀ {Γ τ₁ τ₂ τ} {γ : Env Γ} {s : Γ ⊢ τ₁ [+] τ₂} {t₁ : Γ ▸ τ₁ ⊢ τ} {t₂ : Γ ▸ τ₂ ⊢ τ}
               {v u R T} →
               γ , s ⇓ inr v [ R ] → γ · v , t₂ ⇓ u [ T ] →
               γ , case s t₁ t₂ ⇓ u [ T ∘ ⟨ new-src R , ⟨ env-cols {width-env γ} , p₂ {1} ∘ R ⟩ ⟩ ]
    ⇓-pair   : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {s : Γ ⊢ τ₁} {t : Γ ⊢ τ₂} {v u R T} →
               γ , s ⇓ v [ R ] → γ , t ⇓ u [ T ] →
               γ , pair s t ⇓ pair v u [ ⟨ wsrc {n = 1} , ⟨ R , T ⟩ ⟩ ]
    ⇓-fst    : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₁ [×] τ₂} {v u R} →
               γ , t ⇓ pair v u [ R ] →
               γ , fst t ⇓ v [ p₁ {width v} {width u} ∘ (p₂ {1} ∘ R) ]
    ⇓-snd    : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₁ [×] τ₂} {v u R} →
               γ , t ⇓ pair v u [ R ] →
               γ , snd t ⇓ u [ p₂ {width v} {width u} ∘ (p₂ {1} ∘ R) ]
    ⇓-lam    : ∀ {Γ σ τ} {γ : Env Γ} {t : Γ ▸ σ ⊢ τ} →
               γ , lam t ⇓ clo γ t [ ⟨ wsrc , env-cols ⟩ ]
    ⇓-app    : ∀ {Γ Γ' σ τ} {γ : Env Γ} {γ' : Env Γ'} {s : Γ ⊢ σ [→] τ} {t t' v u R T U} →
               γ , s ⇓ clo {Γ'} γ' t' [ R ] → γ , t ⇓ v [ T ] → γ' · v , t' ⇓ u [ U ] →
               γ , app s t ⇓ u [ U ∘ ⟨ new-src R , ⟨ p₂ {1} ∘ R , T ⟩ ⟩ ]
    ⇓-bop    : ∀ {Γ is o'} {γ : Env Γ} {ω : op is o'} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R} →
               γ , Ms ⇓s vs [ R ] →
               γ , bop ω Ms ⇓ const (op-fun ω .func vs) [ (op-deps ω .func vs ∘ R) M.+ₘ wsrc ]
    ⇓-brel   : ∀ {Γ is} {γ : Env Γ} {ω : rel is} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R} →
               γ , Ms ⇓s vs [ R ] →
               γ , brel ω Ms ⇓ bool→val (rel-pred ω .func vs)
                     [ brel-src γ (rel-deps ω .func vs ∘ R) (rel-pred ω .func vs) ]
    ⇓-roll   : ∀ {Γ} {τ : type 1} {γ : Env Γ} {t : Γ ⊢ τ [ μ τ ]} {v R} →
               γ , t ⇓ v [ R ] → γ , roll {τ = τ} t ⇓ roll {τ} v [ R ]
    ⇓-fold   : ∀ {Γ} {τ : type 1} {σ : type 0} {γ : Env Γ} {s : Γ ▸ τ [ σ ] ⊢ σ} {t : Γ ⊢ μ τ}
               {v u R R'} →
               γ , t ⇓ v [ R ] → Map γ {τ} {σ} s (var zero) v R u R' → γ , fold s t ⇓ u [ R' ]

  data _,_⇓s_[_] {Γ} (γ : Env Γ) : ∀ {is} → Every (λ s → Γ ⊢ base s) is →
                  sort-vals is → suc (width-env γ) ⇒ bases-width is →
                  Set ℓ where
    []  : γ , [] ⇓s tt [ to-terminal ]
    _∷_ : ∀ {i is v vs R Rs} {M : Γ ⊢ base i} {Ms : Every (λ s → Γ ⊢ base s) is} →
          γ , M ⇓ const v [ R ] → γ , Ms ⇓s vs [ Rs ] → γ , (M ∷ Ms) ⇓s (v , vs) [ ⟨ R , Rs ⟩ ]

  -- Functorial action of σ' on the fold s: the source passes through unchanged, and each rebuilt
  -- constructor carries the copied root pointed at the source.
  data Map {Γ} (γ : Env Γ) {τ₀ : type 1} {σr : type 0} (s : Γ ▸ τ₀ [ σr ] ⊢ σr) :
           (σ' : type 1) (v : Val (σ' [ μ τ₀ ])) → suc (width-env γ) ⇒ width v →
           (v' : Val (σ' [ σr ])) → suc (width-env γ) ⇒ width v' →
           Set ℓ where
    m-rec   : ∀ {w w' u R R' T} →
              Map γ s τ₀ w R w' R' → γ · w' , s ⇓ u [ T ] →
              Map γ s (var zero) (roll w) R u (T ∘ ⟨ src-col , ⟨ env-cols {width-env γ} , R' ⟩ ⟩)
    m-unit  : ∀ {v R} → Map γ s unit v R v R
    m-base  : ∀ {b v R} → Map γ s (base b) v R v R
    m-arrow : ∀ {σ₁ σ₂ v R} → Map γ s (σ₁ [→] σ₂) v R v R
    m-inl   : ∀ {σ₁ σ₂ v v' R R'} →
              Map γ s σ₁ v (p₂ {1} ∘ R) v' R' →
              Map γ s (σ₁ [+] σ₂) (inl v) R (inl v')
                  ⟨ (p₁ {1} {width v} ∘ R) M.+ₘ wsrc , R' ⟩
    m-inr   : ∀ {σ₁ σ₂ v v' R R'} →
              Map γ s σ₂ v (p₂ {1} ∘ R) v' R' →
              Map γ s (σ₁ [+] σ₂) (inr v) R (inr v')
                  ⟨ (p₁ {1} {width v} ∘ R) M.+ₘ wsrc , R' ⟩
    m-pair  : ∀ {σ₁ σ₂ v v' u u' R T U} →
              Map γ s σ₁ v (p₁ {width v} {width u} ∘ (p₂ {1} ∘ R)) v' T →
              Map γ s σ₂ u (p₂ {width v} {width u} ∘ (p₂ {1} ∘ R)) u' U →
              Map γ s (σ₁ [×] σ₂) (pair v u) R (pair v' u')
                  ⟨ (p₁ {1} {width v + width u} ∘ R) M.+ₘ wsrc , ⟨ T , U ⟩ ⟩
    m-mu    : ∀ {τ' : type 2} {w w' R R'} →
              Map γ s (unfold₁ τ') w R w' R' →
              Map γ s (μ τ')
                  (roll (subst Val (unfold₁-inst τ' (μ τ₀)) w))
                  (subst (suc (width-env γ) ⇒_) (sym (width-subst (unfold₁-inst τ' (μ τ₀)) w)) R)
                  (roll (subst Val (unfold₁-inst τ' σr) w'))
                  (subst (suc (width-env γ) ⇒_) (sym (width-subst (unfold₁-inst τ' σr) w')) R')

infix 25 _,_⇓_[_] _,_⇓s_[_]
