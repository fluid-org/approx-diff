{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.Fin using (zero)
open import Data.Bool as Bool using (Bool; not; _∧_)
open import Data.Bool.ListAction using (any)
open import Data.List using (List; []; _∷_; _++_; map; filterᵇ)
open import Data.Nat using (ℕ; suc; _+_)
open import every using (Every; []; _∷_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import signature using (Signature)
open import primitives using (Primitives)
import matrix
import two

-- Paths of a derivation: ε addresses the derivation itself, and each step constructor addresses one
-- premise, in evaluation order. One path type per judgement form, mutually with the judgements they
-- index.
module language-operational.path {ℓ} (Sig : Signature ℓ) (𝒫 : Primitives two.semiring Sig) where

open Signature Sig
open Primitives 𝒫
open import language-syntax Sig renaming (_,_ to _▸_)
open import type-substitution Sig using (unfold₁)
open import language-operational.evaluation Sig 𝒫

private
  module M = matrix.Mat two.semiring

open import categories using (Category; HasProducts)
open Category M.cat using (_⇒_; _∘_)
open HasProducts products using (p₁; p₂)

mutual
  data Path : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v : Val τ} {R : width-env γ ⇒ width v} →
              γ , t ⇓ v [ R ] → Set ℓ where
    ε       : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} → Path D
    inl     : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₁} {v R} {D : γ , t ⇓ v [ R ]} →
              Path D → Path (⇓-inl {τ₂ = τ₂} D)
    inr     : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₂} {v R} {D : γ , t ⇓ v [ R ]} →
              Path D → Path (⇓-inr {τ₁ = τ₁} D)
    case-l₁ : ∀ {Γ τ₁ τ₂ τ} {γ : Env Γ} {s : Γ ⊢ τ₁ [+] τ₂} {t₁ : Γ ▸ τ₁ ⊢ τ} {t₂ : Γ ▸ τ₂ ⊢ τ}
              {v u R S} {D₁ : γ , s ⇓ inl v [ R ]} {D₂ : γ · v , t₁ ⇓ u [ S ]} →
              Path D₁ → Path (⇓-case-l {t₂ = t₂} D₁ D₂)
    case-l₂ : ∀ {Γ τ₁ τ₂ τ} {γ : Env Γ} {s : Γ ⊢ τ₁ [+] τ₂} {t₁ : Γ ▸ τ₁ ⊢ τ} {t₂ : Γ ▸ τ₂ ⊢ τ}
              {v u R S} {D₁ : γ , s ⇓ inl v [ R ]} {D₂ : γ · v , t₁ ⇓ u [ S ]} →
              Path D₂ → Path (⇓-case-l {t₂ = t₂} D₁ D₂)
    case-r₁ : ∀ {Γ τ₁ τ₂ τ} {γ : Env Γ} {s : Γ ⊢ τ₁ [+] τ₂} {t₁ : Γ ▸ τ₁ ⊢ τ} {t₂ : Γ ▸ τ₂ ⊢ τ}
              {v u R S} {D₁ : γ , s ⇓ inr v [ R ]} {D₂ : γ · v , t₂ ⇓ u [ S ]} →
              Path D₁ → Path (⇓-case-r {t₁ = t₁} D₁ D₂)
    case-r₂ : ∀ {Γ τ₁ τ₂ τ} {γ : Env Γ} {s : Γ ⊢ τ₁ [+] τ₂} {t₁ : Γ ▸ τ₁ ⊢ τ} {t₂ : Γ ▸ τ₂ ⊢ τ}
              {v u R S} {D₁ : γ , s ⇓ inr v [ R ]} {D₂ : γ · v , t₂ ⇓ u [ S ]} →
              Path D₂ → Path (⇓-case-r {t₁ = t₁} D₁ D₂)
    pair₁   : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {s : Γ ⊢ τ₁} {t : Γ ⊢ τ₂} {v u R S}
              {D₁ : γ , s ⇓ v [ R ]} {D₂ : γ , t ⇓ u [ S ]} →
              Path D₁ → Path (⇓-pair D₁ D₂)
    pair₂   : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {s : Γ ⊢ τ₁} {t : Γ ⊢ τ₂} {v u R S}
              {D₁ : γ , s ⇓ v [ R ]} {D₂ : γ , t ⇓ u [ S ]} →
              Path D₂ → Path (⇓-pair D₁ D₂)
    fst     : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₁ [×] τ₂} {v u R} {D : γ , t ⇓ pair v u [ R ]} →
              Path D → Path (⇓-fst D)
    snd     : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₁ [×] τ₂} {v u R} {D : γ , t ⇓ pair v u [ R ]} →
              Path D → Path (⇓-snd D)
    app₁    : ∀ {Γ Γ' σ τ} {γ : Env Γ} {γ' : Env Γ'} {s : Γ ⊢ σ [→] τ} {t t' v u R S T}
              {D₁ : γ , s ⇓ clo {Γ'} γ' t' [ R ]} {D₂ : γ , t ⇓ v [ S ]} {D₃ : γ' · v , t' ⇓ u [ T ]} →
              Path D₁ → Path (⇓-app D₁ D₂ D₃)
    app₂    : ∀ {Γ Γ' σ τ} {γ : Env Γ} {γ' : Env Γ'} {s : Γ ⊢ σ [→] τ} {t t' v u R S T}
              {D₁ : γ , s ⇓ clo {Γ'} γ' t' [ R ]} {D₂ : γ , t ⇓ v [ S ]} {D₃ : γ' · v , t' ⇓ u [ T ]} →
              Path D₂ → Path (⇓-app D₁ D₂ D₃)
    app₃    : ∀ {Γ Γ' σ τ} {γ : Env Γ} {γ' : Env Γ'} {s : Γ ⊢ σ [→] τ} {t t' v u R S T}
              {D₁ : γ , s ⇓ clo {Γ'} γ' t' [ R ]} {D₂ : γ , t ⇓ v [ S ]} {D₃ : γ' · v , t' ⇓ u [ T ]} →
              Path D₃ → Path (⇓-app D₁ D₂ D₃)
    bop     : ∀ {Γ is o'} {γ : Env Γ} {ω : op is o'} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
              {D : γ , Ms ⇓s vs [ R ]} →
              PathS D → Path (⇓-bop {ω = ω} D)
    brel    : ∀ {Γ is} {γ : Env Γ} {ω : rel is} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
              {D : γ , Ms ⇓s vs [ R ]} →
              PathS D → Path (⇓-brel {ω = ω} D)
    roll    : ∀ {Γ} {τ : type 1} {γ : Env Γ} {t : Γ ⊢ τ [ μ τ ]} {v : Val (τ [ μ τ ])}
              {R : width-env γ ⇒ width v} {D : γ , t ⇓ v [ R ]} →
              Path D → Path (⇓-roll {τ = τ} D)
    fold₁   : ∀ {Γ} {τ : type 1} {σ : type 0} {γ : Env Γ} {s : Γ ▸ τ [ σ ] ⊢ σ} {t : Γ ⊢ μ τ}
              {v u R R'} {D₁ : γ , t ⇓ v [ R ]} {D₂ : Map γ {τ} {σ} s (var zero) v R u R'} →
              Path D₁ → Path (⇓-fold D₁ D₂)
    fold₂   : ∀ {Γ} {τ : type 1} {σ : type 0} {γ : Env Γ} {s : Γ ▸ τ [ σ ] ⊢ σ} {t : Γ ⊢ μ τ}
              {v u R R'} {D₁ : γ , t ⇓ v [ R ]} {D₂ : Map γ {τ} {σ} s (var zero) v R u R'} →
              PathM D₂ → Path (⇓-fold D₁ D₂)

  data PathS : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs}
               {R : width-env γ ⇒ bases-width is} → γ , Ms ⇓s vs [ R ] → Set ℓ where
    ε  : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
         {D : γ , Ms ⇓s vs [ R ]} → PathS D
    hd : ∀ {Γ i is} {γ : Env Γ} {v vs R Rs} {M : Γ ⊢ base i} {Ms : Every (λ s → Γ ⊢ base s) is}
         {D₁ : γ , M ⇓ const v [ R ]} {D₂ : γ , Ms ⇓s vs [ Rs ]} →
         Path D₁ → PathS (D₁ ∷ D₂)
    tl : ∀ {Γ i is} {γ : Env Γ} {v vs R Rs} {M : Γ ⊢ base i} {Ms : Every (λ s → Γ ⊢ base s) is}
         {D₁ : γ , M ⇓ const v [ R ]} {D₂ : γ , Ms ⇓s vs [ Rs ]} →
         PathS D₂ → PathS (D₁ ∷ D₂)

  data PathM : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
               {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R} {v' : Val (σ' [ σr ])} {R'} →
               Map γ {τ₀} {σr} s σ' v R v' R' → Set ℓ where
    ε       : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
              {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
              {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
              {D : Map γ s σ' v R v' R'} → PathM D
    m-rec₁  : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
              {w : Val (τ₀ [ μ τ₀ ])} {R : width-env γ ⇒ width w}
              {w' : Val (τ₀ [ σr ])} {R' : width-env γ ⇒ width w'}
              {u : Val σr} {S : width-env (γ · w') ⇒ width u}
              {D₁ : Map γ s τ₀ w R w' R'} {D₂ : γ · w' , s ⇓ u [ S ]} →
              PathM D₁ → PathM (m-rec D₁ D₂)
    m-rec₂  : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
              {w : Val (τ₀ [ μ τ₀ ])} {R : width-env γ ⇒ width w}
              {w' : Val (τ₀ [ σr ])} {R' : width-env γ ⇒ width w'}
              {u : Val σr} {S : width-env (γ · w') ⇒ width u}
              {D₁ : Map γ s τ₀ w R w' R'} {D₂ : γ · w' , s ⇓ u [ S ]} →
              Path D₂ → PathM (m-rec D₁ D₂)
    m-inl   : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
              {σ₁ σ₂ : type 1} {v : Val (σ₁ [ μ τ₀ ])} {R : width-env γ ⇒ width v}
              {v' : Val (σ₁ [ σr ])} {R' : width-env γ ⇒ width v'}
              {D : Map γ s σ₁ v R v' R'} →
              PathM D → PathM (m-inl {σ₂ = σ₂} D)
    m-inr   : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
              {σ₁ σ₂ : type 1} {v : Val (σ₂ [ μ τ₀ ])} {R : width-env γ ⇒ width v}
              {v' : Val (σ₂ [ σr ])} {R' : width-env γ ⇒ width v'}
              {D : Map γ s σ₂ v R v' R'} →
              PathM D → PathM (m-inr {σ₁ = σ₁} D)
    m-pair₁ : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
              {σ₁ σ₂ : type 1} {v : Val (σ₁ [ μ τ₀ ])} {u : Val (σ₂ [ μ τ₀ ])}
              {R : width-env γ ⇒ width (pair v u)}
              {v' : Val (σ₁ [ σr ])} {S : width-env γ ⇒ width v'}
              {u' : Val (σ₂ [ σr ])} {T : width-env γ ⇒ width u'}
              {D₁ : Map γ s σ₁ v (p₁ ∘ R) v' S} {D₂ : Map γ s σ₂ u (p₂ ∘ R) u' T} →
              PathM D₁ → PathM (m-pair D₁ D₂)
    m-pair₂ : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
              {σ₁ σ₂ : type 1} {v : Val (σ₁ [ μ τ₀ ])} {u : Val (σ₂ [ μ τ₀ ])}
              {R : width-env γ ⇒ width (pair v u)}
              {v' : Val (σ₁ [ σr ])} {S : width-env γ ⇒ width v'}
              {u' : Val (σ₂ [ σr ])} {T : width-env γ ⇒ width u'}
              {D₁ : Map γ s σ₁ v (p₁ ∘ R) v' S} {D₂ : Map γ s σ₂ u (p₂ ∘ R) u' T} →
              PathM D₂ → PathM (m-pair D₁ D₂)
    m-mu    : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
              {τ' : type 2} {w : Val (unfold₁ τ' [ μ τ₀ ])} {R : width-env γ ⇒ width w}
              {w' : Val (unfold₁ τ' [ σr ])} {R' : width-env γ ⇒ width w'}
              {D : Map γ s (unfold₁ τ') w R w' R'} →
              PathM D → PathM (m-mu {τ' = τ'} D)

-- The width of the vertex a path addresses: the width of the value of the subderivation there.
mutual
  width-at : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} → Path D → ℕ
  width-at (ε {v = v})  = width v
  width-at (inl p)      = width-at p
  width-at (inr p)      = width-at p
  width-at (case-l₁ p)  = width-at p
  width-at (case-l₂ p)  = width-at p
  width-at (case-r₁ p)  = width-at p
  width-at (case-r₂ p)  = width-at p
  width-at (pair₁ p)    = width-at p
  width-at (pair₂ p)    = width-at p
  width-at (fst p)      = width-at p
  width-at (snd p)      = width-at p
  width-at (app₁ p)     = width-at p
  width-at (app₂ p)     = width-at p
  width-at (app₃ p)     = width-at p
  width-at (bop p)      = width-at-s p
  width-at (brel p)     = width-at-s p
  width-at (roll p)     = width-at p
  width-at (fold₁ p)    = width-at p
  width-at (fold₂ p)    = width-at-m p

  width-at-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
               {D : γ , Ms ⇓s vs [ R ]} → PathS D → ℕ
  width-at-s (ε {is = is}) = bases-width is
  width-at-s (hd p)        = width-at p
  width-at-s (tl p)        = width-at-s p

  width-at-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
               {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
               {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
               {D : Map γ s σ' v R v' R'} → PathM D → ℕ
  width-at-m (ε {v' = v'}) = width v'
  width-at-m (m-rec₁ p)    = width-at-m p
  width-at-m (m-rec₂ p)    = width-at p
  width-at-m (m-inl p)     = width-at-m p
  width-at-m (m-inr p)     = width-at-m p
  width-at-m (m-pair₁ p)   = width-at-m p
  width-at-m (m-pair₂ p)   = width-at-m p
  width-at-m (m-mu p)      = width-at-m p

-- All paths of a derivation, root first, premises in evaluation order. Fixes the canonical order in
-- which sets of vertices are enumerated and hidden.
mutual
  paths : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) → List (Path D)
  paths D = ε ∷ interior D

  paths-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
            (D : γ , Ms ⇓s vs [ R ]) → List (PathS D)
  paths-s D = ε ∷ interior-s D

  paths-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
            {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
            {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
            (D : Map γ s σ' v R v' R') → List (PathM D)
  paths-m D = ε ∷ interior-m D

  interior : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) → List (Path D)
  interior (⇓-var x)        = []
  interior ⇓-unit           = []
  interior (⇓-inl D)        = map inl (paths D)
  interior (⇓-inr D)        = map inr (paths D)
  interior (⇓-case-l D₁ D₂) = map case-l₁ (paths D₁) ++ map case-l₂ (paths D₂)
  interior (⇓-case-r D₁ D₂) = map case-r₁ (paths D₁) ++ map case-r₂ (paths D₂)
  interior (⇓-pair D₁ D₂)   = map pair₁ (paths D₁) ++ map pair₂ (paths D₂)
  interior (⇓-fst D)        = map fst (paths D)
  interior (⇓-snd D)        = map snd (paths D)
  interior ⇓-lam            = []
  interior (⇓-app D₁ D₂ D₃) = map app₁ (paths D₁) ++ map app₂ (paths D₂) ++ map app₃ (paths D₃)
  interior (⇓-bop D)       = map bop (paths-s D)
  interior (⇓-brel D)      = map brel (paths-s D)
  interior (⇓-roll D)       = map roll (paths D)
  interior (⇓-fold D₁ D₂)   = map fold₁ (paths D₁) ++ map fold₂ (paths-m D₂)

  interior-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
               (D : γ , Ms ⇓s vs [ R ]) → List (PathS D)
  interior-s []       = []
  interior-s (D₁ ∷ D₂) = map hd (paths D₁) ++ map tl (paths-s D₂)

  interior-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
               {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
               {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
               (D : Map γ s σ' v R v' R') → List (PathM D)
  interior-m (m-rec D₁ D₂)   = map m-rec₁ (paths-m D₁) ++ map m-rec₂ (paths D₂)
  interior-m m-unit           = []
  interior-m m-base           = []
  interior-m m-arrow          = []
  interior-m (m-inl D)       = map m-inl (paths-m D)
  interior-m (m-inr D)       = map m-inr (paths-m D)
  interior-m (m-pair D₁ D₂)  = map m-pair₁ (paths-m D₁) ++ map m-pair₂ (paths-m D₂)
  interior-m (m-mu D)        = map m-mu (paths-m D)

-- Whether the value at a path is first-order, by the type of the subderivation's conclusion.
-- Operand-list vertices hold tuples of constants, so they are always first-order.
mutual
  fo-at : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} → Path D → Bool
  fo-at (ε {τ = τ}) = ⌊ first-order? τ ⌋
  fo-at (inl p)     = fo-at p
  fo-at (inr p)     = fo-at p
  fo-at (case-l₁ p) = fo-at p
  fo-at (case-l₂ p) = fo-at p
  fo-at (case-r₁ p) = fo-at p
  fo-at (case-r₂ p) = fo-at p
  fo-at (pair₁ p)   = fo-at p
  fo-at (pair₂ p)   = fo-at p
  fo-at (fst p)     = fo-at p
  fo-at (snd p)     = fo-at p
  fo-at (app₁ p)    = fo-at p
  fo-at (app₂ p)    = fo-at p
  fo-at (app₃ p)    = fo-at p
  fo-at (bop p)     = fo-at-s p
  fo-at (brel p)    = fo-at-s p
  fo-at (roll p)    = fo-at p
  fo-at (fold₁ p)   = fo-at p
  fo-at (fold₂ p)   = fo-at-m p

  fo-at-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
            {D : γ , Ms ⇓s vs [ R ]} → PathS D → Bool
  fo-at-s _ = Bool.true

  fo-at-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
            {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
            {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
            {D : Map γ s σ' v R v' R'} → PathM D → Bool
  fo-at-m (ε {σr = σr} {σ' = σ'}) = ⌊ first-order? (σ' [ σr ]) ⌋
  fo-at-m (m-rec₁ p)  = fo-at-m p
  fo-at-m (m-rec₂ p)  = fo-at p
  fo-at-m (m-inl p)   = fo-at-m p
  fo-at-m (m-inr p)   = fo-at-m p
  fo-at-m (m-pair₁ p) = fo-at-m p
  fo-at-m (m-pair₂ p) = fo-at-m p
  fo-at-m (m-mu p)    = fo-at-m p

-- Whether a path is the root.
is-ε : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} → Path D → Bool
is-ε ε = Bool.true
is-ε _ = Bool.false

-- The non-empty paths whose values are first-order: the vertices an interaction may reveal.
FO : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) → List (Path D)
FO D = filterᵇ (λ p → not (is-ε p) ∧ fo-at p) (paths D)

-- Equality of paths of the same derivation.
mutual
  eq-path : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} → Path D → Path D → Bool
  eq-path ε ε = Bool.true
  eq-path (inl p)     (inl q)     = eq-path p q
  eq-path (inr p)     (inr q)     = eq-path p q
  eq-path (case-l₁ p) (case-l₁ q) = eq-path p q
  eq-path (case-l₂ p) (case-l₂ q) = eq-path p q
  eq-path (case-r₁ p) (case-r₁ q) = eq-path p q
  eq-path (case-r₂ p) (case-r₂ q) = eq-path p q
  eq-path (pair₁ p)   (pair₁ q)   = eq-path p q
  eq-path (pair₂ p)   (pair₂ q)   = eq-path p q
  eq-path (fst p)     (fst q)     = eq-path p q
  eq-path (snd p)     (snd q)     = eq-path p q
  eq-path (app₁ p)    (app₁ q)    = eq-path p q
  eq-path (app₂ p)    (app₂ q)    = eq-path p q
  eq-path (app₃ p)    (app₃ q)    = eq-path p q
  eq-path (bop p)     (bop q)     = eq-path-s p q
  eq-path (brel p)    (brel q)    = eq-path-s p q
  eq-path (roll p)    (roll q)    = eq-path p q
  eq-path (fold₁ p)   (fold₁ q)   = eq-path p q
  eq-path (fold₂ p)   (fold₂ q)   = eq-path-m p q
  eq-path _ _ = Bool.false

  eq-path-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
              {D : γ , Ms ⇓s vs [ R ]} → PathS D → PathS D → Bool
  eq-path-s ε ε = Bool.true
  eq-path-s (hd p) (hd q) = eq-path p q
  eq-path-s (tl p) (tl q) = eq-path-s p q
  eq-path-s _ _ = Bool.false

  eq-path-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
              {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
              {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
              {D : Map γ s σ' v R v' R'} → PathM D → PathM D → Bool
  eq-path-m ε ε = Bool.true
  eq-path-m (m-rec₁ p)  (m-rec₁ q)  = eq-path-m p q
  eq-path-m (m-rec₂ p)  (m-rec₂ q)  = eq-path p q
  eq-path-m (m-inl p)   (m-inl q)   = eq-path-m p q
  eq-path-m (m-inr p)   (m-inr q)   = eq-path-m p q
  eq-path-m (m-pair₁ p) (m-pair₁ q) = eq-path-m p q
  eq-path-m (m-pair₂ p) (m-pair₂ q) = eq-path-m p q
  eq-path-m (m-mu p)    (m-mu q)    = eq-path-m p q
  eq-path-m _ _ = Bool.false

-- Membership of a path in a list of paths of the same derivation.
member : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} →
         Path D → List (Path D) → Bool
member p = any (eq-path p)

-- Completion rank: paths in a premise complete before paths in a later premise, and every path of
-- a derivation completes before the derivation itself, whose rank is the sum of its premise sizes.
-- The forward-edge lemma states that entries run strictly upward in rank, giving acyclicity.
mutual
  size : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) → ℕ
  size D = suc (psize D)

  size-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
           (D : γ , Ms ⇓s vs [ R ]) → ℕ
  size-s D = suc (psize-s D)

  size-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
           {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
           {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
           (D : Map γ s σ' v R v' R') → ℕ
  size-m D = suc (psize-m D)

  psize : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) → ℕ
  psize (⇓-var x)        = 0
  psize ⇓-unit           = 0
  psize (⇓-inl D)        = size D
  psize (⇓-inr D)        = size D
  psize (⇓-case-l D₁ D₂) = size D₁ + size D₂
  psize (⇓-case-r D₁ D₂) = size D₁ + size D₂
  psize (⇓-pair D₁ D₂)   = size D₁ + size D₂
  psize (⇓-fst D)        = size D
  psize (⇓-snd D)        = size D
  psize ⇓-lam            = 0
  psize (⇓-app D₁ D₂ D₃) = size D₁ + size D₂ + size D₃
  psize (⇓-bop D)       = size-s D
  psize (⇓-brel D)      = size-s D
  psize (⇓-roll D)       = size D
  psize (⇓-fold D₁ D₂)   = size D₁ + size-m D₂

  psize-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
            (D : γ , Ms ⇓s vs [ R ]) → ℕ
  psize-s []       = 0
  psize-s (D₁ ∷ D₂) = size D₁ + size-s D₂

  psize-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
            {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
            {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
            (D : Map γ s σ' v R v' R') → ℕ
  psize-m (m-rec D₁ D₂)  = size-m D₁ + size D₂
  psize-m m-unit          = 0
  psize-m m-base          = 0
  psize-m m-arrow         = 0
  psize-m (m-inl D)      = size-m D
  psize-m (m-inr D)      = size-m D
  psize-m (m-pair D₁ D₂) = size-m D₁ + size-m D₂
  psize-m (m-mu D)       = size-m D

mutual
  rank : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} → Path D → ℕ
  rank (ε {D = D})            = psize D
  rank (inl p)                = rank p
  rank (inr p)                = rank p
  rank (case-l₁ p)            = rank p
  rank (case-l₂ {D₁ = D₁} p)  = size D₁ + rank p
  rank (case-r₁ p)            = rank p
  rank (case-r₂ {D₁ = D₁} p)  = size D₁ + rank p
  rank (pair₁ p)              = rank p
  rank (pair₂ {D₁ = D₁} p)    = size D₁ + rank p
  rank (fst p)                = rank p
  rank (snd p)                = rank p
  rank (app₁ p)               = rank p
  rank (app₂ {D₁ = D₁} p)     = size D₁ + rank p
  rank (app₃ {D₁ = D₁} {D₂ = D₂} p) = size D₁ + size D₂ + rank p
  rank (bop p)                = rank-s p
  rank (brel p)               = rank-s p
  rank (roll p)               = rank p
  rank (fold₁ p)              = rank p
  rank (fold₂ {D₁ = D₁} p)    = size D₁ + rank-m p

  rank-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
           {D : γ , Ms ⇓s vs [ R ]} → PathS D → ℕ
  rank-s (ε {D = D})     = psize-s D
  rank-s (hd p)          = rank p
  rank-s (tl {D₁ = D₁} p) = size D₁ + rank-s p

  rank-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
           {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
           {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
           {D : Map γ s σ' v R v' R'} → PathM D → ℕ
  rank-m (ε {D = D})           = psize-m D
  rank-m (m-rec₁ p)            = rank-m p
  rank-m (m-rec₂ {D₁ = D₁} p)  = size-m D₁ + rank p
  rank-m (m-inl p)             = rank-m p
  rank-m (m-inr p)             = rank-m p
  rank-m (m-pair₁ p)           = rank-m p
  rank-m (m-pair₂ {D₁ = D₁} p) = size-m D₁ + rank-m p
  rank-m (m-mu p)              = rank-m p

is-ε-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
         {D : γ , Ms ⇓s vs [ R ]} → PathS D → Bool
is-ε-s ε = Bool.true
is-ε-s _ = Bool.false

is-ε-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
         {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
         {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
         {D : Map γ s σ' v R v' R'} → PathM D → Bool
is-ε-m ε = Bool.true
is-ε-m _ = Bool.false
