{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.Fin using (zero)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Nat using (ℕ)
open import every using (Every; []; _∷_)
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
              {v u R S} {Ds : γ , s ⇓ inl v [ R ]} {D₁ : γ · v , t₁ ⇓ u [ S ]} →
              Path Ds → Path (⇓-case-l {t₂ = t₂} Ds D₁)
    case-l₂ : ∀ {Γ τ₁ τ₂ τ} {γ : Env Γ} {s : Γ ⊢ τ₁ [+] τ₂} {t₁ : Γ ▸ τ₁ ⊢ τ} {t₂ : Γ ▸ τ₂ ⊢ τ}
              {v u R S} {Ds : γ , s ⇓ inl v [ R ]} {D₁ : γ · v , t₁ ⇓ u [ S ]} →
              Path D₁ → Path (⇓-case-l {t₂ = t₂} Ds D₁)
    case-r₁ : ∀ {Γ τ₁ τ₂ τ} {γ : Env Γ} {s : Γ ⊢ τ₁ [+] τ₂} {t₁ : Γ ▸ τ₁ ⊢ τ} {t₂ : Γ ▸ τ₂ ⊢ τ}
              {v u R S} {Ds : γ , s ⇓ inr v [ R ]} {D₂ : γ · v , t₂ ⇓ u [ S ]} →
              Path Ds → Path (⇓-case-r {t₁ = t₁} Ds D₂)
    case-r₂ : ∀ {Γ τ₁ τ₂ τ} {γ : Env Γ} {s : Γ ⊢ τ₁ [+] τ₂} {t₁ : Γ ▸ τ₁ ⊢ τ} {t₂ : Γ ▸ τ₂ ⊢ τ}
              {v u R S} {Ds : γ , s ⇓ inr v [ R ]} {D₂ : γ · v , t₂ ⇓ u [ S ]} →
              Path D₂ → Path (⇓-case-r {t₁ = t₁} Ds D₂)
    pair₁   : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {s : Γ ⊢ τ₁} {t : Γ ⊢ τ₂} {v u R S}
              {Ds : γ , s ⇓ v [ R ]} {Dt : γ , t ⇓ u [ S ]} →
              Path Ds → Path (⇓-pair Ds Dt)
    pair₂   : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {s : Γ ⊢ τ₁} {t : Γ ⊢ τ₂} {v u R S}
              {Ds : γ , s ⇓ v [ R ]} {Dt : γ , t ⇓ u [ S ]} →
              Path Dt → Path (⇓-pair Ds Dt)
    fst     : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₁ [×] τ₂} {v u R} {D : γ , t ⇓ pair v u [ R ]} →
              Path D → Path (⇓-fst D)
    snd     : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₁ [×] τ₂} {v u R} {D : γ , t ⇓ pair v u [ R ]} →
              Path D → Path (⇓-snd D)
    app₁    : ∀ {Γ Γ' σ τ} {γ : Env Γ} {γ' : Env Γ'} {s : Γ ⊢ σ [→] τ} {t t' v u R S T}
              {Ds : γ , s ⇓ clo {Γ'} γ' t' [ R ]} {Dt : γ , t ⇓ v [ S ]} {Db : γ' · v , t' ⇓ u [ T ]} →
              Path Ds → Path (⇓-app Ds Dt Db)
    app₂    : ∀ {Γ Γ' σ τ} {γ : Env Γ} {γ' : Env Γ'} {s : Γ ⊢ σ [→] τ} {t t' v u R S T}
              {Ds : γ , s ⇓ clo {Γ'} γ' t' [ R ]} {Dt : γ , t ⇓ v [ S ]} {Db : γ' · v , t' ⇓ u [ T ]} →
              Path Dt → Path (⇓-app Ds Dt Db)
    app₃    : ∀ {Γ Γ' σ τ} {γ : Env Γ} {γ' : Env Γ'} {s : Γ ⊢ σ [→] τ} {t t' v u R S T}
              {Ds : γ , s ⇓ clo {Γ'} γ' t' [ R ]} {Dt : γ , t ⇓ v [ S ]} {Db : γ' · v , t' ⇓ u [ T ]} →
              Path Db → Path (⇓-app Ds Dt Db)
    bop     : ∀ {Γ is o'} {γ : Env Γ} {ω : op is o'} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
              {Ds : γ , Ms ⇓s vs [ R ]} →
              PathS Ds → Path (⇓-bop {ω = ω} Ds)
    brel    : ∀ {Γ is} {γ : Env Γ} {ω : rel is} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
              {Ds : γ , Ms ⇓s vs [ R ]} →
              PathS Ds → Path (⇓-brel {ω = ω} Ds)
    roll    : ∀ {Γ} {τ : type 1} {γ : Env Γ} {t : Γ ⊢ τ [ μ τ ]} {v : Val (τ [ μ τ ])}
              {R : width-env γ ⇒ width v} {D : γ , t ⇓ v [ R ]} →
              Path D → Path (⇓-roll {τ = τ} D)
    fold₁   : ∀ {Γ} {τ : type 1} {σ : type 0} {γ : Env Γ} {s : Γ ▸ τ [ σ ] ⊢ σ} {t : Γ ⊢ μ τ}
              {v u R R'} {Dt : γ , t ⇓ v [ R ]} {Dm : Map γ {τ} {σ} s (var zero) v R u R'} →
              Path Dt → Path (⇓-fold Dt Dm)
    fold₂   : ∀ {Γ} {τ : type 1} {σ : type 0} {γ : Env Γ} {s : Γ ▸ τ [ σ ] ⊢ σ} {t : Γ ⊢ μ τ}
              {v u R R'} {Dt : γ , t ⇓ v [ R ]} {Dm : Map γ {τ} {σ} s (var zero) v R u R'} →
              PathM Dm → Path (⇓-fold Dt Dm)

  data PathS : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs}
               {R : width-env γ ⇒ bases-width is} → γ , Ms ⇓s vs [ R ] → Set ℓ where
    ε  : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
         {Ds : γ , Ms ⇓s vs [ R ]} → PathS Ds
    hd : ∀ {Γ i is} {γ : Env Γ} {v vs R Rs} {M : Γ ⊢ base i} {Ms : Every (λ s → Γ ⊢ base s) is}
         {D : γ , M ⇓ const v [ R ]} {Ds : γ , Ms ⇓s vs [ Rs ]} →
         Path D → PathS (D ∷ Ds)
    tl : ∀ {Γ i is} {γ : Env Γ} {v vs R Rs} {M : Γ ⊢ base i} {Ms : Every (λ s → Γ ⊢ base s) is}
         {D : γ , M ⇓ const v [ R ]} {Ds : γ , Ms ⇓s vs [ Rs ]} →
         PathS Ds → PathS (D ∷ Ds)

  data PathM : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
               {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R} {v' : Val (σ' [ σr ])} {R'} →
               Map γ {τ₀} {σr} s σ' v R v' R' → Set ℓ where
    ε       : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
              {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
              {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
              {Dm : Map γ s σ' v R v' R'} → PathM Dm
    m-rec₁  : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
              {w : Val (τ₀ [ μ τ₀ ])} {R : width-env γ ⇒ width w}
              {w' : Val (τ₀ [ σr ])} {R' : width-env γ ⇒ width w'}
              {u : Val σr} {S : width-env (γ · w') ⇒ width u}
              {Dm : Map γ s τ₀ w R w' R'} {De : γ · w' , s ⇓ u [ S ]} →
              PathM Dm → PathM (m-rec Dm De)
    m-rec₂  : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
              {w : Val (τ₀ [ μ τ₀ ])} {R : width-env γ ⇒ width w}
              {w' : Val (τ₀ [ σr ])} {R' : width-env γ ⇒ width w'}
              {u : Val σr} {S : width-env (γ · w') ⇒ width u}
              {Dm : Map γ s τ₀ w R w' R'} {De : γ · w' , s ⇓ u [ S ]} →
              Path De → PathM (m-rec Dm De)
    m-inl   : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
              {σ₁ σ₂ : type 1} {v : Val (σ₁ [ μ τ₀ ])} {R : width-env γ ⇒ width v}
              {v' : Val (σ₁ [ σr ])} {R' : width-env γ ⇒ width v'}
              {Dm : Map γ s σ₁ v R v' R'} →
              PathM Dm → PathM (m-inl {σ₂ = σ₂} Dm)
    m-inr   : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
              {σ₁ σ₂ : type 1} {v : Val (σ₂ [ μ τ₀ ])} {R : width-env γ ⇒ width v}
              {v' : Val (σ₂ [ σr ])} {R' : width-env γ ⇒ width v'}
              {Dm : Map γ s σ₂ v R v' R'} →
              PathM Dm → PathM (m-inr {σ₁ = σ₁} Dm)
    m-pair₁ : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
              {σ₁ σ₂ : type 1} {v : Val (σ₁ [ μ τ₀ ])} {u : Val (σ₂ [ μ τ₀ ])}
              {R : width-env γ ⇒ width (pair v u)}
              {v' : Val (σ₁ [ σr ])} {S : width-env γ ⇒ width v'}
              {u' : Val (σ₂ [ σr ])} {T : width-env γ ⇒ width u'}
              {Dm : Map γ s σ₁ v (p₁ ∘ R) v' S} {Dm' : Map γ s σ₂ u (p₂ ∘ R) u' T} →
              PathM Dm → PathM (m-pair Dm Dm')
    m-pair₂ : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
              {σ₁ σ₂ : type 1} {v : Val (σ₁ [ μ τ₀ ])} {u : Val (σ₂ [ μ τ₀ ])}
              {R : width-env γ ⇒ width (pair v u)}
              {v' : Val (σ₁ [ σr ])} {S : width-env γ ⇒ width v'}
              {u' : Val (σ₂ [ σr ])} {T : width-env γ ⇒ width u'}
              {Dm : Map γ s σ₁ v (p₁ ∘ R) v' S} {Dm' : Map γ s σ₂ u (p₂ ∘ R) u' T} →
              PathM Dm' → PathM (m-pair Dm Dm')
    m-mu    : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
              {τ' : type 2} {w : Val (unfold₁ τ' [ μ τ₀ ])} {R : width-env γ ⇒ width w}
              {w' : Val (unfold₁ τ' [ σr ])} {R' : width-env γ ⇒ width w'}
              {Dm : Map γ s (unfold₁ τ') w R w' R'} →
              PathM Dm → PathM (m-mu {τ' = τ'} Dm)

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
               {Ds : γ , Ms ⇓s vs [ R ]} → PathS Ds → ℕ
  width-at-s (ε {is = is}) = bases-width is
  width-at-s (hd p)        = width-at p
  width-at-s (tl p)        = width-at-s p

  width-at-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
               {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
               {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
               {Dm : Map γ s σ' v R v' R'} → PathM Dm → ℕ
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
  paths (⇓-var x)        = ε ∷ []
  paths ⇓-unit           = ε ∷ []
  paths (⇓-inl D)        = ε ∷ map inl (paths D)
  paths (⇓-inr D)        = ε ∷ map inr (paths D)
  paths (⇓-case-l Ds D₁) = ε ∷ map case-l₁ (paths Ds) ++ map case-l₂ (paths D₁)
  paths (⇓-case-r Ds D₂) = ε ∷ map case-r₁ (paths Ds) ++ map case-r₂ (paths D₂)
  paths (⇓-pair Ds Dt)   = ε ∷ map pair₁ (paths Ds) ++ map pair₂ (paths Dt)
  paths (⇓-fst D)        = ε ∷ map fst (paths D)
  paths (⇓-snd D)        = ε ∷ map snd (paths D)
  paths ⇓-lam            = ε ∷ []
  paths (⇓-app Ds Dt Db) = ε ∷ map app₁ (paths Ds) ++ map app₂ (paths Dt) ++ map app₃ (paths Db)
  paths (⇓-bop Ds)       = ε ∷ map bop (paths-s Ds)
  paths (⇓-brel Ds)      = ε ∷ map brel (paths-s Ds)
  paths (⇓-roll D)       = ε ∷ map roll (paths D)
  paths (⇓-fold Dt Dm)   = ε ∷ map fold₁ (paths Dt) ++ map fold₂ (paths-m Dm)

  paths-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
            (Ds : γ , Ms ⇓s vs [ R ]) → List (PathS Ds)
  paths-s []       = ε ∷ []
  paths-s (D ∷ Ds) = ε ∷ map hd (paths D) ++ map tl (paths-s Ds)

  paths-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
            {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
            {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
            (Dm : Map γ s σ' v R v' R') → List (PathM Dm)
  paths-m (m-rec Dm De)    = ε ∷ map m-rec₁ (paths-m Dm) ++ map m-rec₂ (paths De)
  paths-m m-unit           = ε ∷ []
  paths-m m-base           = ε ∷ []
  paths-m m-arrow          = ε ∷ []
  paths-m (m-inl Dm)       = ε ∷ map m-inl (paths-m Dm)
  paths-m (m-inr Dm)       = ε ∷ map m-inr (paths-m Dm)
  paths-m (m-pair Dm Dm')  = ε ∷ map m-pair₁ (paths-m Dm) ++ map m-pair₂ (paths-m Dm')
  paths-m (m-mu Dm)        = ε ∷ map m-mu (paths-m Dm)
