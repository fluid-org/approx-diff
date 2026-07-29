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
  paths D = ε ∷ interior D

  paths-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
            (Ds : γ , Ms ⇓s vs [ R ]) → List (PathS Ds)
  paths-s Ds = ε ∷ interior-s Ds

  paths-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
            {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
            {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
            (Dm : Map γ s σ' v R v' R') → List (PathM Dm)
  paths-m Dm = ε ∷ interior-m Dm

  interior : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) → List (Path D)
  interior (⇓-var x)        = []
  interior ⇓-unit           = []
  interior (⇓-inl D)        = map inl (paths D)
  interior (⇓-inr D)        = map inr (paths D)
  interior (⇓-case-l Ds D₁) = map case-l₁ (paths Ds) ++ map case-l₂ (paths D₁)
  interior (⇓-case-r Ds D₂) = map case-r₁ (paths Ds) ++ map case-r₂ (paths D₂)
  interior (⇓-pair Ds Dt)   = map pair₁ (paths Ds) ++ map pair₂ (paths Dt)
  interior (⇓-fst D)        = map fst (paths D)
  interior (⇓-snd D)        = map snd (paths D)
  interior ⇓-lam            = []
  interior (⇓-app Ds Dt Db) = map app₁ (paths Ds) ++ map app₂ (paths Dt) ++ map app₃ (paths Db)
  interior (⇓-bop Ds)       = map bop (paths-s Ds)
  interior (⇓-brel Ds)      = map brel (paths-s Ds)
  interior (⇓-roll D)       = map roll (paths D)
  interior (⇓-fold Dt Dm)   = map fold₁ (paths Dt) ++ map fold₂ (paths-m Dm)

  interior-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
               (Ds : γ , Ms ⇓s vs [ R ]) → List (PathS Ds)
  interior-s []       = []
  interior-s (D ∷ Ds) = map hd (paths D) ++ map tl (paths-s Ds)

  interior-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
               {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
               {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
               (Dm : Map γ s σ' v R v' R') → List (PathM Dm)
  interior-m (m-rec Dm De)    = map m-rec₁ (paths-m Dm) ++ map m-rec₂ (paths De)
  interior-m m-unit           = []
  interior-m m-base           = []
  interior-m m-arrow          = []
  interior-m (m-inl Dm)       = map m-inl (paths-m Dm)
  interior-m (m-inr Dm)       = map m-inr (paths-m Dm)
  interior-m (m-pair Dm Dm')  = map m-pair₁ (paths-m Dm) ++ map m-pair₂ (paths-m Dm')
  interior-m (m-mu Dm)        = map m-mu (paths-m Dm)

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
            {Ds : γ , Ms ⇓s vs [ R ]} → PathS Ds → Bool
  fo-at-s _ = Bool.true

  fo-at-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
            {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
            {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
            {Dm : Map γ s σ' v R v' R'} → PathM Dm → Bool
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
              {Ds : γ , Ms ⇓s vs [ R ]} → PathS Ds → PathS Ds → Bool
  eq-path-s ε ε = Bool.true
  eq-path-s (hd p) (hd q) = eq-path p q
  eq-path-s (tl p) (tl q) = eq-path-s p q
  eq-path-s _ _ = Bool.false

  eq-path-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
              {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
              {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
              {Dm : Map γ s σ' v R v' R'} → PathM Dm → PathM Dm → Bool
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
           (Ds : γ , Ms ⇓s vs [ R ]) → ℕ
  size-s Ds = suc (psize-s Ds)

  size-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
           {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
           {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
           (Dm : Map γ s σ' v R v' R') → ℕ
  size-m Dm = suc (psize-m Dm)

  psize : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) → ℕ
  psize (⇓-var x)        = 0
  psize ⇓-unit           = 0
  psize (⇓-inl D)        = size D
  psize (⇓-inr D)        = size D
  psize (⇓-case-l Ds D₁) = size Ds + size D₁
  psize (⇓-case-r Ds D₂) = size Ds + size D₂
  psize (⇓-pair Ds Dt)   = size Ds + size Dt
  psize (⇓-fst D)        = size D
  psize (⇓-snd D)        = size D
  psize ⇓-lam            = 0
  psize (⇓-app Ds Dt Db) = size Ds + size Dt + size Db
  psize (⇓-bop Ds)       = size-s Ds
  psize (⇓-brel Ds)      = size-s Ds
  psize (⇓-roll D)       = size D
  psize (⇓-fold Dt Dm)   = size Dt + size-m Dm

  psize-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
            (Ds : γ , Ms ⇓s vs [ R ]) → ℕ
  psize-s []       = 0
  psize-s (D ∷ Ds) = size D + size-s Ds

  psize-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
            {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
            {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
            (Dm : Map γ s σ' v R v' R') → ℕ
  psize-m (m-rec Dm De)   = size-m Dm + size De
  psize-m m-unit          = 0
  psize-m m-base          = 0
  psize-m m-arrow         = 0
  psize-m (m-inl Dm)      = size-m Dm
  psize-m (m-inr Dm)      = size-m Dm
  psize-m (m-pair Dm Dm') = size-m Dm + size-m Dm'
  psize-m (m-mu Dm)       = size-m Dm

mutual
  rank : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} → Path D → ℕ
  rank (ε {D = D})            = psize D
  rank (inl p)                = rank p
  rank (inr p)                = rank p
  rank (case-l₁ p)            = rank p
  rank (case-l₂ {Ds = Ds} p)  = size Ds + rank p
  rank (case-r₁ p)            = rank p
  rank (case-r₂ {Ds = Ds} p)  = size Ds + rank p
  rank (pair₁ p)              = rank p
  rank (pair₂ {Ds = Ds} p)    = size Ds + rank p
  rank (fst p)                = rank p
  rank (snd p)                = rank p
  rank (app₁ p)               = rank p
  rank (app₂ {Ds = Ds} p)     = size Ds + rank p
  rank (app₃ {Ds = Ds} {Dt = Dt} p) = size Ds + size Dt + rank p
  rank (bop p)                = rank-s p
  rank (brel p)               = rank-s p
  rank (roll p)               = rank p
  rank (fold₁ p)              = rank p
  rank (fold₂ {Dt = Dt} p)    = size Dt + rank-m p

  rank-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
           {Ds : γ , Ms ⇓s vs [ R ]} → PathS Ds → ℕ
  rank-s (ε {Ds = Ds})   = psize-s Ds
  rank-s (hd p)          = rank p
  rank-s (tl {D = D} p)  = size D + rank-s p

  rank-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
           {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
           {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
           {Dm : Map γ s σ' v R v' R'} → PathM Dm → ℕ
  rank-m (ε {Dm = Dm})         = psize-m Dm
  rank-m (m-rec₁ p)            = rank-m p
  rank-m (m-rec₂ {Dm = Dm} p)  = size-m Dm + rank p
  rank-m (m-inl p)             = rank-m p
  rank-m (m-inr p)             = rank-m p
  rank-m (m-pair₁ p)           = rank-m p
  rank-m (m-pair₂ {Dm = Dm} p) = size-m Dm + rank-m p
  rank-m (m-mu p)              = rank-m p
