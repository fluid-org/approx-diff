{-# OPTIONS --prop --postfix-projections --safe #-}

import Level
open import Data.Fin using (Fin; splitAt; toℕ; _↑ˡ_; _↑ʳ_)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _<ᵇ_; _≡ᵇ_)
open import Data.Bool using () renaming (if_then_else_ to ifᵇ_then_else_)
open import Data.Nat.Properties using (+-assoc; +-identityʳ)
open import Relation.Binary.PropositionalEquality using (trans; cong)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing)
import Data.List
open import Data.List using (List; []; _∷_; _++_; length; concatMap; allFin)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import every using (Every; []; _∷_)
open import signature using (Signature)
open import primitives using (Primitives)
import matrix
import two

-- Instrumentation of evaluation derivations: the visible nodes of a derivation determine the intermediates.
module language-operational.instrument
  {ℓ} (Sig : Signature ℓ) (𝒫 : Primitives two.semiring Sig) where

open Signature Sig
open Primitives 𝒫
open prop-setoid._⇒_ using (func)
open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.evaluation Sig 𝒫
open import type-substitution Sig using (unfold₁; unfold₁-inst)

private
  module CS = CommutativeSemiring two.semiring
  module M = matrix.Mat two.semiring

open import categories using (Category; HasProducts)
open Category M.cat using (_∘_)
open HasProducts products using (p₁; p₂)

------------------------------------------------------------------------

open import language-operational.dependence-graph Sig 𝒫 public

------------------------------------------------------------------------
-- Visibility of derivation nodes.

mutual
  data Visible : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v : Val τ} {R} →
                 γ , t ⇓ v [ R ] → Set ℓ where
    vis      : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} →
               first-order τ → Visible D → Visible D
    ⇓-var    : ∀ {Γ τ} {γ : Env Γ} (x : Γ ∋ τ) → Visible (⇓-var {γ = γ} x)
    ⇓-unit   : ∀ {Γ} {γ : Env Γ} → Visible (⇓-unit {γ = γ})
    ⇓-inl    : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₁} {v R} {D : γ , t ⇓ v [ R ]} →
               Visible D → Visible (⇓-inl {τ₂ = τ₂} D)
    ⇓-inr    : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₂} {v R} {D : γ , t ⇓ v [ R ]} →
               Visible D → Visible (⇓-inr {τ₁ = τ₁} D)
    ⇓-case-l : ∀ {Γ τ₁ τ₂ τ} {γ : Env Γ} {s : Γ ⊢ τ₁ [+] τ₂} {t₁ : Γ ▸ τ₁ ⊢ τ} {t₂ : Γ ▸ τ₂ ⊢ τ}
               {v u R S} {Ds : γ , s ⇓ inl v [ R ]} {D₁ : γ · v , t₁ ⇓ u [ S ]} →
               Visible Ds → Visible D₁ → Visible (⇓-case-l {t₂ = t₂} Ds D₁)
    ⇓-case-r : ∀ {Γ τ₁ τ₂ τ} {γ : Env Γ} {s : Γ ⊢ τ₁ [+] τ₂} {t₁ : Γ ▸ τ₁ ⊢ τ} {t₂ : Γ ▸ τ₂ ⊢ τ}
               {v u R S} {Ds : γ , s ⇓ inr v [ R ]} {D₂ : γ · v , t₂ ⇓ u [ S ]} →
               Visible Ds → Visible D₂ → Visible (⇓-case-r {t₁ = t₁} Ds D₂)
    ⇓-pair   : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {s : Γ ⊢ τ₁} {t : Γ ⊢ τ₂} {v u R S}
               {D₁ : γ , s ⇓ v [ R ]} {D₂ : γ , t ⇓ u [ S ]} →
               Visible D₁ → Visible D₂ → Visible (⇓-pair D₁ D₂)
    ⇓-fst    : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₁ [×] τ₂} {v u R} {D : γ , t ⇓ pair v u [ R ]} →
               Visible D → Visible (⇓-fst D)
    ⇓-snd    : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₁ [×] τ₂} {v u R} {D : γ , t ⇓ pair v u [ R ]} →
               Visible D → Visible (⇓-snd D)
    ⇓-lam    : ∀ {Γ σ τ} {γ : Env Γ} {t : Γ ▸ σ ⊢ τ} → Visible (⇓-lam {γ = γ} {t = t})
    ⇓-app    : ∀ {Γ Γ' σ τ} {γ : Env Γ} {γ' : Env Γ'} {s : Γ ⊢ σ [→] τ} {t t' v u R S T}
               {Ds : γ , s ⇓ clo {Γ'} γ' t' [ R ]} {Dt : γ , t ⇓ v [ S ]}
               {Db : γ' · v , t' ⇓ u [ T ]} →
               Visible Ds → Visible Dt → Visible Db → Visible (⇓-app Ds Dt Db)
    ⇓-bop    : ∀ {Γ is o'} {γ : Env Γ} {ω : op is o'} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
               {Es : γ , Ms ⇓s vs [ R ]} → VisibleS Es → Visible (⇓-bop {ω = ω} Es)
    ⇓-brel   : ∀ {Γ is} {γ : Env Γ} {ω : rel is} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
               {Es : γ , Ms ⇓s vs [ R ]} → VisibleS Es → Visible (⇓-brel {ω = ω} Es)
    ⇓-roll   : ∀ {Γ} {τ : type 1} {γ : Env Γ} {t : Γ ⊢ τ [ μ τ ]} {v R} {D : γ , t ⇓ v [ R ]} →
               Visible D → Visible (⇓-roll {τ = τ} D)
    ⇓-fold   : ∀ {Γ} {τ : type 1} {σ : type 0} {γ : Env Γ} {s : Γ ▸ τ [ σ ] ⊢ σ} {t : Γ ⊢ μ τ}
               {v u R R'} {Dt : γ , t ⇓ v [ R ]} {Dm : Map γ {τ} {σ} s (var Fin.zero) v R u R'} →
               Visible Dt → VisibleM Dm → Visible (⇓-fold Dt Dm)

  data VisibleS {Γ} {γ : Env Γ} : ∀ {is} {Ms : Every (λ s → Γ ⊢ base s) is} {vs Rs} →
                γ , Ms ⇓s vs [ Rs ] → Set ℓ where
    []  : VisibleS []
    _∷_ : ∀ {i is v vs R Rs} {M : Γ ⊢ base i} {Ms : Every (λ s → Γ ⊢ base s) is}
          {E : γ , M ⇓ const v [ R ]} {Es : γ , Ms ⇓s vs [ Rs ]} →
          Visible E → VisibleS Es → VisibleS (E ∷ Es)

  data VisibleM {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr} :
               ∀ {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : M.Matrix (width v) (width-env γ)}
               {v' : Val (σ' [ σr ])} {R' : M.Matrix (width v') (width-env γ)} →
               Map γ s σ' v R v' R' → Set ℓ where
    m-rec   : ∀ {w w' u R R' S} {Dm : Map γ s τ₀ w R w' R'} {Db : γ · w' , s ⇓ u [ S ]} →
              VisibleM Dm → Visible Db → VisibleM (m-rec Dm Db)
    m-unit  : ∀ {v R} → VisibleM (m-unit {v = v} {R = R})
    m-base  : ∀ {b v R} → VisibleM (m-base {b = b} {v = v} {R = R})
    m-arrow : ∀ {σ₁ σ₂ v R} → VisibleM (m-arrow {σ₁ = σ₁} {σ₂ = σ₂} {v = v} {R = R})
    m-inl   : ∀ {σ₁ σ₂ v v' R R'} {Dm : Map γ s σ₁ v R v' R'} →
              VisibleM Dm → VisibleM (m-inl {σ₂ = σ₂} Dm)
    m-inr   : ∀ {σ₁ σ₂ v v' R R'} {Dm : Map γ s σ₂ v R v' R'} →
              VisibleM Dm → VisibleM (m-inr {σ₁ = σ₁} Dm)
    m-pair  : ∀ {σ₁ σ₂ v v' u u' R S T}
              {Dm₁ : Map γ s σ₁ v (p₁ ∘ R) v' S} {Dm₂ : Map γ s σ₂ u (p₂ ∘ R) u' T} →
              VisibleM Dm₁ → VisibleM Dm₂ → VisibleM (m-pair Dm₁ Dm₂)
    m-mu    : ∀ {τ' : type 2} {w w' R R'} {Dm : Map γ s (unfold₁ τ') w R w' R'} →
              VisibleM Dm → VisibleM (m-mu {τ' = τ'} Dm)

------------------------------------------------------------------------
-- Paths addressing the nodes of a derivation, as plain data so that a path can be checked against a
-- derivation without normalising it.

data Dir : Set where
  inl inr roll fst snd pair₁ pair₂ case₁ case₂ app₁ app₂ app₃ bop brel fold₁ fold₂ : Dir
  hd tl rec₁ rec₂ m-inj m-pair₁ m-pair₂ m-mu : Dir

Path : Set
Path = List Dir

------------------------------------------------------------------------
-- The overlay with nothing visible.

mutual
  visible-none : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) → Visible D
  visible-none (⇓-var x)          = ⇓-var x
  visible-none ⇓-unit             = ⇓-unit
  visible-none ⇓-lam              = ⇓-lam
  visible-none (⇓-inl D)          = ⇓-inl (visible-none D)
  visible-none (⇓-inr D)          = ⇓-inr (visible-none D)
  visible-none (⇓-roll D)         = ⇓-roll (visible-none D)
  visible-none (⇓-fst D)          = ⇓-fst (visible-none D)
  visible-none (⇓-snd D)          = ⇓-snd (visible-none D)
  visible-none (⇓-pair D₁ D₂)     = ⇓-pair (visible-none D₁) (visible-none D₂)
  visible-none (⇓-case-l Ds D₁)   = ⇓-case-l (visible-none Ds) (visible-none D₁)
  visible-none (⇓-case-r Ds D₂)   = ⇓-case-r (visible-none Ds) (visible-none D₂)
  visible-none (⇓-app Ds Dt Db)   = ⇓-app (visible-none Ds) (visible-none Dt) (visible-none Db)
  visible-none (⇓-bop Es)         = ⇓-bop (visible-none-s Es)
  visible-none (⇓-brel Es)        = ⇓-brel (visible-none-s Es)
  visible-none (⇓-fold Dt Dm)     = ⇓-fold (visible-none Dt) (visible-none-m Dm)

  visible-none-s : ∀ {Γ is} {Ms : Every (λ s → Γ ⊢ base s) is} {γ : Env Γ} {vs Rs}
                (Ds : γ , Ms ⇓s vs [ Rs ]) → VisibleS Ds
  visible-none-s []       = []
  visible-none-s (E ∷ Es) = visible-none E ∷ visible-none-s Es

  visible-none-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
                {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : M.Matrix (width v) (width-env γ)}
                {v' : Val (σ' [ σr ])} {R' : M.Matrix (width v') (width-env γ)}
                (Dm : Map γ s σ' v R v' R') → VisibleM Dm
  visible-none-m (m-rec Dm Db)    = m-rec (visible-none-m Dm) (visible-none Db)
  visible-none-m m-unit           = m-unit
  visible-none-m m-base           = m-base
  visible-none-m m-arrow          = m-arrow
  visible-none-m (m-inl Dm)       = m-inl (visible-none-m Dm)
  visible-none-m (m-inr Dm)       = m-inr (visible-none-m Dm)
  visible-none-m (m-pair Dm₁ Dm₂) = m-pair (visible-none-m Dm₁) (visible-none-m Dm₂)
  visible-none-m (m-mu Dm)        = m-mu (visible-none-m Dm)

------------------------------------------------------------------------
-- The overlay with every first-order node visible.

private
  first-order? : ∀ {Δ} (τ : type Δ) → Maybe (first-order τ)
  first-order? (var i)   = just (var i)
  first-order? unit      = just unit
  first-order? (base s)  = just (base s)
  first-order? (σ [+] τ) with first-order? σ | first-order? τ
  ... | just a  | just b  = just (a [+] b)
  ... | _       | _       = nothing
  first-order? (σ [×] τ) with first-order? σ | first-order? τ
  ... | just a  | just b  = just (a [×] b)
  ... | _       | _       = nothing
  first-order? (σ [→] τ) = nothing
  first-order? (μ τ) with first-order? τ
  ... | just a  = just (μ a)
  ... | nothing = nothing

mutual
  visible-all : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) → Visible D
  visible-all {τ = τ} D with first-order? τ
  ... | just fo = vis fo (visible-all′ D)
  ... | nothing = visible-all′ D

  private
    visible-all′ : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) → Visible D
    visible-all′ (⇓-var x)        = ⇓-var x
    visible-all′ ⇓-unit           = ⇓-unit
    visible-all′ ⇓-lam            = ⇓-lam
    visible-all′ (⇓-inl D)        = ⇓-inl (visible-all D)
    visible-all′ (⇓-inr D)        = ⇓-inr (visible-all D)
    visible-all′ (⇓-roll D)       = ⇓-roll (visible-all D)
    visible-all′ (⇓-fst D)        = ⇓-fst (visible-all D)
    visible-all′ (⇓-snd D)        = ⇓-snd (visible-all D)
    visible-all′ (⇓-pair D₁ D₂)   = ⇓-pair (visible-all D₁) (visible-all D₂)
    visible-all′ (⇓-case-l Ds D₁) = ⇓-case-l (visible-all Ds) (visible-all D₁)
    visible-all′ (⇓-case-r Ds D₂) = ⇓-case-r (visible-all Ds) (visible-all D₂)
    visible-all′ (⇓-app Ds Dt Db) = ⇓-app (visible-all Ds) (visible-all Dt) (visible-all Db)
    visible-all′ (⇓-bop Es)       = ⇓-bop (visible-all-s Es)
    visible-all′ (⇓-brel Es)      = ⇓-brel (visible-all-s Es)
    visible-all′ (⇓-fold Dt Dm)   = ⇓-fold (visible-all Dt) (visible-all-m Dm)

    visible-all-s : ∀ {Γ is} {Ms : Every (λ s → Γ ⊢ base s) is} {γ : Env Γ} {vs Rs}
                    (Ds : γ , Ms ⇓s vs [ Rs ]) → VisibleS Ds
    visible-all-s []       = []
    visible-all-s (E ∷ Es) = visible-all E ∷ visible-all-s Es

    visible-all-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
                    {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : M.Matrix (width v) (width-env γ)}
                    {v' : Val (σ' [ σr ])} {R' : M.Matrix (width v') (width-env γ)}
                    (Dm : Map γ s σ' v R v' R') → VisibleM Dm
    visible-all-m (m-rec Dm Db)    = m-rec (visible-all-m Dm) (visible-all Db)
    visible-all-m m-unit           = m-unit
    visible-all-m m-base           = m-base
    visible-all-m m-arrow          = m-arrow
    visible-all-m (m-inl Dm)       = m-inl (visible-all-m Dm)
    visible-all-m (m-inr Dm)       = m-inr (visible-all-m Dm)
    visible-all-m (m-pair Dm₁ Dm₂) = m-pair (visible-all-m Dm₁) (visible-all-m Dm₂)
    visible-all-m (m-mu Dm)        = m-mu (visible-all-m Dm)

------------------------------------------------------------------------
-- Reveal or hide the node at a path. Revealing is idempotent and hiding strips every wrapper at the node;
-- a path step that does not match the derivation, or revealing a higher-order node, leaves the overlay
-- unchanged.

private
  reveal-here : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} →
              Visible D → Visible D
  reveal-here (vis f m) = vis f m
  reveal-here {τ = τ} m with first-order? τ
  ... | just fo = vis fo m
  ... | nothing = m

  hide-here : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} →
                Visible D → Visible D
  hide-here (vis f m) = hide-here m
  hide-here m = m

reveal-at :
  ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} →
  Path → Visible D → Visible D
reveal-at-s :
  ∀ {Γ is} {Ms : Every (λ s → Γ ⊢ base s) is} {γ : Env Γ} {vs Rs}
  {Ds : γ , Ms ⇓s vs [ Rs ]} →
  Path → VisibleS Ds → VisibleS Ds
reveal-at-m :
  ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
  {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : M.Matrix (width v) (width-env γ)}
  {v' : Val (σ' [ σr ])} {R' : M.Matrix (width v') (width-env γ)}
  {Dm : Map γ s σ' v R v' R'} →
  Path → VisibleM Dm → VisibleM Dm

reveal-at [] m = reveal-here m
reveal-at (d ∷ p) (vis f m)                 = vis f (reveal-at (d ∷ p) m)
reveal-at (inl ∷ p) (⇓-inl mD)              = ⇓-inl (reveal-at p mD)
reveal-at (inr ∷ p) (⇓-inr mD)              = ⇓-inr (reveal-at p mD)
reveal-at (roll ∷ p) (⇓-roll mD)            = ⇓-roll (reveal-at p mD)
reveal-at (fst ∷ p) (⇓-fst mD)              = ⇓-fst (reveal-at p mD)
reveal-at (snd ∷ p) (⇓-snd mD)              = ⇓-snd (reveal-at p mD)
reveal-at (pair₁ ∷ p) (⇓-pair mD₁ mD₂)      = ⇓-pair (reveal-at p mD₁) mD₂
reveal-at (pair₂ ∷ p) (⇓-pair mD₁ mD₂)      = ⇓-pair mD₁ (reveal-at p mD₂)
reveal-at (case₁ ∷ p) (⇓-case-l mDs mD₁)    = ⇓-case-l (reveal-at p mDs) mD₁
reveal-at (case₁ ∷ p) (⇓-case-r mDs mD₂)    = ⇓-case-r (reveal-at p mDs) mD₂
reveal-at (case₂ ∷ p) (⇓-case-l mDs mD₁)    = ⇓-case-l mDs (reveal-at p mD₁)
reveal-at (case₂ ∷ p) (⇓-case-r mDs mD₂)    = ⇓-case-r mDs (reveal-at p mD₂)
reveal-at (app₁ ∷ p) (⇓-app mDs mDt mDb)    = ⇓-app (reveal-at p mDs) mDt mDb
reveal-at (app₂ ∷ p) (⇓-app mDs mDt mDb)    = ⇓-app mDs (reveal-at p mDt) mDb
reveal-at (app₃ ∷ p) (⇓-app mDs mDt mDb)    = ⇓-app mDs mDt (reveal-at p mDb)
reveal-at (bop ∷ p) (⇓-bop mEs)             = ⇓-bop (reveal-at-s p mEs)
reveal-at (brel ∷ p) (⇓-brel mEs)           = ⇓-brel (reveal-at-s p mEs)
reveal-at (fold₁ ∷ p) (⇓-fold mDt mDm)      = ⇓-fold (reveal-at p mDt) mDm
reveal-at (fold₂ ∷ p) (⇓-fold mDt mDm)      = ⇓-fold mDt (reveal-at-m p mDm)
reveal-at (_ ∷ _) m = m

reveal-at-s (hd ∷ p) (mE ∷ mEs) = reveal-at p mE ∷ mEs
reveal-at-s (tl ∷ p) (mE ∷ mEs) = mE ∷ reveal-at-s p mEs
reveal-at-s _ mEs = mEs

reveal-at-m (rec₁ ∷ p) (m-rec mDm mDb)      = m-rec (reveal-at-m p mDm) mDb
reveal-at-m (rec₂ ∷ p) (m-rec mDm mDb)      = m-rec mDm (reveal-at p mDb)
reveal-at-m (m-inj ∷ p) (m-inl mDm)         = m-inl (reveal-at-m p mDm)
reveal-at-m (m-inj ∷ p) (m-inr mDm)         = m-inr (reveal-at-m p mDm)
reveal-at-m (m-pair₁ ∷ p) (m-pair mDm₁ mDm₂) = m-pair (reveal-at-m p mDm₁) mDm₂
reveal-at-m (m-pair₂ ∷ p) (m-pair mDm₁ mDm₂) = m-pair mDm₁ (reveal-at-m p mDm₂)
reveal-at-m (m-mu ∷ p) (m-mu mDm)           = m-mu (reveal-at-m p mDm)
reveal-at-m _ mDm = mDm

hide-at :
  ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} →
  Path → Visible D → Visible D
hide-at-s :
  ∀ {Γ is} {Ms : Every (λ s → Γ ⊢ base s) is} {γ : Env Γ} {vs Rs}
  {Ds : γ , Ms ⇓s vs [ Rs ]} →
  Path → VisibleS Ds → VisibleS Ds
hide-at-m :
  ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
  {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : M.Matrix (width v) (width-env γ)}
  {v' : Val (σ' [ σr ])} {R' : M.Matrix (width v') (width-env γ)}
  {Dm : Map γ s σ' v R v' R'} →
  Path → VisibleM Dm → VisibleM Dm

hide-at [] m = hide-here m
hide-at (d ∷ p) (vis f m)                 = vis f (hide-at (d ∷ p) m)
hide-at (inl ∷ p) (⇓-inl mD)              = ⇓-inl (hide-at p mD)
hide-at (inr ∷ p) (⇓-inr mD)              = ⇓-inr (hide-at p mD)
hide-at (roll ∷ p) (⇓-roll mD)            = ⇓-roll (hide-at p mD)
hide-at (fst ∷ p) (⇓-fst mD)              = ⇓-fst (hide-at p mD)
hide-at (snd ∷ p) (⇓-snd mD)              = ⇓-snd (hide-at p mD)
hide-at (pair₁ ∷ p) (⇓-pair mD₁ mD₂)      = ⇓-pair (hide-at p mD₁) mD₂
hide-at (pair₂ ∷ p) (⇓-pair mD₁ mD₂)      = ⇓-pair mD₁ (hide-at p mD₂)
hide-at (case₁ ∷ p) (⇓-case-l mDs mD₁)    = ⇓-case-l (hide-at p mDs) mD₁
hide-at (case₁ ∷ p) (⇓-case-r mDs mD₂)    = ⇓-case-r (hide-at p mDs) mD₂
hide-at (case₂ ∷ p) (⇓-case-l mDs mD₁)    = ⇓-case-l mDs (hide-at p mD₁)
hide-at (case₂ ∷ p) (⇓-case-r mDs mD₂)    = ⇓-case-r mDs (hide-at p mD₂)
hide-at (app₁ ∷ p) (⇓-app mDs mDt mDb)    = ⇓-app (hide-at p mDs) mDt mDb
hide-at (app₂ ∷ p) (⇓-app mDs mDt mDb)    = ⇓-app mDs (hide-at p mDt) mDb
hide-at (app₃ ∷ p) (⇓-app mDs mDt mDb)    = ⇓-app mDs mDt (hide-at p mDb)
hide-at (bop ∷ p) (⇓-bop mEs)             = ⇓-bop (hide-at-s p mEs)
hide-at (brel ∷ p) (⇓-brel mEs)           = ⇓-brel (hide-at-s p mEs)
hide-at (fold₁ ∷ p) (⇓-fold mDt mDm)      = ⇓-fold (hide-at p mDt) mDm
hide-at (fold₂ ∷ p) (⇓-fold mDt mDm)      = ⇓-fold mDt (hide-at-m p mDm)
hide-at (_ ∷ _) m = m

hide-at-s (hd ∷ p) (mE ∷ mEs) = hide-at p mE ∷ mEs
hide-at-s (tl ∷ p) (mE ∷ mEs) = mE ∷ hide-at-s p mEs
hide-at-s _ mEs = mEs

hide-at-m (rec₁ ∷ p) (m-rec mDm mDb)      = m-rec (hide-at-m p mDm) mDb
hide-at-m (rec₂ ∷ p) (m-rec mDm mDb)      = m-rec mDm (hide-at p mDb)
hide-at-m (m-inj ∷ p) (m-inl mDm)         = m-inl (hide-at-m p mDm)
hide-at-m (m-inj ∷ p) (m-inr mDm)         = m-inr (hide-at-m p mDm)
hide-at-m (m-pair₁ ∷ p) (m-pair mDm₁ mDm₂) = m-pair (hide-at-m p mDm₁) mDm₂
hide-at-m (m-pair₂ ∷ p) (m-pair mDm₁ mDm₂) = m-pair mDm₁ (hide-at-m p mDm₂)
hide-at-m (m-mu ∷ p) (m-mu mDm)           = m-mu (hide-at-m p mDm)
hide-at-m _ mDm = mDm

------------------------------------------------------------------------
-- Instrumentation.

Res : (g : ℕ) → ℕ → Set ℓ
Res g t = Σ (Graph g) λ G → Dep g G t

Out : (g : ℕ) (G : Graph g) → ℕ → Set ℓ
Out g G t = Σ (Graph g) λ G′ → (G′ ⊒ G) × Dep g G′ t

instrument-d :
  ∀ {Γ τ} {t : Γ ⊢ τ} {γ : Env Γ} {v R} {D : γ , t ⇓ v [ R ]} →
  Visible D → Res (width-env γ) (width v)
instrument-ds :
  ∀ {Γ is} {Ms : Every (λ s → Γ ⊢ base s) is} {γ : Env Γ} {vs Rs}
  {Ds : γ , Ms ⇓s vs [ Rs ]} →
  VisibleS Ds → Res (width-env γ) (bases-width is)
instrument-dm :
  ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
  {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : M.Matrix (width v) (width-env γ)}
  {v' : Val (σ' [ σr ])} {R' : M.Matrix (width v') (width-env γ)}
  {Dm : Map γ s σ' v R v' R'} →
  VisibleM Dm → (G : Graph (width-env γ)) → Dep (width-env γ) G (width v) →
  Out (width-env γ) G (width v')

instrument-d {v = v} (vis fo mD) with instrument-d mD
... | G , R = snoc G v R , constDep G M.εₘ ∣ M.I
instrument-d {γ = γ} (⇓-var x) = ∅ , ⟨ proj-var x γ ∣⟩
instrument-d ⇓-unit = ∅ , ⟨ M.εₘ ∣⟩
instrument-d ⇓-lam = ∅ , ⟨ M.I ∣⟩
instrument-d (⇓-inl mD) = instrument-d mD
instrument-d (⇓-inr mD) = instrument-d mD
instrument-d (⇓-roll mD) = instrument-d mD
instrument-d (⇓-fst mD) with instrument-d mD
... | G , R = G , mapCod M.p₁ R
instrument-d (⇓-snd mD) with instrument-d mD
... | G , R = G , mapCod M.p₂ R
instrument-d (⇓-pair mD₁ mD₂) with instrument-d mD₁
... | G , R
  with instrument-d mD₂
... | H , S = G ++G H , R ⊗ S
instrument-d (⇓-case-l mDs mD₁) with instrument-d mDs
... | G , R
  with instrument-d mD₁
... | H , Sb =
  let E = pairDep (constDep G M.I) R
      (G′ , _) = substGraph E H
  in G′ , substDep E Sb
instrument-d (⇓-case-r mDs mD₂) with instrument-d mDs
... | G , R
  with instrument-d mD₂
... | H , Sb =
  let E = pairDep (constDep G M.I) R
      (G′ , _) = substGraph E H
  in G′ , substDep E Sb
instrument-d (⇓-app mDs mDt mDb) with instrument-d mDs
... | G , R
  with instrument-d mDt
... | H , Sa
  with instrument-d mDb
... | K , Tb =
  let E = R ⊗ Sa
      (G′ , _) = substGraph E K
  in G′ , substDep E Tb
instrument-d (⇓-bop {ω = ω} {vs = vs} mEs) with instrument-ds mEs
... | G , Rs = G , mapCod (op-deps ω .func vs) Rs
instrument-d {γ = γ} (⇓-brel {ω = ω} {vs = vs} mEs) with instrument-ds mEs
... | G , _ = G , constDep G (brel-mat γ (rel-pred ω .func vs))
instrument-d (⇓-fold mDt mDm) with instrument-d mDt
... | G , R
  with instrument-dm mDm G R
... | G′ , _ , R′ = G′ , R′

instrument-ds [] = ∅ , ⟨ M.εₘ ∣⟩
instrument-ds (mE ∷ mEs) with instrument-d mE
... | G , R
  with instrument-ds mEs
... | H , Rs = G ++G H , R ⊗ Rs

instrument-dm m-unit G Rin = G , done , Rin
instrument-dm m-base G Rin = G , done , Rin
instrument-dm m-arrow G Rin = G , done , Rin
instrument-dm (m-inl mDm) G Rin = instrument-dm mDm G Rin
instrument-dm (m-inr mDm) G Rin = instrument-dm mDm G Rin
instrument-dm (m-pair mDm₁ mDm₂) G Rin
  with instrument-dm mDm₁ G (mapCod M.p₁ Rin)
... | G₁ , e₁ , S₁
  with instrument-dm mDm₂ G₁ (widen e₁ (mapCod M.p₂ Rin))
... | G₂ , e₂ , S₂ = G₂ , ⊒-trans e₂ e₁ , pairDep (widen e₂ S₁) S₂
instrument-dm (m-rec mDm mDb) G Rin
  with instrument-dm mDm G Rin
... | G₁ , e₁ , R₁
  with instrument-d mDb
... | H , Sb =
  let E = pairDep (constDep G₁ M.I) R₁
      (G′ , e′) = substGraph E H
  in G′ , ⊒-trans e′ e₁ , substDep E Sb
instrument-dm {τ₀ = τ₀} {σr = σr} (m-mu {τ' = τ'} {w = w} {w' = w'} mDm) G Rin
  with instrument-dm mDm G (dcast (width-subst (unfold₁-inst τ' (μ τ₀)) w) Rin)
... | G′ , e , S′ = G′ , e , dcast (sym (width-subst (unfold₁-inst τ' σr) w')) S′
