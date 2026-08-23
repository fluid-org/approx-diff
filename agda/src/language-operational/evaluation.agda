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
open import signature.interpretation using (Interpretation)
import matrix
import cmon-enriched
open import categories using (Category; HasProducts; HasTerminal)
open import Level using (0ℓ) renaming (_⊔_ to _⊔ℓ_)
open import Data.List using (List; []; _∷_)

-- Values, environments, and big-step evaluation decorated with dependency relations, threading a
-- control input: a distinguished extra input position holding the last eliminated constructor,
-- initially the run itself. A terminal rule attaches the control input to its value's control
-- positions; a constructor attaches it to the new root; an elimination points the consumed root at
-- the control input and makes that root the control input of its continuation.
module language-operational.evaluation {ℓ} (Sig : Signature ℓ)
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (ℐ : Interpretation S Sig) (ctrl-weight : Setoid.Carrier A) where

open Signature Sig
open Interpretation ℐ
open prop-setoid._⇒_ using (func)
open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.type-substitution Sig using (unfold₁; unfold₁-inst)

mutual
  data Val : type 0 → Set ℓ where
    unit  : Val unit
    const : ∀ {s} → sort-val s → Val (base s)
    inl   : ∀ {τ₁ τ₂} → Val τ₁ → Val (τ₁ [+] τ₂)
    inr   : ∀ {τ₁ τ₂} → Val τ₂ → Val (τ₁ [+] τ₂)
    pair  : ∀ {τ₁ τ₂} → Val τ₁ → Val τ₂ → Val (τ₁ [×] τ₂)
    clo   : ∀ {Γ σ τ} → Env Γ → (Γ ▸ σ) ⊢ τ → Val (σ [→] τ)
    roll  : ∀ {τ : type 1} → Val (τ [ μ τ ]) → Val (μ τ)

  data Env : ctxt → Set ℓ where
    emp : Env emp
    _·_ : ∀ {Γ τ} → Env Γ → Val τ → Env (Γ ▸ τ)

infixl 30 _·_

lookup : ∀ {Γ τ} → Γ ∋ τ → Env Γ → Val τ
lookup zero     (γ · v) = v
lookup (succ x) (γ · _) = lookup x γ

bool→val : ⊤ {0ℓ} ⊎ ⊤ {0ℓ} → Val (unit [+] unit)
bool→val (inj₁ _) = inl unit
bool→val (inj₂ _) = inr unit

private
  module M = matrix.Mat S

open Category M.cat using (_⇒_; _∘_; ∘-cong₁; ∘-cong₂; assoc; id-right) renaming (id to idm)
open HasTerminal M.terminal using (to-terminal)

open HasProducts M.products using (p₁; p₂)
open M using (⟨_,_⟩)

mutual
  width : ∀ {τ} → Val τ → ℕ
  width unit          = 1
  width (const {s} _) = sort-width s
  width (inl v)       = suc (width v)
  width (inr v)       = suc (width v)
  width (pair v u)    = suc (width v + width u)
  width (clo γ _)     = suc (width-env γ)
  width (roll v)      = width v

  width-env : ∀ {Γ} → Env Γ → ℕ
  width-env emp     = 0
  width-env (γ · v) = width-env γ + width v

ctrl-row : ∀ {n} → 1 ⇒ n
ctrl-row _ _ = ctrl-weight

-- The positions of a value that carry control dependence: what a terminal rule or an eliminator
-- writes the control input to. Every position of a first-order value, so that a value returned under an
-- unavailable constructor is wholly unavailable. Only the root of a closure: its environment
-- cells reach a result only through the body at an application, and the application attaches
-- control dependence to its whole result from the closure's root in any case. Attaching it to the
-- cells as well would make the closure's control dependence a function of what its body reads,
-- which the interpretation cannot express, since there a value of arrow type carries the fibre of
-- every possible result at once and an eliminator writes a constant fixed by the type.
ctrl-of : ∀ {τ} (v : Val τ) → 1 ⇒ width v
ctrl-of unit        = ctrl-row
ctrl-of (const _)   = ctrl-row
ctrl-of (inl v)     = ⟨ ctrl-row {1} , ctrl-of v ⟩
ctrl-of (inr v)     = ⟨ ctrl-row {1} , ctrl-of v ⟩
ctrl-of (pair v u)  = ⟨ ctrl-row {1} , ⟨ ctrl-of v , ctrl-of u ⟩ ⟩
ctrl-of (clo γ _)   = ⟨ ctrl-row {1} , M.εₘ ⟩
ctrl-of (roll v)    = ctrl-of v

width-subst : ∀ {τ τ'} (e : τ ≡ τ') (v : Val τ) → width (subst Val e v) ≡ width v
width-subst refl v = refl

size : ∀ {τ} → Val τ → ℕ
size unit       = 1
size (const _)  = 1
size (inl v)    = suc (size v)
size (inr v)    = suc (size v)
size (pair v u) = suc (size v + size u)
size (clo _ _)  = 1
size (roll v)   = suc (size v)

size-subst : ∀ {τ τ'} (e : τ ≡ τ') (v : Val τ) → size (subst Val e v) ≡ size v
size-subst refl v = refl

proj-var : ∀ {Γ τ} (x : Γ ∋ τ) (γ : Env Γ) → width-env γ ⇒ width (lookup x γ)
proj-var zero     (γ · v) = p₂ {width-env γ} {width v}
proj-var (succ x) (γ · v) = proj-var x γ ∘ p₁ {width-env γ} {width v}

brel-deps : ∀ {is} (ω : rel is) (vs : sort-vals is) (b : ⊤ {0ℓ} ⊎ ⊤ {0ℓ}) →
            bases-width is ⇒ width (bool→val b)
brel-deps ω vs (inj₁ _) = ⟨ rel-deps ω .func vs , M.εₘ ⟩
brel-deps ω vs (inj₂ _) = ⟨ rel-deps ω .func vs , M.εₘ ⟩

open M using (≈ₘ-refl; ≈ₘ-sym; ≈ₘ-trans)
open HasProducts M.products using () renaming (prod-m to _⊕_) public

ctrl-col : ∀ {m} → suc m ⇒ 1
ctrl-col {m} = p₁ {1} {m}

env-cols : ∀ {m} → suc m ⇒ m
env-cols {m} = p₂ {1} {m}

wctrl : ∀ {m n} → suc m ⇒ n
wctrl = ctrl-row ∘ ctrl-col

var-out : ∀ {Γ τ} (x : Γ ∋ τ) (γ : Env Γ) → suc (width-env γ) ⇒ width (lookup x γ)
var-out x γ = ctrl-of (lookup x γ) M.∥ proj-var x γ

built-out : ∀ {Γ} (γ : Env Γ) (n : ℕ) → suc (width-env γ) ⇒ suc n
built-out γ n = M.in₁ {1} {n} ∘ wctrl

elim-out : ∀ {Γ τ} (γ : Env Γ) (w : Val τ) → suc (width-env γ) ⇒ width w
elim-out γ w = ctrl-of w ∘ wctrl

lam-out : ∀ {Γ σ τ} (γ : Env Γ) (t : Γ ▸ σ ⊢ τ) → suc (width-env γ) ⇒ width (clo γ t)
lam-out γ t = ctrl-row {1} ⊕ M.I {width-env γ}

proj-up : ∀ {m n τ} (w : Val τ) → M.Matrix (width w) (m + n) → M.Matrix (width w) (suc (m + n))
proj-up {m} {n} w P = (P ∘ p₂ {1} {m + n}) M.+ₘ (ctrl-of w ∘ p₁ {1} {m + n})

branch-inputs : ∀ {Γ τ} (γ : Env Γ) (v : Val τ) →
                (suc (width-env γ) + suc (width v)) ⇒ suc (width-env γ + width v)
branch-inputs γ v = (ctrl-row {1} ⊕ M.in₁ {width-env γ} {width v}) M.∥ (M.I {1} ⊕ M.in₂ {width-env γ} {width v})

body-inputs : ∀ {Γ Γ' σ} (γ : Env Γ) (γ' : Env Γ') (v : Val σ) →
              ((suc (width-env γ) + suc (width-env γ')) + width v) ⇒ suc (width-env γ' + width v)
body-inputs γ γ' v =
  ((M.in₁ {1} ∘ wctrl) M.∥ (M.I {1} ⊕ M.in₁ {width-env γ'} {width v})) M.∥ (M.in₂ {1} ∘ M.in₂ {width-env γ'} {width v})

rcast : ∀ {m m' n} → m ≡ m' → M.Matrix m n → M.Matrix m' n
rcast refl R = R

ccast : ∀ {m n n'} → n ≡ n' → M.Matrix m n → M.Matrix m n'
ccast refl R = R

sub-inputs : ∀ {Γ} (γ : Env Γ) {m n} → M.Matrix m n →
              (suc (width-env γ) + n) ⇒ (suc (width-env γ) + m)
sub-inputs γ C = M.I ⊕ C

rec-inputs : ∀ {Γ τ} (γ : Env Γ) (w' : Val τ) {m} →
             ((suc (width-env γ) + m) + width w') ⇒ suc (width-env γ + width w')
rec-inputs γ w' {m} =
  ((M.I {1} ⊕ M.in₁ {width-env γ} {width w'}) ∘ p₁ {suc (width-env γ)} {m}) M.∥ (M.in₂ {1} ∘ M.in₂ {width-env γ} {width w'})

map-built-out : ∀ {Γ} (γ : Env Γ) (m n : ℕ) → (suc (width-env γ) + suc m) ⇒ suc n
map-built-out γ m n = M.in₁ {1} {n} ∘ ((wctrl ∘ p₁ {suc (width-env γ)} {suc m}) M.+ₘ (p₁ {1} {m} ∘ p₂ {suc (width-env γ)} {suc m}))

map-leaf : ∀ {Γ} (γ : Env Γ) (n : ℕ) → (suc (width-env γ) + n) ⇒ n
map-leaf γ n = p₂ {suc (width-env γ)} {n}

mutual
  data _,_⇓_[_] : ∀ {Γ τ} (γ : Env Γ) (t : Γ ⊢ τ) (v : Val τ) →
                   suc (width-env γ) ⇒ width v → Set ℓ where
    ⇓-var    : ∀ {Γ τ} {γ : Env Γ} (x : Γ ∋ τ) → γ , var x ⇓ lookup x γ [ var-out x γ ]
    ⇓-unit   : ∀ {Γ} {γ : Env Γ} → γ , unit ⇓ unit [ wctrl ]
    ⇓-inl    : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₁} {v R} →
               γ , t ⇓ v [ R ] →
               γ , inl {τ₂ = τ₂} t ⇓ inl v [ built-out γ (width v) M.+ₘ (M.in₂ {1} ∘ R) ]
    ⇓-inr    : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₂} {v R} →
               γ , t ⇓ v [ R ] →
               γ , inr {τ₁ = τ₁} t ⇓ inr v [ built-out γ (width v) M.+ₘ (M.in₂ {1} ∘ R) ]
    ⇓-case-l : ∀ {Γ τ₁ τ₂ τ} {γ : Env Γ} {s : Γ ⊢ τ₁ [+] τ₂} {t₁ : Γ ▸ τ₁ ⊢ τ} {t₂ : Γ ▸ τ₂ ⊢ τ}
               {v u R T} →
               γ , s ⇓ inl v [ R ] → γ · v , t₁ ⇓ u [ T ] →
               γ , case s t₁ t₂ ⇓ u [ T ∘ (branch-inputs γ v ∘ ⟨ M.I , R ⟩) ]
    ⇓-case-r : ∀ {Γ τ₁ τ₂ τ} {γ : Env Γ} {s : Γ ⊢ τ₁ [+] τ₂} {t₁ : Γ ▸ τ₁ ⊢ τ} {t₂ : Γ ▸ τ₂ ⊢ τ}
               {v u R T} →
               γ , s ⇓ inr v [ R ] → γ · v , t₂ ⇓ u [ T ] →
               γ , case s t₁ t₂ ⇓ u [ T ∘ (branch-inputs γ v ∘ ⟨ M.I , R ⟩) ]
    ⇓-pair   : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {s : Γ ⊢ τ₁} {t : Γ ⊢ τ₂} {v u R T} →
               γ , s ⇓ v [ R ] → γ , t ⇓ u [ T ] →
               γ , pair s t ⇓ pair v u [ built-out γ (width v + width u) M.+ₘ (M.in₂ {1} ∘ ⟨ R , T ⟩) ]
    ⇓-fst    : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₁ [×] τ₂} {v u R} →
               γ , t ⇓ pair v u [ R ] →
               γ , fst t ⇓ v [ elim-out γ v M.+ₘ (proj-up {width v} {width u} v (p₁ {width v} {width u}) ∘ R) ]
    ⇓-snd    : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₁ [×] τ₂} {v u R} →
               γ , t ⇓ pair v u [ R ] →
               γ , snd t ⇓ u [ elim-out γ u M.+ₘ (proj-up {width v} {width u} u (p₂ {width v} {width u}) ∘ R) ]
    ⇓-lam    : ∀ {Γ σ τ} {γ : Env Γ} {t : Γ ▸ σ ⊢ τ} → γ , lam t ⇓ clo γ t [ lam-out γ t ]
    ⇓-app    : ∀ {Γ Γ' σ τ} {γ : Env Γ} {γ' : Env Γ'} {s : Γ ⊢ σ [→] τ} {t t' v u R T U} →
               γ , s ⇓ clo {Γ'} γ' t' [ R ] → γ , t ⇓ v [ T ] → γ' · v , t' ⇓ u [ U ] →
               γ , app s t ⇓ u
                 [ U ∘ (body-inputs γ γ' v ∘ ⟨ ⟨ M.I , R ⟩ , T ⟩) ]
    ⇓-bop    : ∀ {Γ is o'} {γ : Env Γ} {ω : op is o'} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R} →
               γ , Ms ⇓s vs [ R ] →
               γ , bop ω Ms ⇓ const (op-fun ω .func vs) [ wctrl M.+ₘ (op-deps ω .func vs ∘ R) ]
    ⇓-brel   : ∀ {Γ is} {γ : Env Γ} {ω : rel is} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R} →
               γ , Ms ⇓s vs [ R ] →
               γ , brel ω Ms ⇓ bool→val (rel-pred ω .func vs)
                 [ wctrl M.+ₘ (brel-deps ω vs (rel-pred ω .func vs) ∘ R) ]
    ⇓-roll   : ∀ {Γ} {τ : type 1} {γ : Env Γ} {t : Γ ⊢ τ [ μ τ ]} {v R} →
               γ , t ⇓ v [ R ] → γ , roll {τ = τ} t ⇓ roll {τ} v [ R ]
    ⇓-fold   : ∀ {Γ} {τ : type 1} {σ : type 0} {γ : Env Γ} {s : Γ ▸ τ [ σ ] ⊢ σ} {t : Γ ⊢ μ τ}
               {v u R F} →
               γ , t ⇓ v [ R ] → Map γ {τ} {σ} s (var zero) v u F →
               γ , fold s t ⇓ u [ F ∘ ⟨ M.I , R ⟩ ]

  data _,_⇓s_[_] {Γ} (γ : Env Γ) : ∀ {is} → Every (λ s → Γ ⊢ base s) is →
                  sort-vals is → suc (width-env γ) ⇒ bases-width is →
                  Set ℓ where
    []  : γ , [] ⇓s tt [ M.εₘ ]
    _∷_ : ∀ {i is v vs R Rs} {M : Γ ⊢ base i} {Ms : Every (λ s → Γ ⊢ base s) is} →
          γ , M ⇓ const v [ R ] → γ , Ms ⇓s vs [ Rs ] →
          γ , (M ∷ Ms) ⇓s (v , vs) [ ⟨ R , Rs ⟩ ]

  data Map {Γ} (γ : Env Γ) {τ₀ : type 1} {σr : type 0} (s : Γ ▸ τ₀ [ σr ] ⊢ σr) :
           (σ' : type 1) (v : Val (σ' [ μ τ₀ ])) (v' : Val (σ' [ σr ])) →
           (suc (width-env γ) + width v) ⇒ width v' → Set ℓ where
    m-rec   : ∀ {w w' u F T} →
              Map γ s τ₀ w w' F → γ · w' , s ⇓ u [ T ] →
              Map γ s (var zero) (roll w) u (T ∘ (rec-inputs γ w' ∘ ⟨ M.I , F ⟩))
    m-unit  : ∀ {v} → Map γ s unit v v (map-leaf γ (width v))
    m-base  : ∀ {b v} → Map γ s (base b) v v (map-leaf γ (width v))
    m-arrow : ∀ {σ₁ σ₂ v} → Map γ s (σ₁ [→] σ₂) v v (map-leaf γ (width v))
    m-inl   : ∀ {σ₁ σ₂ v v' F} →
              Map γ s σ₁ v v' F →
              Map γ s (σ₁ [+] σ₂) (inl v) (inl v')
                  (map-built-out γ (width v) (width v') M.+ₘ
                   (M.in₂ {1} ∘ (F ∘ sub-inputs γ (p₂ {1} {width v}))))
    m-inr   : ∀ {σ₁ σ₂ v v' F} →
              Map γ s σ₂ v v' F →
              Map γ s (σ₁ [+] σ₂) (inr v) (inr v')
                  (map-built-out γ (width v) (width v') M.+ₘ
                   (M.in₂ {1} ∘ (F ∘ sub-inputs γ (p₂ {1} {width v}))))
    m-pair  : ∀ {σ₁ σ₂ v v' u u' F G} →
              Map γ s σ₁ v v' F → Map γ s σ₂ u u' G →
              Map γ s (σ₁ [×] σ₂) (pair v u) (pair v' u')
                  (map-built-out γ (width v + width u) (width v' + width u') M.+ₘ
                   (M.in₂ {1} ∘ ⟨ F ∘ sub-inputs γ (p₁ {width v} {width u} ∘ p₂ {1} {width v + width u}) ,
                                  G ∘ sub-inputs γ (p₂ {width v} {width u} ∘ p₂ {1} {width v + width u}) ⟩))
    m-mu    : ∀ {τ' : type 2} {w w' F} →
              Map γ s (unfold₁ τ') w w' F →
              Map γ s (μ τ')
                  (roll (subst Val (unfold₁-inst τ' (μ τ₀)) w))
                  (roll (subst Val (unfold₁-inst τ' σr) w'))
                  (rcast (sym (width-subst (unfold₁-inst τ' σr) w')) M.I ∘
                   (F ∘ sub-inputs γ (ccast (sym (width-subst (unfold₁-inst τ' (μ τ₀)) w)) M.I)))

infix 25 _,_⇓_[_] _,_⇓s_[_]
