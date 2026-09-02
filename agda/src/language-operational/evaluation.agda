{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (0ℓ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import Data.List.Relation.Unary.All using ([]; _∷_) renaming (All to Every)
open import signature using (Signature)
open import signature.interpretation using (Interpretation)
open import categories using (Category)
open import cmon-enriched using (CMonEnriched; Biproduct)
import matrix-embedding
import semimodule
import sd-semimodule-primitives
open import Data.List using ([]; _∷_)

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
open prop-setoid._⇒_ using (func; func-resp-≈)
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

infix 4 _≈v_

data _≈v_ : ∀ {τ} → Val τ → Val τ → Prop ℓ where
  unit  : unit ≈v unit
  const : ∀ {s} {a b : sort-val s} → Setoid._≈_ (sort-index s) a b → const a ≈v const b
  inl   : ∀ {τ₁ τ₂} {v v' : Val τ₁} → v ≈v v' → inl {τ₂ = τ₂} v ≈v inl v'
  inr   : ∀ {τ₁ τ₂} {v v' : Val τ₂} → v ≈v v' → inr {τ₁ = τ₁} v ≈v inr v'
  pair  : ∀ {τ₁ τ₂} {v v' : Val τ₁} {u u' : Val τ₂} → v ≈v v' → u ≈v u' → pair v u ≈v pair v' u'
  roll  : ∀ {τ : type 1} {v v' : Val (τ [ μ τ ])} → v ≈v v' → roll {τ} v ≈v roll {τ} v'

lookup : ∀ {Γ τ} → Γ ∋ τ → Env Γ → Val τ
lookup zero     (γ · v) = v
lookup (succ x) (γ · _) = lookup x γ

bool→val : ⊤ {0ℓ} ⊎ ⊤ {0ℓ} → Val (unit [+] unit)
bool→val (inj₁ _) = inl unit
bool→val (inj₂ _) = inr unit

private
  module CS = CommutativeSemiring S
  module ME = matrix-embedding S
  module SemiMod = semimodule S
  module SDP = sd-semimodule-primitives S

open ME using (𝔽)
open SemiMod._⇒_ using (*→*; preserve-ze; preserve-+; preserve-·)
open Category SemiMod.cat using (_⇒_; _∘_; ≡-to-⇒)
open CMonEnriched SemiMod.cmon-enriched using (_+m_)
open SDP.interp-deps Sig ℐ using (op-dep; rel-dep)

I : ∀ {n} → 𝔽 n ⇒ 𝔽 n
I {n} = SemiMod.id (𝔽 n)

εₘ : ∀ {m n} → 𝔽 m ⇒ 𝔽 n
εₘ {m} {n} = CMonEnriched.εm SemiMod.cmon-enriched {𝔽 m} {𝔽 n}

p₁ : ∀ {m n} → 𝔽 (m + n) ⇒ 𝔽 m
p₁ {m} {n} = Biproduct.p₁ (ME.𝔽-biproduct m n)

p₂ : ∀ {m n} → 𝔽 (m + n) ⇒ 𝔽 n
p₂ {m} {n} = Biproduct.p₂ (ME.𝔽-biproduct m n)

in₁ : ∀ {m n} → 𝔽 m ⇒ 𝔽 (m + n)
in₁ {m} {n} = Biproduct.in₁ (ME.𝔽-biproduct m n)

in₂ : ∀ {m n} → 𝔽 n ⇒ 𝔽 (m + n)
in₂ {m} {n} = Biproduct.in₂ (ME.𝔽-biproduct m n)

⟨_,_⟩ : ∀ {k m n} → 𝔽 k ⇒ 𝔽 m → 𝔽 k ⇒ 𝔽 n → 𝔽 k ⇒ 𝔽 (m + n)
⟨_,_⟩ {k} {m} {n} = Biproduct.pair (ME.𝔽-biproduct m n)

_∥_ : ∀ {m n k} → 𝔽 m ⇒ 𝔽 k → 𝔽 n ⇒ 𝔽 k → 𝔽 (m + n) ⇒ 𝔽 k
_∥_ {m} {n} {k} = Biproduct.copair (ME.𝔽-biproduct m n)

_⊕_ : ∀ {m m' n n'} → 𝔽 m ⇒ 𝔽 m' → 𝔽 n ⇒ 𝔽 n' → 𝔽 (m + n) ⇒ 𝔽 (m' + n')
f ⊕ g = ⟨ f ∘ p₁ , g ∘ p₂ ⟩

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

-- Scaling by control weight, on control channel.
ctrl-scale : 𝔽 1 ⇒ 𝔽 1
ctrl-scale .*→* .func v i = v i CS.· ctrl-weight
ctrl-scale .*→* .func-resp-≈ e i = CS.·-cong (e i) CS.refl
ctrl-scale .preserve-ze i = CS.ε-annihilₗ
ctrl-scale .preserve-+ i = CS.·-+-distribᵣ
ctrl-scale .preserve-· i = CS.·-assoc

-- Everywhere-one column: unit section at width without value structure.
ones : ∀ {n} → 𝔽 1 ⇒ 𝔽 n
ones {zero}  = εₘ
ones {suc n} = ⟨ I {1} , ones {n} ⟩

-- The positions of a value that carry control dependence: what a terminal rule or an eliminator
-- writes the control input to, scaled by the control weight at use sites. Every position of a
-- first-order value, so that a value returned under an unavailable constructor is wholly
-- unavailable. Only the root of a closure: its environment cells reach a result only through the
-- body at an application, and the application attaches control dependence to its whole result from
-- the closure's root in any case. Attaching it to the cells as well would make the closure's
-- control dependence a function of what its body reads, which the interpretation cannot express,
-- since there a value of arrow type carries the fibre of every possible result at once and an
-- eliminator writes a constant fixed by the type.
unit-section : ∀ {τ} (v : Val τ) → 𝔽 1 ⇒ 𝔽 (width v)
unit-section unit          = I {1}
unit-section (const {s} _) = ones {sort-width s}
unit-section (inl v)       = ⟨ I {1} , unit-section v ⟩
unit-section (inr v)       = ⟨ I {1} , unit-section v ⟩
unit-section (pair v u)    = ⟨ I {1} , ⟨ unit-section v , unit-section u ⟩ ⟩
unit-section (clo γ _)     = ⟨ I {1} , εₘ ⟩
unit-section (roll v)      = unit-section v

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

proj-var : ∀ {Γ τ} (x : Γ ∋ τ) (γ : Env Γ) → 𝔽 (width-env γ) ⇒ 𝔽 (width (lookup x γ))
proj-var zero     (γ · v) = p₂ {width-env γ} {width v}
proj-var (succ x) (γ · v) = proj-var x γ ∘ p₁ {width-env γ} {width v}

brel-deps : ∀ {is} (ω : rel is) (vs : sort-vals is) (b : ⊤ {0ℓ} ⊎ ⊤ {0ℓ}) →
            𝔽 (bases-width is) ⇒ 𝔽 (width (bool→val b))
brel-deps ω vs (inj₁ _) = ⟨ rel-dep ω vs , εₘ ⟩
brel-deps ω vs (inj₂ _) = ⟨ rel-dep ω vs , εₘ ⟩

ctrl-col : ∀ {m} → 𝔽 (suc m) ⇒ 𝔽 1
ctrl-col {m} = p₁ {1} {m}

wctrl : ∀ {m n} → 𝔽 (suc m) ⇒ 𝔽 n
wctrl = ones ∘ (ctrl-scale ∘ ctrl-col)

var-out : ∀ {Γ τ} (x : Γ ∋ τ) (γ : Env Γ) → 𝔽 (suc (width-env γ)) ⇒ 𝔽 (width (lookup x γ))
var-out x γ = (unit-section (lookup x γ) ∘ ctrl-scale) ∥ proj-var x γ

built-out : ∀ {Γ} (γ : Env Γ) (n : ℕ) → 𝔽 (suc (width-env γ)) ⇒ 𝔽 (suc n)
built-out γ n = in₁ {1} {n} ∘ wctrl

elim-out : ∀ {Γ τ} (γ : Env Γ) (w : Val τ) → 𝔽 (suc (width-env γ)) ⇒ 𝔽 (width w)
elim-out γ w = unit-section w ∘ wctrl

lam-out : ∀ {Γ σ τ} (γ : Env Γ) (t : Γ ▸ σ ⊢ τ) → 𝔽 (suc (width-env γ)) ⇒ 𝔽 (width (clo γ t))
lam-out γ t = ctrl-scale ⊕ I {width-env γ}

proj-up : ∀ {m n τ} (w : Val τ) → 𝔽 (m + n) ⇒ 𝔽 (width w) → 𝔽 (suc (m + n)) ⇒ 𝔽 (width w)
proj-up {m} {n} w P = (P ∘ p₂ {1} {m + n}) +m ((unit-section w ∘ ctrl-scale) ∘ p₁ {1} {m + n})

branch-inputs : ∀ {Γ τ} (γ : Env Γ) (v : Val τ) →
                𝔽 (suc (width-env γ) + suc (width v)) ⇒ 𝔽 (suc (width-env γ + width v))
branch-inputs γ v = (ctrl-scale ⊕ in₁ {width-env γ} {width v}) ∥ (I {1} ⊕ in₂ {width-env γ} {width v})

body-inputs : ∀ {Γ Γ' σ} (γ : Env Γ) (γ' : Env Γ') (v : Val σ) →
              𝔽 ((suc (width-env γ) + suc (width-env γ')) + width v) ⇒ 𝔽 (suc (width-env γ' + width v))
body-inputs γ γ' v =
  ((in₁ {1} ∘ wctrl) ∥ (I {1} ⊕ in₁ {width-env γ'} {width v})) ∥ (in₂ {1} ∘ in₂ {width-env γ'} {width v})

sub-inputs : ∀ {Γ} (γ : Env Γ) {m n} → 𝔽 n ⇒ 𝔽 m →
             𝔽 (suc (width-env γ) + n) ⇒ 𝔽 (suc (width-env γ) + m)
sub-inputs γ C = I ⊕ C

rec-inputs : ∀ {Γ τ} (γ : Env Γ) (w' : Val τ) {m} →
             𝔽 ((suc (width-env γ) + m) + width w') ⇒ 𝔽 (suc (width-env γ + width w'))
rec-inputs γ w' {m} =
  ((I {1} ⊕ in₁ {width-env γ} {width w'}) ∘ p₁ {suc (width-env γ)} {m}) ∥ (in₂ {1} ∘ in₂ {width-env γ} {width w'})

map-built-out : ∀ {Γ} (γ : Env Γ) (m n : ℕ) → 𝔽 (suc (width-env γ) + suc m) ⇒ 𝔽 (suc n)
map-built-out γ m n = in₁ {1} {n} ∘ ((wctrl ∘ p₁ {suc (width-env γ)} {suc m}) +m (p₁ {1} {m} ∘ p₂ {suc (width-env γ)} {suc m}))

map-leaf : ∀ {Γ} (γ : Env Γ) (n : ℕ) → 𝔽 (suc (width-env γ) + n) ⇒ 𝔽 n
map-leaf γ n = p₂ {suc (width-env γ)} {n}

mutual
  data _,_⇓_[_] : ∀ {Γ τ} (γ : Env Γ) (t : Γ ⊢ τ) (v : Val τ) →
                   𝔽 (suc (width-env γ)) ⇒ 𝔽 (width v) → Set ℓ where
    ⇓-var    : ∀ {Γ τ} {γ : Env Γ} (x : Γ ∋ τ) → γ , var x ⇓ lookup x γ [ var-out x γ ]
    ⇓-unit   : ∀ {Γ} {γ : Env Γ} → γ , unit ⇓ unit [ wctrl ]
    ⇓-inl    : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₁} {v R} →
               γ , t ⇓ v [ R ] →
               γ , inl {τ₂ = τ₂} t ⇓ inl v [ built-out γ (width v) +m (in₂ {1} ∘ R) ]
    ⇓-inr    : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₂} {v R} →
               γ , t ⇓ v [ R ] →
               γ , inr {τ₁ = τ₁} t ⇓ inr v [ built-out γ (width v) +m (in₂ {1} ∘ R) ]
    ⇓-case-l : ∀ {Γ τ₁ τ₂ τ} {γ : Env Γ} {s : Γ ⊢ τ₁ [+] τ₂} {t₁ : Γ ▸ τ₁ ⊢ τ} {t₂ : Γ ▸ τ₂ ⊢ τ}
               {v u R T} →
               γ , s ⇓ inl v [ R ] → γ · v , t₁ ⇓ u [ T ] →
               γ , case s t₁ t₂ ⇓ u [ T ∘ (branch-inputs γ v ∘ ⟨ I , R ⟩) ]
    ⇓-case-r : ∀ {Γ τ₁ τ₂ τ} {γ : Env Γ} {s : Γ ⊢ τ₁ [+] τ₂} {t₁ : Γ ▸ τ₁ ⊢ τ} {t₂ : Γ ▸ τ₂ ⊢ τ}
               {v u R T} →
               γ , s ⇓ inr v [ R ] → γ · v , t₂ ⇓ u [ T ] →
               γ , case s t₁ t₂ ⇓ u [ T ∘ (branch-inputs γ v ∘ ⟨ I , R ⟩) ]
    ⇓-pair   : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {s : Γ ⊢ τ₁} {t : Γ ⊢ τ₂} {v u R T} →
               γ , s ⇓ v [ R ] → γ , t ⇓ u [ T ] →
               γ , pair s t ⇓ pair v u [ built-out γ (width v + width u) +m (in₂ {1} ∘ ⟨ R , T ⟩) ]
    ⇓-fst    : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₁ [×] τ₂} {v u R} →
               γ , t ⇓ pair v u [ R ] →
               γ , fst t ⇓ v [ elim-out γ v +m (proj-up {width v} {width u} v (p₁ {width v} {width u}) ∘ R) ]
    ⇓-snd    : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₁ [×] τ₂} {v u R} →
               γ , t ⇓ pair v u [ R ] →
               γ , snd t ⇓ u [ elim-out γ u +m (proj-up {width v} {width u} u (p₂ {width v} {width u}) ∘ R) ]
    ⇓-lam    : ∀ {Γ σ τ} {γ : Env Γ} {t : Γ ▸ σ ⊢ τ} → γ , lam t ⇓ clo γ t [ lam-out γ t ]
    ⇓-app    : ∀ {Γ Γ' σ τ} {γ : Env Γ} {γ' : Env Γ'} {s : Γ ⊢ σ [→] τ} {t t' v u R T U} →
               γ , s ⇓ clo {Γ'} γ' t' [ R ] → γ , t ⇓ v [ T ] → γ' · v , t' ⇓ u [ U ] →
               γ , app s t ⇓ u
                 [ U ∘ (body-inputs γ γ' v ∘ ⟨ ⟨ I , R ⟩ , T ⟩) ]
    ⇓-bop    : ∀ {Γ is o'} {γ : Env Γ} {ω : op is o'} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R} →
               γ , Ms ⇓s vs [ R ] →
               γ , bop ω Ms ⇓ const (op-fun ω .func vs) [ wctrl +m (op-dep ω vs ∘ R) ]
    ⇓-brel   : ∀ {Γ is} {γ : Env Γ} {ω : rel is} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R} →
               γ , Ms ⇓s vs [ R ] →
               γ , brel ω Ms ⇓ bool→val (rel-pred ω .func vs)
                 [ wctrl +m (brel-deps ω vs (rel-pred ω .func vs) ∘ R) ]
    ⇓-roll   : ∀ {Γ} {τ : type 1} {γ : Env Γ} {t : Γ ⊢ τ [ μ τ ]} {v R} →
               γ , t ⇓ v [ R ] → γ , roll {τ = τ} t ⇓ roll {τ} v [ R ]
    ⇓-fold   : ∀ {Γ} {τ : type 1} {σ : type 0} {γ : Env Γ} {s : Γ ▸ τ [ σ ] ⊢ σ} {t : Γ ⊢ μ τ}
               {v u R F} →
               γ , t ⇓ v [ R ] → Map γ {τ} {σ} s (var zero) v u F →
               γ , fold s t ⇓ u [ F ∘ ⟨ I , R ⟩ ]

  data _,_⇓s_[_] {Γ} (γ : Env Γ) : ∀ {is} → Every (λ s → Γ ⊢ base s) is →
                  sort-vals is → 𝔽 (suc (width-env γ)) ⇒ 𝔽 (bases-width is) →
                  Set ℓ where
    []  : γ , [] ⇓s tt [ εₘ ]
    _∷_ : ∀ {i is v vs R Rs} {M : Γ ⊢ base i} {Ms : Every (λ s → Γ ⊢ base s) is} →
          γ , M ⇓ const v [ R ] → γ , Ms ⇓s vs [ Rs ] →
          γ , (M ∷ Ms) ⇓s (v , vs) [ ⟨ R , Rs ⟩ ]

  data Map {Γ} (γ : Env Γ) {τ₀ : type 1} {σr : type 0} (s : Γ ▸ τ₀ [ σr ] ⊢ σr) :
           (σ' : type 1) (v : Val (σ' [ μ τ₀ ])) (v' : Val (σ' [ σr ])) →
           𝔽 (suc (width-env γ) + width v) ⇒ 𝔽 (width v') → Set ℓ where
    m-rec   : ∀ {w w' u F T} →
              Map γ s τ₀ w w' F → γ · w' , s ⇓ u [ T ] →
              Map γ s (var zero) (roll w) u (T ∘ (rec-inputs γ w' ∘ ⟨ I , F ⟩))
    m-unit  : ∀ {v} → Map γ s unit v v (map-leaf γ (width v))
    m-base  : ∀ {b v} → Map γ s (base b) v v (map-leaf γ (width v))
    m-arrow : ∀ {σ₁ σ₂ v} → Map γ s (σ₁ [→] σ₂) v v (map-leaf γ (width v))
    m-inl   : ∀ {σ₁ σ₂ v v' F} →
              Map γ s σ₁ v v' F →
              Map γ s (σ₁ [+] σ₂) (inl v) (inl v')
                  (map-built-out γ (width v) (width v') +m
                   (in₂ {1} ∘ (F ∘ sub-inputs γ (p₂ {1} {width v}))))
    m-inr   : ∀ {σ₁ σ₂ v v' F} →
              Map γ s σ₂ v v' F →
              Map γ s (σ₁ [+] σ₂) (inr v) (inr v')
                  (map-built-out γ (width v) (width v') +m
                   (in₂ {1} ∘ (F ∘ sub-inputs γ (p₂ {1} {width v}))))
    m-pair  : ∀ {σ₁ σ₂ v v' u u' F G} →
              Map γ s σ₁ v v' F → Map γ s σ₂ u u' G →
              Map γ s (σ₁ [×] σ₂) (pair v u) (pair v' u')
                  (map-built-out γ (width v + width u) (width v' + width u') +m
                   (in₂ {1} ∘ ⟨ F ∘ sub-inputs γ (p₁ {width v} {width u} ∘ p₂ {1} {width v + width u}) ,
                                  G ∘ sub-inputs γ (p₂ {width v} {width u} ∘ p₂ {1} {width v + width u}) ⟩))
    m-mu    : ∀ {τ' : type 2} {w w' F} →
              Map γ s (unfold₁ τ') w w' F →
              Map γ s (μ τ')
                  (roll (subst Val (unfold₁-inst τ' (μ τ₀)) w))
                  (roll (subst Val (unfold₁-inst τ' σr) w'))
                  (≡-to-⇒ (cong 𝔽 (sym (width-subst (unfold₁-inst τ' σr) w'))) ∘
                   (F ∘ sub-inputs γ (≡-to-⇒ (cong 𝔽 (width-subst (unfold₁-inst τ' (μ τ₀)) w)))))

infix 25 _,_⇓_[_] _,_⇓s_[_]

Derivation : ∀ {Γ τ} (γ : Env Γ) (t : Γ ⊢ τ) → Set ℓ
Derivation {τ = τ} γ t = Σ (Val τ) λ v → Σ (𝔽 (suc (width-env γ)) ⇒ 𝔽 (width v)) λ R → γ , t ⇓ v [ R ]

Derivations : ∀ {Γ is} (γ : Env Γ) (Ms : Every (λ s → Γ ⊢ base s) is) → Set ℓ
Derivations {is = is} γ Ms =
  Σ (sort-vals is) λ vs → Σ (𝔽 (suc (width-env γ)) ⇒ 𝔽 (bases-width is)) λ Rs → γ , Ms ⇓s vs [ Rs ]

MapDerivation : ∀ {Γ} (γ : Env Γ) (τ₀ : type 1) (σr : type 0) (s : Γ ▸ τ₀ [ σr ] ⊢ σr) (σ' : type 1) → Set ℓ
MapDerivation γ τ₀ σr s σ' =
  Σ (Val (σ' [ μ τ₀ ])) λ v → Σ (Val (σ' [ σr ])) λ v' →
  Σ (𝔽 (suc (width-env γ) + width v) ⇒ 𝔽 (width v')) λ F → Map γ {τ₀} {σr} s σ' v v' F
