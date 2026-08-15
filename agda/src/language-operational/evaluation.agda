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
open import Level using (0ℓ) renaming (_⊔_ to _⊔ℓ_)
open import Data.List using (List; []; _∷_)

-- Values, environments, and big-step evaluation decorated with dependency relations, threading a
-- control source: a distinguished extra input position holding the last eliminated constructor,
-- initially the run itself. A terminal rule attaches the source to its whole value; a constructor
-- attaches it to the new root; an elimination points the consumed root at the source and makes
-- that root the source of its continuation.
module language-operational.evaluation {ℓ} (Sig : Signature ℓ)
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (𝒫 : Primitives S Sig) (elim-weight : Setoid.Carrier A) where

open Signature Sig
open Primitives 𝒫
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

products : HasProducts M.cat
products = cmon-enriched.biproducts→products M.cmon M.biproduct

open HasProducts products using (p₁; p₂) renaming (pair to ⟨_,_⟩)

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

rooted : ∀ {m n} → m ⇒ n → m ⇒ suc n
rooted R = ⟨ M.εₘ , R ⟩

unrooted : ∀ {m n} → m ⇒ suc n → m ⇒ n
unrooted R = p₂ {1} ∘ R

-- The control row: every position at the elimination weight.
ctrl-row : ∀ {n} → 1 ⇒ n
ctrl-row _ _ = elim-weight

-- Control dependence: an eliminator's whole result depends on the root it consumes.
ctrl : ∀ {m n k} → m ⇒ suc n → m ⇒ k
ctrl R = ctrl-row ∘ (p₁ {1} ∘ R)

width-subst : ∀ {τ τ'} (e : τ ≡ τ') (v : Val τ) → width (subst Val e v) ≡ width v
width-subst refl v = refl

proj-var : ∀ {Γ τ} (x : Γ ∋ τ) (γ : Env Γ) → width-env γ ⇒ width (lookup x γ)
proj-var zero     (γ · v) = p₂ {width-env γ} {width v}
proj-var (succ x) (γ · v) = proj-var x γ ∘ p₁ {width-env γ} {width v}

-- Case on the branch so that the width computes.
brel-mat : ∀ {Γ} (γ : Env Γ) (d : width-env γ ⇒ 1) (b : ⊤ {0ℓ} ⊎ ⊤ {0ℓ}) →
           width-env γ ⇒ width (bool→val b)
brel-mat γ d (inj₁ _) = ⟨ d , M.εₘ ⟩
brel-mat γ d (inj₂ _) = ⟨ d , M.εₘ ⟩

brel-deps : ∀ {is} (ω : rel is) (vs : sort-vals is) (b : ⊤ {0ℓ} ⊎ ⊤ {0ℓ}) →
            bases-width is ⇒ width (bool→val b)
brel-deps ω vs (inj₁ _) = ⟨ rel-deps ω .func vs , M.εₘ ⟩
brel-deps ω vs (inj₂ _) = ⟨ rel-deps ω .func vs , M.εₘ ⟩

open M using (≈ₘ-refl; ≈ₘ-sym; ≈ₘ-trans)

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


-- Input positions of a derivation: the environment and the control source.
data Input : Set where
  environment source : Input

input-width : ∀ {Γ} → Env Γ → Input → ℕ
input-width γ environment = width-env γ
input-width _ source      = 1

-- A relation as its column at each input position, and back.
cols : ∀ {Γ} {γ : Env Γ} {n} → suc (width-env γ) ⇒ n → (i : Input) → M.Matrix n (input-width γ i)
cols R environment = R ∘ M.in₂ {1}
cols R source      = R ∘ M.in₁ {1}

of-cols : ∀ {Γ} {γ : Env Γ} {n} →
          ((i : Input) → M.Matrix n (input-width γ i)) → suc (width-env γ) ⇒ n
of-cols f = (f source ∘ src-col) M.+ₘ (f environment ∘ env-cols)

-- Reading a relation off its columns recovers it.
cols-of-cols : ∀ {Γ} {γ : Env Γ} {n} (f : (i : Input) → M.Matrix n (input-width γ i)) (i : Input) →
               cols (of-cols f) i M.≈ₘ f i
cols-of-cols {γ = γ} f environment =
  ≈ₘ-trans (M.comp-bilinear₁ (f source ∘ src-col) (f environment ∘ env-cols) (M.in₂ {1}))
  (≈ₘ-trans (M.+ₘ-cong (≈ₘ-trans (assoc (f source) src-col (M.in₂ {1}))
                                 (∘-cong₂ {f = f source} (M.zero-1 1 (width-env γ))))
                       (≈ₘ-trans (assoc (f environment) env-cols (M.in₂ {1}))
                                 (∘-cong₂ {f = f environment} (M.id-2 1 (width-env γ)))))
  (≈ₘ-trans (M.+ₘ-comm (f source ∘ M.εₘ) (f environment ∘ M.I))
  (≈ₘ-trans (M.absorb₂ (f environment ∘ M.I) (f source)) (id-right {f = f environment}))))
cols-of-cols {γ = γ} f source =
  ≈ₘ-trans (M.comp-bilinear₁ (f source ∘ src-col) (f environment ∘ env-cols) (M.in₁ {1}))
  (≈ₘ-trans (M.+ₘ-cong (≈ₘ-trans (assoc (f source) src-col (M.in₁ {1}))
                                 (∘-cong₂ {f = f source} (M.id-1 1 (width-env γ))))
                       (≈ₘ-trans (assoc (f environment) env-cols (M.in₁ {1}))
                                 (∘-cong₂ {f = f environment} (M.zero-2 1 (width-env γ)))))
  (≈ₘ-trans (M.absorb₂ (f source ∘ M.I) (f environment)) (id-right {f = f source})))

-- Each rule's wiring: the routing by which a premise reaches the conclusion's inputs, the column
-- the conclusion's root receives directly, and the entry it receives from each premise's root.
-- The graph semantics is built from the same data.
var-out : ∀ {Γ τ} (x : Γ ∋ τ) (γ : Env Γ) (i : Input) → M.Matrix (width (lookup x γ)) (input-width γ i)
var-out x γ environment = proj-var x γ
var-out x γ source      = ctrl-row

unit-out : ∀ {Γ} (γ : Env Γ) (i : Input) → M.Matrix (width unit) (input-width γ i)
unit-out γ environment = M.εₘ
unit-out γ source      = ctrl-row

lam-out : ∀ {Γ σ τ} (γ : Env Γ) (t : Γ ▸ σ ⊢ τ) (i : Input) →
          M.Matrix (width (clo γ t)) (input-width γ i)
lam-out γ t environment = M.in₂ {1}
lam-out γ t source      = M.in₁ {1} ∘ ctrl-row {1}

-- A freshly built constructor: its root carries the source, its argument the premise's root.
built-out : ∀ {Γ} (γ : Env Γ) (n : ℕ) (i : Input) → M.Matrix (suc n) (input-width γ i)
built-out γ n environment = M.εₘ
built-out γ n source      = M.in₁ {1} {n} ∘ ctrl-row {1}

-- An eliminated root: the conclusion's root points at it, and the source is charged the control
-- weight of consuming it.
elim-out : ∀ {Γ} (γ : Env Γ) (n : ℕ) (i : Input) → M.Matrix n (input-width γ i)
elim-out γ n environment = M.εₘ
elim-out γ n source      = ctrl-row ∘ ctrl-row {1}

proj-up : ∀ {m n k} → M.Matrix k (m + n) → M.Matrix k (suc (m + n))
proj-up {m} {n} P = (P ∘ p₂ {1} {m + n}) M.+ₘ (ctrl-row ∘ p₁ {1} {m + n})

-- A premise whose inputs are reached from the conclusion's by a fixed pair of matrices.
two-route : ∀ {Γ Γ'} (γ : Env Γ) (γ' : Env Γ') →
            M.Matrix (width-env γ') (width-env γ) → M.Matrix 1 1 →
            M.Linear (input-width γ') (input-width γ)
two-route γ γ' A B .M.ap f environment = f environment ∘ A
two-route γ γ' A B .M.ap f source      = f source ∘ B
two-route γ γ' A B .M.ap-+ f g environment = M.comp-bilinear₁ (f environment) (g environment) A
two-route γ γ' A B .M.ap-+ f g source      = M.comp-bilinear₁ (f source) (g source) B
two-route γ γ' A B .M.ap-∘ X f environment = assoc X (f environment) A
two-route γ γ' A B .M.ap-∘ X f source      = assoc X (f source) B
two-route γ γ' A B .M.ap-cong e environment = ∘-cong₁ {g = A} (e environment)
two-route γ γ' A B .M.ap-cong e source      = ∘-cong₁ {g = B} (e source)

-- A premise whose inputs are reached from an earlier premise's root by a fixed pair of matrices.
two-link : ∀ {Γ'} (γ' : Env Γ') {n} →
           M.Matrix (width-env γ') n → M.Matrix 1 n → M.Link (input-width γ') n
two-link γ' W U .M.at f = (f environment ∘ W) M.+ₘ (f source ∘ U)
two-link γ' W U .M.at-+ f g =
  ≈ₘ-trans (M.+ₘ-cong (M.comp-bilinear₁ (f environment) (g environment) W)
                      (M.comp-bilinear₁ (f source) (g source) U))
           (M.+ₘ-interchange (f environment ∘ W) (g environment ∘ W)
                             (f source ∘ U) (g source ∘ U))
two-link γ' W U .M.at-∘ X f =
  ≈ₘ-trans (M.+ₘ-cong (assoc X (f environment) W) (assoc X (f source) U))
           (≈ₘ-sym (M.comp-bilinear₂ X (f environment ∘ W) (f source ∘ U)))
two-link γ' W U .M.at-cong e =
  M.+ₘ-cong (∘-cong₁ {g = W} (e environment)) (∘-cong₁ {g = U} (e source))

-- The branch of a case: its environment extends the conclusion's by the matched value, and its
-- source is the scrutinee's root.
branch-route : ∀ {Γ τ} (γ : Env Γ) (v : Val τ) → M.Linear (input-width (γ · v)) (input-width γ)
branch-route γ v = two-route γ (γ · v) (M.in₁ {width-env γ} {width v}) (ctrl-row {1})

branch-link : ∀ {Γ τ} (γ : Env Γ) (v : Val τ) → M.Link (input-width (γ · v)) (suc (width v))
branch-link γ v =
  two-link (γ · v) (M.in₂ {width-env γ} {width v} ∘ p₂ {1} {width v}) (p₁ {1} {width v})

-- An application's body: its environment is the closure's extended by the argument, unrelated to
-- the conclusion's, and its source is the closure's root.
body-route : ∀ {Γ Γ' σ} (γ : Env Γ) (γ' : Env Γ') (v : Val σ) →
             M.Linear (input-width (γ' · v)) (input-width γ)
body-route γ γ' v = two-route γ (γ' · v) M.εₘ (ctrl-row {1})

body-link₁ : ∀ {Γ' σ} (γ' : Env Γ') (v : Val σ) →
             M.Link (input-width (γ' · v)) (suc (width-env γ'))
body-link₁ γ' v =
  two-link (γ' · v) (M.in₁ {width-env γ'} {width v} ∘ p₂ {1} {width-env γ'})
           (p₁ {1} {width-env γ'})

body-link₂ : ∀ {Γ' σ} (γ' : Env Γ') (v : Val σ) → M.Link (input-width (γ' · v)) (width v)
body-link₂ γ' v = two-link (γ' · v) (M.in₂ {width-env γ'} {width v}) M.εₘ

prim-out : ∀ {Γ} (γ : Env Γ) (n : ℕ) (i : Input) → M.Matrix n (input-width γ i)
prim-out γ n environment = M.εₘ
prim-out γ n source      = ctrl-row

-- Input positions of a fold action: the environment, the control source, and the value folded over.
data InputM : Set where
  environment source input : InputM

inputM-width : ∀ {Γ} → Env Γ → ℕ → InputM → ℕ
inputM-width γ n environment = width-env γ
inputM-width γ n source      = 1
inputM-width γ n input       = n

rcast : ∀ {m m' n} → m ≡ m' → M.Matrix m n → M.Matrix m' n
rcast refl R = R

ccast : ∀ {m n n'} → n ≡ n' → M.Matrix m n → M.Matrix m n'
ccast refl R = R

-- A fold action on a subvalue: the environment and source pass through, and the value folded over
-- is reached by C.
input-route : ∀ {Γ} (γ : Env Γ) {m n} → M.Matrix m n →
              M.Linear (inputM-width γ m) (inputM-width γ n)
input-route γ C .M.ap f environment = f environment
input-route γ C .M.ap f source      = f source
input-route γ C .M.ap f input       = f input ∘ C
input-route γ C .M.ap-+ f g environment = ≈ₘ-refl
input-route γ C .M.ap-+ f g source      = ≈ₘ-refl
input-route γ C .M.ap-+ f g input       = M.comp-bilinear₁ (f input) (g input) C
input-route γ C .M.ap-∘ X f environment = ≈ₘ-refl
input-route γ C .M.ap-∘ X f source      = ≈ₘ-refl
input-route γ C .M.ap-∘ X f input       = assoc X (f input) C
input-route γ C .M.ap-cong e environment = e environment
input-route γ C .M.ap-cong e source      = e source
input-route γ C .M.ap-cong e input       = ∘-cong₁ {g = C} (e input)

-- A fold action's recursive call: evaluated in the environment extended by the folded subresult,
-- with the source passing through and no dependence on the value folded over.
rec-route : ∀ {Γ τ} (γ : Env Γ) (w' : Val τ) {m} →
            M.Linear (input-width (γ · w')) (inputM-width γ m)
rec-route γ w' .M.ap f environment = f environment ∘ M.in₁ {width-env γ} {width w'}
rec-route γ w' .M.ap f source      = f source
rec-route γ w' .M.ap f input       = M.εₘ
rec-route γ w' .M.ap-+ f g environment =
  M.comp-bilinear₁ (f environment) (g environment) (M.in₁ {width-env γ} {width w'})
rec-route γ w' .M.ap-+ f g source = ≈ₘ-refl
rec-route γ w' .M.ap-+ f g input  = ≈ₘ-sym (M.+ₘ-lunit M.εₘ)
rec-route γ w' .M.ap-∘ X f environment = assoc X (f environment) (M.in₁ {width-env γ} {width w'})
rec-route γ w' .M.ap-∘ X f source = ≈ₘ-refl
rec-route γ w' .M.ap-∘ X f input  = ≈ₘ-sym (M.comp-bilinear-ε₂ X)
rec-route γ w' .M.ap-cong e environment = ∘-cong₁ {g = M.in₁ {width-env γ} {width w'}} (e environment)
rec-route γ w' .M.ap-cong e source = e source
rec-route γ w' .M.ap-cong e input  = ≈ₘ-refl

rec-link : ∀ {Γ τ} (γ : Env Γ) (w' : Val τ) → M.Link (input-width (γ · w')) (width w')
rec-link γ w' = two-link (γ · w') (M.in₂ {width-env γ} {width w'}) M.εₘ

-- A fold: the action's environment and source are the conclusion's, and the value folded over is
-- the first premise's root.
fold-route : ∀ {Γ} (γ : Env Γ) (m : ℕ) → M.Linear (inputM-width γ m) (input-width γ)
fold-route γ m .M.ap f environment = f environment
fold-route γ m .M.ap f source      = f source
fold-route γ m .M.ap-+ f g environment = ≈ₘ-refl
fold-route γ m .M.ap-+ f g source      = ≈ₘ-refl
fold-route γ m .M.ap-∘ X f environment = ≈ₘ-refl
fold-route γ m .M.ap-∘ X f source      = ≈ₘ-refl
fold-route γ m .M.ap-cong e environment = e environment
fold-route γ m .M.ap-cong e source      = e source

fold-link : ∀ {Γ} (γ : Env Γ) (m : ℕ) → M.Link (inputM-width γ m) m
fold-link γ m .M.at f = f input
fold-link γ m .M.at-+ f g = ≈ₘ-refl
fold-link γ m .M.at-∘ X f = ≈ₘ-refl
fold-link γ m .M.at-cong e = e input

-- A fold action that rebuilds a constructor, and one that copies its input unchanged.
map-built-out : ∀ {Γ} (γ : Env Γ) (m n : ℕ) (i : InputM) →
                M.Matrix (suc n) (inputM-width γ (suc m) i)
map-built-out γ m n environment = M.εₘ
map-built-out γ m n source      = M.in₁ {1} {n} ∘ ctrl-row {1}
map-built-out γ m n input       = M.in₁ {1} {n} ∘ p₁ {1} {m}

map-leaf : ∀ {Γ} (γ : Env Γ) (n : ℕ) (i : InputM) → M.Matrix n (inputM-width γ n i)
map-leaf γ n environment = M.εₘ
map-leaf γ n source      = M.εₘ
map-leaf γ n input       = M.I


mutual
  data _,_⇓_[_] : ∀ {Γ τ} (γ : Env Γ) (t : Γ ⊢ τ) (v : Val τ) →
                   suc (width-env γ) ⇒ width v → Set ℓ where
    ⇓-var    : ∀ {Γ τ} {γ : Env Γ} (x : Γ ∋ τ) →
               γ , var x ⇓ lookup x γ [ of-cols (var-out x γ) ]
    ⇓-unit   : ∀ {Γ} {γ : Env Γ} → γ , unit ⇓ unit [ of-cols (unit-out γ) ]
    ⇓-inl    : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₁} {v R} →
               γ , t ⇓ v [ R ] →
               γ , inl {τ₂ = τ₂} t ⇓ inl v
                 [ of-cols (M.rule₁-result (M.id-linear (input-width γ)) (built-out γ (width v))
                                         (M.in₂ {1}) (cols R)) ]
    ⇓-inr    : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₂} {v R} →
               γ , t ⇓ v [ R ] →
               γ , inr {τ₁ = τ₁} t ⇓ inr v
                 [ of-cols (M.rule₁-result (M.id-linear (input-width γ)) (built-out γ (width v))
                                         (M.in₂ {1}) (cols R)) ]
    ⇓-case-l : ∀ {Γ τ₁ τ₂ τ} {γ : Env Γ} {s : Γ ⊢ τ₁ [+] τ₂} {t₁ : Γ ▸ τ₁ ⊢ τ} {t₂ : Γ ▸ τ₂ ⊢ τ}
               {v u R T} →
               γ , s ⇓ inl v [ R ] → γ · v , t₁ ⇓ u [ T ] →
               γ , case s t₁ t₂ ⇓ u
                 [ of-cols (M.rule₂-result (M.id-linear (input-width γ)) (branch-route γ v)
                                         (branch-link γ v) (λ _ → M.εₘ) M.εₘ M.I
                                         (cols R) (cols T)) ]
    ⇓-case-r : ∀ {Γ τ₁ τ₂ τ} {γ : Env Γ} {s : Γ ⊢ τ₁ [+] τ₂} {t₁ : Γ ▸ τ₁ ⊢ τ} {t₂ : Γ ▸ τ₂ ⊢ τ}
               {v u R T} →
               γ , s ⇓ inr v [ R ] → γ · v , t₂ ⇓ u [ T ] →
               γ , case s t₁ t₂ ⇓ u
                 [ of-cols (M.rule₂-result (M.id-linear (input-width γ)) (branch-route γ v)
                                         (branch-link γ v) (λ _ → M.εₘ) M.εₘ M.I
                                         (cols R) (cols T)) ]
    ⇓-pair   : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {s : Γ ⊢ τ₁} {t : Γ ⊢ τ₂} {v u R T} →
               γ , s ⇓ v [ R ] → γ , t ⇓ u [ T ] →
               γ , pair s t ⇓ pair v u
                 [ of-cols (M.rule₂-result (M.id-linear (input-width γ)) (M.id-linear (input-width γ))
                                         (M.no-link (input-width γ) (width v))
                                         (built-out γ (width v + width u))
                                         (M.in₂ {1} ∘ M.in₁ {width v} {width u})
                                         (M.in₂ {1} ∘ M.in₂ {width v} {width u})
                                         (cols R) (cols T)) ]
    ⇓-fst    : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₁ [×] τ₂} {v u R} →
               γ , t ⇓ pair v u [ R ] →
               γ , fst t ⇓ v
                 [ of-cols (M.rule₁-result (M.id-linear (input-width γ)) (elim-out γ (width v))
                                         (proj-up {width v} {width u} (p₁ {width v} {width u})) (cols R)) ]
    ⇓-snd    : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₁ [×] τ₂} {v u R} →
               γ , t ⇓ pair v u [ R ] →
               γ , snd t ⇓ u
                 [ of-cols (M.rule₁-result (M.id-linear (input-width γ)) (elim-out γ (width u))
                                         (proj-up {width v} {width u} (p₂ {width v} {width u})) (cols R)) ]
    ⇓-lam    : ∀ {Γ σ τ} {γ : Env Γ} {t : Γ ▸ σ ⊢ τ} →
               γ , lam t ⇓ clo γ t [ of-cols (lam-out γ t) ]
    ⇓-app    : ∀ {Γ Γ' σ τ} {γ : Env Γ} {γ' : Env Γ'} {s : Γ ⊢ σ [→] τ} {t t' v u R T U} →
               γ , s ⇓ clo {Γ'} γ' t' [ R ] → γ , t ⇓ v [ T ] → γ' · v , t' ⇓ u [ U ] →
               γ , app s t ⇓ u
                 [ of-cols (M.rule₃-result (M.id-linear (input-width γ)) (M.id-linear (input-width γ))
                                          (body-route γ γ' v) (body-link₁ γ' v) (body-link₂ γ' v)
                                          (λ _ → M.εₘ) M.εₘ M.εₘ M.I
                                          (cols R) (cols T) (cols U)) ]
    ⇓-bop    : ∀ {Γ is o'} {γ : Env Γ} {ω : op is o'} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R} →
               γ , Ms ⇓s vs [ R ] →
               γ , bop ω Ms ⇓ const (op-fun ω .func vs)
                 [ of-cols (M.rule₁-result (M.id-linear (input-width γ))
                                         (prim-out γ (width (const (op-fun ω .func vs))))
                                         (op-deps ω .func vs) (cols R)) ]
    ⇓-brel   : ∀ {Γ is} {γ : Env Γ} {ω : rel is} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R} →
               γ , Ms ⇓s vs [ R ] →
               γ , brel ω Ms ⇓ bool→val (rel-pred ω .func vs)
                 [ of-cols (M.rule₁-result (M.id-linear (input-width γ))
                                         (prim-out γ (width (bool→val (rel-pred ω .func vs))))
                                         (brel-deps ω vs (rel-pred ω .func vs)) (cols R)) ]
    ⇓-roll   : ∀ {Γ} {τ : type 1} {γ : Env Γ} {t : Γ ⊢ τ [ μ τ ]} {v R} →
               γ , t ⇓ v [ R ] →
               γ , roll {τ = τ} t ⇓ roll {τ} v
                 [ of-cols (M.rule₁-result (M.id-linear (input-width γ)) (λ _ → M.εₘ) M.I (cols R)) ]
    ⇓-fold   : ∀ {Γ} {τ : type 1} {σ : type 0} {γ : Env Γ} {s : Γ ▸ τ [ σ ] ⊢ σ} {t : Γ ⊢ μ τ}
               {v u R F} →
               γ , t ⇓ v [ R ] → Map γ {τ} {σ} s (var zero) v u F →
               γ , fold s t ⇓ u
                 [ of-cols (M.rule₂-result (M.id-linear (input-width γ)) (fold-route γ (width v))
                                         (fold-link γ (width v)) (λ _ → M.εₘ) M.εₘ M.I
                                         (cols R) F) ]

  data _,_⇓s_[_] {Γ} (γ : Env Γ) : ∀ {is} → Every (λ s → Γ ⊢ base s) is →
                  sort-vals is → suc (width-env γ) ⇒ bases-width is →
                  Set ℓ where
    []  : γ , [] ⇓s tt [ of-cols {γ = γ} (λ _ → M.εₘ) ]
    _∷_ : ∀ {i is v vs R Rs} {M : Γ ⊢ base i} {Ms : Every (λ s → Γ ⊢ base s) is} →
          γ , M ⇓ const v [ R ] → γ , Ms ⇓s vs [ Rs ] →
          γ , (M ∷ Ms) ⇓s (v , vs)
            [ of-cols (M.rule₂-result (M.id-linear (input-width γ)) (M.id-linear (input-width γ))
                                    (M.no-link (input-width γ) (width (const v)))
                                    (λ _ → M.εₘ)
                                    (M.in₁ {width (const v)} {bases-width is})
                                    (M.in₂ {width (const v)} {bases-width is})
                                    (cols R) (cols Rs)) ]

  -- Functorial action of σ' on the fold s: the source passes through unchanged, and each rebuilt
  -- constructor carries the copied root pointed at the source.
  data Map {Γ} (γ : Env Γ) {τ₀ : type 1} {σr : type 0} (s : Γ ▸ τ₀ [ σr ] ⊢ σr) :
           (σ' : type 1) (v : Val (σ' [ μ τ₀ ])) (v' : Val (σ' [ σr ])) →
           ((i : InputM) → M.Matrix (width v') (inputM-width γ (width v) i)) →
           Set ℓ where
    m-rec   : ∀ {w w' u F T} →
              Map γ s τ₀ w w' F → γ · w' , s ⇓ u [ T ] →
              Map γ s (var zero) (roll w) u
                  (M.rule₂-result (M.id-linear (inputM-width γ (width w))) (rec-route γ w')
                                (rec-link γ w') (λ _ → M.εₘ) M.εₘ M.I F (cols T))
    m-unit  : ∀ {v} → Map γ s unit v v (map-leaf γ (width v))
    m-base  : ∀ {b v} → Map γ s (base b) v v (map-leaf γ (width v))
    m-arrow : ∀ {σ₁ σ₂ v} → Map γ s (σ₁ [→] σ₂) v v (map-leaf γ (width v))
    m-inl   : ∀ {σ₁ σ₂ v v' F} →
              Map γ s σ₁ v v' F →
              Map γ s (σ₁ [+] σ₂) (inl v) (inl v')
                  (M.rule₁-result (input-route γ (p₂ {1} {width v}))
                                (map-built-out γ (width v) (width v')) (M.in₂ {1}) F)
    m-inr   : ∀ {σ₁ σ₂ v v' F} →
              Map γ s σ₂ v v' F →
              Map γ s (σ₁ [+] σ₂) (inr v) (inr v')
                  (M.rule₁-result (input-route γ (p₂ {1} {width v}))
                                (map-built-out γ (width v) (width v')) (M.in₂ {1}) F)
    m-pair  : ∀ {σ₁ σ₂ v v' u u' F G} →
              Map γ s σ₁ v v' F → Map γ s σ₂ u u' G →
              Map γ s (σ₁ [×] σ₂) (pair v u) (pair v' u')
                  (M.rule₂-result (input-route γ (p₁ {width v} {width u} ∘ p₂ {1} {width v + width u}))
                                (input-route γ (p₂ {width v} {width u} ∘ p₂ {1} {width v + width u}))
                                (M.no-link (inputM-width γ (width u)) (width v'))
                                (map-built-out γ (width v + width u) (width v' + width u'))
                                (M.in₂ {1} ∘ M.in₁ {width v'} {width u'})
                                (M.in₂ {1} ∘ M.in₂ {width v'} {width u'}) F G)
    m-mu    : ∀ {τ' : type 2} {w w' F} →
              Map γ s (unfold₁ τ') w w' F →
              Map γ s (μ τ')
                  (roll (subst Val (unfold₁-inst τ' (μ τ₀)) w))
                  (roll (subst Val (unfold₁-inst τ' σr) w'))
                  (M.rule₁-result
                     (input-route γ (ccast (sym (width-subst (unfold₁-inst τ' (μ τ₀)) w)) M.I))
                     (λ _ → M.εₘ)
                     (rcast (sym (width-subst (unfold₁-inst τ' σr) w')) M.I) F)

infix 25 _,_⇓_[_] _,_⇓s_[_]
