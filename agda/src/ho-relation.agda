{-# OPTIONS --prop --postfix-projections --safe #-}

-- The logical relation between the operational semantics and the higher-order model, on the fragment
-- without μ-types: values against indices of the interpretation, dependence vectors against elements
-- of the fibre, and the lemmas by recursion on types that the fundamental lemma needs (respect for the
-- setoids, adding the control positions and the control dependence, absorption, transport).
open import Level using (0ℓ; lift)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import every using (Every)
open import Data.List using ([]; _∷_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import prop
open import prop using (_∧_; ∃; ∃ₛ; Prf; ⟪_⟫; _,_)
open import prop-setoid using (Setoid; IsEquivalence)
open import commutative-semiring using (CommutativeSemiring)
open import signature using (Signature)
import signature
open import signature.interpretation using (Interpretation; sort-vals-setoid)
open import categories using (Category; HasProducts; HasTerminal; HasWeakExponentials; HasStrongCoproducts)
open import cmon-enriched using (CMonEnriched; Biproduct)
import indexed-family
open import indexed-family using (HasSetoidProducts)
import matrix
import semimodule
import commutative-monoid
import ho-model
import language-interpretation

module ho-relation
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A) (ctrl-weight : Setoid.Carrier A)
  (Sig : Signature 0ℓ) (ℐ : Interpretation S Sig)
  (let module Sc = CommutativeSemiring S)
  -- Addition is idempotent, and the control weight is idempotent and absorbs its multiples.
  (+-idem : ∀ x → Setoid._≈_ A (x Sc.+ x) x)
  (c-idem : Setoid._≈_ A (ctrl-weight Sc.· ctrl-weight) ctrl-weight)
  (c-absorb : ∀ x → Setoid._≈_ A ((ctrl-weight Sc.· x) Sc.+ ctrl-weight) ctrl-weight)
  where

open Signature Sig
open Interpretation ℐ
open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.evaluation Sig S ℐ ctrl-weight

module model = ho-model S ctrl-weight
module interp = model.interp Sig ℐ
open model using (𝔽; mat; ι1-fwd; ι1-bwd; module Ls; module SemiMod)
open SemiMod using (Semimodule; _⇒_)
open Semimodule using () renaming (Carrier to ∣_∣)
open SemiMod._⇒_ using (func)

module M = matrix.Mat S
module SMP = HasProducts SemiMod.products
module FD = model.Fam⟨𝒟⟩μ
module SP = HasSetoidProducts model.SPmod

open FD using (Obj; Mor; idx; fam; fm; idxf; famf; Constant)
open indexed-family.Fam using (subst)
open indexed-family._⇒f_ using (transf)
open prop-setoid._⇒_ using () renaming (func to sfunc)

-- The interpretation, at the parameters the higher-order model fixes.
module LI = language-interpretation Sig 0ℓ 0ℓ
  SemiMod.terminal SemiMod.cmon-enriched SemiMod.biproduct SemiMod.𝕀 model.SemiModExp
  interp.δ∅𝒟 interp.𝒟𝟙ty interp.𝒟unit-pt interp.𝒟-Sig-model model.ctrl-weight-endo
  (λ {X} {Y} → model.exp-const {X} {Y}) interp.𝒟𝟙ty-const interp.𝒟-sort-const

open LI using (⟦_⟧ty; ⟦_⟧ctxt; ⟦_⟧tm; ⟦_⟧tms; ctrl-dep; ty-unit)
open Constant using (at)

module IP = model.FP.interp-primitives Sig ℐ
module FCμ = model.Fam⟨𝒞⟩μ

⟦_⟧ : type 0 → Obj
⟦ τ ⟧ = ⟦ τ ⟧ty (λ ())

Ix : type 0 → Set
Ix τ = Setoid.Carrier (⟦ τ ⟧ .idx)

Fib : (τ : type 0) → Ix τ → Semimodule
Fib τ i = ⟦ τ ⟧ .fam .fm i

IxC : ctxt → Set
IxC Γ = Setoid.Carrier (⟦ Γ ⟧ctxt .idx)

FibC : (Γ : ctxt) → IxC Γ → Semimodule
FibC Γ i = ⟦ Γ ⟧ctxt .fam .fm i

_≈A_ : Setoid.Carrier A → Setoid.Carrier A → Prop
_≈A_ = Setoid._≈_ A


-- Values related to indices, by recursion on the type. A closure is related to a fibre map of the
-- exponential when, for every related argument and every derivation of the body at it, the result
-- is related to the map's index at the argument.
ValRel : ∀ τ → Val τ → Ix τ → Set
ValRel unit unit i = ⊤
ValRel (base s) (const a) i = Prf (Setoid._≈_ (sort-index s) i a)
ValRel (σ [+] τ) (inl v) i = Σ (Ix σ) λ i' → ValRel σ v i' × Prf (Setoid._≈_ (⟦ σ [+] τ ⟧ .idx) i (inj₁ i'))
ValRel (σ [+] τ) (inr v) i = Σ (Ix τ) λ i' → ValRel τ v i' × Prf (Setoid._≈_ (⟦ σ [+] τ ⟧ .idx) i (inj₂ i'))
ValRel (σ [×] τ) (pair v u) (i , j) = ValRel σ v i × ValRel τ u j
ValRel (σ [→] τ) (clo γ' t) f =
  ∀ {v : Val σ} {j : Ix σ} → ValRel σ v j → ∀ {u U} → γ' · v , t ⇓ u [ U ] → ValRel τ u (f .idxf .sfunc j)
ValRel (μ τ) v i = ⊥

-- The vector over the body's inputs at an application: the value at the control input, then the
-- closure's cells and the argument as the environment.
body-input : ∀ {Γ' σ} (γ' : Env Γ') (v : Val σ) → Setoid.Carrier A →
             ∣ 𝔽 (width-env γ') ∣ → ∣ 𝔽 (width v) ∣ → ∣ 𝔽 (suc (width-env γ' + width v)) ∣
body-input γ' v s x z zero    = s
body-input γ' v s x z (suc k) =
  Semimodule._+_ (𝔽 (width-env γ' + width v))
    (mat (M.in₁ {width-env γ'} {width v}) .func x)
    (mat (M.in₂ {width-env γ'} {width v}) .func z) k

-- The control dependence at an index and a value of the control input.
ctrl-dep-at : ∀ τ (i : Ix τ) → Setoid.Carrier A → ∣ Fib τ i ∣
ctrl-dep-at τ i s = ctrl-dep τ .at i .func s

-- Each fibre's semimodule with its additive order: x ⊑ y when x + y is y. Addition in a fibre is
-- idempotent because it is in the semiring.
fib-+-idem : ∀ τ i {x} → Semimodule._≈_ (Fib τ i) (Semimodule._+_ (Fib τ i) x x) x
fib-+-idem τ i =
  X.trans (X.+-cong (X.sym X.·-unit) (X.sym X.·-unit))
          (X.trans (X.sym X.+-distribʳ) (X.trans (X.·-cong (+-idem Sc.ι) X.refl) X.·-unit))
  where module X = Semimodule (Fib τ i)

module F τ i where
  open Semimodule (Fib τ i) public
  open commutative-monoid.AdditivePreorder additive (fib-+-idem τ i) public

-- A dependence vector on a value's positions against an element of the fibre at a related index.
-- At an arrow type the root agrees, and for any further weight, any argument related up to control
-- dependence at the root and the further weight, and any derivation of the body, the body's
-- dependence through the root and the further weight at the control input and the cells and
-- argument as environment agrees with the control dependence at that weight plus the payload
-- evaluated at the argument plus the index's fibre map at the argument. The relation up to control
-- dependence at a value of the control input allows a further summand below the control dependence
-- at that value.
DepRel⊑ : ∀ τ {v : Val τ} {i : Ix τ} → ValRel τ v i → Setoid.Carrier A →
          ∣ 𝔽 (width v) ∣ → ∣ Fib τ i ∣ → Prop
DepRel : ∀ τ {v : Val τ} {i : Ix τ} → ValRel τ v i → ∣ 𝔽 (width v) ∣ → ∣ Fib τ i ∣ → Prop
DepRel unit {unit} {i} r o d = Semimodule._≈_ (Fib unit i) o d
DepRel (base s) {const a} {i} r o d = Semimodule._≈_ (Fib (base s) i) o d
DepRel (σ [+] τ) {inl v} {i} (i' , r , ⟪ e ⟫) o d =
  let d' = ⟦ σ [+] τ ⟧ .fam .subst {i} {inj₁ i'} e .func d in
  (o zero ≈A proj₁ d') ∧ DepRel σ r (λ k → o (suc k)) (proj₂ d')
DepRel (σ [+] τ) {inr v} {i} (i' , r , ⟪ e ⟫) o d =
  let d' = ⟦ σ [+] τ ⟧ .fam .subst {i} {inj₂ i'} e .func d in
  (o zero ≈A proj₁ d') ∧ DepRel τ r (λ k → o (suc k)) (proj₂ d')
DepRel (σ [×] τ) {pair v u} {i , j} (r , r') o d =
  (o zero ≈A proj₁ d) ∧
  (DepRel σ r (mat (M.p₁ {width v} {width u}) .func (λ k → o (suc k))) (proj₁ (proj₂ d)) ∧
   DepRel τ r' (mat (M.p₂ {width v} {width u}) .func (λ k → o (suc k))) (proj₂ (proj₂ d)))
DepRel (σ [→] τ) {clo γ' t} {f} r o d =
  (o zero ≈A proj₁ d) ∧
  (∀ (s' : Setoid.Carrier A) {v : Val σ} {j : Ix σ} (rv : ValRel σ v j)
     (z : ∣ 𝔽 (width v) ∣) (y : ∣ Fib σ j ∣) → DepRel⊑ σ rv (s' Sc.+ o zero) z y →
   ∀ {u U} (D : γ' · v , t ⇓ u [ U ]) →
     DepRel τ (r rv D) (mat U .func (body-input γ' v (s' Sc.+ o zero) (λ k → o (suc k)) z))
       (Semimodule._+_ (Fib τ (f .idxf .sfunc j))
         (ctrl-dep τ .at (f .idxf .sfunc j) .func (s' Sc.+ o zero))
         (Semimodule._+_ (Fib τ (f .idxf .sfunc j))
           (SP.evalΠ (⟦ τ ⟧ .fam indexed-family.[ f .idxf ]) j .func (proj₂ d))
           (f .famf .transf j .func y))))

DepRel⊑ τ {i = i} r s o d =
  ∃ (∣ Fib τ i ∣) (λ m → F._⊑_ τ i m (ctrl-dep-at τ i s) ∧ DepRel τ r o (Semimodule._+_ (Fib τ i) d m))

-- A primitive's arguments need no relations of their own. The model's index at a tuple of
-- arguments is a tuple of sort indices, and sort-vals-setoid is built from ⊗-setoid, whose
-- equality is the pairwise conjunction, so the value relation is equality in that setoid, one
-- base equation per argument. The fibre is 𝔽 (bases-width is) on both sides, the arguments'
-- positions laid end to end, so the vector relation is equality there, as at a single base sort.

-- Environments related to context indices, and environment vectors to elements of the context
-- fibre at a value s at the control input: each cell may carry, beyond its relation, control
-- dependence below the control dependence at s.
data EnvValRel : ∀ {Γ} → Env Γ → IxC Γ → Set where
  emp : EnvValRel emp (lift tt)
  _·_ : ∀ {Γ τ} {γ : Env Γ} {v : Val τ} {gi i} → EnvValRel γ gi → ValRel τ v i → EnvValRel (γ · v) (gi , i)

infixl 30 _·_

EnvDepRel : ∀ {Γ} {γ : Env Γ} {gi} → EnvValRel γ gi → Setoid.Carrier A →
            ∣ 𝔽 (width-env γ) ∣ → ∣ FibC Γ gi ∣ → Prop
EnvDepRel emp s x g = prop.⊤
EnvDepRel (_·_ {γ = γ} {v = v} rγ r) s x g =
  EnvDepRel rγ s (mat (M.p₁ {width-env γ} {width v}) .func x) (proj₁ g) ∧
  DepRel⊑ _ r s (mat (M.p₂ {width-env γ} {width v}) .func x) (proj₂ g)

-- The inputs of a derivation: the control input's value at the first position, the environment after.
inputs : ∀ {Γ} (γ : Env Γ) → Setoid.Carrier A → ∣ 𝔽 (width-env γ) ∣ → ∣ 𝔽 (suc (width-env γ)) ∣
inputs γ s x zero    = s
inputs γ s x (suc k) = x k

open model using (app-+; app-+ₘ; app-∘; app-εₘ; app-I; app-e; app-congₘ; app-congᵥ) renaming (app to ap)
open Sc using (ι; ε) renaming (_≈_ to _≈s_; _+_ to _+ₛ_; _·_ to _·ₛ_)
open Setoid A using () renaming (refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)
open M using (Σ-cong; Σ-unit; Σ-ε; _∘_; _+ₘ_; εₘ; ≈ₘ-refl; ≈ₘ-sym; ≈ₘ-trans) renaming (Σ to Σₛ)

open Sc using (+-cong; ·-cong; +-lunit; +-comm; +-assoc; ·-lunit; ·-comm; ε-annihilₗ; ε-annihilᵣ)
open M using (⟨_,_⟩)

-- Reading a relation at the inputs: the control input's column at its value, and the environment
-- columns at the environment vector.
p₁-e : ∀ {m} (j : Fin (suc m)) → M.p₁ {1} {m} zero j ≈s M.e zero j
p₁-e zero    = ≈-refl
p₁-e (suc j) = ≈-refl

p₂-e : ∀ {m} (j : Fin m) (l : Fin m) → M.p₂ {1} {m} j (suc l) ≈s M.e j l
p₂-e j l = ≈-refl

-- Semiring shorthands.
c = ctrl-weight
+-runit : ∀ {x} → (x +ₛ ε) ≈s x
+-runit = ≈-trans +-comm +-lunit
·-runit : ∀ {x} → (x ·ₛ ι) ≈s x
·-runit = ≈-trans ·-comm ·-lunit
Σ₁ : ∀ (f : Fin 1 → Setoid.Carrier A) → Σₛ f ≈s f zero
Σ₁ f = +-runit

m-runit : ∀ (X : Semimodule) {x} → Semimodule._≈_ X (Semimodule._+_ X x (Semimodule.ε X)) x
m-runit X = Semimodule.trans X (Semimodule.+-comm X) (Semimodule.+-lunit X)

-- Reading a lifted vector: the first position of the first summand's injection, and the rest of
-- the second's.
ap-in₁-zero : ∀ {n} (u : ∣ 𝔽 1 ∣) → ap (M.in₁ {1} {n}) u zero ≈s u zero
ap-in₁-zero {n} u = ≈-trans (Σ₁ (λ j → M.in₁ {1} {n} zero j ·ₛ u j)) ·-lunit

ap-in₁-suc : ∀ {n} (u : ∣ 𝔽 1 ∣) (k : Fin n) → ap (M.in₁ {1} {n}) u (suc k) ≈s ε
ap-in₁-suc {n} u k = ≈-trans (Σ₁ (λ j → M.in₁ {1} {n} (suc k) j ·ₛ u j)) ε-annihilₗ

ap-in₂-zero : ∀ {n} (u : ∣ 𝔽 n ∣) → ap (M.in₂ {1} {n}) u zero ≈s ε
ap-in₂-zero {n} u = ≈-trans (Σ-cong {n} (λ _ → ε-annihilₗ)) (Σ-ε {n})

ap-in₂-suc : ∀ {n} (u : ∣ 𝔽 n ∣) (k : Fin n) → ap (M.in₂ {1} {n}) u (suc k) ≈s u k
ap-in₂-suc {n} u k =
  ≈-trans (Σ-cong {n} (λ j → ·-cong (≈-trans (p₂-e {n} j k) (M.e-sym j k)) ≈-refl)) (Σ-unit {n} k u)

ap-pair-zero : ∀ {m n} (f : M.Matrix 1 m) (g : M.Matrix n m) (u : ∣ 𝔽 m ∣) →
               ap (⟨ f , g ⟩) u zero ≈s ap f u zero
ap-pair-zero {m} {n} f g u =
  ≈-trans (app-+ₘ (M.in₁ {1} {n} ∘ f) (M.in₂ {1} {n} ∘ g) u zero)
          (≈-trans (+-cong (≈-trans (app-∘ (M.in₁ {1} {n}) f u zero) (ap-in₁-zero {n} (ap f u)))
                           (≈-trans (app-∘ (M.in₂ {1} {n}) g u zero) (ap-in₂-zero {n} (ap g u))))
                   +-runit)

ap-pair-suc : ∀ {m n} (f : M.Matrix 1 m) (g : M.Matrix n m) (u : ∣ 𝔽 m ∣) (k : Fin n) →
              ap (⟨ f , g ⟩) u (suc k) ≈s ap g u k
ap-pair-suc {m} {n} f g u k =
  ≈-trans (app-+ₘ (M.in₁ {1} {n} ∘ f) (M.in₂ {1} {n} ∘ g) u (suc k))
          (≈-trans (+-cong (≈-trans (app-∘ (M.in₁ {1} {n}) f u (suc k)) (ap-in₁-suc {n} (ap f u) k))
                           (≈-trans (app-∘ (M.in₂ {1} {n}) g u (suc k)) (ap-in₂-suc {n} (ap g u) k)))
                   +-lunit)

-- The control vector at a value s at the control input: the weight at the root of a lifted value, and the
-- payload's control vector after.
ap-ctrl-row : ∀ {n} (s : Setoid.Carrier A) (k : Fin n) → ap ctrl-row (λ _ → s) k ≈s (c ·ₛ s)
ap-ctrl-row {n} s k = Σ₁ (λ j → ctrl-row {n} k j ·ₛ s)

ctrl-lift-zero : ∀ {n} (g : M.Matrix n 1) (s : Setoid.Carrier A) →
                 ap (⟨ ctrl-row {1} , g ⟩) (λ _ → s) zero ≈s (c ·ₛ s)
ctrl-lift-zero {n} g s = ≈-trans (ap-pair-zero {1} {n} ctrl-row g (λ _ → s)) (ap-ctrl-row {1} s zero)

ctrl-lift-suc : ∀ {n} (g : M.Matrix n 1) (s : Setoid.Carrier A) (k : Fin n) →
                ap (⟨ ctrl-row {1} , g ⟩) (λ _ → s) (suc k) ≈s ap g (λ _ → s) k
ctrl-lift-suc {n} g s k = ap-pair-suc {1} {n} ctrl-row g (λ _ → s) k

-- Reading a relation at the inputs: the control input's column at its value and the environment
-- columns at the environment vector, and the relations the rules are built from at any vector.
ap-p₁₁ : ∀ {m} (o : ∣ 𝔽 (suc m) ∣) (k : Fin 1) → ap (M.p₁ {1} {m}) o k ≈s o zero
ap-p₁₁ {m} o zero =
  ≈-trans (Σ-cong {suc m} (λ j → ·-cong (p₁-e {m} j) (≈-refl {o j}))) (Σ-unit {suc m} zero o)

ap-p₂₁ : ∀ {m} (o : ∣ 𝔽 (suc m) ∣) (k : Fin m) → ap (M.p₂ {1} {m}) o k ≈s o (suc k)
ap-p₂₁ {m} o k =
  ≈-trans (+-cong ε-annihilₗ (Σ-cong {m} (λ j → ·-cong (p₂-e {m} k j) ≈-refl)))
          (≈-trans +-lunit (Σ-unit {m} k (λ j → o (suc j))))

ap-∥ : ∀ {m n} (A : M.Matrix n 1) (B : M.Matrix n m) (y : ∣ 𝔽 (suc m) ∣) (k : Fin n) →
       ap (A M.∥ B) y k ≈s (ap A (λ _ → y zero) k +ₛ ap B (λ l → y (suc l)) k)
ap-∥ {m} A B y k =
  ≈-trans (app-+ₘ (A ∘ M.p₁ {1} {m}) (B ∘ M.p₂ {1} {m}) y k)
          (+-cong (≈-trans (app-∘ A (M.p₁ {1} {m}) y k) (app-congᵥ A (ap-p₁₁ {m} y) k))
                  (≈-trans (app-∘ B (M.p₂ {1} {m}) y k) (app-congᵥ B (ap-p₂₁ {m} y) k)))

ap-wctrl : ∀ {m n} (y : ∣ 𝔽 (suc m) ∣) (k : Fin n) → ap (wctrl {m} {n}) y k ≈s (c ·ₛ y zero)
ap-wctrl {m} {n} y k =
  ≈-trans (app-∘ (ctrl-row {n}) (M.p₁ {1} {m}) y k)
          (≈-trans (app-congᵥ (ctrl-row {n}) (ap-p₁₁ {m} y) k) (ap-ctrl-row {n} (y zero) k))

ap-⊕-zero : ∀ {m a b} (f : M.Matrix 1 a) (g : M.Matrix b m) (y : ∣ 𝔽 (a + m) ∣) →
            ap (f ⊕ g) y zero ≈s ap f (ap (M.p₁ {a} {m}) y) zero
ap-⊕-zero {m} {a} {b} f g y =
  ≈-trans (ap-pair-zero {a + m} {b} (f ∘ M.p₁ {a} {m}) (g ∘ M.p₂ {a} {m}) y)
          (app-∘ f (M.p₁ {a} {m}) y zero)

ap-⊕-suc : ∀ {m a b} (f : M.Matrix 1 a) (g : M.Matrix b m) (y : ∣ 𝔽 (a + m) ∣) (k : Fin b) →
           ap (f ⊕ g) y (suc k) ≈s ap g (ap (M.p₂ {a} {m}) y) k
ap-⊕-suc {m} {a} {b} f g y k =
  ≈-trans (ap-pair-suc {a + m} {b} (f ∘ M.p₁ {a} {m}) (g ∘ M.p₂ {a} {m}) y k)
          (app-∘ g (M.p₂ {a} {m}) y k)

ap-⊕₁-zero : ∀ {m b} (f : M.Matrix 1 1) (g : M.Matrix b m) (y : ∣ 𝔽 (suc m) ∣) →
             ap (f ⊕ g) y zero ≈s ap f (λ _ → y zero) zero
ap-⊕₁-zero {m} f g y = ≈-trans (ap-⊕-zero {m} {1} f g y) (app-congᵥ f (ap-p₁₁ {m} y) zero)

ap-⊕₁-suc : ∀ {m b} (f : M.Matrix 1 1) (g : M.Matrix b m) (y : ∣ 𝔽 (suc m) ∣) (k : Fin b) →
            ap (f ⊕ g) y (suc k) ≈s ap g (λ l → y (suc l)) k
ap-⊕₁-suc {m} f g y k = ≈-trans (ap-⊕-suc {m} {1} f g y k) (app-congᵥ g (ap-p₂₁ {m} y) k)

-- The control dependence elementwise: the weight times the control input's value at each root, the
-- payload's constant under it, and zero at a closure's payload.
ctrl-dep-unit : ∀ i s → ctrl-dep-at unit i s zero ≈s (c ·ₛ s)
ctrl-dep-unit i s =
  ≈-trans (+-cong (·-cong +-runit ≈-refl) ≈-refl)
          (≈-trans +-runit (≈-trans ·-lunit +-runit))

-- The same at a base sort: the sort's unit constant is the row of units, so scaling by the
-- control weight leaves the weight at every position of the result.
ctrl-dep-base : ∀ {σ} i s (k : Fin (sort-width σ)) → ctrl-dep-at (base σ) i s k ≈s (c ·ₛ s)
ctrl-dep-base i s k = ≈-trans +-runit (≈-trans ·-lunit +-runit)

ctrl-dep-inj₁ : ∀ {σ τ} (i : Ix σ) s →
          (proj₁ (ctrl-dep-at (σ [+] τ) (inj₁ i) s) ≈s (c ·ₛ s)) ∧
          Semimodule._≈_ (Fib σ i) (proj₂ (ctrl-dep-at (σ [+] τ) (inj₁ i) s)) (ctrl-dep-at σ i s)
ctrl-dep-inj₁ {σ} i s = ≈-trans +-runit +-runit , Semimodule.+-lunit (Fib σ i)

ctrl-dep-inj₂ : ∀ {σ τ} (i : Ix τ) s →
          (proj₁ (ctrl-dep-at (σ [+] τ) (inj₂ i) s) ≈s (c ·ₛ s)) ∧
          Semimodule._≈_ (Fib τ i) (proj₂ (ctrl-dep-at (σ [+] τ) (inj₂ i) s)) (ctrl-dep-at τ i s)
ctrl-dep-inj₂ {σ} {τ} i s = ≈-trans +-runit +-runit , Semimodule.+-lunit (Fib τ i)

ctrl-dep-pair : ∀ {σ τ} (i : Ix σ) (j : Ix τ) s →
          (proj₁ (ctrl-dep-at (σ [×] τ) (i , j) s) ≈s (c ·ₛ s)) ∧
          (Semimodule._≈_ (Fib σ i) (proj₁ (proj₂ (ctrl-dep-at (σ [×] τ) (i , j) s))) (ctrl-dep-at σ i s) ∧
           Semimodule._≈_ (Fib τ j) (proj₂ (proj₂ (ctrl-dep-at (σ [×] τ) (i , j) s))) (ctrl-dep-at τ j s))
ctrl-dep-pair {σ} {τ} i j s =
  ≈-trans +-runit +-runit ,
  (Semimodule.trans (Fib σ i) (F.+-lunit σ i) (m-runit (Fib σ i)) ,
   Semimodule.trans (Fib τ j) (F.+-lunit τ j) (F.+-lunit τ j))

ctrl-dep-clo : ∀ {σ τ} (f : Ix (σ [→] τ)) s →
         (proj₁ (ctrl-dep-at (σ [→] τ) f s) ≈s (c ·ₛ s)) ∧
         Semimodule._≈_ (model.FE._⟶_ ⟦ σ ⟧ ⟦ τ ⟧ .fam .fm f) (proj₂ (ctrl-dep-at (σ [→] τ) f s))
           (Semimodule.ε (model.FE._⟶_ ⟦ σ ⟧ ⟦ τ ⟧ .fam .fm f))
ctrl-dep-clo {σ} {τ} f s =
  ≈-trans +-runit +-runit ,
  Semimodule.+-lunit (model.FE._⟶_ ⟦ σ ⟧ ⟦ τ ⟧ .fam .fm f) {Semimodule.ε (model.FE._⟶_ ⟦ σ ⟧ ⟦ τ ⟧ .fam .fm f)}

ctrl-dep-natural : ∀ τ {i i' : Ix τ} (e : Setoid._≈_ (⟦ τ ⟧ .idx) i i') s →
             Semimodule._≈_ (Fib τ i') (⟦ τ ⟧ .fam .subst e .func (ctrl-dep-at τ i s)) (ctrl-dep-at τ i' s)
ctrl-dep-natural τ e s = ctrl-dep τ .Constant.at-natural e .SemiMod._≈m_.*≈* .prop-setoid._≃m_.func-eq ≈-refl

-- The fibre relation respects the setoids on both sides.
body-input-resp : ∀ {Γ' σ} (γ' : Env Γ') (v : Val σ) {s s' x x' z} →
                  s ≈s s' → (∀ k → x k ≈s x' k) → ∀ k →
                  body-input γ' v s x z k ≈s body-input γ' v s' x' z k
body-input-resp γ' v es ecs zero    = es
body-input-resp γ' v es ecs (suc k) =
  +-cong (app-congᵥ (M.in₁ {width-env γ'} {width v}) ecs k) ≈-refl

-- The relation up to control dependence respects the control input's value.
DepRel⊑-resp-ctrl : ∀ τ {v : Val τ} {i : Ix τ} (r : ValRel τ v i) {s s'} {o : ∣ 𝔽 (width v) ∣} {d} →
                    s ≈s s' → DepRel⊑ τ r s o d → DepRel⊑ τ r s' o d
DepRel⊑-resp-ctrl τ {i = i} r es (m , (dm , h)) =
  m , (F.trans τ i (F.+-cong τ i (F.refl τ i) (ctrl-dep τ .at i .SemiMod._⇒_.func-resp-≈ (≈-sym es)))
                   (F.trans τ i dm (ctrl-dep τ .at i .SemiMod._⇒_.func-resp-≈ es)) , h)

DepRel-resp : ∀ τ {v : Val τ} {i : Ix τ} (r : ValRel τ v i) {o o' : ∣ 𝔽 (width v) ∣} {d d' : ∣ Fib τ i ∣} →
              (∀ k → o k ≈s o' k) → F._≈_ τ i d d' → DepRel τ r o d → DepRel τ r o' d'
DepRel-resp unit {unit} r eo ed h k = ≈-trans (≈-sym (eo k)) (≈-trans (h k) (ed k))
DepRel-resp (base s) {const a} r eo ed h k = ≈-trans (≈-sym (eo k)) (≈-trans (h k) (ed k))
DepRel-resp (σ [+] τ) {inl v} {i} (i' , r , ⟪ e ⟫) {d = d} {d'} eo ed (h₀ , h) =
  let ed' = ⟦ σ [+] τ ⟧ .fam .subst {i} {inj₁ i'} e .SemiMod._⇒_.func-resp-≈ ed in
  ≈-trans (≈-sym (eo zero)) (≈-trans h₀ (prop._∧_.proj₁ ed')) ,
  DepRel-resp σ r (λ k → eo (suc k)) (prop._∧_.proj₂ ed') h
DepRel-resp (σ [+] τ) {inr v} {i} (i' , r , ⟪ e ⟫) {d = d} {d'} eo ed (h₀ , h) =
  let ed' = ⟦ σ [+] τ ⟧ .fam .subst {i} {inj₂ i'} e .SemiMod._⇒_.func-resp-≈ ed in
  ≈-trans (≈-sym (eo zero)) (≈-trans h₀ (prop._∧_.proj₁ ed')) ,
  DepRel-resp τ r (λ k → eo (suc k)) (prop._∧_.proj₂ ed') h
DepRel-resp (σ [×] τ) {pair v u} {i , j} (r , r') eo (ed₀ , (ed₁ , ed₂)) (h₀ , (h₁ , h₂)) =
  ≈-trans (≈-sym (eo zero)) (≈-trans h₀ ed₀) ,
  (DepRel-resp σ r (app-congᵥ (M.p₁ {width v} {width u}) (λ k → eo (suc k))) ed₁ h₁ ,
   DepRel-resp τ r' (app-congᵥ (M.p₂ {width v} {width u}) (λ k → eo (suc k))) ed₂ h₂)
DepRel-resp (σ [→] τ) {clo γ' t} {f} r {o} {o'} {d} {d'} eo (ed₀ , ed₂) (h₀ , hc) =
  ≈-trans (≈-sym (eo zero)) (≈-trans h₀ ed₀) ,
  λ s' {v} {j} rv z y hz {u} {U} D →
    DepRel-resp τ (r rv D)
      (app-congᵥ U (body-input-resp γ' v (+-cong ≈-refl (eo zero)) (λ k → eo (suc k))))
      (F.+-cong τ (f .idxf .sfunc j)
         (ctrl-dep τ .at (f .idxf .sfunc j) .SemiMod._⇒_.func-resp-≈ (+-cong ≈-refl (eo zero)))
         (F.+-cong τ (f .idxf .sfunc j)
            (SP.evalΠ (⟦ τ ⟧ .fam indexed-family.[ f .idxf ]) j .SemiMod._⇒_.func-resp-≈
               {proj₂ d} {proj₂ d'} ed₂)
            (F.refl τ (f .idxf .sfunc j) {f .famf .transf j .func y})))
      (hc s' rv z y (DepRel⊑-resp-ctrl σ rv (+-cong ≈-refl (≈-sym (eo zero))) hz) D)

-- Transport of a sum of the control dependence and an element along an index equation.
subst-ctrl-dep+ : ∀ τ {i i' : Ix τ} (e : Setoid._≈_ (⟦ τ ⟧ .idx) i i') s d →
            F._≈_ τ i' (⟦ τ ⟧ .fam .subst e .func (F._+_ τ i (ctrl-dep-at τ i s) d))
                       (F._+_ τ i' (ctrl-dep-at τ i' s) (⟦ τ ⟧ .fam .subst e .func d))
subst-ctrl-dep+ τ {i} {i'} e s d =
  F.trans τ i' (⟦ τ ⟧ .fam .subst e .SemiMod._⇒_.preserve-+ {ctrl-dep-at τ i s} {d})
               (F.+-cong τ i' (ctrl-dep-natural τ e s) (F.refl τ i'))

ap-pair-p₁ : ∀ {m a b} (f : M.Matrix a m) (g : M.Matrix b m) (u : ∣ 𝔽 m ∣) (k : Fin a) →
             ap (M.p₁ {a} {b}) (ap (⟨ f , g ⟩) u) k ≈s ap f u k
ap-pair-p₁ {m} {a} {b} f g u k =
  ≈-trans (≈-sym (app-∘ (M.p₁ {a} {b}) (⟨ f , g ⟩) u k))
          (app-congₘ (HasProducts.pair-p₁ M.products f g) u k)

ap-pair-p₂ : ∀ {m a b} (f : M.Matrix a m) (g : M.Matrix b m) (u : ∣ 𝔽 m ∣) (k : Fin b) →
             ap (M.p₂ {a} {b}) (ap (⟨ f , g ⟩) u) k ≈s ap g u k
ap-pair-p₂ {m} {a} {b} f g u k =
  ≈-trans (≈-sym (app-∘ (M.p₂ {a} {b}) (⟨ f , g ⟩) u k))
          (app-congₘ (HasProducts.pair-p₂ M.products f g) u k)

-- Adding the value's control positions at a value s at the control input on the operational side, and the
-- control dependence on the denotational side, preserves the relation.
ctrl-add : ∀ τ {v : Val τ} {i : Ix τ} (r : ValRel τ v i) (s : Setoid.Carrier A)
           {o : ∣ 𝔽 (width v) ∣} {d : ∣ Fib τ i ∣} → DepRel τ r o d →
           DepRel τ r (λ k → ap (ctrl-of v) (λ _ → s) k +ₛ o k) (F._+_ τ i (ctrl-dep-at τ i s) d)
ctrl-add unit {unit} {i} r s h zero =
  +-cong (≈-trans (ap-ctrl-row {1} s zero) (≈-sym (ctrl-dep-unit i s))) (h zero)
ctrl-add (base σ) {const a} {i} r s h k =
  +-cong (≈-trans (ap-ctrl-row {sort-width σ} s k) (≈-sym (ctrl-dep-base i s k))) (h k)
ctrl-add (σ [+] τ) {inl v} {i} (i' , r , ⟪ e ⟫) s {o} {d} (h₀ , h) =
  let e+ = subst-ctrl-dep+ (σ [+] τ) {i} {inj₁ i'} e s d
      d' = ⟦ σ [+] τ ⟧ .fam .subst {i} {inj₁ i'} e .func d
  in
  ≈-trans (+-cong (ctrl-lift-zero (ctrl-of v) s) h₀)
          (≈-sym (≈-trans (prop._∧_.proj₁ e+) (+-cong (prop._∧_.proj₁ (ctrl-dep-inj₁ {σ} {τ} i' s)) ≈-refl))) ,
  DepRel-resp σ r
    (λ k → +-cong (≈-sym (ctrl-lift-suc (ctrl-of v) s k)) ≈-refl)
    (F.sym σ i' (F.trans σ i' (prop._∧_.proj₂ e+)
                              (F.+-cong σ i' (prop._∧_.proj₂ (ctrl-dep-inj₁ {σ} {τ} i' s)) (F.refl σ i'))))
    (ctrl-add σ r s h)
ctrl-add (σ [+] τ) {inr v} {i} (i' , r , ⟪ e ⟫) s {o} {d} (h₀ , h) =
  let e+ = subst-ctrl-dep+ (σ [+] τ) {i} {inj₂ i'} e s d
  in
  ≈-trans (+-cong (ctrl-lift-zero (ctrl-of v) s) h₀)
          (≈-sym (≈-trans (prop._∧_.proj₁ e+) (+-cong (prop._∧_.proj₁ (ctrl-dep-inj₂ {σ} {τ} i' s)) ≈-refl))) ,
  DepRel-resp τ r
    (λ k → +-cong (≈-sym (ctrl-lift-suc (ctrl-of v) s k)) ≈-refl)
    (F.sym τ i' (F.trans τ i' (prop._∧_.proj₂ e+)
                              (F.+-cong τ i' (prop._∧_.proj₂ (ctrl-dep-inj₂ {σ} {τ} i' s)) (F.refl τ i'))))
    (ctrl-add τ r s h)
ctrl-add (σ [×] τ) {pair v u} {i , j} (r , r') s {o} {d} (h₀ , (h₁ , h₂)) =
  ≈-trans (+-cong (ctrl-lift-zero (⟨ ctrl-of v , ctrl-of u ⟩) s) h₀)
          (+-cong (≈-sym (prop._∧_.proj₁ (ctrl-dep-pair {σ} {τ} i j s))) ≈-refl) ,
  (DepRel-resp σ r
     (λ k → ≈-trans (+-cong (≈-sym (ap-pair-p₁ (ctrl-of v) (ctrl-of u) (λ _ → s) k)) ≈-refl)
              (≈-trans (≈-sym (app-+ (M.p₁ {width v} {width u}) _ _ k))
                       (app-congᵥ (M.p₁ {width v} {width u})
                          (λ l → +-cong (≈-sym (ctrl-lift-suc (⟨ ctrl-of v , ctrl-of u ⟩) s l)) ≈-refl) k)))
     (F.+-cong σ i (F.sym σ i (prop._∧_.proj₁ (prop._∧_.proj₂ (ctrl-dep-pair {σ} {τ} i j s)))) (F.refl σ i))
     (ctrl-add σ r s h₁) ,
   DepRel-resp τ r'
     (λ k → ≈-trans (+-cong (≈-sym (ap-pair-p₂ (ctrl-of v) (ctrl-of u) (λ _ → s) k)) ≈-refl)
              (≈-trans (≈-sym (app-+ (M.p₂ {width v} {width u}) _ _ k))
                       (app-congᵥ (M.p₂ {width v} {width u})
                          (λ l → +-cong (≈-sym (ctrl-lift-suc (⟨ ctrl-of v , ctrl-of u ⟩) s l)) ≈-refl) k)))
     (F.+-cong τ j (F.sym τ j (prop._∧_.proj₂ (prop._∧_.proj₂ (ctrl-dep-pair {σ} {τ} i j s)))) (F.refl τ j))
     (ctrl-add τ r' s h₂))
ctrl-add (σ [→] τ) {clo γ' t} {f} r s {o} {d} (h₀ , hc) =
  ≈-trans (+-cong (ctrl-lift-zero {width-env γ'} εₘ s) h₀)
          (+-cong (≈-sym (prop._∧_.proj₁ (ctrl-dep-clo {σ} {τ} f s))) ≈-refl) ,
  λ s' {v} {j} rv z y hz {u} {U} D →
    let e₀ : ((s' +ₛ (c ·ₛ s)) +ₛ o zero) ≈s (s' +ₛ (ap (ctrl-of (clo γ' t)) (λ _ → s) zero +ₛ o zero))
        e₀ = ≈-trans +-assoc (+-cong ≈-refl (+-cong (≈-sym (ctrl-lift-zero {width-env γ'} εₘ s)) ≈-refl))
    in
    DepRel-resp τ (r rv D)
      (app-congᵥ U (body-input-resp γ' v e₀
         (λ k → ≈-sym (≈-trans (+-cong (ctrl-lift-suc {width-env γ'} εₘ s k) ≈-refl)
                               (≈-trans (+-cong (app-εₘ {width-env γ'} {1} (λ _ → s) k) ≈-refl) +-lunit)))))
      (F.+-cong τ (f .idxf .sfunc j)
         (ctrl-dep τ .at (f .idxf .sfunc j) .SemiMod._⇒_.func-resp-≈ e₀)
         (F.+-cong τ (f .idxf .sfunc j)
            (SP.evalΠ (⟦ τ ⟧ .fam indexed-family.[ f .idxf ]) j .SemiMod._⇒_.func-resp-≈
               {proj₂ d} {proj₂ (F._+_ (σ [→] τ) f (ctrl-dep-at (σ [→] τ) f s) d)}
               (P.sym {proj₂ (F._+_ (σ [→] τ) f (ctrl-dep-at (σ [→] τ) f s) d)} {proj₂ d}
                 (P.trans {proj₂ (F._+_ (σ [→] τ) f (ctrl-dep-at (σ [→] τ) f s) d)} {P._+_ P.ε (proj₂ d)} {proj₂ d}
                   (P.+-cong {proj₂ (ctrl-dep-at (σ [→] τ) f s)} {P.ε} {proj₂ d} {proj₂ d}
                      (prop._∧_.proj₂ (ctrl-dep-clo {σ} {τ} f s)) (P.refl {proj₂ d}))
                   (P.+-lunit {proj₂ d}))))
            (F.refl τ (f .idxf .sfunc j) {f .famf .transf j .func y})))
      (hc (s' +ₛ (c ·ₛ s)) rv z y (DepRel⊑-resp-ctrl σ rv (≈-sym e₀) hz) D)
  where module P = Semimodule (model.FE._⟶_ ⟦ σ ⟧ ⟦ τ ⟧ .fam .fm f)

-- Looking up a variable in a related environment.
lookup-val : ∀ {Γ τ} (x : Γ ∋ τ) {γ : Env Γ} {gi} → EnvValRel γ gi →
             ValRel τ (lookup x γ) (LI.⟦ x ⟧var .idxf .sfunc gi)
lookup-val zero     (rγ · r) = r
lookup-val (succ x) (rγ · r) = lookup-val x rγ

DepRel⊑-resp : ∀ τ {v : Val τ} {i : Ix τ} (r : ValRel τ v i) s {o o' : ∣ 𝔽 (width v) ∣} {d} →
               (∀ k → o k ≈s o' k) → DepRel⊑ τ r s o d → DepRel⊑ τ r s o' d
DepRel⊑-resp τ {i = i} r s eo (m , (dm , h)) = m , (dm , DepRel-resp τ r eo (F.refl τ i) h)

lookup-dep : ∀ {Γ τ} (x : Γ ∋ τ) {γ : Env Γ} {gi} (rγ : EnvValRel γ gi) s xs g →
             EnvDepRel rγ s xs g →
             DepRel⊑ τ (lookup-val x rγ) s (ap (proj-var x γ) xs) (LI.⟦ x ⟧var .famf .transf gi .func g)
lookup-dep zero (rγ · r) s xs g (_ , h) = h
lookup-dep {τ = τ} (succ x) {γ · v} {gi , i} (rγ · r) s xs g (h , _) =
  DepRel⊑-resp τ (lookup-val x rγ) s
    (λ k → ≈-sym (app-∘ (proj-var x γ) (M.p₁ {width-env γ} {width v}) xs k))
    (lookup-dep x rγ s (ap (M.p₁ {width-env γ} {width v}) xs) (proj₁ g) h)

-- Dependence below the control dependence is absorbed by it, so a relation up to such dependence
-- becomes a relation once the control positions and the control dependence are added.
⊑-absorb : ∀ τ (i : Ix τ) s (d m : ∣ Fib τ i ∣) → F._⊑_ τ i m (ctrl-dep-at τ i s) →
         F._≈_ τ i (F._+_ τ i (ctrl-dep-at τ i s) (F._+_ τ i d m)) (F._+_ τ i (ctrl-dep-at τ i s) d)
⊑-absorb τ i s d m dm =
  F.trans τ i (F.+-cong τ i (F.refl τ i) (F.+-comm τ i))
  (F.trans τ i (F.sym τ i (F.+-assoc τ i))
  (F.trans τ i (F.+-cong τ i (F.trans τ i (F.+-comm τ i) dm) (F.refl τ i))
               (F.refl τ i)))

DepRel⊑-ctrl : ∀ τ {v : Val τ} {i : Ix τ} (r : ValRel τ v i) s {o : ∣ 𝔽 (width v) ∣} {d} →
               DepRel⊑ τ r s o d →
               DepRel τ r (λ k → ap (ctrl-of v) (λ _ → s) k +ₛ o k) (F._+_ τ i (ctrl-dep-at τ i s) d)
DepRel⊑-ctrl τ {i = i} r s {o} {d} (m , (dm , h)) =
  DepRel-resp τ r (λ k → ≈-refl) (⊑-absorb τ i s d m dm) (ctrl-add τ r s h)

-- Related values are related at equal indices.
ValRel-resp : ∀ τ {v : Val τ} {i i' : Ix τ} → Setoid._≈_ (⟦ τ ⟧ .idx) i i' → ValRel τ v i → ValRel τ v i'
ValRel-resp unit {unit} e r = tt
ValRel-resp (base σ) {const a} {i} {i'} e ⟪ e₀ ⟫ =
  ⟪ Setoid.trans (sort-index σ) {i'} {i} {a} (Setoid.sym (sort-index σ) {i} {i'} e) e₀ ⟫
ValRel-resp (σ [+] τ) {inl v} {i} {i'} e (i₀ , r , ⟪ e₀ ⟫) =
  i₀ , r , ⟪ Setoid.trans (⟦ σ [+] τ ⟧ .idx) {i'} {i} {inj₁ i₀} (Setoid.sym (⟦ σ [+] τ ⟧ .idx) {i} {i'} e) e₀ ⟫
ValRel-resp (σ [+] τ) {inr v} {i} {i'} e (i₀ , r , ⟪ e₀ ⟫) =
  i₀ , r , ⟪ Setoid.trans (⟦ σ [+] τ ⟧ .idx) {i'} {i} {inj₂ i₀} (Setoid.sym (⟦ σ [+] τ ⟧ .idx) {i} {i'} e) e₀ ⟫
ValRel-resp (σ [×] τ) {pair v u} {i , j} {i' , j'} (e₁ , e₂) (r , r') = ValRel-resp σ e₁ r , ValRel-resp τ e₂ r'
ValRel-resp (σ [→] τ) {clo γ' t} {f} {f'} e r {v} {j} rv {u} {U} D =
  ValRel-resp τ (e .FD._≃_.idxf-eq .prop-setoid._≃m_.func-eq (Setoid.refl (⟦ σ ⟧ .idx) {j})) (r rv D)


-- Reading the model's constructions elementwise: a pairing through the biproduct is the pair of
-- the components, the lifted action keeps the root and acts on the payload, and eliminating a
-- root applies the continuation to the payload and the control dependence to the root.
module SMBP = HasProducts (cmon-enriched.biproducts→products SemiMod.cmon-enriched SemiMod.biproduct)

bpair-elt : ∀ {X Y Z : Semimodule} (f : X ⇒ Y) (g : X ⇒ Z) (x : ∣ X ∣) →
            Semimodule._≈_ (SemiMod._⊕_ Y Z) (SMBP.pair f g .func x) (f .func x , g .func x)
bpair-elt {X} {Y} {Z} f g x = m-runit Y , Semimodule.+-lunit Z

Fpair-elt : ∀ {X Y Z : Obj} (f : Mor X Y) (g : Mor X Z) (x : Setoid.Carrier (X .idx)) (z : ∣ X .fam .fm x ∣) →
            Semimodule._≈_ (HasProducts.prod FD.products Y Z .fam .fm (f .idxf .sfunc x , g .idxf .sfunc x))
              (HasProducts.pair FD.products f g .famf .transf x .func z)
              (f .famf .transf x .func z , g .famf .transf x .func z)
Fpair-elt f g x z = bpair-elt (f .famf .transf x) (g .famf .transf x) z

elim-root-elt : ∀ {G X Y : Semimodule} (k : SemiMod.𝕀 ⇒ Y) (r : SemiMod._⊕_ G X ⇒ Y)
                (γe : ∣ G ∣) (a : Setoid.Carrier A) (y : ∣ X ∣) →
                Semimodule._≈_ Y (Ls.elim-root k r .func (γe , (a , y)))
                                 (Semimodule._+_ Y (r .func (γe , y)) (k .func a))
elim-root-elt {G} {X} {Y} k r γe a y =
  Semimodule.+-cong Y
    (r .SemiMod._⇒_.func-resp-≈
       (Semimodule.trans (SemiMod._⊕_ G X)
          (bpair-elt {SemiMod._⊕_ G (Ls.L X)} {G} {X}
             (SemiMod._∘_ (SemiMod.id G) (SemiMod.p₁ {G} {Ls.L X}))
             (SemiMod._∘_ (Ls.payload-L {X}) (SemiMod.p₂ {G} {Ls.L X})) (γe , (a , y)))
          (Semimodule.refl G {γe} , Semimodule.+-lunit X {y})))
    (k .SemiMod._⇒_.func-resp-≈ +-runit)

elimF-elt : ∀ {Γ' X C : Obj} (cC : Constant C) (f : Mor (HasProducts.prod FD.products Γ' X) C)
            {γi : Setoid.Carrier (Γ' .idx)} {xi : Setoid.Carrier (X .idx)}
            (γe : ∣ Γ' .fam .fm γi ∣) (a : Setoid.Carrier A) (y : ∣ X .fam .fm xi ∣) →
            Semimodule._≈_ (C .fam .fm (f .idxf .sfunc (γi , xi)))
              (FD.elimF cC f .famf .transf (γi , xi) .func (γe , (a , y)))
              (Semimodule._+_ (C .fam .fm (f .idxf .sfunc (γi , xi)))
                (f .famf .transf (γi , xi) .func (γe , y))
                (cC .at (f .idxf .sfunc (γi , xi)) .func a))
elimF-elt cC f {γi} {xi} γe a y = elim-root-elt (cC .at (f .idxf .sfunc (γi , xi))) (f .famf .transf (γi , xi)) γe a y

-- Being below the control dependence is monotone in the control input's value, and a relation is a relation up to
-- zero.
ctrl-dep-linear : ∀ τ (i : Ix τ) s s' →
            F._≈_ τ i (ctrl-dep-at τ i (s +ₛ s')) (F._+_ τ i (ctrl-dep-at τ i s) (ctrl-dep-at τ i s'))
ctrl-dep-linear τ i s s' = ctrl-dep τ .at i .SemiMod._⇒_.preserve-+ {s} {s'}

ctrl-dep-c : ∀ τ (i : Ix τ) s → F._≈_ τ i (ctrl-dep-at τ i (c ·ₛ s)) (ctrl-dep-at τ i s)
ctrl-dep-c τ i s =
  LI.ty-unit τ (λ ()) (λ ()) .at i .SemiMod._⇒_.func-resp-≈
    (+-cong (≈-trans (≈-sym Sc.·-assoc) (·-cong c-idem ≈-refl)) ≈-refl)

⊑ctrl-dep-mono : ∀ τ (i : Ix τ) s s' m → F._⊑_ τ i m (ctrl-dep-at τ i s) → F._⊑_ τ i m (ctrl-dep-at τ i (s' +ₛ (c ·ₛ s)))
⊑ctrl-dep-mono τ i s s' m dm =
  F.trans τ i (F.+-cong τ i (F.refl τ i) (F.trans τ i (ctrl-dep-linear τ i s' (c ·ₛ s))
                                                      (F.+-cong τ i (F.refl τ i) (ctrl-dep-c τ i s))))
  (F.trans τ i (F.+-cong τ i (F.refl τ i) (F.+-comm τ i))
  (F.trans τ i (F.sym τ i (F.+-assoc τ i))
  (F.trans τ i (F.+-cong τ i dm (F.refl τ i))
  (F.trans τ i (F.+-comm τ i)
  (F.sym τ i (F.trans τ i (ctrl-dep-linear τ i s' (c ·ₛ s))
                          (F.+-cong τ i (F.refl τ i) (ctrl-dep-c τ i s))))))))

DepRel⊑-mono : ∀ τ {v : Val τ} {i : Ix τ} (r : ValRel τ v i) s s' {o d} →
               DepRel⊑ τ r s o d → DepRel⊑ τ r (s' +ₛ (c ·ₛ s)) o d
DepRel⊑-mono τ {i = i} r s s' (m , (dm , h)) = m , (⊑ctrl-dep-mono τ i s s' m dm , h)

EnvDepRel-mono : ∀ {Γ} {γ : Env Γ} {gi} (rγ : EnvValRel γ gi) s s' {x g} →
                 EnvDepRel rγ s x g → EnvDepRel rγ (s' +ₛ (c ·ₛ s)) x g
EnvDepRel-mono emp s s' rel = prop.tt
EnvDepRel-mono (rγ · r) s s' (rel , h) = EnvDepRel-mono rγ s s' rel , DepRel⊑-mono _ r s s' h

-- Splitting a concatenated environment vector.
ap-p₁-++ : ∀ {m n} (x : ∣ 𝔽 m ∣) (z : ∣ 𝔽 n ∣) k →
           ap (M.p₁ {m} {n}) (λ l → ap (M.in₁ {m} {n}) x l +ₛ ap (M.in₂ {m} {n}) z l) k ≈s x k
ap-p₁-++ {m} {n} x z k =
  ≈-trans (app-+ (M.p₁ {m} {n}) _ _ k)
          (≈-trans (+-cong (≈-trans (≈-sym (app-∘ (M.p₁ {m} {n}) (M.in₁ {m} {n}) x k))
                                    (≈-trans (app-congₘ (M.id-1 m n) x k) (app-I x k)))
                           (≈-trans (≈-sym (app-∘ (M.p₁ {m} {n}) (M.in₂ {m} {n}) z k))
                                    (≈-trans (app-congₘ (M.zero-1 m n) z k) (app-εₘ z k))))
                   +-runit)

ap-p₂-++ : ∀ {m n} (x : ∣ 𝔽 m ∣) (z : ∣ 𝔽 n ∣) k →
           ap (M.p₂ {m} {n}) (λ l → ap (M.in₁ {m} {n}) x l +ₛ ap (M.in₂ {m} {n}) z l) k ≈s z k
ap-p₂-++ {m} {n} x z k =
  ≈-trans (app-+ (M.p₂ {m} {n}) _ _ k)
          (≈-trans (+-cong (≈-trans (≈-sym (app-∘ (M.p₂ {m} {n}) (M.in₁ {m} {n}) x k))
                                    (≈-trans (app-congₘ (M.zero-2 m n) x k) (app-εₘ x k)))
                           (≈-trans (≈-sym (app-∘ (M.p₂ {m} {n}) (M.in₂ {m} {n}) z k))
                                    (≈-trans (app-congₘ (M.id-2 m n) z k) (app-I z k))))
                   +-lunit)

EnvDepRel-resp : ∀ {Γ} {γ : Env Γ} {gi} (rγ : EnvValRel γ gi) s {x x' g} →
                 (∀ k → x k ≈s x' k) → EnvDepRel rγ s x g → EnvDepRel rγ s x' g
EnvDepRel-resp emp s ex rel = prop.tt
EnvDepRel-resp (_·_ {γ = γ} {v = v} rγ r) s ex (rel , h) =
  EnvDepRel-resp rγ s (app-congᵥ (M.p₁ {width-env γ} {width v}) ex) rel ,
  DepRel⊑-resp _ r s (app-congᵥ (M.p₂ {width-env γ} {width v}) ex) h

-- The weight times s absorbs any multiple of s.
cs-absorb : ∀ s e → ((c ·ₛ s) +ₛ ((s ·ₛ c) ·ₛ e)) ≈s (c ·ₛ s)
cs-absorb s e =
  ≈-trans (+-cong ·-comm Sc.·-assoc)
  (≈-trans (≈-sym Sc.·-+-distribₗ)
  (≈-trans (·-cong ≈-refl (≈-trans +-comm (c-absorb e))) ·-comm))

-- The control dependence at s is below itself.
ctrl-dep-root : ∀ τ (i : Ix τ) s → F._⊑_ τ i (ctrl-dep-at τ i s) (ctrl-dep-at τ i s)
ctrl-dep-root τ i s = F.trans τ i (F.sym τ i (ctrl-dep-linear τ i s s))
                            (ctrl-dep τ .at i .SemiMod._⇒_.func-resp-≈ (+-idem s))

-- The control dependence at the weighted s plus itself and a further weight: the one at s plus the
-- one at the further weight.
ctrl-dep-double : ∀ τ (i : Ix τ) s a → F._≈_ τ i (ctrl-dep-at τ i ((c ·ₛ s) +ₛ ((c ·ₛ s) +ₛ a))) (F._+_ τ i (ctrl-dep-at τ i s) (ctrl-dep-at τ i a))
ctrl-dep-double τ i s a =
  F.trans τ i (ctrl-dep-linear τ i (c ·ₛ s) ((c ·ₛ s) +ₛ a))
  (F.trans τ i (F.+-cong τ i (ctrl-dep-c τ i s) (F.trans τ i (ctrl-dep-linear τ i (c ·ₛ s) a) (F.+-cong τ i (ctrl-dep-c τ i s) (F.refl τ i))))
  (F.trans τ i (F.sym τ i (F.+-assoc τ i)) (F.+-cong τ i (ctrl-dep-root τ i s) (F.refl τ i))))

-- Reading the first position of a lifted vector, and its tail, by the projections.
built-zero : ∀ {Γ} {γ : Env Γ} {n} (R' : M.Matrix n (suc (width-env γ))) s x →
             ap (built-out γ n +ₘ (M.in₂ {1} ∘ R')) (inputs γ s x) zero ≈s (c ·ₛ s)
built-zero {γ = γ} {n} R' s x =
  ≈-trans (app-+ₘ (built-out γ n) (M.in₂ {1} ∘ R') (inputs γ s x) zero)
  (≈-trans (+-cong (≈-trans (app-∘ (M.in₁ {1} {n}) wctrl (inputs γ s x) zero)
                            (≈-trans (ap-in₁-zero {n} (ap wctrl (inputs γ s x)))
                                     (ap-wctrl {width-env γ} {1} (inputs γ s x) zero)))
                   (≈-trans (app-∘ (M.in₂ {1} {n}) R' (inputs γ s x) zero)
                            (ap-in₂-zero {n} (ap R' (inputs γ s x)))))
           +-runit)

built-suc : ∀ {Γ} {γ : Env Γ} {n} (R' : M.Matrix n (suc (width-env γ))) s x k →
            ap (built-out γ n +ₘ (M.in₂ {1} ∘ R')) (inputs γ s x) (suc k) ≈s ap R' (inputs γ s x) k
built-suc {γ = γ} {n} R' s x k =
  ≈-trans (app-+ₘ (built-out γ n) (M.in₂ {1} ∘ R') (inputs γ s x) (suc k))
  (≈-trans (+-cong (≈-trans (app-∘ (M.in₁ {1} {n}) wctrl (inputs γ s x) (suc k))
                            (ap-in₁-suc {n} (ap wctrl (inputs γ s x)) k))
                   (≈-trans (app-∘ (M.in₂ {1} {n}) R' (inputs γ s x) (suc k))
                            (ap-in₂-suc {n} (ap R' (inputs γ s x)) k)))
           +-lunit)

-- Transport along a reflexivity proof is the identity.
subst-refl : ∀ τ {i : Ix τ} (e : Setoid._≈_ (⟦ τ ⟧ .idx) i i) (d : ∣ Fib τ i ∣) →
             F._≈_ τ i (⟦ τ ⟧ .fam .subst e .func d) d
subst-refl τ {i} e d = ⟦ τ ⟧ .fam .indexed-family.Fam.refl* .SemiMod._≈m_.*≈* .prop-setoid._≃m_.func-eq (F.refl τ i {d})

-- A base sort's fibres do not vary with the index, so its transports are the identity.
subst-base : ∀ {σ} {i i' : Ix (base σ)} (e : Setoid._≈_ (⟦ base σ ⟧ .idx) i i')
             (d : ∣ Fib (base σ) i ∣) (k : Fin (sort-width σ)) →
             ⟦ base σ ⟧ .fam .subst e .func d k ≈s d k
subst-base {σ} e d k = Σ-unit {sort-width σ} k d

-- Transporting a relation along an index equation.
DepRel-transport : ∀ τ {v : Val τ} {i i' : Ix τ} (E : Setoid._≈_ (⟦ τ ⟧ .idx) i i') (r : ValRel τ v i)
                   {o : ∣ 𝔽 (width v) ∣} {d : ∣ Fib τ i ∣} →
                   DepRel τ r o d → DepRel τ (ValRel-resp τ E r) o (⟦ τ ⟧ .fam .subst E .func d)
DepRel-transport unit {unit} {i} {i'} E r {o} {d} h k =
  ≈-trans (h k) (≈-sym (subst-refl unit {i} E d k))
DepRel-transport (base σ) {const a} {i} {i'} E r {o} {d} h k =
  ≈-trans (h k) (≈-sym (subst-base {σ} {i} {i'} E d k))
DepRel-transport (σ [+] τ) {inl v} {i} {i'} E (i₀ , r₀ , ⟪ e₀ ⟫) {o} {d} (h₀ , h) =
  let e' = Setoid.trans (⟦ σ [+] τ ⟧ .idx) {i'} {i} {inj₁ i₀} (Setoid.sym (⟦ σ [+] τ ⟧ .idx) {i} {i'} E) e₀
      comp = ⟦ σ [+] τ ⟧ .fam .indexed-family.Fam.trans* {i} {i'} {inj₁ i₀} e' E
               .SemiMod._≈m_.*≈* .prop-setoid._≃m_.func-eq (F.refl (σ [+] τ) i {d})
  in
  ≈-trans h₀ (prop._∧_.proj₁ comp) ,
  DepRel-resp σ r₀ (λ k → ≈-refl) (prop._∧_.proj₂ comp) h
DepRel-transport (σ [+] τ) {inr v} {i} {i'} E (i₀ , r₀ , ⟪ e₀ ⟫) {o} {d} (h₀ , h) =
  let e' = Setoid.trans (⟦ σ [+] τ ⟧ .idx) {i'} {i} {inj₂ i₀} (Setoid.sym (⟦ σ [+] τ ⟧ .idx) {i} {i'} E) e₀
      comp = ⟦ σ [+] τ ⟧ .fam .indexed-family.Fam.trans* {i} {i'} {inj₂ i₀} e' E
               .SemiMod._≈m_.*≈* .prop-setoid._≃m_.func-eq (F.refl (σ [+] τ) i {d})
  in
  ≈-trans h₀ (prop._∧_.proj₁ comp) ,
  DepRel-resp τ r₀ (λ k → ≈-refl) (prop._∧_.proj₂ comp) h
DepRel-transport (σ [×] τ) {pair v u} {i , j} {i' , j'} (E₁ , E₂) (r₁ , r₂) {o} {d} (h₀ , (h₁ , h₂)) =
  ≈-trans h₀ (≈-sym +-runit) ,
  (DepRel-resp σ (ValRel-resp σ E₁ r₁) (λ k → ≈-refl)
     (F.sym σ i' (F.trans σ i' (F.+-lunit σ i') (m-runit (Fib σ i'))))
     (DepRel-transport σ E₁ r₁ h₁) ,
   DepRel-resp τ (ValRel-resp τ E₂ r₂) (λ k → ≈-refl)
     (F.sym τ j' (F.trans τ j' (F.+-lunit τ j') (F.+-lunit τ j')))
     (DepRel-transport τ E₂ r₂ h₂))
DepRel-transport (σ [→] τ) {clo γ' t} {f} {f'} E r {o} {d} (h₀ , hc) =
  ≈-trans h₀ (≈-sym +-runit) ,
  λ s' {v} {j} rv z y hz {u} {U} D →
    DepRel-resp τ (ValRel-resp τ (Ej j) (r rv D)) (λ k → ≈-refl)
      (F.trans τ (f' .idxf .sfunc j)
         (⟦ τ ⟧ .fam .subst (Ej j) .SemiMod._⇒_.preserve-+ {ctrl-dep-at τ (f .idxf .sfunc j) (s' +ₛ o zero)} {_})
      (F.+-cong τ (f' .idxf .sfunc j) (ctrl-dep-natural τ (Ej j) (s' +ₛ o zero))
      (F.trans τ (f' .idxf .sfunc j)
         (⟦ τ ⟧ .fam .subst (Ej j) .SemiMod._⇒_.preserve-+ {_} {_})
      (F.+-cong τ (f' .idxf .sfunc j) (eval-part j) (arg-part j y)))))
      (DepRel-transport τ (Ej j) (r rv D) (hc s' rv z y hz D))
  where
  P = model.FE._⟶_ ⟦ σ ⟧ ⟦ τ ⟧
  Ej : ∀ j → Setoid._≈_ (⟦ τ ⟧ .idx) (f .idxf .sfunc j) (f' .idxf .sfunc j)
  Ej j = E .FD._≃_.idxf-eq .prop-setoid._≃m_.func-eq (Setoid.refl (⟦ σ ⟧ .idx) {j})
  hmap = indexed-family.reindex-≈ {P = ⟦ τ ⟧ .fam} (f .idxf) (f' .idxf) (E .FD._≃_.idxf-eq)
  eval-part : ∀ j → F._≈_ τ (f' .idxf .sfunc j)
                (⟦ τ ⟧ .fam .subst (Ej j) .func (SP.evalΠ (⟦ τ ⟧ .fam indexed-family.[ f .idxf ]) j .func (proj₂ d)))
                (SP.evalΠ (⟦ τ ⟧ .fam indexed-family.[ f' .idxf ]) j .func
                   (proj₂ (⟦ σ [→] τ ⟧ .fam .subst {f} {f'} E .func d)))
  eval-part j =
    F.trans τ (f' .idxf .sfunc j)
      (F.sym τ (f' .idxf .sfunc j)
         (SP.lambda-eval {A = ⟦ σ ⟧ .idx} {P = ⟦ τ ⟧ .fam indexed-family.[ f' .idxf ]}
            {x = P .fam .fm f}
            {f = indexed-family._∘f_ {A = ⟦ σ ⟧ .idx}
                   {P = indexed-family.constantFam (⟦ σ ⟧ .idx) SemiMod.cat (P .fam .fm f)}
                   {Q = ⟦ τ ⟧ .fam indexed-family.[ f .idxf ]} {R = ⟦ τ ⟧ .fam indexed-family.[ f' .idxf ]}
                   hmap (SP.evalΠf {A = ⟦ σ ⟧ .idx} (⟦ τ ⟧ .fam indexed-family.[ f .idxf ]))} j
            .SemiMod._≈m_.*≈* .prop-setoid._≃m_.func-eq {proj₂ d} {proj₂ d} (Semimodule.refl (P .fam .fm f) {proj₂ d})))
      (SP.evalΠ (⟦ τ ⟧ .fam indexed-family.[ f' .idxf ]) j .SemiMod._⇒_.func-resp-≈
         {SP.Π-map hmap .func (proj₂ d)} {proj₂ (⟦ σ [→] τ ⟧ .fam .subst {f} {f'} E .func d)}
         (Semimodule.sym (P .fam .fm f') {proj₂ (⟦ σ [→] τ ⟧ .fam .subst {f} {f'} E .func d)} {SP.Π-map hmap .func (proj₂ d)}
            (Semimodule.+-lunit (P .fam .fm f') {SP.Π-map hmap .func (proj₂ d)})))
  arg-part : ∀ j (y : ∣ Fib σ j ∣) →
             F._≈_ τ (f' .idxf .sfunc j) (⟦ τ ⟧ .fam .subst (Ej j) .func (f .famf .transf j .func y))
                                        (f' .famf .transf j .func y)
  arg-part j y = E .FD._≃_.famf-eq .indexed-family._≃f_.transf-eq {j} .SemiMod._≈m_.*≈* .prop-setoid._≃m_.func-eq
                   (Semimodule.refl (Fib σ j) {y})

