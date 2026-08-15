{-# OPTIONS --prop --postfix-projections #-}

-- Agreement between the operational relation and the higher-order model, on the fragment without
-- μ-types and primitives, as a logical relation. A value is related to an index of its type's
-- interpretation by recursion on the type, behaviourally at arrow types: for related arguments and
-- any derivation of the body, the result is related. Over that, a dependence vector on the value's
-- positions is related to an element of the fibre: at first-order types position by position, at
-- arrow types the root exactly and the payload through application, comparing the body's
-- dependence through the closure's cells and the argument with the evaluation of the payload and
-- the index's fibre map at the argument. Inputs are a source weight and an environment vector,
-- and the environment relation lets a cell carry a control mark dominated by the source, which is
-- how the operational semantics marks values inside a branch where the interpretation marks the
-- branch's result once. The fundamental lemma, by induction on the term over all derivations,
-- says the relation applied to the inputs is related to the term's fibre map at the environment's
-- denotation plus the elimination constant at the source. The absorption of marks needs the
-- elimination weight to be idempotent and to absorb its multiples under addition, as in a lattice.
open import Level using (0ℓ; lift)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import prop
open import prop using (_∧_; ∃; ∃ₛ; Prf; ⟪_⟫; _,_)
open import prop-setoid using (Setoid; IsEquivalence)
open import commutative-semiring using (CommutativeSemiring)
open import signature using (Signature)
open import primitives using (Primitives)
open import categories using (Category; HasProducts; HasTerminal; HasWeakExponentials; HasStrongCoproducts)
open import cmon-enriched using (CMonEnriched; Biproduct)
import indexed-family
open import indexed-family using (HasSetoidProducts)
import matrix
import semimodule
import ho-model
import language-interpretation

module ho-agreement
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A) (elim-weight : Setoid.Carrier A)
  (Sig : Signature 0ℓ) (𝒫 : Primitives S Sig)
  (let module Sc = CommutativeSemiring S)
  -- The elimination weight is idempotent and absorbs its multiples.
  (w-idem : Setoid._≈_ A (elim-weight Sc.· elim-weight) elim-weight)
  (w-absorb : ∀ x → Setoid._≈_ A ((elim-weight Sc.· x) Sc.+ elim-weight) elim-weight)
  where

open Signature Sig
open Primitives 𝒫
open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.evaluation Sig S 𝒫 elim-weight

module model = ho-model S elim-weight
module interp = model.interp Sig 𝒫
open model using (𝔽; mat; ι1-fwd; ι1-bwd; module Ls; module SemiMod)
open SemiMod using (Semimodule; _⇒_)
open Semimodule using () renaming (Carrier to ∣_∣)
open SemiMod._⇒_ using (func)

private
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
  interp.δ∅𝒟 interp.𝒟𝟙ty interp.𝒟unit-pt interp.𝒟-Sig-model model.elim-weight-endo
  (λ {X} {Y} → model.exp-const {X} {Y}) interp.𝒟𝟙ty-const interp.𝒟-sort-const

open LI using (⟦_⟧ty; ⟦_⟧ctxt; ⟦_⟧tm; elim-const; ty-unit)
open Constant using (at)

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

-- The fragment: no μ-types, no primitives.
data CoreTm : ∀ {Γ τ} → Γ ⊢ τ → Set where
  var  : ∀ {Γ τ} (x : Γ ∋ τ) → CoreTm (var x)
  unit : ∀ {Γ} → CoreTm (unit {Γ})
  inl  : ∀ {Γ τ₁ τ₂} {t : Γ ⊢ τ₁} → CoreTm t → CoreTm (inl {τ₂ = τ₂} t)
  inr  : ∀ {Γ τ₁ τ₂} {t : Γ ⊢ τ₂} → CoreTm t → CoreTm (inr {τ₁ = τ₁} t)
  case : ∀ {Γ τ₁ τ₂ τ} {s : Γ ⊢ τ₁ [+] τ₂} {t₁ : Γ ▸ τ₁ ⊢ τ} {t₂ : Γ ▸ τ₂ ⊢ τ} →
         CoreTm s → CoreTm t₁ → CoreTm t₂ → CoreTm (case s t₁ t₂)
  pair : ∀ {Γ τ₁ τ₂} {s : Γ ⊢ τ₁} {t : Γ ⊢ τ₂} → CoreTm s → CoreTm t → CoreTm (pair s t)
  fst  : ∀ {Γ τ₁ τ₂} {t : Γ ⊢ τ₁ [×] τ₂} → CoreTm t → CoreTm (fst t)
  snd  : ∀ {Γ τ₁ τ₂} {t : Γ ⊢ τ₁ [×] τ₂} → CoreTm t → CoreTm (snd t)
  lam  : ∀ {Γ σ τ} {t : Γ ▸ σ ⊢ τ} → CoreTm t → CoreTm (lam t)
  app  : ∀ {Γ σ τ} {s : Γ ⊢ σ [→] τ} {t : Γ ⊢ σ} → CoreTm s → CoreTm t → CoreTm (app s t)

-- Values related to indices, by recursion on the type. A closure is related to a fibre map of the
-- exponential when, for every related argument and every derivation of the body at it, the result
-- is related to the map's index at the argument.
RelV : ∀ τ → Val τ → Ix τ → Set
RelV unit unit i = ⊤
RelV (base s) v i = ⊥
RelV (σ [+] τ) (inl v) i = Σ (Ix σ) λ i' → RelV σ v i' × Prf (Setoid._≈_ (⟦ σ [+] τ ⟧ .idx) i (inj₁ i'))
RelV (σ [+] τ) (inr v) i = Σ (Ix τ) λ i' → RelV τ v i' × Prf (Setoid._≈_ (⟦ σ [+] τ ⟧ .idx) i (inj₂ i'))
RelV (σ [×] τ) (pair v u) (i , j) = RelV σ v i × RelV τ u j
RelV (σ [→] τ) (clo γ' t) f =
  ∀ {v : Val σ} {j : Ix σ} → RelV σ v j → ∀ {u U} → γ' · v , t ⇓ u [ U ] → RelV τ u (f .idxf .sfunc j)
RelV (μ τ) v i = ⊥

-- The vector over the body's inputs at an application: a source weight, then the closure's cells
-- and the argument as the environment.
body-input : ∀ {Γ' σ} (γ' : Env Γ') (v : Val σ) → Setoid.Carrier A →
             ∣ 𝔽 (width-env γ') ∣ → ∣ 𝔽 (width v) ∣ → ∣ 𝔽 (suc (width-env γ' + width v)) ∣
body-input γ' v s c z zero    = s
body-input γ' v s c z (suc k) =
  Semimodule._+_ (𝔽 (width-env γ' + width v))
    (mat (M.in₁ {width-env γ'} {width v}) .func c)
    (mat (M.in₂ {width-env γ'} {width v}) .func z) k

-- A dependence vector on a value's positions against an element of the fibre at a related index.
-- At an arrow type the root agrees, and for any further source weight, any related argument and
-- any derivation of the body, the body's dependence through the root and the further weight as
-- source and the cells and argument as environment agrees with the elimination constant at that
-- source plus the payload evaluated at the argument plus the index's fibre map at the argument.
RelF : ∀ τ {v : Val τ} {i : Ix τ} → RelV τ v i → ∣ 𝔽 (width v) ∣ → ∣ Fib τ i ∣ → Prop
RelF unit {unit} {i} r o d = Semimodule._≈_ (Fib unit i) o d
RelF (σ [+] τ) {inl v} {i} (i' , r , ⟪ e ⟫) o d =
  let d' = ⟦ σ [+] τ ⟧ .fam .subst {i} {inj₁ i'} e .func d in
  (o zero ≈A proj₁ d') ∧ RelF σ r (λ k → o (suc k)) (proj₂ d')
RelF (σ [+] τ) {inr v} {i} (i' , r , ⟪ e ⟫) o d =
  let d' = ⟦ σ [+] τ ⟧ .fam .subst {i} {inj₂ i'} e .func d in
  (o zero ≈A proj₁ d') ∧ RelF τ r (λ k → o (suc k)) (proj₂ d')
RelF (σ [×] τ) {pair v u} {i , j} (r , r') o d =
  (o zero ≈A proj₁ d) ∧
  (RelF σ r (mat (M.p₁ {width v} {width u}) .func (λ k → o (suc k))) (proj₁ (proj₂ d)) ∧
   RelF τ r' (mat (M.p₂ {width v} {width u}) .func (λ k → o (suc k))) (proj₂ (proj₂ d)))
RelF (σ [→] τ) {clo γ' t} {f} r o d =
  (o zero ≈A proj₁ d) ∧
  (∀ (s' : Setoid.Carrier A) {v : Val σ} {j : Ix σ} (rv : RelV σ v j)
     (z : ∣ 𝔽 (width v) ∣) (y : ∣ Fib σ j ∣) → RelF σ rv z y →
   ∀ {u U} (D : γ' · v , t ⇓ u [ U ]) →
     RelF τ (r rv D) (mat U .func (body-input γ' v (s' Sc.+ o zero) (λ k → o (suc k)) z))
       (Semimodule._+_ (Fib τ (f .idxf .sfunc j))
         (elim-const τ .at (f .idxf .sfunc j) .func (s' Sc.+ o zero))
         (Semimodule._+_ (Fib τ (f .idxf .sfunc j))
           (SP.evalΠ (⟦ τ ⟧ .fam indexed-family.[ f .idxf ]) j .func (proj₂ d))
           (f .famf .transf j .func y))))

-- Environments related to context indices, and environment vectors to elements of the context
-- fibre at a source weight: each cell may carry, beyond its relation, a mark that the elimination
-- constant at the source absorbs.
data RelVEnv : ∀ {Γ} → Env Γ → IxC Γ → Set where
  emp : RelVEnv emp (lift tt)
  _·_ : ∀ {Γ τ} {γ : Env Γ} {v : Val τ} {gi i} → RelVEnv γ gi → RelV τ v i → RelVEnv (γ · v) (gi , i)

infixl 30 _·_

Dominated : ∀ τ (i : Ix τ) → Setoid.Carrier A → ∣ Fib τ i ∣ → Prop
Dominated τ i s m =
  Semimodule._≈_ (Fib τ i) (Semimodule._+_ (Fib τ i) m (elim-const τ .at i .func s))
                          (elim-const τ .at i .func s)

RelFs : ∀ τ {v : Val τ} {i : Ix τ} → RelV τ v i → Setoid.Carrier A →
        ∣ 𝔽 (width v) ∣ → ∣ Fib τ i ∣ → Prop
RelFs τ {i = i} r s o d =
  ∃ (∣ Fib τ i ∣) (λ m → Dominated τ i s m ∧ RelF τ r o (Semimodule._+_ (Fib τ i) d m))

RelEnv : ∀ {Γ} {γ : Env Γ} {gi} → RelVEnv γ gi → Setoid.Carrier A →
         ∣ 𝔽 (width-env γ) ∣ → ∣ FibC Γ gi ∣ → Prop
RelEnv emp s x g = prop.⊤
RelEnv (_·_ {γ = γ} {v = v} rγ r) s x g =
  RelEnv rγ s (mat (M.p₁ {width-env γ} {width v}) .func x) (proj₁ g) ∧
  RelFs _ r s (mat (M.p₂ {width-env γ} {width v}) .func x) (proj₂ g)

-- The inputs of a derivation: the source weight at the first position, the environment after.
inputs : ∀ {Γ} (γ : Env Γ) → Setoid.Carrier A → ∣ 𝔽 (width-env γ) ∣ → ∣ 𝔽 (suc (width-env γ)) ∣
inputs γ s x zero    = s
inputs γ s x (suc k) = x k

open model using (app-+ₘ; app-∘; app-εₘ; app-I; app-e; app-congₘ; app-congᵥ) renaming (app to ap)
open Sc using (ι; ε) renaming (_≈_ to _≈s_; _+_ to _+ₛ_; _·_ to _·ₛ_)
open Setoid A using () renaming (refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)
open M using (Σ-cong; Σ-unit; Σ-ε; _∘_; _+ₘ_; εₘ; ≈ₘ-refl; ≈ₘ-sym; ≈ₘ-trans) renaming (Σ to Σₛ)

open Sc using (+-cong; ·-cong; +-lunit; +-comm; +-assoc; ·-lunit; ·-comm; ε-annihilₗ; ε-annihilᵣ)
open HasProducts products using () renaming (pair to ⟨_,_⟩)

-- Reading a relation at the inputs: the source column at the source weight, and the environment
-- columns at the environment vector.
private
  p₁-e : ∀ {m} (j : Fin (suc m)) → M.p₁ {1} {m} zero j ≈s M.e zero j
  p₁-e zero    = ≈-refl
  p₁-e (suc j) = ≈-refl

  p₂-e : ∀ {m} (j : Fin m) (l : Fin m) → M.p₂ {1} {m} j (suc l) ≈s M.e j l
  p₂-e j l = ≈-refl

app-source : ∀ {Γ} {γ : Env Γ} {n} (R : M.Matrix n (suc (width-env γ))) (s : Setoid.Carrier A)
             (k : Fin n) →
             ap (cols {γ = γ} R source) (λ _ → s) k ≈s (R k zero ·ₛ s)
app-source {γ = γ} R s k =
  ≈-trans (+-cong (·-cong entry ≈-refl) ≈-refl) (≈-trans +-comm +-lunit)
  where
  entry : (R ∘ M.in₁ {1} {width-env γ}) k zero ≈s R k zero
  entry = ≈-trans (Σ-cong {suc (width-env γ)}
                     (λ j → ≈-trans (·-cong (≈-refl {R k j}) (p₁-e {width-env γ} j)) ·-comm))
                  (Σ-unit {suc (width-env γ)} zero (λ j → R k j))

app-environment : ∀ {Γ} {γ : Env Γ} {n} (R : M.Matrix n (suc (width-env γ)))
                  (x : ∣ 𝔽 (width-env γ) ∣) (k : Fin n) →
                  ap (cols {γ = γ} R environment) x k ≈s Σₛ (λ j → R k (suc j) ·ₛ x j)
app-environment {γ = γ} R x k = Σ-cong {width-env γ} (λ j → ·-cong (entry j) ≈-refl)
  where
  entry : ∀ j → (R ∘ M.in₂ {1} {width-env γ}) k j ≈s R k (suc j)
  entry j =
    ≈-trans (+-cong ε-annihilᵣ
                    (Σ-cong {width-env γ}
                       (λ l → ≈-trans (·-cong (≈-refl {R k (suc l)}) (p₂-e {width-env γ} j l)) ·-comm)))
            (≈-trans +-lunit (Σ-unit {width-env γ} j (λ l → R k (suc l))))

app-inputs : ∀ {Γ} {γ : Env Γ} {n} (R : M.Matrix n (suc (width-env γ))) s x (k : Fin n) →
             ap R (inputs γ s x) k ≈s
             (ap (cols {γ = γ} R source) (λ _ → s) k +ₛ ap (cols {γ = γ} R environment) x k)
app-inputs {γ = γ} R s x k =
  +-cong (≈-sym (app-source {γ = γ} R s k)) (≈-sym (app-environment {γ = γ} R x k))

app-of-cols : ∀ {Γ} {γ : Env Γ} {n} (f : (i : Input) → M.Matrix n (input-width γ i)) s x
              (k : Fin n) →
              ap (of-cols {γ = γ} f) (inputs γ s x) k ≈s
              (ap (f source) (λ _ → s) k +ₛ ap (f environment) x k)
app-of-cols {γ = γ} f s x k =
  ≈-trans (app-inputs {γ = γ} (of-cols {γ = γ} f) s x k)
          (+-cong (app-congₘ (cols-of-cols {γ = γ} f source) (λ _ → s) k)
                  (app-congₘ (cols-of-cols {γ = γ} f environment) x k))

-- Semiring shorthands.
private
  w = elim-weight
  +-runit : ∀ {x} → (x +ₛ ε) ≈s x
  +-runit = ≈-trans +-comm +-lunit
  ·-runit : ∀ {x} → (x ·ₛ ι) ≈s x
  ·-runit = ≈-trans ·-comm ·-lunit
  Σ₁ : ∀ (f : Fin 1 → Setoid.Carrier A) → Σₛ f ≈s f zero
  Σ₁ f = +-runit

  -- The same in a semimodule.
  m-lunit : ∀ (X : Semimodule) {x} → Semimodule._≈_ X (Semimodule._+_ X (Semimodule.ε X) x) x
  m-lunit X = Semimodule.+-lunit X
  m-runit : ∀ (X : Semimodule) {x} → Semimodule._≈_ X (Semimodule._+_ X x (Semimodule.ε X)) x
  m-runit X = Semimodule.trans X (Semimodule.+-comm X) (Semimodule.+-lunit X)

-- Reading a lifted vector: the first position of the first summand's injection, and the rest of
-- the second's.
private
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

-- The control vector at a source weight: the weight at the root of a lifted value, and the
-- payload's control vector after.
private
  ap-ctrl-row : ∀ {n} (s : Setoid.Carrier A) (k : Fin n) → ap ctrl-row (λ _ → s) k ≈s (w ·ₛ s)
  ap-ctrl-row {n} s k = Σ₁ (λ j → ctrl-row {n} k j ·ₛ s)

  ctrl-lift-zero : ∀ {n} (g : M.Matrix n 1) (s : Setoid.Carrier A) →
                   ap (⟨ ctrl-row {1} , g ⟩) (λ _ → s) zero ≈s (w ·ₛ s)
  ctrl-lift-zero {n} g s = ≈-trans (ap-pair-zero {1} {n} ctrl-row g (λ _ → s)) (ap-ctrl-row {1} s zero)

  ctrl-lift-suc : ∀ {n} (g : M.Matrix n 1) (s : Setoid.Carrier A) (k : Fin n) →
                  ap (⟨ ctrl-row {1} , g ⟩) (λ _ → s) (suc k) ≈s ap g (λ _ → s) k
  ctrl-lift-suc {n} g s k = ap-pair-suc {1} {n} ctrl-row g (λ _ → s) k

-- The elimination constant, elementwise: the weight times the source at each root, the payload's
-- constant under it, and zero at a closure's payload.
ec : ∀ τ (i : Ix τ) → Setoid.Carrier A → ∣ Fib τ i ∣
ec τ i s = elim-const τ .at i .func s

private
  ec-unit : ∀ i s → ec unit i s zero ≈s (w ·ₛ s)
  ec-unit i s =
    ≈-trans (+-cong (·-cong +-runit ≈-refl) ≈-refl)
            (≈-trans +-runit (≈-trans ·-lunit +-runit))

  ec-inj₁ : ∀ {σ τ} (i : Ix σ) s →
            (proj₁ (ec (σ [+] τ) (inj₁ i) s) ≈s (w ·ₛ s)) ∧
            Semimodule._≈_ (Fib σ i) (proj₂ (ec (σ [+] τ) (inj₁ i) s)) (ec σ i s)
  ec-inj₁ {σ} i s = ≈-trans +-runit +-runit , Semimodule.+-lunit (Fib σ i)

  ec-inj₂ : ∀ {σ τ} (i : Ix τ) s →
            (proj₁ (ec (σ [+] τ) (inj₂ i) s) ≈s (w ·ₛ s)) ∧
            Semimodule._≈_ (Fib τ i) (proj₂ (ec (σ [+] τ) (inj₂ i) s)) (ec τ i s)
  ec-inj₂ {σ} {τ} i s = ≈-trans +-runit +-runit , Semimodule.+-lunit (Fib τ i)

  ec-pair : ∀ {σ τ} (i : Ix σ) (j : Ix τ) s →
            (proj₁ (ec (σ [×] τ) (i , j) s) ≈s (w ·ₛ s)) ∧
            (Semimodule._≈_ (Fib σ i) (proj₁ (proj₂ (ec (σ [×] τ) (i , j) s))) (ec σ i s) ∧
             Semimodule._≈_ (Fib τ j) (proj₂ (proj₂ (ec (σ [×] τ) (i , j) s))) (ec τ j s))
  ec-pair {σ} {τ} i j s =
    ≈-trans +-runit +-runit ,
    (Semimodule.trans (Fib σ i) (m-lunit (Fib σ i)) (m-runit (Fib σ i)) ,
     Semimodule.trans (Fib τ j) (m-lunit (Fib τ j)) (m-lunit (Fib τ j)))

  ec-clo : ∀ {σ τ} (f : Ix (σ [→] τ)) s →
           (proj₁ (ec (σ [→] τ) f s) ≈s (w ·ₛ s)) ∧
           Semimodule._≈_ (model.FE._⟶_ ⟦ σ ⟧ ⟦ τ ⟧ .fam .fm f) (proj₂ (ec (σ [→] τ) f s))
             (Semimodule.ε (model.FE._⟶_ ⟦ σ ⟧ ⟦ τ ⟧ .fam .fm f))
  ec-clo {σ} {τ} f s =
    ≈-trans +-runit +-runit ,
    m-lunit (model.FE._⟶_ ⟦ σ ⟧ ⟦ τ ⟧ .fam .fm f) {Semimodule.ε (model.FE._⟶_ ⟦ σ ⟧ ⟦ τ ⟧ .fam .fm f)}

  ec-natural : ∀ τ {i i' : Ix τ} (e : Setoid._≈_ (⟦ τ ⟧ .idx) i i') s →
               Semimodule._≈_ (Fib τ i') (⟦ τ ⟧ .fam .subst e .func (ec τ i s)) (ec τ i' s)
  ec-natural τ e s = elim-const τ .Constant.at-natural e .SemiMod._≈m_.*≈* .prop-setoid._≃m_.func-eq ≈-refl

-- The fibre relation respects the setoids on both sides.
private
  module F τ i = Semimodule (Fib τ i)

body-input-resp : ∀ {Γ' σ} (γ' : Env Γ') (v : Val σ) {s s' c c' z} →
                  s ≈s s' → (∀ k → c k ≈s c' k) → ∀ k →
                  body-input γ' v s c z k ≈s body-input γ' v s' c' z k
body-input-resp γ' v es ec zero    = es
body-input-resp γ' v es ec (suc k) =
  +-cong (app-congᵥ (M.in₁ {width-env γ'} {width v}) ec k) ≈-refl

RelF-resp : ∀ τ {v : Val τ} {i : Ix τ} (r : RelV τ v i) {o o' : ∣ 𝔽 (width v) ∣} {d d' : ∣ Fib τ i ∣} →
            (∀ k → o k ≈s o' k) → F._≈_ τ i d d' → RelF τ r o d → RelF τ r o' d'
RelF-resp unit {unit} r eo ed h k = ≈-trans (≈-sym (eo k)) (≈-trans (h k) (ed k))
RelF-resp (σ [+] τ) {inl v} {i} (i' , r , ⟪ e ⟫) {d = d} {d'} eo ed (h₀ , h) =
  let ed' = ⟦ σ [+] τ ⟧ .fam .subst {i} {inj₁ i'} e .SemiMod._⇒_.func-resp-≈ ed in
  ≈-trans (≈-sym (eo zero)) (≈-trans h₀ (prop._∧_.proj₁ ed')) ,
  RelF-resp σ r (λ k → eo (suc k)) (prop._∧_.proj₂ ed') h
RelF-resp (σ [+] τ) {inr v} {i} (i' , r , ⟪ e ⟫) {d = d} {d'} eo ed (h₀ , h) =
  let ed' = ⟦ σ [+] τ ⟧ .fam .subst {i} {inj₂ i'} e .SemiMod._⇒_.func-resp-≈ ed in
  ≈-trans (≈-sym (eo zero)) (≈-trans h₀ (prop._∧_.proj₁ ed')) ,
  RelF-resp τ r (λ k → eo (suc k)) (prop._∧_.proj₂ ed') h
RelF-resp (σ [×] τ) {pair v u} {i , j} (r , r') eo (ed₀ , (ed₁ , ed₂)) (h₀ , (h₁ , h₂)) =
  ≈-trans (≈-sym (eo zero)) (≈-trans h₀ ed₀) ,
  (RelF-resp σ r (app-congᵥ (M.p₁ {width v} {width u}) (λ k → eo (suc k))) ed₁ h₁ ,
   RelF-resp τ r' (app-congᵥ (M.p₂ {width v} {width u}) (λ k → eo (suc k))) ed₂ h₂)
RelF-resp (σ [→] τ) {clo γ' t} {f} r {o} {o'} {d} {d'} eo (ed₀ , ed₂) (h₀ , hc) =
  ≈-trans (≈-sym (eo zero)) (≈-trans h₀ ed₀) ,
  λ s' {v} {j} rv z y hz {u} {U} D →
    RelF-resp τ (r rv D)
      (app-congᵥ U (body-input-resp γ' v (+-cong ≈-refl (eo zero)) (λ k → eo (suc k))))
      (F.+-cong τ (f .idxf .sfunc j)
         (elim-const τ .at (f .idxf .sfunc j) .SemiMod._⇒_.func-resp-≈ (+-cong ≈-refl (eo zero)))
         (F.+-cong τ (f .idxf .sfunc j)
            (SP.evalΠ (⟦ τ ⟧ .fam indexed-family.[ f .idxf ]) j .SemiMod._⇒_.func-resp-≈
               {proj₂ d} {proj₂ d'} ed₂)
            (F.refl τ (f .idxf .sfunc j) {f .famf .transf j .func y})))
      (hc s' rv z y hz D)

-- Transport of a sum of the constant and an element along an index equation.
private
  subst-ec+ : ∀ τ {i i' : Ix τ} (e : Setoid._≈_ (⟦ τ ⟧ .idx) i i') s d →
              F._≈_ τ i' (⟦ τ ⟧ .fam .subst e .func (F._+_ τ i (ec τ i s) d))
                         (F._+_ τ i' (ec τ i' s) (⟦ τ ⟧ .fam .subst e .func d))
  subst-ec+ τ {i} {i'} e s d =
    F.trans τ i' (⟦ τ ⟧ .fam .subst e .SemiMod._⇒_.preserve-+ {ec τ i s} {d})
                 (F.+-cong τ i' (ec-natural τ e s) (F.refl τ i'))

  app-+ᵥ : ∀ {m n} (R : M.Matrix m n) (u v : ∣ 𝔽 n ∣) (k : Fin m) →
           ap R (λ j → u j +ₛ v j) k ≈s (ap R u k +ₛ ap R v k)
  app-+ᵥ R u v k = model.app-+ R u v k

  ap-pair-p₁ : ∀ {m a b} (f : M.Matrix a m) (g : M.Matrix b m) (u : ∣ 𝔽 m ∣) (k : Fin a) →
               ap (M.p₁ {a} {b}) (ap (⟨ f , g ⟩) u) k ≈s ap f u k
  ap-pair-p₁ {m} {a} {b} f g u k =
    ≈-trans (≈-sym (app-∘ (M.p₁ {a} {b}) (⟨ f , g ⟩) u k))
            (app-congₘ (HasProducts.pair-p₁ products f g) u k)

  ap-pair-p₂ : ∀ {m a b} (f : M.Matrix a m) (g : M.Matrix b m) (u : ∣ 𝔽 m ∣) (k : Fin b) →
               ap (M.p₂ {a} {b}) (ap (⟨ f , g ⟩) u) k ≈s ap g u k
  ap-pair-p₂ {m} {a} {b} f g u k =
    ≈-trans (≈-sym (app-∘ (M.p₂ {a} {b}) (⟨ f , g ⟩) u k))
            (app-congₘ (HasProducts.pair-p₂ products f g) u k)

-- Adding the value's control positions at a source weight on the operational side, and the
-- elimination constant on the denotational side, preserves the relation.
ctrl-add : ∀ τ {v : Val τ} {i : Ix τ} (r : RelV τ v i) (s : Setoid.Carrier A)
           {o : ∣ 𝔽 (width v) ∣} {d : ∣ Fib τ i ∣} → RelF τ r o d →
           RelF τ r (λ k → ap (ctrl-of v) (λ _ → s) k +ₛ o k) (F._+_ τ i (ec τ i s) d)
ctrl-add unit {unit} {i} r s h zero =
  +-cong (≈-trans (ap-ctrl-row {1} s zero) (≈-sym (ec-unit i s))) (h zero)
ctrl-add (σ [+] τ) {inl v} {i} (i' , r , ⟪ e ⟫) s {o} {d} (h₀ , h) =
  let e+ = subst-ec+ (σ [+] τ) {i} {inj₁ i'} e s d
      d' = ⟦ σ [+] τ ⟧ .fam .subst {i} {inj₁ i'} e .func d
  in
  ≈-trans (+-cong (ctrl-lift-zero (ctrl-of v) s) h₀)
          (≈-sym (≈-trans (prop._∧_.proj₁ e+) (+-cong (prop._∧_.proj₁ (ec-inj₁ {σ} {τ} i' s)) ≈-refl))) ,
  RelF-resp σ r
    (λ k → +-cong (≈-sym (ctrl-lift-suc (ctrl-of v) s k)) ≈-refl)
    (F.sym σ i' (F.trans σ i' (prop._∧_.proj₂ e+)
                              (F.+-cong σ i' (prop._∧_.proj₂ (ec-inj₁ {σ} {τ} i' s)) (F.refl σ i'))))
    (ctrl-add σ r s h)
ctrl-add (σ [+] τ) {inr v} {i} (i' , r , ⟪ e ⟫) s {o} {d} (h₀ , h) =
  let e+ = subst-ec+ (σ [+] τ) {i} {inj₂ i'} e s d
  in
  ≈-trans (+-cong (ctrl-lift-zero (ctrl-of v) s) h₀)
          (≈-sym (≈-trans (prop._∧_.proj₁ e+) (+-cong (prop._∧_.proj₁ (ec-inj₂ {σ} {τ} i' s)) ≈-refl))) ,
  RelF-resp τ r
    (λ k → +-cong (≈-sym (ctrl-lift-suc (ctrl-of v) s k)) ≈-refl)
    (F.sym τ i' (F.trans τ i' (prop._∧_.proj₂ e+)
                              (F.+-cong τ i' (prop._∧_.proj₂ (ec-inj₂ {σ} {τ} i' s)) (F.refl τ i'))))
    (ctrl-add τ r s h)
ctrl-add (σ [×] τ) {pair v u} {i , j} (r , r') s {o} {d} (h₀ , (h₁ , h₂)) =
  ≈-trans (+-cong (ctrl-lift-zero (⟨ ctrl-of v , ctrl-of u ⟩) s) h₀)
          (+-cong (≈-sym (prop._∧_.proj₁ (ec-pair {σ} {τ} i j s))) ≈-refl) ,
  (RelF-resp σ r
     (λ k → ≈-trans (+-cong (≈-sym (ap-pair-p₁ (ctrl-of v) (ctrl-of u) (λ _ → s) k)) ≈-refl)
              (≈-trans (≈-sym (app-+ᵥ (M.p₁ {width v} {width u}) _ _ k))
                       (app-congᵥ (M.p₁ {width v} {width u})
                          (λ l → +-cong (≈-sym (ctrl-lift-suc (⟨ ctrl-of v , ctrl-of u ⟩) s l)) ≈-refl) k)))
     (F.+-cong σ i (F.sym σ i (prop._∧_.proj₁ (prop._∧_.proj₂ (ec-pair {σ} {τ} i j s)))) (F.refl σ i))
     (ctrl-add σ r s h₁) ,
   RelF-resp τ r'
     (λ k → ≈-trans (+-cong (≈-sym (ap-pair-p₂ (ctrl-of v) (ctrl-of u) (λ _ → s) k)) ≈-refl)
              (≈-trans (≈-sym (app-+ᵥ (M.p₂ {width v} {width u}) _ _ k))
                       (app-congᵥ (M.p₂ {width v} {width u})
                          (λ l → +-cong (≈-sym (ctrl-lift-suc (⟨ ctrl-of v , ctrl-of u ⟩) s l)) ≈-refl) k)))
     (F.+-cong τ j (F.sym τ j (prop._∧_.proj₂ (prop._∧_.proj₂ (ec-pair {σ} {τ} i j s)))) (F.refl τ j))
     (ctrl-add τ r' s h₂))
ctrl-add (σ [→] τ) {clo γ' t} {f} r s {o} {d} (h₀ , hc) =
  ≈-trans (+-cong (ctrl-lift-zero {width-env γ'} εₘ s) h₀)
          (+-cong (≈-sym (prop._∧_.proj₁ (ec-clo {σ} {τ} f s))) ≈-refl) ,
  λ s' {v} {j} rv z y hz {u} {U} D →
    RelF-resp τ (r rv D)
      (app-congᵥ U (body-input-resp γ' v
         (≈-trans +-assoc (+-cong ≈-refl (+-cong (≈-sym (ctrl-lift-zero {width-env γ'} εₘ s)) ≈-refl)))
         (λ k → ≈-sym (≈-trans (+-cong (ctrl-lift-suc {width-env γ'} εₘ s k) ≈-refl)
                               (≈-trans (+-cong (app-εₘ {width-env γ'} {1} (λ _ → s) k) ≈-refl) +-lunit)))))
      (F.+-cong τ (f .idxf .sfunc j)
         (elim-const τ .at (f .idxf .sfunc j) .SemiMod._⇒_.func-resp-≈
            (≈-trans +-assoc (+-cong ≈-refl (+-cong (≈-sym (ctrl-lift-zero {width-env γ'} εₘ s)) ≈-refl))))
         (F.+-cong τ (f .idxf .sfunc j)
            (SP.evalΠ (⟦ τ ⟧ .fam indexed-family.[ f .idxf ]) j .SemiMod._⇒_.func-resp-≈
               {proj₂ d} {proj₂ (F._+_ (σ [→] τ) f (ec (σ [→] τ) f s) d)}
               (P.sym {proj₂ (F._+_ (σ [→] τ) f (ec (σ [→] τ) f s) d)} {proj₂ d}
                 (P.trans {proj₂ (F._+_ (σ [→] τ) f (ec (σ [→] τ) f s) d)} {P._+_ P.ε (proj₂ d)} {proj₂ d}
                   (P.+-cong {proj₂ (ec (σ [→] τ) f s)} {P.ε} {proj₂ d} {proj₂ d}
                      (prop._∧_.proj₂ (ec-clo {σ} {τ} f s)) (P.refl {proj₂ d}))
                   (P.+-lunit {proj₂ d}))))
            (F.refl τ (f .idxf .sfunc j) {f .famf .transf j .func y})))
      (hc (s' +ₛ (w ·ₛ s)) rv z y hz D)
  where module P = Semimodule (model.FE._⟶_ ⟦ σ ⟧ ⟦ τ ⟧ .fam .fm f)

-- Looking up a variable in a related environment.
lookupR : ∀ {Γ τ} (x : Γ ∋ τ) {γ : Env Γ} {gi} → RelVEnv γ gi →
          RelV τ (lookup x γ) (LI.⟦ x ⟧var .idxf .sfunc gi)
lookupR zero     (rγ · r) = r
lookupR (succ x) (rγ · r) = lookupR x rγ

private
  RelFs-resp : ∀ τ {v : Val τ} {i : Ix τ} (r : RelV τ v i) s {o o' : ∣ 𝔽 (width v) ∣} {d} →
               (∀ k → o k ≈s o' k) → RelFs τ r s o d → RelFs τ r s o' d
  RelFs-resp τ {i = i} r s eo (m , (dm , h)) = m , (dm , RelF-resp τ r eo (F.refl τ i) h)

lookupRel : ∀ {Γ τ} (x : Γ ∋ τ) {γ : Env Γ} {gi} (rγ : RelVEnv γ gi) s xs g →
            RelEnv rγ s xs g →
            RelFs τ (lookupR x rγ) s (ap (proj-var x γ) xs) (LI.⟦ x ⟧var .famf .transf gi .func g)
lookupRel zero (rγ · r) s xs g (_ , h) = h
lookupRel {τ = τ} (succ x) {γ · v} {gi , i} (rγ · r) s xs g (h , _) =
  RelFs-resp τ (lookupR x rγ) s
    (λ k → ≈-sym (app-∘ (proj-var x γ) (M.p₁ {width-env γ} {width v}) xs k))
    (lookupRel x rγ s (ap (M.p₁ {width-env γ} {width v}) xs) (proj₁ g) h)

-- A dominated mark is absorbed by the constant, so a relation up to a mark becomes a relation
-- once the control positions and the constant are added.
private
  absorb : ∀ τ (i : Ix τ) s (d m : ∣ Fib τ i ∣) → Dominated τ i s m →
           F._≈_ τ i (F._+_ τ i (ec τ i s) (F._+_ τ i d m)) (F._+_ τ i (ec τ i s) d)
  absorb τ i s d m dm =
    F.trans τ i (F.+-cong τ i (F.refl τ i) (F.+-comm τ i))
    (F.trans τ i (F.sym τ i (F.+-assoc τ i))
    (F.trans τ i (F.+-cong τ i (F.trans τ i (F.+-comm τ i) dm) (F.refl τ i))
                 (F.refl τ i)))

RelFs-ctrl : ∀ τ {v : Val τ} {i : Ix τ} (r : RelV τ v i) s {o : ∣ 𝔽 (width v) ∣} {d} →
             RelFs τ r s o d →
             RelF τ r (λ k → ap (ctrl-of v) (λ _ → s) k +ₛ o k) (F._+_ τ i (ec τ i s) d)
RelFs-ctrl τ {i = i} r s {o} {d} (m , (dm , h)) =
  RelF-resp τ r (λ k → ≈-refl) (absorb τ i s d m dm) (ctrl-add τ r s h)

-- Related values are related at equal indices.
RelV-resp : ∀ τ {v : Val τ} {i i' : Ix τ} → Setoid._≈_ (⟦ τ ⟧ .idx) i i' → RelV τ v i → RelV τ v i'
RelV-resp unit {unit} e r = tt
RelV-resp (σ [+] τ) {inl v} {i} {i'} e (i₀ , r , ⟪ e₀ ⟫) =
  i₀ , r , ⟪ Setoid.trans (⟦ σ [+] τ ⟧ .idx) {i'} {i} {inj₁ i₀} (Setoid.sym (⟦ σ [+] τ ⟧ .idx) {i} {i'} e) e₀ ⟫
RelV-resp (σ [+] τ) {inr v} {i} {i'} e (i₀ , r , ⟪ e₀ ⟫) =
  i₀ , r , ⟪ Setoid.trans (⟦ σ [+] τ ⟧ .idx) {i'} {i} {inj₂ i₀} (Setoid.sym (⟦ σ [+] τ ⟧ .idx) {i} {i'} e) e₀ ⟫
RelV-resp (σ [×] τ) {pair v u} {i , j} {i' , j'} (e₁ , e₂) (r , r') = RelV-resp σ e₁ r , RelV-resp τ e₂ r'
RelV-resp (σ [→] τ) {clo γ' t} {f} {f'} e r {v} {j} rv {u} {U} D =
  RelV-resp τ (e .FD._≃_.idxf-eq .prop-setoid._≃m_.func-eq (Setoid.refl (⟦ σ ⟧ .idx) {j})) (r rv D)

-- The value part of the fundamental lemma: a term's value is related to the term's index at a
-- related environment, by induction on the term over all derivations.
relV : ∀ {Γ τ} {t : Γ ⊢ τ} (c : CoreTm t) {γ : Env Γ} {v R} (D : γ , t ⇓ v [ R ])
       {gi} (rγ : RelVEnv γ gi) → RelV τ v (⟦ t ⟧tm .idxf .sfunc gi)
relV (var x) (⇓-var .x) rγ = lookupR x rγ
relV unit ⇓-unit rγ = tt
relV {τ = τ₁ [+] τ₂} (inl {t = t} c) (⇓-inl D) {gi} rγ =
  ⟦ t ⟧tm .idxf .sfunc gi , relV c D rγ ,
  ⟪ Setoid.refl (⟦ τ₁ [+] τ₂ ⟧ .idx) {inj₁ (⟦ t ⟧tm .idxf .sfunc gi)} ⟫
relV {τ = τ₁ [+] τ₂} (inr {t = t} c) (⇓-inr D) {gi} rγ =
  ⟦ t ⟧tm .idxf .sfunc gi , relV c D rγ ,
  ⟪ Setoid.refl (⟦ τ₁ [+] τ₂ ⟧ .idx) {inj₂ (⟦ t ⟧tm .idxf .sfunc gi)} ⟫
relV {Γ = Γ} {τ = τ} (case {τ₁ = τ₁} {τ₂ = τ₂} {s = s} {t₁ = t₁} {t₂ = t₂} c c₁ c₂) (⇓-case-l D₁ D₂) {gi} rγ =
  let (i' , r , ⟪ e ⟫) = relV c D₁ rγ in
  RelV-resp τ
    (Setoid.sym (⟦ τ ⟧ .idx)
      (HasStrongCoproducts.copair FD.strongCoproducts
         (FD.elimF (elim-const τ) ⟦ t₁ ⟧tm) (FD.elimF (elim-const τ) ⟦ t₂ ⟧tm)
         .idxf .prop-setoid._⇒_.func-resp-≈ {gi , ⟦ s ⟧tm .idxf .sfunc gi} {gi , inj₁ i'}
         (Setoid.refl (⟦ Γ ⟧ctxt .idx) {gi} , e)))
    (relV c₁ D₂ (rγ · r))
relV {Γ = Γ} {τ = τ} (case {τ₁ = τ₁} {τ₂ = τ₂} {s = s} {t₁ = t₁} {t₂ = t₂} c c₁ c₂) (⇓-case-r D₁ D₂) {gi} rγ =
  let (i' , r , ⟪ e ⟫) = relV c D₁ rγ in
  RelV-resp τ
    (Setoid.sym (⟦ τ ⟧ .idx)
      (HasStrongCoproducts.copair FD.strongCoproducts
         (FD.elimF (elim-const τ) ⟦ t₁ ⟧tm) (FD.elimF (elim-const τ) ⟦ t₂ ⟧tm)
         .idxf .prop-setoid._⇒_.func-resp-≈ {gi , ⟦ s ⟧tm .idxf .sfunc gi} {gi , inj₂ i'}
         (Setoid.refl (⟦ Γ ⟧ctxt .idx) {gi} , e)))
    (relV c₂ D₂ (rγ · r))
relV (pair c₁ c₂) (⇓-pair D₁ D₂) rγ = relV c₁ D₁ rγ , relV c₂ D₂ rγ
relV (fst c) (⇓-fst D) rγ = proj₁ (relV c D rγ)
relV (snd c) (⇓-snd D) rγ = proj₂ (relV c D rγ)
relV (lam c) ⇓-lam rγ {v} {j} rv {u} {U} D = relV c D (rγ · rv)
relV (app c₁ c₂) (⇓-app D₁ D₂ D₃) rγ = relV c₁ D₁ rγ (relV c₂ D₂ rγ) D₃

-- Domination is monotone in the source weight, and a relation is a relation up to the zero mark.
private
  ec-linear : ∀ τ (i : Ix τ) s s' →
              F._≈_ τ i (ec τ i (s +ₛ s')) (F._+_ τ i (ec τ i s) (ec τ i s'))
  ec-linear τ i s s' = elim-const τ .at i .SemiMod._⇒_.preserve-+ {s} {s'}

  ec-w : ∀ τ (i : Ix τ) s → F._≈_ τ i (ec τ i (w ·ₛ s)) (ec τ i s)
  ec-w τ i s =
    LI.ty-unit τ (λ ()) (λ ()) .at i .SemiMod._⇒_.func-resp-≈
      (+-cong (≈-trans (≈-sym Sc.·-assoc) (·-cong w-idem ≈-refl)) ≈-refl)

  Dominated-mono : ∀ τ (i : Ix τ) s s' m → Dominated τ i s m → Dominated τ i (s' +ₛ (w ·ₛ s)) m
  Dominated-mono τ i s s' m dm =
    F.trans τ i (F.+-cong τ i (F.refl τ i) (F.trans τ i (ec-linear τ i s' (w ·ₛ s))
                                                        (F.+-cong τ i (F.refl τ i) (ec-w τ i s))))
    (F.trans τ i (F.+-cong τ i (F.refl τ i) (F.+-comm τ i))
    (F.trans τ i (F.sym τ i (F.+-assoc τ i))
    (F.trans τ i (F.+-cong τ i dm (F.refl τ i))
    (F.trans τ i (F.+-comm τ i)
    (F.sym τ i (F.trans τ i (ec-linear τ i s' (w ·ₛ s))
                            (F.+-cong τ i (F.refl τ i) (ec-w τ i s))))))))

  RelFs-mono : ∀ τ {v : Val τ} {i : Ix τ} (r : RelV τ v i) s s' {o d} →
               RelFs τ r s o d → RelFs τ r (s' +ₛ (w ·ₛ s)) o d
  RelFs-mono τ {i = i} r s s' (m , (dm , h)) = m , (Dominated-mono τ i s s' m dm , h)

  RelEnv-mono : ∀ {Γ} {γ : Env Γ} {gi} (rγ : RelVEnv γ gi) s s' {x g} →
                RelEnv rγ s x g → RelEnv rγ (s' +ₛ (w ·ₛ s)) x g
  RelEnv-mono emp s s' rel = prop.tt
  RelEnv-mono (rγ · r) s s' (rel , h) = RelEnv-mono rγ s s' rel , RelFs-mono _ r s s' h

  RelFs-of : ∀ τ {v : Val τ} {i : Ix τ} (r : RelV τ v i) s {o d} → RelF τ r o d → RelFs τ r s o d
  RelFs-of τ {i = i} r s {o} {d} h =
    F.ε τ i , (m-lunit (Fib τ i) , RelF-resp τ r (λ k → ≈-refl) (F.sym τ i (m-runit (Fib τ i))) h)

-- Splitting a concatenated environment vector.
private
  ap-p₁-++ : ∀ {m n} (x : ∣ 𝔽 m ∣) (z : ∣ 𝔽 n ∣) k →
             ap (M.p₁ {m} {n}) (λ l → ap (M.in₁ {m} {n}) x l +ₛ ap (M.in₂ {m} {n}) z l) k ≈s x k
  ap-p₁-++ {m} {n} x z k =
    ≈-trans (app-+ᵥ (M.p₁ {m} {n}) _ _ k)
            (≈-trans (+-cong (≈-trans (≈-sym (app-∘ (M.p₁ {m} {n}) (M.in₁ {m} {n}) x k))
                                      (≈-trans (app-congₘ (M.id-1 m n) x k) (app-I x k)))
                             (≈-trans (≈-sym (app-∘ (M.p₁ {m} {n}) (M.in₂ {m} {n}) z k))
                                      (≈-trans (app-congₘ (M.zero-1 m n) z k) (app-εₘ z k))))
                     +-runit)

  ap-p₂-++ : ∀ {m n} (x : ∣ 𝔽 m ∣) (z : ∣ 𝔽 n ∣) k →
             ap (M.p₂ {m} {n}) (λ l → ap (M.in₁ {m} {n}) x l +ₛ ap (M.in₂ {m} {n}) z l) k ≈s z k
  ap-p₂-++ {m} {n} x z k =
    ≈-trans (app-+ᵥ (M.p₂ {m} {n}) _ _ k)
            (≈-trans (+-cong (≈-trans (≈-sym (app-∘ (M.p₂ {m} {n}) (M.in₁ {m} {n}) x k))
                                      (≈-trans (app-congₘ (M.zero-2 m n) x k) (app-εₘ x k)))
                             (≈-trans (≈-sym (app-∘ (M.p₂ {m} {n}) (M.in₂ {m} {n}) z k))
                                      (≈-trans (app-congₘ (M.id-2 m n) z k) (app-I z k))))
                     +-lunit)

private
  RelEnv-resp : ∀ {Γ} {γ : Env Γ} {gi} (rγ : RelVEnv γ gi) s {x x' g} →
                (∀ k → x k ≈s x' k) → RelEnv rγ s x g → RelEnv rγ s x' g
  RelEnv-resp emp s ex rel = prop.tt
  RelEnv-resp (_·_ {γ = γ} {v = v} rγ r) s ex (rel , h) =
    RelEnv-resp rγ s (app-congᵥ (M.p₁ {width-env γ} {width v}) ex) rel ,
    RelFs-resp _ r s (app-congᵥ (M.p₂ {width-env γ} {width v}) ex) h

-- The fundamental lemma.
fundamental : ∀ {Γ τ} {t : Γ ⊢ τ} (c : CoreTm t) {γ : Env Γ} {v R} (D : γ , t ⇓ v [ R ])
              {gi} (rγ : RelVEnv γ gi) (s : Setoid.Carrier A) (x : ∣ 𝔽 (width-env γ) ∣)
              (g : ∣ FibC Γ gi ∣) → RelEnv rγ s x g →
              RelF τ (relV c D rγ) (mat R .func (inputs γ s x))
                (Semimodule._+_ (Fib τ (⟦ t ⟧tm .idxf .sfunc gi))
                  (elim-const τ .at (⟦ t ⟧tm .idxf .sfunc gi) .func s)
                  (⟦ t ⟧tm .famf .transf gi .func g))
fundamental {τ = τ} (var x) {γ = γ} (⇓-var .x) {gi} rγ s xs g rel =
  RelF-resp τ (lookupR x rγ)
    (λ k → ≈-sym (app-of-cols {γ = γ} (var-out x γ) s xs k))
    (F.refl τ (LI.⟦ x ⟧var .idxf .sfunc gi))
    (RelFs-ctrl τ (lookupR x rγ) s (lookupRel x rγ s xs g rel))
fundamental {Γ = Γ} unit {γ = γ} (⇓-unit) {gi} rγ s x g rel = goal
  where
  goal : ∀ k → ap (of-cols {γ = γ} (unit-out γ)) (inputs γ s x) k ≈s
               (elim-const unit .at (⟦ unit {Γ} ⟧tm .idxf .sfunc gi) .func s k +ₛ
                ⟦ unit {Γ} ⟧tm .famf .transf gi .func g k)
  goal zero =
    ≈-trans (app-of-cols {γ = γ} (unit-out γ) s x zero)
            (+-cong (≈-sym (≈-trans (+-cong (·-cong (≈-trans +-comm +-lunit)
                                                    (≈-refl {elim-weight ·ₛ s +ₛ ε})) (≈-refl {ε}))
                                    (≈-trans +-comm (≈-trans +-lunit ·-lunit))))
                    (app-εₘ {1} {width-env γ} x zero))
fundamental (inl c) (⇓-inl D) rγ s x g rel = {!!}
fundamental (inr c) (⇓-inr D) rγ s x g rel = {!!}
fundamental (case c c₁ c₂) (⇓-case-l D₁ D₂) rγ s x g rel = {!!}
fundamental (case c c₁ c₂) (⇓-case-r D₁ D₂) rγ s x g rel = {!!}
fundamental (pair c₁ c₂) (⇓-pair D₁ D₂) rγ s x g rel = {!!}
fundamental (fst c) (⇓-fst D) rγ s x g rel = {!!}
fundamental (snd c) (⇓-snd D) rγ s x g rel = {!!}
fundamental {Γ = Γ} {τ = σ [→] τ} (lam {t = t'} c) {γ = γ} ⇓-lam {gi} rγ s x g rel =
  root , clause
  where
  o : ∣ 𝔽 (suc (width-env γ)) ∣
  o = ap (of-cols {γ = γ} (lam-out γ t')) (inputs γ s x)

  o₀ : o zero ≈s (w ·ₛ s)
  o₀ = ≈-trans (app-of-cols {γ = γ} (lam-out γ t') s x zero)
               (≈-trans (+-cong (≈-trans (app-∘ (M.in₁ {1} {width-env γ}) ctrl-row (λ _ → s) zero)
                                         (≈-trans (ap-in₁-zero {width-env γ} (ap (ctrl-row {1}) (λ _ → s)))
                                                  (ap-ctrl-row {1} s zero)))
                                (ap-in₂-zero {width-env γ} x))
                        +-runit)

  o-tail : ∀ k → o (suc k) ≈s x k
  o-tail k = ≈-trans (app-of-cols {γ = γ} (lam-out γ t') s x (suc k))
                     (≈-trans (+-cong (≈-trans (app-∘ (M.in₁ {1} {width-env γ}) ctrl-row (λ _ → s) (suc k))
                                               (ap-in₁-suc {width-env γ} (ap (ctrl-row {1}) (λ _ → s)) k))
                                      (ap-in₂-suc {width-env γ} x k))
                              +-lunit)

  f = ⟦ lam t' ⟧tm .idxf .sfunc gi

  root : o zero ≈A proj₁ (F._+_ (σ [→] τ) f (ec (σ [→] τ) f s) (⟦ lam t' ⟧tm .famf .transf gi .func g))
  root = ≈-trans o₀ (≈-sym (≈-trans (+-cong (prop._∧_.proj₁ (ec-clo {σ} {τ} f s)) ≈-refl) +-runit))

  clause : ∀ (s' : Setoid.Carrier A) {v : Val σ} {j : Ix σ} (rv : RelV σ v j)
             (z : ∣ 𝔽 (width v) ∣) (y : ∣ Fib σ j ∣) → RelF σ rv z y →
           ∀ {u U} (D : γ · v , t' ⇓ u [ U ]) →
             RelF τ (relV c D (rγ · rv)) (mat U .func (body-input γ v (s' +ₛ o zero) (λ k → o (suc k)) z))
               (F._+_ τ (f .idxf .sfunc j)
                 (ec τ (f .idxf .sfunc j) (s' +ₛ o zero))
                 (F._+_ τ (f .idxf .sfunc j)
                   (SP.evalΠ (⟦ τ ⟧ .fam indexed-family.[ f .idxf ]) j .func
                      (proj₂ (F._+_ (σ [→] τ) f (ec (σ [→] τ) f s) (⟦ lam t' ⟧tm .famf .transf gi .func g))))
                   (f .famf .transf j .func y)))
  clause s' {v} {j} rv z y hz {u} {U} D =
    RelF-resp τ (relV c D (rγ · rv))
      (app-congᵥ U (body-input-resp γ v (+-cong ≈-refl (≈-sym o₀)) (λ k → ≈-sym (o-tail k))))
      (F.+-cong τ (f .idxf .sfunc j)
         (elim-const τ .at (f .idxf .sfunc j) .SemiMod._⇒_.func-resp-≈ (+-cong ≈-refl (≈-sym o₀)))
         (F.trans τ (f .idxf .sfunc j)
            (⟦ t' ⟧tm .famf .transf (gi , j) .SemiMod._⇒_.func-resp-≈
               {g , y} {(FibC Γ gi Semimodule.+ g) (Semimodule.ε (FibC Γ gi)) ,
                        (Fib σ j Semimodule.+ Semimodule.ε (Fib σ j)) y}
               (Semimodule.sym (FibC Γ gi) (m-runit (FibC Γ gi)) , Semimodule.sym (Fib σ j) (m-lunit (Fib σ j))))
         (F.trans τ (f .idxf .sfunc j)
            (⟦ t' ⟧tm .famf .transf (gi , j) .SemiMod._⇒_.preserve-+
               {g , Semimodule.ε (Fib σ j)} {Semimodule.ε (FibC Γ gi) , y})
            (F.+-cong τ (f .idxf .sfunc j)
               (F.trans τ (f .idxf .sfunc j) (F.sym τ (f .idxf .sfunc j) β)
                  (SP.evalΠ (⟦ τ ⟧ .fam indexed-family.[ f .idxf ]) j .SemiMod._⇒_.func-resp-≈
                     {proj₂ L} {proj₂ (F._+_ (σ [→] τ) f (ec (σ [→] τ) f s) L)} pd))
               (F.refl τ (f .idxf .sfunc j) {f .famf .transf j .func y})))))
      (fundamental c D (rγ · rv) (s' +ₛ (w ·ₛ s)) (λ k → body-input γ v (s' +ₛ (w ·ₛ s)) x z (suc k)) (g , y)
         (RelEnv-resp rγ (s' +ₛ (w ·ₛ s)) (λ k → ≈-sym (ap-p₁-++ x z k)) (RelEnv-mono rγ s s' rel) ,
          RelFs-resp σ rv (s' +ₛ (w ·ₛ s)) (λ k → ≈-sym (ap-p₂-++ x z k)) (RelFs-of σ rv (s' +ₛ (w ·ₛ s)) hz)))
    where
    module P = Semimodule (model.FE._⟶_ ⟦ σ ⟧ ⟦ τ ⟧ .fam .fm f)
    L = ⟦ lam t' ⟧tm .famf .transf gi .func g

    -- The payload of the lambda's fibre evaluated at the argument is the body's fibre on the
    -- environment part.
    β : F._≈_ τ (f .idxf .sfunc j)
          (SP.evalΠ (⟦ τ ⟧ .fam indexed-family.[ f .idxf ]) j .func (proj₂ L))
          (⟦ t' ⟧tm .famf .transf (gi , j) .func (g , Semimodule.ε (Fib σ j)))
    Fλ : indexed-family.constantFam (⟦ σ ⟧ .idx) SemiMod.cat (FibC Γ gi)
           indexed-family.⇒f (⟦ τ ⟧ .fam indexed-family.[ f .idxf ])
    Fλ = indexed-family._∘f_ indexed-family.reindex-comp
           (indexed-family._∘f_ (indexed-family.reindex-f (model.FE.nudge gi) (⟦ t' ⟧tm .famf))
                                (model.FE.nudge-in₁ gi))
    β = SP.lambda-eval {A = ⟦ σ ⟧ .idx} {P = ⟦ τ ⟧ .fam indexed-family.[ f .idxf ]} {x = FibC Γ gi} {f = Fλ} j
          .SemiMod._≈m_.*≈* .prop-setoid._≃m_.func-eq (Semimodule.refl (FibC Γ gi) {g})

    pd : P._≈_ (proj₂ L) (proj₂ (F._+_ (σ [→] τ) f (ec (σ [→] τ) f s) L))
    pd = P.sym {proj₂ (F._+_ (σ [→] τ) f (ec (σ [→] τ) f s) L)} {proj₂ L}
           (P.trans {proj₂ (F._+_ (σ [→] τ) f (ec (σ [→] τ) f s) L)} {P._+_ P.ε (proj₂ L)} {proj₂ L}
              (P.+-cong {proj₂ (ec (σ [→] τ) f s)} {P.ε} {proj₂ L} {proj₂ L}
                 (prop._∧_.proj₂ (ec-clo {σ} {τ} f s)) (P.refl {proj₂ L}))
              (P.+-lunit {proj₂ L}))
fundamental (app c₁ c₂) (⇓-app D₁ D₂ D₃) rγ s x g rel = {!!}
