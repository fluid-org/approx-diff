{-# OPTIONS --prop --postfix-projections --safe #-}

-- Agreement between the operational relation and the higher-order model, on the fragment without
-- μ-types and primitives, as a logical relation. A value is related to an index of its type's
-- interpretation by recursion on the type, behaviourally at arrow types: for related arguments and
-- any derivation of the body, the result is related. Over that, a dependence vector on the value's
-- positions is related to an element of the fibre: at first-order types position by position, at
-- arrow types the root exactly and the payload through application, comparing, for any added
-- source weight, the body's dependence through the root and that weight as source and the cells
-- and the argument as environment with the elimination constant at that source plus the
-- evaluation of the payload and the index's fibre map at the argument. Inputs are a source
-- weight and an environment vector,
-- and the environment relation lets a cell carry a control mark dominated by the source, which is
-- how the operational semantics marks values inside a branch where the interpretation marks the
-- branch's result once. The fundamental lemma, by induction on the term over all derivations,
-- says the relation applied to the inputs is related to the term's fibre map at the environment's
-- denotation plus the elimination constant at the source. The absorption of marks needs the
-- elimination weight to be idempotent and to absorb its multiples under addition, and addition
-- to be idempotent, as in a lattice.
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
  -- Addition is idempotent, and the elimination weight is idempotent and absorbs its multiples.
  (+-idem : ∀ x → Setoid._≈_ A (x Sc.+ x) x)
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

-- Rearrangements in a fibre, by the semilattice solver: addition in every semimodule is
-- idempotent when the semiring's is.
open import semilattice-solver using (Expr; var; nil; _⊕_)
import semilattice-solver as SLS
open import Data.Vec using ([]; _∷_)
private
  m-idem : ∀ (X : Semimodule) {x : ∣ X ∣} → Semimodule._≈_ X (Semimodule._+_ X x x) x
  m-idem X {x} =
    Semimodule.trans X (Semimodule.+-cong X (Semimodule.sym X (Semimodule.·-unit X)) (Semimodule.sym X (Semimodule.·-unit X)))
    (Semimodule.trans X (Semimodule.sym X (Semimodule.+-distribʳ X))
    (Semimodule.trans X (Semimodule.·-cong X (+-idem ι) (Semimodule.refl X)) (Semimodule.·-unit X)))

  module SolveF τ i = SLS.Solver (Semimodule.additive (Fib τ i)) (m-idem (Fib τ i))
  module SolveM (X : Semimodule) = SLS.Solver (Semimodule.additive X) (m-idem X)

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
    F.trans τ i (SolveF.solve τ i (var zero ⊕ (var (suc zero) ⊕ var (suc (suc zero))))
                                  (var (suc zero) ⊕ (var (suc (suc zero)) ⊕ var zero)) refl (ec τ i s ∷ d ∷ m ∷ []))
    (F.trans τ i (F.+-cong τ i (F.refl τ i) dm) (F.+-comm τ i))

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

-- Reading the model's constructions elementwise: a pairing through the biproduct is the pair of
-- the components, the lifted action keeps the root and acts on the payload, and eliminating a
-- root applies the continuation to the payload and the constant to the root.
private
  module SMBP = HasProducts (cmon-enriched.biproducts→products SemiMod.cmon-enriched SemiMod.biproduct)

  bpair-elt : ∀ {X Y Z : Semimodule} (f : X ⇒ Y) (g : X ⇒ Z) (x : ∣ X ∣) →
              Semimodule._≈_ (SemiMod._⊕_ Y Z) (SMBP.pair f g .func x) (f .func x , g .func x)
  bpair-elt {X} {Y} {Z} f g x = m-runit Y , m-lunit Z

  Fpair-elt : ∀ {X Y Z : Obj} (f : Mor X Y) (g : Mor X Z) (x : Setoid.Carrier (X .idx)) (z : ∣ X .fam .fm x ∣) →
              Semimodule._≈_ (HasProducts.prod FD.products Y Z .fam .fm (f .idxf .sfunc x , g .idxf .sfunc x))
                (HasProducts.pair FD.products f g .famf .transf x .func z)
                (f .famf .transf x .func z , g .famf .transf x .func z)
  Fpair-elt f g x z = bpair-elt (f .famf .transf x) (g .famf .transf x) z

  Lmap-elt : ∀ {X Y : Semimodule} (f : X ⇒ Y) (a : Setoid.Carrier A) (x : ∣ X ∣) →
             Semimodule._≈_ (Ls.L Y) (Ls.Lmap f .func (a , x)) (a , f .func x)
  Lmap-elt {X} {Y} f a x = +-runit , m-lunit Y

  -- Transport of a lifted product or exponential fibre: the root unchanged, the payload
  -- transported componentwise, or by the map of products.
  subst-prod-elt : ∀ {σ τ} {i i' : Ix σ} {j j' : Ix τ} (E₁ : Setoid._≈_ (⟦ σ ⟧ .idx) i i') (E₂ : Setoid._≈_ (⟦ τ ⟧ .idx) j j')
                   (a : Setoid.Carrier A) (x₁ : ∣ Fib σ i ∣) (x₂ : ∣ Fib τ j ∣) →
                   F._≈_ (σ [×] τ) (i' , j') (⟦ σ [×] τ ⟧ .fam .subst {i , j} {i' , j'} (E₁ , E₂) .func (a , (x₁ , x₂)))
                                            (a , (⟦ σ ⟧ .fam .subst E₁ .func x₁ , ⟦ τ ⟧ .fam .subst E₂ .func x₂))
  subst-prod-elt {σ} {τ} {i} {i'} {j} {j'} E₁ E₂ a x₁ x₂ =
    Semimodule.trans (Fib (σ [×] τ) (i' , j'))
      (Lmap-elt (SMBP.pair (SemiMod._∘_ (⟦ σ ⟧ .fam .subst E₁) (SemiMod.p₁ {Fib σ i} {Fib τ j}))
                           (SemiMod._∘_ (⟦ τ ⟧ .fam .subst E₂) (SemiMod.p₂ {Fib σ i} {Fib τ j}))) a (x₁ , x₂))
      (≈-refl ,
       bpair-elt {SemiMod._⊕_ (Fib σ i) (Fib τ j)} {Fib σ i'} {Fib τ j'}
         (SemiMod._∘_ (⟦ σ ⟧ .fam .subst E₁) (SemiMod.p₁ {Fib σ i} {Fib τ j}))
         (SemiMod._∘_ (⟦ τ ⟧ .fam .subst E₂) (SemiMod.p₂ {Fib σ i} {Fib τ j})) (x₁ , x₂))

  subst-arrow-elt : ∀ {σ τ} {f f' : Ix (σ [→] τ)} (E : Setoid._≈_ (⟦ σ [→] τ ⟧ .idx) f f')
                    (a : Setoid.Carrier A) (x : ∣ model.FE._⟶_ ⟦ σ ⟧ ⟦ τ ⟧ .fam .fm f ∣) →
                    F._≈_ (σ [→] τ) f' (⟦ σ [→] τ ⟧ .fam .subst {f} {f'} E .func (a , x))
                      (a , SP.Π-map (indexed-family.reindex-≈ {P = ⟦ τ ⟧ .fam} (f .idxf) (f' .idxf) (E .FD._≃_.idxf-eq)) .func x)
  subst-arrow-elt {σ} {τ} {f} {f'} E a x =
    Lmap-elt (SP.Π-map (indexed-family.reindex-≈ {P = ⟦ τ ⟧ .fam} (f .idxf) (f' .idxf) (E .FD._≃_.idxf-eq))) a x

  elim-root-elt : ∀ {G X Y : Semimodule} (c : SemiMod.𝕀 ⇒ Y) (r : SemiMod._⊕_ G X ⇒ Y)
                  (γe : ∣ G ∣) (a : Setoid.Carrier A) (y : ∣ X ∣) →
                  Semimodule._≈_ Y (Ls.elim-root c r .func (γe , (a , y)))
                                   (Semimodule._+_ Y (r .func (γe , y)) (c .func a))
  elim-root-elt {G} {X} {Y} c r γe a y =
    Semimodule.+-cong Y
      (r .SemiMod._⇒_.func-resp-≈
         (Semimodule.trans (SemiMod._⊕_ G X)
            (bpair-elt {SemiMod._⊕_ G (Ls.L X)} {G} {X}
               (SemiMod._∘_ (SemiMod.id G) (SemiMod.p₁ {G} {Ls.L X}))
               (SemiMod._∘_ (Ls.payload-L {X}) (SemiMod.p₂ {G} {Ls.L X})) (γe , (a , y)))
            (Semimodule.refl G {γe} , m-lunit X {y})))
      (c .SemiMod._⇒_.func-resp-≈ +-runit)

  elimF-elt : ∀ {Γ' X C : Obj} (cC : Constant C) (f : Mor (HasProducts.prod FD.products Γ' X) C)
              {γi : Setoid.Carrier (Γ' .idx)} {xi : Setoid.Carrier (X .idx)}
              (γe : ∣ Γ' .fam .fm γi ∣) (a : Setoid.Carrier A) (y : ∣ X .fam .fm xi ∣) →
              Semimodule._≈_ (C .fam .fm (f .idxf .sfunc (γi , xi)))
                (FD.elimF cC f .famf .transf (γi , xi) .func (γe , (a , y)))
                (Semimodule._+_ (C .fam .fm (f .idxf .sfunc (γi , xi)))
                  (f .famf .transf (γi , xi) .func (γe , y))
                  (cC .at (f .idxf .sfunc (γi , xi)) .func a))
  elimF-elt cC f {γi} {xi} γe a y = elim-root-elt (cC .at (f .idxf .sfunc (γi , xi))) (f .famf .transf (γi , xi)) γe a y

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
    F.trans τ i (F.+-cong τ i (F.refl τ i) L)
    (F.trans τ i (SolveF.solve τ i (var zero ⊕ (var (suc zero) ⊕ var (suc (suc zero))))
                                   ((var zero ⊕ var (suc (suc zero))) ⊕ var (suc zero)) refl (m ∷ ec τ i s' ∷ ec τ i s ∷ []))
    (F.trans τ i (F.+-cong τ i dm (F.refl τ i))
    (F.trans τ i (F.+-comm τ i) (F.sym τ i L))))
    where
    L : F._≈_ τ i (ec τ i (s' +ₛ (w ·ₛ s))) (F._+_ τ i (ec τ i s') (ec τ i s))
    L = F.trans τ i (ec-linear τ i s' (w ·ₛ s)) (F.+-cong τ i (F.refl τ i) (ec-w τ i s))

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

-- Absorption. A denotational element absorbs the constant at a source weight when adding the
-- constant leaves it unchanged; an element is bounded by the source weight when it is a multiple
-- of the weight times the elimination weight. A relation to a sum with a bounded summand is a
-- relation to the other summand when that summand absorbs the constant: at first-order types the
-- constant absorbs the bounded summand outright, and at arrow types the body's constant at the
-- root does, since the root itself absorbs the source's weight.
Absorbs : ∀ τ (i : Ix τ) → Setoid.Carrier A → ∣ Fib τ i ∣ → Prop
Absorbs τ i s Q = F._≈_ τ i (F._+_ τ i Q (ec τ i s)) Q

Bounded : ∀ τ (i : Ix τ) → Setoid.Carrier A → ∣ Fib τ i ∣ → Prop
Bounded τ i s E = ∃ (∣ Fib τ i ∣) (λ E' → F._≈_ τ i E (F._·_ τ i (s ·ₛ w) E'))

private
  sw-absorb : ∀ s e → ((w ·ₛ s) +ₛ ((s ·ₛ w) ·ₛ e)) ≈s (w ·ₛ s)
  sw-absorb s e =
    ≈-trans (+-cong ·-comm Sc.·-assoc)
    (≈-trans (≈-sym Sc.·-+-distribₗ)
    (≈-trans (·-cong ≈-refl (≈-trans +-comm (w-absorb e))) ·-comm))

  -- A scalar absorbing the weight times the source absorbs any bounded scalar.
  root-absorb : ∀ s a e → (a +ₛ (w ·ₛ s)) ≈s a → (a +ₛ ((s ·ₛ w) ·ₛ e)) ≈s a
  root-absorb s a e h =
    ≈-trans (+-cong (≈-sym h) ≈-refl) (≈-trans +-assoc (≈-trans (+-cong ≈-refl (sw-absorb s e)) h))

  ec-root : ∀ τ (i : Ix τ) s → Absorbs τ i s (ec τ i s)
  ec-root τ i s = F.trans τ i (F.sym τ i (ec-linear τ i s s))
                              (elim-const τ .at i .SemiMod._⇒_.func-resp-≈ (+-idem s))

  -- The absorbing element's root absorbs the weight times the source; the payload absorbs the
  -- payload's constant.
  absorbs-inj₁ : ∀ {σ τ} (i : Ix σ) s (Q : ∣ Fib (σ [+] τ) (inj₁ i) ∣) → Absorbs (σ [+] τ) (inj₁ i) s Q →
                 ((proj₁ Q +ₛ (w ·ₛ s)) ≈s proj₁ Q) ∧ Absorbs σ i s (proj₂ Q)
  absorbs-inj₁ {σ} {τ} i s Q (h₀ , h₁) =
    ≈-trans (+-cong ≈-refl (≈-sym (prop._∧_.proj₁ (ec-inj₁ {σ} {τ} i s)))) h₀ ,
    F.trans σ i (F.+-cong σ i (F.refl σ i) (F.sym σ i (prop._∧_.proj₂ (ec-inj₁ {σ} {τ} i s)))) h₁

  absorbs-inj₂ : ∀ {σ τ} (i : Ix τ) s (Q : ∣ Fib (σ [+] τ) (inj₂ i) ∣) → Absorbs (σ [+] τ) (inj₂ i) s Q →
                 ((proj₁ Q +ₛ (w ·ₛ s)) ≈s proj₁ Q) ∧ Absorbs τ i s (proj₂ Q)
  absorbs-inj₂ {σ} {τ} i s Q (h₀ , h₁) =
    ≈-trans (+-cong ≈-refl (≈-sym (prop._∧_.proj₁ (ec-inj₂ {σ} {τ} i s)))) h₀ ,
    F.trans τ i (F.+-cong τ i (F.refl τ i) (F.sym τ i (prop._∧_.proj₂ (ec-inj₂ {σ} {τ} i s)))) h₁

  absorbs-pair : ∀ {σ τ} (i : Ix σ) (j : Ix τ) s Q → Absorbs (σ [×] τ) (i , j) s Q →
                 ((proj₁ Q +ₛ (w ·ₛ s)) ≈s proj₁ Q) ∧
                 (Absorbs σ i s (proj₁ (proj₂ Q)) ∧ Absorbs τ j s (proj₂ (proj₂ Q)))
  absorbs-pair {σ} {τ} i j s Q (h₀ , (h₁ , h₂)) =
    ≈-trans (+-cong ≈-refl (≈-sym (prop._∧_.proj₁ (ec-pair {σ} {τ} i j s)))) h₀ ,
    (F.trans σ i (F.+-cong σ i (F.refl σ i) (F.sym σ i (prop._∧_.proj₁ (prop._∧_.proj₂ (ec-pair {σ} {τ} i j s))))) h₁ ,
     F.trans τ j (F.+-cong τ j (F.refl τ j) (F.sym τ j (prop._∧_.proj₂ (prop._∧_.proj₂ (ec-pair {σ} {τ} i j s))))) h₂)

  absorbs-clo : ∀ {σ τ} (f : Ix (σ [→] τ)) s Q → Absorbs (σ [→] τ) f s Q → (proj₁ Q +ₛ (w ·ₛ s)) ≈s proj₁ Q
  absorbs-clo {σ} {τ} f s Q (h₀ , _) = ≈-trans (+-cong ≈-refl (≈-sym (prop._∧_.proj₁ (ec-clo {σ} {τ} f s)))) h₀

  -- Transport preserves absorption and boundedness.
  absorbs-subst : ∀ τ {i i' : Ix τ} (e : Setoid._≈_ (⟦ τ ⟧ .idx) i i') s Q → Absorbs τ i s Q →
                  Absorbs τ i' s (⟦ τ ⟧ .fam .subst e .func Q)
  absorbs-subst τ {i} {i'} e s Q h =
    F.trans τ i' (F.+-cong τ i' (F.refl τ i') (F.sym τ i' (ec-natural τ e s)))
    (F.trans τ i' (F.sym τ i' (⟦ τ ⟧ .fam .subst e .SemiMod._⇒_.preserve-+ {Q} {ec τ i s}))
                  (⟦ τ ⟧ .fam .subst e .SemiMod._⇒_.func-resp-≈ h))

  bounded-subst : ∀ τ {i i' : Ix τ} (e : Setoid._≈_ (⟦ τ ⟧ .idx) i i') s E → Bounded τ i s E →
                  Bounded τ i' s (⟦ τ ⟧ .fam .subst e .func E)
  bounded-subst τ {i} {i'} e s E (E' , h) =
    ⟦ τ ⟧ .fam .subst e .func E' ,
    F.trans τ i' (⟦ τ ⟧ .fam .subst e .SemiMod._⇒_.func-resp-≈ h)
                 (⟦ τ ⟧ .fam .subst e .SemiMod._⇒_.preserve-· {s ·ₛ w} {E'})

private
  -- The root of a bounded element is a bounded scalar; a bounded lifted element has bounded parts.
  root-of : ∀ s a b e → a ≈s (b +ₛ ((s ·ₛ w) ·ₛ e)) → (b +ₛ (w ·ₛ s)) ≈s b → a ≈s b
  root-of s a b e ea hb = ≈-trans ea (root-absorb s b e hb)

  ec-abs : ∀ τ (i : Ix τ) s a → (a +ₛ (w ·ₛ s)) ≈s a → Absorbs τ i s (ec τ i a)
  ec-abs τ i s a h =
    F.trans τ i (F.sym τ i (F.trans τ i (elim-const τ .at i .SemiMod._⇒_.func-resp-≈ (≈-sym h))
                                        (F.trans τ i (ec-linear τ i a (w ·ₛ s))
                                                     (F.+-cong τ i (F.refl τ i) (ec-w τ i s)))))
                (F.refl τ i)

-- The constant at the weighted source plus itself and a further weight: the constant at the
-- source plus the constant at the further weight.
private
  ec-double : ∀ τ (i : Ix τ) s a → F._≈_ τ i (ec τ i ((w ·ₛ s) +ₛ ((w ·ₛ s) +ₛ a))) (F._+_ τ i (ec τ i s) (ec τ i a))
  ec-double τ i s a =
    F.trans τ i (ec-linear τ i (w ·ₛ s) ((w ·ₛ s) +ₛ a))
    (F.trans τ i (F.+-cong τ i (ec-w τ i s) (F.trans τ i (ec-linear τ i (w ·ₛ s) a) (F.+-cong τ i (ec-w τ i s) (F.refl τ i))))
    (F.trans τ i (F.sym τ i (F.+-assoc τ i)) (F.+-cong τ i (ec-root τ i s) (F.refl τ i))))

  ec-double' : ∀ τ (i : Ix τ) s a → F._≈_ τ i (ec τ i (((w ·ₛ s) +ₛ a) +ₛ (w ·ₛ s))) (F._+_ τ i (ec τ i s) (ec τ i a))
  ec-double' τ i s a =
    F.trans τ i (elim-const τ .at i .SemiMod._⇒_.func-resp-≈ (≈-trans +-comm (≈-refl {(w ·ₛ s) +ₛ ((w ·ₛ s) +ₛ a)})))
                (ec-double τ i s a)

private
  -- Splitting a bounded lifted element into a bounded root and a bounded payload.
  BoundedA : Setoid.Carrier A → Setoid.Carrier A → Prop
  BoundedA s a = ∃ (Setoid.Carrier A) (λ e → a ≈s ((s ·ₛ w) ·ₛ e))

  bounded-inj₁ : ∀ {σ τ} (i : Ix σ) s E → Bounded (σ [+] τ) (inj₁ i) s E →
                 BoundedA s (proj₁ E) ∧ Bounded σ i s (proj₂ E)
  bounded-inj₁ i s E (E' , (h₀ , h₁)) = (proj₁ E' , h₀) , (proj₂ E' , h₁)

  bounded-inj₂ : ∀ {σ τ} (i : Ix τ) s E → Bounded (σ [+] τ) (inj₂ i) s E →
                 BoundedA s (proj₁ E) ∧ Bounded τ i s (proj₂ E)
  bounded-inj₂ i s E (E' , (h₀ , h₁)) = (proj₁ E' , h₀) , (proj₂ E' , h₁)

  bounded-pair : ∀ {σ τ} (i : Ix σ) (j : Ix τ) s E → Bounded (σ [×] τ) (i , j) s E →
                 BoundedA s (proj₁ E) ∧ (Bounded σ i s (proj₁ (proj₂ E)) ∧ Bounded τ j s (proj₂ (proj₂ E)))
  bounded-pair i j s E (E' , (h₀ , (h₁ , h₂))) = (proj₁ E' , h₀) , ((proj₁ (proj₂ E') , h₁) , (proj₂ (proj₂ E') , h₂))

  bounded-clo : ∀ {σ τ} (f : Ix (σ [→] τ)) s E → Bounded (σ [→] τ) f s E →
                BoundedA s (proj₁ E) ∧
                ∃ (∣ model.FE._⟶_ ⟦ σ ⟧ ⟦ τ ⟧ .fam .fm f ∣)
                  (λ E' → Semimodule._≈_ (model.FE._⟶_ ⟦ σ ⟧ ⟦ τ ⟧ .fam .fm f) (proj₂ E)
                            (Semimodule._·_ (model.FE._⟶_ ⟦ σ ⟧ ⟦ τ ⟧ .fam .fm f) (s ·ₛ w) E'))
  bounded-clo f s E (E' , (h₀ , h₁)) = (proj₁ E' , h₀) , (proj₂ E' , h₁)

  root-abs : ∀ s a b → BoundedA s a → (b +ₛ (w ·ₛ s)) ≈s b → (b +ₛ a) ≈s b
  root-abs s a b (e , ea) hb = ≈-trans (+-cong ≈-refl ea) (root-absorb s b e hb)

RelF-absorb : ∀ τ {v : Val τ} {i : Ix τ} (r : RelV τ v i) s {P : ∣ 𝔽 (width v) ∣} {Q E : ∣ Fib τ i ∣} →
              RelF τ r P (F._+_ τ i Q E) → Absorbs τ i s Q → Bounded τ i s E → RelF τ r P Q
RelF-absorb unit {unit} {i} r s {P} {Q} {E} h hQ (E' , hE) zero =
  ≈-trans (h zero)
          (root-of s (Q zero +ₛ E zero) (Q zero) (E' zero) (+-cong ≈-refl (hE zero))
                   (≈-trans (+-cong ≈-refl (≈-sym (ec-unit i s))) (hQ zero)))
RelF-absorb (σ [+] τ) {inl v} {i} (i' , r , ⟪ e ⟫) s {P} {Q} {E} (h₀ , h) hQ hE =
  let Q' = ⟦ σ [+] τ ⟧ .fam .subst {i} {inj₁ i'} e .func Q
      E' = ⟦ σ [+] τ ⟧ .fam .subst {i} {inj₁ i'} e .func E
      split = ⟦ σ [+] τ ⟧ .fam .subst {i} {inj₁ i'} e .SemiMod._⇒_.preserve-+ {Q} {E}
      hQ' = absorbs-inj₁ {σ} {τ} i' s Q' (absorbs-subst (σ [+] τ) {i} {inj₁ i'} e s Q hQ)
      hE' = bounded-inj₁ {σ} {τ} i' s E' (bounded-subst (σ [+] τ) {i} {inj₁ i'} e s E hE)
  in
  ≈-trans h₀ (≈-trans (prop._∧_.proj₁ split) (root-abs s (proj₁ E') (proj₁ Q') (prop._∧_.proj₁ hE') (prop._∧_.proj₁ hQ'))) ,
  RelF-absorb σ r s (RelF-resp σ r (λ k → ≈-refl) (prop._∧_.proj₂ split) h) (prop._∧_.proj₂ hQ') (prop._∧_.proj₂ hE')
RelF-absorb (σ [+] τ) {inr v} {i} (i' , r , ⟪ e ⟫) s {P} {Q} {E} (h₀ , h) hQ hE =
  let Q' = ⟦ σ [+] τ ⟧ .fam .subst {i} {inj₂ i'} e .func Q
      E' = ⟦ σ [+] τ ⟧ .fam .subst {i} {inj₂ i'} e .func E
      split = ⟦ σ [+] τ ⟧ .fam .subst {i} {inj₂ i'} e .SemiMod._⇒_.preserve-+ {Q} {E}
      hQ' = absorbs-inj₂ {σ} {τ} i' s Q' (absorbs-subst (σ [+] τ) {i} {inj₂ i'} e s Q hQ)
      hE' = bounded-inj₂ {σ} {τ} i' s E' (bounded-subst (σ [+] τ) {i} {inj₂ i'} e s E hE)
  in
  ≈-trans h₀ (≈-trans (prop._∧_.proj₁ split) (root-abs s (proj₁ E') (proj₁ Q') (prop._∧_.proj₁ hE') (prop._∧_.proj₁ hQ'))) ,
  RelF-absorb τ r s (RelF-resp τ r (λ k → ≈-refl) (prop._∧_.proj₂ split) h) (prop._∧_.proj₂ hQ') (prop._∧_.proj₂ hE')
RelF-absorb (σ [×] τ) {pair v u} {i , j} (r , r') s {P} {Q} {E} (h₀ , (h₁ , h₂)) hQ hE =
  let hQ' = absorbs-pair {σ} {τ} i j s Q hQ
      hE' = bounded-pair {σ} {τ} i j s E hE
  in
  ≈-trans h₀ (root-abs s (proj₁ E) (proj₁ Q) (prop._∧_.proj₁ hE') (prop._∧_.proj₁ hQ')) ,
  (RelF-absorb σ r s h₁ (prop._∧_.proj₁ (prop._∧_.proj₂ hQ')) (prop._∧_.proj₁ (prop._∧_.proj₂ hE')) ,
   RelF-absorb τ r' s h₂ (prop._∧_.proj₂ (prop._∧_.proj₂ hQ')) (prop._∧_.proj₂ (prop._∧_.proj₂ hE')))
RelF-absorb (σ [→] τ) {clo γ' t} {f} r s {P} {Q} {E} (h₀ , hc) hQ hE =
  root ,
  λ s' {v} {j} rv z y hz {u} {U} D →
    RelF-absorb τ (r rv D) s
      (RelF-resp τ (r rv D) (λ k → ≈-refl)
         (F.trans τ (f .idxf .sfunc j)
            (F.+-cong τ (f .idxf .sfunc j) (F.refl τ (f .idxf .sfunc j))
               (F.+-cong τ (f .idxf .sfunc j)
                  (SP.evalΠ (⟦ τ ⟧ .fam indexed-family.[ f .idxf ]) j .SemiMod._⇒_.preserve-+ {proj₂ Q} {proj₂ E})
                  (F.refl τ (f .idxf .sfunc j))))
            (SolveF.solve τ (f .idxf .sfunc j)
               (var zero ⊕ ((var (suc zero) ⊕ var (suc (suc zero))) ⊕ var (suc (suc (suc zero)))))
               ((var zero ⊕ (var (suc zero) ⊕ var (suc (suc (suc zero))))) ⊕ var (suc (suc zero))) refl
               (ec τ (f .idxf .sfunc j) (s' +ₛ P zero)
                ∷ SP.evalΠ (⟦ τ ⟧ .fam indexed-family.[ f .idxf ]) j .func (proj₂ Q)
                ∷ SP.evalΠ (⟦ τ ⟧ .fam indexed-family.[ f .idxf ]) j .func (proj₂ E)
                ∷ f .famf .transf j .func y ∷ [])))
         (hc s' rv z y hz D))
      (absQ₁ s' {j} {y})
      (bndE₁ {j} (prop._∧_.proj₂ hE'))
  where
  hE' = bounded-clo {σ} {τ} f s E hE
  root : P zero ≈A proj₁ Q
  root = ≈-trans h₀ (root-abs s (proj₁ E) (proj₁ Q) (prop._∧_.proj₁ hE') (absorbs-clo {σ} {τ} f s Q hQ))
  P₀-abs : (P zero +ₛ (w ·ₛ s)) ≈s P zero
  P₀-abs = ≈-trans (+-cong root ≈-refl) (≈-trans (absorbs-clo {σ} {τ} f s Q hQ) (≈-sym root))
  absQ₁ : ∀ s' {j : Ix σ} {y : ∣ Fib σ j ∣} →
          Absorbs τ (f .idxf .sfunc j) s
            (F._+_ τ (f .idxf .sfunc j) (ec τ (f .idxf .sfunc j) (s' +ₛ P zero))
              (F._+_ τ (f .idxf .sfunc j) (SP.evalΠ (⟦ τ ⟧ .fam indexed-family.[ f .idxf ]) j .func (proj₂ Q))
                                           (f .famf .transf j .func y)))
  absQ₁ s' {j} {y} =
    F.trans τ i₁ (SolveF.solve τ i₁ ((var zero ⊕ (var (suc zero) ⊕ var (suc (suc zero)))) ⊕ var (suc (suc (suc zero))))
                                    ((var zero ⊕ var (suc (suc (suc zero)))) ⊕ (var (suc zero) ⊕ var (suc (suc zero)))) refl
                                    (ec τ i₁ (s' +ₛ P zero) ∷ SP.evalΠ (⟦ τ ⟧ .fam indexed-family.[ f .idxf ]) j .func (proj₂ Q)
                                     ∷ f .famf .transf j .func y ∷ ec τ i₁ s ∷ []))
                 (F.+-cong τ i₁ (ec-abs τ i₁ s (s' +ₛ P zero) (≈-trans +-assoc (+-cong ≈-refl P₀-abs))) (F.refl τ i₁))
    where i₁ = f .idxf .sfunc j
  bndE₁ : ∀ {j : Ix σ} →
          ∃ (∣ model.FE._⟶_ ⟦ σ ⟧ ⟦ τ ⟧ .fam .fm f ∣)
            (λ E' → Semimodule._≈_ (model.FE._⟶_ ⟦ σ ⟧ ⟦ τ ⟧ .fam .fm f) (proj₂ E)
                      (Semimodule._·_ (model.FE._⟶_ ⟦ σ ⟧ ⟦ τ ⟧ .fam .fm f) (s ·ₛ w) E')) →
          Bounded τ (f .idxf .sfunc j) s (SP.evalΠ (⟦ τ ⟧ .fam indexed-family.[ f .idxf ]) j .func (proj₂ E))
  bndE₁ {j} (E' , h) =
    SP.evalΠ (⟦ τ ⟧ .fam indexed-family.[ f .idxf ]) j .func E' ,
    F.trans τ (f .idxf .sfunc j)
      (SP.evalΠ (⟦ τ ⟧ .fam indexed-family.[ f .idxf ]) j .SemiMod._⇒_.func-resp-≈
         {proj₂ E} {Semimodule._·_ (model.FE._⟶_ ⟦ σ ⟧ ⟦ τ ⟧ .fam .fm f) (s ·ₛ w) E'} h)
      (SP.evalΠ (⟦ τ ⟧ .fam indexed-family.[ f .idxf ]) j .SemiMod._⇒_.preserve-· {s ·ₛ w} {E'})

-- Reading the first position of a lifted vector, and its tail, by the projections.
private
  ap-p₁₁ : ∀ {m} (o : ∣ 𝔽 (suc m) ∣) (k : Fin 1) → ap (M.p₁ {1} {m}) o k ≈s o zero
  ap-p₁₁ {m} o zero =
    ≈-trans (Σ-cong {suc m} (λ j → ·-cong (p₁-e {m} j) (≈-refl {o j}))) (Σ-unit {suc m} zero o)

  ap-p₂₁ : ∀ {m} (o : ∣ 𝔽 (suc m) ∣) (k : Fin m) → ap (M.p₂ {1} {m}) o k ≈s o (suc k)
  ap-p₂₁ {m} o k =
    ≈-trans (+-cong ε-annihilₗ (Σ-cong {m} (λ j → ·-cong (p₂-e {m} k j) ≈-refl)))
            (≈-trans +-lunit (Σ-unit {m} k (λ j → o (suc j))))

-- A one-premise rule with the identity routing, read at the inputs: the rule's own columns at the
-- inputs, plus the entry from the premise's root applied to the premise's relation at the inputs.
app-rule₁ : ∀ {Γ} {γ : Env Γ} {n n₀} (out : (i : Input) → M.Matrix n (input-width γ i))
            (up : M.Matrix n n₀) (R' : M.Matrix n₀ (suc (width-env γ))) s x (k : Fin n) →
            ap (of-cols {γ = γ} (M.rule₁-result (M.id-linear (input-width γ)) out up (cols {γ = γ} R')))
               (inputs γ s x) k
            ≈s ((ap (out source) (λ _ → s) k +ₛ ap (out environment) x k) +ₛ ap up (ap R' (inputs γ s x)) k)
app-rule₁ {γ = γ} out up R' s x k =
  ≈-trans (app-of-cols {γ = γ} (M.rule₁-result (M.id-linear (input-width γ)) out up (cols {γ = γ} R')) s x k)
  (≈-trans (+-cong (≈-trans (app-+ₘ (out source) (up ∘ cols {γ = γ} R' source) (λ _ → s) k)
                            (+-cong ≈-refl (app-∘ up (cols {γ = γ} R' source) (λ _ → s) k)))
                   (≈-trans (app-+ₘ (out environment) (up ∘ cols {γ = γ} R' environment) x k)
                            (+-cong ≈-refl (app-∘ up (cols {γ = γ} R' environment) x k))))
  (≈-trans Sc.+-interchange
           (+-cong ≈-refl
                   (≈-trans (≈-sym (app-+ᵥ up (ap (cols {γ = γ} R' source) (λ _ → s)) (ap (cols {γ = γ} R' environment) x) k))
                            (app-congᵥ up (λ l → ≈-sym (app-inputs {γ = γ} R' s x l)) k)))))

-- A two-premise rule with the identity routings and no link, read at the inputs.
app-rule₂-nolink : ∀ {Γ} {γ : Env Γ} {n n₁ n₂} (out : (i : Input) → M.Matrix n (input-width γ i))
                   (u₁ : M.Matrix n n₁) (u₂ : M.Matrix n n₂)
                   (R₁ : M.Matrix n₁ (suc (width-env γ))) (R₂ : M.Matrix n₂ (suc (width-env γ))) s x (k : Fin n) →
                   ap (of-cols {γ = γ} (M.rule₂-result (M.id-linear (input-width γ)) (M.id-linear (input-width γ))
                                          (M.no-link (input-width γ) n₁) out u₁ u₂ (cols {γ = γ} R₁) (cols {γ = γ} R₂)))
                      (inputs γ s x) k
                   ≈s ((ap (out source) (λ _ → s) k +ₛ ap (out environment) x k) +ₛ
                       (ap u₁ (ap R₁ (inputs γ s x)) k +ₛ ap u₂ (ap R₂ (inputs γ s x)) k))
app-rule₂-nolink {γ = γ} {n₁ = n₁} out u₁ u₂ R₁ R₂ s x k =
  ≈-trans (app-of-cols {γ = γ} f s x k)
  (≈-trans (+-cong (per-input source (λ _ → s) k) (per-input environment x k))
  (≈-trans Sc.+-interchange
  (≈-trans (+-cong Sc.+-interchange ≈-refl)
  (≈-trans +-assoc
           (+-cong ≈-refl
                   (+-cong (≈-trans (≈-sym (app-+ᵥ u₁ (ap (c₁ source) (λ _ → s)) (ap (c₁ environment) x) k))
                                    (app-congᵥ u₁ (λ l → ≈-sym (app-inputs {γ = γ} R₁ s x l)) k))
                           (≈-trans (≈-sym (app-+ᵥ u₂ (ap (c₂ source) (λ _ → s)) (ap (c₂ environment) x) k))
                                    (app-congᵥ u₂ (λ l → ≈-sym (app-inputs {γ = γ} R₂ s x l)) k))))))))
  where
  c₁ = cols {γ = γ} R₁
  c₂ = cols {γ = γ} R₂
  f = M.rule₂-result (M.id-linear (input-width γ)) (M.id-linear (input-width γ))
        (M.no-link (input-width γ) n₁) out u₁ u₂ c₁ c₂
  per-input : ∀ (i : Input) (vi : ∣ 𝔽 (input-width γ i) ∣) k →
              ap (f i) vi k ≈s ((ap (out i) vi k +ₛ ap u₁ (ap (c₁ i) vi) k) +ₛ ap u₂ (ap (c₂ i) vi) k)
  per-input i vi k =
    ≈-trans (app-+ₘ (out i +ₘ (u₁ ∘ c₁ i)) (u₂ ∘ (c₂ i +ₘ (εₘ ∘ c₁ i))) vi k)
            (+-cong (≈-trans (app-+ₘ (out i) (u₁ ∘ c₁ i) vi k) (+-cong ≈-refl (app-∘ u₁ (c₁ i) vi k)))
                    (≈-trans (app-∘ u₂ (c₂ i +ₘ (εₘ ∘ c₁ i)) vi k)
                             (app-congᵥ u₂
                                (λ l → ≈-trans (app-+ₘ (c₂ i) (εₘ ∘ c₁ i) vi l)
                                               (≈-trans (+-cong ≈-refl (≈-trans (app-∘ εₘ (c₁ i) vi l)
                                                                                (app-εₘ (ap (c₁ i) vi) l)))
                                                        +-runit)) k)))

-- The case rule, read at the inputs: the branch's relation at the scrutinee's root plus the
-- weighted source as source, and at the environment and the scrutinee's payload as environment.
app-case : ∀ {Γ τ'} {γ : Env Γ} (v : Val τ') {n} (R_s : M.Matrix (suc (width v)) (suc (width-env γ)))
           (T : M.Matrix n (suc (width-env (γ · v)))) s x (k : Fin n) →
           ap (of-cols {γ = γ} (M.rule₂-result (M.id-linear (input-width γ)) (branch-route γ v) (branch-link γ v)
                                  (λ _ → εₘ) εₘ M.I (cols {γ = γ} R_s) (cols {γ = γ · v} T)))
              (inputs γ s x) k
           ≈s ap T (inputs (γ · v) (ap R_s (inputs γ s x) zero +ₛ (w ·ₛ s))
                     (λ l → ap (M.in₁ {width-env γ} {width v}) x l +ₛ
                            ap (M.in₂ {width-env γ} {width v}) (λ m → ap R_s (inputs γ s x) (suc m)) l)) k
app-case {γ = γ} v R_s T s x k =
  ≈-trans (app-of-cols {γ = γ} f s x k)
  (≈-trans (+-cong (per-input source (λ _ → s) k) (per-input environment x k))
  (≈-trans Sc.+-interchange
  (≈-trans (+-cong src-part (≈-trans (+-cong (app-∘ (l .M.at cT) (cs source) (λ _ → s) k)
                                              (app-∘ (l .M.at cT) (cs environment) x k))
                                     (≈-trans (≈-sym (app-+ᵥ (l .M.at cT) (ap (cs source) (λ _ → s)) (ap (cs environment) x) k))
                                              (≈-trans (app-congᵥ (l .M.at cT) (λ m → ≈-sym (app-inputs {γ = γ} R_s s x m)) k)
                                                       l-expand))))
  (≈-trans regroup
  (≈-trans (+-cong (≈-sym (app-+ᵥ (cT source) (λ _ → w ·ₛ s) (λ _ → o_s zero) k))
                   (≈-sym (app-+ᵥ (cT environment) (ap (M.in₁ {width-env γ} {width v}) x)
                                                   (ap (M.in₂ {width-env γ} {width v}) (λ m → o_s (suc m))) k)))
  (≈-trans (+-cong (app-congᵥ (cT source) (λ _ → +-comm {w ·ₛ s} {o_s zero}) k) (≈-refl {ap (cT environment) X k}))
           (≈-sym (app-inputs {γ = γ · v} T (o_s zero +ₛ (w ·ₛ s)) X k))))))))
  where
  cs = cols {γ = γ} R_s
  cT = cols {γ = γ · v} T
  r₂ = branch-route γ v
  l = branch-link γ v
  f = M.rule₂-result (M.id-linear (input-width γ)) r₂ l (λ _ → εₘ) εₘ M.I cs cT
  o_s = ap R_s (inputs γ s x)
  X : ∣ 𝔽 (width-env γ + width v) ∣
  X m = ap (M.in₁ {width-env γ} {width v}) x m +ₛ ap (M.in₂ {width-env γ} {width v}) (λ m' → o_s (suc m')) m

  per-input : ∀ (i : Input) (vi : ∣ 𝔽 (input-width γ i) ∣) k →
              ap (f i) vi k ≈s (ap (r₂ .M.ap cT i) vi k +ₛ ap (l .M.at cT ∘ cs i) vi k)
  per-input i vi k =
    ≈-trans (app-+ₘ (εₘ +ₘ (εₘ ∘ cs i)) (M.I ∘ (r₂ .M.ap cT i +ₘ (l .M.at cT ∘ cs i))) vi k)
    (≈-trans (+-cong (≈-trans (app-+ₘ εₘ (εₘ ∘ cs i) vi k)
                              (≈-trans (+-cong (app-εₘ vi k) (≈-trans (app-∘ εₘ (cs i) vi k) (app-εₘ (ap (cs i) vi) k)))
                                       +-lunit))
                     (≈-trans (app-∘ M.I (r₂ .M.ap cT i +ₘ (l .M.at cT ∘ cs i)) vi k)
                              (≈-trans (app-I (ap (r₂ .M.ap cT i +ₘ (l .M.at cT ∘ cs i)) vi) k)
                                       (app-+ₘ (r₂ .M.ap cT i) (l .M.at cT ∘ cs i) vi k))))
             +-lunit)

  src-part : (ap (r₂ .M.ap cT source) (λ _ → s) k +ₛ ap (r₂ .M.ap cT environment) x k)
             ≈s (ap (cT source) (λ _ → w ·ₛ s) k +ₛ ap (cT environment) (ap (M.in₁ {width-env γ} {width v}) x) k)
  src-part =
    +-cong (≈-trans (app-∘ (cT source) (ctrl-row {1}) (λ _ → s) k)
                    (app-congᵥ (cT source) (λ m → ap-ctrl-row {1} s m) k))
           (app-∘ (cT environment) (M.in₁ {width-env γ} {width v}) x k)

  l-expand : ap (l .M.at cT) o_s k ≈s
             (ap (cT environment) (ap (M.in₂ {width-env γ} {width v}) (λ m → o_s (suc m))) k +ₛ
              ap (cT source) (λ _ → o_s zero) k)
  l-expand =
    ≈-trans (app-+ₘ (cT environment ∘ (M.in₂ {width-env γ} {width v} ∘ M.p₂ {1} {width v}))
                    (cT source ∘ M.p₁ {1} {width v}) o_s k)
            (+-cong (≈-trans (app-∘ (cT environment) (M.in₂ {width-env γ} {width v} ∘ M.p₂ {1} {width v}) o_s k)
                             (≈-trans (app-congᵥ (cT environment)
                                         (λ m → app-∘ (M.in₂ {width-env γ} {width v}) (M.p₂ {1} {width v}) o_s m) k)
                                      (app-congᵥ (cT environment)
                                         (app-congᵥ (M.in₂ {width-env γ} {width v}) (ap-p₂₁ {width v} o_s)) k)))
                    (≈-trans (app-∘ (cT source) (M.p₁ {1} {width v}) o_s k)
                             (app-congᵥ (cT source) (ap-p₁₁ {width v} o_s) k)))

  regroup : ∀ {a b c d} → (a +ₛ b) +ₛ (c +ₛ d) ≈s ((a +ₛ d) +ₛ (b +ₛ c))
  regroup = ≈-trans (+-cong ≈-refl +-comm) Sc.+-interchange

-- A built constructor, read at the inputs: the weight at the new root, the premise's relation
-- after.
private
  built-zero : ∀ {Γ} {γ : Env Γ} {n} (R' : M.Matrix n (suc (width-env γ))) s x →
               ap (of-cols {γ = γ} (M.rule₁-result (M.id-linear (input-width γ)) (built-out γ n) (M.in₂ {1}) (cols {γ = γ} R')))
                  (inputs γ s x) zero ≈s (w ·ₛ s)
  built-zero {γ = γ} {n} R' s x =
    ≈-trans (app-rule₁ {γ = γ} (built-out γ n) (M.in₂ {1}) R' s x zero)
    (≈-trans (+-cong (+-cong (≈-trans (app-∘ (M.in₁ {1} {n}) (ctrl-row {1}) (λ _ → s) zero)
                                      (≈-trans (ap-in₁-zero {n} (ap (ctrl-row {1}) (λ _ → s))) (ap-ctrl-row {1} s zero)))
                             (app-εₘ {1} {width-env γ} x zero))
                     (ap-in₂-zero {n} (ap R' (inputs γ s x))))
             (≈-trans +-runit +-runit))

  built-suc : ∀ {Γ} {γ : Env Γ} {n} (R' : M.Matrix n (suc (width-env γ))) s x k →
              ap (of-cols {γ = γ} (M.rule₁-result (M.id-linear (input-width γ)) (built-out γ n) (M.in₂ {1}) (cols {γ = γ} R')))
                 (inputs γ s x) (suc k) ≈s ap R' (inputs γ s x) k
  built-suc {γ = γ} {n} R' s x k =
    ≈-trans (app-rule₁ {γ = γ} (built-out γ n) (M.in₂ {1}) R' s x (suc k))
    (≈-trans (+-cong (+-cong (≈-trans (app-∘ (M.in₁ {1} {n}) (ctrl-row {1}) (λ _ → s) (suc k))
                                      (ap-in₁-suc {n} (ap (ctrl-row {1}) (λ _ → s)) k))
                             (app-εₘ {suc n} {width-env γ} x (suc k)))
                     (ap-in₂-suc {n} (ap R' (inputs γ s x)) k))
             (≈-trans (+-cong +-runit ≈-refl) +-lunit))

-- A projection, read at the inputs: the result's control positions at the weighted source plus
-- the consumed root, and the projection of the pair's payload.
private
  proj-op : ∀ {Γ τ'} {γ : Env Γ} (wv : Val τ') {m n} (P : M.Matrix (width wv) (m + n))
            (R' : M.Matrix (suc (m + n)) (suc (width-env γ))) s x k →
            ap (of-cols {γ = γ} (M.rule₁-result (M.id-linear (input-width γ)) (elim-out γ wv) (proj-up {m} {n} wv P) (cols {γ = γ} R')))
               (inputs γ s x) k
            ≈s (ap (ctrl-of wv) (λ _ → (w ·ₛ s) +ₛ ap R' (inputs γ s x) zero) k +ₛ
                ap P (λ l → ap R' (inputs γ s x) (suc l)) k)
  proj-op {γ = γ} wv {m} {n} P R' s x k =
    ≈-trans (app-rule₁ {γ = γ} (elim-out γ wv) (proj-up {m} {n} wv P) R' s x k)
    (≈-trans (+-cong (≈-trans (+-cong (≈-trans (app-∘ (ctrl-of wv) (ctrl-row {1}) (λ _ → s) k)
                                               (app-congᵥ (ctrl-of wv) (λ l → ap-ctrl-row {1} s l) k))
                                      (app-εₘ {width wv} {width-env γ} x k))
                              +-runit)
                     (≈-trans (app-+ₘ (P ∘ M.p₂ {1} {m + n}) (ctrl-of wv ∘ M.p₁ {1} {m + n}) o' k)
                              (+-cong (≈-trans (app-∘ P (M.p₂ {1} {m + n}) o' k)
                                               (app-congᵥ P (ap-p₂₁ {m + n} o') k))
                                      (≈-trans (app-∘ (ctrl-of wv) (M.p₁ {1} {m + n}) o' k)
                                               (app-congᵥ (ctrl-of wv) (ap-p₁₁ {m + n} o') k)))))
    (≈-trans (+-cong ≈-refl +-comm)
    (≈-trans (≈-sym +-assoc)
             (+-cong (≈-sym (app-+ᵥ (ctrl-of wv) (λ _ → w ·ₛ s) (λ _ → o' zero) k)) ≈-refl))))
    where o' = ap R' (inputs γ s x)

  -- The constant at the weighted source plus the consumed root, with the pair's component, against
  -- the constant at the source with the projection's fibre.
  proj-den : ∀ τ' (i : Ix τ') s a₀ o'₀ (comp G m : ∣ Fib τ' i ∣) →
             o'₀ ≈s ((w ·ₛ s) +ₛ a₀) →
             F._≈_ τ' i comp (F._+_ τ' i (ec τ' i s) m) →
             F._≈_ τ' i G (F._+_ τ' i m (ec τ' i a₀)) →
             F._≈_ τ' i (F._+_ τ' i (ec τ' i ((w ·ₛ s) +ₛ o'₀)) comp) (F._+_ τ' i (ec τ' i s) G)
  proj-den τ' i s a₀ o'₀ comp G m eo ecomp eG =
    F.trans τ' i (F.+-cong τ' i ec-part ecomp)
    (F.trans τ' i rearr (F.+-cong τ' i (F.refl τ' i) (F.sym τ' i eG)))
    where
    ec-part : F._≈_ τ' i (ec τ' i ((w ·ₛ s) +ₛ o'₀)) (F._+_ τ' i (ec τ' i s) (ec τ' i a₀))
    ec-part = F.trans τ' i (elim-const τ' .at i .SemiMod._⇒_.func-resp-≈ (+-cong ≈-refl eo)) (ec-double τ' i s a₀)
    rearr : F._≈_ τ' i (F._+_ τ' i (F._+_ τ' i (ec τ' i s) (ec τ' i a₀)) (F._+_ τ' i (ec τ' i s) m))
                       (F._+_ τ' i (ec τ' i s) (F._+_ τ' i m (ec τ' i a₀)))
    rearr = SolveF.solve τ' i ((var zero ⊕ var (suc zero)) ⊕ (var zero ⊕ var (suc (suc zero))))
                              (var zero ⊕ (var (suc (suc zero)) ⊕ var (suc zero))) refl (ec τ' i s ∷ ec τ' i a₀ ∷ m ∷ [])

-- Transport along a reflexivity proof is the identity.
private
  subst-refl : ∀ τ {i : Ix τ} (e : Setoid._≈_ (⟦ τ ⟧ .idx) i i) (d : ∣ Fib τ i ∣) →
               F._≈_ τ i (⟦ τ ⟧ .fam .subst e .func d) d
  subst-refl τ {i} e d = ⟦ τ ⟧ .fam .indexed-family.Fam.refl* .SemiMod._≈m_.*≈* .prop-setoid._≃m_.func-eq (F.refl τ i {d})

-- Transporting a relation along an index equation.
RelF-transport : ∀ τ {v : Val τ} {i i' : Ix τ} (E : Setoid._≈_ (⟦ τ ⟧ .idx) i i') (r : RelV τ v i)
                 {o : ∣ 𝔽 (width v) ∣} {d : ∣ Fib τ i ∣} →
                 RelF τ r o d → RelF τ (RelV-resp τ E r) o (⟦ τ ⟧ .fam .subst E .func d)
RelF-transport unit {unit} {i} {i'} E r {o} {d} h k =
  ≈-trans (h k) (≈-sym (subst-refl unit {i} E d k))
RelF-transport (σ [+] τ) {inl v} {i} {i'} E (i₀ , r₀ , ⟪ e₀ ⟫) {o} {d} (h₀ , h) =
  let e' = Setoid.trans (⟦ σ [+] τ ⟧ .idx) {i'} {i} {inj₁ i₀} (Setoid.sym (⟦ σ [+] τ ⟧ .idx) {i} {i'} E) e₀
      comp = ⟦ σ [+] τ ⟧ .fam .indexed-family.Fam.trans* {i} {i'} {inj₁ i₀} e' E
               .SemiMod._≈m_.*≈* .prop-setoid._≃m_.func-eq (F.refl (σ [+] τ) i {d})
  in
  ≈-trans h₀ (prop._∧_.proj₁ comp) ,
  RelF-resp σ r₀ (λ k → ≈-refl) (prop._∧_.proj₂ comp) h
RelF-transport (σ [+] τ) {inr v} {i} {i'} E (i₀ , r₀ , ⟪ e₀ ⟫) {o} {d} (h₀ , h) =
  let e' = Setoid.trans (⟦ σ [+] τ ⟧ .idx) {i'} {i} {inj₂ i₀} (Setoid.sym (⟦ σ [+] τ ⟧ .idx) {i} {i'} E) e₀
      comp = ⟦ σ [+] τ ⟧ .fam .indexed-family.Fam.trans* {i} {i'} {inj₂ i₀} e' E
               .SemiMod._≈m_.*≈* .prop-setoid._≃m_.func-eq (F.refl (σ [+] τ) i {d})
  in
  ≈-trans h₀ (prop._∧_.proj₁ comp) ,
  RelF-resp τ r₀ (λ k → ≈-refl) (prop._∧_.proj₂ comp) h
RelF-transport (σ [×] τ) {pair v u} {i , j} {i' , j'} (E₁ , E₂) (r₁ , r₂) {o} {d} (h₀ , (h₁ , h₂)) =
  let se = subst-prod-elt {σ} {τ} {i} {i'} {j} {j'} E₁ E₂ (proj₁ d) (proj₁ (proj₂ d)) (proj₂ (proj₂ d)) in
  ≈-trans h₀ (≈-sym (prop._∧_.proj₁ se)) ,
  (RelF-resp σ (RelV-resp σ E₁ r₁) (λ k → ≈-refl) (F.sym σ i' (prop._∧_.proj₁ (prop._∧_.proj₂ se))) (RelF-transport σ E₁ r₁ h₁) ,
   RelF-resp τ (RelV-resp τ E₂ r₂) (λ k → ≈-refl) (F.sym τ j' (prop._∧_.proj₂ (prop._∧_.proj₂ se))) (RelF-transport τ E₂ r₂ h₂))
RelF-transport (σ [→] τ) {clo γ' t} {f} {f'} E r {o} {d} (h₀ , hc) =
  ≈-trans h₀ (≈-sym (prop._∧_.proj₁ (subst-arrow-elt {σ} {τ} {f} {f'} E (proj₁ d) (proj₂ d)))) ,
  λ s' {v} {j} rv z y hz {u} {U} D →
    RelF-resp τ (RelV-resp τ (Ej j) (r rv D)) (λ k → ≈-refl)
      (F.trans τ (f' .idxf .sfunc j)
         (⟦ τ ⟧ .fam .subst (Ej j) .SemiMod._⇒_.preserve-+ {ec τ (f .idxf .sfunc j) (s' +ₛ o zero)} {_})
      (F.+-cong τ (f' .idxf .sfunc j) (ec-natural τ (Ej j) (s' +ₛ o zero))
      (F.trans τ (f' .idxf .sfunc j)
         (⟦ τ ⟧ .fam .subst (Ej j) .SemiMod._⇒_.preserve-+ {_} {_})
      (F.+-cong τ (f' .idxf .sfunc j) (eval-part j) (arg-part j y)))))
      (RelF-transport τ (Ej j) (r rv D) (hc s' rv z y hz D))
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
            (prop._∧_.proj₂ (subst-arrow-elt {σ} {τ} {f} {f'} E (proj₁ d) (proj₂ d)))))
  arg-part : ∀ j (y : ∣ Fib σ j ∣) →
             F._≈_ τ (f' .idxf .sfunc j) (⟦ τ ⟧ .fam .subst (Ej j) .func (f .famf .transf j .func y))
                                        (f' .famf .transf j .func y)
  arg-part j y = E .FD._≃_.famf-eq .indexed-family._≃f_.transf-eq {j} .SemiMod._≈m_.*≈* .prop-setoid._≃m_.func-eq
                   (Semimodule.refl (Fib σ j) {y})

-- The branch of a case: its environment is related at the scrutinee's root plus the weighted
-- source, the scrutinee's payload carrying the source's constant as a mark.
private
  branch-env : ∀ {Γ τk} {γ : Env Γ} {gi} (rγ : RelVEnv γ gi) {v : Val τk} {i'} (r_v : RelV τk v i')
               s x g (o_s : ∣ 𝔽 (suc (width v)) ∣) (y_v : ∣ Fib τk i' ∣) →
               RelEnv rγ s x g → RelF τk r_v (λ m → o_s (suc m)) (F._+_ τk i' y_v (ec τk i' s)) →
               RelEnv (rγ · r_v) (o_s zero +ₛ (w ·ₛ s))
                 (λ m → ap (M.in₁ {width-env γ} {width v}) x m +ₛ ap (M.in₂ {width-env γ} {width v}) (λ m' → o_s (suc m')) m)
                 (g , y_v)
  branch-env {τk = τk} {γ = γ} rγ {v} {i'} r_v s x g o_s y_v rel h =
    RelEnv-resp rγ Sw (λ m → ≈-sym (ap-p₁-++ x (λ m' → o_s (suc m')) m)) (RelEnv-mono rγ s (o_s zero) rel) ,
    RelFs-resp τk r_v Sw (λ m → ≈-sym (ap-p₂-++ x (λ m' → o_s (suc m')) m)) (ec τk i' s , (dom-s , h))
    where
    Sw = o_s zero +ₛ (w ·ₛ s)
    dom-s : Dominated τk i' Sw (ec τk i' s)
    dom-s =
      F.trans τk i' (F.+-cong τk i' (F.refl τk i') L)
      (F.trans τk i' (SolveF.solve τk i' (var zero ⊕ (var (suc zero) ⊕ var zero)) (var (suc zero) ⊕ var zero) refl
                                         (ec τk i' s ∷ ec τk i' (o_s zero) ∷ []))
                     (F.sym τk i' L))
      where
      L : F._≈_ τk i' (ec τk i' Sw) (F._+_ τk i' (ec τk i' (o_s zero)) (ec τk i' s))
      L = F.trans τk i' (ec-linear τk i' (o_s zero) (w ·ₛ s)) (F.+-cong τk i' (F.refl τk i') (ec-w τk i' s))

  -- Transport there and back is the identity.
  roundtrip : ∀ τ {i₁ ic : Ix τ} (E : Setoid._≈_ (⟦ τ ⟧ .idx) i₁ ic) (Eidx : Setoid._≈_ (⟦ τ ⟧ .idx) ic i₁)
              (d : ∣ Fib τ ic ∣) →
              F._≈_ τ ic (⟦ τ ⟧ .fam .subst E .func (⟦ τ ⟧ .fam .subst Eidx .func d)) d
  roundtrip τ {i₁} {ic} E Eidx d =
    F.trans τ ic
      (F.sym τ ic (⟦ τ ⟧ .fam .indexed-family.Fam.trans* {ic} {i₁} {ic} E Eidx
                     .SemiMod._≈m_.*≈* .prop-setoid._≃m_.func-eq (F.refl τ ic {d})))
      (subst-refl τ {ic} (Setoid.trans (⟦ τ ⟧ .idx) {ic} {i₁} {ic} Eidx E) d)

  -- The branch's constant and fibre, transported, against the case's.
  case-den : ∀ τ {i₁ ic : Ix τ} (E : Setoid._≈_ (⟦ τ ⟧ .idx) i₁ ic) s a_s o_s₀ (B : ∣ Fib τ i₁ ∣) (CF : ∣ Fib τ ic ∣) →
             o_s₀ ≈s ((w ·ₛ s) +ₛ a_s) →
             F._≈_ τ ic CF (F._+_ τ ic (⟦ τ ⟧ .fam .subst E .func B) (ec τ ic a_s)) →
             F._≈_ τ ic (⟦ τ ⟧ .fam .subst E .func (F._+_ τ i₁ (ec τ i₁ (o_s₀ +ₛ (w ·ₛ s))) B))
                        (F._+_ τ ic (ec τ ic s) CF)
  case-den τ {i₁} {ic} E s a_s o_s₀ B CF eo eCF =
    F.trans τ ic (subst-ec+ τ E (o_s₀ +ₛ (w ·ₛ s)) B)
    (F.trans τ ic (F.+-cong τ ic ec-part (F.refl τ ic))
    (F.trans τ ic (SolveF.solve τ ic ((var zero ⊕ var (suc zero)) ⊕ var (suc (suc zero)))
                                     (var zero ⊕ (var (suc (suc zero)) ⊕ var (suc zero))) refl
                                     (ec τ ic s ∷ ec τ ic a_s ∷ ⟦ τ ⟧ .fam .subst E .func B ∷ []))
                  (F.+-cong τ ic (F.refl τ ic) (F.sym τ ic eCF))))
    where
    ec-part : F._≈_ τ ic (ec τ ic (o_s₀ +ₛ (w ·ₛ s))) (F._+_ τ ic (ec τ ic s) (ec τ ic a_s))
    ec-part = F.trans τ ic (elim-const τ .at ic .SemiMod._⇒_.func-resp-≈ (+-cong eo ≈-refl)) (ec-double' τ ic s a_s)

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
fundamental {Γ = Γ} {τ = τ₁ [+] τ₂} (inl {t = t} c) {γ = γ} (⇓-inl {v = v} {R = R'} D) {gi} rγ s x g rel =
  ≈-trans (built-zero {γ = γ} R' s x) (≈-sym (≈-trans (prop._∧_.proj₁ (subst-refl (τ₁ [+] τ₂) {inj₁ i'} e d)) root-den)) ,
  RelF-resp τ₁ (relV c D rγ) (λ k → ≈-sym (built-suc {γ = γ} R' s x k))
    (F.sym τ₁ i' (F.trans τ₁ i' (prop._∧_.proj₂ (subst-refl (τ₁ [+] τ₂) {inj₁ i'} e d))
                                (F.+-cong τ₁ i' (prop._∧_.proj₂ (ec-inj₁ {τ₁} {τ₂} i' s)) (F.refl τ₁ i'))))
    (fundamental c D rγ s x g rel)
  where
  i' = ⟦ t ⟧tm .idxf .sfunc gi
  e = Setoid.refl (⟦ τ₁ [+] τ₂ ⟧ .idx) {inj₁ i'}
  d = F._+_ (τ₁ [+] τ₂) (inj₁ i') (ec (τ₁ [+] τ₂) (inj₁ i') s) (⟦ inl {τ₂ = τ₂} t ⟧tm .famf .transf gi .func g)
  root-den : proj₁ d ≈s (w ·ₛ s)
  root-den = ≈-trans (+-cong (prop._∧_.proj₁ (ec-inj₁ {τ₁} {τ₂} i' s)) (≈-refl {ε})) +-runit
fundamental {Γ = Γ} {τ = τ₁ [+] τ₂} (inr {t = t} c) {γ = γ} (⇓-inr {v = v} {R = R'} D) {gi} rγ s x g rel =
  ≈-trans (built-zero {γ = γ} R' s x) (≈-sym (≈-trans (prop._∧_.proj₁ (subst-refl (τ₁ [+] τ₂) {inj₂ i'} e d)) root-den)) ,
  RelF-resp τ₂ (relV c D rγ) (λ k → ≈-sym (built-suc {γ = γ} R' s x k))
    (F.sym τ₂ i' (F.trans τ₂ i' (prop._∧_.proj₂ (subst-refl (τ₁ [+] τ₂) {inj₂ i'} e d))
                                (F.+-cong τ₂ i' (prop._∧_.proj₂ (ec-inj₂ {τ₁} {τ₂} i' s)) (F.refl τ₂ i'))))
    (fundamental c D rγ s x g rel)
  where
  i' = ⟦ t ⟧tm .idxf .sfunc gi
  e = Setoid.refl (⟦ τ₁ [+] τ₂ ⟧ .idx) {inj₂ i'}
  d = F._+_ (τ₁ [+] τ₂) (inj₂ i') (ec (τ₁ [+] τ₂) (inj₂ i') s) (⟦ inr {τ₁ = τ₁} t ⟧tm .famf .transf gi .func g)
  root-den : proj₁ d ≈s (w ·ₛ s)
  root-den = ≈-trans (+-cong (prop._∧_.proj₁ (ec-inj₂ {τ₁} {τ₂} i' s)) (≈-refl {ε})) +-runit
fundamental {Γ = Γ} {τ = τ} (case {τ₁ = τ₁} {τ₂ = τ₂} {s = sc} {t₁ = t₁} {t₂ = t₂} c c₁ c₂) {γ = γ}
            (⇓-case-l {v = v} {u = u} {R = R_s} {T = T} D₁ D₂) {gi} rγ s x g rel =
  RelF-resp τ (RelV-resp τ E r') (λ k → ≈-sym (app-case {γ = γ} v R_s T s x k))
    (case-den τ E s a_s (o_s zero) B (⟦ case sc t₁ t₂ ⟧tm .famf .transf gi .func g) o_s₀ case-famf)
    (RelF-transport τ E r' (fundamental c₁ D₂ (rγ · r_v) (o_s zero +ₛ (w ·ₛ s)) X (g , y_v)
                              (branch-env rγ r_v s x g o_s y_v rel payload₁)))
  where
  rs = relV c D₁ rγ
  i' = proj₁ rs
  r_v = proj₁ (proj₂ rs)
  e : Setoid._≈_ (⟦ τ₁ [+] τ₂ ⟧ .idx) (⟦ sc ⟧tm .idxf .sfunc gi) (inj₁ i')
  e = prop.Prf.prf (proj₂ (proj₂ rs))
  sidx = ⟦ sc ⟧tm .idxf .sfunc gi
  SC = HasStrongCoproducts.copair FD.strongCoproducts (FD.elimF (elim-const τ) ⟦ t₁ ⟧tm) (FD.elimF (elim-const τ) ⟦ t₂ ⟧tm)
  Eidx : Setoid._≈_ (⟦ τ ⟧ .idx) (⟦ case sc t₁ t₂ ⟧tm .idxf .sfunc gi) (⟦ t₁ ⟧tm .idxf .sfunc (gi , i'))
  Eidx = SC .idxf .prop-setoid._⇒_.func-resp-≈ {gi , sidx} {gi , inj₁ i'} (Setoid.refl (⟦ Γ ⟧ctxt .idx) {gi} , e)
  E : Setoid._≈_ (⟦ τ ⟧ .idx) (⟦ t₁ ⟧tm .idxf .sfunc (gi , i')) (⟦ case sc t₁ t₂ ⟧tm .idxf .sfunc gi)
  E = Setoid.sym (⟦ τ ⟧ .idx) Eidx
  i₁ = ⟦ t₁ ⟧tm .idxf .sfunc (gi , i')
  ic = ⟦ case sc t₁ t₂ ⟧tm .idxf .sfunc gi
  r' = relV c₁ D₂ (rγ · r_v)
  o_s = ap R_s (inputs γ s x)
  X : ∣ 𝔽 (width-env γ + width v) ∣
  X m = ap (M.in₁ {width-env γ} {width v}) x m +ₛ ap (M.in₂ {width-env γ} {width v}) (λ m' → o_s (suc m')) m
  IH₁ = fundamental c D₁ rγ s x g rel
  SG = ⟦ τ₁ [+] τ₂ ⟧ .fam .subst {sidx} {inj₁ i'} e .func (⟦ sc ⟧tm .famf .transf gi .func g)
  a_s = proj₁ SG
  y_v = proj₂ SG
  split-sum = subst-ec+ (τ₁ [+] τ₂) {sidx} {inj₁ i'} e s (⟦ sc ⟧tm .famf .transf gi .func g)

  o_s₀ : o_s zero ≈s ((w ·ₛ s) +ₛ a_s)
  o_s₀ = ≈-trans (prop._∧_.proj₁ IH₁)
                 (≈-trans (prop._∧_.proj₁ split-sum) (+-cong (prop._∧_.proj₁ (ec-inj₁ {τ₁} {τ₂} i' s)) ≈-refl))

  payload₁ : RelF τ₁ r_v (λ m → o_s (suc m)) (F._+_ τ₁ i' y_v (ec τ₁ i' s))
  payload₁ =
    RelF-resp τ₁ r_v (λ m → ≈-refl)
      (F.trans τ₁ i' (prop._∧_.proj₂ split-sum)
        (F.trans τ₁ i' (F.+-cong τ₁ i' (prop._∧_.proj₂ (ec-inj₁ {τ₁} {τ₂} i' s)) (F.refl τ₁ i')) (F.+-comm τ₁ i')))
      (prop._∧_.proj₂ IH₁)

  B = ⟦ t₁ ⟧tm .famf .transf (gi , i') .func (g , y_v)

  -- The case's fibre at the environment, through the naturality of the strong copairing along
  -- the scrutinee's index equation.
  Dom = HasProducts.prod FD.products ⟦ Γ ⟧ctxt ⟦ τ₁ [+] τ₂ ⟧
  Pg = HasProducts.pair FD.products (Category.id FD.cat ⟦ Γ ⟧ctxt) ⟦ sc ⟧tm .famf .transf gi .func g
  Q = Dom .fam .subst {gi , sidx} {gi , inj₁ i'} (Setoid.refl (⟦ Γ ⟧ctxt .idx) {gi} , e) .func Pg
  CF = ⟦ case sc t₁ t₂ ⟧tm .famf .transf gi .func g

  case-famf : F._≈_ τ ic CF (F._+_ τ ic (⟦ τ ⟧ .fam .subst E .func B) (ec τ ic a_s))
  case-famf =
    F.trans τ ic (F.sym τ ic (roundtrip τ E Eidx CF))
    (F.trans τ ic (⟦ τ ⟧ .fam .subst E .SemiMod._⇒_.func-resp-≈ {⟦ τ ⟧ .fam .subst Eidx .func CF} {F._+_ τ i₁ B (ec τ i₁ a_s)}
                    (F.trans τ i₁ (F.sym τ i₁ nat) branch-eq))
    (F.trans τ ic (⟦ τ ⟧ .fam .subst E .SemiMod._⇒_.preserve-+ {B} {ec τ i₁ a_s})
                  (F.+-cong τ ic (F.refl τ ic) (ec-natural τ E a_s))))
    where
    nat : F._≈_ τ i₁ (SC .famf .transf (gi , inj₁ i') .func Q) (⟦ τ ⟧ .fam .subst Eidx .func CF)
    nat = SC .famf .indexed-family._⇒f_.natural {gi , sidx} {gi , inj₁ i'} (Setoid.refl (⟦ Γ ⟧ctxt .idx) {gi} , e)
            .SemiMod._≈m_.*≈* .prop-setoid._≃m_.func-eq {Pg} {Pg} (Semimodule.refl (Dom .fam .fm (gi , sidx)) {Pg})

    Q≈ : Semimodule._≈_ (Dom .fam .fm (gi , inj₁ i')) Q (g , SG)
    Q≈ = Semimodule.trans (Dom .fam .fm (gi , inj₁ i'))
           (Dom .fam .subst {gi , sidx} {gi , inj₁ i'} (Setoid.refl (⟦ Γ ⟧ctxt .idx) {gi} , e) .SemiMod._⇒_.func-resp-≈
              (Fpair-elt {⟦ Γ ⟧ctxt} {⟦ Γ ⟧ctxt} {⟦ τ₁ [+] τ₂ ⟧} (Category.id FD.cat ⟦ Γ ⟧ctxt) ⟦ sc ⟧tm gi g))
           (Semimodule.trans (Dom .fam .fm (gi , inj₁ i'))
              (bpair-elt {SemiMod._⊕_ (FibC Γ gi) (Fib (τ₁ [+] τ₂) sidx)} {FibC Γ gi} {Fib (τ₁ [+] τ₂) (inj₁ i')}
                         (SemiMod._∘_ (⟦ Γ ⟧ctxt .fam .subst {gi} {gi} (Setoid.refl (⟦ Γ ⟧ctxt .idx) {gi}))
                                      (SemiMod.p₁ {FibC Γ gi} {Fib (τ₁ [+] τ₂) sidx}))
                         (SemiMod._∘_ (⟦ τ₁ [+] τ₂ ⟧ .fam .subst {sidx} {inj₁ i'} e)
                                      (SemiMod.p₂ {FibC Γ gi} {Fib (τ₁ [+] τ₂) sidx}))
                         (g , ⟦ sc ⟧tm .famf .transf gi .func g))
              (⟦ Γ ⟧ctxt .fam .indexed-family.Fam.refl* .SemiMod._≈m_.*≈* .prop-setoid._≃m_.func-eq
                 (Semimodule.refl (FibC Γ gi) {g}) ,
               F.refl (τ₁ [+] τ₂) (inj₁ i')))

    branch-eq : F._≈_ τ i₁ (SC .famf .transf (gi , inj₁ i') .func Q) (F._+_ τ i₁ B (ec τ i₁ a_s))
    branch-eq =
      F.trans τ i₁ (SC .famf .transf (gi , inj₁ i') .SemiMod._⇒_.func-resp-≈ {Q} {g , SG} Q≈)
                   (elimF-elt {⟦ Γ ⟧ctxt} {⟦ τ₁ ⟧} {⟦ τ ⟧} (elim-const τ) ⟦ t₁ ⟧tm {gi} {i'} g a_s y_v)
fundamental {Γ = Γ} {τ = τ} (case {τ₁ = τ₁} {τ₂ = τ₂} {s = sc} {t₁ = t₁} {t₂ = t₂} c c₁ c₂) {γ = γ}
            (⇓-case-r {v = v} {u = u} {R = R_s} {T = T} D₁ D₂) {gi} rγ s x g rel =
  RelF-resp τ (RelV-resp τ E r') (λ k → ≈-sym (app-case {γ = γ} v R_s T s x k))
    (case-den τ E s a_s (o_s zero) B (⟦ case sc t₁ t₂ ⟧tm .famf .transf gi .func g) o_s₀ case-famf)
    (RelF-transport τ E r' (fundamental c₂ D₂ (rγ · r_v) (o_s zero +ₛ (w ·ₛ s)) X (g , y_v)
                              (branch-env rγ r_v s x g o_s y_v rel payload₁)))
  where
  rs = relV c D₁ rγ
  i' = proj₁ rs
  r_v = proj₁ (proj₂ rs)
  e : Setoid._≈_ (⟦ τ₁ [+] τ₂ ⟧ .idx) (⟦ sc ⟧tm .idxf .sfunc gi) (inj₂ i')
  e = prop.Prf.prf (proj₂ (proj₂ rs))
  sidx = ⟦ sc ⟧tm .idxf .sfunc gi
  SC = HasStrongCoproducts.copair FD.strongCoproducts (FD.elimF (elim-const τ) ⟦ t₁ ⟧tm) (FD.elimF (elim-const τ) ⟦ t₂ ⟧tm)
  Eidx : Setoid._≈_ (⟦ τ ⟧ .idx) (⟦ case sc t₁ t₂ ⟧tm .idxf .sfunc gi) (⟦ t₂ ⟧tm .idxf .sfunc (gi , i'))
  Eidx = SC .idxf .prop-setoid._⇒_.func-resp-≈ {gi , sidx} {gi , inj₂ i'} (Setoid.refl (⟦ Γ ⟧ctxt .idx) {gi} , e)
  E : Setoid._≈_ (⟦ τ ⟧ .idx) (⟦ t₂ ⟧tm .idxf .sfunc (gi , i')) (⟦ case sc t₁ t₂ ⟧tm .idxf .sfunc gi)
  E = Setoid.sym (⟦ τ ⟧ .idx) Eidx
  i₁ = ⟦ t₂ ⟧tm .idxf .sfunc (gi , i')
  ic = ⟦ case sc t₁ t₂ ⟧tm .idxf .sfunc gi
  r' = relV c₂ D₂ (rγ · r_v)
  o_s = ap R_s (inputs γ s x)
  X : ∣ 𝔽 (width-env γ + width v) ∣
  X m = ap (M.in₁ {width-env γ} {width v}) x m +ₛ ap (M.in₂ {width-env γ} {width v}) (λ m' → o_s (suc m')) m
  IH₁ = fundamental c D₁ rγ s x g rel
  SG = ⟦ τ₁ [+] τ₂ ⟧ .fam .subst {sidx} {inj₂ i'} e .func (⟦ sc ⟧tm .famf .transf gi .func g)
  a_s = proj₁ SG
  y_v = proj₂ SG
  split-sum = subst-ec+ (τ₁ [+] τ₂) {sidx} {inj₂ i'} e s (⟦ sc ⟧tm .famf .transf gi .func g)

  o_s₀ : o_s zero ≈s ((w ·ₛ s) +ₛ a_s)
  o_s₀ = ≈-trans (prop._∧_.proj₁ IH₁)
                 (≈-trans (prop._∧_.proj₁ split-sum) (+-cong (prop._∧_.proj₁ (ec-inj₂ {τ₁} {τ₂} i' s)) ≈-refl))

  payload₁ : RelF τ₂ r_v (λ m → o_s (suc m)) (F._+_ τ₂ i' y_v (ec τ₂ i' s))
  payload₁ =
    RelF-resp τ₂ r_v (λ m → ≈-refl)
      (F.trans τ₂ i' (prop._∧_.proj₂ split-sum)
        (F.trans τ₂ i' (F.+-cong τ₂ i' (prop._∧_.proj₂ (ec-inj₂ {τ₁} {τ₂} i' s)) (F.refl τ₂ i')) (F.+-comm τ₂ i')))
      (prop._∧_.proj₂ IH₁)

  B = ⟦ t₂ ⟧tm .famf .transf (gi , i') .func (g , y_v)

  -- The case's fibre at the environment, through the naturality of the strong copairing along
  -- the scrutinee's index equation.
  Dom = HasProducts.prod FD.products ⟦ Γ ⟧ctxt ⟦ τ₁ [+] τ₂ ⟧
  Pg = HasProducts.pair FD.products (Category.id FD.cat ⟦ Γ ⟧ctxt) ⟦ sc ⟧tm .famf .transf gi .func g
  Q = Dom .fam .subst {gi , sidx} {gi , inj₂ i'} (Setoid.refl (⟦ Γ ⟧ctxt .idx) {gi} , e) .func Pg
  CF = ⟦ case sc t₁ t₂ ⟧tm .famf .transf gi .func g

  case-famf : F._≈_ τ ic CF (F._+_ τ ic (⟦ τ ⟧ .fam .subst E .func B) (ec τ ic a_s))
  case-famf =
    F.trans τ ic (F.sym τ ic (roundtrip τ E Eidx CF))
    (F.trans τ ic (⟦ τ ⟧ .fam .subst E .SemiMod._⇒_.func-resp-≈ {⟦ τ ⟧ .fam .subst Eidx .func CF} {F._+_ τ i₁ B (ec τ i₁ a_s)}
                    (F.trans τ i₁ (F.sym τ i₁ nat) branch-eq))
    (F.trans τ ic (⟦ τ ⟧ .fam .subst E .SemiMod._⇒_.preserve-+ {B} {ec τ i₁ a_s})
                  (F.+-cong τ ic (F.refl τ ic) (ec-natural τ E a_s))))
    where
    nat : F._≈_ τ i₁ (SC .famf .transf (gi , inj₂ i') .func Q) (⟦ τ ⟧ .fam .subst Eidx .func CF)
    nat = SC .famf .indexed-family._⇒f_.natural {gi , sidx} {gi , inj₂ i'} (Setoid.refl (⟦ Γ ⟧ctxt .idx) {gi} , e)
            .SemiMod._≈m_.*≈* .prop-setoid._≃m_.func-eq {Pg} {Pg} (Semimodule.refl (Dom .fam .fm (gi , sidx)) {Pg})

    Q≈ : Semimodule._≈_ (Dom .fam .fm (gi , inj₂ i')) Q (g , SG)
    Q≈ = Semimodule.trans (Dom .fam .fm (gi , inj₂ i'))
           (Dom .fam .subst {gi , sidx} {gi , inj₂ i'} (Setoid.refl (⟦ Γ ⟧ctxt .idx) {gi} , e) .SemiMod._⇒_.func-resp-≈
              (Fpair-elt {⟦ Γ ⟧ctxt} {⟦ Γ ⟧ctxt} {⟦ τ₁ [+] τ₂ ⟧} (Category.id FD.cat ⟦ Γ ⟧ctxt) ⟦ sc ⟧tm gi g))
           (Semimodule.trans (Dom .fam .fm (gi , inj₂ i'))
              (bpair-elt {SemiMod._⊕_ (FibC Γ gi) (Fib (τ₁ [+] τ₂) sidx)} {FibC Γ gi} {Fib (τ₁ [+] τ₂) (inj₂ i')}
                         (SemiMod._∘_ (⟦ Γ ⟧ctxt .fam .subst {gi} {gi} (Setoid.refl (⟦ Γ ⟧ctxt .idx) {gi}))
                                      (SemiMod.p₁ {FibC Γ gi} {Fib (τ₁ [+] τ₂) sidx}))
                         (SemiMod._∘_ (⟦ τ₁ [+] τ₂ ⟧ .fam .subst {sidx} {inj₂ i'} e)
                                      (SemiMod.p₂ {FibC Γ gi} {Fib (τ₁ [+] τ₂) sidx}))
                         (g , ⟦ sc ⟧tm .famf .transf gi .func g))
              (⟦ Γ ⟧ctxt .fam .indexed-family.Fam.refl* .SemiMod._≈m_.*≈* .prop-setoid._≃m_.func-eq
                 (Semimodule.refl (FibC Γ gi) {g}) ,
               F.refl (τ₁ [+] τ₂) (inj₂ i')))

    branch-eq : F._≈_ τ i₁ (SC .famf .transf (gi , inj₂ i') .func Q) (F._+_ τ i₁ B (ec τ i₁ a_s))
    branch-eq =
      F.trans τ i₁ (SC .famf .transf (gi , inj₂ i') .SemiMod._⇒_.func-resp-≈ {Q} {g , SG} Q≈)
                   (elimF-elt {⟦ Γ ⟧ctxt} {⟦ τ₂ ⟧} {⟦ τ ⟧} (elim-const τ) ⟦ t₂ ⟧tm {gi} {i'} g a_s y_v)
fundamental {Γ = Γ} {τ = σ [×] τ} (pair {s = M} {t = N} c₁ c₂) {γ = γ} (⇓-pair {v = v} {u = u} {R = R₁} {T = R₂} D₁ D₂) {gi} rγ s x g rel =
  root , (RelF-resp σ r₁ (λ k → ≈-sym (comp₁ k)) den₁ IH₁ , RelF-resp τ r₂ (λ k → ≈-sym (comp₂ k)) den₂ IH₂)
  where
  i = ⟦ M ⟧tm .idxf .sfunc gi
  j = ⟦ N ⟧tm .idxf .sfunc gi
  r₁ = relV c₁ D₁ rγ
  r₂ = relV c₂ D₂ rγ
  IH₁ = fundamental c₁ D₁ rγ s x g rel
  IH₂ = fundamental c₂ D₂ rγ s x g rel
  o₁ = ap R₁ (inputs γ s x)
  o₂ = ap R₂ (inputs γ s x)
  y₁ = ⟦ M ⟧tm .famf .transf gi .func g
  y₂ = ⟦ N ⟧tm .famf .transf gi .func g
  u₁ = M.in₂ {1} ∘ M.in₁ {width v} {width u}
  u₂ = M.in₂ {1} ∘ M.in₂ {width v} {width u}
  o = ap (of-cols {γ = γ} (M.rule₂-result (M.id-linear (input-width γ)) (M.id-linear (input-width γ))
                             (M.no-link (input-width γ) (width v)) (built-out γ (width v + width u)) u₁ u₂
                             (cols {γ = γ} R₁) (cols {γ = γ} R₂)))
         (inputs γ s x)
  d = F._+_ (σ [×] τ) (i , j) (ec (σ [×] τ) (i , j) s) (⟦ pair M N ⟧tm .famf .transf gi .func g)

  op-eq : ∀ k → o k ≈s ((ap (M.in₁ {1} {width v + width u} ∘ ctrl-row {1}) (λ _ → s) k +ₛ ε) +ₛ
                        (ap (M.in₂ {1} {width v + width u}) (ap (M.in₁ {width v} {width u}) o₁) k +ₛ
                         ap (M.in₂ {1} {width v + width u}) (ap (M.in₂ {width v} {width u}) o₂) k))
  op-eq k =
    ≈-trans (app-rule₂-nolink {γ = γ} (built-out γ (width v + width u)) u₁ u₂ R₁ R₂ s x k)
            (+-cong (+-cong ≈-refl (app-εₘ x k))
                    (+-cong (app-∘ (M.in₂ {1}) (M.in₁ {width v} {width u}) o₁ k)
                            (app-∘ (M.in₂ {1}) (M.in₂ {width v} {width u}) o₂ k)))

  tail-eq : ∀ k → o (suc k) ≈s (ap (M.in₁ {width v} {width u}) o₁ k +ₛ ap (M.in₂ {width v} {width u}) o₂ k)
  tail-eq k =
    ≈-trans (op-eq (suc k))
            (≈-trans (+-cong (≈-trans (+-cong (≈-trans (app-∘ (M.in₁ {1} {width v + width u}) (ctrl-row {1}) (λ _ → s) (suc k))
                                                       (ap-in₁-suc {width v + width u} (ap (ctrl-row {1}) (λ _ → s)) k))
                                              ≈-refl)
                                      +-runit)
                             (+-cong (ap-in₂-suc {width v + width u} _ k) (ap-in₂-suc {width v + width u} _ k)))
                     +-lunit)

  root : o zero ≈A proj₁ d
  root =
    ≈-trans (op-eq zero)
    (≈-trans (+-cong (≈-trans (+-cong (≈-trans (app-∘ (M.in₁ {1} {width v + width u}) (ctrl-row {1}) (λ _ → s) zero)
                                               (≈-trans (ap-in₁-zero {width v + width u} (ap (ctrl-row {1}) (λ _ → s)))
                                                        (ap-ctrl-row {1} s zero)))
                                      ≈-refl)
                              +-runit)
                     (≈-trans (+-cong (ap-in₂-zero {width v + width u} _) (ap-in₂-zero {width v + width u} _)) +-runit))
    (≈-trans +-runit
             (≈-sym (≈-trans (+-cong (prop._∧_.proj₁ (ec-pair {σ} {τ} i j s)) (≈-refl {ε})) +-runit))))

  comp₁ : ∀ k → ap (M.p₁ {width v} {width u}) (λ l → o (suc l)) k ≈s o₁ k
  comp₁ k = ≈-trans (app-congᵥ (M.p₁ {width v} {width u}) tail-eq k) (ap-p₁-++ o₁ o₂ k)

  comp₂ : ∀ k → ap (M.p₂ {width v} {width u}) (λ l → o (suc l)) k ≈s o₂ k
  comp₂ k = ≈-trans (app-congᵥ (M.p₂ {width v} {width u}) tail-eq k) (ap-p₂-++ o₁ o₂ k)

  den₁ : F._≈_ σ i (F._+_ σ i (ec σ i s) y₁) (proj₁ (proj₂ d))
  den₁ = F.sym σ i (F.+-cong σ i (prop._∧_.proj₁ (prop._∧_.proj₂ (ec-pair {σ} {τ} i j s))) (m-runit (Fib σ i)))

  den₂ : F._≈_ τ j (F._+_ τ j (ec τ j s) y₂) (proj₂ (proj₂ d))
  den₂ = F.sym τ j (F.+-cong τ j (prop._∧_.proj₂ (prop._∧_.proj₂ (ec-pair {σ} {τ} i j s))) (m-lunit (Fib τ j)))
fundamental {Γ = Γ} {τ = σ} (fst {τ₂ = τ} {t = t} c) {γ = γ} (⇓-fst {v = v} {u = u} {R = R'} D) {gi} rγ s x g rel =
  RelF-resp σ r₁ (λ k → ≈-sym (proj-op {γ = γ} v {width v} {width u} (M.p₁ {width v} {width u}) R' s x k))
    (proj-den σ i s a₀ (o' zero) (proj₁ (proj₂ (F._+_ (σ [×] τ) ij (ec (σ [×] τ) ij s) Mg)))
       (⟦ fst {τ₂ = τ} t ⟧tm .famf .transf gi .func g) m₁
       o'₀ (F.+-cong σ i (prop._∧_.proj₁ (prop._∧_.proj₂ (ec-pair {σ} {τ} i (proj₂ ij) s))) (F.refl σ i)) G-form)
    (ctrl-add σ r₁ ((w ·ₛ s) +ₛ o' zero) (prop._∧_.proj₁ (prop._∧_.proj₂ IH)))
  where
  ij = ⟦ t ⟧tm .idxf .sfunc gi
  i = proj₁ ij
  r₁ = proj₁ (relV c D rγ)
  IH = fundamental c D rγ s x g rel
  o' = ap R' (inputs γ s x)
  Mg = ⟦ t ⟧tm .famf .transf gi .func g
  a₀ = proj₁ Mg
  m₁ = proj₁ (proj₂ Mg)
  o'₀ : o' zero ≈s ((w ·ₛ s) +ₛ a₀)
  o'₀ = ≈-trans (prop._∧_.proj₁ IH) (+-cong (prop._∧_.proj₁ (ec-pair {σ} {τ} i (proj₂ ij) s)) (≈-refl {a₀}))
  G-form : F._≈_ σ i (⟦ fst {τ₂ = τ} t ⟧tm .famf .transf gi .func g) (F._+_ σ i m₁ (ec σ i a₀))
  G-form =
    F.trans σ i (FD.elimF (elim-const σ) body .famf .transf (gi , ij) .SemiMod._⇒_.func-resp-≈
                   (Fpair-elt {⟦ Γ ⟧ctxt} {⟦ Γ ⟧ctxt} {⟦ σ [×] τ ⟧} (Category.id FD.cat ⟦ Γ ⟧ctxt) ⟦ t ⟧tm gi g))
                (elimF-elt {⟦ Γ ⟧ctxt} {HasProducts.prod FD.products ⟦ σ ⟧ ⟦ τ ⟧} {⟦ σ ⟧} (elim-const σ) body {gi} {ij} g a₀ (proj₂ Mg))
    where body = Category._∘_ FD.cat (HasProducts.p₁ FD.products {⟦ σ ⟧} {⟦ τ ⟧})
                                     (HasProducts.p₂ FD.products {⟦ Γ ⟧ctxt} {HasProducts.prod FD.products ⟦ σ ⟧ ⟦ τ ⟧})
fundamental {Γ = Γ} {τ = τ} (snd {τ₁ = σ} {t = t} c) {γ = γ} (⇓-snd {v = v} {u = u} {R = R'} D) {gi} rγ s x g rel =
  RelF-resp τ r₂ (λ k → ≈-sym (proj-op {γ = γ} u {width v} {width u} (M.p₂ {width v} {width u}) R' s x k))
    (proj-den τ j s a₀ (o' zero) (proj₂ (proj₂ (F._+_ (σ [×] τ) ij (ec (σ [×] τ) ij s) Mg)))
       (⟦ snd {τ₁ = σ} t ⟧tm .famf .transf gi .func g) m₂
       o'₀ (F.+-cong τ j (prop._∧_.proj₂ (prop._∧_.proj₂ (ec-pair {σ} {τ} (proj₁ ij) j s))) (F.refl τ j)) G-form)
    (ctrl-add τ r₂ ((w ·ₛ s) +ₛ o' zero) (prop._∧_.proj₂ (prop._∧_.proj₂ IH)))
  where
  ij = ⟦ t ⟧tm .idxf .sfunc gi
  j = proj₂ ij
  r₂ = proj₂ (relV c D rγ)
  IH = fundamental c D rγ s x g rel
  o' = ap R' (inputs γ s x)
  Mg = ⟦ t ⟧tm .famf .transf gi .func g
  a₀ = proj₁ Mg
  m₂ = proj₂ (proj₂ Mg)
  o'₀ : o' zero ≈s ((w ·ₛ s) +ₛ a₀)
  o'₀ = ≈-trans (prop._∧_.proj₁ IH) (+-cong (prop._∧_.proj₁ (ec-pair {σ} {τ} (proj₁ ij) j s)) (≈-refl {a₀}))
  G-form : F._≈_ τ j (⟦ snd {τ₁ = σ} t ⟧tm .famf .transf gi .func g) (F._+_ τ j m₂ (ec τ j a₀))
  G-form =
    F.trans τ j (FD.elimF (elim-const τ) body .famf .transf (gi , ij) .SemiMod._⇒_.func-resp-≈
                   (Fpair-elt {⟦ Γ ⟧ctxt} {⟦ Γ ⟧ctxt} {⟦ σ [×] τ ⟧} (Category.id FD.cat ⟦ Γ ⟧ctxt) ⟦ t ⟧tm gi g))
                (elimF-elt {⟦ Γ ⟧ctxt} {HasProducts.prod FD.products ⟦ σ ⟧ ⟦ τ ⟧} {⟦ τ ⟧} (elim-const τ) body {gi} {ij} g a₀ (proj₂ Mg))
    where body = Category._∘_ FD.cat (HasProducts.p₂ FD.products {⟦ σ ⟧} {⟦ τ ⟧})
                                     (HasProducts.p₂ FD.products {⟦ Γ ⟧ctxt} {HasProducts.prod FD.products ⟦ σ ⟧ ⟦ τ ⟧})
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
fundamental {Γ = Γ} {τ = τ} (app {σ = σ} {s = M} {t = N} c₁ c₂) {γ = γ}
            (⇓-app {Γ' = Γ'} {γ' = γ'} {t' = t'} {v = v} {u = u} {R = R} {T = T} {U = U} D₁ D₂ D₃) {gi} rγ s x g rel =
  RelF-resp τ r₃ (λ k → ≈-sym (app-op k)) (F.refl τ i₁)
    (RelF-absorb τ r₃ s (RelF-resp τ r₃ (λ k → ≈-refl) den-eq C) absG bndE)
  where
  f = ⟦ M ⟧tm .idxf .sfunc gi
  j = ⟦ N ⟧tm .idxf .sfunc gi
  i₁ = f .idxf .sfunc j
  r₁ = relV c₁ D₁ rγ
  r₂ = relV c₂ D₂ rγ
  r₃ = r₁ r₂ D₃
  IH₁ = fundamental c₁ D₁ rγ s x g rel
  IH₂ = fundamental c₂ D₂ rγ s x g rel
  a = proj₁ (⟦ M ⟧tm .famf .transf gi .func g)
  m = proj₂ (⟦ M ⟧tm .famf .transf gi .func g)
  yN = ⟦ N ⟧tm .famf .transf gi .func g
  E = f .famf .transf j .func (ec σ j s)
  G = F._+_ τ i₁ (ec τ i₁ s) (⟦ app M N ⟧tm .famf .transf gi .func g)
  module P = Semimodule (model.FE._⟶_ ⟦ σ ⟧ ⟦ τ ⟧ .fam .fm f)
  evalΠj = SP.evalΠ (⟦ τ ⟧ .fam indexed-family.[ f .idxf ]) j
  -- The operational vectors of the function and the argument, and of the application.
  o : ∣ 𝔽 (suc (width-env γ')) ∣
  o = ap R (inputs γ s x)
  z : ∣ 𝔽 (width v) ∣
  z = ap T (inputs γ s x)

  -- The clause of the function's relation at the application's weighted source and the argument.
  C : RelF τ r₃ (ap U (body-input γ' v ((w ·ₛ s) +ₛ o zero) (λ l → o (suc l)) z))
        (F._+_ τ i₁ (ec τ i₁ ((w ·ₛ s) +ₛ o zero))
          (F._+_ τ i₁ (evalΠj .func (proj₂ (F._+_ (σ [→] τ) f (ec (σ [→] τ) f s) (⟦ M ⟧tm .famf .transf gi .func g))))
                      (f .famf .transf j .func (F._+_ σ j (ec σ j s) yN))))
  C = prop._∧_.proj₂ IH₁ (w ·ₛ s) r₂ z (F._+_ σ j (ec σ j s) yN) IH₂ D₃

  o₀ : o zero ≈s ((w ·ₛ s) +ₛ a)
  o₀ = ≈-trans (prop._∧_.proj₁ IH₁) (+-cong (prop._∧_.proj₁ (ec-clo {σ} {τ} f s)) ≈-refl)

  -- The clause's constant, evaluation and argument against the application's.
  den-eq : F._≈_ τ i₁
             (F._+_ τ i₁ (ec τ i₁ ((w ·ₛ s) +ₛ o zero))
               (F._+_ τ i₁ (evalΠj .func (proj₂ (F._+_ (σ [→] τ) f (ec (σ [→] τ) f s) (⟦ M ⟧tm .famf .transf gi .func g))))
                           (f .famf .transf j .func (F._+_ σ j (ec σ j s) yN))))
             (F._+_ τ i₁ G E)
  den-eq =
    F.trans τ i₁ (F.+-cong τ i₁ ec-part (F.+-cong τ i₁ eval-part arg-part)) rearr
    where
    G-form : F._≈_ τ i₁ (⟦ app M N ⟧tm .famf .transf gi .func g)
               (F._+_ τ i₁ (F._+_ τ i₁ (evalΠj .func m) (f .famf .transf j .func yN)) (ec τ i₁ a))
    G-form =
      F.trans τ i₁ (FD.elimF (elim-const τ) body .famf .transf (gi , f) .SemiMod._⇒_.func-resp-≈
                      {HasProducts.pair FD.products (Category.id FD.cat ⟦ Γ ⟧ctxt) ⟦ M ⟧tm .famf .transf gi .func g} {g , (a , m)}
                      (Fpair-elt {⟦ Γ ⟧ctxt} {⟦ Γ ⟧ctxt} {⟦ σ [→] τ ⟧} (Category.id FD.cat ⟦ Γ ⟧ctxt) ⟦ M ⟧tm gi g))
      (F.trans τ i₁ (elimF-elt {⟦ Γ ⟧ctxt} {Ex} {⟦ τ ⟧} (elim-const τ) body {gi} {f} g a m)
                    (F.+-cong τ i₁ (HasWeakExponentials.eval model.SemiModExp {⟦ σ ⟧} {⟦ τ ⟧} .famf .transf (f , j) .SemiMod._⇒_.func-resp-≈
                                      {HasProducts.pair FD.products (HasProducts.p₂ FD.products {⟦ Γ ⟧ctxt} {Ex})
                                         (Category._∘_ FD.cat ⟦ N ⟧tm (HasProducts.p₁ FD.products {⟦ Γ ⟧ctxt} {Ex})) .famf .transf (gi , f) .func (g , m)}
                                      {m , yN}
                                      (Fpair-elt {HasProducts.prod FD.products ⟦ Γ ⟧ctxt Ex} {Ex} {⟦ σ ⟧}
                                         (HasProducts.p₂ FD.products {⟦ Γ ⟧ctxt} {Ex})
                                         (Category._∘_ FD.cat ⟦ N ⟧tm (HasProducts.p₁ FD.products {⟦ Γ ⟧ctxt} {Ex})) (gi , f) (g , m)))
                                   (F.refl τ i₁)))
      where
      Ex = HasWeakExponentials.exp model.SemiModExp ⟦ σ ⟧ ⟦ τ ⟧
      body = Category._∘_ FD.cat (HasWeakExponentials.eval model.SemiModExp {⟦ σ ⟧} {⟦ τ ⟧})
               (HasProducts.pair FD.products (HasProducts.p₂ FD.products {⟦ Γ ⟧ctxt} {Ex})
                                             (Category._∘_ FD.cat ⟦ N ⟧tm (HasProducts.p₁ FD.products {⟦ Γ ⟧ctxt} {Ex})))

    ec-part : F._≈_ τ i₁ (ec τ i₁ ((w ·ₛ s) +ₛ o zero)) (F._+_ τ i₁ (ec τ i₁ s) (ec τ i₁ a))
    ec-part = F.trans τ i₁ (elim-const τ .at i₁ .SemiMod._⇒_.func-resp-≈ (+-cong ≈-refl o₀)) (ec-double τ i₁ s a)

    eval-part : F._≈_ τ i₁ (evalΠj .func (proj₂ (F._+_ (σ [→] τ) f (ec (σ [→] τ) f s) (⟦ M ⟧tm .famf .transf gi .func g))))
                           (evalΠj .func m)
    eval-part =
      F.trans τ i₁ (evalΠj .SemiMod._⇒_.preserve-+ {proj₂ (ec (σ [→] τ) f s)} {m})
      (F.trans τ i₁ (F.+-cong τ i₁ (F.trans τ i₁ (evalΠj .SemiMod._⇒_.func-resp-≈ {proj₂ (ec (σ [→] τ) f s)} {P.ε}
                                                    (prop._∧_.proj₂ (ec-clo {σ} {τ} f s)))
                                                 (evalΠj .SemiMod._⇒_.preserve-ze))
                                   (F.refl τ i₁))
                    (m-lunit (Fib τ i₁)))

    arg-part : F._≈_ τ i₁ (f .famf .transf j .func (F._+_ σ j (ec σ j s) yN)) (F._+_ τ i₁ E (f .famf .transf j .func yN))
    arg-part = f .famf .transf j .SemiMod._⇒_.preserve-+ {ec σ j s} {yN}

    rearr : F._≈_ τ i₁
              (F._+_ τ i₁ (F._+_ τ i₁ (ec τ i₁ s) (ec τ i₁ a))
                          (F._+_ τ i₁ (evalΠj .func m) (F._+_ τ i₁ E (f .famf .transf j .func yN))))
              (F._+_ τ i₁ G E)
    rearr =
      F.trans τ i₁
        (SolveF.solve τ i₁ ((var zero ⊕ var (suc zero)) ⊕ (var (suc (suc zero)) ⊕ (var (suc (suc (suc zero))) ⊕ var (suc (suc (suc (suc zero)))))))
                           ((var zero ⊕ ((var (suc (suc zero)) ⊕ var (suc (suc (suc (suc zero))))) ⊕ var (suc zero))) ⊕ var (suc (suc (suc zero)))) refl
                           (ec τ i₁ s ∷ ec τ i₁ a ∷ evalΠj .func m ∷ E ∷ f .famf .transf j .func yN ∷ []))
        (F.+-cong τ i₁ (F.+-cong τ i₁ (F.refl τ i₁) (F.sym τ i₁ G-form)) (F.refl τ i₁))

  absG : Absorbs τ i₁ s G
  absG = SolveF.solve τ i₁ ((var zero ⊕ var (suc zero)) ⊕ var zero) (var zero ⊕ var (suc zero)) refl
                           (ec τ i₁ s ∷ ⟦ app M N ⟧tm .famf .transf gi .func g ∷ [])

  bndE : Bounded τ i₁ s E
  bndE = f .famf .transf j .func (ty-unit σ (λ ()) (λ ()) .at j .func ι) ,
         F.trans τ i₁
           (f .famf .transf j .SemiMod._⇒_.func-resp-≈ {ec σ j s}
              {F._·_ σ j (s ·ₛ w) (ty-unit σ (λ ()) (λ ()) .at j .func ι)}
              (F.trans σ j (ty-unit σ (λ ()) (λ ()) .at j .SemiMod._⇒_.func-resp-≈
                              {w ·ₛ s +ₛ ε} {(s ·ₛ w) ·ₛ ι} (≈-trans +-runit (≈-trans ·-comm (≈-sym ·-runit))))
                           (ty-unit σ (λ ()) (λ ()) .at j .SemiMod._⇒_.preserve-· {s ·ₛ w} {ι})))
           (f .famf .transf j .SemiMod._⇒_.preserve-· {s ·ₛ w} {ty-unit σ (λ ()) (λ ()) .at j .func ι})

  -- The application's relation reads the body's at the closure's root and the application's
  -- weighted source as source, and at the closure's cells and the argument as environment.
  app-op : ∀ k → ap (of-cols {γ = γ}
                       (M.rule₃-result (M.id-linear (input-width γ)) (M.id-linear (input-width γ))
                          (body-route γ γ' v) (body-link₁ γ' v) (body-link₂ γ' v)
                          (λ _ → εₘ) εₘ εₘ M.I (cols {γ = γ} R) (cols {γ = γ} T) (cols {γ = γ' · v} U)))
                    (inputs γ s x) k
                 ≈s ap U (body-input γ' v ((w ·ₛ s) +ₛ o zero) (λ l → o (suc l)) z) k
  app-op k =
    ≈-trans (app-of-cols {γ = γ} fR s x k)
    (≈-trans (+-cong (per-input source (λ _ → s) k) (per-input environment x k))
    (≈-trans regroup
    (≈-trans (+-cong (+-cong src-part l₁-part) l₂-part)
    (≈-trans (+-cong (+-cong ≈-refl l₁-expand) l₂-expand)
    (≈-trans final-regroup
    (≈-trans (+-cong (≈-sym (app-+ᵥ (cU source) (λ _ → w ·ₛ s) (λ _ → o zero) k))
                     (≈-sym (app-+ᵥ (cU environment) (ap (M.in₁ {width-env γ'} {width v}) (λ l → o (suc l)))
                                                     (ap (M.in₂ {width-env γ'} {width v}) z) k)))
    (≈-trans (≈-sym (app-inputs {γ = γ' · v} U ((w ·ₛ s) +ₛ o zero) X k))
             (app-congᵥ U same k))))))))
    where
    cR = cols {γ = γ} R
    cT = cols {γ = γ} T
    cU = cols {γ = γ' · v} U
    rt₃ = body-route γ γ' v
    l₁ = body-link₁ γ' v
    l₂ = body-link₂ γ' v
    fR = M.rule₃-result (M.id-linear (input-width γ)) (M.id-linear (input-width γ)) rt₃ l₁ l₂
           (λ _ → εₘ) εₘ εₘ M.I cR cT cU
    X : ∣ 𝔽 (width-env γ' + width v) ∣
    X l = ap (M.in₁ {width-env γ'} {width v}) (λ l' → o (suc l')) l +ₛ ap (M.in₂ {width-env γ'} {width v}) z l

    -- The column at one input, read at that input's vector: the three routed contributions.
    per-input : ∀ (i : Input) (vi : ∣ 𝔽 (input-width γ i) ∣) k →
                ap (fR i) vi k ≈s
                ((ap (rt₃ .M.ap cU i) vi k +ₛ ap (l₁ .M.at cU ∘ cR i) vi k) +ₛ ap (l₂ .M.at cU ∘ cT i) vi k)
    per-input i vi k =
      ≈-trans (app-+ₘ A₁ A₂ vi k)
      (≈-trans (+-cong (≈-trans (app-+ₘ A₁₁ (εₘ ∘ cT i) vi k)
                                (≈-trans (+-cong (≈-trans (app-+ₘ εₘ (εₘ ∘ cR i) vi k)
                                                          (≈-trans (+-cong (app-εₘ vi k)
                                                                           (≈-trans (app-∘ εₘ (cR i) vi k)
                                                                                    (app-εₘ (ap (cR i) vi) k)))
                                                                   +-lunit))
                                                 (≈-trans (app-∘ εₘ (cT i) vi k) (app-εₘ (ap (cT i) vi) k)))
                                         +-lunit))
                       (≈-trans (app-∘ M.I A₂₁ vi k)
                                (≈-trans (app-I (ap A₂₁ vi) k)
                                         (≈-trans (app-+ₘ (rt₃ .M.ap cU i +ₘ (l₁ .M.at cU ∘ cR i)) (l₂ .M.at cU ∘ cT i) vi k)
                                                  (+-cong (app-+ₘ (rt₃ .M.ap cU i) (l₁ .M.at cU ∘ cR i) vi k) ≈-refl)))))
               +-lunit)
      where
      A₁₁ = εₘ +ₘ (εₘ ∘ cR i)
      A₁ = A₁₁ +ₘ (εₘ ∘ cT i)
      A₂₁ = (rt₃ .M.ap cU i +ₘ (l₁ .M.at cU ∘ cR i)) +ₘ (l₂ .M.at cU ∘ cT i)
      A₂ = M.I ∘ A₂₁

    regroup : ∀ {a b c a' b' c'} →
              ((a +ₛ b) +ₛ c) +ₛ ((a' +ₛ b') +ₛ c') ≈s (((a +ₛ a') +ₛ (b +ₛ b')) +ₛ (c +ₛ c'))
    regroup = ≈-trans Sc.+-interchange (+-cong Sc.+-interchange ≈-refl)

    l₁-part : (ap (l₁ .M.at cU ∘ cR source) (λ _ → s) k +ₛ ap (l₁ .M.at cU ∘ cR environment) x k)
              ≈s ap (l₁ .M.at cU) o k
    l₁-part =
      ≈-trans (+-cong (app-∘ (l₁ .M.at cU) (cR source) (λ _ → s) k) (app-∘ (l₁ .M.at cU) (cR environment) x k))
      (≈-trans (≈-sym (app-+ᵥ (l₁ .M.at cU) (ap (cR source) (λ _ → s)) (ap (cR environment) x) k))
               (app-congᵥ (l₁ .M.at cU) (λ l → ≈-sym (app-inputs {γ = γ} R s x l)) k))

    l₂-part : (ap (l₂ .M.at cU ∘ cT source) (λ _ → s) k +ₛ ap (l₂ .M.at cU ∘ cT environment) x k)
              ≈s ap (l₂ .M.at cU) z k
    l₂-part =
      ≈-trans (+-cong (app-∘ (l₂ .M.at cU) (cT source) (λ _ → s) k) (app-∘ (l₂ .M.at cU) (cT environment) x k))
      (≈-trans (≈-sym (app-+ᵥ (l₂ .M.at cU) (ap (cT source) (λ _ → s)) (ap (cT environment) x) k))
               (app-congᵥ (l₂ .M.at cU) (λ l → ≈-sym (app-inputs {γ = γ} T s x l)) k))

    l₁-expand : ap (l₁ .M.at cU) o k ≈s
                (ap (cU environment) (ap (M.in₁ {width-env γ'} {width v}) (λ l → o (suc l))) k +ₛ
                 ap (cU source) (λ _ → o zero) k)
    l₁-expand =
      ≈-trans (app-+ₘ (cU environment ∘ (M.in₁ {width-env γ'} {width v} ∘ M.p₂ {1} {width-env γ'}))
                      (cU source ∘ M.p₁ {1} {width-env γ'}) o k)
              (+-cong (≈-trans (app-∘ (cU environment) (M.in₁ {width-env γ'} {width v} ∘ M.p₂ {1} {width-env γ'}) o k)
                               (≈-trans (app-congᵥ (cU environment)
                                           (λ l → app-∘ (M.in₁ {width-env γ'} {width v}) (M.p₂ {1} {width-env γ'}) o l) k)
                                        (app-congᵥ (cU environment)
                                           (app-congᵥ (M.in₁ {width-env γ'} {width v}) (ap-p₂₁ {width-env γ'} o)) k)))
                      (≈-trans (app-∘ (cU source) (M.p₁ {1} {width-env γ'}) o k)
                               (app-congᵥ (cU source) (ap-p₁₁ {width-env γ'} o) k)))

    l₂-expand : ap (l₂ .M.at cU) z k ≈s
                (ap (cU environment) (ap (M.in₂ {width-env γ'} {width v}) z) k +ₛ ε)
    l₂-expand =
      ≈-trans (app-+ₘ (cU environment ∘ M.in₂ {width-env γ'} {width v}) (cU source ∘ εₘ) z k)
              (+-cong (app-∘ (cU environment) (M.in₂ {width-env γ'} {width v}) z k)
                      (≈-trans (app-∘ (cU source) εₘ z k)
                               (≈-trans (app-congᵥ (cU source) (λ l → app-εₘ z l) k) (model.app-ε (cU source) k))))

    final-regroup : ∀ {a b c d} → (a +ₛ (b +ₛ c)) +ₛ (d +ₛ ε) ≈s ((a +ₛ c) +ₛ (b +ₛ d))
    final-regroup =
      ≈-trans (+-cong ≈-refl +-runit)
      (≈-trans (+-cong (+-cong ≈-refl +-comm) ≈-refl)
      (≈-trans (+-cong (≈-sym +-assoc) ≈-refl) +-assoc))

    same : ∀ l → inputs (γ' · v) ((w ·ₛ s) +ₛ o zero) X l ≈s
                 body-input γ' v ((w ·ₛ s) +ₛ o zero) (λ l' → o (suc l')) z l
    same zero    = ≈-refl
    same (suc l) = ≈-refl

    src-part : (ap (rt₃ .M.ap cU source) (λ _ → s) k +ₛ ap (rt₃ .M.ap cU environment) x k)
               ≈s ap (cU source) (λ _ → w ·ₛ s) k
    src-part =
      ≈-trans (+-cong (≈-trans (app-∘ (cU source) (ctrl-row {1}) (λ _ → s) k)
                               (app-congᵥ (cU source) (λ l → ap-ctrl-row {1} s l) k))
                      (≈-trans (app-∘ (cU environment) εₘ x k)
                               (≈-trans (app-congᵥ (cU environment) (λ l → app-εₘ x l) k) (model.app-ε (cU environment) k))))
              +-runit
