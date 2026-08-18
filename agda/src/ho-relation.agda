{-# OPTIONS --prop --postfix-projections --safe #-}

-- The logical relation between the operational semantics and the higher-order model, on the fragment
-- without μ-types: values against indices of the interpretation, dependence vectors against elements
-- of the fibre, and the lemmas by recursion on types that the fundamental lemma needs (respect for the
-- setoids, adding the control positions and the control dependence, absorption, transport).
open import Level using (0ℓ; lift)
open import Data.Nat using (ℕ; suc; _+_; _⊔_; _≤_; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m⊔n≤o⇒m≤o; m⊔n≤o⇒n≤o)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
import prop
open import prop using (_∧_; ∃; Prf; ⟪_⟫; _,_; proj₁; proj₂)
open import prop-setoid using (Setoid)
open import basics using (IsJoin)
open import commutative-semiring using (CommutativeSemiring)
open import signature using (Signature)
open import signature.interpretation using (Interpretation; sort-vals-setoid)
open import categories using (Category; HasProducts; HasStrongCoproducts)
open import indexed-family using (HasSetoidProducts)
import matrix
import commutative-monoid
import ho-model
import language-interpretation

module ho-relation
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A) (ctrl-weight : Setoid.Carrier A)
  (Sig : Signature 0ℓ) (ℐ : Interpretation S Sig)
  (let module S = CommutativeSemiring S)
  -- Addition is idempotent, and the control weight is idempotent and bounds its multiples.
  (+-idem : ∀ x → (x S.+ x) S.≈ x)
  (let module S⊑ = commutative-monoid.AdditivePreorder S.additive (λ {x} → +-idem x))
  (c-idem : (ctrl-weight S.· ctrl-weight) S.≈ ctrl-weight)
  (c-bound : ∀ x → (ctrl-weight S.· x) S⊑.⊑ ctrl-weight)
  where

open Signature Sig
open Interpretation ℐ
open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.evaluation Sig S ℐ ctrl-weight

module model = ho-model S ctrl-weight
module interp = model.interp Sig ℐ
open model public using (𝔽; mat; module Ls; module SemiMod)
open SemiMod public using (Semimodule; _⇒_)
open Semimodule public using () renaming (Carrier to ∣_∣)
open SemiMod._⇒_ public using (func; func-resp-≈; preserve-+; preserve-·; preserve-ze)
open SemiMod._≈m_ public using (func-eq)

module M = matrix.Mat S
module FD = model.Fam⟨𝒟⟩μ
open HasStrongCoproducts FD.strongCoproducts public using (copair)
module SP = HasSetoidProducts model.SPmod

open FD public using (Obj; Mor; idx; fam; fm; idxf; famf; Constant)
open indexed-family.Fam public using (subst)
open indexed-family._⇒f_ public using (transf)
open prop-setoid._⇒_ public using () renaming (func to sfunc; func-resp-≈ to sfunc-resp-≈)

-- The interpretation, at the parameters the higher-order model fixes.
module LI = language-interpretation Sig 0ℓ 0ℓ
  SemiMod.terminal SemiMod.cmon-enriched SemiMod.biproduct SemiMod.𝕀 model.SemiModExp
  interp.δ∅𝒟 interp.𝒟𝟙ty interp.𝒟unit-pt interp.𝒟-Sig-model model.ctrl-weight-endo
  (λ {X} {Y} → model.exp-const {X} {Y}) interp.𝒟𝟙ty-const interp.𝒟-sort-const

open LI public using (⟦_⟧ty; ⟦_⟧ctxt; ⟦_⟧tm; ⟦_⟧tms; ctrl-dep; ty-unit; roll-mor; unroll-mor)
open Constant public using (at)

module IP = model.sig-model.IP Sig ℐ
open IP public using (collect)
open interp public using (𝒟-arg-product)
module FC = model.Fam⟨𝒞⟩μ

⟦_⟧ : type 0 → Obj
⟦ τ ⟧ = ⟦ τ ⟧ty (λ ())

module Ix (τ : type 0) = Setoid (⟦ τ ⟧ .idx)

Ix : type 0 → Set
Ix τ = Ix.Carrier τ

Fib : (τ : type 0) → Ix τ → Semimodule
Fib τ i = ⟦ τ ⟧ .fam .fm i

module IxC (Γ : ctxt) = Setoid (⟦ Γ ⟧ctxt .idx)

IxC : ctxt → Set
IxC Γ = IxC.Carrier Γ

FibC : (Γ : ctxt) → IxC Γ → Semimodule
FibC Γ i = ⟦ Γ ⟧ctxt .fam .fm i

open model public using (app-+; app-+ₘ; app-∘; app-εₘ; app-I; app-e; app-congₘ; app-congᵥ; app-p₁; app-p₂; app-in₁; app-in₂; app-pair; concat-+)
  renaming (app to ap)
open CommutativeSemiring S public using (ι; ε; +-cong; ·-cong; +-lunit; +-comm; +-assoc; ·-lunit; ·-comm; ε-annihilₗ; ε-annihilᵣ)
  renaming (_≈_ to _≈s_; _+_ to _+ₛ_; _·_ to _·ₛ_)
open Setoid A public using () renaming (refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)
open M public using (Σ-cong; Σ-unit; Σ-ε; _∘_; _+ₘ_; εₘ; ≈ₘ-refl; ≈ₘ-sym; ≈ₘ-trans; ⟨_,_⟩) renaming (Σ to Σₛ)

Payload : ∀ σ τ → Ix (σ [→] τ) → Semimodule
Payload σ τ f = model.FE._⟶_ ⟦ σ ⟧ ⟦ τ ⟧ .fam .fm f

module Payload σ τ f = Semimodule (Payload σ τ f)

evalΠ : ∀ σ τ (f : Ix (σ [→] τ)) (j : Ix σ) → Payload σ τ f ⇒ Fib τ (f .idxf .sfunc j)
evalΠ σ τ f j = SP.evalΠ (⟦ τ ⟧ .fam indexed-family.[ f .idxf ]) j


-- Values related to indices, by recursion on the type. A closure is related to a fibre map of the
-- exponential when, for every related argument and every derivation of the body at it, the result
-- is related to the map's index at the argument.
ValRel : ∀ τ → Val τ → Ix τ → Set
ValRel unit unit i = ⊤
ValRel (base s) (const a) i = Prf (Setoid._≈_ (sort-index s) i a)
ValRel (σ [+] τ) (inl v) i = Σ (Ix σ) λ i' → ValRel σ v i' × Prf (Ix._≈_ (σ [+] τ) i (inj₁ i'))
ValRel (σ [+] τ) (inr v) i = Σ (Ix τ) λ i' → ValRel τ v i' × Prf (Ix._≈_ (σ [+] τ) i (inj₂ i'))
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
    (ap (M.in₁ {width-env γ'} {width v}) x)
    (ap (M.in₂ {width-env γ'} {width v}) z) k

-- The control dependence at an index and a value of the control input.
ctrl-dep-at : ∀ τ (i : Ix τ) → Setoid.Carrier A → ∣ Fib τ i ∣
ctrl-dep-at τ i s = ctrl-dep τ .at i .func s

-- Each fibre's semimodule with its additive order: x ⊑ y when x + y is y. Addition in a fibre is
-- idempotent because it is in the semiring.
fib-+-idem : ∀ τ i {x} → Semimodule._≈_ (Fib τ i) (Semimodule._+_ (Fib τ i) x x) x
fib-+-idem τ i =
  X.trans (X.+-cong (X.sym X.·-unit) (X.sym X.·-unit))
          (X.trans (X.sym X.+-distribʳ) (X.trans (X.·-cong (+-idem ι) X.refl) X.·-unit))
  where module X = Semimodule (Fib τ i)

module Fib τ i where
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
DepRel unit {unit} {i} r o d = Fib._≈_ unit i o d
DepRel (base s) {const a} {i} r o d = Semimodule._≈_ (Fib (base s) i) o d
DepRel (σ [+] τ) {inl v} {i} (i' , r , ⟪ e ⟫) o d =
  let d' = ⟦ σ [+] τ ⟧ .fam .subst {i} {inj₁ i'} e .func d in
  (o zero ≈s proj₁ d') ∧ DepRel σ r (λ k → o (suc k)) (proj₂ d')
DepRel (σ [+] τ) {inr v} {i} (i' , r , ⟪ e ⟫) o d =
  let d' = ⟦ σ [+] τ ⟧ .fam .subst {i} {inj₂ i'} e .func d in
  (o zero ≈s proj₁ d') ∧ DepRel τ r (λ k → o (suc k)) (proj₂ d')
DepRel (σ [×] τ) {pair v u} {i , j} (r , r') o d =
  (o zero ≈s proj₁ d) ∧
  (DepRel σ r (ap (M.p₁ {width v} {width u}) (λ k → o (suc k))) (proj₁ (proj₂ d)) ∧
   DepRel τ r' (ap (M.p₂ {width v} {width u}) (λ k → o (suc k))) (proj₂ (proj₂ d)))
DepRel (σ [→] τ) {clo γ' t} {f} r o d =
  (o zero ≈s proj₁ d) ∧
  (∀ (s' : Setoid.Carrier A) {v : Val σ} {j : Ix σ} (rv : ValRel σ v j)
     (z : ∣ 𝔽 (width v) ∣) (y : ∣ Fib σ j ∣) → DepRel⊑ σ rv (s' +ₛ o zero) z y →
   ∀ {u U} (D : γ' · v , t ⇓ u [ U ]) →
     DepRel τ (r rv D) (ap U (body-input γ' v (s' +ₛ o zero) (λ k → o (suc k)) z))
       (Fib._+_ τ (f .idxf .sfunc j)
         (ctrl-dep τ .at (f .idxf .sfunc j) .func (s' +ₛ o zero))
         (Fib._+_ τ (f .idxf .sfunc j)
           (evalΠ σ τ f j .func (proj₂ d))
           (f .famf .transf j .func y))))

DepRel⊑ τ {i = i} r s o d =
  ∃ (∣ Fib τ i ∣) (λ m → Fib._⊑_ τ i m (ctrl-dep-at τ i s) ∧ DepRel τ r o (Fib._+_ τ i d m))

-- A bound on the arrow depth of a type bounds its components' and, at a μ-type, its unfolding's.
bound₁ : ∀ {m n o} → m ⊔ n ≤ o → m ≤ o
bound₁ = m⊔n≤o⇒m≤o _ _

bound₂ : ∀ {m n o} → m ⊔ n ≤ o → n ≤ o
bound₂ = m⊔n≤o⇒n≤o _ _

bound-μ : ∀ (τ : type 1) {N} → arr-depth (μ τ) ≤ N → arr-depth (τ [ μ τ ]) ≤ N
bound-μ τ = ≤-trans (arr-depth-unfold τ)

-- The relations by recursion on a bound on the arrow depth of the type, which decreases at an arrow,
-- and on the value. A rolled value is related to an index when its payload is related to the
-- unrolled index, and its dependence vector to an element of the fibre when it is to the element's
-- image under unrolling.
ValRel′ : ∀ N τ → arr-depth τ ≤ N → Val τ → Ix τ → Set
ValRel′ N unit p unit i = ⊤
ValRel′ N (base s) p (const a) i = Prf (Setoid._≈_ (sort-index s) i a)
ValRel′ N (σ [+] τ) p (inl v) i = Σ (Ix σ) λ i' → ValRel′ N σ (bound₁ p) v i' × Prf (Ix._≈_ (σ [+] τ) i (inj₁ i'))
ValRel′ N (σ [+] τ) p (inr v) i = Σ (Ix τ) λ i' → ValRel′ N τ (bound₂ p) v i' × Prf (Ix._≈_ (σ [+] τ) i (inj₂ i'))
ValRel′ N (σ [×] τ) p (pair v u) (i , j) = ValRel′ N σ (bound₁ p) v i × ValRel′ N τ (bound₂ p) u j
ValRel′ (suc N) (σ [→] τ) (s≤s p) (clo γ' t) f =
  ∀ {v : Val σ} {j : Ix σ} → ValRel′ N σ (bound₁ p) v j → ∀ {u U} → γ' · v , t ⇓ u [ U ] →
  ValRel′ N τ (bound₂ p) u (f .idxf .sfunc j)
ValRel′ N (μ τ) p (roll v) i = ValRel′ N (τ [ μ τ ]) (bound-μ τ p) v (unroll-mor τ .idxf .sfunc i)

DepRel⊑′ : ∀ N τ (p : arr-depth τ ≤ N) {v : Val τ} {i : Ix τ} → ValRel′ N τ p v i → Setoid.Carrier A →
           ∣ 𝔽 (width v) ∣ → ∣ Fib τ i ∣ → Prop
DepRel′ : ∀ N τ (p : arr-depth τ ≤ N) {v : Val τ} {i : Ix τ} → ValRel′ N τ p v i →
          ∣ 𝔽 (width v) ∣ → ∣ Fib τ i ∣ → Prop
DepRel′ N unit p {unit} {i} r o d = Fib._≈_ unit i o d
DepRel′ N (base s) p {const a} {i} r o d = Semimodule._≈_ (Fib (base s) i) o d
DepRel′ N (σ [+] τ) p {inl v} {i} (i' , r , ⟪ e ⟫) o d =
  let d' = ⟦ σ [+] τ ⟧ .fam .subst {i} {inj₁ i'} e .func d in
  (o zero ≈s proj₁ d') ∧ DepRel′ N σ (bound₁ p) r (λ k → o (suc k)) (proj₂ d')
DepRel′ N (σ [+] τ) p {inr v} {i} (i' , r , ⟪ e ⟫) o d =
  let d' = ⟦ σ [+] τ ⟧ .fam .subst {i} {inj₂ i'} e .func d in
  (o zero ≈s proj₁ d') ∧ DepRel′ N τ (bound₂ p) r (λ k → o (suc k)) (proj₂ d')
DepRel′ N (σ [×] τ) p {pair v u} {i , j} (r , r') o d =
  (o zero ≈s proj₁ d) ∧
  (DepRel′ N σ (bound₁ p) r (ap (M.p₁ {width v} {width u}) (λ k → o (suc k))) (proj₁ (proj₂ d)) ∧
   DepRel′ N τ (bound₂ p) r' (ap (M.p₂ {width v} {width u}) (λ k → o (suc k))) (proj₂ (proj₂ d)))
DepRel′ (suc N) (σ [→] τ) (s≤s p) {clo γ' t} {f} r o d =
  (o zero ≈s proj₁ d) ∧
  (∀ (s' : Setoid.Carrier A) {v : Val σ} {j : Ix σ} (rv : ValRel′ N σ (bound₁ p) v j)
     (z : ∣ 𝔽 (width v) ∣) (y : ∣ Fib σ j ∣) → DepRel⊑′ N σ (bound₁ p) rv (s' +ₛ o zero) z y →
   ∀ {u U} (D : γ' · v , t ⇓ u [ U ]) →
     DepRel′ N τ (bound₂ p) (r rv D) (ap U (body-input γ' v (s' +ₛ o zero) (λ k → o (suc k)) z))
       (Fib._+_ τ (f .idxf .sfunc j)
         (ctrl-dep τ .at (f .idxf .sfunc j) .func (s' +ₛ o zero))
         (Fib._+_ τ (f .idxf .sfunc j)
           (evalΠ σ τ f j .func (proj₂ d))
           (f .famf .transf j .func y))))
DepRel′ N (μ τ) p {roll v} {i} r o d =
  DepRel′ N (τ [ μ τ ]) (bound-μ τ p) r o (unroll-mor τ .famf .transf i .func d)

DepRel⊑′ N τ p {i = i} r s o d =
  ∃ (∣ Fib τ i ∣) (λ m → Fib._⊑_ τ i m (ctrl-dep-at τ i s) ∧ DepRel′ N τ p r o (Fib._+_ τ i d m))

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
  EnvDepRel rγ s (ap (M.p₁ {width-env γ} {width v}) x) (proj₁ g) ∧
  DepRel⊑ _ r s (ap (M.p₂ {width-env γ} {width v}) x) (proj₂ g)

-- The inputs of a derivation: the control input's value at the first position, the environment after.
inputs : ∀ {Γ} (γ : Env Γ) → Setoid.Carrier A → ∣ 𝔽 (width-env γ) ∣ → ∣ 𝔽 (suc (width-env γ)) ∣
inputs γ s x zero    = s
inputs γ s x (suc k) = x k

-- Semiring shorthands.
c = ctrl-weight
+-runit : ∀ {x} → (x +ₛ ε) ≈s x
+-runit = ≈-trans +-comm +-lunit
·-runit : ∀ {x} → (x ·ₛ ι) ≈s x
·-runit = ≈-trans ·-comm ·-lunit

m-runit : ∀ (X : Semimodule) {x} → Semimodule._≈_ X (Semimodule._+_ X x (Semimodule.ε X)) x
m-runit X = Semimodule.trans X (Semimodule.+-comm X) (Semimodule.+-lunit X)

-- Reading a lifted vector: the first position of the first summand's injection, and the rest of
-- the second's.
ap-in₁-zero : ∀ {n} (u : ∣ 𝔽 1 ∣) → ap (M.in₁ {1} {n}) u zero ≈s u zero
ap-in₁-zero {n} u = app-in₁ {1} {n} u zero

ap-in₁-suc : ∀ {n} (u : ∣ 𝔽 1 ∣) (k : Fin n) → ap (M.in₁ {1} {n}) u (suc k) ≈s ε
ap-in₁-suc {n} u k = app-in₁ {1} {n} u (suc k)

ap-in₂-zero : ∀ {n} (u : ∣ 𝔽 n ∣) → ap (M.in₂ {1} {n}) u zero ≈s ε
ap-in₂-zero {n} u = app-in₂ {1} {n} u zero

ap-in₂-suc : ∀ {n} (u : ∣ 𝔽 n ∣) (k : Fin n) → ap (M.in₂ {1} {n}) u (suc k) ≈s u k
ap-in₂-suc {n} u k = app-in₂ {1} {n} u (suc k)

ap-pair-zero : ∀ {m n} (f : M.Matrix 1 m) (g : M.Matrix n m) (u : ∣ 𝔽 m ∣) →
               ap (⟨ f , g ⟩) u zero ≈s ap f u zero
ap-pair-zero {m} {n} f g u = app-pair {m} {1} {n} f g u zero

ap-pair-suc : ∀ {m n} (f : M.Matrix 1 m) (g : M.Matrix n m) (u : ∣ 𝔽 m ∣) (k : Fin n) →
              ap (⟨ f , g ⟩) u (suc k) ≈s ap g u k
ap-pair-suc {m} {n} f g u k = app-pair {m} {1} {n} f g u (suc k)

-- The control vector at a value s at the control input: the weight at the root of a lifted value, and the
-- payload's control vector after.
ap-ctrl-row : ∀ {n} (s : Setoid.Carrier A) (k : Fin n) → ap ctrl-row (λ _ → s) k ≈s (c ·ₛ s)
ap-ctrl-row {n} s k = +-runit

ctrl-lift-zero : ∀ {n} (g : M.Matrix n 1) (s : Setoid.Carrier A) →
                 ap (⟨ ctrl-row {1} , g ⟩) (λ _ → s) zero ≈s (c ·ₛ s)
ctrl-lift-zero {n} g s = ≈-trans (ap-pair-zero {1} {n} ctrl-row g (λ _ → s)) (ap-ctrl-row {1} s zero)

ctrl-lift-suc : ∀ {n} (g : M.Matrix n 1) (s : Setoid.Carrier A) (k : Fin n) →
                ap (⟨ ctrl-row {1} , g ⟩) (λ _ → s) (suc k) ≈s ap g (λ _ → s) k
ctrl-lift-suc {n} g s k = ap-pair-suc {1} {n} ctrl-row g (λ _ → s) k

-- Reading a relation at the inputs: the control input's column at its value and the environment
-- columns at the environment vector, and the relations the rules are built from at any vector.
ap-p₁₁ : ∀ {m} (o : ∣ 𝔽 (suc m) ∣) (k : Fin 1) → ap (M.p₁ {1} {m}) o k ≈s o zero
ap-p₁₁ {m} o zero = app-p₁ {1} {m} o zero

ap-p₂₁ : ∀ {m} (o : ∣ 𝔽 (suc m) ∣) (k : Fin m) → ap (M.p₂ {1} {m}) o k ≈s o (suc k)
ap-p₂₁ {m} o k = app-p₂ {1} {m} o k

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
          Fib._≈_ σ i (proj₂ (ctrl-dep-at (σ [+] τ) (inj₁ i) s)) (ctrl-dep-at σ i s)
ctrl-dep-inj₁ {σ} i s = ≈-trans +-runit +-runit , Fib.+-lunit σ i

ctrl-dep-inj₂ : ∀ {σ τ} (i : Ix τ) s →
          (proj₁ (ctrl-dep-at (σ [+] τ) (inj₂ i) s) ≈s (c ·ₛ s)) ∧
          Fib._≈_ τ i (proj₂ (ctrl-dep-at (σ [+] τ) (inj₂ i) s)) (ctrl-dep-at τ i s)
ctrl-dep-inj₂ {σ} {τ} i s = ≈-trans +-runit +-runit , Fib.+-lunit τ i

ctrl-dep-pair : ∀ {σ τ} (i : Ix σ) (j : Ix τ) s →
          (proj₁ (ctrl-dep-at (σ [×] τ) (i , j) s) ≈s (c ·ₛ s)) ∧
          (Fib._≈_ σ i (proj₁ (proj₂ (ctrl-dep-at (σ [×] τ) (i , j) s))) (ctrl-dep-at σ i s) ∧
           Fib._≈_ τ j (proj₂ (proj₂ (ctrl-dep-at (σ [×] τ) (i , j) s))) (ctrl-dep-at τ j s))
ctrl-dep-pair {σ} {τ} i j s =
  ≈-trans +-runit +-runit ,
  (Fib.trans σ i (Fib.+-lunit σ i) (m-runit (Fib σ i)) ,
   Fib.trans τ j (Fib.+-lunit τ j) (Fib.+-lunit τ j))

ctrl-dep-clo : ∀ {σ τ} (f : Ix (σ [→] τ)) s →
         (proj₁ (ctrl-dep-at (σ [→] τ) f s) ≈s (c ·ₛ s)) ∧
         Payload._≈_ σ τ f (proj₂ (ctrl-dep-at (σ [→] τ) f s))
           (Payload.ε σ τ f)
ctrl-dep-clo {σ} {τ} f s =
  ≈-trans +-runit +-runit ,
  Payload.+-lunit σ τ f {Payload.ε σ τ f}

payload-ctrl-dep : ∀ σ τ (f : Ix (σ [→] τ)) s (d : ∣ Fib (σ [→] τ) f ∣) →
                   Payload._≈_ σ τ f (proj₂ (Fib._+_ (σ [→] τ) f (ctrl-dep-at (σ [→] τ) f s) d)) (proj₂ d)
payload-ctrl-dep σ τ f s d =
  Payload.trans σ τ f {proj₂ (Fib._+_ (σ [→] τ) f (ctrl-dep-at (σ [→] τ) f s) d)} {Payload._+_ σ τ f (Payload.ε σ τ f) (proj₂ d)} {proj₂ d}
    (Payload.+-cong σ τ f {proj₂ (ctrl-dep-at (σ [→] τ) f s)} {Payload.ε σ τ f} {proj₂ d} {proj₂ d} (proj₂ (ctrl-dep-clo {σ} {τ} f s)) (Payload.refl σ τ f {proj₂ d}))
    (Payload.+-lunit σ τ f {proj₂ d})

ctrl-dep-natural : ∀ τ {i i' : Ix τ} (e : Ix._≈_ τ i i') s →
             Fib._≈_ τ i' (⟦ τ ⟧ .fam .subst e .func (ctrl-dep-at τ i s)) (ctrl-dep-at τ i' s)
ctrl-dep-natural τ e s = ctrl-dep τ .Constant.at-natural e .func-eq ≈-refl

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
  m , (Fib.trans τ i (Fib.+-cong τ i (Fib.refl τ i) (ctrl-dep τ .at i .func-resp-≈ (≈-sym es)))
                   (Fib.trans τ i dm (ctrl-dep τ .at i .func-resp-≈ es)) , h)

DepRel-resp : ∀ τ {v : Val τ} {i : Ix τ} (r : ValRel τ v i) {o o' : ∣ 𝔽 (width v) ∣} {d d' : ∣ Fib τ i ∣} →
              (∀ k → o k ≈s o' k) → Fib._≈_ τ i d d' → DepRel τ r o d → DepRel τ r o' d'
DepRel-resp unit {unit} r eo ed h k = ≈-trans (≈-sym (eo k)) (≈-trans (h k) (ed k))
DepRel-resp (base s) {const a} r eo ed h k = ≈-trans (≈-sym (eo k)) (≈-trans (h k) (ed k))
DepRel-resp (σ [+] τ) {inl v} {i} (i' , r , ⟪ e ⟫) {d = d} {d'} eo ed (h₀ , h) =
  let ed' = ⟦ σ [+] τ ⟧ .fam .subst {i} {inj₁ i'} e .func-resp-≈ ed in
  ≈-trans (≈-sym (eo zero)) (≈-trans h₀ (proj₁ ed')) ,
  DepRel-resp σ r (λ k → eo (suc k)) (proj₂ ed') h
DepRel-resp (σ [+] τ) {inr v} {i} (i' , r , ⟪ e ⟫) {d = d} {d'} eo ed (h₀ , h) =
  let ed' = ⟦ σ [+] τ ⟧ .fam .subst {i} {inj₂ i'} e .func-resp-≈ ed in
  ≈-trans (≈-sym (eo zero)) (≈-trans h₀ (proj₁ ed')) ,
  DepRel-resp τ r (λ k → eo (suc k)) (proj₂ ed') h
DepRel-resp (σ [×] τ) {pair v u} {i , j} (r , r') eo (ed₀ , (ed₁ , ed₂)) (h₀ , (h₁ , h₂)) =
  ≈-trans (≈-sym (eo zero)) (≈-trans h₀ ed₀) ,
  (DepRel-resp σ r (app-congᵥ (M.p₁ {width v} {width u}) (λ k → eo (suc k))) ed₁ h₁ ,
   DepRel-resp τ r' (app-congᵥ (M.p₂ {width v} {width u}) (λ k → eo (suc k))) ed₂ h₂)
DepRel-resp (σ [→] τ) {clo γ' t} {f} r {o} {o'} {d} {d'} eo (ed₀ , ed₂) (h₀ , hc) =
  ≈-trans (≈-sym (eo zero)) (≈-trans h₀ ed₀) ,
  λ s' {v} {j} rv z y hz {u} {U} D →
    DepRel-resp τ (r rv D)
      (app-congᵥ U (body-input-resp γ' v (+-cong ≈-refl (eo zero)) (λ k → eo (suc k))))
      (Fib.+-cong τ (f .idxf .sfunc j)
         (ctrl-dep τ .at (f .idxf .sfunc j) .func-resp-≈ (+-cong ≈-refl (eo zero)))
         (Fib.+-cong τ (f .idxf .sfunc j)
            (evalΠ σ τ f j .func-resp-≈
               {proj₂ d} {proj₂ d'} ed₂)
            (Fib.refl τ (f .idxf .sfunc j) {f .famf .transf j .func y})))
      (hc s' rv z y (DepRel⊑-resp-ctrl σ rv (+-cong ≈-refl (≈-sym (eo zero))) hz) D)

-- Transport of a sum of the control dependence and an element along an index equation.
subst-ctrl-dep+ : ∀ τ {i i' : Ix τ} (e : Ix._≈_ τ i i') s d →
            Fib._≈_ τ i' (⟦ τ ⟧ .fam .subst e .func (Fib._+_ τ i (ctrl-dep-at τ i s) d))
                       (Fib._+_ τ i' (ctrl-dep-at τ i' s) (⟦ τ ⟧ .fam .subst e .func d))
subst-ctrl-dep+ τ {i} {i'} e s d =
  Fib.trans τ i' (⟦ τ ⟧ .fam .subst e .preserve-+ {ctrl-dep-at τ i s} {d})
               (Fib.+-cong τ i' (ctrl-dep-natural τ e s) (Fib.refl τ i'))

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
           DepRel τ r (λ k → ap (ctrl-of v) (λ _ → s) k +ₛ o k) (Fib._+_ τ i (ctrl-dep-at τ i s) d)
ctrl-add unit {unit} {i} r s h zero =
  +-cong (≈-trans (ap-ctrl-row {1} s zero) (≈-sym (ctrl-dep-unit i s))) (h zero)
ctrl-add (base σ) {const a} {i} r s h k =
  +-cong (≈-trans (ap-ctrl-row {sort-width σ} s k) (≈-sym (ctrl-dep-base i s k))) (h k)
ctrl-add (σ [+] τ) {inl v} {i} (i' , r , ⟪ e ⟫) s {o} {d} (h₀ , h) =
  let e+ = subst-ctrl-dep+ (σ [+] τ) {i} {inj₁ i'} e s d
      d' = ⟦ σ [+] τ ⟧ .fam .subst {i} {inj₁ i'} e .func d
  in
  ≈-trans (+-cong (ctrl-lift-zero (ctrl-of v) s) h₀)
          (≈-sym (≈-trans (proj₁ e+) (+-cong (proj₁ (ctrl-dep-inj₁ {σ} {τ} i' s)) ≈-refl))) ,
  DepRel-resp σ r
    (λ k → +-cong (≈-sym (ctrl-lift-suc (ctrl-of v) s k)) ≈-refl)
    (Fib.sym σ i' (Fib.trans σ i' (proj₂ e+)
                              (Fib.+-cong σ i' (proj₂ (ctrl-dep-inj₁ {σ} {τ} i' s)) (Fib.refl σ i'))))
    (ctrl-add σ r s h)
ctrl-add (σ [+] τ) {inr v} {i} (i' , r , ⟪ e ⟫) s {o} {d} (h₀ , h) =
  let e+ = subst-ctrl-dep+ (σ [+] τ) {i} {inj₂ i'} e s d
  in
  ≈-trans (+-cong (ctrl-lift-zero (ctrl-of v) s) h₀)
          (≈-sym (≈-trans (proj₁ e+) (+-cong (proj₁ (ctrl-dep-inj₂ {σ} {τ} i' s)) ≈-refl))) ,
  DepRel-resp τ r
    (λ k → +-cong (≈-sym (ctrl-lift-suc (ctrl-of v) s k)) ≈-refl)
    (Fib.sym τ i' (Fib.trans τ i' (proj₂ e+)
                              (Fib.+-cong τ i' (proj₂ (ctrl-dep-inj₂ {σ} {τ} i' s)) (Fib.refl τ i'))))
    (ctrl-add τ r s h)
ctrl-add (σ [×] τ) {pair v u} {i , j} (r , r') s {o} {d} (h₀ , (h₁ , h₂)) =
  ≈-trans (+-cong (ctrl-lift-zero (⟨ ctrl-of v , ctrl-of u ⟩) s) h₀)
          (+-cong (≈-sym (proj₁ (ctrl-dep-pair {σ} {τ} i j s))) ≈-refl) ,
  (DepRel-resp σ r
     (λ k → ≈-trans (+-cong (≈-sym (ap-pair-p₁ (ctrl-of v) (ctrl-of u) (λ _ → s) k)) ≈-refl)
              (≈-trans (≈-sym (app-+ (M.p₁ {width v} {width u}) _ _ k))
                       (app-congᵥ (M.p₁ {width v} {width u})
                          (λ l → +-cong (≈-sym (ctrl-lift-suc (⟨ ctrl-of v , ctrl-of u ⟩) s l)) ≈-refl) k)))
     (Fib.+-cong σ i (Fib.sym σ i (proj₁ (proj₂ (ctrl-dep-pair {σ} {τ} i j s)))) (Fib.refl σ i))
     (ctrl-add σ r s h₁) ,
   DepRel-resp τ r'
     (λ k → ≈-trans (+-cong (≈-sym (ap-pair-p₂ (ctrl-of v) (ctrl-of u) (λ _ → s) k)) ≈-refl)
              (≈-trans (≈-sym (app-+ (M.p₂ {width v} {width u}) _ _ k))
                       (app-congᵥ (M.p₂ {width v} {width u})
                          (λ l → +-cong (≈-sym (ctrl-lift-suc (⟨ ctrl-of v , ctrl-of u ⟩) s l)) ≈-refl) k)))
     (Fib.+-cong τ j (Fib.sym τ j (proj₂ (proj₂ (ctrl-dep-pair {σ} {τ} i j s)))) (Fib.refl τ j))
     (ctrl-add τ r' s h₂))
ctrl-add (σ [→] τ) {clo γ' t} {f} r s {o} {d} (h₀ , hc) =
  ≈-trans (+-cong (ctrl-lift-zero {width-env γ'} εₘ s) h₀)
          (+-cong (≈-sym (proj₁ (ctrl-dep-clo {σ} {τ} f s))) ≈-refl) ,
  λ s' {v} {j} rv z y hz {u} {U} D →
    let e₀ : ((s' +ₛ (c ·ₛ s)) +ₛ o zero) ≈s (s' +ₛ (ap (ctrl-of (clo γ' t)) (λ _ → s) zero +ₛ o zero))
        e₀ = ≈-trans +-assoc (+-cong ≈-refl (+-cong (≈-sym (ctrl-lift-zero {width-env γ'} εₘ s)) ≈-refl))
    in
    DepRel-resp τ (r rv D)
      (app-congᵥ U (body-input-resp γ' v e₀
         (λ k → ≈-sym (≈-trans (+-cong (ctrl-lift-suc {width-env γ'} εₘ s k) ≈-refl)
                               (≈-trans (+-cong (app-εₘ {width-env γ'} {1} (λ _ → s) k) ≈-refl) +-lunit)))))
      (Fib.+-cong τ (f .idxf .sfunc j)
         (ctrl-dep τ .at (f .idxf .sfunc j) .func-resp-≈ e₀)
         (Fib.+-cong τ (f .idxf .sfunc j)
            (evalΠ σ τ f j .func-resp-≈
               {proj₂ d} {proj₂ (Fib._+_ (σ [→] τ) f (ctrl-dep-at (σ [→] τ) f s) d)}
               (Payload.sym σ τ f {proj₂ (Fib._+_ (σ [→] τ) f (ctrl-dep-at (σ [→] τ) f s) d)} {proj₂ d}
                  (payload-ctrl-dep σ τ f s d)))
            (Fib.refl τ (f .idxf .sfunc j) {f .famf .transf j .func y})))
      (hc (s' +ₛ (c ·ₛ s)) rv z y (DepRel⊑-resp-ctrl σ rv (≈-sym e₀) hz) D)

-- Looking up a variable in a related environment.
lookup-val : ∀ {Γ τ} (x : Γ ∋ τ) {γ : Env Γ} {gi} → EnvValRel γ gi →
             ValRel τ (lookup x γ) (LI.⟦ x ⟧var .idxf .sfunc gi)
lookup-val zero     (rγ · r) = r
lookup-val (succ x) (rγ · r) = lookup-val x rγ

DepRel⊑-resp : ∀ τ {v : Val τ} {i : Ix τ} (r : ValRel τ v i) s {o o' : ∣ 𝔽 (width v) ∣} {d} →
               (∀ k → o k ≈s o' k) → DepRel⊑ τ r s o d → DepRel⊑ τ r s o' d
DepRel⊑-resp τ {i = i} r s eo (m , (dm , h)) = m , (dm , DepRel-resp τ r eo (Fib.refl τ i) h)

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
⊑-absorb : ∀ τ (i : Ix τ) s (d m : ∣ Fib τ i ∣) → Fib._⊑_ τ i m (ctrl-dep-at τ i s) →
         Fib._≈_ τ i (Fib._+_ τ i (ctrl-dep-at τ i s) (Fib._+_ τ i d m)) (Fib._+_ τ i (ctrl-dep-at τ i s) d)
⊑-absorb τ i s d m dm =
  Fib.trans τ i (Fib.+-cong τ i (Fib.refl τ i) (Fib.+-comm τ i))
  (Fib.trans τ i (Fib.sym τ i (Fib.+-assoc τ i))
  (Fib.trans τ i (Fib.+-cong τ i (Fib.trans τ i (Fib.+-comm τ i) dm) (Fib.refl τ i))
               (Fib.refl τ i)))

DepRel⊑-ctrl : ∀ τ {v : Val τ} {i : Ix τ} (r : ValRel τ v i) s {o : ∣ 𝔽 (width v) ∣} {d} →
               DepRel⊑ τ r s o d →
               DepRel τ r (λ k → ap (ctrl-of v) (λ _ → s) k +ₛ o k) (Fib._+_ τ i (ctrl-dep-at τ i s) d)
DepRel⊑-ctrl τ {i = i} r s {o} {d} (m , (dm , h)) =
  DepRel-resp τ r (λ k → ≈-refl) (⊑-absorb τ i s d m dm) (ctrl-add τ r s h)

idx-eq-at : ∀ σ τ {f f' : Ix (σ [→] τ)} → Ix._≈_ (σ [→] τ) f f' → ∀ j →
            Ix._≈_ τ (f .idxf .sfunc j) (f' .idxf .sfunc j)
idx-eq-at σ τ E j = E .FD._≃_.idxf-eq .prop-setoid._≃m_.func-eq (Ix.refl σ {j})

famf-eq-at : ∀ σ τ {f f' : Ix (σ [→] τ)} (E : Ix._≈_ (σ [→] τ) f f') j (y : ∣ Fib σ j ∣) →
             Fib._≈_ τ (f' .idxf .sfunc j) (⟦ τ ⟧ .fam .subst (idx-eq-at σ τ E j) .func (f .famf .transf j .func y))
                                        (f' .famf .transf j .func y)
famf-eq-at σ τ E j y = E .FD._≃_.famf-eq .indexed-family._≃f_.transf-eq {j} .func-eq (Fib.refl σ j {y})

-- Related values are related at equal indices.
ValRel-resp : ∀ τ {v : Val τ} {i i' : Ix τ} → Ix._≈_ τ i i' → ValRel τ v i → ValRel τ v i'
ValRel-resp unit {unit} e r = tt
ValRel-resp (base σ) {const a} {i} {i'} e ⟪ e₀ ⟫ =
  ⟪ Setoid.trans (sort-index σ) {i'} {i} {a} (Setoid.sym (sort-index σ) {i} {i'} e) e₀ ⟫
ValRel-resp (σ [+] τ) {inl v} {i} {i'} e (i₀ , r , ⟪ e₀ ⟫) =
  i₀ , r , ⟪ Ix.trans (σ [+] τ) {i'} {i} {inj₁ i₀} (Ix.sym (σ [+] τ) {i} {i'} e) e₀ ⟫
ValRel-resp (σ [+] τ) {inr v} {i} {i'} e (i₀ , r , ⟪ e₀ ⟫) =
  i₀ , r , ⟪ Ix.trans (σ [+] τ) {i'} {i} {inj₂ i₀} (Ix.sym (σ [+] τ) {i} {i'} e) e₀ ⟫
ValRel-resp (σ [×] τ) {pair v u} {i , j} {i' , j'} (e₁ , e₂) (r , r') = ValRel-resp σ e₁ r , ValRel-resp τ e₂ r'
ValRel-resp (σ [→] τ) {clo γ' t} {f} {f'} e r {v} {j} rv {u} {U} D =
  ValRel-resp τ (idx-eq-at σ τ e j) (r rv D)


-- Reading the model's constructions elementwise: a pairing through the biproduct is the pair of
-- the components, the lifted action keeps the root and acts on the payload, and eliminating a
-- root applies the continuation to the payload and the control dependence to the root.
bpair-elt : ∀ {X Y Z : Semimodule} (f : X ⇒ Y) (g : X ⇒ Z) (x : ∣ X ∣) →
            Semimodule._≈_ (SemiMod._⊕_ Y Z) (FD.pair f g .func x) (f .func x , g .func x)
bpair-elt {X} {Y} {Z} f g x = m-runit Y , Semimodule.+-lunit Z

Fpair-elt : ∀ {X Y Z : Obj} (f : Mor X Y) (g : Mor X Z) (x : Setoid.Carrier (X .idx)) (z : ∣ X .fam .fm x ∣) →
            Semimodule._≈_ (FD.Fam𝒞-P.prod Y Z .fam .fm (f .idxf .sfunc x , g .idxf .sfunc x))
              (FD.Fam𝒞-P.pair f g .famf .transf x .func z)
              (f .famf .transf x .func z , g .famf .transf x .func z)
Fpair-elt f g x z = bpair-elt (f .famf .transf x) (g .famf .transf x) z

Fprod-subst-elt : ∀ {X Y : Obj} {x x' : Setoid.Carrier (X .idx)} {y y' : Setoid.Carrier (Y .idx)}
                  (e₁ : Setoid._≈_ (X .idx) x x') (e₂ : Setoid._≈_ (Y .idx) y y')
                  (z : ∣ X .fam .fm x ∣) (w : ∣ Y .fam .fm y ∣) →
                  Semimodule._≈_ (FD.Fam𝒞-P.prod X Y .fam .fm (x' , y'))
                    (FD.Fam𝒞-P.prod X Y .fam .subst (e₁ , e₂) .func (z , w))
                    (X .fam .subst e₁ .func z , Y .fam .subst e₂ .func w)
Fprod-subst-elt {X} {Y} {x} {x'} {y} {y'} e₁ e₂ z w =
  bpair-elt {SemiMod._⊕_ (X .fam .fm x) (Y .fam .fm y)} {X .fam .fm x'} {Y .fam .fm y'}
    (SemiMod._∘_ (X .fam .subst e₁) (SemiMod.p₁ {X .fam .fm x} {Y .fam .fm y}))
    (SemiMod._∘_ (Y .fam .subst e₂) (SemiMod.p₂ {X .fam .fm x} {Y .fam .fm y})) (z , w)

subst-refl : ∀ (X : Obj) {x : Setoid.Carrier (X .idx)} (e : Setoid._≈_ (X .idx) x x) (d : ∣ X .fam .fm x ∣) →
             Semimodule._≈_ (X .fam .fm x) (X .fam .subst e .func d) d
subst-refl X {x} e d = X .fam .indexed-family.Fam.refl* .func-eq (Semimodule.refl (X .fam .fm x) {d})

subst-trans : ∀ (X : Obj) {x y z : Setoid.Carrier (X .idx)} (e₁ : Setoid._≈_ (X .idx) x y) (e₂ : Setoid._≈_ (X .idx) y z)
              (d : ∣ X .fam .fm x ∣) →
              Semimodule._≈_ (X .fam .fm z) (X .fam .subst (Setoid.trans (X .idx) e₁ e₂) .func d)
                                            (X .fam .subst e₂ .func (X .fam .subst e₁ .func d))
subst-trans X {x} {y} {z} e₁ e₂ d = X .fam .indexed-family.Fam.trans* {x} {y} {z} e₂ e₁ .func-eq (Semimodule.refl (X .fam .fm x) {d})

transf-natural : ∀ {X Y : Obj} (f : Mor X Y) {x x' : Setoid.Carrier (X .idx)} (e : Setoid._≈_ (X .idx) x x')
                 (z : ∣ X .fam .fm x ∣) →
                 Semimodule._≈_ (Y .fam .fm (f .idxf .sfunc x'))
                   (f .famf .transf x' .func (X .fam .subst e .func z))
                   (Y .fam .subst (f .idxf .sfunc-resp-≈ e) .func (f .famf .transf x .func z))
transf-natural {X} f {x} {x'} e z = f .famf .indexed-family._⇒f_.natural {x} {x'} e .func-eq (Semimodule.refl (X .fam .fm x) {z})

elim-root-elt : ∀ {G X Y : Semimodule} (k : SemiMod.𝕀 ⇒ Y) (r : SemiMod._⊕_ G X ⇒ Y)
                (γe : ∣ G ∣) (a : Setoid.Carrier A) (y : ∣ X ∣) →
                Semimodule._≈_ Y (Ls.elim-root k r .func (γe , (a , y)))
                                 (Semimodule._+_ Y (r .func (γe , y)) (k .func a))
elim-root-elt {G} {X} {Y} k r γe a y =
  Semimodule.+-cong Y
    (r .func-resp-≈
       (Semimodule.trans (SemiMod._⊕_ G X)
          (bpair-elt {SemiMod._⊕_ G (Ls.L X)} {G} {X}
             (SemiMod._∘_ (SemiMod.id G) (SemiMod.p₁ {G} {Ls.L X}))
             (SemiMod._∘_ (Ls.payload-L {X}) (SemiMod.p₂ {G} {Ls.L X})) (γe , (a , y)))
          (Semimodule.refl G {γe} , Semimodule.+-lunit X {y})))
    (k .func-resp-≈ +-runit)

elimF-elt : ∀ {Γ' X C : Obj} (cC : Constant C) (f : Mor (FD.Fam𝒞-P.prod Γ' X) C)
            {γi : Setoid.Carrier (Γ' .idx)} {xi : Setoid.Carrier (X .idx)}
            (γe : ∣ Γ' .fam .fm γi ∣) (a : Setoid.Carrier A) (y : ∣ X .fam .fm xi ∣) →
            Semimodule._≈_ (C .fam .fm (f .idxf .sfunc (γi , xi)))
              (FD.elimF cC f .famf .transf (γi , xi) .func (γe , (a , y)))
              (Semimodule._+_ (C .fam .fm (f .idxf .sfunc (γi , xi)))
                (f .famf .transf (γi , xi) .func (γe , y))
                (cC .at (f .idxf .sfunc (γi , xi)) .func a))
elimF-elt cC f {γi} {xi} γe a y = elim-root-elt (cC .at (f .idxf .sfunc (γi , xi))) (f .famf .transf (γi , xi)) γe a y

elim-elt : ∀ {Γ' X C : Obj} (cC : Constant C) (body : Mor (FD.Fam𝒞-P.prod Γ' X) C) (f : Mor Γ' (FD.Lf X))
           {γi : Setoid.Carrier (Γ' .idx)} (γe : ∣ Γ' .fam .fm γi ∣) →
           Semimodule._≈_ (C .fam .fm (body .idxf .sfunc (γi , f .idxf .sfunc γi)))
             (FD.Fam𝒞._∘_ (FD.elimF cC body) (FD.Fam𝒞-P.pair (FD.Fam𝒞.id Γ') f) .famf .transf γi .func γe)
             (Semimodule._+_ (C .fam .fm (body .idxf .sfunc (γi , f .idxf .sfunc γi)))
               (body .famf .transf (γi , f .idxf .sfunc γi) .func (γe , proj₂ (f .famf .transf γi .func γe)))
               (cC .at (body .idxf .sfunc (γi , f .idxf .sfunc γi)) .func (proj₁ (f .famf .transf γi .func γe))))
elim-elt {Γ'} {X} {C} cC body f {γi} γe =
  Semimodule.trans (C .fam .fm (body .idxf .sfunc (γi , f .idxf .sfunc γi)))
    (FD.elimF cC body .famf .transf (γi , f .idxf .sfunc γi) .func-resp-≈
       {FD.Fam𝒞-P.pair (FD.Fam𝒞.id Γ') f .famf .transf γi .func γe} {γe , f .famf .transf γi .func γe}
       (Fpair-elt {Γ'} {Γ'} {FD.Lf X} (FD.Fam𝒞.id Γ') f γi γe))
    (elimF-elt {Γ'} {X} {C} cC body {γi} {f .idxf .sfunc γi} γe (proj₁ (f .famf .transf γi .func γe)) (proj₂ (f .famf .transf γi .func γe)))

-- Being below the control dependence is monotone in the control input's value, and a relation is a relation up to
-- zero.
ctrl-dep-linear : ∀ τ (i : Ix τ) s s' →
            Fib._≈_ τ i (ctrl-dep-at τ i (s +ₛ s')) (Fib._+_ τ i (ctrl-dep-at τ i s) (ctrl-dep-at τ i s'))
ctrl-dep-linear τ i s s' = ctrl-dep τ .at i .preserve-+ {s} {s'}

ctrl-dep-c : ∀ τ (i : Ix τ) s → Fib._≈_ τ i (ctrl-dep-at τ i (c ·ₛ s)) (ctrl-dep-at τ i s)
ctrl-dep-c τ i s =
  LI.ty-unit τ (λ ()) (λ ()) .at i .func-resp-≈
    (+-cong (≈-trans (≈-sym S.·-assoc) (·-cong c-idem ≈-refl)) ≈-refl)

⊑ctrl-dep-mono : ∀ τ (i : Ix τ) s s' m → Fib._⊑_ τ i m (ctrl-dep-at τ i s) → Fib._⊑_ τ i m (ctrl-dep-at τ i (s' +ₛ (c ·ₛ s)))
⊑ctrl-dep-mono τ i s s' m dm =
  Fib.⊑-trans τ i dm (Fib.⊑-trans τ i (IsJoin.inr (Fib.∨-isJoin τ i))
    (Fib.≈→⊑ τ i (Fib.sym τ i (Fib.trans τ i (ctrl-dep-linear τ i s' (c ·ₛ s)) (Fib.+-cong τ i (Fib.refl τ i) (ctrl-dep-c τ i s))))))

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
  ≈-trans (app-congᵥ (M.p₁ {m} {n}) (λ l → ≈-trans (+-cong (app-in₁ x l) (app-in₂ z l)) (concat-+ x z l)) k)
          (≈-trans (app-p₁ {m} {n} (M.concat x z) k) (M.split₁-concat x z k))

ap-p₂-++ : ∀ {m n} (x : ∣ 𝔽 m ∣) (z : ∣ 𝔽 n ∣) k →
           ap (M.p₂ {m} {n}) (λ l → ap (M.in₁ {m} {n}) x l +ₛ ap (M.in₂ {m} {n}) z l) k ≈s z k
ap-p₂-++ {m} {n} x z k =
  ≈-trans (app-congᵥ (M.p₂ {m} {n}) (λ l → ≈-trans (+-cong (app-in₁ x l) (app-in₂ z l)) (concat-+ x z l)) k)
          (≈-trans (app-p₂ {m} {n} (M.concat x z) k) (M.split₂-concat x z k))

EnvDepRel-resp : ∀ {Γ} {γ : Env Γ} {gi} (rγ : EnvValRel γ gi) s {x x' g} →
                 (∀ k → x k ≈s x' k) → EnvDepRel rγ s x g → EnvDepRel rγ s x' g
EnvDepRel-resp emp s ex rel = prop.tt
EnvDepRel-resp (_·_ {γ = γ} {v = v} rγ r) s ex (rel , h) =
  EnvDepRel-resp rγ s (app-congᵥ (M.p₁ {width-env γ} {width v}) ex) rel ,
  DepRel⊑-resp _ r s (app-congᵥ (M.p₂ {width-env γ} {width v}) ex) h

-- The weight times s absorbs any multiple of s.
cs-absorb : ∀ s e → ((c ·ₛ s) +ₛ ((s ·ₛ c) ·ₛ e)) ≈s (c ·ₛ s)
cs-absorb s e =
  ≈-trans (+-cong ·-comm S.·-assoc)
  (≈-trans (≈-sym S.·-+-distribₗ)
  (≈-trans (·-cong ≈-refl (≈-trans +-comm (c-bound e))) ·-comm))

-- The control dependence at the weighted s plus itself and a further weight: the one at s plus the
-- one at the further weight.
ctrl-dep-double : ∀ τ (i : Ix τ) s a → Fib._≈_ τ i (ctrl-dep-at τ i ((c ·ₛ s) +ₛ ((c ·ₛ s) +ₛ a))) (Fib._+_ τ i (ctrl-dep-at τ i s) (ctrl-dep-at τ i a))
ctrl-dep-double τ i s a =
  Fib.trans τ i (ctrl-dep-linear τ i (c ·ₛ s) ((c ·ₛ s) +ₛ a))
  (Fib.trans τ i (Fib.+-cong τ i (ctrl-dep-c τ i s) (Fib.trans τ i (ctrl-dep-linear τ i (c ·ₛ s) a) (Fib.+-cong τ i (ctrl-dep-c τ i s) (Fib.refl τ i))))
  (Fib.trans τ i (Fib.sym τ i (Fib.+-assoc τ i)) (Fib.+-cong τ i (Fib.⊑-refl τ i) (Fib.refl τ i))))

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

-- A base sort's fibres do not vary with the index, so its transports are the identity.
subst-base : ∀ {σ} {i i' : Ix (base σ)} (e : Ix._≈_ (base σ) i i')
             (d : ∣ Fib (base σ) i ∣) (k : Fin (sort-width σ)) →
             ⟦ base σ ⟧ .fam .subst e .func d k ≈s d k
subst-base {σ} e d k = Σ-unit {sort-width σ} k d

-- Transporting a relation along an index equation.
DepRel-transport : ∀ τ {v : Val τ} {i i' : Ix τ} (E : Ix._≈_ τ i i') (r : ValRel τ v i)
                   {o : ∣ 𝔽 (width v) ∣} {d : ∣ Fib τ i ∣} →
                   DepRel τ r o d → DepRel τ (ValRel-resp τ E r) o (⟦ τ ⟧ .fam .subst E .func d)
DepRel-transport unit {unit} {i} {i'} E r {o} {d} h k =
  ≈-trans (h k) (≈-sym (subst-refl ⟦ unit ⟧ {i} E d k))
DepRel-transport (base σ) {const a} {i} {i'} E r {o} {d} h k =
  ≈-trans (h k) (≈-sym (subst-base {σ} {i} {i'} E d k))
DepRel-transport (σ [+] τ) {inl v} {i} {i'} E (i₀ , r₀ , ⟪ e₀ ⟫) {o} {d} (h₀ , h) =
  let e' = Ix.trans (σ [+] τ) {i'} {i} {inj₁ i₀} (Ix.sym (σ [+] τ) {i} {i'} E) e₀
      comp = subst-trans ⟦ σ [+] τ ⟧ {i} {i'} {inj₁ i₀} E e' d
  in
  ≈-trans h₀ (proj₁ comp) ,
  DepRel-resp σ r₀ (λ k → ≈-refl) (proj₂ comp) h
DepRel-transport (σ [+] τ) {inr v} {i} {i'} E (i₀ , r₀ , ⟪ e₀ ⟫) {o} {d} (h₀ , h) =
  let e' = Ix.trans (σ [+] τ) {i'} {i} {inj₂ i₀} (Ix.sym (σ [+] τ) {i} {i'} E) e₀
      comp = subst-trans ⟦ σ [+] τ ⟧ {i} {i'} {inj₂ i₀} E e' d
  in
  ≈-trans h₀ (proj₁ comp) ,
  DepRel-resp τ r₀ (λ k → ≈-refl) (proj₂ comp) h
DepRel-transport (σ [×] τ) {pair v u} {i , j} {i' , j'} (E₁ , E₂) (r₁ , r₂) {o} {d} (h₀ , (h₁ , h₂)) =
  ≈-trans h₀ (≈-sym +-runit) ,
  (DepRel-resp σ (ValRel-resp σ E₁ r₁) (λ k → ≈-refl)
     (Fib.sym σ i' (Fib.trans σ i' (Fib.+-lunit σ i') (m-runit (Fib σ i'))))
     (DepRel-transport σ E₁ r₁ h₁) ,
   DepRel-resp τ (ValRel-resp τ E₂ r₂) (λ k → ≈-refl)
     (Fib.sym τ j' (Fib.trans τ j' (Fib.+-lunit τ j') (Fib.+-lunit τ j')))
     (DepRel-transport τ E₂ r₂ h₂))
DepRel-transport (σ [→] τ) {clo γ' t} {f} {f'} E r {o} {d} (h₀ , hc) =
  ≈-trans h₀ (≈-sym +-runit) ,
  λ s' {v} {j} rv z y hz {u} {U} D →
    DepRel-resp τ (ValRel-resp τ (Ej j) (r rv D)) (λ k → ≈-refl)
      (Fib.trans τ (f' .idxf .sfunc j)
         (⟦ τ ⟧ .fam .subst (Ej j) .preserve-+ {ctrl-dep-at τ (f .idxf .sfunc j) (s' +ₛ o zero)} {_})
      (Fib.+-cong τ (f' .idxf .sfunc j) (ctrl-dep-natural τ (Ej j) (s' +ₛ o zero))
      (Fib.trans τ (f' .idxf .sfunc j)
         (⟦ τ ⟧ .fam .subst (Ej j) .preserve-+ {_} {_})
      (Fib.+-cong τ (f' .idxf .sfunc j) (eval-part j) (famf-eq-at σ τ E j y)))))
      (DepRel-transport τ (Ej j) (r rv D) (hc s' rv z y hz D))
  where
  Ej = idx-eq-at σ τ E
  hmap = indexed-family.reindex-≈ {P = ⟦ τ ⟧ .fam} (f .idxf) (f' .idxf) (E .FD._≃_.idxf-eq)
  eval-part : ∀ j → Fib._≈_ τ (f' .idxf .sfunc j)
                (⟦ τ ⟧ .fam .subst (Ej j) .func (evalΠ σ τ f j .func (proj₂ d)))
                (evalΠ σ τ f' j .func
                   (proj₂ (⟦ σ [→] τ ⟧ .fam .subst {f} {f'} E .func d)))
  eval-part j =
    Fib.trans τ (f' .idxf .sfunc j)
      (Fib.sym τ (f' .idxf .sfunc j)
         (SP.lambda-eval {A = ⟦ σ ⟧ .idx} {P = ⟦ τ ⟧ .fam indexed-family.[ f' .idxf ]}
            {x = Payload σ τ f}
            {f = indexed-family._∘f_ {A = ⟦ σ ⟧ .idx}
                   {P = indexed-family.constantFam (⟦ σ ⟧ .idx) SemiMod.cat (Payload σ τ f)}
                   {Q = ⟦ τ ⟧ .fam indexed-family.[ f .idxf ]} {R = ⟦ τ ⟧ .fam indexed-family.[ f' .idxf ]}
                   hmap (SP.evalΠf {A = ⟦ σ ⟧ .idx} (⟦ τ ⟧ .fam indexed-family.[ f .idxf ]))} j
            .func-eq {proj₂ d} {proj₂ d} (Payload.refl σ τ f {proj₂ d})))
      (evalΠ σ τ f' j .func-resp-≈
         {SP.Π-map hmap .func (proj₂ d)} {proj₂ (⟦ σ [→] τ ⟧ .fam .subst {f} {f'} E .func d)}
         (Payload.sym σ τ f' {proj₂ (⟦ σ [→] τ ⟧ .fam .subst {f} {f'} E .func d)} {SP.Π-map hmap .func (proj₂ d)}
            (Payload.+-lunit σ τ f' {SP.Π-map hmap .func (proj₂ d)})))

