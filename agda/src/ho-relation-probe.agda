{-# OPTIONS --prop --postfix-projections --safe #-}

-- The logical relation between the operational semantics and the higher-order model: values against
-- indices of the interpretation, dependence vectors against elements of the fibre, and the lemmas by
-- recursion on types that the fundamental lemma needs (respect for the setoids, adding control
-- dependence and the elimination constant, absorption, transport, independence of the size bound at
-- μ-types).
open import Level using (0ℓ; lift)
open import Data.Nat using (ℕ; suc; _+_; _<_; s≤s)
open import Data.Nat.Properties using (≤-reflexive; <-trans; n<1+n; m≤m+n; m≤n+m)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Data.Fin using (Fin; zero; suc; splitAt; _↑ˡ_; _↑ʳ_)
open import Data.Fin.Properties using (splitAt⁻¹-↑ˡ; splitAt⁻¹-↑ʳ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import every using (Every)
open import Data.List using ([]; _∷_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Relation.Binary.PropositionalEquality as ≡
open import polynomial-functor using (Poly; extend)
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

module ho-relation-probe
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A) (elim-weight : Setoid.Carrier A)
  (Sig : Signature 0ℓ) (ℐ : Interpretation S Sig)
  (let module Sc = CommutativeSemiring S)
  -- Addition is idempotent, and the elimination weight is idempotent and absorbs its multiples.
  (+-idem : ∀ x → Setoid._≈_ A (x Sc.+ x) x)
  (w-idem : Setoid._≈_ A (elim-weight Sc.· elim-weight) elim-weight)
  (w-absorb : ∀ x → Setoid._≈_ A ((elim-weight Sc.· x) Sc.+ elim-weight) elim-weight)
  where

open Signature Sig
open Interpretation ℐ
open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.evaluation Sig S ℐ elim-weight
open import language-operational.type-substitution Sig using (unfold-sub)

module model = ho-model S elim-weight
module interp = model.interp Sig ℐ
open model using (𝔽; mat; ι1-fwd; ι1-bwd; module Ls; module SemiMod)
open SemiMod using (Semimodule; _⇒_)
open Semimodule using () renaming (Carrier to ∣_∣)
open SemiMod._⇒_ using (func)

module M = matrix.Mat S
module SMP = HasProducts SemiMod.products
module FD = model.Fam⟨𝒟⟩μ
module SP = HasSetoidProducts model.SPmod

open FD using (Obj; Mor; idx; fam; fm; idxf; famf; Constant; mkSort)
open indexed-family.Fam using (subst)
open indexed-family._⇒f_ using (transf)
open prop-setoid._⇒_ using () renaming (func to sfunc)

-- The interpretation, at the parameters the higher-order model fixes.
module LI = language-interpretation Sig 0ℓ 0ℓ
  SemiMod.terminal SemiMod.cmon-enriched SemiMod.biproduct SemiMod.𝕀 model.SemiModExp
  interp.δ∅𝒟 interp.𝒟𝟙ty interp.𝒟unit-pt interp.𝒟-Sig-model model.elim-weight-endo
  (λ {X} {Y} → model.exp-const {X} {Y}) interp.𝒟𝟙ty-const interp.𝒟-sort-const

open LI using (⟦_⟧ty; ⟦_⟧ctxt; ⟦_⟧tm; ⟦_⟧tms; elim-const; ty-unit)
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



module FDC = Category FD.cat

-- The interpretation of roll at a closed body: the map from the unfolded type into the carrier.
roll-mor : (τ : type 1) → Mor ⟦ τ [ μ τ ] ⟧ ⟦ μ τ ⟧
roll-mor τ = FDC._∘_ (FD.InMapDef.inMor (LI.as-poly τ (λ ())) interp.δ∅𝒟) (LI.sub-as-apply-fwd τ (μ τ))

-- Transport of a fibre element along an equation between closed types.
subst-fib : ∀ {ρ ρ' : type 0} (E : ρ ≡ ρ') {j : Ix ρ} → ∣ Fib ρ j ∣ → ∣ Fib ρ' (≡.subst Ix E j) ∣
subst-fib ≡.refl d = d

-- The relations at the variables of an open type under a substitution of closed types: values below a
-- size bound against indices.
record VarRel {n} (σ : TySub n 0) (N : ℕ) : Set₁ where
  field vrel : ∀ j (u : Val (σ j)) → size u < N → Ix (σ j) → Set

open VarRel public

extend-VarRel : ∀ {n} {σ : TySub n 0} {N} {ρ : type 0} →
                ((u : Val ρ) → size u < N → Ix ρ → Set) → VarRel σ N → VarRel (extend σ ρ) N
extend-VarRel R₀ R .vrel zero    = R₀
extend-VarRel R₀ R .vrel (suc j) = R .vrel j

lower-VarRel : ∀ {n} {σ : TySub n 0} {N N'} → N' < N → VarRel σ N → VarRel σ N'
lower-VarRel p R .vrel j u q = R .vrel j u (<-trans q p)

mu-VarRel : ∀ {τ N} → ((u : Val (μ τ)) → size u < N → Ix (μ τ) → Set) → VarRel (push (μ τ)) N
mu-VarRel R .vrel zero = R
mu-VarRel R .vrel (suc ())

-- Values related to indices, by recursion on the type. A closure is related to a fibre map of the
-- exponential when, for every related argument and every derivation of the body at it, the result
-- is related to the map's index at the argument. A rolled value is related to a tree when its payload
-- is related, at the body under the substitution of the μ-type, to an index the interpretation of
-- roll sends to the tree, by well-founded recursion on the value: the relation itself, at smaller
-- values, stands at the recursive variable. A value at an open type under a substitution of closed
-- types is related to an index of the substituted type given the relations at the variables; a
-- nested μ-type extends the substitution by its unfolding.
ValRel : ∀ τ → Val τ → Ix τ → Set
MuRel : ∀ (τ : type 1) (N : ℕ) → Acc _<_ N → (v : Val (μ τ)) → size v < N → Ix (μ τ) → Set
SubRel : ∀ {n} (τ : type n) (σ : TySub n 0) (N : ℕ) → Acc _<_ N → VarRel σ N →
         (v : Val (sub σ τ)) → size v < N → Ix (sub σ τ) → Set

ValRel unit unit i = ⊤
ValRel (base s) (const c) i = Prf (Setoid._≈_ (sort-index s) i c)
ValRel (σ [+] τ) (inl v) i = Σ (Ix σ) λ i' → ValRel σ v i' × Prf (Setoid._≈_ (⟦ σ [+] τ ⟧ .idx) i (inj₁ i'))
ValRel (σ [+] τ) (inr v) i = Σ (Ix τ) λ i' → ValRel τ v i' × Prf (Setoid._≈_ (⟦ σ [+] τ ⟧ .idx) i (inj₂ i'))
ValRel (σ [×] τ) (pair v u) (i , j) = ValRel σ v i × ValRel τ u j
ValRel (σ [→] τ) (clo γ' t) f =
  ∀ {v : Val σ} {j : Ix σ} → ValRel σ v j → ∀ {u U} → γ' · v , t ⇓ u [ U ] → ValRel τ u (f .idxf .sfunc j)
ValRel (μ τ) v i = MuRel τ (suc (size v)) (<-wellFounded _) v (n<1+n _) i

MuRel τ N (acc rs) (roll w) p i =
  Σ (Ix (τ [ μ τ ])) λ j →
    SubRel τ (push (μ τ)) (suc (size w)) (rs p) (mu-VarRel (MuRel τ (suc (size w)) (rs p))) w (n<1+n _) j ×
    Prf (Setoid._≈_ (⟦ μ τ ⟧ .idx) i (roll-mor τ .idxf .sfunc j))

SubRel (var i) σ N a RP v p j = RP .vrel i v p j
SubRel unit σ N a RP unit p j = ⊤
SubRel (base s) σ N a RP (const c) p j = Prf (Setoid._≈_ (sort-index s) j c)
SubRel (σ₁ [+] σ₂) σ N a RP (inl v) p j =
  Σ (Ix (sub σ σ₁)) λ j' →
    SubRel σ₁ σ N a RP v (<-trans (n<1+n _) p) j' × Prf (Setoid._≈_ (⟦ sub σ σ₁ [+] sub σ σ₂ ⟧ .idx) j (inj₁ j'))
SubRel (σ₁ [+] σ₂) σ N a RP (inr v) p j =
  Σ (Ix (sub σ σ₂)) λ j' →
    SubRel σ₂ σ N a RP v (<-trans (n<1+n _) p) j' × Prf (Setoid._≈_ (⟦ sub σ σ₁ [+] sub σ σ₂ ⟧ .idx) j (inj₂ j'))
SubRel (σ₁ [×] σ₂) σ N a RP (pair v u) p (j , k) =
  SubRel σ₁ σ N a RP v (<-trans (s≤s (m≤m+n (size v) (size u))) p) j ×
  SubRel σ₂ σ N a RP u (<-trans (s≤s (m≤n+m (size u) (size v))) p) k
SubRel (σ₁ [→] σ₂) σ N a RP v p j = ValRel (σ₁ [→] σ₂) v j
SubRel (μ τ) σ N (acc rs) RP (roll w) p i =
  Σ (Ix (B [ μ B ])) λ j →
    SubRel τ (extend σ (μ B)) (suc (size w)) (rs p)
      (extend-VarRel (SubRel (μ τ) σ (suc (size w)) (rs p) (lower-VarRel p RP)) (lower-VarRel p RP))
      (≡.subst Val (unfold-sub σ τ) w) (s≤s (≤-reflexive (size-subst (unfold-sub σ τ) w))) (≡.subst Ix (unfold-sub σ τ) j) ×
    Prf (Setoid._≈_ (⟦ μ B ⟧ .idx) i (roll-mor B .idxf .sfunc j))
  where B = sub (sub-lift σ) τ

-- The vector over the body's inputs at an application: the value at the control input, then the
-- closure's cells and the argument as the environment.
body-input : ∀ {Γ' σ} (γ' : Env Γ') (v : Val σ) → Setoid.Carrier A →
             ∣ 𝔽 (width-env γ') ∣ → ∣ 𝔽 (width v) ∣ → ∣ 𝔽 (suc (width-env γ' + width v)) ∣
body-input γ' v s c z zero    = s
body-input γ' v s c z (suc k) =
  Semimodule._+_ (𝔽 (width-env γ' + width v))
    (mat (M.in₁ {width-env γ'} {width v}) .func c)
    (mat (M.in₂ {width-env γ'} {width v}) .func z) k

-- The dependence relations at the variables, over the value relations there.
record VarDep {n} {σ : TySub n 0} {N} (RP : VarRel σ N) : Set₁ where
  field vdep : ∀ j u q x (r : RP .vrel j u q x) → ∣ 𝔽 (width u) ∣ → ∣ Fib (σ j) x ∣ → Prop

open VarDep public

extend-VarDep : ∀ {n} {σ : TySub n 0} {N} {ρ : type 0}
                (R₀ : (u : Val ρ) → size u < N → Ix ρ → Set) (RP : VarRel σ N) →
                (∀ u q x (r : R₀ u q x) → ∣ 𝔽 (width u) ∣ → ∣ Fib ρ x ∣ → Prop) →
                VarDep RP → VarDep (extend-VarRel R₀ RP)
extend-VarDep R₀ RP D₀ D .vdep zero    = D₀
extend-VarDep R₀ RP D₀ D .vdep (suc j) = D .vdep j

lower-VarDep : ∀ {n} {σ : TySub n 0} {N N'} (p : N' < N) (RP : VarRel σ N) → VarDep RP → VarDep (lower-VarRel p RP)
lower-VarDep p RP D .vdep j u q = D .vdep j u (<-trans q p)

mu-VarDep : ∀ {τ N} (R : (u : Val (μ τ)) → size u < N → Ix (μ τ) → Set) →
            (∀ u q x (r : R u q x) → ∣ 𝔽 (width u) ∣ → ∣ Fib (μ τ) x ∣ → Prop) → VarDep (mu-VarRel R)
mu-VarDep R D .vdep zero = D
mu-VarDep R D .vdep (suc ())

-- A dependence vector on a value's positions against an element of the fibre at a related index.
-- At an arrow type the root agrees, and for any further weight, any related argument and any
-- derivation of the body, the body's dependence through the root and the further weight at the
-- control input and the cells and argument as environment agrees with the elimination constant at
-- that weight plus the payload evaluated at the argument plus the index's fibre map at the argument. At
-- a μ-type the element is the interpretation of roll applied to an element related to the payload.
DepRel : ∀ τ {v : Val τ} {i : Ix τ} → ValRel τ v i → ∣ 𝔽 (width v) ∣ → ∣ Fib τ i ∣ → Prop
MuDepRel : ∀ (τ : type 1) (N : ℕ) (a : Acc _<_ N) {v : Val (μ τ)} {p : size v < N} {i : Ix (μ τ)} →
           MuRel τ N a v p i → ∣ 𝔽 (width v) ∣ → ∣ Fib (μ τ) i ∣ → Prop
SubDepRel : ∀ {n} (τ : type n) (σ : TySub n 0) (N : ℕ) (a : Acc _<_ N) (RP : VarRel σ N) → VarDep RP →
            {v : Val (sub σ τ)} {p : size v < N} {j : Ix (sub σ τ)} → SubRel τ σ N a RP v p j →
            ∣ 𝔽 (width v) ∣ → ∣ Fib (sub σ τ) j ∣ → Prop

DepRel unit {unit} {i} r o d = Semimodule._≈_ (Fib unit i) o d
DepRel (base s) {const c} {i} r o d = Semimodule._≈_ (Fib (base s) i) o d
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
     (z : ∣ 𝔽 (width v) ∣) (y : ∣ Fib σ j ∣) → DepRel σ rv z y →
   ∀ {u U} (D : γ' · v , t ⇓ u [ U ]) →
     DepRel τ (r rv D) (mat U .func (body-input γ' v (s' Sc.+ o zero) (λ k → o (suc k)) z))
       (Semimodule._+_ (Fib τ (f .idxf .sfunc j))
         (elim-const τ .at (f .idxf .sfunc j) .func (s' Sc.+ o zero))
         (Semimodule._+_ (Fib τ (f .idxf .sfunc j))
           (SP.evalΠ (⟦ τ ⟧ .fam indexed-family.[ f .idxf ]) j .func (proj₂ d))
           (f .famf .transf j .func y))))
DepRel (μ τ) {v} {i} r o d = MuDepRel τ (suc (size v)) (<-wellFounded _) {v} {n<1+n _} {i} r o d

MuDepRel τ N (acc rs) {roll w} {p} {i} (j , r , ⟪ e ⟫) o d =
  ∃ (∣ Fib (τ [ μ τ ]) j ∣) λ d' →
    Semimodule._≈_ (Fib (μ τ) (roll-mor τ .idxf .sfunc j))
      (⟦ μ τ ⟧ .fam .subst {i} {roll-mor τ .idxf .sfunc j} e .func d) (roll-mor τ .famf .transf j .func d') ∧
    SubDepRel τ (push (μ τ)) (suc (size w)) (rs p) (mu-VarRel (MuRel τ (suc (size w)) (rs p)))
      (mu-VarDep (MuRel τ (suc (size w)) (rs p)) (λ u q x r → MuDepRel τ (suc (size w)) (rs p) {u} {q} {x} r)) r o d'

SubDepRel (var i) σ N a RP DP {v} {p} {j} r o dv = DP .vdep i v p j r o dv
SubDepRel unit σ N a RP DP {unit} {j = j} r o dv = Semimodule._≈_ (Fib unit j) o dv
SubDepRel (base s) σ N a RP DP {const c} {j = j} r o dv = Semimodule._≈_ (Fib (base s) j) o dv
SubDepRel (σ₁ [+] σ₂) σ N a RP DP {inl v} {j = j} (j' , r , ⟪ e ⟫) o dv =
  let dv' = ⟦ sub σ σ₁ [+] sub σ σ₂ ⟧ .fam .subst {j} {inj₁ j'} e .func dv in
  (o zero ≈A proj₁ dv') ∧ SubDepRel σ₁ σ N a RP DP r (λ k → o (suc k)) (proj₂ dv')
SubDepRel (σ₁ [+] σ₂) σ N a RP DP {inr v} {j = j} (j' , r , ⟪ e ⟫) o dv =
  let dv' = ⟦ sub σ σ₁ [+] sub σ σ₂ ⟧ .fam .subst {j} {inj₂ j'} e .func dv in
  (o zero ≈A proj₁ dv') ∧ SubDepRel σ₂ σ N a RP DP r (λ k → o (suc k)) (proj₂ dv')
SubDepRel (σ₁ [×] σ₂) σ N a RP DP {pair v u} {j = j , k} (r , r') o dv =
  (o zero ≈A proj₁ dv) ∧
  (SubDepRel σ₁ σ N a RP DP r (mat (M.p₁ {width v} {width u}) .func (λ k → o (suc k))) (proj₁ (proj₂ dv)) ∧
   SubDepRel σ₂ σ N a RP DP r' (mat (M.p₂ {width v} {width u}) .func (λ k → o (suc k))) (proj₂ (proj₂ dv)))
SubDepRel (σ₁ [→] σ₂) σ N a RP DP {v} {j = j} r o dv = DepRel (σ₁ [→] σ₂) {v} {j} r o dv
SubDepRel (μ τ) σ N (acc rs) RP DP {roll w} {p} {i} (j , r , ⟪ e ⟫) o d =
  ∃ (∣ Fib (B [ μ B ]) j ∣) λ d' →
    Semimodule._≈_ (Fib (μ B) (roll-mor B .idxf .sfunc j))
      (⟦ μ B ⟧ .fam .subst {i} {roll-mor B .idxf .sfunc j} e .func d) (roll-mor B .famf .transf j .func d') ∧
    SubDepRel τ (extend σ (μ B)) (suc (size w)) (rs p)
      (extend-VarRel (SubRel (μ τ) σ (suc (size w)) (rs p) (lower-VarRel p RP)) (lower-VarRel p RP))
      (extend-VarDep (SubRel (μ τ) σ (suc (size w)) (rs p) (lower-VarRel p RP)) (lower-VarRel p RP)
         (λ u q x r → SubDepRel (μ τ) σ (suc (size w)) (rs p) (lower-VarRel p RP) (lower-VarDep p RP DP) {u} {q} {x} r)
         (lower-VarDep p RP DP))
      r (λ k → o (≡.subst Fin (width-subst (unfold-sub σ τ) w) k)) (subst-fib (unfold-sub σ τ) d')
  where B = sub (sub-lift σ) τ
