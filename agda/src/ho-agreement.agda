{-# OPTIONS --prop --postfix-projections #-}

-- Agreement between the operational relation and the higher-order model, on the fragment without
-- μ-types and primitives. A value denotes an index of its type's interpretation and a fibre map
-- from the free semimodule on its positions to the fibre there, both by recursion on the value; a
-- closure denotes the index and fibre of the lambda's denotation at its environment. The
-- fundamental lemma, by induction on the derivation, says the term's denotation at the
-- environment's denotation is the value's, that the environment columns of the relation realise
-- as the fibre map, and that the source column realises as the elimination constant. At a
-- closure's payload the two sides agree only up to a control mark scaled by the closure's root:
-- the operational environment cells carry marks that the interpretation's payload does not, and an
-- application absorbs them into the constant its own elimination writes. The absorption needs the
-- unit weight to be top and the elimination weight idempotent, as in a lattice.
open import Level using (0ℓ; lift)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import prop
open import prop using (_∧_; ∃; ∃ₛ; LiftS; liftS)
open import prop-setoid using (Setoid; IsEquivalence)
open import commutative-semiring using (CommutativeSemiring)
open import signature using (Signature)
open import primitives using (Primitives)
open import categories using (Category; HasProducts; HasTerminal; HasWeakExponentials)
open import cmon-enriched using (CMonEnriched; Biproduct)
import indexed-family
import matrix
import semimodule
import ho-model
import language-interpretation

module ho-agreement
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A) (elim-weight : Setoid.Carrier A)
  (Sig : Signature 0ℓ) (𝒫 : Primitives S Sig)
  (let module Sc = CommutativeSemiring S)
  -- The unit weight is top and the elimination weight idempotent.
  (+-top : ∀ x → Setoid._≈_ A (x Sc.+ Sc.ι) Sc.ι)
  (w-idem : Setoid._≈_ A (elim-weight Sc.· elim-weight) elim-weight)
  where

open Signature Sig
open Primitives 𝒫
open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.evaluation Sig S 𝒫 elim-weight

module model = ho-model S elim-weight
module interp = model.interp Sig 𝒫
open model using (𝔽; mat; ι1-fwd; ι1-bwd; 𝔽-L-iso; 𝔽-biproduct; module Ls; module SemiMod)
open SemiMod using (Semimodule; _⇒_; _≈m_)
open Semimodule using () renaming (Carrier to ∣_∣)
open SemiMod._⇒_ using (func)

private
  module M = matrix.Mat S
  module SMC = Category SemiMod.cat
  module SMCM = CMonEnriched SemiMod.cmon-enriched
  module SMP = HasProducts SemiMod.products
  module FD = model.Fam⟨𝒟⟩μ

open FD using (Obj; Mor; idx; fam; fm; idxf; famf; Lf; Constant)
open indexed-family.Fam using (subst)
open indexed-family._⇒f_ using (transf)
open prop-setoid._⇒_ using () renaming (func to sfunc)

-- The interpretation, at the parameters the higher-order model fixes.
module LI = language-interpretation Sig 0ℓ 0ℓ
  SemiMod.terminal SemiMod.cmon-enriched SemiMod.biproduct SemiMod.𝕀 model.SemiModExp
  interp.δ∅𝒟 interp.𝒟𝟙ty interp.𝒟unit-pt interp.𝒟-Sig-model model.elim-weight-endo
  (λ {X} {Y} → model.exp-const {X} {Y}) interp.𝒟𝟙ty-const interp.𝒟-sort-const

open LI using (⟦_⟧ty; ⟦_⟧ctxt; ⟦_⟧tm; elim-const; ty-unit)
open HasWeakExponentials model.SemiModExp using (lambda; eval)

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

-- The fragment: no μ-types, no primitives.
mutual
  data CoreVal : ∀ {τ} → Val τ → Set where
    unit : CoreVal unit
    inl  : ∀ {τ₁ τ₂} {v : Val τ₁} → CoreVal v → CoreVal (inl {τ₂ = τ₂} v)
    inr  : ∀ {τ₁ τ₂} {v : Val τ₂} → CoreVal v → CoreVal (inr {τ₁ = τ₁} v)
    pair : ∀ {τ₁ τ₂} {v : Val τ₁} {u : Val τ₂} → CoreVal v → CoreVal u → CoreVal (pair v u)
    clo  : ∀ {Γ σ τ} {γ : Env Γ} {t : Γ ▸ σ ⊢ τ} → CoreEnv γ → CoreTm t → CoreVal (clo γ t)

  data CoreEnv : ∀ {Γ} → Env Γ → Set where
    emp : CoreEnv emp
    _·_ : ∀ {Γ τ} {γ : Env Γ} {v : Val τ} → CoreEnv γ → CoreVal v → CoreEnv (γ · v)

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

infixl 30 _·_

-- The denotation of a value: its index, and its fibre map from the free semimodule on its
-- positions. Lifted values map their root to the root and their payload under the injection; a
-- closure's payload is the lambda's fibre at the environment's denotation.
mutual
  ⌊_⌋ : ∀ {τ} {v : Val τ} → CoreVal v → Ix τ
  ⌊ unit ⌋      = lift tt
  ⌊ inl m ⌋     = inj₁ ⌊ m ⌋
  ⌊ inr m ⌋     = inj₂ ⌊ m ⌋
  ⌊ pair m n ⌋  = ⌊ m ⌋ , ⌊ n ⌋
  ⌊ clo {t = t} mγ mt ⌋ = lambda ⟦ t ⟧tm .idxf .sfunc ⌊ mγ ⌋e

  ⌊_⌋e : ∀ {Γ} {γ : Env Γ} → CoreEnv γ → IxC Γ
  ⌊ emp ⌋e     = lift tt
  ⌊ mγ · m ⌋e = ⌊ mγ ⌋e , ⌊ m ⌋

  ⌊_⌋f : ∀ {τ} {v : Val τ} (m : CoreVal v) → 𝔽 (width v) ⇒ Fib τ ⌊ m ⌋
  ⌊ unit ⌋f = SemiMod.id (𝔽 1)
  ⌊ inl {v = v} m ⌋f = SemiMod._∘_ (Ls.Lmap ⌊ m ⌋f) (𝔽-L-iso (width v) .Category.Iso.fwd)
  ⌊ inr {v = v} m ⌋f = SemiMod._∘_ (Ls.Lmap ⌊ m ⌋f) (𝔽-L-iso (width v) .Category.Iso.fwd)
  ⌊ pair {v = v} {u = u} m n ⌋f =
    SemiMod._∘_ (Ls.Lmap (SMP.pair (SemiMod._∘_ ⌊ m ⌋f (mat (M.p₁ {width v} {width u})))
                                   (SemiMod._∘_ ⌊ n ⌋f (mat (M.p₂ {width v} {width u})))))
                (𝔽-L-iso (width v + width u) .Category.Iso.fwd)
  ⌊ clo {γ = γ} {t = t} mγ mt ⌋f =
    SemiMod._∘_ (Ls.Lmap (SemiMod._∘_ (lambda ⟦ t ⟧tm .famf .transf ⌊ mγ ⌋e) ⌊ mγ ⌋ef))
                (𝔽-L-iso (width-env γ) .Category.Iso.fwd)

  ⌊_⌋ef : ∀ {Γ} {γ : Env Γ} (mγ : CoreEnv γ) → 𝔽 (width-env γ) ⇒ FibC Γ ⌊ mγ ⌋e
  ⌊ emp ⌋ef = SemiMod.ε-map (𝔽 0) SemiMod.𝟘
  ⌊ _·_ {γ = γ} {v = v} mγ m ⌋ef =
    SMP.pair (SemiMod._∘_ ⌊ mγ ⌋ef (mat (M.p₁ {width-env γ} {width v})))
             (SemiMod._∘_ ⌊ m ⌋f (mat (M.p₂ {width-env γ} {width v})))

private
  w = elim-weight

-- Agreement of two elements of a fibre: equal, except at a closure's payload, where the first
-- may exceed the second by a control mark scaled by the root.
Agree : ∀ (τ : type 0) {i : Ix τ} → ∣ Fib τ i ∣ → ∣ Fib τ i ∣ → Prop
Agree unit {i} x y = Semimodule._≈_ (Fib unit i) x y
Agree (base s) {i} x y = Semimodule._≈_ (Fib (base s) i) x y
Agree (σ [+] τ) {inj₁ i} (a , x) (b , y) = Setoid._≈_ A a b ∧ Agree σ x y
Agree (σ [+] τ) {inj₂ i} (a , x) (b , y) = Setoid._≈_ A a b ∧ Agree τ x y
Agree (σ [×] τ) {i , j} (a , (x₁ , x₂)) (b , (y₁ , y₂)) =
  Setoid._≈_ A a b ∧ (Agree σ x₁ y₁ ∧ Agree τ x₂ y₂)
Agree (σ [→] τ) {f} (a , x) (b , y) =
  Setoid._≈_ A a b ∧
  ∃ ∣ P ∣ (λ K → Semimodule._≈_ P x (Semimodule._+_ P y (Semimodule._·_ P (a Sc.· w) K)))
  where P = model.FE._⟶_ ⟦ σ ⟧ ⟦ τ ⟧ .fam .fm f
Agree (μ τ) {i} x y = Semimodule._≈_ (Fib (μ τ) i) x y

open Constant using (at)

-- The value's control positions realise as the elimination constant at its index.
ctrl-const : ∀ {τ} {v : Val τ} (m : CoreVal v) (x : ∣ 𝔽 1 ∣) →
             Semimodule._≈_ (Fib τ ⌊ m ⌋)
               (⌊ m ⌋f .func (mat (ctrl-of v) .func x))
               (elim-const τ .at ⌊ m ⌋ .func (ι1-fwd .func x))
ctrl-const = {!!}

-- Agreement of a derivation with the interpretation: the index, the environment columns and the
-- source column.
record Agrees {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ])
              (mγ : CoreEnv γ) (m : CoreVal v) : Prop where
  field
    ix  : Setoid._≈_ (⟦ τ ⟧ .idx) (⟦ t ⟧tm .idxf .sfunc ⌊ mγ ⌋e) ⌊ m ⌋
    env : ∀ (x : ∣ 𝔽 (width-env γ) ∣) →
          Agree τ (⌊ m ⌋f .func (mat (cols {γ = γ} R environment) .func x))
                        (⟦ τ ⟧ .fam .subst ix .func
                          (⟦ t ⟧tm .famf .transf ⌊ mγ ⌋e .func (⌊ mγ ⌋ef .func x)))
    src : ∀ (x : ∣ 𝔽 1 ∣) →
          Agree τ (⌊ m ⌋f .func (mat (cols {γ = γ} R source) .func x))
                        (elim-const τ .at ⌊ m ⌋ .func (ι1-fwd .func x))

open Agrees

fundamental : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) →
              CoreTm t → (mγ : CoreEnv γ) → ∃ₛ (CoreVal v) (Agrees D mγ)
fundamental (⇓-var x) (var .x) mγ = {!!}
fundamental ⇓-unit unit mγ = {!!}
fundamental (⇓-inl D) (inl c) mγ = {!!}
fundamental (⇓-inr D) (inr c) mγ = {!!}
fundamental (⇓-case-l D₁ D₂) (case c c₁ c₂) mγ = {!!}
fundamental (⇓-case-r D₁ D₂) (case c c₁ c₂) mγ = {!!}
fundamental (⇓-pair D₁ D₂) (pair c₁ c₂) mγ = {!!}
fundamental (⇓-fst D) (fst c) mγ = {!!}
fundamental (⇓-snd D) (snd c) mγ = {!!}
fundamental ⇓-lam (lam c) mγ = {!!}
fundamental (⇓-app D₁ D₂ D₃) (app c₁ c₂) mγ = {!!}
