{-# OPTIONS --prop --postfix-projections --safe #-}

-- Control dependence through a closure, operationally and in the interpretation. In
-- app (case y of inl _ → x | inr _ → x) unit, with x the identity closure, the result depends on
-- y's root through the closure's root alone: the case charges the closure's root the elimination
-- weight when it consumes y's root, and the application charges it again when it consumes the
-- closure's root, giving w². Both sides agree because both mark only a closure's root: the
-- operational control positions of a closure (ctrl-of) and the interpretation's arrow constant
-- (ho-model.exp-const) leave the closure's environment, respectively the tuple of results over
-- every argument, unmarked. Had the interpretation written the target's constant into that
-- tuple, application would read it back at the argument for a further w, which no position of
-- the closure carries. Over the counting semiring with weight 3 both give 9; the closure's root
-- and y's payload columns give 3 and 0.
module example.closure-control where

open import Data.Fin using (zero; suc)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ; _,_; proj₁)
open import Data.Rational using (ℚ)
open import Data.Sum using (inj₁)
open import Data.Unit using (tt)
open import Level using (lift; 0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import prop-setoid using (Setoid)
open import categories using (Category)
import indexed-family
import matrix
import semimodule
import semiring-N
import ho-model

open import example.signature ℚ using (Sig)
import example.primitives-over semiring-N.semiring as Dep

open import language-syntax Sig
  using (ctxt; type; _⊢_; zero; succ; var; case; app; unit; lam; _[+]_; _[→]_; emp)
  renaming (_,_ to _▸_)
open import language-operational.evaluation Sig semiring-N.semiring Dep.primitives 3

Γ₀ : ctxt
Γ₀ = emp ▸ (unit [→] unit) ▸ (unit [+] unit)

t₀ : Γ₀ ⊢ unit
t₀ = app (case (var zero) (var (succ (succ zero))) (var (succ (succ zero)))) unit

γ₀ : Env Γ₀
γ₀ = emp · clo emp (var zero) · inl unit

-- The operational side: the derivation and its relation.
open Category (matrix.Mat.cat semiring-N.semiring) using (_⇒_)

Dev : Σ (suc (width-env γ₀) ⇒ 1) λ R → γ₀ , t₀ ⇓ unit [ R ]
Dev = _ , ⇓-app (⇓-case-l (⇓-var zero) (⇓-var (succ (succ zero)))) ⇓-unit (⇓-var zero)

R = proj₁ Dev

-- The result's root against the environment's positions: the closure's root, y's root, y's
-- payload root.
_ : cols {γ = γ₀} R environment zero zero ≡ 3
_ = refl

_ : cols {γ = γ₀} R environment zero (suc zero) ≡ 9
_ = refl

_ : cols {γ = γ₀} R environment zero (suc (suc zero)) ≡ 0
_ = refl

-- The interpretation: the fibre map of the term at the environment's index, applied to the basis
-- vector at each of the same positions.
open semimodule semiring-N.semiring using (Semimodule)

module model = ho-model semiring-N.semiring 3
module interp = model.interp Sig Dep.primitives
open interp using (𝒟⟦_⟧tm; 𝒟⟦_⟧ctxt; 𝒟⟦_⟧ty)
open model.Fam⟨𝒟⟩μ using (idx; fam; fm; idxf; famf)
open prop-setoid._⇒_ using (func)
open indexed-family._⇒f_ using (transf)

arrow unitty : type 0
arrow = unit [→] unit
unitty = unit

idterm : emp ⊢ arrow
idterm = lam (var zero)

-- The closure's index: the identity's denotation.
idfun : Setoid.Carrier (𝒟⟦ arrow ⟧ty (λ ()) .idx)
idfun = 𝒟⟦ idterm ⟧tm .idxf .func (lift tt)

γ-idx : Setoid.Carrier (𝒟⟦ Γ₀ ⟧ctxt .idx)
γ-idx = (lift {0ℓ} {0ℓ} tt , idfun) , inj₁ (lift {0ℓ} {0ℓ} tt)

-- A vector over the environment's fibre: a scalar at the closure's root, zero at its payload,
-- and scalars at y's root and payload root.
vec : ℕ → ℕ → ℕ → Setoid.Carrier (Semimodule.setoid (𝒟⟦ Γ₀ ⟧ctxt .fam .fm γ-idx))
vec a b c =
  (lift {0ℓ} {0ℓ} tt ,
   (a , Semimodule.ε (model.FE._⟶_ (𝒟⟦ unitty ⟧ty (λ ())) (𝒟⟦ unitty ⟧ty (λ ())) .fam .fm idfun))) ,
  (b , λ _ → c)

dep : ℕ → ℕ → ℕ → ℕ
dep a b c = model.SemiMod._⇒_.func (𝒟⟦ t₀ ⟧tm .famf .transf γ-idx) (vec a b c) zero

_ : dep 1 0 0 ≡ 3
_ = refl

_ : dep 0 1 0 ≡ 9
_ = refl

_ : dep 0 0 1 ≡ 0
_ = refl
