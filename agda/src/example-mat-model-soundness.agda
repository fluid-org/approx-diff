{-# OPTIONS --postfix-projections --prop --safe #-}

module example-mat-model-soundness where

open import example-mat-model public
open import indexed-family using (module _⇒f_; module Fam)
open Fam using (fm)
open import prop-setoid using (Setoid)
open import prop using (substP)
open Setoid using (Carrier)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Level using (lift)
open import Data.Unit using (tt)
open import every using (Every; []; _∷_)
open prop-setoid._⇒_ using (func)
open import categories using (HasProducts; HasTerminal)
open import ho-model using (module MatRep)
open import signature using (FPCat; FPC[_,_,_])
open FPCat (FPC[ MatRep.cat , MatRep.terminal , products-mat ]) using (list→product)
open Mat using (_⇒_; _∘_; id; _≈_; ≈-refl; ≈-sym; ≈-trans; ∘-cong; id-left; id-right; assoc)
open import categories using (Category)
open Category Fam⟨𝒞⟩.cat using () renaming (_⇒_ to _⇒f_; _∘_ to _∘f_; id to idf)
open HasProducts products-mat using (prod; p₁; p₂; pair-cong; pair-p₁; pair-p₂; pair-natural; pair-ext; prod-m; pair-compose) renaming (pair to pairM)
open HasTerminal MatRep.terminal using (to-terminal)
open import Data.Fin using (Fin)
import two
open two using (Two; O; I)
import matrix
open import prop-setoid using (IsEquivalence)
open import functor using (Functor)
open Functor using (fmor-cong; fmor-id)
open signature.Algebra Alg using (op-fun; rel-pred)

------------------------------------------------------------------------
-- Soundness: the per-step morphism (carried as Eval's ℛ-index) agrees with the categorical
-- denotation. Because Eval already encodes the morphism, ⌊_⌋ is no longer needed — we just
-- compare ℛ against ⟦M⟧tm.famf.transf γ.

open _⇒f_ using (transf)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; subst; subst₂; sym)
open import Relation.Binary.PropositionalEquality.Properties using (cong-∘; trans-reflʳ; subst-sym-subst; sym-cong)
open import Axiom.UniquenessOfIdentityProofs.WithK using (uip)
open import Data.Nat.Properties using (+-cancelˡ-≡; +-cancelʳ-≡)

-- Operational and categorical value/env types coincide propositionally (definitionally for
-- ground types; structural induction extends this to abstract τ/Γ).
Val-≡ : ∀ τ → Val τ ≡ Carrier (⟦ τ ⟧ty .idx)
Val-≡ unit         = refl
Val-≡ (base number) = refl
Val-≡ (base label)  = refl
Val-≡ (τ₁ [×] τ₂)  = cong₂ _×_ (Val-≡ τ₁) (Val-≡ τ₂)
Val-≡ (τ₁ [+] τ₂)  = cong₂ _⊎_ (Val-≡ τ₁) (Val-≡ τ₂)
Val-≡ (list τ)     = cong List (Val-≡ τ)

Env-≡ : ∀ Γ → Env Γ ≡ Carrier (⟦ Γ ⟧ctxt .idx)
Env-≡ emp     = refl
Env-≡ (Γ · τ) = cong₂ _×_ (Env-≡ Γ) (Val-≡ τ)

-- Structural denotational interpretation at the value level: embed an operational Val into the
-- categorical Carrier. Definitional identity at each type/ctxt shape.
⟦_⟧val : ∀ {τ} → Val τ → Carrier (⟦ τ ⟧ty .idx)
⟦_⟧env : ∀ {Γ} → Env Γ → Carrier (⟦ Γ ⟧ctxt .idx)

⟦_⟧val {unit}        v        = v
⟦_⟧val {base number} v        = v
⟦_⟧val {base label}  v        = v
⟦_⟧val {τ₁ [×] τ₂}   (v , u)  = ⟦_⟧val {τ₁} v , ⟦_⟧val {τ₂} u
⟦_⟧val {τ₁ [+] τ₂}   (inj₁ v) = inj₁ (⟦_⟧val {τ₁} v)
⟦_⟧val {τ₁ [+] τ₂}   (inj₂ v) = inj₂ (⟦_⟧val {τ₂} v)
⟦_⟧val {list τ}      []       = []
⟦_⟧val {list τ}      (v ∷ vs) = ⟦_⟧val {τ} v ∷ ⟦_⟧val {list τ} vs

⟦_⟧env {emp} γ          = γ
⟦_⟧env {Γ · τ} (γ , v)  = ⟦_⟧env {Γ} γ , ⟦_⟧val {τ} v

⟦_⟧val-Bool : (v : Val (unit [+] unit)) → ⟦_⟧val {unit [+] unit} v ≡ v
⟦_⟧val-Bool (inj₁ _) = refl
⟦_⟧val-Bool (inj₂ _) = refl

⟦_⟧bases-vals : ∀ {σs} → Bases-input σs → Carrier (⟦ σs ⟧bases-list .idx)
⟦_⟧bases-vals {[]}     _        = lift tt
⟦_⟧bases-vals {σ ∷ σs} (v , vs) = ⟦_⟧val {base σ} v , ⟦_⟧bases-vals {σs} vs

width-≡       : ∀ τ (v : Val τ) → width τ v ≡ ⟦ τ ⟧ty .fam .fm (⟦_⟧val {τ} v)
width-ctxt-≡  : ∀ Γ (γ : Env Γ) → width-ctxt Γ γ ≡ ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env {Γ} γ)

width-≡ unit _                = refl
width-≡ (base number) _       = refl
width-≡ (base label) _        = refl
width-≡ (τ₁ [×] τ₂) (v , u)   = cong₂ _+_ (width-≡ τ₁ v) (width-≡ τ₂ u)
width-≡ (τ₁ [+] τ₂) (inj₁ v)  = width-≡ τ₁ v
width-≡ (τ₁ [+] τ₂) (inj₂ v)  = width-≡ τ₂ v
width-≡ (list τ)    []        = refl
width-≡ (list τ)    (v ∷ vs)  = cong₂ _+_ (width-≡ τ v) (width-≡ (list τ) vs)

width-ctxt-≡ emp _           = refl
width-ctxt-≡ (Γ · τ) (γ , v) = cong₂ _+_ (width-ctxt-≡ Γ γ) (width-≡ τ v)

subst₂-∘ : ∀ {m m' k k' n n'} (s : m ≡ m') (t : k ≡ k') (u : n ≡ n') (f : k ⇒ n) (g : m ⇒ k) →
           subst₂ _⇒_ s u (_∘_ {x = m} {y = k} {z = n} f g)
           ≡ _∘_ {x = m'} {y = k'} {z = n'} (subst₂ _⇒_ t u f) (subst₂ _⇒_ s t g)
subst₂-∘ refl refl refl f g = refl

-- subst₂ commutes through (p₁ ∘ -) by rebasing the inner morphism along the +-bridge.
subst₂-p₁-∘ : ∀ {m m' n n' k k'} (m≡m' : m ≡ m') (n≡n' : n ≡ n') (n+k≡n'+k' : n + k ≡ n' + k') (ℛ : m ⇒ (n + k)) →
              _≈_ {x = m'} {y = n'}
                  (subst₂ _⇒_ m≡m' n≡n' (_∘_ {x = m} {y = n + k} {z = n} (p₁ {n} {k}) ℛ))
                  (_∘_ {x = m'} {y = n' + k'} {z = n'} (p₁ {n'} {k'}) (subst₂ _⇒_ m≡m' n+k≡n'+k' ℛ))
subst₂-p₁-∘ {m} {n = n} refl refl n+k≡n'+k' ℛ with +-cancelˡ-≡ n _ _ n+k≡n'+k'
... | refl with uip n+k≡n'+k' refl
... | refl = ≈-refl {x = m} {y = n}

subst₂-p₂-∘ : ∀ {m m' n n' k k'} (m≡m' : m ≡ m') (n≡n' : n ≡ n') (k+n≡k'+n' : k + n ≡ k' + n') (ℛ : m ⇒ (k + n)) →
              _≈_ {x = m'} {y = n'}
                  (subst₂ _⇒_ m≡m' n≡n' (_∘_ {x = m} {y = k + n} {z = n} (p₂ {k} {n}) ℛ))
                  (_∘_ {x = m'} {y = k' + n'} {z = n'} (p₂ {k'} {n'}) (subst₂ _⇒_ m≡m' k+n≡k'+n' ℛ))
subst₂-p₂-∘ {m} {n = n} {k = k} refl refl k+n≡k'+n' ℛ with +-cancelʳ-≡ _ k _ k+n≡k'+n'
... | refl with uip k+n≡k'+n' refl
... | refl = ≈-refl {x = m} {y = n}

-- subst₂ commutes through pairM: rebasing the pair equals pairing the rebased components.
subst₂-pair : ∀ {m m' n n' k k'} (m≡m' : m ≡ m') (n≡n' : n ≡ n') (k≡k' : k ≡ k')
              (n+k≡n'+k' : n + k ≡ n' + k') (f : m ⇒ n) (g : m ⇒ k) →
              _≈_ {x = m'} {y = n' + k'}
                  (subst₂ _⇒_ m≡m' n+k≡n'+k' (pairM {x = m} {y = n} {z = k} f g))
                  (pairM {x = m'} {y = n'} {z = k'} (subst₂ _⇒_ m≡m' n≡n' f) (subst₂ _⇒_ m≡m' k≡k' g))
subst₂-pair {m} {n = n} {k = k} refl refl refl n+k≡n'+k' f g with uip n+k≡n'+k' refl
... | refl = ≈-refl {x = m} {y = n + k}

-- subst₂ over an identity morphism gives the identity at the target type.
subst₂-id : ∀ {m₁ m₂} (m₁≡m₂ : m₁ ≡ m₂) → _≈_ {x = m₂} {y = m₂} (subst₂ _⇒_ m₁≡m₂ m₁≡m₂ (id m₁)) (id m₂)
subst₂-id {m₁} refl = ≈-refl {x = m₁} {y = m₁}

-- subst₂ over `trans n₁≡n₂ n₂≡n₃` (codomain) factors as nested subst.
subst₂-trans-cod : ∀ {m₁ m₂ n₁ n₂ n₃} (m₁≡m₂ : m₁ ≡ m₂) (n₁≡n₂ : n₁ ≡ n₂) (n₂≡n₃ : n₂ ≡ n₃) (f : m₁ ⇒ n₁) →
                   subst₂ _⇒_ m₁≡m₂ (trans n₁≡n₂ n₂≡n₃) f ≡ subst (λ X → m₂ ⇒ X) n₂≡n₃ (subst₂ _⇒_ m₁≡m₂ n₁≡n₂ f)
subst₂-trans-cod m₁≡m₂ refl refl f = refl

-- `≈` lifts through subst on the codomain.
subst-≈-cong : ∀ {m n₁ n₂} (n₁≡n₂ : n₁ ≡ n₂) {f g : m ⇒ n₁} → _≈_ {x = m} {y = n₁} f g →
               _≈_ {x = m} {y = n₂} (subst (λ X → m ⇒ X) n₁≡n₂ f) (subst (λ X → m ⇒ X) n₁≡n₂ g)
subst-≈-cong refl eq = eq

-- `≈` lifts through subst₂ on both source and codomain.
subst₂-≈-cong : ∀ {m₁ m₂ n₁ n₂} (p : m₁ ≡ m₂) (q : n₁ ≡ n₂) {f g : m₁ ⇒ n₁} →
                _≈_ {x = m₁} {y = n₁} f g →
                _≈_ {x = m₂} {y = n₂} (subst₂ _⇒_ p q f) (subst₂ _⇒_ p q g)
subst₂-≈-cong refl refl eq = eq

-- Factor subst₂ over (trans p₁ p') (trans q₁ q') into nested subst₂'s.
subst₂-trans-fact : ∀ {m₁ m₂ m₃ n₁ n₂ n₃} (p₁ : m₁ ≡ m₂) (p' : m₂ ≡ m₃) (q₁ : n₁ ≡ n₂) (q' : n₂ ≡ n₃)
                    (f : m₁ ⇒ n₁) → subst₂ _⇒_ (trans p₁ p') (trans q₁ q') f ≡ subst₂ _⇒_ p' q' (subst₂ _⇒_ p₁ q₁ f)
subst₂-trans-fact refl p' refl q' f = refl

-- projection rebased through propositionally-equal width pairs equals projection at the new widths.
p₁-subst₂ : ∀ {n n' k k'} (n+k≡n'+k' : n + k ≡ n' + k') (n≡n' : n ≡ n') →
            _≈_ {x = n' + k'} {y = n'} (subst₂ _⇒_ n+k≡n'+k' n≡n' (p₁ {n} {k})) (p₁ {n'} {k'})
p₁-subst₂ {n} {k = k} n+k≡n'+k' refl with +-cancelˡ-≡ n _ _ n+k≡n'+k'
... | refl with uip n+k≡n'+k' refl
... | refl = ≈-refl {x = n + k} {y = n}

p₂-subst₂ : ∀ {n n' k k'} (k+n≡k'+n' : k + n ≡ k' + n') (n≡n' : n ≡ n') →
            _≈_ {x = k' + n'} {y = n'} (subst₂ _⇒_ k+n≡k'+n' n≡n' (p₂ {k} {n})) (p₂ {k'} {n'})
p₂-subst₂ {n} {k = k} k+n≡k'+n' refl with +-cancelʳ-≡ _ k _ k+n≡k'+n'
... | refl with uip k+n≡k'+n' refl
... | refl = ≈-refl {x = k + n} {y = n}

-- Heterogeneous equality of Mat morphisms whose source/target are propositionally equal.
_≈H_⟨_,_⟩ : ∀ {m₁ n₁ m₂ n₂} → m₁ ⇒ n₁ → m₂ ⇒ n₂ → m₁ ≡ m₂ → n₁ ≡ n₂ → Prop _
_≈H_⟨_,_⟩ {m₁} {n₁} {m₂} {n₂} f g eq₁ eq₂ =
  _≈_ {x = m₂} {y = n₂} (subst₂ _⇒_ {m₁} {m₂} {n₁} {n₂} eq₁ eq₂ f) g

-- Rewrite the codomain bridge of an ≈H proof along a propositional equality between bridges.
≈H-bridge : ∀ {m₁ n₁ m₂ n₂} {f : m₁ ⇒ n₁} {g : m₂ ⇒ n₂} {m₁≡m₂ : m₁ ≡ m₂} {n₁≡n₂ n₁≡n₂' : n₁ ≡ n₂} →
            n₁≡n₂ ≡ n₁≡n₂' → f ≈H g ⟨ m₁≡m₂ , n₁≡n₂ ⟩ → f ≈H g ⟨ m₁≡m₂ , n₁≡n₂' ⟩
≈H-bridge {m₁} {n₁} {m₂} {n₂} {f} {g} {m₁≡m₂} eq H =
  substP (λ b → _≈_ {x = m₂} {y = n₂} (subst₂ _⇒_ m₁≡m₂ b f) g) eq H

≈H-trans : ∀ {m₁ n₁ m₂ n₂ n₃} {f : m₁ ⇒ n₁} {g : m₂ ⇒ n₂} {h : m₂ ⇒ n₃}
           {m₁≡m₂ : m₁ ≡ m₂} {n₁≡n₂ : n₁ ≡ n₂} {n₂≡n₃ : n₂ ≡ n₃} →
           f ≈H g ⟨ m₁≡m₂ , n₁≡n₂ ⟩ → g ≈H h ⟨ refl {x = m₂} , n₂≡n₃ ⟩ → f ≈H h ⟨ m₁≡m₂ , trans n₁≡n₂ n₂≡n₃ ⟩
≈H-trans {m₂ = m₂} {n₃ = n₃} {m₁≡m₂ = m₁≡m₂} {n₁≡n₂ = n₁≡n₂} {n₂≡n₃ = n₂≡n₃} P Q
  rewrite m₁≡m₂ | n₁≡n₂ | n₂≡n₃ = ≈-trans {x = m₂} {y = n₃} P Q

-- Soundness shortcut for clauses whose codomain has width 0: by terminal-uniqueness in MatRep,
-- modulo the width-ctxt coercion and a propositional eq from the categorical codomain.
into-zero-≈H : ∀ {Γ n} (γ : Env Γ) (eq : n ≡ 0)
               (f : (width-ctxt Γ γ) ⇒ 0) (g : (⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env {Γ} γ)) ⇒ n) →
               _≈H_⟨_,_⟩ {n₁ = 0} {n₂ = n} f g (width-ctxt-≡ Γ γ) (sym eq)
into-zero-≈H {Γ} γ refl f g rewrite width-ctxt-≡ Γ γ =
  HasTerminal.to-terminal-unique MatRep.terminal {x = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env {Γ} γ)} f g

-- Generalisation of `into-zero-≈H`: both sides go to "morally 0" types, given propositional
-- eqs to 0 for each codomain. Useful when the operational side's codomain doesn't def-reduce
-- to 0 (e.g. `width (unit [+] unit) v` for an opaque `v`).
into-via-zero-≈H : ∀ {Γ n n'} (γ : Env Γ) (eq-n : n ≡ 0) (eq-n' : n' ≡ 0)
                   (f : (width-ctxt Γ γ) ⇒ n) (g : (⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env {Γ} γ)) ⇒ n') →
                   _≈H_⟨_,_⟩ {n₁ = n} {n₂ = n'} f g (width-ctxt-≡ Γ γ) (trans eq-n (sym eq-n'))
into-via-zero-≈H {Γ} γ refl refl f g rewrite width-ctxt-≡ Γ γ =
  HasTerminal.to-terminal-unique MatRep.terminal {x = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env {Γ} γ)} f g

-- Categorical-side value: extract from ⟦M⟧tm.idxf, after coercing the operational env to a
-- categorical Carrier via ⟦_⟧env.
val : ∀ {Γ τ} (M : Γ ⊢ τ) (γ : Env Γ) → Carrier (⟦ τ ⟧ty .idx)
val {Γ} M γ = ⟦ M ⟧tm .idxf .func (⟦_⟧env {Γ} γ)

val-bases : ∀ {Γ σs} (Ms : Every (λ σ → Γ ⊢ base σ) σs) (γ : Env Γ) → Carrier (⟦ σs ⟧bases-list .idx)
val-bases {Γ} Ms γ = ⟦ Ms ⟧bases .idxf .func (⟦_⟧env {Γ} γ)

fold-iter-val : ∀ {Γ τ₁ τ₂} (M₂ : (Γ · τ₁) · τ₂ ⊢ τ₂) (γ : Env Γ) (v-nil : Val τ₂)
                (us : Val (list τ₁)) → Carrier (⟦ τ₂ ⟧ty .idx)
fold-iter-val {τ₂ = τ₂} M₂ γ v-nil []       = ⟦_⟧val {τ₂} v-nil
fold-iter-val {τ₁ = τ₁} M₂ γ v-nil (u ∷ us) =
  ⟦ M₂ ⟧tm .idxf .func ((⟦_⟧env γ , ⟦_⟧val {τ₁} u) , fold-iter-val M₂ γ v-nil us)

fold-eq : ∀ {Γ τ₁ τ₂} (seed : ⟦ Γ ⟧ctxt ⇒f ⟦ τ₂ ⟧ty) (M₂ : (Γ · τ₁) · τ₂ ⊢ τ₂) (γ : Env Γ)
          (v-nil : Val τ₂) (seed-eq : ⟦_⟧val {τ₂} v-nil ≡ seed .idxf .func (⟦_⟧env γ))
          (ys : Val (list τ₁)) →
          fold-iter-val M₂ γ v-nil ys ≡ ⟦fold⟧ seed ⟦ M₂ ⟧tm .idxf .func (⟦_⟧env γ , ⟦_⟧val {list τ₁} ys)
fold-eq seed M₂ γ v-nil seed-eq [] = seed-eq
fold-eq {τ₁ = τ₁} seed M₂ γ v-nil seed-eq (y ∷ ys) =
  cong (λ a → ⟦ M₂ ⟧tm .idxf .func ((⟦_⟧env γ , ⟦_⟧val {τ₁} y) , a))
       (fold-eq seed M₂ γ v-nil seed-eq ys)

val-det       : ∀ {Γ τ} {M : Γ ⊢ τ} {γ : Env Γ} {v ℛ} → γ , M ⇓ v , ℛ → ⟦_⟧val {τ} v ≡ val M γ
val-det-bases : ∀ {Γ σs} {Ms : Every (λ σ → Γ ⊢ base σ) σs} {γ : Env Γ} {vs ℛ} →
                EvalBases γ Ms vs ℛ → ⟦_⟧bases-vals {σs} vs ≡ val-bases Ms γ
val-det-iters : ∀ {Γ τ₁ τ₂} {M₁ : Γ ⊢ τ₂} {M₂ : (Γ · τ₁) · τ₂ ⊢ τ₂}
                {γ : Env Γ} {v-nil ℛ ys final 𝒮 ℛ₂} → EvalIters M₁ M₂ γ v-nil ℛ ys final 𝒮 ℛ₂ →
                ⟦_⟧val {τ₂} final ≡ fold-iter-val M₂ γ v-nil ys

val-det (eval-var zero     (γ , v)) = refl
val-det (eval-var (succ x) (γ , v)) = val-det (eval-var x γ)
val-det eval-unit            = refl
val-det eval-nil             = refl
val-det (eval-pair E F)      = cong₂ _,_ (val-det E) (val-det F)
val-det (eval-fst E)         = cong proj₁ (val-det E)
val-det (eval-snd E)         = cong proj₂ (val-det E)
val-det (eval-inl E)         = cong inj₁ (val-det E)
val-det (eval-inr E)         = cong inj₂ (val-det E)
val-det {γ = γ} (eval-case-l {N₁ = N₁} {N₂ = N₂} E F) =
  trans (val-det F)
        (cong (λ z → [ ⟦ N₁ ⟧tm , ⟦ N₂ ⟧tm ] .idxf .func (⟦_⟧env γ , z)) (val-det E))
val-det {γ = γ} (eval-case-r {N₁ = N₁} {N₂ = N₂} E F) =
  trans (val-det F)
        (cong (λ z → [ ⟦ N₁ ⟧tm , ⟦ N₂ ⟧tm ] .idxf .func (⟦_⟧env γ , z)) (val-det E))
val-det (eval-cons E F)      = cong₂ _∷_ (val-det E) (val-det F)
val-det (eval-bop op-zero E) = cong (⟦op⟧ op-zero .idxf .func) (val-det-bases E)
val-det (eval-bop add     E) = cong (⟦op⟧ add     .idxf .func) (val-det-bases E)
val-det (eval-bop mult    E) = cong (⟦op⟧ mult    .idxf .func) (val-det-bases E)
val-det (eval-bop (lbl l) E) = cong (⟦op⟧ (lbl l) .idxf .func) (val-det-bases E)
val-det (eval-brel {vs = vs} equal-label E) =
  trans (⟦_⟧val-Bool (rel-pred equal-label vs))
        (cong (⟦rel⟧ equal-label .idxf .func) (val-det-bases E))
val-det {γ = γ} (eval-fold {M₁ = M₁} {M₂ = M₂} {v-nil = v-nil} {ys = ys} E₁ E₂ E₃) =
  trans (val-det-iters E₃)
        (trans (fold-eq ⟦ M₁ ⟧tm M₂ γ v-nil (val-det E₁) ys)
               (cong (λ z → ⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .idxf .func (⟦_⟧env γ , z)) (val-det E₂)))

val-det-bases []-bases = refl
val-det-bases (E ∷-bases Es) = cong₂ _,_ (val-det E) (val-det-bases Es)

val-det-iters nil-iter = refl
val-det-iters {τ₁ = τ₁} {M₂ = M₂} {γ = γ} (cons-iter {y = y} _ rec F) =
  trans (val-det F) (cong (λ a → ⟦ M₂ ⟧tm .idxf .func ((⟦_⟧env γ , ⟦_⟧val {τ₁} y) , a)) (val-det-iters rec))

soundness-var : ∀ {Γ τ} (x : Γ ∋ τ) (γ : Env Γ) →
                proj-var x γ ≈H ⟦ x ⟧var .famf .transf (⟦_⟧env γ)
                  ⟨ width-ctxt-≡ Γ γ
                  , trans (width-≡ τ (lookup x γ)) (cong (⟦ τ ⟧ty .fam .fm) (val-det (eval-var x γ)))
                  ⟩
soundness-var {Γ · τ} {.τ} zero (γ , v) =
  ≈H-bridge {f = proj-var {Γ · τ} {τ} zero (γ , v)}
            {g = ⟦ zero {Γ} {τ} ⟧var .famf .transf (⟦_⟧env {Γ · τ} (γ , v))}
            {m₁≡m₂ = cong₂ _+_ (width-ctxt-≡ Γ γ) (width-≡ τ v)}
            {n₁≡n₂ = width-≡ τ v}
            (sym (trans-reflʳ (width-≡ τ v)))
            (p₂-subst₂ (cong₂ _+_ (width-ctxt-≡ Γ γ) (width-≡ τ v)) (width-≡ τ v))
soundness-var {Γ · τ'} {τ} (succ x) (γ , v) =
  substP (λ X → _≈_ {x = m} {y = n} X (⟦ succ {Γ} {τ} {τ'} x ⟧var .famf .transf (⟦_⟧env {Γ · τ'} (γ , v))))
         (sym (subst₂-∘ (cong₂ _+_ (width-ctxt-≡ Γ γ) (width-≡ τ' v))
                        (width-ctxt-≡ Γ γ)
                        (trans (width-≡ τ (lookup x γ)) (cong (⟦ τ ⟧ty .fam .fm) (val-det (eval-var x γ))))
                        (proj-var x γ) (p₁ {width-ctxt Γ γ} {width τ' v})))
         (≈-trans {x = m} {y = n}
           (∘-cong {x = m} {y = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)} {z = n}
                   (soundness-var x γ)
                   (p₁-subst₂ (cong₂ _+_ (width-ctxt-≡ Γ γ) (width-≡ τ' v)) (width-ctxt-≡ Γ γ)))
           (≈-sym {x = m} {y = n} (id-left {x = m} {y = n})))
  where
    m = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ) + ⟦ τ' ⟧ty .fam .fm (⟦_⟧val {τ'} v)
    n = ⟦ τ ⟧ty .fam .fm (⟦ x ⟧var .idxf .func (⟦_⟧env γ))

bases-fm-≡ : ∀ σs (vs : Carrier (⟦ σs ⟧bases-list .idx)) →
             ⟦ σs ⟧bases-list .fam .fm vs ≡ list→product ⟦sort⟧-𝒞 σs
bases-fm-≡ [] _              = refl
bases-fm-≡ (σ ∷ σs) (_ , vs) = cong (⟦sort⟧-𝒞 σ +_) (bases-fm-≡ σs vs)

unit-mor∘to-terminal-rebase : ∀ {Γ} (γ : Env Γ) →
  _≈_ {x = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)} {y = 1}
          (subst₂ _⇒_ (width-ctxt-≡ Γ γ) (refl {x = 1})
                  (_∘_ {x = width-ctxt Γ γ} {y = 0} {z = 1} unit-mor (to-terminal {width-ctxt Γ γ})))
          (_∘_ {x = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)} {y = 0} {z = 1}
                   unit-mor (to-terminal {⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)}))
unit-mor∘to-terminal-rebase {Γ} γ =
  substP (λ X → _≈_ {x = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)} {y = 1} X
                        (_∘_ {x = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)} {y = 0} {z = 1}
                                 unit-mor (to-terminal {⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)})))
         (sym (subst₂-∘ (width-ctxt-≡ Γ γ) (refl {x = 0}) (refl {x = 1}) unit-mor (to-terminal {width-ctxt Γ γ})))
         (∘-cong {x = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)} {y = 0} {z = 1}
                     (≈-refl {x = 0} {y = 1})
                     (HasTerminal.to-terminal-unique MatRep.terminal
                       {x = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)}
                       (subst₂ _⇒_ (width-ctxt-≡ Γ γ) (refl {x = 0}) (to-terminal {width-ctxt Γ γ}))
                       (to-terminal {⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)})))

binary-famf-transf-eq : ∀ {X n}
                        (y : Carrier ((Fam⟨𝒞⟩.simple[ X , n ] ⟦×⟧ (Fam⟨𝒞⟩.simple[ X , n ] ⟦×⟧ ⟦unit⟧)) .idx)) →
                        _≈_ {x = n + (n + 0)} {y = n + n}
                            (binary {X = X} {G = n} .famf .transf y)
                            (pairM {x = n + (n + 0)} {y = n} {z = n}
                                   (p₁ {n} {n + 0})
                                   (_∘_ {x = n + (n + 0)} {y = n + 0} {z = n} (p₁ {n} {0}) (p₂ {n} {n + 0})))
binary-famf-transf-eq {n = n} y =
  ≈-trans {x = n + (n + 0)} {y = n + n}
    (id-left {x = n + (n + 0)} {y = n + n})
    (≈-trans {x = n + (n + 0)} {y = n + n}
      (id-left {x = n + (n + 0)} {y = n + n})
      (pair-cong {x = n + (n + 0)} {y = n} {z = n}
                 (≈-refl {x = n + (n + 0)} {y = n})
                 (id-left {x = n + (n + 0)} {y = n})))

private
  module ML = matrix.Mat two.semiring

  p₁-deg-matrix : ML.p₁ {1} {0} ML.≈ₘ ML.I {1}
  p₁-deg-matrix Fin.zero Fin.zero = two.Two-setoid .Setoid.isEquivalence .IsEquivalence.refl {x = I}

p₁-degenerate : _≈_ {x = 1 + 0} {y = 1} (p₁ {1} {0}) (id 1)
p₁-degenerate =
  ≈-trans {x = 1 + 0} {y = 1}
    (MatRep.F .fmor-cong {x = 1} {y = 1 + 0} p₁-deg-matrix) (MatRep.F .fmor-id {x = 1})

binary-≈-id : ∀ {X} (y : Carrier ((Fam⟨𝒞⟩.simple[ X , 1 ] ⟦×⟧ (Fam⟨𝒞⟩.simple[ X , 1 ] ⟦×⟧ ⟦unit⟧)) .idx)) →
              _≈_ {x = 1 + (1 + 0)} {y = 1 + 1} (binary {X = X} {G = 1} .famf .transf y) (id (1 + 1))
binary-≈-id {X = X} y =
  ≈-trans {x = 1 + (1 + 0)} {y = 1 + 1}
    (binary-famf-transf-eq {X = X} {n = 1} y)
    (≈-trans {x = 1 + (1 + 0)} {y = 1 + 1}
      (pair-cong {x = 1 + (1 + 0)} {y = 1} {z = 1}
        (≈-refl {x = 1 + (1 + 0)} {y = 1})
        (≈-trans {x = 1 + (1 + 0)} {y = 1}
          (∘-cong {x = 1 + (1 + 0)} {y = 1 + 0} {z = 1} p₁-degenerate (≈-refl {x = 1 + (1 + 0)} {y = 1 + 0}))
          (id-left {x = 1 + (1 + 0)} {y = 1})))
      (≈-sym {x = 1 + (1 + 0)} {y = 1 + 1}
        (≈-trans {x = 1 + (1 + 0)} {y = 1 + 1}
          (≈-sym {x = 1 + (1 + 0)} {y = 1 + 1} (pair-ext {x = 1 + (1 + 0)} {y = 1} {z = 1} (id (1 + 1))))
          (pair-cong {x = 1 + (1 + 0)} {y = 1} {z = 1}
                     (id-right {x = 1 + (1 + 0)} {y = 1}) (id-right {x = 1 + (1 + 0)} {y = 1})))))

binary-pair : ∀ {X m n} (y : Carrier ((Fam⟨𝒞⟩.simple[ X , n ] ⟦×⟧ (Fam⟨𝒞⟩.simple[ X , n ] ⟦×⟧ ⟦unit⟧)) .idx))
              (ℛ₁ ℛ₂ : m ⇒ n) (ω : m ⇒ 0) →
              _≈_ {x = m} {y = n + n}
                  (_∘_ {x = m} {y = n + (n + 0)} {z = n + n}
                       (binary {X = X} {G = n} .famf .transf y)
                       (pairM {x = m} {y = n} {z = n + 0} ℛ₁ (pairM {x = m} {y = n} {z = 0} ℛ₂ ω)))
                  (pairM {x = m} {y = n} {z = n} ℛ₁ ℛ₂)
binary-pair {X = X} {m = m} {n = n} y ℛ₁ ℛ₂ ω =
  ≈-trans {x = m} {y = n + n}
    (∘-cong {x = m} {y = n + (n + 0)} {z = n + n}
            (binary-famf-transf-eq {X = X} {n = n} y)
            (≈-refl {x = m} {y = n + (n + 0)}))
    (≈-trans {x = m} {y = n + n}
       (pair-natural {w = m} {x = n + (n + 0)} {y = n} {z = n} _ _ _)
       (pair-cong {x = m} {y = n} {z = n}
          (pair-p₁ {x = m} {y = n} {z = n + 0} ℛ₁ (pairM {x = m} {y = n} {z = 0} ℛ₂ ω))
          (≈-trans {x = m} {y = n}
             (assoc {w = m} {x = n + (n + 0)} {y = n + 0} {z = n} _ _ _)
             (≈-trans {x = m} {y = n}
               (∘-cong {x = m} {y = n + 0} {z = n}
                  (≈-refl {x = n + 0} {y = n})
                  (pair-p₂ {x = m} {y = n} {z = n + 0} ℛ₁ (pairM {x = m} {y = n} {z = 0} ℛ₂ ω)))
               (pair-p₁ {x = m} {y = n} {z = 0} ℛ₂ ω)))))

soundness-bases : ∀ {Γ σs} {Ms : Every (λ σ → Γ ⊢ base σ) σs} {γ : Env Γ} {vs ℛ} →
                  EvalBases γ Ms vs ℛ →
                  ℛ ≈H ⟦ Ms ⟧bases .famf .transf (⟦_⟧env γ)
                    ⟨ width-ctxt-≡ Γ γ , sym (bases-fm-≡ σs (⟦ Ms ⟧bases .idxf .func (⟦_⟧env γ))) ⟩

soundness-iters : ∀ {Γ τ₁ τ₂} {M₁ : Γ ⊢ τ₂} {M₂ : (Γ · τ₁) · τ₂ ⊢ τ₂} {γ : Env Γ}
                  {v-nil ys final ℛ 𝒮 ℛ₂}
                  (E₁ : γ , M₁ ⇓ v-nil , ℛ)
                  (its : EvalIters M₁ M₂ γ v-nil ℛ ys final 𝒮 ℛ₂) →
                  _≈H_⟨_,_⟩
                    {m₁ = width-ctxt Γ γ}
                    {n₁ = width τ₂ final}
                    {m₂ = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)}
                    {n₂ = ⟦ τ₂ ⟧ty .fam .fm
                            (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .idxf .func
                                   (⟦_⟧env γ , ⟦_⟧val {list τ₁} ys))}
                    ℛ₂
                    (_∘_ {x = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)}
                         {y = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ) + ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys)}
                         {z = ⟦ τ₂ ⟧ty .fam .fm
                                (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .idxf .func
                                       (⟦_⟧env γ , ⟦_⟧val {list τ₁} ys))}
                         (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .famf .transf
                                 (⟦_⟧env γ , ⟦_⟧val {list τ₁} ys))
                         (pairM {x = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)}
                                {y = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)}
                                {z = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys)}
                                (id (⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)))
                                (subst₂ _⇒_ (width-ctxt-≡ Γ γ) (width-≡ (list τ₁) ys) 𝒮)))
                    (width-ctxt-≡ Γ γ)
                    (trans (width-≡ τ₂ final)
                           (cong (⟦ τ₂ ⟧ty .fam .fm)
                                 (trans (val-det-iters its)
                                        (fold-eq ⟦ M₁ ⟧tm M₂ γ v-nil (val-det E₁) ys))))

soundness-bop : ∀ {Γ is o} {γ : Env Γ} (ω : op is o)
                {Ms : Every (λ σ → Γ ⊢ base σ) is} {vs ℛ_E}
                (E : EvalBases γ Ms vs ℛ_E) →
                _∘_ {x = width-ctxt Γ γ} {y = list→product ⟦sort⟧-𝒞 is} {z = ⟦sort⟧-𝒞 o} (op-ℛ ω) ℛ_E
                  ≈H ⟦ bop ω Ms ⟧tm .famf .transf (⟦_⟧env γ)
                  ⟨ width-ctxt-≡ Γ γ
                  , trans (width-≡ (base o) (op-fun ω vs)) (cong (⟦ base o ⟧ty .fam .fm) (val-det (eval-bop ω E)))
                  ⟩

soundness-bop-numeric : ∀ {Γ γ}
                        {Ms : Every (λ σ → Γ ⊢ base σ) (number ∷ number ∷ [])}
                        {vs ℛ_E}
                        (ω : op (number ∷ number ∷ []) number)
                        (E : EvalBases γ Ms vs ℛ_E)
                        (op-eq : _≈_ {x = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)} {y = 1}
                                     (_∘_ {x = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)} {y = 1 + (1 + 0)} {z = 1}
                                          (_∘_ {x = 1 + (1 + 0)} {y = 1} {z = 1}
                                               (id 1)
                                               (_∘_ {x = 1 + (1 + 0)} {y = 1 + 1} {z = 1}
                                                    (op-ℛ ω)
                                                    (binary {X = ⟦ base number ⟧ty .idx} {G = 1} .famf .transf
                                                            (⟦ Ms ⟧bases .idxf .func (⟦_⟧env γ)))))
                                          (⟦ Ms ⟧bases .famf .transf (⟦_⟧env γ)))
                                     (⟦ bop ω Ms ⟧tm .famf .transf (⟦_⟧env γ))) →
                        _∘_ {x = width-ctxt Γ γ} {y = 1 + (1 + 0)} {z = 1} (op-ℛ ω) ℛ_E
                        ≈H ⟦ bop ω Ms ⟧tm .famf .transf (⟦_⟧env γ)
                        ⟨ width-ctxt-≡ Γ γ
                        , trans (width-≡ (base number) (op-fun ω vs))
                                (cong (⟦ base number ⟧ty .fam .fm) (val-det (eval-bop ω E)))
                        ⟩

soundness   : ∀ {Γ τ} {M : Γ ⊢ τ} {γ : Env Γ} {v ℛ} (E : γ , M ⇓ v , ℛ) →
              ℛ ≈H ⟦ M ⟧tm .famf .transf (⟦_⟧env γ)
                ⟨ width-ctxt-≡ Γ γ , trans (width-≡ τ v) (cong (⟦ τ ⟧ty .fam .fm) (val-det E)) ⟩

soundness-case-l : ∀ {Γ τ₁ τ₂ τ} {M : Γ ⊢ τ₁ [+] τ₂} {N₁ : Γ · τ₁ ⊢ τ} {N₂ : Γ · τ₂ ⊢ τ}
                   {γ : Env Γ} {v u ℛ 𝒮}
                   (E : γ , M ⇓ inj₁ v , ℛ)
                   (F : (γ , v) , N₁ ⇓ u , 𝒮) →
                   _≈H_⟨_,_⟩
                     {m₁ = width-ctxt Γ γ}
                     {n₁ = width τ u}
                     {m₂ = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)}
                     {n₂ = ⟦ τ ⟧ty .fam .fm
                             (⟦ case M N₁ N₂ ⟧tm .idxf .func (⟦_⟧env γ))}
                     (_∘_ {x = width-ctxt Γ γ} {y = width-ctxt Γ γ + width τ₁ v} {z = width τ u}
                          𝒮 (pairM {x = width-ctxt Γ γ} {y = width-ctxt Γ γ} {z = width τ₁ v}
                                   (id (width-ctxt Γ γ)) ℛ))
                     (⟦ case M N₁ N₂ ⟧tm .famf .transf (⟦_⟧env γ))
                     (width-ctxt-≡ Γ γ)
                     (trans (width-≡ τ u)
                            (cong (⟦ τ ⟧ty .fam .fm)
                                  (trans (val-det F)
                                         (cong (λ z → [ ⟦ N₁ ⟧tm , ⟦ N₂ ⟧tm ] .idxf .func (⟦_⟧env γ , z))
                                               (val-det E)))))

soundness-case-r : ∀ {Γ τ₁ τ₂ τ} {M : Γ ⊢ τ₁ [+] τ₂} {N₁ : Γ · τ₁ ⊢ τ} {N₂ : Γ · τ₂ ⊢ τ}
                   {γ : Env Γ} {v u ℛ 𝒮}
                   (E : γ , M ⇓ inj₂ v , ℛ)
                   (F : (γ , v) , N₂ ⇓ u , 𝒮) →
                   _≈H_⟨_,_⟩
                     {m₁ = width-ctxt Γ γ}
                     {n₁ = width τ u}
                     {m₂ = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)}
                     {n₂ = ⟦ τ ⟧ty .fam .fm
                             (⟦ case M N₁ N₂ ⟧tm .idxf .func (⟦_⟧env γ))}
                     (_∘_ {x = width-ctxt Γ γ} {y = width-ctxt Γ γ + width τ₂ v} {z = width τ u}
                          𝒮 (pairM {x = width-ctxt Γ γ} {y = width-ctxt Γ γ} {z = width τ₂ v}
                                   (id (width-ctxt Γ γ)) ℛ))
                     (⟦ case M N₁ N₂ ⟧tm .famf .transf (⟦_⟧env γ))
                     (width-ctxt-≡ Γ γ)
                     (trans (width-≡ τ u)
                            (cong (⟦ τ ⟧ty .fam .fm)
                                  (trans (val-det F)
                                         (cong (λ z → [ ⟦ N₁ ⟧tm , ⟦ N₂ ⟧tm ] .idxf .func (⟦_⟧env γ , z))
                                               (val-det E)))))

soundness (eval-var x γ) = soundness-var x γ
soundness {Γ = Γ} {γ = γ} eval-unit  = into-zero-≈H {Γ} γ refl _ _
soundness {Γ = Γ} {γ = γ} eval-nil   = into-zero-≈H {Γ} γ refl _ _
soundness {Γ = Γ} {τ = τ₁ [×] τ₂} {γ = γ} (eval-pair {M = M} {N = N} {v = v} {u = u} {ℛ₁ = ℛ₁} {ℛ₂ = ℛ₂} E F) =
  ≈-trans {x = m} {y = n}
    (subst₂-pair (width-ctxt-≡ Γ γ)
      (trans (width-≡ τ₁ v) (cong (⟦ τ₁ ⟧ty .fam .fm) (val-det E)))
      (trans (width-≡ τ₂ u) (cong (⟦ τ₂ ⟧ty .fam .fm) (val-det F)))
      (trans (cong₂ _+_ (width-≡ τ₁ v) (width-≡ τ₂ u))
             (cong (⟦ τ₁ [×] τ₂ ⟧ty .fam .fm) (val-det (eval-pair E F))))
      ℛ₁ ℛ₂)
    (pair-cong {x = m} {y = ⟦ τ₁ ⟧ty .fam .fm (val M γ)} {z = ⟦ τ₂ ⟧ty .fam .fm (val N γ)}
               (soundness E) (soundness F))
  where
    m = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)
    n = ⟦ τ₁ ⟧ty .fam .fm (val M γ) + ⟦ τ₂ ⟧ty .fam .fm (val N γ)
soundness {Γ = Γ} {τ = τ} {γ = γ} (eval-fst {τ₂ = τ₂} {M = M} {v = v} {u = u} {ℛ = ℛ} E) =
  ≈-trans {x = m} {y = n}
    (subst₂-p₁-∘ (width-ctxt-≡ Γ γ)
      (trans (width-≡ τ  v) (cong (⟦ τ  ⟧ty .fam .fm) (cong proj₁ (val-det E))))
      (trans (width-≡ (τ [×] τ₂) (v , u)) (cong (⟦ τ [×] τ₂ ⟧ty .fam .fm) (val-det E))) ℛ)
    (≈-trans {x = m} {y = n}
      (∘-cong {x = m} {y = k} {z = n} (≈-refl {x = k} {y = n}) (soundness E))
      (≈-sym {x = m} {y = n} (id-left {x = m} {y = n})))
  where
    m = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)
    k = ⟦ τ [×] τ₂ ⟧ty .fam .fm (val M γ)
    n = ⟦ τ ⟧ty .fam .fm (proj₁ (val M γ))
soundness {Γ = Γ} {τ = τ} {γ = γ} (eval-snd {τ₁ = τ₁} {M = M} {v = v} {u = u} {ℛ = ℛ} E) =
  ≈-trans {x = m} {y = n}
    (subst₂-p₂-∘ (width-ctxt-≡ Γ γ)
      (trans (width-≡ τ  u) (cong (⟦ τ  ⟧ty .fam .fm) (cong proj₂ (val-det E))))
      (trans (width-≡ (τ₁ [×] τ) (v , u)) (cong (⟦ τ₁ [×] τ ⟧ty .fam .fm) (val-det E))) ℛ)
    (≈-trans {x = m} {y = n}
      (∘-cong {x = m} {y = k} {z = n} (≈-refl {x = k} {y = n}) (soundness E))
      (≈-sym {x = m} {y = n} (id-left {x = m} {y = n})))
  where
    m = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)
    k = ⟦ τ₁ [×] τ ⟧ty .fam .fm (val M γ)
    n = ⟦ τ ⟧ty .fam .fm (proj₂ (val M γ))
soundness {Γ = Γ} {τ = τ₁ [+] τ₂} {γ = γ} {ℛ = ℛ} (eval-inl {M = M} {v = v} E) =
  ≈-trans {x = m} {y = n}
    (≈H-bridge {f = ℛ} {g = ⟦ M ⟧tm .famf .transf (⟦_⟧env γ)} {m₁≡m₂ = width-ctxt-≡ Γ γ}
               (cong (trans (width-≡ τ₁ v)) (cong-∘ {f = ⟦ τ₁ [+] τ₂ ⟧ty .fam .fm} {g = inj₁} (val-det E)))
               (soundness E))
    (≈-sym {x = m} {y = n}
      (≈-trans {x = m} {y = n} (id-left {x = m} {y = n}) (id-left {x = m} {y = n})))
  where m = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ); n = ⟦ τ₁ ⟧ty .fam .fm (val M γ)
soundness {Γ = Γ} {τ = τ₁ [+] τ₂} {γ = γ} {ℛ = ℛ} (eval-inr {M = M} {v = v} E) =
  ≈-trans {x = m} {y = n}
    (≈H-bridge {f = ℛ} {g = ⟦ M ⟧tm .famf .transf (⟦_⟧env γ)} {m₁≡m₂ = width-ctxt-≡ Γ γ}
               (cong (trans (width-≡ τ₂ v)) (cong-∘ {f = ⟦ τ₁ [+] τ₂ ⟧ty .fam .fm} {g = inj₂} (val-det E)))
               (soundness E))
    (≈-sym {x = m} {y = n}
      (≈-trans {x = m} {y = n} (id-left {x = m} {y = n}) (id-left {x = m} {y = n})))
  where m = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ); n = ⟦ τ₂ ⟧ty .fam .fm (val M γ)
soundness (eval-case-l {N₂ = N₂} E F) = soundness-case-l {N₂ = N₂} E F
soundness (eval-case-r {N₁ = N₁} E F) = soundness-case-r {N₁ = N₁} E F
soundness {Γ = Γ} {γ = γ} (eval-cons {τ = τ} {M = M} {N = N} {v = v} {u = u} {ℛ₁ = ℛ₁} {ℛ₂ = ℛ₂} E F) =
  ≈-trans {x = m} {y = n}
    (subst₂-pair (width-ctxt-≡ Γ γ)
      (trans (width-≡ τ v) (cong (⟦ τ ⟧ty .fam .fm) (val-det E)))
      (trans (width-≡ (list τ) u) (cong (⟦ list τ ⟧ty .fam .fm) (val-det F)))
      (trans (cong₂ _+_ (width-≡ τ v) (width-≡ (list τ) u))
             (cong (⟦ list τ ⟧ty .fam .fm) (val-det (eval-cons E F))))
      ℛ₁ ℛ₂)
    (≈-trans {x = m} {y = n}
      (pair-cong {x = m} {y = ⟦ τ ⟧ty .fam .fm (val M γ)} {z = ⟦ list τ ⟧ty .fam .fm (val N γ)}
                 (soundness E) (soundness F))
      (≈-sym {x = m} {y = n} (≈-trans {x = m} {y = n} (id-left {x = m} {y = n}) (id-left {x = m} {y = n}))))
  where
    m = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)
    n = ⟦ τ ⟧ty .fam .fm (val M γ) + ⟦ list τ ⟧ty .fam .fm (val N γ)
soundness (eval-bop ω E) = soundness-bop ω E
soundness {Γ = Γ} {γ = γ} (eval-brel {Ms = Ms} {vs = vs} ω E) =
  ≈H-bridge {f = brel-rel γ (rel-pred ω vs)}
            {g = ⟦ brel ω Ms ⟧tm .famf .transf (⟦_⟧env γ)}
            {m₁≡m₂ = width-ctxt-≡ Γ γ}
            (uip _ _)
            (into-via-zero-≈H {Γ} γ
              (b-width (rel-pred ω vs))
              (b-fm (⟦rel⟧ ω .idxf .func (val-bases Ms γ)))
              _ _)
  where
    b-width : ∀ (v : Val (unit [+] unit)) → width (unit [+] unit) v ≡ 0
    b-width (inj₁ _) = refl
    b-width (inj₂ _) = refl
    b-fm : ∀ (v : Val (unit [+] unit)) → ⟦ unit [+] unit ⟧ty .fam .fm v ≡ 0
    b-fm (inj₁ _) = refl
    b-fm (inj₂ _) = refl
soundness {Γ = Γ} {γ = γ} (eval-fold {τ₁ = τ₁} {τ₂ = τ₂} {M₁ = M₁} {M₂ = M₂} {M = M}
                                       {v-nil = v-nil} {ys = ys} {final = final}
                                       {𝒮 = 𝒮} {ℛ₂ = ℛ₂} E₁ E₂ E₃) =
  ≈H-bridge {f = ℛ₂}
            {g = ⟦ fold M₁ M₂ M ⟧tm .famf .transf (⟦_⟧env γ)}
            {m₁≡m₂ = width-ctxt-≡ Γ γ}
            (uip _ _)
            (≈H-trans {n₂ = ⟦ τ₂ ⟧ty .fam .fm
                                (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .idxf .func
                                       (⟦_⟧env γ , ⟦_⟧val {list τ₁} ys))}
                      {n₃ = ⟦ τ₂ ⟧ty .fam .fm
                              (⟦ fold M₁ M₂ M ⟧tm .idxf .func (⟦_⟧env γ))}
                      {m₁≡m₂ = width-ctxt-≡ Γ γ}
                      (soundness-iters E₁ E₃)
                      (substP (λ X → _≈_ {x = m₂}
                                         {y = ⟦ τ₂ ⟧ty .fam .fm
                                                (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .idxf .func
                                                       (⟦_⟧env γ , val M γ))}
                                         X
                                         (⟦ fold M₁ M₂ M ⟧tm .famf .transf (⟦_⟧env γ)))
                              (sym (subst₂-∘
                                refl inter-eq _
                                (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .famf .transf
                                        (⟦_⟧env γ , ⟦_⟧val {list τ₁} ys))
                                (pairM {x = m₂} {y = m₂}
                                       {z = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys)}
                                       (id m₂) 𝒮-coerced)))
                              (≈-trans {x = m₂}
                                       {y = ⟦ τ₂ ⟧ty .fam .fm
                                              (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .idxf .func
                                                     (⟦_⟧env γ , val M γ))}
                                (∘-cong {x = m₂}
                                        {y = m₂ + ⟦ list τ₁ ⟧ty .fam .fm (val M γ)}
                                        {z = ⟦ τ₂ ⟧ty .fam .fm
                                               (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .idxf .func (⟦_⟧env γ , val M γ))}
                                        (fold-transf-coh (val-det E₂))
                                        (≈-trans {x = m₂} {y = m₂ + ⟦ list τ₁ ⟧ty .fam .fm (val M γ)}
                                          (subst₂-pair refl refl
                                                       (cong (⟦ list τ₁ ⟧ty .fam .fm) (val-det E₂))
                                                       inter-eq (id m₂) 𝒮-coerced)
                                          (pair-cong {x = m₂} {y = m₂}
                                                     {z = ⟦ list τ₁ ⟧ty .fam .fm (val M γ)}
                                                     (subst₂-id (refl {x = m₂}))
                                                     𝒮-stuff)))
                                (≈-sym {x = m₂}
                                       {y = ⟦ τ₂ ⟧ty .fam .fm
                                              (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .idxf .func (⟦_⟧env γ , val M γ))}
                                       (id-left {x = m₂}
                                                {y = ⟦ τ₂ ⟧ty .fam .fm
                                                       (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .idxf .func
                                                              (⟦_⟧env γ , val M γ))})))))
  where
    m₂ = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)
    𝒮-coerced : m₂ ⇒ ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys)
    𝒮-coerced = subst₂ _⇒_ (width-ctxt-≡ Γ γ) (width-≡ (list τ₁) ys) 𝒮
    inter-eq : (m₂ + ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys))
             ≡ (m₂ + ⟦ list τ₁ ⟧ty .fam .fm (val M γ))
    inter-eq = cong (m₂ +_) (cong (⟦ list τ₁ ⟧ty .fam .fm) (val-det E₂))
    fold-transf-coh : ∀ {a b : ⟦ list τ₁ ⟧ty .idx .Carrier} (eq : a ≡ b) →
                      _≈_ {x = m₂ + ⟦ list τ₁ ⟧ty .fam .fm b}
                          {y = ⟦ τ₂ ⟧ty .fam .fm
                                 (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .idxf .func (⟦_⟧env γ , b))}
                          (subst₂ _⇒_ (cong (m₂ +_) (cong (⟦ list τ₁ ⟧ty .fam .fm) eq))
                                      (cong (⟦ τ₂ ⟧ty .fam .fm)
                                            (cong (λ z → ⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .idxf .func
                                                                (⟦_⟧env γ , z)) eq))
                                      (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .famf .transf (⟦_⟧env γ , a)))
                          (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .famf .transf (⟦_⟧env γ , b))
    fold-transf-coh {a} refl =
      ≈-refl {x = m₂ + ⟦ list τ₁ ⟧ty .fam .fm a}
             {y = ⟦ τ₂ ⟧ty .fam .fm
                    (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .idxf .func (⟦_⟧env γ , a))}
    -- Bridges `subst₂ refl (cong .fm (val-det E₂)) 𝒮-coerced` to soundness E₂'s form via
    -- a propositional equality `subst₂ refl q 𝒮-coerced ≡ subst₂ (width-ctxt-≡) (trans (width-≡) q) 𝒮`,
    -- then applies soundness E₂.
    𝒮-stuff : _≈_ {x = m₂} {y = ⟦ list τ₁ ⟧ty .fam .fm (val M γ)}
                  (subst₂ _⇒_ {x = m₂} {y = m₂}
                              {u = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys)}
                              {v = ⟦ list τ₁ ⟧ty .fam .fm (val M γ)}
                              refl
                              (cong (⟦ list τ₁ ⟧ty .fam .fm) (val-det E₂))
                              𝒮-coerced)
                  (⟦ M ⟧tm .famf .transf (⟦_⟧env γ))
    𝒮-stuff = substP (λ X → _≈_ {x = m₂} {y = ⟦ list τ₁ ⟧ty .fam .fm (val M γ)}
                                X (⟦ M ⟧tm .famf .transf (⟦_⟧env γ)))
                     (sym (𝒮-bridge (val-det E₂)))
                     (soundness E₂)
      where
        𝒮-bridge : ∀ {b} (eq : ⟦_⟧val {list τ₁} ys ≡ b) →
                   _≡_ (subst₂ _⇒_ refl (cong (⟦ list τ₁ ⟧ty .fam .fm) eq) 𝒮-coerced)
                       (subst₂ _⇒_ (width-ctxt-≡ Γ γ)
                                   (trans (width-≡ (list τ₁) ys)
                                          (cong (⟦ list τ₁ ⟧ty .fam .fm) eq))
                                   𝒮)
        𝒮-bridge refl =
          cong (λ q → subst₂ _⇒_ (width-ctxt-≡ Γ γ) q 𝒮)
               (sym (trans-reflʳ (width-≡ (list τ₁) ys)))

-- At γ with `b ≡ v`, `[ N₁ , N₂ ]` dispatches definitionally to the selected branch
-- (`⟦N₁⟧` for `inj₁ x`, `⟦N₂⟧` for `inj₂ y`). Pattern-matches on the equation so `b`
-- reduces to `v`, exposing the dispatch.
case-eval-case : ∀ {Γ τ₁ τ₂ τ} {N₁ : Γ · τ₁ ⊢ τ} {N₂ : Γ · τ₂ ⊢ τ} {γ : Env Γ}
                 (v : Carrier ((⟦ τ₁ ⟧ty ⟦+⟧ ⟦ τ₂ ⟧ty) .idx))
                 {b}
                 (e : b ≡ v) →
                 [ ⟦ N₁ ⟧tm , ⟦ N₂ ⟧tm ] .idxf .func (⟦_⟧env γ , b)
                   ≡ [ ⟦ N₁ ⟧tm , ⟦ N₂ ⟧tm ] .idxf .func (⟦_⟧env γ , v)
case-eval-case _ refl = refl


-- Case-l analog of if-mor-≈H-aux: at index `(γ, b)` with `b ≡ inj₁ v-sub`, the case-side
-- Mor-∘ unfolded form reduces to `⟦N₁⟧.transf (γ, v-sub) ∘ pair (id m) h-trf-coerced`. The
-- proof is just `≈-sym id-left` after the pattern match collapses the outer id.
case-mor-≈H-aux : ∀ {Γ τ₁ τ₂ τ} {N₁ : Γ · τ₁ ⊢ τ} {N₂ : Γ · τ₂ ⊢ τ} {γ : Env Γ}
                  (v : Carrier ((⟦ τ₁ ⟧ty ⟦+⟧ ⟦ τ₂ ⟧ty) .idx))
                  {b}
                  (eq : b ≡ v)
                  (h-trf : ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ) ⇒ ⟦ τ₁ [+] τ₂ ⟧ty .fam .fm b) →
                  _≈H_⟨_,_⟩
                    {m₁ = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)}
                    {n₁ = ⟦ τ ⟧ty .fam .fm
                            ([ ⟦ N₁ ⟧tm , ⟦ N₂ ⟧tm ] .idxf .func (⟦_⟧env γ , v))}
                    {m₂ = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)}
                    {n₂ = ⟦ τ ⟧ty .fam .fm
                            ([ ⟦ N₁ ⟧tm , ⟦ N₂ ⟧tm ] .idxf .func (⟦_⟧env γ , b))}
                    (_∘_ {x = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)}
                         {y = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ) + ⟦ τ₁ [+] τ₂ ⟧ty .fam .fm v}
                         {z = ⟦ τ ⟧ty .fam .fm
                                ([ ⟦ N₁ ⟧tm , ⟦ N₂ ⟧tm ] .idxf .func (⟦_⟧env γ , v))}
                         ([ ⟦ N₁ ⟧tm , ⟦ N₂ ⟧tm ] .famf .transf (⟦_⟧env γ , v))
                         (pairM {x = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)}
                                {y = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)}
                                {z = ⟦ τ₁ [+] τ₂ ⟧ty .fam .fm v}
                                (id (⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)))
                                (subst (λ X → ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ) ⇒ X)
                                       (cong (⟦ τ₁ [+] τ₂ ⟧ty .fam .fm) eq) h-trf)))
                    (_∘_ {x = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)}
                         {y = ⟦ τ ⟧ty .fam .fm
                                ([ ⟦ N₁ ⟧tm , ⟦ N₂ ⟧tm ] .idxf .func (⟦_⟧env γ , b))}
                         {z = ⟦ τ ⟧ty .fam .fm
                                ([ ⟦ N₁ ⟧tm , ⟦ N₂ ⟧tm ] .idxf .func (⟦_⟧env γ , b))}
                         (id (⟦ τ ⟧ty .fam .fm
                                ([ ⟦ N₁ ⟧tm , ⟦ N₂ ⟧tm ] .idxf .func (⟦_⟧env γ , b))))
                         (_∘_ {x = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)}
                              {y = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ) + ⟦ τ₁ [+] τ₂ ⟧ty .fam .fm b}
                              {z = ⟦ τ ⟧ty .fam .fm
                                     ([ ⟦ N₁ ⟧tm , ⟦ N₂ ⟧tm ] .idxf .func (⟦_⟧env γ , b))}
                              ([ ⟦ N₁ ⟧tm , ⟦ N₂ ⟧tm ] .famf .transf (⟦_⟧env γ , b))
                              (pairM {x = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)}
                                     {y = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)}
                                     {z = ⟦ τ₁ [+] τ₂ ⟧ty .fam .fm b}
                                     (id (⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ))) h-trf)))
                    refl
                    (sym (cong (⟦ τ ⟧ty .fam .fm) (case-eval-case {N₁ = N₁} {N₂ = N₂} {γ = γ} v eq)))
case-mor-≈H-aux {Γ = Γ} {τ = τ} {N₁ = N₁} {N₂ = N₂} {γ = γ} v refl h-trf =
  ≈-sym {x = m} {y = n} (id-left {x = m} {y = n})
  where
    m = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)
    n = ⟦ τ ⟧ty .fam .fm ([ ⟦ N₁ ⟧tm , ⟦ N₂ ⟧tm ] .idxf .func (⟦_⟧env γ , v))

soundness-case-l {Γ = Γ} {τ₁ = τ₁} {τ₂ = τ₂} {τ = τ} {M = M} {N₁ = N₁} {N₂ = N₂}
                 {γ = γ} {v = v} {u = u} {ℛ = ℛ} {𝒮 = 𝒮} E F =
  ≈H-bridge {f = lhs-mor}
            {g = ⟦ case M N₁ N₂ ⟧tm .famf .transf (⟦_⟧env γ)}
            {m₁≡m₂ = width-ctxt-≡ Γ γ}
            (uip _ _)
            (≈H-trans {m₁ = m₁} {n₁ = width τ u}
                      {m₂ = m₂} {n₂ = n-int}
                      {n₃ = ⟦ τ ⟧ty .fam .fm
                              ([ ⟦ N₁ ⟧tm , ⟦ N₂ ⟧tm ] .idxf .func
                                 (⟦_⟧env γ , ⟦ M ⟧tm .idxf .func (⟦_⟧env γ)))}
                      {f = lhs-mor}
                      {g = int-mor}
                      {h = ⟦ case M N₁ N₂ ⟧tm .famf .transf (⟦_⟧env γ)}
                      {m₁≡m₂ = width-ctxt-≡ Γ γ}
                      {n₁≡n₂ = trans (width-≡ τ u) (cong (⟦ τ ⟧ty .fam .fm) (val-det F))}
                      {n₂≡n₃ = sym (cong (⟦ τ ⟧ty .fam .fm)
                                        (case-eval-case {N₁ = N₁} {N₂ = N₂} {γ = γ}
                                                        (inj₁ v₁) (sym (val-det E))))}
                      first-leg
                      (case-mor-≈H-aux {Γ = Γ} {τ₁ = τ₁} {τ₂ = τ₂} {τ = τ}
                                       {N₁ = N₁} {N₂ = N₂} {γ = γ}
                                       (inj₁ v₁) (sym (val-det E))
                                       (⟦ M ⟧tm .famf .transf (⟦_⟧env γ))))
  where
    m₁ = width-ctxt Γ γ
    m₂ = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)
    v₁ = ⟦_⟧val {τ₁} v
    n-int = ⟦ τ ⟧ty .fam .fm (⟦ N₁ ⟧tm .idxf .func (⟦_⟧env γ , v₁))
    pair-mor : m₁ ⇒ (m₁ + width τ₁ v)
    pair-mor = pairM {x = m₁} {y = m₁} {z = width τ₁ v} (id m₁) ℛ
    lhs-mor : m₁ ⇒ width τ u
    lhs-mor = _∘_ {x = m₁} {y = m₁ + width τ₁ v} {z = width τ u} 𝒮 pair-mor
    M-mor-coerced : m₂ ⇒ ⟦ τ₁ ⟧ty .fam .fm v₁
    M-mor-coerced = subst (λ X → m₂ ⇒ X)
                          (cong (⟦ τ₁ [+] τ₂ ⟧ty .fam .fm) (sym (val-det E)))
                          (⟦ M ⟧tm .famf .transf (⟦_⟧env γ))
    pair-coerced-model : m₂ ⇒ (m₂ + ⟦ τ₁ ⟧ty .fam .fm v₁)
    pair-coerced-model = pairM {x = m₂} {y = m₂} {z = ⟦ τ₁ ⟧ty .fam .fm v₁}
                                (id m₂) M-mor-coerced
    int-mor : m₂ ⇒ n-int
    int-mor = _∘_ {x = m₂} {y = m₂ + ⟦ τ₁ ⟧ty .fam .fm v₁} {z = n-int}
                  (⟦ N₁ ⟧tm .famf .transf (⟦_⟧env γ , v₁)) pair-coerced-model
    m₁+v≡m₂+v₁ : (m₁ + width τ₁ v) ≡ (m₂ + ⟦ τ₁ ⟧ty .fam .fm v₁)
    m₁+v≡m₂+v₁ = cong₂ _+_ (width-ctxt-≡ Γ γ) (width-≡ τ₁ v)
    bridge-F = trans (width-≡ τ u) (cong (⟦ τ ⟧ty .fam .fm) (val-det F))
    ℛ-stuff : _≈_ {x = m₂} {y = ⟦ τ₁ ⟧ty .fam .fm v₁}
                  (subst₂ _⇒_ (width-ctxt-≡ Γ γ) (width-≡ τ₁ v) ℛ)
                  M-mor-coerced
    ℛ-stuff =
      -- (1) Factor soundness E's subst₂ over trans (subst₂-trans-cod),
      -- (2) apply subst (sym (cong fm (val-det E))) to both sides (subst-≈-cong),
      -- (3) cancel inner subst-on-sym pair (subst-sym-subst),
      -- (4) convert `sym (cong fm p)` to `cong fm (sym p)` (sym-cong) to land at M-mor-coerced.
      substP (λ X → _≈_ {x = m₂} {y = ⟦ τ₁ ⟧ty .fam .fm v₁}
                        (subst₂ _⇒_ (width-ctxt-≡ Γ γ) (width-≡ τ₁ v) ℛ) X)
             (cong (λ p → subst (λ X → m₂ ⇒ X) p (⟦ M ⟧tm .famf .transf (⟦_⟧env γ)))
                   (sym-cong (val-det E)))
             (substP (λ X → _≈_ {x = m₂} {y = ⟦ τ₁ ⟧ty .fam .fm v₁} X
                                (subst (λ X' → m₂ ⇒ X')
                                       (sym (cong (⟦ τ₁ [+] τ₂ ⟧ty .fam .fm) (val-det E)))
                                       (⟦ M ⟧tm .famf .transf (⟦_⟧env γ))))
                     (subst-sym-subst (cong (⟦ τ₁ [+] τ₂ ⟧ty .fam .fm) (val-det E)))
                     (subst-≈-cong {m = m₂}
                                   (sym (cong (⟦ τ₁ [+] τ₂ ⟧ty .fam .fm) (val-det E)))
                                   (substP (λ X → _≈_ {x = m₂}
                                                      {y = ⟦ τ₁ [+] τ₂ ⟧ty .fam .fm
                                                             (⟦ M ⟧tm .idxf .func (⟦_⟧env γ))}
                                                      X (⟦ M ⟧tm .famf .transf (⟦_⟧env γ)))
                                           (subst₂-trans-cod (width-ctxt-≡ Γ γ) (width-≡ τ₁ v)
                                                             (cong (⟦ τ₁ [+] τ₂ ⟧ty .fam .fm) (val-det E)) ℛ)
                                           (soundness E))))
    first-leg : _≈H_⟨_,_⟩ {m₁ = m₁} {n₁ = width τ u} {m₂ = m₂} {n₂ = n-int}
                  lhs-mor int-mor
                  (width-ctxt-≡ Γ γ)
                  bridge-F
    first-leg =
      substP (λ X → _≈_ {x = m₂} {y = n-int} X int-mor)
             (sym (subst₂-∘ {m = m₁} {m' = m₂} {k = m₁ + width τ₁ v}
                            {k' = m₂ + ⟦ τ₁ ⟧ty .fam .fm v₁}
                            {n = width τ u} {n' = n-int}
                            (width-ctxt-≡ Γ γ) m₁+v≡m₂+v₁ bridge-F 𝒮 pair-mor))
             (∘-cong {x = m₂} {y = m₂ + ⟦ τ₁ ⟧ty .fam .fm v₁} {z = n-int}
                     (soundness F)
                     (≈-trans {x = m₂} {y = m₂ + ⟦ τ₁ ⟧ty .fam .fm v₁}
                       (subst₂-pair (width-ctxt-≡ Γ γ) (width-ctxt-≡ Γ γ)
                                    (width-≡ τ₁ v) m₁+v≡m₂+v₁ (id m₁) ℛ)
                       (pair-cong {x = m₂} {y = m₂} {z = ⟦ τ₁ ⟧ty .fam .fm v₁}
                                  (subst₂-id (width-ctxt-≡ Γ γ))
                                  ℛ-stuff)))

soundness-case-r {Γ = Γ} {τ₁ = τ₁} {τ₂ = τ₂} {τ = τ} {M = M} {N₁ = N₁} {N₂ = N₂}
                 {γ = γ} {v = v} {u = u} {ℛ = ℛ} {𝒮 = 𝒮} E F =
  ≈H-bridge {f = lhs-mor}
            {g = ⟦ case M N₁ N₂ ⟧tm .famf .transf (⟦_⟧env γ)}
            {m₁≡m₂ = width-ctxt-≡ Γ γ}
            (uip _ _)
            (≈H-trans {m₁ = m₁} {n₁ = width τ u}
                      {m₂ = m₂} {n₂ = n-int}
                      {n₃ = ⟦ τ ⟧ty .fam .fm
                              ([ ⟦ N₁ ⟧tm , ⟦ N₂ ⟧tm ] .idxf .func
                                 (⟦_⟧env γ , ⟦ M ⟧tm .idxf .func (⟦_⟧env γ)))}
                      {f = lhs-mor}
                      {g = int-mor}
                      {h = ⟦ case M N₁ N₂ ⟧tm .famf .transf (⟦_⟧env γ)}
                      {m₁≡m₂ = width-ctxt-≡ Γ γ}
                      {n₁≡n₂ = trans (width-≡ τ u) (cong (⟦ τ ⟧ty .fam .fm) (val-det F))}
                      {n₂≡n₃ = sym (cong (⟦ τ ⟧ty .fam .fm)
                                        (case-eval-case {N₁ = N₁} {N₂ = N₂} {γ = γ}
                                                        (inj₂ v₁) (sym (val-det E))))}
                      first-leg
                      (case-mor-≈H-aux {Γ = Γ} {τ₁ = τ₁} {τ₂ = τ₂} {τ = τ}
                                       {N₁ = N₁} {N₂ = N₂} {γ = γ}
                                       (inj₂ v₁) (sym (val-det E))
                                       (⟦ M ⟧tm .famf .transf (⟦_⟧env γ))))
  where
    m₁ = width-ctxt Γ γ
    m₂ = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)
    v₁ = ⟦_⟧val {τ₂} v
    n-int = ⟦ τ ⟧ty .fam .fm (⟦ N₂ ⟧tm .idxf .func (⟦_⟧env γ , v₁))
    pair-mor : m₁ ⇒ (m₁ + width τ₂ v)
    pair-mor = pairM {x = m₁} {y = m₁} {z = width τ₂ v} (id m₁) ℛ
    lhs-mor : m₁ ⇒ width τ u
    lhs-mor = _∘_ {x = m₁} {y = m₁ + width τ₂ v} {z = width τ u} 𝒮 pair-mor
    M-mor-coerced : m₂ ⇒ ⟦ τ₂ ⟧ty .fam .fm v₁
    M-mor-coerced = subst (λ X → m₂ ⇒ X)
                          (cong (⟦ τ₁ [+] τ₂ ⟧ty .fam .fm) (sym (val-det E)))
                          (⟦ M ⟧tm .famf .transf (⟦_⟧env γ))
    pair-coerced-model : m₂ ⇒ (m₂ + ⟦ τ₂ ⟧ty .fam .fm v₁)
    pair-coerced-model = pairM {x = m₂} {y = m₂} {z = ⟦ τ₂ ⟧ty .fam .fm v₁}
                                (id m₂) M-mor-coerced
    int-mor : m₂ ⇒ n-int
    int-mor = _∘_ {x = m₂} {y = m₂ + ⟦ τ₂ ⟧ty .fam .fm v₁} {z = n-int}
                  (⟦ N₂ ⟧tm .famf .transf (⟦_⟧env γ , v₁)) pair-coerced-model
    m₁+v≡m₂+v₁ : (m₁ + width τ₂ v) ≡ (m₂ + ⟦ τ₂ ⟧ty .fam .fm v₁)
    m₁+v≡m₂+v₁ = cong₂ _+_ (width-ctxt-≡ Γ γ) (width-≡ τ₂ v)
    bridge-F = trans (width-≡ τ u) (cong (⟦ τ ⟧ty .fam .fm) (val-det F))
    ℛ-stuff : _≈_ {x = m₂} {y = ⟦ τ₂ ⟧ty .fam .fm v₁}
                  (subst₂ _⇒_ (width-ctxt-≡ Γ γ) (width-≡ τ₂ v) ℛ)
                  M-mor-coerced
    ℛ-stuff =
      substP (λ X → _≈_ {x = m₂} {y = ⟦ τ₂ ⟧ty .fam .fm v₁}
                        (subst₂ _⇒_ (width-ctxt-≡ Γ γ) (width-≡ τ₂ v) ℛ) X)
             (cong (λ p → subst (λ X → m₂ ⇒ X) p (⟦ M ⟧tm .famf .transf (⟦_⟧env γ)))
                   (sym-cong (val-det E)))
             (substP (λ X → _≈_ {x = m₂} {y = ⟦ τ₂ ⟧ty .fam .fm v₁} X
                                (subst (λ X' → m₂ ⇒ X')
                                       (sym (cong (⟦ τ₁ [+] τ₂ ⟧ty .fam .fm) (val-det E)))
                                       (⟦ M ⟧tm .famf .transf (⟦_⟧env γ))))
                     (subst-sym-subst (cong (⟦ τ₁ [+] τ₂ ⟧ty .fam .fm) (val-det E)))
                     (subst-≈-cong {m = m₂}
                                   (sym (cong (⟦ τ₁ [+] τ₂ ⟧ty .fam .fm) (val-det E)))
                                   (substP (λ X → _≈_ {x = m₂}
                                                      {y = ⟦ τ₁ [+] τ₂ ⟧ty .fam .fm
                                                             (⟦ M ⟧tm .idxf .func (⟦_⟧env γ))}
                                                      X (⟦ M ⟧tm .famf .transf (⟦_⟧env γ)))
                                           (subst₂-trans-cod (width-ctxt-≡ Γ γ) (width-≡ τ₂ v)
                                                             (cong (⟦ τ₁ [+] τ₂ ⟧ty .fam .fm) (val-det E)) ℛ)
                                           (soundness E))))
    first-leg : _≈H_⟨_,_⟩ {m₁ = m₁} {n₁ = width τ u} {m₂ = m₂} {n₂ = n-int}
                  lhs-mor int-mor
                  (width-ctxt-≡ Γ γ)
                  bridge-F
    first-leg =
      substP (λ X → _≈_ {x = m₂} {y = n-int} X int-mor)
             (sym (subst₂-∘ {m = m₁} {m' = m₂} {k = m₁ + width τ₂ v}
                            {k' = m₂ + ⟦ τ₂ ⟧ty .fam .fm v₁}
                            {n = width τ u} {n' = n-int}
                            (width-ctxt-≡ Γ γ) m₁+v≡m₂+v₁ bridge-F 𝒮 pair-mor))
             (∘-cong {x = m₂} {y = m₂ + ⟦ τ₂ ⟧ty .fam .fm v₁} {z = n-int}
                     (soundness F)
                     (≈-trans {x = m₂} {y = m₂ + ⟦ τ₂ ⟧ty .fam .fm v₁}
                       (subst₂-pair (width-ctxt-≡ Γ γ) (width-ctxt-≡ Γ γ)
                                    (width-≡ τ₂ v) m₁+v≡m₂+v₁ (id m₁) ℛ)
                       (pair-cong {x = m₂} {y = m₂} {z = ⟦ τ₂ ⟧ty .fam .fm v₁}
                                  (subst₂-id (width-ctxt-≡ Γ γ))
                                  ℛ-stuff)))

soundness-bases {Γ = Γ} {γ = γ} []-bases = into-zero-≈H {Γ} γ refl _ _
soundness-bases {Γ = Γ} {σs = σ ∷ σs} {Ms = M ∷ Ms} {γ = γ}
                (_∷-bases_ {v = v} {vs = vs} {ℛ₁ = ℛ₁} {ℛ₂ = ℛ₂} E Es) =
  ≈-trans {x = m} {y = n}
    (subst₂-pair (width-ctxt-≡ Γ γ)
                 (trans (width-≡ (base σ) v) (cong (⟦ base σ ⟧ty .fam .fm) (val-det E)))
                 (sym (bases-fm-≡ σs (⟦ Ms ⟧bases .idxf .func (⟦_⟧env γ))))
                 (sym (bases-fm-≡ (σ ∷ σs) (⟦ M ∷ Ms ⟧bases .idxf .func (⟦_⟧env γ))))
                 ℛ₁ ℛ₂)
    (pair-cong {x = m} {y = ⟦ base σ ⟧ty .fam .fm (val M γ)}
               {z = ⟦ σs ⟧bases-list .fam .fm (⟦ Ms ⟧bases .idxf .func (⟦_⟧env γ))}
               (soundness E) (soundness-bases Es))
  where
    m = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)
    n = ⟦ base σ ⟧ty .fam .fm (val M γ) + ⟦ σs ⟧bases-list .fam .fm (⟦ Ms ⟧bases .idxf .func (⟦_⟧env γ))

soundness-iters {Γ = Γ} {τ₁ = τ₁} {τ₂ = τ₂} {M₁ = M₁} {γ = γ} {𝒮 = 𝒮} E₁ nil-iter =
  ≈-trans {x = m₂} {y = n}
    (soundness E₁)
    (≈-sym {x = m₂} {y = n}
      (≈-trans {x = m₂} {y = n}
        (assoc {w = m₂} {x = m₂ + 0} {y = m₂} {z = n}
               (⟦ M₁ ⟧tm .famf .transf (⟦_⟧env γ))
               (p₁ {m₂} {0})
               (pairM {x = m₂} {y = m₂} {z = 0} (id m₂) 𝒮-coerced))
        (≈-trans {x = m₂} {y = n}
          (∘-cong {x = m₂} {y = m₂} {z = n}
                  (≈-refl {x = m₂} {y = n})
                  (pair-p₁ {x = m₂} {y = m₂} {z = 0} (id m₂) 𝒮-coerced))
          (id-right {x = m₂} {y = n}))))
  where
    m₂ = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)
    n = ⟦ τ₂ ⟧ty .fam .fm (⟦ M₁ ⟧tm .idxf .func (⟦_⟧env γ))
    𝒮-coerced : m₂ ⇒ 0
    𝒮-coerced = subst₂ _⇒_ (width-ctxt-≡ Γ γ) (width-≡ (list τ₁) []) 𝒮
soundness-iters {Γ = Γ} {τ₁ = τ₁} {τ₂ = τ₂} {M₁ = M₁} {M₂ = M₂} {γ = γ} {v-nil = v-nil}
                {ℛ = ℛ}
                E₁ (cons-iter {y = y} {ys = ys-inner} {acc-rest = acc-rest}
                              {acc-this = acc-this} {ℛ₃ = ℛ₃} {𝒮₂ = 𝒮₂}
                              𝒮' rec F) =
  ≈H-bridge {f = ℛ-op} {g = middle-mor-cons} {m₁≡m₂ = width-ctxt-≡ Γ γ}
            (uip _ _)
            (substP (λ X → _≈_ {x = m₂} {y = n-cons} X middle-mor-cons)
                    (sym (subst₂-∘ (width-ctxt-≡ Γ γ) t-intermediate _ 𝒮₂ outer-pair))
                    (≈-trans {x = m₂} {y = n-cons}
                      (∘-cong {x = m₂} {y = k'-mid} {z = n-cons} factor-A factor-B)
                      (≈-trans {x = m₂} {y = n-cons}
                        (∘-cong {x = m₂} {y = k'-mid} {z = n-cons}
                                (≈-refl {x = k'-mid} {y = n-cons})
                                (≈-sym {x = m₂} {y = k'-mid} prod-m-pair-collapse))
                        (≈-trans {x = m₂} {y = n-cons}
                          (≈-sym {x = m₂} {y = n-cons}
                            (assoc {w = m₂} {x = k''-mid} {y = k'-mid} {z = n-cons} M₂-target _ _))
                          (≈-trans {x = m₂} {y = n-cons}
                            (∘-cong {x = m₂} {y = k''-mid} {z = n-cons}
                                    (≈-refl {x = k''-mid} {y = n-cons}) shuffle-pair-eq)
                            (≈-sym {x = m₂} {y = n-cons}
                              (assoc {w = m₂} {x = m₂ + ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} (y ∷ ys-inner))}
                                     {y = k''-mid} {z = n-cons} _ shuffle-form _)))))))
  where
    m₁ = width-ctxt Γ γ
    m₂ = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)
    n-cons = ⟦ τ₂ ⟧ty .fam .fm
                    (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .idxf .func
                           (⟦_⟧env γ , ⟦_⟧val {list τ₁} (y ∷ ys-inner)))
    k'-mid = (m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y))
           + ⟦ τ₂ ⟧ty .fam .fm (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .idxf .func (⟦_⟧env γ , ⟦_⟧val {list τ₁} ys-inner))
    bridge1-cons : width τ₂ acc-this ≡ n-cons
    bridge1-cons = trans (width-≡ τ₂ acc-this)
                         (cong (⟦ τ₂ ⟧ty .fam .fm)
                               (trans (val-det-iters (cons-iter 𝒮' rec F))
                                      (fold-eq ⟦ M₁ ⟧tm M₂ γ v-nil (val-det E₁) (y ∷ ys-inner))))
    -- Intermediate type bridge: operational widths to model-side fm's, via val-det-iters rec
    -- (acc-rest's val mapping to fold-iter-val) and fold-eq (fold-iter-val to ⟦fold⟧.idxf).
    t-intermediate : ((m₁ + width τ₁ y) + width τ₂ acc-rest) ≡ k'-mid
    t-intermediate =
      cong₂ _+_ (cong₂ _+_ (width-ctxt-≡ Γ γ) (width-≡ τ₁ y))
                (trans (width-≡ τ₂ acc-rest)
                       (cong (⟦ τ₂ ⟧ty .fam .fm)
                             (trans (val-det-iters rec)
                                    (fold-eq ⟦ M₁ ⟧tm M₂ γ v-nil (val-det E₁) ys-inner))))
    -- Model-side M₂.transf at the fold-recursive idx (matches LHS-factored's k'-mid → n-cons).
    M₂-target : k'-mid ⇒ n-cons
    M₂-target = ⟦ M₂ ⟧tm .famf .transf
                       ((⟦_⟧env γ , ⟦_⟧val {τ₁} y) ,
                        ⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .idxf .func
                               (⟦_⟧env γ , ⟦_⟧val {list τ₁} ys-inner))
    -- J-elim coherence: transports ⟦M₂⟧.transf along an idx-level eq in its third arg.
    M₂-transf-coh : ∀ {a b : ⟦ τ₂ ⟧ty .idx .Carrier} (eq : a ≡ b) →
                    _≈_ {x = (m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)) + ⟦ τ₂ ⟧ty .fam .fm b}
                        {y = ⟦ τ₂ ⟧ty .fam .fm
                               (⟦ M₂ ⟧tm .idxf .func
                                       ((⟦_⟧env γ , ⟦_⟧val {τ₁} y) , b))}
                        (subst₂ _⇒_
                          (cong (λ z → (m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y))
                                      + ⟦ τ₂ ⟧ty .fam .fm z) eq)
                          (cong (λ z → ⟦ τ₂ ⟧ty .fam .fm
                                              (⟦ M₂ ⟧tm .idxf .func
                                                      ((⟦_⟧env γ , ⟦_⟧val {τ₁} y) , z))) eq)
                          (⟦ M₂ ⟧tm .famf .transf
                                  ((⟦_⟧env γ , ⟦_⟧val {τ₁} y) , a)))
                        (⟦ M₂ ⟧tm .famf .transf
                                ((⟦_⟧env γ , ⟦_⟧val {τ₁} y) , b))
    M₂-transf-coh {a} refl =
      ≈-refl {x = (m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)) + ⟦ τ₂ ⟧ty .fam .fm a}
             {y = ⟦ τ₂ ⟧ty .fam .fm (⟦ M₂ ⟧tm .idxf .func ((⟦_⟧env γ , ⟦_⟧val {τ₁} y) , a))}

    -- Components for factor A's bridging chain.
    acc-eq : ⟦_⟧val {τ₂} acc-rest ≡ ⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .idxf .func (⟦_⟧env γ , ⟦_⟧val {list τ₁} ys-inner)
    acc-eq = trans (val-det-iters rec) (fold-eq ⟦ M₁ ⟧tm M₂ γ v-nil (val-det E₁) ys-inner)

    context-eq : ((m₁ + width τ₁ y) + width τ₂ acc-rest) ≡
                 ((m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)) + ⟦ τ₂ ⟧ty .fam .fm (⟦_⟧val {τ₂} acc-rest))
    context-eq = cong₂ _+_ (cong₂ _+_ (width-ctxt-≡ Γ γ) (width-≡ τ₁ y)) (width-≡ τ₂ acc-rest)

    F-bridge : width τ₂ acc-this ≡
               ⟦ τ₂ ⟧ty .fam .fm (⟦ M₂ ⟧tm .idxf .func ((⟦_⟧env γ , ⟦_⟧val {τ₁} y) , ⟦_⟧val {τ₂} acc-rest))
    F-bridge = trans (width-≡ τ₂ acc-this) (cong (⟦ τ₂ ⟧ty .fam .fm) (val-det F))

    ext-m : ((m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)) + ⟦ τ₂ ⟧ty .fam .fm (⟦_⟧val {τ₂} acc-rest)) ≡ k'-mid
    ext-m = cong (λ z → (m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)) + ⟦ τ₂ ⟧ty .fam .fm z) acc-eq

    ext-n : ⟦ τ₂ ⟧ty .fam .fm (⟦ M₂ ⟧tm .idxf .func ((⟦_⟧env γ , ⟦_⟧val {τ₁} y) , ⟦_⟧val {τ₂} acc-rest)) ≡ n-cons
    ext-n = cong (λ z → ⟦ τ₂ ⟧ty .fam .fm (⟦ M₂ ⟧tm .idxf .func ((⟦_⟧env γ , ⟦_⟧val {τ₁} y) , z))) acc-eq

    -- Bridge propositional eq: subst₂ via t-intermediate/bridge1-cons ≡ nested subst₂ via context/F + ext.
    factor-A-bridge-≡ : subst₂ _⇒_ t-intermediate bridge1-cons 𝒮₂
                      ≡ subst₂ _⇒_ ext-m ext-n
                                   (subst₂ _⇒_ context-eq F-bridge 𝒮₂)
    factor-A-bridge-≡ =
      trans (cong₂ (λ a b → subst₂ _⇒_ a b 𝒮₂)
                   (uip t-intermediate (trans context-eq ext-m))
                   (uip bridge1-cons (trans F-bridge ext-n)))
            (subst₂-trans-fact context-eq ext-m F-bridge ext-n 𝒮₂)
    factor-A : _≈_ {x = k'-mid} {y = n-cons}
                   (subst₂ _⇒_ t-intermediate bridge1-cons 𝒮₂)
                   M₂-target
    factor-A = substP (λ X → _≈_ {x = k'-mid} {y = n-cons} X M₂-target)
                      (sym factor-A-bridge-≡)
                      (≈-trans {x = k'-mid} {y = n-cons}
                        (subst₂-≈-cong ext-m ext-n (soundness F))
                        (M₂-transf-coh acc-eq))
    -- Components for factor B's structural decomposition.
    inner-eq-m : (m₁ + width τ₁ y) ≡ (m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y))
    inner-eq-m = cong₂ _+_ (width-ctxt-≡ Γ γ) (width-≡ τ₁ y)
    ℛ₃-eq : width τ₂ acc-rest
          ≡ ⟦ τ₂ ⟧ty .fam .fm
              (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .idxf .func
                     (⟦_⟧env γ , ⟦_⟧val {list τ₁} ys-inner))
    ℛ₃-eq = trans (width-≡ τ₂ acc-rest) (cong (⟦ τ₂ ⟧ty .fam .fm) acc-eq)
    𝒮-coerced : m₂ ⇒ ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} (y ∷ ys-inner))
    𝒮-coerced = subst₂ _⇒_ (width-ctxt-≡ Γ γ) (width-≡ (list τ₁) (y ∷ ys-inner)) 𝒮'
    inner-pair : m₁ ⇒ (m₁ + width τ₁ y)
    inner-pair = pairM {x = m₁} {y = m₁} {z = width τ₁ y}
                       (id m₁)
                       (_∘_ {x = m₁} {y = width τ₁ y + width (list τ₁) ys-inner} {z = width τ₁ y}
                            (p₁ {width τ₁ y} {width (list τ₁) ys-inner})
                            𝒮')
    outer-pair : m₁ ⇒ ((m₁ + width τ₁ y) + width τ₂ acc-rest)
    outer-pair = pairM {x = m₁} {y = m₁ + width τ₁ y} {z = width τ₂ acc-rest}
                       inner-pair ℛ₃
    ℛ-op : m₁ ⇒ width τ₂ acc-this
    ℛ-op = _∘_ {x = m₁} {y = (m₁ + width τ₁ y) + width τ₂ acc-rest} {z = width τ₂ acc-this}
                𝒮₂ outer-pair
    middle-mor-cons : m₂ ⇒ n-cons
    middle-mor-cons =
      _∘_ {x = m₂}
          {y = m₂ + ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} (y ∷ ys-inner))}
          {z = n-cons}
          (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .famf .transf
                  (⟦_⟧env γ , ⟦_⟧val {list τ₁} (y ∷ ys-inner)))
          (pairM {x = m₂} {y = m₂}
                 {z = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} (y ∷ ys-inner))}
                 (id m₂) 𝒮-coerced)
    -- Inner factor: subst₂ inner-pair ≈ pair (id m₂) (p₁ ∘ 𝒮-coerced)
    right-inner-≈ : _≈_ {x = m₂} {y = ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                        (subst₂ _⇒_ (width-ctxt-≡ Γ γ) (width-≡ τ₁ y)
                                    (_∘_ {x = m₁} {y = width τ₁ y + width (list τ₁) ys-inner}
                                         {z = width τ₁ y}
                                         (p₁ {width τ₁ y} {width (list τ₁) ys-inner}) 𝒮'))
                        (_∘_ {x = m₂}
                             {y = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} (y ∷ ys-inner))}
                             {z = ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                             (p₁ {⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                                 {⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner)})
                             𝒮-coerced)
    right-inner-≈ =
      substP (λ X → _≈_ {x = m₂} {y = ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)} X
                        (_∘_ {x = m₂}
                             {y = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} (y ∷ ys-inner))}
                             {z = ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                             (p₁ {⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                                 {⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner)})
                             𝒮-coerced))
             (sym (subst₂-∘ {m = m₁} {m' = m₂}
                            {k = width τ₁ y + width (list τ₁) ys-inner}
                            {k' = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} (y ∷ ys-inner))}
                            {n = width τ₁ y} {n' = ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                            (width-ctxt-≡ Γ γ)
                            (width-≡ (list τ₁) (y ∷ ys-inner))
                            (width-≡ τ₁ y)
                            (p₁ {width τ₁ y} {width (list τ₁) ys-inner}) 𝒮'))
             (∘-cong {x = m₂}
                     {y = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} (y ∷ ys-inner))}
                     {z = ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                     (p₁-subst₂ (width-≡ (list τ₁) (y ∷ ys-inner)) (width-≡ τ₁ y))
                     (≈-refl {x = m₂}
                             {y = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} (y ∷ ys-inner))}))
    -- Outer factor: subst₂ ℛ₃ ≈ ⟦fold⟧.transf-rec ∘ pair (id m₂) (p₂ ∘ 𝒮-coerced)
    right-outer-≈ : _≈_ {x = m₂} {y = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner)}
                        (subst₂ _⇒_ (width-ctxt-≡ Γ γ) (width-≡ (list τ₁) ys-inner)
                                    (_∘_ {x = m₁} {y = width τ₁ y + width (list τ₁) ys-inner}
                                         {z = width (list τ₁) ys-inner}
                                         (p₂ {width τ₁ y} {width (list τ₁) ys-inner}) 𝒮'))
                        (_∘_ {x = m₂}
                             {y = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} (y ∷ ys-inner))}
                             {z = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner)}
                             (p₂ {⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                                 {⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner)})
                             𝒮-coerced)
    right-outer-≈ =
      substP (λ X → _≈_ {x = m₂}
                        {y = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner)}
                        X
                        (_∘_ {x = m₂}
                             {y = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} (y ∷ ys-inner))}
                             {z = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner)}
                             (p₂ {⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                                 {⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner)})
                             𝒮-coerced))
             (sym (subst₂-∘ {m = m₁} {m' = m₂}
                            {k = width τ₁ y + width (list τ₁) ys-inner}
                            {k' = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} (y ∷ ys-inner))}
                            {n = width (list τ₁) ys-inner}
                            {n' = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner)}
                            (width-ctxt-≡ Γ γ)
                            (width-≡ (list τ₁) (y ∷ ys-inner))
                            (width-≡ (list τ₁) ys-inner)
                            (p₂ {width τ₁ y} {width (list τ₁) ys-inner}) 𝒮'))
             (∘-cong {x = m₂}
                     {y = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} (y ∷ ys-inner))}
                     {z = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner)}
                     (p₂-subst₂ (width-≡ (list τ₁) (y ∷ ys-inner)) (width-≡ (list τ₁) ys-inner))
                     (≈-refl {x = m₂}
                             {y = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} (y ∷ ys-inner))}))
    factor-B : _≈_ {x = m₂} {y = k'-mid}
                   (subst₂ _⇒_ (width-ctxt-≡ Γ γ) t-intermediate outer-pair)
                   (pairM {x = m₂} {y = m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                          {z = ⟦ τ₂ ⟧ty .fam .fm
                                 (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .idxf .func
                                        (⟦_⟧env γ , ⟦_⟧val {list τ₁} ys-inner))}
                          (pairM {x = m₂} {y = m₂}
                                 {z = ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                                 (id m₂)
                                 (_∘_ {x = m₂}
                                      {y = ⟦ list τ₁ ⟧ty .fam .fm
                                             (⟦_⟧val {list τ₁} (y ∷ ys-inner))}
                                      {z = ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                                      (p₁ {⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                                          {⟦ list τ₁ ⟧ty .fam .fm
                                             (⟦_⟧val {list τ₁} ys-inner)})
                                      𝒮-coerced))
                          (_∘_ {x = m₂}
                               {y = m₂ + ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner)}
                               {z = ⟦ τ₂ ⟧ty .fam .fm
                                      (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .idxf .func (⟦_⟧env γ , ⟦_⟧val {list τ₁} ys-inner))}
                               (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .famf .transf (⟦_⟧env γ , ⟦_⟧val {list τ₁} ys-inner))
                               (pairM {x = m₂} {y = m₂} {z = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner)}
                                      (id m₂)
                                      (_∘_ {x = m₂}
                                           {y = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} (y ∷ ys-inner))}
                                           {z = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner)}
                                           (p₂ {⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                                               {⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner)})
                                           𝒮-coerced))))
    factor-B =
      ≈-trans {x = m₂} {y = k'-mid}
        (subst₂-pair (width-ctxt-≡ Γ γ) inner-eq-m ℛ₃-eq t-intermediate
                     inner-pair ℛ₃)
        (pair-cong {x = m₂} {y = m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                   {z = ⟦ τ₂ ⟧ty .fam .fm
                          (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .idxf .func
                                 (⟦_⟧env γ , ⟦_⟧val {list τ₁} ys-inner))}
                   (≈-trans {x = m₂} {y = m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                      (subst₂-pair (width-ctxt-≡ Γ γ) (width-ctxt-≡ Γ γ) (width-≡ τ₁ y) inner-eq-m
                                   (id m₁) _)
                      (pair-cong {x = m₂} {y = m₂} {z = ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                                 (subst₂-id (width-ctxt-≡ Γ γ))
                                 right-inner-≈))
                   (≈-trans {x = m₂}
                            {y = ⟦ τ₂ ⟧ty .fam .fm
                                   (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .idxf .func
                                          (⟦_⟧env γ , ⟦_⟧val {list τ₁} ys-inner))}
                      (soundness-iters E₁ rec)
                      (∘-cong {x = m₂}
                              {y = m₂ + ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner)}
                              {z = ⟦ τ₂ ⟧ty .fam .fm
                                     (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .idxf .func
                                            (⟦_⟧env γ , ⟦_⟧val {list τ₁} ys-inner))}
                              (≈-refl {x = m₂ + ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner)}
                                      {y = ⟦ τ₂ ⟧ty .fam .fm
                                             (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .idxf .func
                                                    (⟦_⟧env γ , ⟦_⟧val {list τ₁} ys-inner))})
                              (pair-cong {x = m₂} {y = m₂}
                                         {z = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner)}
                                         (≈-refl {x = m₂} {y = m₂})
                                         right-outer-≈))))
    -- "pair of pairs" intermediate: what shuffle ∘ pair (id m₂) 𝒮-coerced reduces to.
    k''-mid = (m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y))
            + (m₂ + ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner))
    pair-of-pairs : m₂ ⇒ k''-mid
    pair-of-pairs =
      pairM {x = m₂}
            {y = m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
            {z = m₂ + ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner)}
            (pairM {x = m₂} {y = m₂} {z = ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                   (id m₂)
                   (_∘_ {x = m₂}
                        {y = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} (y ∷ ys-inner))}
                        {z = ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                        (p₁ {⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                            {⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner)})
                        𝒮-coerced))
            (pairM {x = m₂} {y = m₂}
                   {z = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner)}
                   (id m₂)
                   (_∘_ {x = m₂}
                        {y = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} (y ∷ ys-inner))}
                        {z = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner)}
                        (p₂ {⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                            {⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner)})
                        𝒮-coerced))
    -- prod-m (id) ⟦fold⟧.transf-rec ∘ pair-of-pairs ≈ g₂-form
    -- via pair-compose + pair-cong + id-left
    prod-m-pair-collapse :
      _≈_ {x = m₂} {y = k'-mid}
          (_∘_ {x = m₂} {y = k''-mid} {z = k'-mid}
               (prod-m {x₁ = m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                       {x₂ = m₂ + ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner)}
                       {y₁ = m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                       {y₂ = ⟦ τ₂ ⟧ty .fam .fm
                               (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .idxf .func
                                      (⟦_⟧env γ , ⟦_⟧val {list τ₁} ys-inner))}
                       (id (m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)))
                       (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .famf .transf
                               (⟦_⟧env γ , ⟦_⟧val {list τ₁} ys-inner)))
               pair-of-pairs)
          (pairM {x = m₂}
                 {y = m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                 {z = ⟦ τ₂ ⟧ty .fam .fm
                        (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .idxf .func
                               (⟦_⟧env γ , ⟦_⟧val {list τ₁} ys-inner))}
                 (pairM {x = m₂} {y = m₂} {z = ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                        (id m₂)
                        (_∘_ {x = m₂}
                             {y = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} (y ∷ ys-inner))}
                             {z = ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                             (p₁ {⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                                 {⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner)})
                             𝒮-coerced))
                 (_∘_ {x = m₂}
                      {y = m₂ + ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner)}
                      {z = ⟦ τ₂ ⟧ty .fam .fm
                             (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .idxf .func
                                    (⟦_⟧env γ , ⟦_⟧val {list τ₁} ys-inner))}
                      (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .famf .transf
                              (⟦_⟧env γ , ⟦_⟧val {list τ₁} ys-inner))
                      (pairM {x = m₂} {y = m₂}
                             {z = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner)}
                             (id m₂)
                             (_∘_ {x = m₂}
                                  {y = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} (y ∷ ys-inner))}
                                  {z = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner)}
                                  (p₂ {⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                                      {⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner)})
                                  𝒮-coerced))))
    prod-m-pair-collapse =
      ≈-trans {x = m₂} {y = k'-mid}
        -- pair-natural unfolds prod-m and pushes pair-of-pairs through the pair.
        (pair-natural {w = m₂} {x = k''-mid}
                      {y = m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                      {z = ⟦ τ₂ ⟧ty .fam .fm
                             (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .idxf .func
                                    (⟦_⟧env γ , ⟦_⟧val {list τ₁} ys-inner))}
                      pair-of-pairs _ _)
        (pair-cong {x = m₂}
                   {y = m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                   {z = ⟦ τ₂ ⟧ty .fam .fm
                          (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .idxf .func
                                 (⟦_⟧env γ , ⟦_⟧val {list τ₁} ys-inner))}
                   inner-collapse outer-collapse)
      where
        inner-X : m₂ ⇒ (m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y))
        inner-X = pairM {x = m₂} {y = m₂} {z = ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                        (id m₂)
                        (_∘_ {x = m₂}
                             {y = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} (y ∷ ys-inner))}
                             {z = ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                             (p₁ {⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                                 {⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner)})
                             𝒮-coerced)
        inner-Y : m₂ ⇒ (m₂ + ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner))
        inner-Y = pairM {x = m₂} {y = m₂}
                        {z = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner)}
                        (id m₂)
                        (_∘_ {x = m₂}
                             {y = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} (y ∷ ys-inner))}
                             {z = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner)}
                             (p₂ {⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                                 {⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner)})
                             𝒮-coerced)
        -- (id ∘ p₁) ∘ pair-of-pairs ≈ inner-X
        inner-collapse : _≈_ {x = m₂} {y = m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                             (_∘_ {x = m₂} {y = k''-mid}
                                  {z = m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                                  (_∘_ {x = k''-mid}
                                       {y = m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                                       {z = m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                                       (id (m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)))
                                       (p₁ {m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                                           {m₂ + ⟦ list τ₁ ⟧ty .fam .fm
                                                  (⟦_⟧val {list τ₁} ys-inner)}))
                                  pair-of-pairs)
                             inner-X
        inner-collapse =
          ≈-trans {x = m₂} {y = m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
            (assoc {w = m₂} {x = k''-mid}
                   {y = m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                   {z = m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                   (id (m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y))) _ _)
            (≈-trans {x = m₂} {y = m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
              (∘-cong {x = m₂} {y = m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                      {z = m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                      (≈-refl {x = m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                              {y = m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)})
                      (pair-p₁ {x = m₂}
                               {y = m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                               {z = m₂ + ⟦ list τ₁ ⟧ty .fam .fm
                                          (⟦_⟧val {list τ₁} ys-inner)}
                               inner-X inner-Y))
              (id-left {x = m₂}
                       {y = m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}))
        -- (⟦fold⟧.transf-rec ∘ p₂) ∘ pair-of-pairs ≈ ⟦fold⟧.transf-rec ∘ inner-Y
        outer-collapse : _≈_ {x = m₂}
                             {y = ⟦ τ₂ ⟧ty .fam .fm
                                    (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .idxf .func
                                           (⟦_⟧env γ , ⟦_⟧val {list τ₁} ys-inner))}
                             (_∘_ {x = m₂} {y = k''-mid}
                                  {z = ⟦ τ₂ ⟧ty .fam .fm
                                         (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .idxf .func
                                                (⟦_⟧env γ , ⟦_⟧val {list τ₁} ys-inner))}
                                  (_∘_ {x = k''-mid}
                                       {y = m₂ + ⟦ list τ₁ ⟧ty .fam .fm
                                                  (⟦_⟧val {list τ₁} ys-inner)}
                                       {z = ⟦ τ₂ ⟧ty .fam .fm
                                              (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .idxf .func
                                                     (⟦_⟧env γ , ⟦_⟧val {list τ₁} ys-inner))}
                                       (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .famf .transf
                                               (⟦_⟧env γ , ⟦_⟧val {list τ₁} ys-inner))
                                       (p₂ {m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                                           {m₂ + ⟦ list τ₁ ⟧ty .fam .fm
                                                  (⟦_⟧val {list τ₁} ys-inner)}))
                                  pair-of-pairs)
                             (_∘_ {x = m₂}
                                  {y = m₂ + ⟦ list τ₁ ⟧ty .fam .fm
                                             (⟦_⟧val {list τ₁} ys-inner)}
                                  {z = ⟦ τ₂ ⟧ty .fam .fm
                                         (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .idxf .func
                                                (⟦_⟧env γ , ⟦_⟧val {list τ₁} ys-inner))}
                                  (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .famf .transf
                                          (⟦_⟧env γ , ⟦_⟧val {list τ₁} ys-inner))
                                  inner-Y)
        outer-collapse =
          ≈-trans {x = m₂}
                  {y = ⟦ τ₂ ⟧ty .fam .fm
                         (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .idxf .func
                                (⟦_⟧env γ , ⟦_⟧val {list τ₁} ys-inner))}
            (assoc {w = m₂} {x = k''-mid}
                   {y = m₂ + ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner)}
                   {z = ⟦ τ₂ ⟧ty .fam .fm
                          (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .idxf .func
                                 (⟦_⟧env γ , ⟦_⟧val {list τ₁} ys-inner))}
                   (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .famf .transf
                           (⟦_⟧env γ , ⟦_⟧val {list τ₁} ys-inner)) _ _)
            (∘-cong {x = m₂}
                    {y = m₂ + ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner)}
                    {z = ⟦ τ₂ ⟧ty .fam .fm
                           (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .idxf .func
                                  (⟦_⟧env γ , ⟦_⟧val {list τ₁} ys-inner))}
                    (≈-refl {x = m₂ + ⟦ list τ₁ ⟧ty .fam .fm
                                       (⟦_⟧val {list τ₁} ys-inner)}
                            {y = ⟦ τ₂ ⟧ty .fam .fm
                                   (⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm .idxf .func
                                          (⟦_⟧env γ , ⟦_⟧val {list τ₁} ys-inner))})
                    (pair-p₂ {x = m₂}
                             {y = m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                             {z = m₂ + ⟦ list τ₁ ⟧ty .fam .fm
                                        (⟦_⟧val {list τ₁} ys-inner)}
                             inner-X inner-Y))
    -- shuffle ∘ pair (id m₂) 𝒮-coerced, expanded with shuffle as `pair (prod-m id p₁) (prod-m id p₂)`.
    shuffle-form : (m₂ + ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} (y ∷ ys-inner))) ⇒ k''-mid
    shuffle-form =
      pairM {x = m₂ + ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} (y ∷ ys-inner))}
            {y = m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
            {z = m₂ + ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner)}
            (prod-m {x₁ = m₂} {x₂ = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} (y ∷ ys-inner))}
                    {y₁ = m₂} {y₂ = ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                    (id m₂)
                    (p₁ {⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                        {⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner)}))
            (prod-m {x₁ = m₂} {x₂ = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} (y ∷ ys-inner))}
                    {y₁ = m₂} {y₂ = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner)}
                    (id m₂)
                    (p₂ {⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                        {⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner)}))
    -- pair-of-pairs ≈ shuffle-form ∘ pair (id m₂) 𝒮-coerced (assumes shuffle's def-expansion).
    -- Apply pair-cong + (analog of prod-m-pair-collapse for p₁, p₂) + ≈-sym pair-natural.
    shuffle-pair-eq : _≈_ {x = m₂} {y = k''-mid}
                          pair-of-pairs
                          (_∘_ {x = m₂}
                               {y = m₂ + ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} (y ∷ ys-inner))}
                               {z = k''-mid}
                               shuffle-form
                               (pairM {x = m₂} {y = m₂}
                                      {z = ⟦ list τ₁ ⟧ty .fam .fm
                                             (⟦_⟧val {list τ₁} (y ∷ ys-inner))}
                                      (id m₂) 𝒮-coerced))
    -- Helper: prod-m (id m₂) f ∘ pair (id m₂) 𝒮-coerced ≈ pair (id m₂) (f ∘ 𝒮-coerced)
    prod-m-id-collapse : ∀ {Z} (f : ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} (y ∷ ys-inner)) ⇒ Z) →
                        _≈_ {x = m₂} {y = m₂ + Z}
                            (_∘_ {x = m₂}
                                 {y = m₂ + ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} (y ∷ ys-inner))}
                                 {z = m₂ + Z}
                                 (prod-m {x₁ = m₂}
                                         {x₂ = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} (y ∷ ys-inner))}
                                         {y₁ = m₂} {y₂ = Z}
                                         (id m₂) f)
                                 (pairM {x = m₂} {y = m₂}
                                        {z = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} (y ∷ ys-inner))}
                                        (id m₂) 𝒮-coerced))
                            (pairM {x = m₂} {y = m₂} {z = Z}
                                   (id m₂)
                                   (_∘_ {x = m₂}
                                        {y = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} (y ∷ ys-inner))}
                                        {z = Z}
                                        f 𝒮-coerced))
    prod-m-id-collapse {Z} f =
      ≈-trans {x = m₂} {y = m₂ + Z}
        (pair-natural {w = m₂} {x = m₂ + ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} (y ∷ ys-inner))} {y = m₂} {z = Z}
                      (pairM {x = m₂} {y = m₂} {z = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} (y ∷ ys-inner))}
                             (id m₂) 𝒮-coerced) _ _)
        (pair-cong {x = m₂} {y = m₂} {z = Z}
          (≈-trans {x = m₂} {y = m₂}
            (assoc {w = m₂}
                   {x = m₂ + ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} (y ∷ ys-inner))}
                   {y = m₂} {z = m₂}
                   (id m₂) _ _)
            (≈-trans {x = m₂} {y = m₂}
              (∘-cong {x = m₂} {y = m₂} {z = m₂}
                      (≈-refl {x = m₂} {y = m₂})
                      (pair-p₁ {x = m₂} {y = m₂}
                               {z = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} (y ∷ ys-inner))}
                               (id m₂) 𝒮-coerced))
              (id-left {x = m₂} {y = m₂})))
          (≈-trans {x = m₂} {y = Z}
            (assoc {w = m₂}
                   {x = m₂ + ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} (y ∷ ys-inner))}
                   {y = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} (y ∷ ys-inner))}
                   {z = Z}
                   f _ _)
            (∘-cong {x = m₂} {y = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} (y ∷ ys-inner))} {z = Z}
                    (≈-refl {x = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} (y ∷ ys-inner))} {y = Z})
                    (pair-p₂ {x = m₂} {y = m₂} {z = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} (y ∷ ys-inner))}
                             (id m₂) 𝒮-coerced))))
    shuffle-pair-eq =
      -- pair-of-pairs has inner-X and inner-Y as components.
      -- Apply pair-cong with (≈-sym prod-m-id-collapse) for both p₁ and p₂,
      -- then ≈-sym pair-natural to combine into (pair (prod-m id p₁) (prod-m id p₂)) ∘ pair-id-𝒮 = shuffle-form ∘ pair-id-𝒮.
      ≈-trans {x = m₂} {y = k''-mid}
        (pair-cong {x = m₂}
                   {y = m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                   {z = m₂ + ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner)}
                   (≈-sym {x = m₂} {y = m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                          (prod-m-id-collapse {⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                                              (p₁ {⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                                                  {⟦ list τ₁ ⟧ty .fam .fm
                                                     (⟦_⟧val {list τ₁} ys-inner)})))
                   (≈-sym {x = m₂} {y = m₂ + ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner)}
                          (prod-m-id-collapse {⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner)}
                                              (p₂ {⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                                                  {⟦ list τ₁ ⟧ty .fam .fm
                                                     (⟦_⟧val {list τ₁} ys-inner)}))))
        (≈-sym {x = m₂} {y = k''-mid}
          (pair-natural {w = m₂}
                        {x = m₂ + ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} (y ∷ ys-inner))}
                        {y = m₂ + ⟦ τ₁ ⟧ty .fam .fm (⟦_⟧val {τ₁} y)}
                        {z = m₂ + ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} ys-inner)}
                        (pairM {x = m₂} {y = m₂}
                               {z = ⟦ list τ₁ ⟧ty .fam .fm (⟦_⟧val {list τ₁} (y ∷ ys-inner))}
                               (id m₂) 𝒮-coerced)
                        _ _))

soundness-bop {Γ = Γ} {γ = γ} op-zero []-bases =
  ≈-trans {x = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)} {y = 1}
    (unit-mor∘to-terminal-rebase γ)
    (≈-sym {x = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)} {y = 1} (id-left {x = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)} {y = 1}))
soundness-bop {Γ = Γ} {γ = γ} add  E =
  soundness-bop-numeric add  E
    (≈-sym {x = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)} {y = 1} (id-left {x = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)} {y = 1}))
soundness-bop {Γ = Γ} {γ = γ} mult E =
  soundness-bop-numeric mult E
    (≈-sym {x = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)} {y = 1} (id-left {x = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)} {y = 1}))
soundness-bop {Γ = Γ} {γ = γ} (lbl l) []-bases = into-zero-≈H {Γ} γ refl _ _

soundness-bop-numeric {Γ = Γ} {γ = γ} {Ms = Ms} {ℛ_E = ℛ_E} ω E op-eq =
  ≈H-bridge {f = _∘_ {x = width-ctxt Γ γ} {y = 1 + (1 + 0)} {z = 1} (op-ℛ ω) ℛ_E}
            {g = ⟦ bop ω Ms ⟧tm .famf .transf (⟦_⟧env γ)} {m₁≡m₂ = width-ctxt-≡ Γ γ} {n₁≡n₂ = refl {x = 1}}
            (uip refl _)
            (substP (λ X → _≈_ {x = m} {y = 1}
                               X (⟦ bop ω Ms ⟧tm .famf .transf (⟦_⟧env γ)))
                    (sym (subst₂-∘ (width-ctxt-≡ Γ γ) (refl {x = 1 + (1 + 0)}) (refl {x = 1}) (op-ℛ ω) ℛ_E))
                    (≈-trans {x = m} {y = 1}
                       (∘-cong {x = m} {y = 1 + (1 + 0)} {z = 1}
                               (≈-refl {x = 1 + (1 + 0)} {y = 1})
                               (soundness-bases E))
                       (≈-trans {x = m} {y = 1}
                          (∘-cong {x = m} {y = 1 + (1 + 0)} {z = 1}
                                  (≈-refl {x = 1 + (1 + 0)} {y = 1})
                                  (≈-trans {x = m} {y = 1 + (1 + 0)}
                                     (≈-sym {x = m} {y = 1 + (1 + 0)} (id-left {x = m} {y = 1 + (1 + 0)}))
                                     (∘-cong {x = m} {y = 1 + (1 + 0)} {z = 1 + (1 + 0)}
                                             (≈-sym {x = 1 + (1 + 0)} {y = 1 + 1}
                                               (binary-≈-id {X = ⟦ base number ⟧ty .idx}
                                                 (⟦ Ms ⟧bases .idxf .func (⟦_⟧env γ))))
                                             (≈-refl {x = m} {y = 1 + (1 + 0)}))))
                          (≈-trans {x = m} {y = 1}
                             (≈-sym {x = m} {y = 1}
                                (assoc {w = m} {x = 1 + (1 + 0)} {y = 1 + (1 + 0)} {z = 1} (op-ℛ ω) _ _))
                             (≈-trans {x = m} {y = 1}
                                (∘-cong {x = m} {y = 1 + (1 + 0)} {z = 1}
                                        (≈-sym {x = 1 + (1 + 0)} {y = 1} (id-left {x = 1 + (1 + 0)} {y = 1}))
                                        (≈-refl {x = m} {y = 1 + (1 + 0)}))
                                op-eq)))))
  where m = ⟦ Γ ⟧ctxt .fam .fm (⟦_⟧env γ)
