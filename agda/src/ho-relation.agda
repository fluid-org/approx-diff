{-# OPTIONS --prop --postfix-projections --safe #-}

-- The logical relation between the operational semantics and the higher-order model: values against
-- indices of the interpretation, dependence vectors against elements of the fibre, and the lemmas by
-- recursion on types that the fundamental lemma needs (respect for the setoids, adding the control
-- positions and the control dependence, absorption, transport).
open import Level using (0ℓ; lift)
open import Data.Nat using (ℕ; suc; _+_; _⊔_; _≤_; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m⊔n≤o⇒m≤o; m⊔n≤o⇒n≤o)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong) renaming (subst to ≡-subst)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
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
open import cmon-enriched using (Biproduct)
import language-interpretation

module ho-relation
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A) (ctrl-weight : Setoid.Carrier A)
  (Sig : Signature 0ℓ) (ℐ : Interpretation S Sig)
  (let module S = CommutativeSemiring S)
  (+-idem : ∀ x → (x S.+ x) S.≈ x)
  (let module S⊑ = commutative-monoid.AdditivePreorder S.additive (λ {x} → +-idem x))
  (c-idem : (ctrl-weight S.· ctrl-weight) S.≈ ctrl-weight)
  (c-bound : ∀ x → (ctrl-weight S.· x) S⊑.⊑ ctrl-weight)
  where

open Signature Sig
open Interpretation ℐ
open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.evaluation Sig S ℐ ctrl-weight

open import value-interpretation S ctrl-weight Sig ℐ public using (module model; module interp; val-idx; env-idx)
open model public using (𝔽; mat; module lifting-SemiMod; module SemiMod)
open lifting-SemiMod using (L; payload-L; prod-m; elim-root; strong-Lmap)
open SemiMod public using (Semimodule; _⇒_)
open Semimodule public using () renaming (Carrier to ∣_∣)
open SemiMod._⇒_ public using (func; func-resp-≈; preserve-+; preserve-·; preserve-ze)
open SemiMod._≈m_ public using (func-eq)

module M = matrix.Mat S
module Fam⟨𝒟⟩μ = model.Fam⟨𝒟⟩μ
open Fam⟨𝒟⟩μ public using (Obj; Mor; idx; fam; fm; idxf; famf; Section; Lf; elimF;
                          strong-Lf-map-transf; _≃_; module _≃_; preserves-section;
                          module preserves-section; module Fam-P; module Fam-cat)
open HasStrongCoproducts Fam⟨𝒟⟩μ.strongCoproducts public using (copair; in₁; in₂)
module ΠP = HasSetoidProducts model.SPmod

open preserves-section public using (at)
open indexed-family.Fam public using (subst)
open indexed-family._⇒f_ public using (transf)
open prop-setoid._⇒_ public using () renaming (func to sfunc; func-resp-≈ to sfunc-resp-≈)

private
  module LI = language-interpretation Sig 0ℓ 0ℓ
    SemiMod.terminal SemiMod.cmon-enriched SemiMod.biproduct SemiMod.𝕀 model.SemiModExp
    interp.δ∅𝒟 interp.𝒟𝟙ty interp.𝒟unit-pt interp.𝒟-Sig-model model.ctrl-weight-endo
    (λ {X} {Y} → model.exp-section {X} {Y}) interp.𝒟𝟙ty-section interp.𝒟-sort-section

open LI public using (⟦_⟧ty; ⟦_⟧ctxt; ⟦_⟧tm; ⟦_⟧tms; ⟦_⟧var; ctrl-dep; unit-section; roll-mor;
                      unroll-mor; preserves-unroll-ctrl-dep; ≡-to-⇒; roll-unroll; unroll-roll;
                      fold-map; fold-map-var; fold-map-unit; fold-map-base; fold-map-arrow;
                      fold-map-rec; fold-map-mu; fold-map-pair; fold-map-pair-L;
                      fold-map-inl; fold-map-inl-L; fold-map-inr; fold-map-inr-L)
open Section public using (at)

module prim = model.sig-model.prim Sig ℐ
open prim public using (collect)
open interp public using (𝒟-arg-product)
module Fam⟨𝒞⟩μ = model.Fam⟨𝒞⟩μ

⟦_⟧ : type 0 → Obj
⟦ τ ⟧ = ⟦ τ ⟧ty (λ ())

module IxO (X : Obj) = Setoid (X .idx)

IxO : Obj → Set
IxO X = IxO.Carrier X

FibO : (X : Obj) → IxO X → Semimodule
FibO X x = X .fam .fm x

module FibO X x = Semimodule (FibO X x)

module 𝔽 n = Semimodule (𝔽 n)

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

module FibC Γ i = Semimodule (FibC Γ i)

open model public using (app-+; app-+ₘ; app-∘; app-εₘ; app-I; app-congₘ; app-congᵥ; app-p₁; app-p₂; app-in₁; app-in₂; app-pair; concat-pad)
  renaming (app to ap)
open CommutativeSemiring S public using (ι; ε; +-cong; ·-cong; +-lunit; +-runit; +-comm; +-assoc; ·-lunit; ·-runit; ·-comm; ε-annihilₗ; ε-annihilᵣ)
  renaming (_≈_ to _≈s_; _+_ to _+ₛ_; _·_ to _·ₛ_)
open Setoid A public using () renaming (refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)
open M public using (Σ-cong; Σ-unit; Σ-ε; _∘_; _+ₘ_; εₘ; ≈ₘ-refl; ≈ₘ-sym; ≈ₘ-trans; ⟨_,_⟩) renaming (Σ to Σₛ)

Payload : ∀ σ τ → Ix (σ [→] τ) → Semimodule
Payload σ τ f = model.exp._⟶_ ⟦ σ ⟧ ⟦ τ ⟧ .fam .fm f

module Payload σ τ f = Semimodule (Payload σ τ f)

evalΠ : ∀ σ τ (f : Ix (σ [→] τ)) (j : Ix σ) → Payload σ τ f ⇒ Fib τ (f .idxf .sfunc j)
evalΠ σ τ f j = ΠP.evalΠ (⟦ τ ⟧ .fam indexed-family.[ f .idxf ]) j

body-input : ∀ {Γ' σ} (γ' : Env Γ') (v : Val σ) → Setoid.Carrier A →
             ∣ 𝔽 (width-env γ') ∣ → ∣ 𝔽 (width v) ∣ → ∣ 𝔽 (suc (width-env γ' + width v)) ∣
body-input γ' v s x z zero    = s
body-input γ' v s x z (suc k) =
  𝔽._+_ (width-env γ' + width v)
    (ap (M.in₁ {width-env γ'} {width v}) x)
    (ap (M.in₂ {width-env γ'} {width v}) z) k

ctrl-dep-at : ∀ τ (i : Ix τ) → Setoid.Carrier A → ∣ Fib τ i ∣
ctrl-dep-at τ i s = ctrl-dep τ .at i .func s

fib-+-idem : ∀ τ i {x} → Semimodule._≈_ (Fib τ i) (Semimodule._+_ (Fib τ i) x x) x
fib-+-idem τ i =
  X.trans (X.+-cong (X.sym X.·-unit) (X.sym X.·-unit))
          (X.trans (X.sym X.+-distribʳ) (X.trans (X.·-cong (+-idem ι) X.refl) X.·-unit))
  where module X = Semimodule (Fib τ i)

module Fib τ i where
  open Semimodule (Fib τ i) public
  open commutative-monoid.AdditivePreorder additive (fib-+-idem τ i) public

bound₁ : ∀ {m n o} → m ⊔ n ≤ o → m ≤ o
bound₁ = m⊔n≤o⇒m≤o _ _

bound₂ : ∀ {m n o} → m ⊔ n ≤ o → n ≤ o
bound₂ = m⊔n≤o⇒n≤o _ _

bound-μ : ∀ (τ : type 1) {N} → arr-depth (μ τ) ≤ N → arr-depth (τ [ μ τ ]) ≤ N
bound-μ τ = ≤-trans (arr-depth-unfold τ)

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

ValRel : ∀ τ → Val τ → Ix τ → Set
ValRel τ = ValRel′ (arr-depth τ) τ ≤-refl

DepRel : ∀ τ {v : Val τ} {i : Ix τ} → ValRel τ v i → ∣ 𝔽 (width v) ∣ → ∣ Fib τ i ∣ → Prop
DepRel τ = DepRel′ (arr-depth τ) τ ≤-refl

DepRel⊑ : ∀ τ {v : Val τ} {i : Ix τ} → ValRel τ v i → Setoid.Carrier A → ∣ 𝔽 (width v) ∣ → ∣ Fib τ i ∣ → Prop
DepRel⊑ τ = DepRel⊑′ (arr-depth τ) τ ≤-refl

ValRel′-bounds : ∀ {N N'} τ {p : arr-depth τ ≤ N} {p' : arr-depth τ ≤ N'} {v : Val τ} {i : Ix τ} →
                 (ValRel′ N τ p v i → ValRel′ N' τ p' v i) × (ValRel′ N' τ p' v i → ValRel′ N τ p v i)
ValRel′-bounds unit {v = unit} = (λ r → r) , (λ r → r)
ValRel′-bounds (base s) {v = const a} = (λ r → r) , (λ r → r)
ValRel′-bounds (σ [+] τ) {v = inl v} =
  (λ (i' , r , e) → i' , proj₁ (ValRel′-bounds σ) r , e) , (λ (i' , r , e) → i' , proj₂ (ValRel′-bounds σ) r , e)
ValRel′-bounds (σ [+] τ) {v = inr v} =
  (λ (i' , r , e) → i' , proj₁ (ValRel′-bounds τ) r , e) , (λ (i' , r , e) → i' , proj₂ (ValRel′-bounds τ) r , e)
ValRel′-bounds (σ [×] τ) {v = pair v u} {i , j} =
  (λ (r , r') → proj₁ (ValRel′-bounds σ) r , proj₁ (ValRel′-bounds τ) r') ,
  (λ (r , r') → proj₂ (ValRel′-bounds σ) r , proj₂ (ValRel′-bounds τ) r')
ValRel′-bounds {suc N} {suc N'} (σ [→] τ) {s≤s p} {s≤s p'} {clo γ' t} =
  (λ r rv D → proj₁ (ValRel′-bounds τ) (r (proj₂ (ValRel′-bounds σ) rv) D)) ,
  (λ r rv D → proj₂ (ValRel′-bounds τ) (r (proj₁ (ValRel′-bounds σ) rv) D))
ValRel′-bounds (μ τ) {v = roll v} = ValRel′-bounds (τ [ μ τ ])

ValRel-at-bound : ∀ {N N'} τ {p : arr-depth τ ≤ N} {p' : arr-depth τ ≤ N'} {v : Val τ} {i : Ix τ} →
                  ValRel′ N τ p v i → ValRel′ N' τ p' v i
ValRel-at-bound τ = proj₁ (ValRel′-bounds τ)

DepRel′-bounds : ∀ {N N'} τ {p : arr-depth τ ≤ N} {p' : arr-depth τ ≤ N'} {v : Val τ} {i : Ix τ} →
                 (∀ (r : ValRel′ N τ p v i) {o d} →
                    DepRel′ N τ p r o d → DepRel′ N' τ p' (proj₁ (ValRel′-bounds τ) r) o d) ∧
                 (∀ (r : ValRel′ N' τ p' v i) {o d} →
                    DepRel′ N' τ p' r o d → DepRel′ N τ p (proj₂ (ValRel′-bounds τ) r) o d)
DepRel′-bounds unit {v = unit} = (λ r h → h) , (λ r h → h)
DepRel′-bounds (base s) {v = const a} = (λ r h → h) , (λ r h → h)
DepRel′-bounds (σ [+] τ) {v = inl v} =
  (λ (i' , r , ⟪ e ⟫) (h₀ , h) → h₀ , proj₁ (DepRel′-bounds σ) r h) ,
  (λ (i' , r , ⟪ e ⟫) (h₀ , h) → h₀ , proj₂ (DepRel′-bounds σ) r h)
DepRel′-bounds (σ [+] τ) {v = inr v} =
  (λ (i' , r , ⟪ e ⟫) (h₀ , h) → h₀ , proj₁ (DepRel′-bounds τ) r h) ,
  (λ (i' , r , ⟪ e ⟫) (h₀ , h) → h₀ , proj₂ (DepRel′-bounds τ) r h)
DepRel′-bounds (σ [×] τ) {v = pair v u} {i , j} =
  (λ (r , r') (h₀ , (h₁ , h₂)) → h₀ , (proj₁ (DepRel′-bounds σ) r h₁ , proj₁ (DepRel′-bounds τ) r' h₂)) ,
  (λ (r , r') (h₀ , (h₁ , h₂)) → h₀ , (proj₂ (DepRel′-bounds σ) r h₁ , proj₂ (DepRel′-bounds τ) r' h₂))
DepRel′-bounds {suc N} {suc N'} (σ [→] τ) {s≤s p} {s≤s p'} {clo γ' t} =
  (λ r (h₀ , hc) → h₀ , λ s' rv z y hz D →
     proj₁ (DepRel′-bounds τ) _ (hc s' (proj₂ (ValRel′-bounds σ) rv) z y (bwd rv hz) D)) ,
  (λ r (h₀ , hc) → h₀ , λ s' rv z y hz D →
     proj₂ (DepRel′-bounds τ) _ (hc s' (proj₁ (ValRel′-bounds σ) rv) z y (fwd rv hz) D))
  where
    fwd : ∀ {v j} (rv : ValRel′ N σ (bound₁ p) v j) {s o d} → DepRel⊑′ N σ (bound₁ p) rv s o d →
          DepRel⊑′ N' σ (bound₁ p') (proj₁ (ValRel′-bounds σ) rv) s o d
    fwd rv (m , (dm , h)) = m , (dm , proj₁ (DepRel′-bounds σ) rv h)
    bwd : ∀ {v j} (rv : ValRel′ N' σ (bound₁ p') v j) {s o d} → DepRel⊑′ N' σ (bound₁ p') rv s o d →
          DepRel⊑′ N σ (bound₁ p) (proj₂ (ValRel′-bounds σ) rv) s o d
    bwd rv (m , (dm , h)) = m , (dm , proj₂ (DepRel′-bounds σ) rv h)
DepRel′-bounds (μ τ) {v = roll v} =
  (λ r h → proj₁ (DepRel′-bounds (τ [ μ τ ])) r h) , (λ r h → proj₂ (DepRel′-bounds (τ [ μ τ ])) r h)

DepRel-at-bound : ∀ {N N'} τ {p : arr-depth τ ≤ N} {p' : arr-depth τ ≤ N'} {v : Val τ} {i : Ix τ}
                  (r : ValRel′ N τ p v i) {o d} → DepRel′ N τ p r o d → DepRel′ N' τ p' (ValRel-at-bound τ r) o d
DepRel-at-bound τ = proj₁ (DepRel′-bounds τ)

DepRel⊑-at-bound : ∀ {N N'} τ {p : arr-depth τ ≤ N} {p' : arr-depth τ ≤ N'} {v : Val τ} {i : Ix τ}
                   (r : ValRel′ N τ p v i) {s o d} → DepRel⊑′ N τ p r s o d → DepRel⊑′ N' τ p' (ValRel-at-bound τ r) s o d
DepRel⊑-at-bound τ r (m , (dm , h)) = m , (dm , DepRel-at-bound τ r h)

-- A primitive's arguments need no relations of their own: the index at a tuple of arguments is a
-- tuple of sort indices, so the value relation is equality in sort-vals-setoid, and the fibre is
-- 𝔽 (bases-width is) on both sides, so the vector relation is equality, as at a base sort.

data EnvValRel : ∀ {Γ} → Env Γ → IxC Γ → Set where
  emp : EnvValRel emp (lift tt)
  _·_ : ∀ {Γ τ} {γ : Env Γ} {v : Val τ} {gi i} → EnvValRel γ gi → ValRel τ v i → EnvValRel (γ · v) (gi , i)

infixl 30 _·_

EnvDepRel : ∀ {Γ} {γ : Env Γ} {gi} → EnvValRel γ gi → Setoid.Carrier A →
            ∣ 𝔽 (width-env γ) ∣ → ∣ FibC Γ gi ∣ → Prop
EnvDepRel emp s x g = prop.⊤
EnvDepRel (_·_ {τ = τ} {γ = γ} {v = v} rγ r) s x g =
  EnvDepRel rγ s (ap (M.p₁ {width-env γ} {width v}) x) (proj₁ g) ∧
  DepRel⊑ τ r s (ap (M.p₂ {width-env γ} {width v}) x) (proj₂ g)

inputs : ∀ {Γ} (γ : Env Γ) → Setoid.Carrier A → ∣ 𝔽 (width-env γ) ∣ → ∣ 𝔽 (suc (width-env γ)) ∣
inputs γ s x zero    = s
inputs γ s x (suc k) = x k

map-input : ∀ {Γ} (γ : Env Γ) {n} → Setoid.Carrier A → ∣ 𝔽 (width-env γ) ∣ → ∣ 𝔽 n ∣ →
            ∣ 𝔽 (suc (width-env γ) + n) ∣
map-input γ {n} s x o l =
  ap (M.in₁ {suc (width-env γ)} {n}) (inputs γ s x) l +ₛ ap (M.in₂ {suc (width-env γ)} {n}) o l

ctrl = ctrl-weight

ap-ctrl-row : ∀ {n} (s : Setoid.Carrier A) (k : Fin n) → ap ctrl-row (λ _ → s) k ≈s (ctrl ·ₛ s)
ap-ctrl-row {n} s k = +-runit

ctrl-lift : ∀ {n} (g : M.Matrix n 1) (s : Setoid.Carrier A) (k : Fin (suc n)) →
            ap (⟨ ctrl-row {1} , g ⟩) (λ _ → s) k ≈s M.concat {1} {n} (λ _ → ctrl ·ₛ s) (ap g (λ _ → s)) k
ctrl-lift {n} g s zero = ≈-trans (app-pair {1} {1} {n} ctrl-row g (λ _ → s) zero) (ap-ctrl-row {1} s zero)
ctrl-lift {n} g s (suc k) = app-pair {1} {1} {n} ctrl-row g (λ _ → s) (suc k)

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

ap-wctrl : ∀ {m n} (y : ∣ 𝔽 (suc m) ∣) (k : Fin n) → ap (wctrl {m} {n}) y k ≈s (ctrl ·ₛ y zero)
ap-wctrl {m} {n} y k =
  ≈-trans (app-∘ (ctrl-row {n}) (M.p₁ {1} {m}) y k)
          (≈-trans (app-congᵥ (ctrl-row {n}) (ap-p₁₁ {m} y) k) (ap-ctrl-row {n} (y zero) k))

ap-⊕ : ∀ {m a b} (f : M.Matrix 1 a) (g : M.Matrix b m) (y : ∣ 𝔽 (a + m) ∣) (k : Fin (suc b)) →
       ap (f ⊕ g) y k ≈s M.concat {1} {b} (ap f (ap (M.p₁ {a} {m}) y)) (ap g (ap (M.p₂ {a} {m}) y)) k
ap-⊕ {m} {a} {b} f g y zero =
  ≈-trans (app-pair {a + m} {1} {b} (f ∘ M.p₁ {a} {m}) (g ∘ M.p₂ {a} {m}) y zero) (app-∘ f (M.p₁ {a} {m}) y zero)
ap-⊕ {m} {a} {b} f g y (suc k) =
  ≈-trans (app-pair {a + m} {1} {b} (f ∘ M.p₁ {a} {m}) (g ∘ M.p₂ {a} {m}) y (suc k)) (app-∘ g (M.p₂ {a} {m}) y k)

ap-⊕₁ : ∀ {m b} (f : M.Matrix 1 1) (g : M.Matrix b m) (y : ∣ 𝔽 (suc m) ∣) (k : Fin (suc b)) →
        ap (f ⊕ g) y k ≈s M.concat {1} {b} (ap f (λ _ → y zero)) (ap g (λ l → y (suc l))) k
ap-⊕₁ {m} f g y zero = ≈-trans (ap-⊕ {m} {1} f g y zero) (app-congᵥ f (ap-p₁₁ {m} y) zero)
ap-⊕₁ {m} f g y (suc k) = ≈-trans (ap-⊕ {m} {1} f g y (suc k)) (app-congᵥ g (ap-p₂₁ {m} y) k)

ctrl-dep-unit : ∀ i s → ctrl-dep-at unit i s zero ≈s (ctrl ·ₛ s)
ctrl-dep-unit i s =
  ≈-trans (+-cong (·-cong +-runit ≈-refl) ≈-refl)
          (≈-trans +-runit (≈-trans ·-lunit +-runit))

ctrl-dep-base : ∀ {σ} i s (k : Fin (sort-width σ)) → ctrl-dep-at (base σ) i s k ≈s (ctrl ·ₛ s)
ctrl-dep-base i s k = ≈-trans +-runit (≈-trans ·-lunit +-runit)

ctrl-dep-inj₁ : ∀ {σ τ} (i : Ix σ) s →
          (proj₁ (ctrl-dep-at (σ [+] τ) (inj₁ i) s) ≈s (ctrl ·ₛ s)) ∧
          Fib._≈_ σ i (proj₂ (ctrl-dep-at (σ [+] τ) (inj₁ i) s)) (ctrl-dep-at σ i s)
ctrl-dep-inj₁ {σ} i s = ≈-trans +-runit +-runit , Fib.+-lunit σ i

ctrl-dep-inj₂ : ∀ {σ τ} (i : Ix τ) s →
          (proj₁ (ctrl-dep-at (σ [+] τ) (inj₂ i) s) ≈s (ctrl ·ₛ s)) ∧
          Fib._≈_ τ i (proj₂ (ctrl-dep-at (σ [+] τ) (inj₂ i) s)) (ctrl-dep-at τ i s)
ctrl-dep-inj₂ {σ} {τ} i s = ≈-trans +-runit +-runit , Fib.+-lunit τ i

ctrl-dep-pair : ∀ {σ τ} (i : Ix σ) (j : Ix τ) s →
          (proj₁ (ctrl-dep-at (σ [×] τ) (i , j) s) ≈s (ctrl ·ₛ s)) ∧
          (Fib._≈_ σ i (proj₁ (proj₂ (ctrl-dep-at (σ [×] τ) (i , j) s))) (ctrl-dep-at σ i s) ∧
           Fib._≈_ τ j (proj₂ (proj₂ (ctrl-dep-at (σ [×] τ) (i , j) s))) (ctrl-dep-at τ j s))
ctrl-dep-pair {σ} {τ} i j s =
  ≈-trans +-runit +-runit ,
  (Fib.trans σ i (Fib.+-lunit σ i) (Fib.+-runit σ i) ,
   Fib.trans τ j (Fib.+-lunit τ j) (Fib.+-lunit τ j))

ctrl-dep-clo : ∀ {σ τ} (f : Ix (σ [→] τ)) s →
         (proj₁ (ctrl-dep-at (σ [→] τ) f s) ≈s (ctrl ·ₛ s)) ∧
         Payload._≈_ σ τ f (proj₂ (ctrl-dep-at (σ [→] τ) f s))
           (Payload.ε σ τ f)
ctrl-dep-clo {σ} {τ} f s = ≈-trans +-runit +-runit , Payload.+-lunit σ τ f {Payload.ε σ τ f}

payload-ctrl-dep : ∀ σ τ (f : Ix (σ [→] τ)) s (d : ∣ Fib (σ [→] τ) f ∣) →
                   Payload._≈_ σ τ f (proj₂ (Fib._+_ (σ [→] τ) f (ctrl-dep-at (σ [→] τ) f s) d)) (proj₂ d)
payload-ctrl-dep σ τ f s d =
  Payload.trans σ τ f
    {proj₂ (Fib._+_ (σ [→] τ) f (ctrl-dep-at (σ [→] τ) f s) d)}
    {Payload._+_ σ τ f (Payload.ε σ τ f) (proj₂ d)} {proj₂ d}
    (Payload.+-cong σ τ f {proj₂ (ctrl-dep-at (σ [→] τ) f s)} {Payload.ε σ τ f} {proj₂ d} {proj₂ d}
      (proj₂ (ctrl-dep-clo {σ} {τ} f s)) (Payload.refl σ τ f {proj₂ d}))
    (Payload.+-lunit σ τ f {proj₂ d})

ctrl-dep-natural : ∀ τ {i i' : Ix τ} (e : Ix._≈_ τ i i') s →
             Fib._≈_ τ i' (⟦ τ ⟧ .fam .subst e .func (ctrl-dep-at τ i s)) (ctrl-dep-at τ i' s)
ctrl-dep-natural τ e s = ctrl-dep τ .Section.at-natural e .func-eq ≈-refl

body-input-resp : ∀ {Γ' σ} (γ' : Env Γ') (v : Val σ) {s s' x x' z} →
                  s ≈s s' → (∀ k → x k ≈s x' k) → ∀ k →
                  body-input γ' v s x z k ≈s body-input γ' v s' x' z k
body-input-resp γ' v es ecs zero    = es
body-input-resp γ' v es ecs (suc k) = +-cong (app-congᵥ (M.in₁ {width-env γ'} {width v}) ecs k) ≈-refl

DepRel⊑-resp-ctrl′ : ∀ {N} τ (p : arr-depth τ ≤ N) {v : Val τ} {i : Ix τ} (r : ValRel′ N τ p v i)
                     {s s'} {o : ∣ 𝔽 (width v) ∣} {d} →
                     s ≈s s' → DepRel⊑′ N τ p r s o d → DepRel⊑′ N τ p r s' o d
DepRel⊑-resp-ctrl′ τ p {i = i} r es (m , (dm , h)) =
  m , (Fib.trans τ i (Fib.+-cong τ i (Fib.refl τ i) (ctrl-dep τ .at i .func-resp-≈ (≈-sym es)))
                   (Fib.trans τ i dm (ctrl-dep τ .at i .func-resp-≈ es)) , h)

DepRel⊑-resp-ctrl : ∀ τ {v : Val τ} {i : Ix τ} (r : ValRel τ v i) {s s'} {o : ∣ 𝔽 (width v) ∣} {d} →
                    s ≈s s' → DepRel⊑ τ r s o d → DepRel⊑ τ r s' o d
DepRel⊑-resp-ctrl τ = DepRel⊑-resp-ctrl′ τ ≤-refl

DepRel-resp′ : ∀ {N} τ (p : arr-depth τ ≤ N) {v : Val τ} {i : Ix τ} (r : ValRel′ N τ p v i)
               {o o' : ∣ 𝔽 (width v) ∣} {d d' : ∣ Fib τ i ∣} →
               (∀ k → o k ≈s o' k) → Fib._≈_ τ i d d' → DepRel′ N τ p r o d → DepRel′ N τ p r o' d'
DepRel-resp′ unit p {unit} r eo ed h k = ≈-trans (≈-sym (eo k)) (≈-trans (h k) (ed k))
DepRel-resp′ (base s) p {const a} r eo ed h k = ≈-trans (≈-sym (eo k)) (≈-trans (h k) (ed k))
DepRel-resp′ (σ [+] τ) p {inl v} {i} (i' , r , ⟪ e ⟫) {d = d} {d'} eo ed (h₀ , h) =
  let ed' = ⟦ σ [+] τ ⟧ .fam .subst {i} {inj₁ i'} e .func-resp-≈ ed in
  ≈-trans (≈-sym (eo zero)) (≈-trans h₀ (proj₁ ed')) ,
  DepRel-resp′ σ (bound₁ p) r (λ k → eo (suc k)) (proj₂ ed') h
DepRel-resp′ (σ [+] τ) p {inr v} {i} (i' , r , ⟪ e ⟫) {d = d} {d'} eo ed (h₀ , h) =
  let ed' = ⟦ σ [+] τ ⟧ .fam .subst {i} {inj₂ i'} e .func-resp-≈ ed in
  ≈-trans (≈-sym (eo zero)) (≈-trans h₀ (proj₁ ed')) ,
  DepRel-resp′ τ (bound₂ p) r (λ k → eo (suc k)) (proj₂ ed') h
DepRel-resp′ (σ [×] τ) p {pair v u} {i , j} (r , r') eo (ed₀ , (ed₁ , ed₂)) (h₀ , (h₁ , h₂)) =
  ≈-trans (≈-sym (eo zero)) (≈-trans h₀ ed₀) ,
  (DepRel-resp′ σ (bound₁ p) r (app-congᵥ (M.p₁ {width v} {width u}) (λ k → eo (suc k))) ed₁ h₁ ,
   DepRel-resp′ τ (bound₂ p) r' (app-congᵥ (M.p₂ {width v} {width u}) (λ k → eo (suc k))) ed₂ h₂)
DepRel-resp′ {suc N} (σ [→] τ) (s≤s p) {clo γ' t} {f} r {o} {o'} {d} {d'} eo (ed₀ , ed₂) (h₀ , hc) =
  ≈-trans (≈-sym (eo zero)) (≈-trans h₀ ed₀) ,
  λ s' {v} {j} rv z y hz {u} {U} D →
    DepRel-resp′ τ (bound₂ p) (r rv D)
      (app-congᵥ U (body-input-resp γ' v (+-cong ≈-refl (eo zero)) (λ k → eo (suc k))))
      (Fib.+-cong τ (f .idxf .sfunc j)
         (ctrl-dep τ .at (f .idxf .sfunc j) .func-resp-≈ (+-cong ≈-refl (eo zero)))
         (Fib.+-cong τ (f .idxf .sfunc j)
            (evalΠ σ τ f j .func-resp-≈
               {proj₂ d} {proj₂ d'} ed₂)
            (Fib.refl τ (f .idxf .sfunc j) {f .famf .transf j .func y})))
      (hc s' rv z y (DepRel⊑-resp-ctrl′ σ (bound₁ p) rv (+-cong ≈-refl (≈-sym (eo zero))) hz) D)
DepRel-resp′ (μ τ) p {roll v} {i} r {o} {o'} {d} {d'} eo ed h =
  DepRel-resp′ (τ [ μ τ ]) (bound-μ τ p) r eo (unroll-mor τ .famf .transf i .func-resp-≈ {d} {d'} ed) h

DepRel-resp : ∀ τ {v : Val τ} {i : Ix τ} (r : ValRel τ v i) {o o' : ∣ 𝔽 (width v) ∣} {d d' : ∣ Fib τ i ∣} →
              (∀ k → o k ≈s o' k) → Fib._≈_ τ i d d' → DepRel τ r o d → DepRel τ r o' d'
DepRel-resp τ = DepRel-resp′ τ ≤-refl

subst-ctrl-dep+ : ∀ τ {i i' : Ix τ} (e : Ix._≈_ τ i i') s d →
            Fib._≈_ τ i' (⟦ τ ⟧ .fam .subst e .func (Fib._+_ τ i (ctrl-dep-at τ i s) d))
                       (Fib._+_ τ i' (ctrl-dep-at τ i' s) (⟦ τ ⟧ .fam .subst e .func d))
subst-ctrl-dep+ τ {i} {i'} e s d =
  Fib.trans τ i' (⟦ τ ⟧ .fam .subst e .preserve-+ {ctrl-dep-at τ i s} {d})
               (Fib.+-cong τ i' (ctrl-dep-natural τ e s) (Fib.refl τ i'))

ctrl-add′ : ∀ {N} τ (p : arr-depth τ ≤ N) {v : Val τ} {i : Ix τ} (r : ValRel′ N τ p v i)
            (s : Setoid.Carrier A) {o : ∣ 𝔽 (width v) ∣} {d : ∣ Fib τ i ∣} → DepRel′ N τ p r o d →
            DepRel′ N τ p r (λ k → ap (ctrl-of v) (λ _ → s) k +ₛ o k) (Fib._+_ τ i (ctrl-dep-at τ i s) d)
ctrl-add′ unit p {unit} {i} r s h zero =
  +-cong (≈-trans (ap-ctrl-row {1} s zero) (≈-sym (ctrl-dep-unit i s))) (h zero)
ctrl-add′ (base σ) p {const a} {i} r s h k =
  +-cong (≈-trans (ap-ctrl-row {sort-width σ} s k) (≈-sym (ctrl-dep-base i s k))) (h k)
ctrl-add′ (σ [+] τ) p {inl v} {i} (i' , r , ⟪ e ⟫) s {o} {d} (h₀ , h) =
  let e+ = subst-ctrl-dep+ (σ [+] τ) {i} {inj₁ i'} e s d
      d' = ⟦ σ [+] τ ⟧ .fam .subst {i} {inj₁ i'} e .func d
  in
  ≈-trans (+-cong (ctrl-lift (ctrl-of v) s zero) h₀)
          (≈-sym (≈-trans (proj₁ e+) (+-cong (proj₁ (ctrl-dep-inj₁ {σ} {τ} i' s)) ≈-refl))) ,
  DepRel-resp′ σ (bound₁ p) r
    (λ k → +-cong (≈-sym (ctrl-lift (ctrl-of v) s (suc k))) ≈-refl)
    (Fib.sym σ i' (Fib.trans σ i' (proj₂ e+)
                              (Fib.+-cong σ i' (proj₂ (ctrl-dep-inj₁ {σ} {τ} i' s)) (Fib.refl σ i'))))
    (ctrl-add′ σ (bound₁ p) r s h)
ctrl-add′ (σ [+] τ) p {inr v} {i} (i' , r , ⟪ e ⟫) s {o} {d} (h₀ , h) =
  let e+ = subst-ctrl-dep+ (σ [+] τ) {i} {inj₂ i'} e s d
  in
  ≈-trans (+-cong (ctrl-lift (ctrl-of v) s zero) h₀)
          (≈-sym (≈-trans (proj₁ e+) (+-cong (proj₁ (ctrl-dep-inj₂ {σ} {τ} i' s)) ≈-refl))) ,
  DepRel-resp′ τ (bound₂ p) r
    (λ k → +-cong (≈-sym (ctrl-lift (ctrl-of v) s (suc k))) ≈-refl)
    (Fib.sym τ i' (Fib.trans τ i' (proj₂ e+)
                              (Fib.+-cong τ i' (proj₂ (ctrl-dep-inj₂ {σ} {τ} i' s)) (Fib.refl τ i'))))
    (ctrl-add′ τ (bound₂ p) r s h)
ctrl-add′ (σ [×] τ) p {pair v u} {i , j} (r , r') s {o} {d} (h₀ , (h₁ , h₂)) =
  ≈-trans (+-cong (ctrl-lift (⟨ ctrl-of v , ctrl-of u ⟩) s zero) h₀)
          (+-cong (≈-sym (proj₁ (ctrl-dep-pair {σ} {τ} i j s))) ≈-refl) ,
  (DepRel-resp′ σ (bound₁ p) r
     (λ k → ≈-trans (+-cong (≈-trans (≈-sym (app-congₘ (HasProducts.pair-p₁ M.products (ctrl-of v) (ctrl-of u)) (λ _ → s) k))
                                     (app-∘ (M.p₁ {width v} {width u}) ⟨ ctrl-of v , ctrl-of u ⟩ (λ _ → s) k))
                            ≈-refl)
              (≈-trans (≈-sym (app-+ (M.p₁ {width v} {width u}) _ _ k))
                       (app-congᵥ (M.p₁ {width v} {width u})
                          (λ l → +-cong (≈-sym (ctrl-lift (⟨ ctrl-of v , ctrl-of u ⟩) s (suc l))) ≈-refl) k)))
     (Fib.+-cong σ i (Fib.sym σ i (proj₁ (proj₂ (ctrl-dep-pair {σ} {τ} i j s)))) (Fib.refl σ i))
     (ctrl-add′ σ (bound₁ p) r s h₁) ,
   DepRel-resp′ τ (bound₂ p) r'
     (λ k → ≈-trans (+-cong (≈-trans (≈-sym (app-congₘ (HasProducts.pair-p₂ M.products (ctrl-of v) (ctrl-of u)) (λ _ → s) k))
                                     (app-∘ (M.p₂ {width v} {width u}) ⟨ ctrl-of v , ctrl-of u ⟩ (λ _ → s) k))
                            ≈-refl)
              (≈-trans (≈-sym (app-+ (M.p₂ {width v} {width u}) _ _ k))
                       (app-congᵥ (M.p₂ {width v} {width u})
                          (λ l → +-cong (≈-sym (ctrl-lift (⟨ ctrl-of v , ctrl-of u ⟩) s (suc l))) ≈-refl) k)))
     (Fib.+-cong τ j (Fib.sym τ j (proj₂ (proj₂ (ctrl-dep-pair {σ} {τ} i j s)))) (Fib.refl τ j))
     (ctrl-add′ τ (bound₂ p) r' s h₂))
ctrl-add′ {suc N} (σ [→] τ) (s≤s p) {clo γ' t} {f} r s {o} {d} (h₀ , hc) =
  ≈-trans (+-cong (ctrl-lift {width-env γ'} εₘ s zero) h₀)
          (+-cong (≈-sym (proj₁ (ctrl-dep-clo {σ} {τ} f s))) ≈-refl) ,
  λ s' {v} {j} rv z y hz {u} {U} D →
    let e₀ : ((s' +ₛ (ctrl ·ₛ s)) +ₛ o zero) ≈s (s' +ₛ (ap (ctrl-of (clo γ' t)) (λ _ → s) zero +ₛ o zero))
        e₀ = ≈-trans +-assoc (+-cong ≈-refl (+-cong (≈-sym (ctrl-lift {width-env γ'} εₘ s zero)) ≈-refl))
    in
    DepRel-resp′ τ (bound₂ p) (r rv D)
      (app-congᵥ U (body-input-resp γ' v e₀
         (λ k → ≈-sym (≈-trans (+-cong (ctrl-lift {width-env γ'} εₘ s (suc k)) ≈-refl)
                               (≈-trans (+-cong (app-εₘ {width-env γ'} {1} (λ _ → s) k) ≈-refl) +-lunit)))))
      (Fib.+-cong τ (f .idxf .sfunc j)
         (ctrl-dep τ .at (f .idxf .sfunc j) .func-resp-≈ e₀)
         (Fib.+-cong τ (f .idxf .sfunc j)
            (evalΠ σ τ f j .func-resp-≈
               {proj₂ d} {proj₂ (Fib._+_ (σ [→] τ) f (ctrl-dep-at (σ [→] τ) f s) d)}
               (Payload.sym σ τ f {proj₂ (Fib._+_ (σ [→] τ) f (ctrl-dep-at (σ [→] τ) f s) d)} {proj₂ d}
                  (payload-ctrl-dep σ τ f s d)))
            (Fib.refl τ (f .idxf .sfunc j) {f .famf .transf j .func y})))
      (hc (s' +ₛ (ctrl ·ₛ s)) rv z y (DepRel⊑-resp-ctrl′ σ (bound₁ p) rv (≈-sym e₀) hz) D)
ctrl-add′ (μ τ) p {roll v} {i} r s {o} {d} h =
  DepRel-resp′ (τ [ μ τ ]) (bound-μ τ p) r (λ k → ≈-refl)
    (Fib.sym (τ [ μ τ ]) i'
      (Fib.trans (τ [ μ τ ]) i'
        (unroll-mor τ .famf .transf i .preserve-+ {ctrl-dep-at (μ τ) i s} {d})
        (Fib.+-cong (τ [ μ τ ]) i'
          (preserves-unroll-ctrl-dep τ .at i .func-eq {s} {s} ≈-refl)
          (Fib.refl (τ [ μ τ ]) i'))))
    (ctrl-add′ (τ [ μ τ ]) (bound-μ τ p) r s h)
  where i' = unroll-mor τ .idxf .sfunc i

ctrl-add : ∀ τ {v : Val τ} {i : Ix τ} (r : ValRel τ v i) (s : Setoid.Carrier A)
           {o : ∣ 𝔽 (width v) ∣} {d : ∣ Fib τ i ∣} → DepRel τ r o d →
           DepRel τ r (λ k → ap (ctrl-of v) (λ _ → s) k +ₛ o k) (Fib._+_ τ i (ctrl-dep-at τ i s) d)
ctrl-add τ = ctrl-add′ τ ≤-refl

lookup-val : ∀ {Γ τ} (x : Γ ∋ τ) {γ : Env Γ} {gi} → EnvValRel γ gi →
             ValRel τ (lookup x γ) (⟦ x ⟧var .idxf .sfunc gi)
lookup-val zero     (rγ · r) = r
lookup-val (succ x) (rγ · r) = lookup-val x rγ

DepRel⊑-resp : ∀ τ {v : Val τ} {i : Ix τ} (r : ValRel τ v i) s {o o' : ∣ 𝔽 (width v) ∣} {d} →
               (∀ k → o k ≈s o' k) → DepRel⊑ τ r s o d → DepRel⊑ τ r s o' d
DepRel⊑-resp τ {i = i} r s eo (m , (dm , h)) = m , (dm , DepRel-resp τ r eo (Fib.refl τ i) h)

lookup-dep : ∀ {Γ τ} (x : Γ ∋ τ) {γ : Env Γ} {gi} (rγ : EnvValRel γ gi) s xs g →
             EnvDepRel rγ s xs g →
             DepRel⊑ τ (lookup-val x rγ) s (ap (proj-var x γ) xs) (⟦ x ⟧var .famf .transf gi .func g)
lookup-dep zero (rγ · r) s xs g (_ , h) = h
lookup-dep {τ = τ} (succ x) {γ · v} {gi , i} (rγ · r) s xs g (h , _) =
  DepRel⊑-resp τ (lookup-val x rγ) s
    (λ k → ≈-sym (app-∘ (proj-var x γ) (M.p₁ {width-env γ} {width v}) xs k))
    (lookup-dep x rγ s (ap (M.p₁ {width-env γ} {width v}) xs) (proj₁ g) h)

DepRel⊑-ctrl : ∀ τ {v : Val τ} {i : Ix τ} (r : ValRel τ v i) s {o : ∣ 𝔽 (width v) ∣} {d} →
               DepRel⊑ τ r s o d →
               DepRel τ r (λ k → ap (ctrl-of v) (λ _ → s) k +ₛ o k) (Fib._+_ τ i (ctrl-dep-at τ i s) d)
DepRel⊑-ctrl τ {i = i} r s {o} {d} (m , (dm , h)) =
  DepRel-resp τ r (λ k → ≈-refl)
    (Fib.trans τ i (Fib.+-cong τ i (Fib.refl τ i) (Fib.+-comm τ i))
    (Fib.trans τ i (Fib.sym τ i (Fib.+-assoc τ i)) (Fib.+-cong τ i (Fib.trans τ i (Fib.+-comm τ i) dm) (Fib.refl τ i))))
    (ctrl-add τ r s h)

idx-eq : ∀ {X Y : Obj} {f g : Mor X Y} → f ≃ g → ∀ x →
         IxO._≈_ Y (f .idxf .sfunc x) (g .idxf .sfunc x)
idx-eq {X} E x = E ._≃_.idxf-eq .prop-setoid._≃m_.func-eq {x} {x} (IxO.refl X {x})

fam-eq : ∀ {X Y : Obj} {f g : Mor X Y} (E : f ≃ g) x (a : ∣ FibO X x ∣) →
         FibO._≈_ Y (g .idxf .sfunc x)
           (Y .fam .subst (idx-eq E x) .func (f .famf .transf x .func a)) (g .famf .transf x .func a)
fam-eq {X} E x a = E ._≃_.famf-eq .indexed-family._≃f_.transf-eq {x} .func-eq (FibO.refl X x {a})

idx-eq-at : ∀ σ τ {f f' : Ix (σ [→] τ)} → Ix._≈_ (σ [→] τ) f f' → ∀ j →
            Ix._≈_ τ (f .idxf .sfunc j) (f' .idxf .sfunc j)
idx-eq-at σ τ E j = idx-eq E j

ValRel-resp′ : ∀ {N} τ (p : arr-depth τ ≤ N) {v : Val τ} {i i' : Ix τ} →
               Ix._≈_ τ i i' → ValRel′ N τ p v i → ValRel′ N τ p v i'
ValRel-resp′ unit p {unit} e r = tt
ValRel-resp′ (base σ) p {const a} {i} {i'} e ⟪ e₀ ⟫ =
  ⟪ Setoid.trans (sort-index σ) {i'} {i} {a} (Setoid.sym (sort-index σ) {i} {i'} e) e₀ ⟫
ValRel-resp′ (σ [+] τ) p {inl v} {i} {i'} e (i₀ , r , ⟪ e₀ ⟫) =
  i₀ , r , ⟪ Ix.trans (σ [+] τ) {i'} {i} {inj₁ i₀} (Ix.sym (σ [+] τ) {i} {i'} e) e₀ ⟫
ValRel-resp′ (σ [+] τ) p {inr v} {i} {i'} e (i₀ , r , ⟪ e₀ ⟫) =
  i₀ , r , ⟪ Ix.trans (σ [+] τ) {i'} {i} {inj₂ i₀} (Ix.sym (σ [+] τ) {i} {i'} e) e₀ ⟫
ValRel-resp′ (σ [×] τ) p {pair v u} {i , j} {i' , j'} (e₁ , e₂) (r , r') =
  ValRel-resp′ σ (bound₁ p) e₁ r , ValRel-resp′ τ (bound₂ p) e₂ r'
ValRel-resp′ {suc N} (σ [→] τ) (s≤s p) {clo γ' t} {f} {f'} e r {v} {j} rv {u} {U} D =
  ValRel-resp′ τ (bound₂ p) (idx-eq-at σ τ e j) (r rv D)
ValRel-resp′ (μ τ) p {roll v} {i} {i'} e r =
  ValRel-resp′ (τ [ μ τ ]) (bound-μ τ p) (unroll-mor τ .idxf .sfunc-resp-≈ {i} {i'} e) r

ValRel-resp : ∀ τ {v : Val τ} {i i' : Ix τ} → Ix._≈_ τ i i' → ValRel τ v i → ValRel τ v i'
ValRel-resp τ = ValRel-resp′ τ ≤-refl

bpair-elt : ∀ {X Y Z : Semimodule} (f : X ⇒ Y) (g : X ⇒ Z) (x : ∣ X ∣) →
            Semimodule._≈_ (SemiMod._⊕_ Y Z) (Fam⟨𝒟⟩μ.pair f g .func x) (f .func x , g .func x)
bpair-elt {X} {Y} {Z} f g x = Semimodule.+-runit Y , Semimodule.+-lunit Z

Fpair-elt : ∀ {X Y Z : Obj} (f : Mor X Y) (g : Mor X Z) (x : IxO X) (z : ∣ FibO X x ∣) →
            FibO._≈_ (Fam-P.prod Y Z) (f .idxf .sfunc x , g .idxf .sfunc x)
              (Fam-P.pair f g .famf .transf x .func z)
              (f .famf .transf x .func z , g .famf .transf x .func z)
Fpair-elt f g x z = bpair-elt (f .famf .transf x) (g .famf .transf x) z

Fprod-subst-elt : ∀ {X Y : Obj} {x x' : IxO X} {y y' : IxO Y}
                  (e₁ : IxO._≈_ X x x') (e₂ : IxO._≈_ Y y y')
                  (z : ∣ FibO X x ∣) (w : ∣ FibO Y y ∣) →
                  FibO._≈_ (Fam-P.prod X Y) (x' , y')
                    (Fam-P.prod X Y .fam .subst (e₁ , e₂) .func (z , w))
                    (X .fam .subst e₁ .func z , Y .fam .subst e₂ .func w)
Fprod-subst-elt {X} {Y} {x} {x'} {y} {y'} e₁ e₂ z w =
  bpair-elt {SemiMod._⊕_ (FibO X x) (FibO Y y)} {FibO X x'} {FibO Y y'}
    (SemiMod._∘_ (X .fam .subst e₁) (SemiMod.p₁ {FibO X x} {FibO Y y}))
    (SemiMod._∘_ (Y .fam .subst e₂) (SemiMod.p₂ {FibO X x} {FibO Y y})) (z , w)

subst-refl : ∀ (X : Obj) {x : IxO X} (e : IxO._≈_ X x x) (d : ∣ FibO X x ∣) →
             FibO._≈_ X x (X .fam .subst e .func d) d
subst-refl X {x} e d = X .fam .indexed-family.Fam.refl* .func-eq (FibO.refl X x {d})

subst-trans : ∀ (X : Obj) {x y z : IxO X} (e₁ : IxO._≈_ X x y) (e₂ : IxO._≈_ X y z)
              (d : ∣ FibO X x ∣) →
              FibO._≈_ X z (X .fam .subst (IxO.trans X e₁ e₂) .func d)
                                            (X .fam .subst e₂ .func (X .fam .subst e₁ .func d))
subst-trans X {x} {y} {z} e₁ e₂ d = X .fam .indexed-family.Fam.trans* {x} {y} {z} e₂ e₁ .func-eq (FibO.refl X x {d})

transf-natural : ∀ {X Y : Obj} (f : Mor X Y) {x x' : IxO X} (e : IxO._≈_ X x x')
                 (z : ∣ FibO X x ∣) →
                 FibO._≈_ Y (f .idxf .sfunc x')
                   (f .famf .transf x' .func (X .fam .subst e .func z))
                   (Y .fam .subst (f .idxf .sfunc-resp-≈ e) .func (f .famf .transf x .func z))
transf-natural {X} f {x} {x'} e z = f .famf .indexed-family._⇒f_.natural {x} {x'} e .func-eq (FibO.refl X x {z})

payload-prod-elt : ∀ {G X : Semimodule} (γe : ∣ G ∣) (a : Setoid.Carrier A) (y : ∣ X ∣) →
                   Semimodule._≈_ (SemiMod._⊕_ G X)
                     (prod-m (SemiMod.id G) (payload-L {X}) .func (γe , (a , y))) (γe , y)
payload-prod-elt {G} {X} γe a y =
  Semimodule.trans (SemiMod._⊕_ G X)
    (bpair-elt {SemiMod._⊕_ G (L X)} {G} {X} (SemiMod._∘_ (SemiMod.id G) (SemiMod.p₁ {G} {L X}))
       (SemiMod._∘_ (payload-L {X}) (SemiMod.p₂ {G} {L X})) (γe , (a , y)))
    (Semimodule.refl G {γe} , Semimodule.+-lunit X {y})

elim-root-elt : ∀ {G X Y : Semimodule} (k : SemiMod.𝕀 ⇒ Y) (r : SemiMod._⊕_ G X ⇒ Y)
                (γe : ∣ G ∣) (a : Setoid.Carrier A) (y : ∣ X ∣) →
                Semimodule._≈_ Y (elim-root k r .func (γe , (a , y)))
                                 (Semimodule._+_ Y (r .func (γe , y)) (k .func a))
elim-root-elt {G} {X} {Y} k r γe a y =
  Semimodule.+-cong Y (r .func-resp-≈ (payload-prod-elt {G} {X} γe a y)) (k .func-resp-≈ +-runit)

strong-Lmap-elt : ∀ {G X Y : Semimodule} (r : SemiMod._⊕_ G X ⇒ Y) (γe : ∣ G ∣) (a : Setoid.Carrier A) (y : ∣ X ∣) →
                  Semimodule._≈_ (L Y) (strong-Lmap r .func (γe , (a , y))) (a , r .func (γe , y))
strong-Lmap-elt {G} {X} {Y} r γe a y =
  ≈-trans +-lunit +-runit ,
  Semimodule.trans Y (Semimodule.+-cong Y (r .func-resp-≈ (payload-prod-elt {G} {X} γe a y)) (Semimodule.refl Y))
                     (Semimodule.+-runit Y)

elimF-elt : ∀ {Γ' X C : Obj} (cC : Section C) (f : Mor (Fam-P.prod Γ' X) C)
            {γi : IxO Γ'} {xi : IxO X}
            (γe : ∣ FibO Γ' γi ∣) (a : Setoid.Carrier A) (y : ∣ FibO X xi ∣) →
            FibO._≈_ C (f .idxf .sfunc (γi , xi))
              (elimF cC f .famf .transf (γi , xi) .func (γe , (a , y)))
              (FibO._+_ C (f .idxf .sfunc (γi , xi))
                (f .famf .transf (γi , xi) .func (γe , y))
                (cC .at (f .idxf .sfunc (γi , xi)) .func a))
elimF-elt cC f {γi} {xi} γe a y = elim-root-elt (cC .at (f .idxf .sfunc (γi , xi))) (f .famf .transf (γi , xi)) γe a y

elim-elt : ∀ {Γ' X C : Obj} (cC : Section C) (body : Mor (Fam-P.prod Γ' X) C) (f : Mor Γ' (Lf X))
           {γi : IxO Γ'} (γe : ∣ FibO Γ' γi ∣) →
           FibO._≈_ C (body .idxf .sfunc (γi , f .idxf .sfunc γi))
             (Fam-cat._∘_ (elimF cC body) (Fam-P.pair (Fam-cat.id Γ') f) .famf .transf γi .func γe)
             (FibO._+_ C (body .idxf .sfunc (γi , f .idxf .sfunc γi))
               (body .famf .transf (γi , f .idxf .sfunc γi) .func (γe , proj₂ (f .famf .transf γi .func γe)))
               (cC .at (body .idxf .sfunc (γi , f .idxf .sfunc γi)) .func (proj₁ (f .famf .transf γi .func γe))))
elim-elt {Γ'} {X} {C} cC body f {γi} γe =
  FibO.trans C (body .idxf .sfunc (γi , f .idxf .sfunc γi))
    (elimF cC body .famf .transf (γi , f .idxf .sfunc γi) .func-resp-≈
       {Fam-P.pair (Fam-cat.id Γ') f .famf .transf γi .func γe} {γe , f .famf .transf γi .func γe}
       (Fpair-elt {Γ'} {Γ'} {Lf X} (Fam-cat.id Γ') f γi γe))
    (elimF-elt {Γ'} {X} {C} cC body {γi} {f .idxf .sfunc γi} γe (proj₁ (f .famf .transf γi .func γe)) (proj₂ (f .famf .transf γi .func γe)))

ctrl-dep-linear : ∀ τ (i : Ix τ) s s' →
            Fib._≈_ τ i (ctrl-dep-at τ i (s +ₛ s')) (Fib._+_ τ i (ctrl-dep-at τ i s) (ctrl-dep-at τ i s'))
ctrl-dep-linear τ i s s' = ctrl-dep τ .at i .preserve-+ {s} {s'}

ctrl-dep-c : ∀ τ (i : Ix τ) s → Fib._≈_ τ i (ctrl-dep-at τ i (ctrl ·ₛ s)) (ctrl-dep-at τ i s)
ctrl-dep-c τ i s =
  unit-section τ (λ ()) (λ ()) .at i .func-resp-≈
    (+-cong (≈-trans (≈-sym S.·-assoc) (·-cong c-idem ≈-refl)) ≈-refl)

⊑ctrl-dep-mono : ∀ τ (i : Ix τ) s s' m → Fib._⊑_ τ i m (ctrl-dep-at τ i s) → Fib._⊑_ τ i m (ctrl-dep-at τ i (s' +ₛ (ctrl ·ₛ s)))
⊑ctrl-dep-mono τ i s s' m dm =
  Fib.⊑-trans τ i dm (Fib.⊑-trans τ i (IsJoin.inr (Fib.∨-isJoin τ i))
    (Fib.≈→⊑ τ i (Fib.sym τ i (Fib.trans τ i (ctrl-dep-linear τ i s' (ctrl ·ₛ s)) (Fib.+-cong τ i (Fib.refl τ i) (ctrl-dep-c τ i s))))))

DepRel⊑-mono : ∀ τ {v : Val τ} {i : Ix τ} (r : ValRel τ v i) s s' {o d} →
               DepRel⊑ τ r s o d → DepRel⊑ τ r (s' +ₛ (ctrl ·ₛ s)) o d
DepRel⊑-mono τ {i = i} r s s' (m , (dm , h)) = m , (⊑ctrl-dep-mono τ i s s' m dm , h)

EnvDepRel-mono : ∀ {Γ} {γ : Env Γ} {gi} (rγ : EnvValRel γ gi) s s' {x g} →
                 EnvDepRel rγ s x g → EnvDepRel rγ (s' +ₛ (ctrl ·ₛ s)) x g
EnvDepRel-mono emp s s' rel = prop.tt
EnvDepRel-mono (_·_ {τ = τ} rγ r) s s' (rel , h) = EnvDepRel-mono rγ s s' rel , DepRel⊑-mono τ r s s' h

ap-p₁-++ : ∀ {m n} (x : ∣ 𝔽 m ∣) (z : ∣ 𝔽 n ∣) k →
           ap (M.p₁ {m} {n}) (λ l → ap (M.in₁ {m} {n}) x l +ₛ ap (M.in₂ {m} {n}) z l) k ≈s x k
ap-p₁-++ {m} {n} x z k =
  ≈-trans (app-congᵥ (M.p₁ {m} {n}) (λ l → ≈-trans (+-cong (app-in₁ x l) (app-in₂ z l)) (concat-pad x z l)) k)
          (≈-trans (app-p₁ {m} {n} (M.concat x z) k) (M.split₁-concat x z k))

ap-p₂-++ : ∀ {m n} (x : ∣ 𝔽 m ∣) (z : ∣ 𝔽 n ∣) k →
           ap (M.p₂ {m} {n}) (λ l → ap (M.in₁ {m} {n}) x l +ₛ ap (M.in₂ {m} {n}) z l) k ≈s z k
ap-p₂-++ {m} {n} x z k =
  ≈-trans (app-congᵥ (M.p₂ {m} {n}) (λ l → ≈-trans (+-cong (app-in₁ x l) (app-in₂ z l)) (concat-pad x z l)) k)
          (≈-trans (app-p₂ {m} {n} (M.concat x z) k) (M.split₂-concat x z k))

ap-++-p : ∀ {m n} (w : ∣ 𝔽 (m + n) ∣) k →
          (ap (M.in₁ {m} {n}) (ap (M.p₁ {m} {n}) w) k +ₛ ap (M.in₂ {m} {n}) (ap (M.p₂ {m} {n}) w) k) ≈s w k
ap-++-p {m} {n} w k =
  ≈-trans (+-cong (≈-sym (app-∘ (M.in₁ {m} {n}) (M.p₁ {m} {n}) w k)) (≈-sym (app-∘ (M.in₂ {m} {n}) (M.p₂ {m} {n}) w k)))
  (≈-trans (≈-sym (app-+ₘ (M.in₁ {m} {n} ∘ M.p₁ {m} {n}) (M.in₂ {m} {n} ∘ M.p₂ {m} {n}) w k))
  (≈-trans (app-congₘ (M.biproduct m n .Biproduct.id-+) w k) (app-I w k)))

ap-∥-pair : ∀ {r a b m} (A : M.Matrix r a) (B : M.Matrix r b) (C : M.Matrix a m) (D : M.Matrix b m) (y : ∣ 𝔽 m ∣) (k : Fin r) →
            ap ((A M.∥ B) ∘ ⟨ C , D ⟩) y k ≈s (ap A (ap C y) k +ₛ ap B (ap D y) k)
ap-∥-pair A B C D y k =
  ≈-trans (app-congₘ (M.∥-pair A B C D) y k)
  (≈-trans (app-+ₘ (A ∘ C) (B ∘ D) y k) (+-cong (app-∘ A C y k) (app-∘ B D y k)))

ap-rec-inputs : ∀ {Γ} (γ : Env Γ) {m σ'} (v' : Val σ')
                (F : M.Matrix (width v') (suc (width-env γ) + m)) s x (o : ∣ 𝔽 m ∣) k →
                ap (rec-inputs γ v' ∘ ⟨ M.I , F ⟩) (map-input γ s x o) k ≈s
                inputs (γ · v') s
                  (λ l → ap (M.in₁ {width-env γ} {width v'}) x l +ₛ
                         ap (M.in₂ {width-env γ} {width v'}) (ap F (map-input γ s x o)) l) k
ap-rec-inputs {Γ} γ {m} v' F s x o k =
  ≈-trans (ap-∥-pair ((M.I {1} ⊕ M.in₁ {n} {p}) ∘ M.p₁ {suc n} {m}) (M.in₂ {1} {n + p} ∘ M.in₂ {n} {p}) M.I F y k)
  (≈-trans (+-cong left (app-∘ (M.in₂ {1} {n + p}) (M.in₂ {n} {p}) oF k)) (final k))
  where
  n = width-env γ
  p = width v'
  y = map-input γ s x o
  oF = ap F y
  left : ap ((M.I {1} ⊕ M.in₁ {n} {p}) ∘ M.p₁ {suc n} {m}) (ap M.I y) k ≈s ap (M.I {1} ⊕ M.in₁ {n} {p}) (inputs γ s x) k
  left =
    ≈-trans (app-∘ (M.I {1} ⊕ M.in₁ {n} {p}) (M.p₁ {suc n} {m}) (ap M.I y) k)
            (app-congᵥ (M.I {1} ⊕ M.in₁ {n} {p})
               (λ l → ≈-trans (app-congᵥ (M.p₁ {suc n} {m}) (app-I y) l) (ap-p₁-++ (inputs γ s x) o l)) k)
  final : ∀ k → (ap (M.I {1} ⊕ M.in₁ {n} {p}) (inputs γ s x) k +ₛ ap (M.in₂ {1} {n + p}) (ap (M.in₂ {n} {p}) oF) k) ≈s
                inputs (γ · v') s (λ l → ap (M.in₁ {n} {p}) x l +ₛ ap (M.in₂ {n} {p}) oF l) k
  final zero =
    ≈-trans (+-cong (≈-trans (ap-⊕ M.I (M.in₁ {n} {p}) (inputs γ s x) zero)
                             (≈-trans (app-I (ap (M.p₁ {1} {n}) (inputs γ s x)) zero) (ap-p₁₁ (inputs γ s x) zero)))
                    (app-in₂ {1} {n + p} (ap (M.in₂ {n} {p}) oF) zero))
            +-runit
  final (suc k) =
    +-cong (≈-trans (ap-⊕ M.I (M.in₁ {n} {p}) (inputs γ s x) (suc k))
                    (app-congᵥ (M.in₁ {n} {p}) (ap-p₂₁ (inputs γ s x)) k))
           (app-in₂ {1} (ap (M.in₂ {n} {p}) oF) (suc k))

ap-body-inputs : ∀ {Γ Γ' σ} (γ : Env Γ) (γ' : Env Γ') (v : Val σ)
                 (R : M.Matrix (suc (width-env γ')) (suc (width-env γ))) (T : M.Matrix (width v) (suc (width-env γ))) s x k →
                 ap (body-inputs γ γ' v ∘ ⟨ ⟨ M.I , R ⟩ , T ⟩) (inputs γ s x) k ≈s
                 body-input γ' v ((ctrl ·ₛ s) +ₛ ap R (inputs γ s x) zero) (λ l → ap R (inputs γ s x) (suc l)) (ap T (inputs γ s x)) k
ap-body-inputs γ γ' v R T s x k =
  ≈-trans (ap-∥-pair (from-ctrl M.∥ from-closure) from-argument ⟨ M.I , R ⟩ T y k)
  (≈-trans (+-cong (≈-trans (≈-sym (app-∘ (from-ctrl M.∥ from-closure) ⟨ M.I , R ⟩ y k))
                            (≈-trans (ap-∥-pair from-ctrl from-closure M.I R y k)
                                     (+-cong (app-congᵥ from-ctrl (app-I y) k) ≈-refl)))
                   ≈-refl)
           (body-at k))
  where
  n' = width-env γ'
  p = width v
  y = inputs γ s x
  o = ap R y
  z = ap T y
  from-ctrl : M.Matrix (suc (n' + p)) (suc (width-env γ))
  from-ctrl = M.in₁ {1} ∘ wctrl
  from-closure : M.Matrix (suc (n' + p)) (suc n')
  from-closure = M.I {1} ⊕ M.in₁ {n'} {p}
  from-argument : M.Matrix (suc (n' + p)) p
  from-argument = M.in₂ {1} ∘ M.in₂ {n'} {p}
  body-at : ∀ l → ((ap from-ctrl y l +ₛ ap from-closure o l) +ₛ ap from-argument z l) ≈s
             body-input γ' v ((ctrl ·ₛ s) +ₛ o zero) (λ l' → o (suc l')) z l
  body-at zero =
    ≈-trans (+-cong (+-cong (≈-trans (app-∘ (M.in₁ {1} {n' + p}) wctrl y zero)
                                     (≈-trans (app-in₁ {1} {n' + p} (ap wctrl y) zero) (ap-wctrl {width-env γ} {1} y zero)))
                            (≈-trans (ap-⊕₁ {n'} M.I (M.in₁ {n'} {p}) o zero) (app-I {1} (λ _ → o zero) zero)))
                    (≈-trans (app-∘ (M.in₂ {1}) (M.in₂ {n'} {p}) z zero) (app-in₂ {1} {n' + p} _ zero)))
            +-runit
  body-at (suc l) =
    +-cong (≈-trans (+-cong (≈-trans (app-∘ (M.in₁ {1} {n' + p}) wctrl y (suc l)) (app-in₁ {1} {n' + p} (ap wctrl y) (suc l)))
                            (ap-⊕₁ {n'} M.I (M.in₁ {n'} {p}) o (suc l)))
                    +-lunit)
           (≈-trans (app-∘ (M.in₂ {1}) (M.in₂ {n'} {p}) z (suc l)) (app-in₂ {1} {n' + p} _ (suc l)))

ap-branch-inputs : ∀ {Γ τ'} (γ : Env Γ) (v : Val τ') (R : M.Matrix (suc (width v)) (suc (width-env γ))) s x k →
                   ap (branch-inputs γ v ∘ ⟨ M.I , R ⟩) (inputs γ s x) k ≈s
                   inputs (γ · v) (ap R (inputs γ s x) zero +ₛ (ctrl ·ₛ s))
                     (λ l → ap (M.in₁ {width-env γ} {width v}) x l +ₛ
                            ap (M.in₂ {width-env γ} {width v}) (λ m → ap R (inputs γ s x) (suc m)) l) k
ap-branch-inputs γ v R s x k =
  ≈-trans (ap-∥-pair (ctrl-row {1} ⊕ M.in₁ {n} {p}) (M.I {1} ⊕ M.in₂ {n} {p}) M.I R y k)
  (≈-trans (+-cong (app-congᵥ (ctrl-row {1} ⊕ M.in₁ {n} {p}) (app-I y) k) ≈-refl) (branch-at k))
  where
  n = width-env γ
  p = width v
  y = inputs γ s x
  branch-at : ∀ l → (ap (ctrl-row {1} ⊕ M.in₁ {n} {p}) y l +ₛ ap (M.I {1} ⊕ M.in₂ {n} {p}) (ap R y) l) ≈s
             inputs (γ · v) (ap R y zero +ₛ (ctrl ·ₛ s))
               (λ m → ap (M.in₁ {n} {p}) x m +ₛ ap (M.in₂ {n} {p}) (λ m' → ap R y (suc m')) m) l
  branch-at zero =
    ≈-trans (+-cong (≈-trans (ap-⊕₁ {n} (ctrl-row {1}) (M.in₁ {n} {p}) y zero) (ap-ctrl-row {1} s zero))
                    (≈-trans (ap-⊕₁ {p} M.I (M.in₂ {n} {p}) (ap R y) zero) (app-I {1} (λ _ → ap R y zero) zero)))
            +-comm
  branch-at (suc m) =
    +-cong (ap-⊕₁ {n} (ctrl-row {1}) (M.in₁ {n} {p}) y (suc m))
           (ap-⊕₁ {p} M.I (M.in₂ {n} {p}) (ap R y) (suc m))

ap-sub-inputs : ∀ {Γ} (γ : Env Γ) {m n} (C : M.Matrix m n) s x (o : ∣ 𝔽 n ∣) k →
                ap (sub-inputs γ C) (map-input γ s x o) k ≈s map-input γ s x (ap C o) k
ap-sub-inputs γ {m} {n} C s x o k =
  ≈-trans (app-pair (M.I ∘ M.p₁ {a} {n}) (C ∘ M.p₂ {a} {n}) y k)
  (≈-trans (M.concat-preserves _≈s_
              {u₁ = ap (M.I ∘ M.p₁ {a} {n}) y} {u₂ = inputs γ s x} {v₁ = ap (C ∘ M.p₂ {a} {n}) y} {v₂ = ap C o}
              (λ l → ≈-trans (app-∘ M.I (M.p₁ {a} {n}) y l)
                             (≈-trans (app-I (ap (M.p₁ {a} {n}) y) l) (ap-p₁-++ (inputs γ s x) o l)))
              (λ l → ≈-trans (app-∘ C (M.p₂ {a} {n}) y l) (app-congᵥ C (ap-p₂-++ (inputs γ s x) o) l)) k)
           (≈-sym (≈-trans (+-cong (app-in₁ (inputs γ s x) k) (app-in₂ (ap C o) k))
                           (concat-pad (inputs γ s x) (ap C o) k))))
  where
  a = suc (width-env γ)
  y = map-input γ s x o

map-built : ∀ {Γ} (γ : Env Γ) {m n} (G : M.Matrix n (suc (width-env γ) + suc m)) s x (o : ∣ 𝔽 (suc m) ∣)
            (k : Fin (suc n)) →
            ap (map-built-out γ m n +ₘ (M.in₂ {1} {n} ∘ G)) (map-input γ s x o) k ≈s
            M.concat {1} {n} (λ _ → (ctrl ·ₛ s) +ₛ o zero) (ap G (map-input γ s x o)) k
map-built γ {m} {n} G s x o k =
  ≈-trans (app-+ₘ (map-built-out γ m n) (M.in₂ {1} {n} ∘ G) y k)
  (≈-trans (+-cong (≈-trans (app-∘ (M.in₁ {1} {n}) Z y k) (app-in₁ {1} {n} (ap Z y) k))
                   (≈-trans (app-∘ (M.in₂ {1} {n}) G y k) (app-in₂ {1} {n} (ap G y) k)))
  (≈-trans (concat-pad (ap Z y) (ap G y) k)
           (M.concat-preserves _≈s_ {u₁ = ap Z y} {u₂ = λ _ → (ctrl ·ₛ s) +ₛ o zero} {v₁ = ap G y} {v₂ = ap G y}
              row (λ _ → ≈-refl) k)))
  where
  a = suc (width-env γ)
  y = map-input γ s x o
  Z = (wctrl ∘ M.p₁ {a} {suc m}) +ₘ (M.p₁ {1} {m} ∘ M.p₂ {a} {suc m})
  row : ∀ l → ap Z y l ≈s ((ctrl ·ₛ s) +ₛ o zero)
  row l =
    ≈-trans (app-+ₘ (wctrl ∘ M.p₁ {a} {suc m}) (M.p₁ {1} {m} ∘ M.p₂ {a} {suc m}) y l)
      (+-cong (≈-trans (app-∘ (wctrl {width-env γ} {1}) (M.p₁ {a} {suc m}) y l)
               (≈-trans (ap-wctrl {width-env γ} {1} (ap (M.p₁ {a} {suc m}) y) l)
                        (·-cong ≈-refl (ap-p₁-++ (inputs γ s x) o zero))))
              (≈-trans (app-∘ (M.p₁ {1} {m}) (M.p₂ {a} {suc m}) y l)
               (≈-trans (ap-p₁₁ (ap (M.p₂ {a} {suc m}) y) l) (ap-p₂-++ (inputs γ s x) o zero))))

EnvDepRel-resp : ∀ {Γ} {γ : Env Γ} {gi} (rγ : EnvValRel γ gi) s {x x' g} →
                 (∀ k → x k ≈s x' k) → EnvDepRel rγ s x g → EnvDepRel rγ s x' g
EnvDepRel-resp emp s ex rel = prop.tt
EnvDepRel-resp (_·_ {τ = τ} {γ = γ} {v = v} rγ r) s ex (rel , h) =
  EnvDepRel-resp rγ s (app-congᵥ (M.p₁ {width-env γ} {width v}) ex) rel ,
  DepRel⊑-resp τ r s (app-congᵥ (M.p₂ {width-env γ} {width v}) ex) h

cs-absorb : ∀ s e → ((ctrl ·ₛ s) +ₛ ((s ·ₛ ctrl) ·ₛ e)) ≈s (ctrl ·ₛ s)
cs-absorb s e =
  ≈-trans (+-cong ·-comm S.·-assoc)
  (≈-trans (≈-sym S.·-+-distribₗ)
  (≈-trans (·-cong ≈-refl (≈-trans +-comm (c-bound e))) ·-comm))

ctrl-dep-split : ∀ τ (i : Ix τ) s a {o} → o ≈s ((ctrl ·ₛ s) +ₛ a) →
                 Fib._≈_ τ i (ctrl-dep-at τ i ((ctrl ·ₛ s) +ₛ o))
                             (Fib._+_ τ i (ctrl-dep-at τ i s) (ctrl-dep-at τ i a))
ctrl-dep-split τ i s a eo =
  Fib.trans τ i (ctrl-dep τ .at i .func-resp-≈ (+-cong ≈-refl eo))
    (Fib.trans τ i (ctrl-dep-linear τ i (ctrl ·ₛ s) ((ctrl ·ₛ s) +ₛ a))
    (Fib.trans τ i (Fib.+-cong τ i (ctrl-dep-c τ i s)
      (Fib.trans τ i (ctrl-dep-linear τ i (ctrl ·ₛ s) a) (Fib.+-cong τ i (ctrl-dep-c τ i s) (Fib.refl τ i))))
    (Fib.trans τ i (Fib.sym τ i (Fib.+-assoc τ i)) (Fib.+-cong τ i (Fib.⊑-refl τ i) (Fib.refl τ i)))))


built : ∀ {Γ} {γ : Env Γ} {n} (R' : M.Matrix n (suc (width-env γ))) s x (k : Fin (suc n)) →
        ap (built-out γ n +ₘ (M.in₂ {1} ∘ R')) (inputs γ s x) k ≈s
        M.concat {1} {n} (λ _ → ctrl ·ₛ s) (ap R' (inputs γ s x)) k
built {γ = γ} {n} R' s x k =
  ≈-trans (app-+ₘ (built-out γ n) (M.in₂ {1} ∘ R') y k)
  (≈-trans (+-cong (≈-trans (app-∘ (M.in₁ {1} {n}) wctrl y k) (app-in₁ {1} {n} (ap wctrl y) k))
                   (≈-trans (app-∘ (M.in₂ {1} {n}) R' y k) (app-in₂ {1} {n} (ap R' y) k)))
  (≈-trans (concat-pad (ap wctrl y) (ap R' y) k)
           (M.concat-preserves _≈s_ {u₁ = ap wctrl y} {u₂ = λ _ → ctrl ·ₛ s} {v₁ = ap R' y} {v₂ = ap R' y}
              (ap-wctrl {width-env γ} {1} y) (λ _ → ≈-refl) k)))
  where y = inputs γ s x

subst-base : ∀ {σ} {i i' : Ix (base σ)} (e : Ix._≈_ (base σ) i i')
             (d : ∣ Fib (base σ) i ∣) (k : Fin (sort-width σ)) →
             ⟦ base σ ⟧ .fam .subst e .func d k ≈s d k
subst-base {σ} e d k = Σ-unit {sort-width σ} k d

subst-inj₁ : ∀ {σ τ} {i i' : Ix σ} (e : Ix._≈_ σ i i') (d : ∣ Fib (σ [+] τ) (inj₁ i) ∣) →
             Fib._≈_ (σ [+] τ) (inj₁ i') (⟦ σ [+] τ ⟧ .fam .subst {inj₁ i} {inj₁ i'} e .func d)
                                         (proj₁ d , ⟦ σ ⟧ .fam .subst e .func (proj₂ d))
subst-inj₁ {σ} {i' = i'} e d = +-runit , Fib.+-lunit σ i'

subst-inj₂ : ∀ {σ τ} {i i' : Ix τ} (e : Ix._≈_ τ i i') (d : ∣ Fib (σ [+] τ) (inj₂ i) ∣) →
             Fib._≈_ (σ [+] τ) (inj₂ i') (⟦ σ [+] τ ⟧ .fam .subst {inj₂ i} {inj₂ i'} e .func d)
                                         (proj₁ d , ⟦ τ ⟧ .fam .subst e .func (proj₂ d))
subst-inj₂ {τ = τ} {i' = i'} e d = +-runit , Fib.+-lunit τ i'

subst-pair : ∀ {σ τ} {i i' : Ix σ} {j j' : Ix τ} (e₁ : Ix._≈_ σ i i') (e₂ : Ix._≈_ τ j j')
             (d : ∣ Fib (σ [×] τ) (i , j) ∣) →
             Fib._≈_ (σ [×] τ) (i' , j') (⟦ σ [×] τ ⟧ .fam .subst {i , j} {i' , j'} (e₁ , e₂) .func d)
               (proj₁ d , (⟦ σ ⟧ .fam .subst e₁ .func (proj₁ (proj₂ d)) , ⟦ τ ⟧ .fam .subst e₂ .func (proj₂ (proj₂ d))))
subst-pair {σ} {τ} {i' = i'} {j' = j'} e₁ e₂ d =
  +-runit , (Fib.trans σ i' (Fib.+-lunit σ i') (Fib.+-runit σ i') , Fib.trans τ j' (Fib.+-lunit τ j') (Fib.+-lunit τ j'))

DepRel-transport′ : ∀ {N} τ (p : arr-depth τ ≤ N) {v : Val τ} {i i' : Ix τ} (E : Ix._≈_ τ i i')
                    (r : ValRel′ N τ p v i) {o : ∣ 𝔽 (width v) ∣} {d : ∣ Fib τ i ∣} →
                    DepRel′ N τ p r o d → DepRel′ N τ p (ValRel-resp′ τ p E r) o (⟦ τ ⟧ .fam .subst E .func d)
DepRel-transport′ unit p {unit} {i} {i'} E r {o} {d} h k =
  ≈-trans (h k) (≈-sym (subst-refl ⟦ unit ⟧ {i} E d k))
DepRel-transport′ (base σ) p {const a} {i} {i'} E r {o} {d} h k =
  ≈-trans (h k) (≈-sym (subst-base {σ} {i} {i'} E d k))
DepRel-transport′ (σ [+] τ) p {inl v} {i} {i'} E (i₀ , r₀ , ⟪ e₀ ⟫) {o} {d} (h₀ , h) =
  let e' = Ix.trans (σ [+] τ) {i'} {i} {inj₁ i₀} (Ix.sym (σ [+] τ) {i} {i'} E) e₀
      comp = subst-trans ⟦ σ [+] τ ⟧ {i} {i'} {inj₁ i₀} E e' d
  in
  ≈-trans h₀ (proj₁ comp) ,
  DepRel-resp′ σ (bound₁ p) r₀ (λ k → ≈-refl) (proj₂ comp) h
DepRel-transport′ (σ [+] τ) p {inr v} {i} {i'} E (i₀ , r₀ , ⟪ e₀ ⟫) {o} {d} (h₀ , h) =
  let e' = Ix.trans (σ [+] τ) {i'} {i} {inj₂ i₀} (Ix.sym (σ [+] τ) {i} {i'} E) e₀
      comp = subst-trans ⟦ σ [+] τ ⟧ {i} {i'} {inj₂ i₀} E e' d
  in
  ≈-trans h₀ (proj₁ comp) ,
  DepRel-resp′ τ (bound₂ p) r₀ (λ k → ≈-refl) (proj₂ comp) h
DepRel-transport′ (σ [×] τ) p {pair v u} {i , j} {i' , j'} (E₁ , E₂) (r₁ , r₂) {o} {d} (h₀ , (h₁ , h₂)) =
  ≈-trans h₀ (≈-sym +-runit) ,
  (DepRel-resp′ σ (bound₁ p) (ValRel-resp′ σ (bound₁ p) E₁ r₁) (λ k → ≈-refl)
     (Fib.sym σ i' (Fib.trans σ i' (Fib.+-lunit σ i') (Fib.+-runit σ i')))
     (DepRel-transport′ σ (bound₁ p) E₁ r₁ h₁) ,
   DepRel-resp′ τ (bound₂ p) (ValRel-resp′ τ (bound₂ p) E₂ r₂) (λ k → ≈-refl)
     (Fib.sym τ j' (Fib.trans τ j' (Fib.+-lunit τ j') (Fib.+-lunit τ j')))
     (DepRel-transport′ τ (bound₂ p) E₂ r₂ h₂))
DepRel-transport′ {suc N} (σ [→] τ) (s≤s p) {clo γ' t} {f} {f'} E r {o} {d} (h₀ , hc) =
  ≈-trans h₀ (≈-sym +-runit) ,
  λ s' {v} {j} rv z y hz {u} {U} D →
    DepRel-resp′ τ (bound₂ p) (ValRel-resp′ τ (bound₂ p) (Ej j) (r rv D)) (λ k → ≈-refl)
      (Fib.trans τ (f' .idxf .sfunc j)
         (⟦ τ ⟧ .fam .subst (Ej j) .preserve-+ {ctrl-dep-at τ (f .idxf .sfunc j) (s' +ₛ o zero)} {_})
      (Fib.+-cong τ (f' .idxf .sfunc j) (ctrl-dep-natural τ (Ej j) (s' +ₛ o zero))
      (Fib.trans τ (f' .idxf .sfunc j)
         (⟦ τ ⟧ .fam .subst (Ej j) .preserve-+ {_} {_})
      (Fib.+-cong τ (f' .idxf .sfunc j) (eval-part j)
         (E ._≃_.famf-eq .indexed-family._≃f_.transf-eq {j} .func-eq (Fib.refl σ j {y}))))))
      (DepRel-transport′ τ (bound₂ p) (Ej j) (r rv D) (hc s' rv z y hz D))
  where
  Ej = idx-eq-at σ τ E
  hmap = indexed-family.reindex-≈ {P = ⟦ τ ⟧ .fam} (f .idxf) (f' .idxf) (E ._≃_.idxf-eq)
  eval-part : ∀ j → Fib._≈_ τ (f' .idxf .sfunc j)
                (⟦ τ ⟧ .fam .subst (Ej j) .func (evalΠ σ τ f j .func (proj₂ d)))
                (evalΠ σ τ f' j .func
                   (proj₂ (⟦ σ [→] τ ⟧ .fam .subst {f} {f'} E .func d)))
  eval-part j =
    Fib.trans τ (f' .idxf .sfunc j)
      (Fib.sym τ (f' .idxf .sfunc j)
         (ΠP.lambda-eval {A = ⟦ σ ⟧ .idx} {P = ⟦ τ ⟧ .fam indexed-family.[ f' .idxf ]}
            {x = Payload σ τ f}
            {f = indexed-family._∘f_ {A = ⟦ σ ⟧ .idx}
                   {P = indexed-family.constantFam (⟦ σ ⟧ .idx) SemiMod.cat (Payload σ τ f)}
                   {Q = ⟦ τ ⟧ .fam indexed-family.[ f .idxf ]} {R = ⟦ τ ⟧ .fam indexed-family.[ f' .idxf ]}
                   hmap (ΠP.evalΠf {A = ⟦ σ ⟧ .idx} (⟦ τ ⟧ .fam indexed-family.[ f .idxf ]))} j
            .func-eq {proj₂ d} {proj₂ d} (Payload.refl σ τ f {proj₂ d})))
      (evalΠ σ τ f' j .func-resp-≈
         {ΠP.Π-map hmap .func (proj₂ d)} {proj₂ (⟦ σ [→] τ ⟧ .fam .subst {f} {f'} E .func d)}
         (Payload.sym σ τ f' {proj₂ (⟦ σ [→] τ ⟧ .fam .subst {f} {f'} E .func d)} {ΠP.Π-map hmap .func (proj₂ d)}
            (Payload.+-lunit σ τ f' {ΠP.Π-map hmap .func (proj₂ d)})))
DepRel-transport′ (μ τ) p {roll v} {i} {i'} E r {o} {d} h =
  DepRel-resp′ (τ [ μ τ ]) (bound-μ τ p) (ValRel-resp′ (τ [ μ τ ]) (bound-μ τ p) E' r) (λ k → ≈-refl)
    (Fib.sym (τ [ μ τ ]) (unroll-mor τ .idxf .sfunc i')
      (transf-natural (unroll-mor τ) {i} {i'} E d))
    (DepRel-transport′ (τ [ μ τ ]) (bound-μ τ p) E' r h)
  where E' = unroll-mor τ .idxf .sfunc-resp-≈ {i} {i'} E

DepRel-transport : ∀ τ {v : Val τ} {i i' : Ix τ} (E : Ix._≈_ τ i i') (r : ValRel τ v i)
                   {o : ∣ 𝔽 (width v) ∣} {d : ∣ Fib τ i ∣} →
                   DepRel τ r o d → DepRel τ (ValRel-resp τ E r) o (⟦ τ ⟧ .fam .subst E .func d)
DepRel-transport τ = DepRel-transport′ τ ≤-refl

DepRel-transport⁻′ : ∀ {N} τ (p : arr-depth τ ≤ N) {v : Val τ} {i i' : Ix τ} (E : Ix._≈_ τ i' i)
                     (r : ValRel′ N τ p v i) {o : ∣ 𝔽 (width v) ∣} {d : ∣ Fib τ i' ∣} {d' : ∣ Fib τ i ∣} →
                     Fib._≈_ τ i (⟦ τ ⟧ .fam .subst E .func d) d' →
                     DepRel′ N τ p r o d' → DepRel′ N τ p (ValRel-resp′ τ p (Ix.sym τ E) r) o d
DepRel-transport⁻′ τ p {i = i} {i'} E r {o} {d} {d'} ed h =
  DepRel-resp′ τ p (ValRel-resp′ τ p (Ix.sym τ E) r) (λ k → ≈-refl)
    (Fib.trans τ i' (Fib.sym τ i' (subst-trans ⟦ τ ⟧ E (Ix.sym τ E) d))
                    (subst-refl ⟦ τ ⟧ (Ix.trans τ E (Ix.sym τ E)) d))
    (DepRel-transport′ τ p (Ix.sym τ E) r (DepRel-resp′ τ p r (λ k → ≈-refl) (Fib.sym τ i ed) h))

DepRel-transport⁻ : ∀ τ {v : Val τ} {i i' : Ix τ} (E : Ix._≈_ τ i' i) (r : ValRel τ v i)
                    {o : ∣ 𝔽 (width v) ∣} {d : ∣ Fib τ i' ∣} {d' : ∣ Fib τ i ∣} →
                    Fib._≈_ τ i (⟦ τ ⟧ .fam .subst E .func d) d' →
                    DepRel τ r o d' → DepRel τ (ValRel-resp τ (Ix.sym τ E) r) o d
DepRel-transport⁻ τ = DepRel-transport⁻′ τ ≤-refl

ty-cast : ∀ {τ τ'} → τ ≡ τ' → Mor ⟦ τ ⟧ ⟦ τ' ⟧
ty-cast e = ≡-to-⇒ (cong (λ υ → ⟦ υ ⟧ty (λ ())) e)

vec-cast : ∀ {τ τ'} (e : τ ≡ τ') {v : Val τ} → ∣ 𝔽 (width v) ∣ → ∣ 𝔽 (width (≡-subst Val e v)) ∣
vec-cast refl o = o

ValRel-cast : ∀ {τ τ'} (e : τ ≡ τ') {v : Val τ} {i : Ix τ} →
              ValRel τ v i → ValRel τ' (≡-subst Val e v) (ty-cast e .idxf .sfunc i)
ValRel-cast refl r = r

ValRel-cast⁻ : ∀ {τ τ'} (e : τ ≡ τ') {v : Val τ} {i : Ix τ'} →
               ValRel τ' (≡-subst Val e v) i → ValRel τ v (ty-cast (sym e) .idxf .sfunc i)
ValRel-cast⁻ refl r = r

ty-cast-cancel : ∀ {τ τ'} (e : τ ≡ τ') (i : Ix τ') →
                 Ix._≈_ τ' (ty-cast e .idxf .sfunc (ty-cast (sym e) .idxf .sfunc i)) i
ty-cast-cancel {τ' = τ'} refl i = Ix.refl τ' {i}

DepRel-cast : ∀ {τ τ'} (e : τ ≡ τ') {v : Val τ} {i : Ix τ} (r : ValRel τ v i)
              {o : ∣ 𝔽 (width v) ∣} {d : ∣ Fib τ i ∣} →
              DepRel τ r o d → DepRel τ' (ValRel-cast e r) (vec-cast e {v} o) (ty-cast e .famf .transf i .func d)
DepRel-cast refl r h = h

vec-cast⁻ : ∀ {τ τ'} (e : τ ≡ τ') {v : Val τ} → ∣ 𝔽 (width (≡-subst Val e v)) ∣ → ∣ 𝔽 (width v) ∣
vec-cast⁻ refl o = o

vec-cast-cong : ∀ {τ τ'} (e : τ ≡ τ') {v : Val τ} {o o' : ∣ 𝔽 (width v) ∣} → (∀ k → o k ≈s o' k) →
                ∀ k → vec-cast e {v} o k ≈s vec-cast e {v} o' k
vec-cast-cong refl eq = eq

DepRel-cast⁻ : ∀ {τ τ'} (e : τ ≡ τ') {v : Val τ} {i : Ix τ'} (r : ValRel τ' (≡-subst Val e v) i)
               {o : ∣ 𝔽 (width (≡-subst Val e v)) ∣} {d : ∣ Fib τ' i ∣} →
               DepRel τ' r o d →
               DepRel τ (ValRel-cast⁻ e r) (vec-cast⁻ e {v} o) (ty-cast (sym e) .famf .transf i .func d)
DepRel-cast⁻ refl r h = h

ty-cast-cancel-elt : ∀ {τ τ'} (e : τ ≡ τ') (i : Ix τ') (d : ∣ Fib τ' i ∣) →
                     Fib._≈_ τ' i
                       (⟦ τ' ⟧ .fam .subst (ty-cast-cancel e i) .func
                         (ty-cast e .famf .transf (ty-cast (sym e) .idxf .sfunc i) .func
                           (ty-cast (sym e) .famf .transf i .func d)))
                       d
ty-cast-cancel-elt {τ' = τ'} refl i d = subst-refl ⟦ τ' ⟧ {i} (Ix.refl τ' {i}) d

ty-cast-ctrl-dep : ∀ {τ τ'} (e : τ ≡ τ') (i : Ix τ) (s : Setoid.Carrier A) →
                   Fib._≈_ τ' (ty-cast e .idxf .sfunc i)
                     (ty-cast e .famf .transf i .func (ctrl-dep-at τ i s)) (ctrl-dep-at τ' (ty-cast e .idxf .sfunc i) s)
ty-cast-ctrl-dep {τ' = τ'} refl i s = Fib.refl τ' i

ap-ccast-I : ∀ {τ τ'} (e : τ ≡ τ') {v : Val τ} (o : ∣ 𝔽 (width (≡-subst Val e v)) ∣) k →
             ap (ccast (sym (width-subst e v)) M.I) o k ≈s vec-cast⁻ e {v} o k
ap-ccast-I refl o k = app-I o k

ap-rcast-I : ∀ {τ τ'} (e : τ ≡ τ') {v : Val τ} (o : ∣ 𝔽 (width v) ∣) k →
             ap (rcast (sym (width-subst e v)) M.I) o k ≈s vec-cast e {v} o k
ap-rcast-I refl o k = app-I o k
