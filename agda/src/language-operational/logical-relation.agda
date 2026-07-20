{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (0ℓ)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; s≤s)
open import Data.List using (List; []; _∷_)
open import Data.Nat.Properties using (≤-refl; m≤m+n; m≤n+m)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Unit using () renaming (⊤ to ⊤ₛ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym) renaming (subst to ≡-subst)
open import prop using (Prf; ∃ₚ; _∧_)
import matrix
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
import two
open import signature using (Signature; Model; PFPC[_,_,_,_])
open import language-operational.algebra using (Algebra; sort-vals)
open import categories using (Category; HasProducts; HasTerminal; HasCoproducts; HasExponentials; strong-coproducts→coproducts)
import matrix-embedding-semimod
import matrix-semimod-action
import ho-model-boolalg-sd-semimod

-- Logical relation between the operational semantics and the interpretation in Fam(SemiMod(𝟚)), in
-- existential (computability) form. Defined by well-founded recursion on type size: at an inductive type the
-- relation is an inductive family that consumes the value, taking the relation at smaller types as a
-- parameter, with the size bound carried by the arrow-leaf constructor.
module language-operational.logical-relation
  (Sig : Signature 0ℓ)
  (open ho-model-boolalg-sd-semimod two.semiring two.semiring-boolean)
  (Impl : Model PFPC[ Fam⟨𝒞⟩.cat , Fam⟨𝒞⟩-terminal , Fam⟨𝒞⟩-products , Fam⟨𝒞⟩-bool ] Sig)
  where

open Signature Sig
private
  module PA = language-operational.algebra.IndexAlgebra BoolAlg.cat BoolAlg.terminal BoolAlg.products Sig

-- The value-level algebra is the model's index elements, so agreement at base sorts is definitional.
𝒜 : Algebra Sig 0ℓ
𝒜 = PA.index-algebra Impl

open Algebra 𝒜
open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.evaluation Sig 𝒜
  using (Val; Env; unit; const; inl; inr; pair; clo; roll; emp; _·_)
import language-operational.evaluation-mat
open import type-substitution Sig using (unfold₁; unfold₁-inst; size)

open interp-boolean Sig Impl

private
  module FamCP = HasCoproducts (strong-coproducts→coproducts Fam⟨𝒟⟩-terminal Fam⟨𝒟⟩-strongCoproducts)
  module FamP  = HasProducts Fam⟨𝒟⟩-products
  module FamE  = HasExponentials Fam⟨𝒟⟩-exponentials

private
  module MES = matrix-embedding-semimod two.semiring
  module MSA = matrix-semimod-action two.semiring
  module SM = Category SemiMod.cat
  module M = matrix.Mat two.semiring

open MES using (X^; F)

δ₀ : Fin 0 → Fam⟨𝒟⟩.Obj
δ₀ = λ ()

Index : type 0 → Set
Index τ = Setoid.Carrier ((⟦ τ ⟧ty δ₀) .idx)

Fibre : (τ : type 0) → Index τ → SM.obj
Fibre τ a = Fam⟨𝒟⟩.fm ((⟦ τ ⟧ty δ₀) .fam) a

idx-≈ : (τ : type 0) → Index τ → Index τ → Prop 0ℓ
idx-≈ τ = Setoid._≈_ ((⟦ τ ⟧ty δ₀) .idx)

fibre-subst : (τ : type 0) {a a' : Index τ} → idx-≈ τ a a' → SM._⇒_ (Fibre τ a) (Fibre τ a')
fibre-subst τ e = Fam⟨𝒟⟩.subst ((⟦ τ ⟧ty δ₀) .fam) e

-- The denotational roll: ⟦ τ [ μ τ ] ⟧ ⇒ ⟦ μ τ ⟧.
roll-mor : (τ : type 1) → Category._⇒_ Fam⟨𝒟⟩.cat (⟦ τ [ μ τ ] ⟧ty δ₀) (⟦ μ τ ⟧ty δ₀)
roll-mor τ =
  Category._∘_ Fam⟨𝒟⟩.cat
    (polynomial-functor.Interp.HasMu.inMap Fam⟨𝒟⟩-hasMu (as-poly τ δ₀) δ₀)
    (sub-as-apply-fwd τ (μ τ))
  where import polynomial-functor

roll-ix : (τ : type 1) → Index (τ [ μ τ ]) → Index (μ τ)
roll-ix τ a = roll-mor τ .idxf .prop-setoid._⇒_.func a

roll-fib : (τ : type 1) (a : Index (τ [ μ τ ])) →
           SM._⇒_ (Fibre (τ [ μ τ ]) a) (Fibre (μ τ) (roll-ix τ a))
roll-fib τ a = roll-mor τ .famf .indexed-family._⇒f_.transf a
  where import indexed-family

private
  _∘M_ = SM._∘_
  _≈M_ = SM._≈_
  infixr 30 _∘M_

-- Coercions along propositional type equality.
ix-coerce : ∀ {σ σ' : type 0} → σ ≡ σ' → Index σ → Index σ'
ix-coerce e = ≡-subst Index e

fib-coerce : ∀ {σ σ' : type 0} (e : σ ≡ σ') (a : Index σ) →
             SM._⇒_ (Fibre σ a) (Fibre σ' (ix-coerce e a))
fib-coerce refl a = SM.id _

free-coerce : ∀ {m n : ℕ} → m ≡ n → SM._⇒_ (X^ m) (X^ n)
free-coerce refl = SM.id _

-- Structure maps at points and fibres.
ix-in₁ : (σ τ : type 0) → Index σ → Index (σ [+] τ)
ix-in₁ σ τ a = FamCP.in₁ {⟦ σ ⟧ty δ₀} {⟦ τ ⟧ty δ₀} .idxf .prop-setoid._⇒_.func a

ix-in₂ : (σ τ : type 0) → Index τ → Index (σ [+] τ)
ix-in₂ σ τ a = FamCP.in₂ {⟦ σ ⟧ty δ₀} {⟦ τ ⟧ty δ₀} .idxf .prop-setoid._⇒_.func a

fib-in₁ : (σ τ : type 0) (a : Index σ) → SM._⇒_ (Fibre σ a) (Fibre (σ [+] τ) (ix-in₁ σ τ a))
fib-in₁ σ τ a = FamCP.in₁ {⟦ σ ⟧ty δ₀} {⟦ τ ⟧ty δ₀} .famf .indexed-family._⇒f_.transf a
  where import indexed-family

fib-in₂ : (σ τ : type 0) (a : Index τ) → SM._⇒_ (Fibre τ a) (Fibre (σ [+] τ) (ix-in₂ σ τ a))
fib-in₂ σ τ a = FamCP.in₂ {⟦ σ ⟧ty δ₀} {⟦ τ ⟧ty δ₀} .famf .indexed-family._⇒f_.transf a
  where import indexed-family

ix-p₁ : (σ τ : type 0) → Index (σ [×] τ) → Index σ
ix-p₁ σ τ ab = FamP.p₁ {⟦ σ ⟧ty δ₀} {⟦ τ ⟧ty δ₀} .idxf .prop-setoid._⇒_.func ab

ix-p₂ : (σ τ : type 0) → Index (σ [×] τ) → Index τ
ix-p₂ σ τ ab = FamP.p₂ {⟦ σ ⟧ty δ₀} {⟦ τ ⟧ty δ₀} .idxf .prop-setoid._⇒_.func ab

fib-p₁ : (σ τ : type 0) (ab : Index (σ [×] τ)) →
         SM._⇒_ (Fibre (σ [×] τ) ab) (Fibre σ (ix-p₁ σ τ ab))
fib-p₁ σ τ ab = FamP.p₁ {⟦ σ ⟧ty δ₀} {⟦ τ ⟧ty δ₀} .famf .indexed-family._⇒f_.transf ab
  where import indexed-family

fib-p₂ : (σ τ : type 0) (ab : Index (σ [×] τ)) →
         SM._⇒_ (Fibre (σ [×] τ) ab) (Fibre τ (ix-p₂ σ τ ab))
fib-p₂ σ τ ab = FamP.p₂ {⟦ σ ⟧ty δ₀} {⟦ τ ⟧ty δ₀} .famf .indexed-family._⇒f_.transf ab
  where import indexed-family

-- Application at points and the evaluation fibre map.
app-ix : (σ τ : type 0) → Index (σ [→] τ) → Index σ → Index τ
app-ix σ τ f a = FamE.eval .idxf .prop-setoid._⇒_.func (f , a)

∂ε : (σ τ : type 0) (f : Index (σ [→] τ)) (a : Index σ) →
     SM._⇒_ (Fam⟨𝒟⟩.fm ((FamP.prod (⟦ σ [→] τ ⟧ty δ₀) (⟦ σ ⟧ty δ₀)) .fam) (f , a))
            (Fibre τ (app-ix σ τ f a))
∂ε σ τ f a = FamE.eval {⟦ σ ⟧ty δ₀} {⟦ τ ⟧ty δ₀} .famf .indexed-family._⇒f_.transf (f , a)
  where import indexed-family

i⊕₁ : ∀ {X Y} → SM._⇒_ X (SemiMod._⊕_ X Y)
i⊕₁ {X} {Y} = cmon-enriched.Biproduct.in₁ (SemiMod.biproduct X Y)
  where import cmon-enriched

i⊕₂ : ∀ {X Y} → SM._⇒_ Y (SemiMod._⊕_ X Y)
i⊕₂ {X} {Y} = cmon-enriched.Biproduct.in₂ (SemiMod.biproduct X Y)
  where import cmon-enriched

private
  BW : (sort → ℕ) → List sort → ℕ
  BW w = language-operational.evaluation-mat.bases-width Sig 𝒜 w

-- The witness set relating the operational treatment of primitives to the model: the fibre description
-- of each base sort and the dependency matrix of each operation. Widths and canonical maps follow from
-- the fibre descriptions.
record Presentation : Set where
  field
    sort-approx : sort → FO.Approx
    -- The canonical map realising each base fibre by the free object of its width. For the model built
    -- from sort-approx this is FO.canonical, but the relation is generic in the model, so it is supplied.
    sort-can   : ∀ s (c : sort-val s) → SM._⇒_ (X^ (FO.width (sort-approx s))) (Fibre (base s) c)
    op-rel     : ∀ {is o'} → op is o' → sort-vals sort-val is →
                 Category._⇒_ M.cat (BW (λ s → FO.width (sort-approx s)) is) (FO.width (sort-approx o'))

module WithPresentation (P : Presentation) where

  open Presentation P

  private
    module EM = language-operational.evaluation-mat Sig 𝒜 (λ s → FO.width (sort-approx s))
  open EM using (width; width-env; width-subst; module WithOpRels)
  open WithOpRels op-rel

  Realiser : (τ : type 0) → Val τ → Index τ → Set
  Realiser τ v a = SM._⇒_ (X^ (width v)) (Fibre τ a)

  RelSpec : type 0 → Set₁
  RelSpec τ = (v : Val τ) (a : Index τ) → Realiser τ v a → Set

  in-free₁ : (m n : ℕ) → SM._⇒_ (X^ m) (X^ (m + n))
  in-free₁ m n = MSA.mat-mor (M.in₁ {m} {n})

  in-free₂ : (m n : ℕ) → SM._⇒_ (X^ n) (X^ (m + n))
  in-free₂ m n = MSA.mat-mor (M.in₂ {m} {n})

  data MuRel (τ₀ : type 1)
             (Rel< : (σ : type 0) → size σ < size (μ τ₀) → RelSpec σ) :
             (σ' : type 1) (v : Val (σ' [ μ τ₀ ])) (a : Index (σ' [ μ τ₀ ])) →
             Realiser (σ' [ μ τ₀ ]) v a → Set where
    mrel-roll  : ∀ {w a' r' a r} →
                 MuRel τ₀ Rel< τ₀ w a' r' →
                 Prf (∃ₚ (idx-≈ (μ τ₀) (roll-ix τ₀ a') a) λ e →
                      r ≈M (fibre-subst (μ τ₀) {roll-ix τ₀ a'} {a} e ∘M roll-fib τ₀ a' ∘M r')) →
                 MuRel τ₀ Rel< (var Fin.zero) (roll w) a r
    mrel-unit  : ∀ {a r} → MuRel τ₀ Rel< unit unit a r
    mrel-base  : ∀ {s c a r} →
                 Prf (∃ₚ (idx-≈ (base s) c a) λ e →
                      r ≈M (fibre-subst (base s) {c} {a} e ∘M sort-can s c)) →
                 MuRel τ₀ Rel< (base s) (const c) a r
    mrel-arrow : ∀ {σ₁ σ₂ : type 0} {v a r} →
                 (p : size {1} (σ₁ [→] σ₂) < size (μ τ₀)) →
                 Rel< (σ₁ [→] σ₂) p v a r →
                 MuRel τ₀ Rel< (σ₁ [→] σ₂) v a r
    mrel-inl   : ∀ {σ₁ σ₂ : type 1} {v a' r' a r} →
                 MuRel τ₀ Rel< σ₁ v a' r' →
                 Prf (∃ₚ (idx-≈ ((σ₁ [+] σ₂) [ μ τ₀ ]) (ix-in₁ (σ₁ [ μ τ₀ ]) (σ₂ [ μ τ₀ ]) a') a) λ e →
                      r ≈M (fibre-subst ((σ₁ [+] σ₂) [ μ τ₀ ]) {ix-in₁ (σ₁ [ μ τ₀ ]) (σ₂ [ μ τ₀ ]) a'} {a} e ∘M fib-in₁ (σ₁ [ μ τ₀ ]) (σ₂ [ μ τ₀ ]) a' ∘M r')) →
                 MuRel τ₀ Rel< (σ₁ [+] σ₂) (inl v) a r
    mrel-inr   : ∀ {σ₁ σ₂ : type 1} {v a' r' a r} →
                 MuRel τ₀ Rel< σ₂ v a' r' →
                 Prf (∃ₚ (idx-≈ ((σ₁ [+] σ₂) [ μ τ₀ ]) (ix-in₂ (σ₁ [ μ τ₀ ]) (σ₂ [ μ τ₀ ]) a') a) λ e →
                      r ≈M (fibre-subst ((σ₁ [+] σ₂) [ μ τ₀ ]) {ix-in₂ (σ₁ [ μ τ₀ ]) (σ₂ [ μ τ₀ ]) a'} {a} e ∘M fib-in₂ (σ₁ [ μ τ₀ ]) (σ₂ [ μ τ₀ ]) a' ∘M r')) →
                 MuRel τ₀ Rel< (σ₁ [+] σ₂) (inr v) a r
    mrel-pair  : ∀ {σ₁ σ₂ : type 1} {v₁ v₂ a r} →
                 MuRel τ₀ Rel< σ₁ v₁ (ix-p₁ (σ₁ [ μ τ₀ ]) (σ₂ [ μ τ₀ ]) a)
                       (fib-p₁ (σ₁ [ μ τ₀ ]) (σ₂ [ μ τ₀ ]) a ∘M r ∘M in-free₁ (width v₁) (width v₂)) →
                 MuRel τ₀ Rel< σ₂ v₂ (ix-p₂ (σ₁ [ μ τ₀ ]) (σ₂ [ μ τ₀ ]) a)
                       (fib-p₂ (σ₁ [ μ τ₀ ]) (σ₂ [ μ τ₀ ]) a ∘M r ∘M in-free₂ (width v₁) (width v₂)) →
                 MuRel τ₀ Rel< (σ₁ [×] σ₂) (pair v₁ v₂) a r
    mrel-mu    : ∀ {τ' : type 2} {w} (a' : Index (unfold₁ τ' [ μ τ₀ ])) (r' : Realiser (unfold₁ τ' [ μ τ₀ ]) w a') → ∀ {a r} →
                 MuRel τ₀ Rel< (unfold₁ τ') w a' r' →
                 Prf (∃ₚ (idx-≈ ((μ τ') [ μ τ₀ ])
                            (roll-ix (sub (sub-lift (push (μ τ₀))) τ')
                                     (ix-coerce (unfold₁-inst τ' (μ τ₀)) a')) a) λ e →
                      (r ∘M free-coerce (sym (width-subst (unfold₁-inst τ' (μ τ₀)) w))) ≈M
                      (fibre-subst ((μ τ') [ μ τ₀ ])
                         {roll-ix (sub (sub-lift (push (μ τ₀))) τ')
                                  (ix-coerce (unfold₁-inst τ' (μ τ₀)) a')} {a} e
                         ∘M roll-fib (sub (sub-lift (push (μ τ₀))) τ')
                                     (ix-coerce (unfold₁-inst τ' (μ τ₀)) a')
                         ∘M fib-coerce (unfold₁-inst τ' (μ τ₀)) a' ∘M r')) →
                 MuRel τ₀ Rel< (μ τ') (roll (≡-subst Val (unfold₁-inst τ' (μ τ₀)) w)) a r

  Rel-acc : (τ : type 0) → Acc _<_ (size τ) → RelSpec τ
  Rel-acc (var ())
  Rel-acc unit _ v a r = ⊤ₛ
  Rel-acc (base s) _ (const c) a r =
    Prf (∃ₚ (idx-≈ (base s) c a) λ e →
         r ≈M (fibre-subst (base s) {c} {a} e ∘M sort-can s c))
  Rel-acc (σ [+] τ) (acc rs) (inl v) a r =
    Σ (Index σ) λ a' → Σ (Realiser σ v a') λ r' →
      Rel-acc σ (rs (s≤s (m≤m+n (size σ) (size τ)))) v a' r' ×
      Prf (∃ₚ (idx-≈ (σ [+] τ) (ix-in₁ σ τ a') a) λ e →
           r ≈M (fibre-subst (σ [+] τ) {ix-in₁ σ τ a'} {a} e ∘M fib-in₁ σ τ a' ∘M r'))
  Rel-acc (σ [+] τ) (acc rs) (inr v) a r =
    Σ (Index τ) λ a' → Σ (Realiser τ v a') λ r' →
      Rel-acc τ (rs (s≤s (m≤n+m (size τ) (size σ)))) v a' r' ×
      Prf (∃ₚ (idx-≈ (σ [+] τ) (ix-in₂ σ τ a') a) λ e →
           r ≈M (fibre-subst (σ [+] τ) {ix-in₂ σ τ a'} {a} e ∘M fib-in₂ σ τ a' ∘M r'))
  Rel-acc (σ [×] τ) (acc rs) (pair v u) a r =
    Rel-acc σ (rs (s≤s (m≤m+n (size σ) (size τ)))) v (ix-p₁ σ τ a)
            (fib-p₁ σ τ a ∘M r ∘M in-free₁ (width v) (width u)) ×
    Rel-acc τ (rs (s≤s (m≤n+m (size τ) (size σ)))) u (ix-p₂ σ τ a)
            (fib-p₂ σ τ a ∘M r ∘M in-free₂ (width v) (width u))
  Rel-acc (σ [→] τ) (acc rs) (clo {Γ'} γ' t) f r =
    ∀ (v : Val σ) (a : Index σ) (rv : Realiser σ v a) →
    Rel-acc σ (rs (s≤s (m≤m+n (size σ) (size τ)))) v a rv →
    Σ (Val τ) λ u →
    Σ (Category._⇒_ M.cat (width-env γ' + width v) (width u)) λ R →
    Σ (γ' · v , t ⇓ u [ R ]) λ _ →
    Σ (Realiser τ u (app-ix σ τ f a)) λ q →
      Rel-acc τ (rs (s≤s (m≤n+m (size τ) (size σ)))) u (app-ix σ τ f a) q ×
      Prf (((q ∘M MSA.mat-mor R ∘M in-free₁ (width-env γ') (width v)) ≈M
              (∂ε σ τ f a ∘M i⊕₁ ∘M r))
         ∧ ((q ∘M MSA.mat-mor R ∘M in-free₂ (width-env γ') (width v)) ≈M
              (∂ε σ τ f a ∘M i⊕₂ ∘M rv)))
  Rel-acc (μ τ₀) (acc rs) v a r =
    MuRel τ₀ (λ σ p → Rel-acc σ (rs p)) (var Fin.zero) v a r

  Rel : (τ : type 0) → RelSpec τ
  Rel τ = Rel-acc τ (<-wellFounded (size τ))

  IndexC : ctxt → Set
  IndexC Γ = Setoid.Carrier ((⟦ Γ ⟧ctxt) .idx)

  FibreC : (Γ : ctxt) → IndexC Γ → SM.obj
  FibreC Γ g = Fam⟨𝒟⟩.fm ((⟦ Γ ⟧ctxt) .fam) g

  EnvRel : (Γ : ctxt) (γ : Env Γ) (g : IndexC Γ) →
           SM._⇒_ (X^ (width-env γ)) (FibreC Γ g) → Set
  EnvRel emp emp g r = ⊤ₛ
  EnvRel (Γ ▸ τ) (γ · v) g r =
    EnvRel Γ γ (FamP.p₁ {⟦ Γ ⟧ctxt} {⟦ τ ⟧ty δ₀} .idxf .prop-setoid._⇒_.func g)
           (FamP.p₁ {⟦ Γ ⟧ctxt} {⟦ τ ⟧ty δ₀} .famf .indexed-family._⇒f_.transf g
              ∘M r ∘M in-free₁ (width-env γ) (width v)) ×
    Rel τ v (FamP.p₂ {⟦ Γ ⟧ctxt} {⟦ τ ⟧ty δ₀} .idxf .prop-setoid._⇒_.func g)
        (FamP.p₂ {⟦ Γ ⟧ctxt} {⟦ τ ⟧ty δ₀} .famf .indexed-family._⇒f_.transf g
           ∘M r ∘M in-free₂ (width-env γ) (width v))
    where import indexed-family

  -- Statement only; the proof is future work and yields eval (totality), soundness at first-order types, and
  -- the existence half of determinism.
  FundamentalProperty : Set
  FundamentalProperty =
    ∀ {Γ τ} (t : Γ ⊢ τ) (γ : Env Γ) (g : IndexC Γ)
      (rγ : SM._⇒_ (X^ (width-env γ)) (FibreC Γ g)) →
    EnvRel Γ γ g rγ →
    Σ (Val τ) λ v →
    Σ (Category._⇒_ M.cat (width-env γ) (width v)) λ R →
    Σ (γ , t ⇓ v [ R ]) λ _ →
    Σ (Realiser τ v (⟦ t ⟧tm .idxf .prop-setoid._⇒_.func g)) λ q →
      Rel τ v (⟦ t ⟧tm .idxf .prop-setoid._⇒_.func g) q ×
      Prf ((q ∘M MSA.mat-mor R) ≈M (mor t g ∘M rγ))
