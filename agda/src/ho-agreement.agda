{-# OPTIONS --prop --postfix-projections --safe #-}

-- Agreement between the operational relation and the higher-order model, on the fragment without
-- μ-types, as a logical relation. A value is related to an index of its type's
-- interpretation by recursion on the type, behaviourally at arrow types: for related arguments and
-- any derivation of the body, the result is related. Over that, a dependence vector on the value's
-- positions is related to an element of the fibre: at first-order types position by position, at
-- arrow types the root exactly and the payload through application, comparing, for any added
-- source weight, the body's dependence through the root and that weight as source and the cells
-- and the argument as environment with the elimination constant at that source plus the
-- evaluation of the payload and the index's fibre map at the argument. Inputs are a source
-- weight and an environment vector, and the environment relation lets a cell carry further control
-- dependence below the elimination constant at the source in the additive order, which is how the
-- operational semantics attaches control dependence to values inside a branch where the
-- interpretation attaches it to the branch's result once. The fundamental lemma, by induction on
-- the term over all derivations, says the relation applied to the inputs is related to the term's
-- fibre map at the environment's denotation plus the elimination constant at the source. That the
-- constant absorbs such dependence needs the elimination weight to be idempotent and to absorb its
-- multiples under addition, and addition to be idempotent, as in a lattice.
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

module ho-agreement
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

open import ho-relation S elim-weight Sig ℐ +-idem w-idem w-absorb

open model using (𝔽; mat; ι1-fwd; ι1-bwd; module Ls; module SemiMod)
open SemiMod using (Semimodule; _⇒_)
open Semimodule using () renaming (Carrier to ∣_∣)
open SemiMod._⇒_ using (func)
open FD using (Obj; Mor; idx; fam; fm; idxf; famf; Constant)
open indexed-family.Fam using (subst)
open indexed-family._⇒f_ using (transf)
open prop-setoid._⇒_ using () renaming (func to sfunc)
open LI using (⟦_⟧ty; ⟦_⟧ctxt; ⟦_⟧tm; ⟦_⟧tms; elim-const; ty-unit)
open Constant using (at)
open model using (app-+ₘ; app-∘; app-εₘ; app-I; app-e; app-congₘ; app-congᵥ) renaming (app to ap)
open Sc using (ι; ε) renaming (_≈_ to _≈s_; _+_ to _+ₛ_; _·_ to _·ₛ_)
open Setoid A using () renaming (refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)
open M using (Σ-cong; Σ-unit; Σ-ε; _∘_; _+ₘ_; εₘ; ≈ₘ-refl; ≈ₘ-sym; ≈ₘ-trans) renaming (Σ to Σₛ)
open Sc using (+-cong; ·-cong; +-lunit; +-comm; +-assoc; ·-lunit; ·-comm; ε-annihilₗ; ε-annihilᵣ)
open M using (⟨_,_⟩)

-- The fragment: no μ-types.
data CoreTm : ∀ {Γ τ} → Γ ⊢ τ → Set
data CoreTms : ∀ {Γ is} → Every (λ σ → Γ ⊢ base σ) is → Set

data CoreTm where
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
  bop  : ∀ {Γ is o} {ω : op is o} {Ms : Every (λ σ → Γ ⊢ base σ) is} → CoreTms Ms → CoreTm (bop ω Ms)
  brel : ∀ {Γ is} {ω : rel is} {Ms : Every (λ σ → Γ ⊢ base σ) is} → CoreTms Ms → CoreTm (brel ω Ms)

-- Every's constructors are qualified: the evaluation judgement reuses [] and _∷_ for the
-- derivations of an argument list.
data CoreTms where
  []  : ∀ {Γ} → CoreTms {Γ} Every.[]
  _∷_ : ∀ {Γ σ is} {M : Γ ⊢ base σ} {Ms : Every (λ σ' → Γ ⊢ base σ') is} →
        CoreTm M → CoreTms Ms → CoreTms (M Every.∷ Ms)
args-idx : ∀ {Γ is} (Ms : Every (λ σ → Γ ⊢ base σ) is) (gi : IxC Γ) → sort-vals is
args-idx {is = is} Ms gi =
  IP.collect is .FCμ.idxf .sfunc (interp.𝒟-arg-product is .idxf .sfunc (⟦ Ms ⟧tms .idxf .sfunc gi))

private
  bool-idx : ∀ (b : Ix (unit [+] unit)) →
             Setoid._≈_ (⟦ unit [+] unit ⟧ .idx)
               (interp.HR.bool.Fam⟨F⟩-preserves-bool model.𝒞𝟙ty .idxf .sfunc b) b
  bool-idx (inj₁ _) = prop.tt
  bool-idx (inj₂ _) = prop.tt

  ValRel-bool : ∀ (b i : Ix (unit [+] unit)) → Prf (Setoid._≈_ (⟦ unit [+] unit ⟧ .idx) i b) →
                ValRel (unit [+] unit) (bool→val b) i
  ValRel-bool (inj₁ _) i e = lift tt , tt , e
  ValRel-bool (inj₂ _) i e = lift tt , tt , e

-- The value part of the fundamental lemma: a term's value is related to the term's index at a
-- related environment, by induction on the term over all derivations.
fundamental-val : ∀ {Γ τ} {t : Γ ⊢ τ} (c : CoreTm t) {γ : Env Γ} {v R} (D : γ , t ⇓ v [ R ])
       {gi} (rγ : EnvValRel γ gi) → ValRel τ v (⟦ t ⟧tm .idxf .sfunc gi)
fundamental-vals : ∀ {Γ is} {Ms : Every (λ σ → Γ ⊢ base σ) is} (cs : CoreTms Ms) {γ : Env Γ} {vs R}
        (D : γ , Ms ⇓s vs [ R ]) {gi} (rγ : EnvValRel γ gi) →
        Prf (Setoid._≈_ (sort-vals-setoid sort-index is) (args-idx Ms gi) vs)
fundamental-val (var x) (⇓-var .x) rγ = lookup-val x rγ
fundamental-val unit ⇓-unit rγ = tt
fundamental-val {τ = τ₁ [+] τ₂} (inl {t = t} c) (⇓-inl D) {gi} rγ =
  ⟦ t ⟧tm .idxf .sfunc gi , fundamental-val c D rγ ,
  ⟪ Setoid.refl (⟦ τ₁ [+] τ₂ ⟧ .idx) {inj₁ (⟦ t ⟧tm .idxf .sfunc gi)} ⟫
fundamental-val {τ = τ₁ [+] τ₂} (inr {t = t} c) (⇓-inr D) {gi} rγ =
  ⟦ t ⟧tm .idxf .sfunc gi , fundamental-val c D rγ ,
  ⟪ Setoid.refl (⟦ τ₁ [+] τ₂ ⟧ .idx) {inj₂ (⟦ t ⟧tm .idxf .sfunc gi)} ⟫
fundamental-val {Γ = Γ} {τ = τ} (case {τ₁ = τ₁} {τ₂ = τ₂} {s = s} {t₁ = t₁} {t₂ = t₂} c c₁ c₂) (⇓-case-l D₁ D₂) {gi} rγ =
  let (i' , r , ⟪ e ⟫) = fundamental-val c D₁ rγ in
  ValRel-resp τ
    (Setoid.sym (⟦ τ ⟧ .idx)
      (HasStrongCoproducts.copair FD.strongCoproducts
         (FD.elimF (elim-const τ) ⟦ t₁ ⟧tm) (FD.elimF (elim-const τ) ⟦ t₂ ⟧tm)
         .idxf .prop-setoid._⇒_.func-resp-≈ {gi , ⟦ s ⟧tm .idxf .sfunc gi} {gi , inj₁ i'}
         (Setoid.refl (⟦ Γ ⟧ctxt .idx) {gi} , e)))
    (fundamental-val c₁ D₂ (rγ · r))
fundamental-val {Γ = Γ} {τ = τ} (case {τ₁ = τ₁} {τ₂ = τ₂} {s = s} {t₁ = t₁} {t₂ = t₂} c c₁ c₂) (⇓-case-r D₁ D₂) {gi} rγ =
  let (i' , r , ⟪ e ⟫) = fundamental-val c D₁ rγ in
  ValRel-resp τ
    (Setoid.sym (⟦ τ ⟧ .idx)
      (HasStrongCoproducts.copair FD.strongCoproducts
         (FD.elimF (elim-const τ) ⟦ t₁ ⟧tm) (FD.elimF (elim-const τ) ⟦ t₂ ⟧tm)
         .idxf .prop-setoid._⇒_.func-resp-≈ {gi , ⟦ s ⟧tm .idxf .sfunc gi} {gi , inj₂ i'}
         (Setoid.refl (⟦ Γ ⟧ctxt .idx) {gi} , e)))
    (fundamental-val c₂ D₂ (rγ · r))
fundamental-val (pair c₁ c₂) (⇓-pair D₁ D₂) rγ = fundamental-val c₁ D₁ rγ , fundamental-val c₂ D₂ rγ
fundamental-val (fst c) (⇓-fst D) rγ = proj₁ (fundamental-val c D rγ)
fundamental-val (snd c) (⇓-snd D) rγ = proj₂ (fundamental-val c D rγ)
fundamental-val (lam c) ⇓-lam rγ {v} {j} rv {u} {U} D = fundamental-val c D (rγ · rv)
fundamental-val (app c₁ c₂) (⇓-app D₁ D₂ D₃) rγ = fundamental-val c₁ D₁ rγ (fundamental-val c₂ D₂ rγ) D₃
fundamental-val (bop {ω = ω} cs) (⇓-bop D) rγ = ⟪ op-fun ω .prop-setoid._⇒_.func-resp-≈ (Prf.prf (fundamental-vals cs D rγ)) ⟫
fundamental-val (brel {ω = ω} {Ms = Ms} cs) (⇓-brel {vs = vs} D) {gi} rγ =
  ValRel-bool (rel-pred ω .sfunc vs) (⟦ brel ω Ms ⟧tm .idxf .sfunc gi)
    ⟪ Setoid.trans (⟦ unit [+] unit ⟧ .idx)
        {⟦ brel ω Ms ⟧tm .idxf .sfunc gi} {rel-pred ω .sfunc (args-idx Ms gi)} {rel-pred ω .sfunc vs}
        (bool-idx (rel-pred ω .sfunc (args-idx Ms gi)))
        (rel-pred ω .prop-setoid._⇒_.func-resp-≈ (Prf.prf (fundamental-vals cs D rγ))) ⟫

fundamental-vals [] [] rγ = ⟪ prop.tt ⟫
fundamental-vals (c ∷ cs) (D ∷ Ds) rγ = ⟪ Prf.prf (fundamental-val c D rγ) , Prf.prf (fundamental-vals cs Ds rγ) ⟫
-- The case rule, read at the inputs: the branch's relation at the scrutinee's root plus the
-- weighted source as source, and at the environment and the scrutinee's payload as environment.
app-case : ∀ {Γ τ'} {γ : Env Γ} (v : Val τ') {n} (R_s : M.Matrix (suc (width v)) (suc (width-env γ)))
           (T : M.Matrix n (suc (width-env (γ · v)))) s x (k : Fin n) →
           ap (T ∘ (branch-inputs γ v ∘ ⟨ M.I , R_s ⟩)) (inputs γ s x) k
           ≈s ap T (inputs (γ · v) (ap R_s (inputs γ s x) zero +ₛ (w ·ₛ s))
                     (λ l → ap (M.in₁ {width-env γ} {width v}) x l +ₛ
                            ap (M.in₂ {width-env γ} {width v}) (λ m → ap R_s (inputs γ s x) (suc m)) l)) k
app-case {γ = γ} v R_s T s x k =
  ≈-trans (app-congₘ (MC.∘-cong₂ {f = T} (≈ₘ-trans (M.∥-pair from-inputs from-scrutinee M.I R_s)
                                                   (M.+ₘ-cong (MC.id-right {f = from-inputs}) ≈ₘ-refl))) y k)
  (≈-trans (app-∘ T (from-inputs +ₘ (from-scrutinee ∘ R_s)) y k)
           (app-congᵥ T branch-at k))
  where
  module MC = Category M.cat
  y = inputs γ s x
  o_s = ap R_s y
  from-inputs : M.Matrix (suc (width-env γ + width v)) (suc (width-env γ))
  from-inputs = ctrl-row {1} ⊕ M.in₁ {width-env γ} {width v}
  from-scrutinee : M.Matrix (suc (width-env γ + width v)) (suc (width v))
  from-scrutinee = M.I {1} ⊕ M.in₂ {width-env γ} {width v}

  branch-at : ∀ l → ap (from-inputs +ₘ (from-scrutinee ∘ R_s)) y l ≈s
                    inputs (γ · v) (o_s zero +ₛ (w ·ₛ s))
                      (λ m → ap (M.in₁ {width-env γ} {width v}) x m +ₛ
                             ap (M.in₂ {width-env γ} {width v}) (λ m' → o_s (suc m')) m) l
  branch-at zero =
    ≈-trans (app-+ₘ from-inputs (from-scrutinee ∘ R_s) y zero)
    (≈-trans (+-cong (≈-trans (ap-⊕₁-zero {width-env γ} (ctrl-row {1}) (M.in₁ {width-env γ} {width v}) y)
                              (ap-ctrl-row {1} s zero))
                     (≈-trans (app-∘ from-scrutinee R_s y zero)
                              (≈-trans (ap-⊕₁-zero {width v} M.I (M.in₂ {width-env γ} {width v}) o_s)
                                       (app-I {1} (λ _ → o_s zero) zero))))
             +-comm)
  branch-at (suc m) =
    ≈-trans (app-+ₘ from-inputs (from-scrutinee ∘ R_s) y (suc m))
            (+-cong (ap-⊕₁-suc {width-env γ} (ctrl-row {1}) (M.in₁ {width-env γ} {width v}) y m)
                    (≈-trans (app-∘ from-scrutinee R_s y (suc m))
                             (ap-⊕₁-suc {width v} M.I (M.in₂ {width-env γ} {width v}) o_s m)))

-- A projection, read at the inputs: the result's control positions at the weighted source plus
-- the consumed root, and the projection of the pair's payload.
private
  proj-op : ∀ {Γ τ'} {γ : Env Γ} (wv : Val τ') {m n} (P : M.Matrix (width wv) (m + n))
            (R' : M.Matrix (suc (m + n)) (suc (width-env γ))) s x k →
            ap (elim-out γ wv +ₘ (proj-up {m} {n} wv P ∘ R')) (inputs γ s x) k
            ≈s (ap (ctrl-of wv) (λ _ → (w ·ₛ s) +ₛ ap R' (inputs γ s x) zero) k +ₛ
                ap P (λ l → ap R' (inputs γ s x) (suc l)) k)
  proj-op {γ = γ} wv {m} {n} P R' s x k =
    ≈-trans (app-+ₘ (elim-out γ wv) (proj-up {m} {n} wv P ∘ R') (inputs γ s x) k)
    (≈-trans (+-cong (≈-trans (app-∘ (ctrl-of wv) wsrc (inputs γ s x) k)
                              (app-congᵥ (ctrl-of wv) (λ l → ap-wsrc {width-env γ} {1} (inputs γ s x) l) k))
                     (≈-trans (app-∘ (proj-up {m} {n} wv P) R' (inputs γ s x) k)
                     (≈-trans (app-+ₘ (P ∘ M.p₂ {1} {m + n}) (ctrl-of wv ∘ M.p₁ {1} {m + n}) o' k)
                              (+-cong (≈-trans (app-∘ P (M.p₂ {1} {m + n}) o' k)
                                               (app-congᵥ P (ap-p₂₁ {m + n} o') k))
                                      (≈-trans (app-∘ (ctrl-of wv) (M.p₁ {1} {m + n}) o' k)
                                               (app-congᵥ (ctrl-of wv) (ap-p₁₁ {m + n} o') k))))))
    (≈-trans (+-cong ≈-refl +-comm)
    (≈-trans (≈-sym +-assoc)
             (+-cong (≈-sym (app-+ᵥ (ctrl-of wv) (λ _ → w ·ₛ s) (λ _ → o' zero) k)) ≈-refl))))
    where o' = ap R' (inputs γ s x)


private
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
    -- (e + a) + (e + m) ≈ e + (m + a)
    rearr : F._≈_ τ' i (F._+_ τ' i (F._+_ τ' i (ec τ' i s) (ec τ' i a₀)) (F._+_ τ' i (ec τ' i s) m))
                       (F._+_ τ' i (ec τ' i s) (F._+_ τ' i m (ec τ' i a₀)))
    rearr =
      F.trans τ' i (F.+-cong τ' i (F.+-comm τ' i) (F.refl τ' i))
      (F.trans τ' i (F.+-assoc τ' i)
      (F.trans τ' i (F.+-cong τ' i (F.refl τ' i) (F.sym τ' i (F.+-assoc τ' i)))
      (F.trans τ' i (F.+-cong τ' i (F.refl τ' i) (F.+-cong τ' i (ec-root τ' i s) (F.refl τ' i)))
      (F.trans τ' i (F.+-cong τ' i (F.refl τ' i) (F.+-comm τ' i))
      (F.trans τ' i (F.sym τ' i (F.+-assoc τ' i))
      (F.trans τ' i (F.+-cong τ' i (F.+-comm τ' i) (F.refl τ' i))
                    (F.+-comm τ' i)))))))

-- The branch of a case: its environment is related at the scrutinee's root plus the weighted
-- source, the scrutinee's payload carrying the constant at the source as further control dependence.
private
  branch-env : ∀ {Γ τk} {γ : Env Γ} {gi} (rγ : EnvValRel γ gi) {v : Val τk} {i'} (r_v : ValRel τk v i')
               s x g (o_s : ∣ 𝔽 (suc (width v)) ∣) (y_v : ∣ Fib τk i' ∣) →
               EnvDepRel rγ s x g → DepRel τk r_v (λ m → o_s (suc m)) (F._+_ τk i' y_v (ec τk i' s)) →
               EnvDepRel (rγ · r_v) (o_s zero +ₛ (w ·ₛ s))
                 (λ m → ap (M.in₁ {width-env γ} {width v}) x m +ₛ ap (M.in₂ {width-env γ} {width v}) (λ m' → o_s (suc m')) m)
                 (g , y_v)
  branch-env {τk = τk} {γ = γ} rγ {v} {i'} r_v s x g o_s y_v rel h =
    EnvDepRel-resp rγ Sw (λ m → ≈-sym (ap-p₁-++ x (λ m' → o_s (suc m')) m)) (EnvDepRel-mono rγ s (o_s zero) rel) ,
    DepRel⊑-resp τk r_v Sw (λ m → ≈-sym (ap-p₂-++ x (λ m' → o_s (suc m')) m)) (ec τk i' s , (dom-s , h))
    where
    Sw = o_s zero +ₛ (w ·ₛ s)
    dom-s : F._⊑_ τk i' (ec τk i' s) (ec τk i' Sw)
    dom-s =
      F.trans τk i' (F.+-cong τk i' (F.refl τk i') (F.trans τk i' (ec-linear τk i' (o_s zero) (w ·ₛ s))
                                                                  (F.+-cong τk i' (F.refl τk i') (ec-w τk i' s))))
      (F.trans τk i' (F.+-cong τk i' (F.refl τk i') (F.+-comm τk i'))
      (F.trans τk i' (F.sym τk i' (F.+-assoc τk i'))
      (F.trans τk i' (F.+-cong τk i' (ec-root τk i' s) (F.refl τk i'))
      (F.trans τk i' (F.+-comm τk i')
      (F.sym τk i' (F.trans τk i' (ec-linear τk i' (o_s zero) (w ·ₛ s))
                                  (F.+-cong τk i' (F.refl τk i') (ec-w τk i' s))))))))

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
    (F.trans τ ic (F.+-assoc τ ic)
    (F.trans τ ic (F.+-cong τ ic (F.refl τ ic) (F.+-comm τ ic))
                  (F.+-cong τ ic (F.refl τ ic) (F.sym τ ic eCF)))))
    where
    ec-part : F._≈_ τ ic (ec τ ic (o_s₀ +ₛ (w ·ₛ s))) (F._+_ τ ic (ec τ ic s) (ec τ ic a_s))
    ec-part = F.trans τ ic (elim-const τ .at ic .SemiMod._⇒_.func-resp-≈ (+-cong eo ≈-refl)) (ec-double' τ ic s a_s)

-- A primitive's arguments on the model side, as a vector on their positions laid end to end.
args-vec : ∀ {Γ is} (Ms : Every (λ σ → Γ ⊢ base σ) is) (gi : IxC Γ) → ∣ FibC Γ gi ∣ →
           ∣ 𝔽 (bases-width is) ∣
args-vec {is = is} Ms gi g =
  ap (IP.collect is .FCμ.famf .transf (interp.𝒟-arg-product is .idxf .sfunc (⟦ Ms ⟧tms .idxf .sfunc gi)))
     (interp.𝒟-arg-product is .famf .transf (⟦ Ms ⟧tms .idxf .sfunc gi) .func
        (⟦ Ms ⟧tms .famf .transf gi .func g))

private
  args-width : ∀ is → Setoid.Carrier (IP.args is .FCμ.idx) → ℕ
  args-width is p = IP.args is .FCμ.fam .fm p

  collect-cons : ∀ i is (a : Setoid.Carrier (sort-index i)) (p : Setoid.Carrier (IP.args is .FCμ.idx)) →
                 IP.collect (i ∷ is) .FCμ.famf .transf (a , p) M.≈ₘ
                 ((M.in₁ {sort-width i} {bases-width is} ∘ M.p₁ {sort-width i} {args-width is p}) +ₘ
                  (M.in₂ {sort-width i} {bases-width is} ∘
                    (IP.collect is .FCμ.famf .transf p ∘ M.p₂ {sort-width i} {args-width is p})))
  collect-cons i is a p =
    ≈ₘ-trans (MC.id-left {f = M.I ∘ (u₁ +ₘ u₂)})
    (≈ₘ-trans (MC.id-left {f = u₁ +ₘ u₂})
      (M.+ₘ-cong (∘-cong₂ {f = M.in₁ {sort-width i} {bases-width is}}
                          (≈ₘ-trans (MC.id-left {f = M.I ∘ M.p₁ {sort-width i} {n}}) (MC.id-left {f = M.p₁ {sort-width i} {n}})))
                 (∘-cong₂ {f = M.in₂ {sort-width i} {bases-width is}} (MC.id-left {f = C ∘ M.p₂ {sort-width i} {n}}))))
    where
    module MC = Category M.cat
    open MC using (∘-cong₂)
    n = args-width is p
    C = IP.collect is .FCμ.famf .transf p
    u₁ = M.in₁ {sort-width i} {bases-width is} ∘ (M.I ∘ (M.I ∘ M.p₁ {sort-width i} {n}))
    u₂ = M.in₂ {sort-width i} {bases-width is} ∘ (M.I ∘ (C ∘ M.p₂ {sort-width i} {n}))

  args-vec-cons : ∀ {Γ i is} (M : Γ ⊢ base i) (Ms : Every (λ σ → Γ ⊢ base σ) is) gi g k →
                  args-vec (M Every.∷ Ms) gi g k ≈s
                  (ap (M.in₁ {sort-width i} {bases-width is}) (⟦ M ⟧tm .famf .transf gi .func g) k +ₛ
                   ap (M.in₂ {sort-width i} {bases-width is}) (args-vec Ms gi g) k)
  args-vec-cons {i = i} {is} M Ms gi g k =
    ≈-trans (app-congₘ (collect-cons i is a p') Zc k)
    (≈-trans (app-+ₘ (u₁ ∘ M.p₁ {sort-width i} {n}) (u₂ ∘ (C ∘ M.p₂ {sort-width i} {n})) Zc k)
    (+-cong (≈-trans (app-∘ u₁ (M.p₁ {sort-width i} {n}) Zc k)
                     (app-congᵥ u₁ (λ l → ≈-trans (app-congᵥ (M.p₁ {sort-width i} {n}) Zc-split l)
                                                    (ap-p₁-++ y₁ tp-ys l)) k))
            (≈-trans (app-∘ u₂ (C ∘ M.p₂ {sort-width i} {n}) Zc k)
                     (app-congᵥ u₂ (λ l → ≈-trans (app-∘ C (M.p₂ {sort-width i} {n}) Zc l)
                                                    (app-congᵥ C (λ l' → ≈-trans (app-congᵥ (M.p₂ {sort-width i} {n}) Zc-split l')
                                                                                   (ap-p₂-++ y₁ tp-ys l')) l)) k))))
    where
    a = ⟦ M ⟧tm .idxf .sfunc gi
    p = ⟦ Ms ⟧tms .idxf .sfunc gi
    p' = interp.𝒟-arg-product is .idxf .sfunc p
    n = args-width is p'
    u₁ = M.in₁ {sort-width i} {bases-width is}
    u₂ = M.in₂ {sort-width i} {bases-width is}
    C = IP.collect is .FCμ.famf .transf p'
    y₁ = ⟦ M ⟧tm .famf .transf gi .func g
    ys = ⟦ Ms ⟧tms .famf .transf gi .func g
    q = ⟦ M Every.∷ Ms ⟧tms .famf .transf gi .func g
    tp-ys = interp.𝒟-arg-product is .famf .transf p .func ys
    Zc = interp.𝒟-arg-product (i ∷ is) .famf .transf (a , p) .func q
    z = HasProducts.prod-m FD.products (Category.id FD.cat ⟦ base i ⟧) (interp.𝒟-arg-product is) .famf .transf (a , p) .func q

    q≈ = Fpair-elt ⟦ M ⟧tm ⟦ Ms ⟧tms gi g
    ArgsD = signature.PointedFPCat.list→product
              signature.PFPC[ FD.cat , FD.terminal SemiMod.terminal , FD.products , interp.𝒟Bool ]
              (signature.Model.⟦sort⟧ interp.𝒟-Sig-model) is .fam .fm p
    Q = SemiMod._⊕_ (𝔽 (sort-width i)) ArgsD
    f₁ = SemiMod._∘_ (SemiMod.id (𝔽 (sort-width i))) (SemiMod.p₁ {𝔽 (sort-width i)} {ArgsD})
    f₂ = SemiMod._∘_ (interp.𝒟-arg-product is .famf .transf p) (SemiMod.p₂ {𝔽 (sort-width i)} {ArgsD})

    z≈ : (∀ l → proj₁ z l ≈s y₁ l) ∧ (∀ l → proj₂ z l ≈s tp-ys l)
    z≈ = (λ l → ≈-trans (prop._∧_.proj₁ (bpair-elt {Q} {𝔽 (sort-width i)} {𝔽 n} f₁ f₂ q) l) (prop._∧_.proj₁ q≈ l)) ,
         (λ l → ≈-trans (prop._∧_.proj₂ (bpair-elt {Q} {𝔽 (sort-width i)} {𝔽 n} f₁ f₂ q) l)
                        (interp.𝒟-arg-product is .famf .transf p .SemiMod._⇒_.func-resp-≈ (prop._∧_.proj₂ q≈) l))

    Zc-split : ∀ l → Zc l ≈s (ap (M.in₁ {sort-width i} {n}) y₁ l +ₛ ap (M.in₂ {sort-width i} {n}) tp-ys l)
    Zc-split l = +-cong (app-congᵥ (M.in₁ {sort-width i} {n}) (prop._∧_.proj₁ z≈) l)
                        (app-congᵥ (M.in₂ {sort-width i} {n}) (prop._∧_.proj₂ z≈) l)

  ap-p₁-const : ∀ {m n} (c : Setoid.Carrier A) (l : Fin m) → ap (M.p₁ {m} {n}) (λ _ → c) l ≈s c
  ap-p₁-const {suc m} {n} c zero =
    ≈-trans (+-cong ·-lunit (≈-trans (Σ-cong {m + n} (λ _ → ε-annihilₗ)) (Σ-ε {m + n}))) +-runit
  ap-p₁-const {suc m} c (suc l) = ≈-trans (+-cong ε-annihilₗ (ap-p₁-const {m} c l)) +-lunit

  ap-p₂-const : ∀ {m n} (c : Setoid.Carrier A) (l : Fin n) → ap (M.p₂ {m} {n}) (λ _ → c) l ≈s c
  ap-p₂-const {ℕ.zero} {n} c l = Σ-unit {n} l (λ _ → c)
  ap-p₂-const {suc m} c l = ≈-trans (+-cong ε-annihilₗ (ap-p₂-const {m} c l)) +-lunit

  in-const : ∀ {m n} (c : Setoid.Carrier A) (k : Fin (m + n)) →
             (ap (M.in₁ {m} {n}) (λ _ → c) k +ₛ ap (M.in₂ {m} {n}) (λ _ → c) k) ≈s c
  in-const {m} {n} c k =
    ≈-trans (+-cong (app-congᵥ (M.in₁ {m} {n}) (λ l → ≈-sym (ap-p₁-const {m} {n} c l)) k)
                    (app-congᵥ (M.in₂ {m} {n}) (λ l → ≈-sym (ap-p₂-const {m} {n} c l)) k))
    (≈-trans (+-cong (≈-sym (app-∘ (M.in₁ {m} {n}) (M.p₁ {m} {n}) (λ _ → c) k))
                     (≈-sym (app-∘ (M.in₂ {m} {n}) (M.p₂ {m} {n}) (λ _ → c) k)))
    (≈-trans (≈-sym (app-+ₘ (M.in₁ {m} {n} ∘ M.p₁ {m} {n}) (M.in₂ {m} {n} ∘ M.p₂ {m} {n}) (λ _ → c) k))
    (≈-trans (app-congₘ (M.id-+ m n) (λ _ → c) k) (app-I (λ _ → c) k))))

-- The outcome of a test at either branch: the root carries the source weight and the test's
-- reading of its arguments, and the unit beneath the source weight alone.
private
  test-branch : ∀ {n} (D : M.Matrix 1 n) (o : ∣ 𝔽 2 ∣) (a : Setoid.Carrier A) (v : ∣ 𝔽 1 ∣) s
                (y : ∣ 𝔽 n ∣) →
                (∀ k → o k ≈s ((w ·ₛ s) +ₛ ap (⟨ D , εₘ ⟩) (λ l → (w ·ₛ s) +ₛ y l) k)) →
                a ≈s ((w ·ₛ s) +ₛ ap D y zero) → v zero ≈s (w ·ₛ s) →
                (o zero ≈s a) ∧ (∀ k → o (suc k) ≈s v k)
  test-branch {n} D o a v s y ho ha hv = root , payload
    where
    u = λ l → (w ·ₛ s) +ₛ y l
    root : o zero ≈s a
    root =
      ≈-trans (ho zero)
      (≈-trans (+-cong ≈-refl (≈-trans (ap-pair-zero {n} {1} D εₘ u) (app-+ᵥ D (λ _ → w ·ₛ s) y zero)))
      (≈-trans (≈-sym +-assoc)
      (≈-trans (+-cong (≈-trans (+-cong ≈-refl (≈-trans (app-congᵥ D (λ _ → ≈-sym ·-runit) zero)
                                                          (≈-trans (model.app-· D (w ·ₛ s) (λ _ → ι) zero) (·-cong ·-comm ≈-refl))))
                                (sw-absorb s (ap D (λ _ → ι) zero)))
                       ≈-refl)
               (≈-sym ha))))
    payload : ∀ k → o (suc k) ≈s v k
    payload zero =
      ≈-trans (ho (suc zero))
      (≈-trans (+-cong ≈-refl (≈-trans (ap-pair-suc {n} {1} D εₘ u zero) (app-εₘ {1} u zero)))
               (≈-trans +-runit (≈-sym hv)))

  DepRel-bool : ∀ {is} (ω : rel is) (vs : sort-vals is) b {i : Ix (unit [+] unit)}
                (e : Setoid._≈_ (⟦ unit [+] unit ⟧ .idx) i b)
                (o : ∣ 𝔽 (width (bool→val b)) ∣) (d : ∣ Fib (unit [+] unit) i ∣) s
                (y : ∣ 𝔽 (bases-width is) ∣) →
                (∀ k → o k ≈s ((w ·ₛ s) +ₛ ap (brel-deps ω vs b) (λ l → (w ·ₛ s) +ₛ y l) k)) →
                F._≈_ (unit [+] unit) b (⟦ unit [+] unit ⟧ .fam .subst {i} {b} e .func d)
                (F._+_ (unit [+] unit) b (ec (unit [+] unit) b s)
                   (interp.bool-elt b (ap (rel-deps ω .sfunc vs) y zero))) →
                DepRel (unit [+] unit) (ValRel-bool b i ⟪ e ⟫) o d
  DepRel-bool ω vs (inj₁ x) {i} e o d s y ho (hd₁ , hd₂) =
    test-branch (rel-deps ω .sfunc vs) o (proj₁ d') (proj₂ d') s y ho
      (≈-trans hd₁ (+-cong (prop._∧_.proj₁ (ec-inj₁ {unit} {unit} x s)) ≈-refl))
      (≈-trans (hd₂ zero) (≈-trans (+-cong (prop._∧_.proj₂ (ec-inj₁ {unit} {unit} x s) zero) ≈-refl)
                                   (≈-trans +-runit (ec-unit x s))))
    where d' = ⟦ unit [+] unit ⟧ .fam .subst {i} {inj₁ x} e .func d
  DepRel-bool ω vs (inj₂ x) {i} e o d s y ho (hd₁ , hd₂) =
    test-branch (rel-deps ω .sfunc vs) o (proj₁ d') (proj₂ d') s y ho
      (≈-trans hd₁ (+-cong (prop._∧_.proj₁ (ec-inj₂ {unit} {unit} x s)) ≈-refl))
      (≈-trans (hd₂ zero) (≈-trans (+-cong (prop._∧_.proj₂ (ec-inj₂ {unit} {unit} x s) zero) ≈-refl)
                                   (≈-trans +-runit (ec-unit x s))))
    where d' = ⟦ unit [+] unit ⟧ .fam .subst {i} {inj₂ x} e .func d

-- The fundamental lemma.
fundamental : ∀ {Γ τ} {t : Γ ⊢ τ} (c : CoreTm t) {γ : Env Γ} {v R} (D : γ , t ⇓ v [ R ])
              {gi} (rγ : EnvValRel γ gi) (s : Setoid.Carrier A) (x : ∣ 𝔽 (width-env γ) ∣)
              (g : ∣ FibC Γ gi ∣) → EnvDepRel rγ s x g →
              DepRel τ (fundamental-val c D rγ) (mat R .func (inputs γ s x))
                (Semimodule._+_ (Fib τ (⟦ t ⟧tm .idxf .sfunc gi))
                  (elim-const τ .at (⟦ t ⟧tm .idxf .sfunc gi) .func s)
                  (⟦ t ⟧tm .famf .transf gi .func g))
-- At a primitive's arguments the relation is equality, with the elimination weight times the source
-- at every position, as at a base sort.
fundamental-s : ∀ {Γ is} {Ms : Every (λ σ → Γ ⊢ base σ) is} (cs : CoreTms Ms) {γ : Env Γ} {vs R}
                (D : γ , Ms ⇓s vs [ R ]) {gi} (rγ : EnvValRel γ gi) (s : Setoid.Carrier A)
                (x : ∣ 𝔽 (width-env γ) ∣) (g : ∣ FibC Γ gi ∣) → EnvDepRel rγ s x g →
                ∀ k → ap R (inputs γ s x) k ≈s ((w ·ₛ s) +ₛ args-vec Ms gi g k)
fundamental {τ = τ} (var x) {γ = γ} (⇓-var .x) {gi} rγ s xs g rel =
  DepRel-resp τ (lookup-val x rγ)
    (λ k → ≈-sym (ap-∥ (ctrl-of (lookup x γ)) (proj-var x γ) (inputs γ s xs) k))
    (F.refl τ (LI.⟦ x ⟧var .idxf .sfunc gi))
    (DepRel⊑-ctrl τ (lookup-val x rγ) s (lookup-dep x rγ s xs g rel))
fundamental {Γ = Γ} unit {γ = γ} (⇓-unit) {gi} rγ s x g rel = goal
  where
  goal : ∀ k → ap wsrc (inputs γ s x) k ≈s
               (elim-const unit .at (⟦ unit {Γ} ⟧tm .idxf .sfunc gi) .func s k +ₛ
                ⟦ unit {Γ} ⟧tm .famf .transf gi .func g k)
  goal zero =
    ≈-trans (ap-wsrc {width-env γ} {1} (inputs γ s x) zero)
            (≈-sym (≈-trans (+-cong (ec-unit (⟦ unit {Γ} ⟧tm .idxf .sfunc gi) s) (≈-refl {ε})) +-runit))
fundamental {Γ = Γ} {τ = τ₁ [+] τ₂} (inl {t = t} c) {γ = γ} (⇓-inl {v = v} {R = R'} D) {gi} rγ s x g rel =
  ≈-trans (built-zero {γ = γ} R' s x) (≈-sym (≈-trans (prop._∧_.proj₁ (subst-refl (τ₁ [+] τ₂) {inj₁ i'} e d)) root-den)) ,
  DepRel-resp τ₁ (fundamental-val c D rγ) (λ k → ≈-sym (built-suc {γ = γ} R' s x k))
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
  DepRel-resp τ₂ (fundamental-val c D rγ) (λ k → ≈-sym (built-suc {γ = γ} R' s x k))
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
  DepRel-resp τ (ValRel-resp τ E r') (λ k → ≈-sym (app-case {γ = γ} v R_s T s x k))
    (case-den τ E s a_s (o_s zero) B (⟦ case sc t₁ t₂ ⟧tm .famf .transf gi .func g) o_s₀ case-famf)
    (DepRel-transport τ E r' (fundamental c₁ D₂ (rγ · r_v) (o_s zero +ₛ (w ·ₛ s)) X (g , y_v)
                              (branch-env rγ r_v s x g o_s y_v rel payload₁)))
  where
  rs = fundamental-val c D₁ rγ
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
  r' = fundamental-val c₁ D₂ (rγ · r_v)
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

  payload₁ : DepRel τ₁ r_v (λ m → o_s (suc m)) (F._+_ τ₁ i' y_v (ec τ₁ i' s))
  payload₁ =
    DepRel-resp τ₁ r_v (λ m → ≈-refl)
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
  DepRel-resp τ (ValRel-resp τ E r') (λ k → ≈-sym (app-case {γ = γ} v R_s T s x k))
    (case-den τ E s a_s (o_s zero) B (⟦ case sc t₁ t₂ ⟧tm .famf .transf gi .func g) o_s₀ case-famf)
    (DepRel-transport τ E r' (fundamental c₂ D₂ (rγ · r_v) (o_s zero +ₛ (w ·ₛ s)) X (g , y_v)
                              (branch-env rγ r_v s x g o_s y_v rel payload₁)))
  where
  rs = fundamental-val c D₁ rγ
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
  r' = fundamental-val c₂ D₂ (rγ · r_v)
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

  payload₁ : DepRel τ₂ r_v (λ m → o_s (suc m)) (F._+_ τ₂ i' y_v (ec τ₂ i' s))
  payload₁ =
    DepRel-resp τ₂ r_v (λ m → ≈-refl)
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
  root , (DepRel-resp σ r₁ (λ k → ≈-sym (comp₁ k)) den₁ IH₁ , DepRel-resp τ r₂ (λ k → ≈-sym (comp₂ k)) den₂ IH₂)
  where
  i = ⟦ M ⟧tm .idxf .sfunc gi
  j = ⟦ N ⟧tm .idxf .sfunc gi
  r₁ = fundamental-val c₁ D₁ rγ
  r₂ = fundamental-val c₂ D₂ rγ
  IH₁ = fundamental c₁ D₁ rγ s x g rel
  IH₂ = fundamental c₂ D₂ rγ s x g rel
  o₁ = ap R₁ (inputs γ s x)
  o₂ = ap R₂ (inputs γ s x)
  y₁ = ⟦ M ⟧tm .famf .transf gi .func g
  y₂ = ⟦ N ⟧tm .famf .transf gi .func g
  o = ap (built-out γ (width v + width u) +ₘ (M.in₂ {1} ∘ ⟨ R₁ , R₂ ⟩)) (inputs γ s x)
  d = F._+_ (σ [×] τ) (i , j) (ec (σ [×] τ) (i , j) s) (⟦ pair M N ⟧tm .famf .transf gi .func g)

  tail-eq : ∀ k → o (suc k) ≈s (ap (M.in₁ {width v} {width u}) o₁ k +ₛ ap (M.in₂ {width v} {width u}) o₂ k)
  tail-eq k =
    ≈-trans (built-suc {γ = γ} ⟨ R₁ , R₂ ⟩ s x k)
            (≈-trans (app-+ₘ (M.in₁ {width v} {width u} ∘ R₁) (M.in₂ {width v} {width u} ∘ R₂) (inputs γ s x) k)
                     (+-cong (app-∘ (M.in₁ {width v} {width u}) R₁ (inputs γ s x) k)
                             (app-∘ (M.in₂ {width v} {width u}) R₂ (inputs γ s x) k)))

  root : o zero ≈A proj₁ d
  root =
    ≈-trans (built-zero {γ = γ} ⟨ R₁ , R₂ ⟩ s x)
            (≈-sym (≈-trans (+-cong (prop._∧_.proj₁ (ec-pair {σ} {τ} i j s)) (≈-refl {ε})) +-runit))

  comp₁ : ∀ k → ap (M.p₁ {width v} {width u}) (λ l → o (suc l)) k ≈s o₁ k
  comp₁ k = ≈-trans (app-congᵥ (M.p₁ {width v} {width u}) tail-eq k) (ap-p₁-++ o₁ o₂ k)

  comp₂ : ∀ k → ap (M.p₂ {width v} {width u}) (λ l → o (suc l)) k ≈s o₂ k
  comp₂ k = ≈-trans (app-congᵥ (M.p₂ {width v} {width u}) tail-eq k) (ap-p₂-++ o₁ o₂ k)

  den₁ : F._≈_ σ i (F._+_ σ i (ec σ i s) y₁) (proj₁ (proj₂ d))
  den₁ = F.sym σ i (F.+-cong σ i (prop._∧_.proj₁ (prop._∧_.proj₂ (ec-pair {σ} {τ} i j s))) (m-runit (Fib σ i)))

  den₂ : F._≈_ τ j (F._+_ τ j (ec τ j s) y₂) (proj₂ (proj₂ d))
  den₂ = F.sym τ j (F.+-cong τ j (prop._∧_.proj₂ (prop._∧_.proj₂ (ec-pair {σ} {τ} i j s))) (m-lunit (Fib τ j)))
fundamental {Γ = Γ} {τ = σ} (fst {τ₂ = τ} {t = t} c) {γ = γ} (⇓-fst {v = v} {u = u} {R = R'} D) {gi} rγ s x g rel =
  DepRel-resp σ r₁ (λ k → ≈-sym (proj-op {γ = γ} v {width v} {width u} (M.p₁ {width v} {width u}) R' s x k))
    (proj-den σ i s a₀ (o' zero) (proj₁ (proj₂ (F._+_ (σ [×] τ) ij (ec (σ [×] τ) ij s) Mg)))
       (⟦ fst {τ₂ = τ} t ⟧tm .famf .transf gi .func g) m₁
       o'₀ (F.+-cong σ i (prop._∧_.proj₁ (prop._∧_.proj₂ (ec-pair {σ} {τ} i (proj₂ ij) s))) (F.refl σ i)) G-form)
    (ctrl-add σ r₁ ((w ·ₛ s) +ₛ o' zero) (prop._∧_.proj₁ (prop._∧_.proj₂ IH)))
  where
  ij = ⟦ t ⟧tm .idxf .sfunc gi
  i = proj₁ ij
  r₁ = proj₁ (fundamental-val c D rγ)
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
  DepRel-resp τ r₂ (λ k → ≈-sym (proj-op {γ = γ} u {width v} {width u} (M.p₂ {width v} {width u}) R' s x k))
    (proj-den τ j s a₀ (o' zero) (proj₂ (proj₂ (F._+_ (σ [×] τ) ij (ec (σ [×] τ) ij s) Mg)))
       (⟦ snd {τ₁ = σ} t ⟧tm .famf .transf gi .func g) m₂
       o'₀ (F.+-cong τ j (prop._∧_.proj₂ (prop._∧_.proj₂ (ec-pair {σ} {τ} (proj₁ ij) j s))) (F.refl τ j)) G-form)
    (ctrl-add τ r₂ ((w ·ₛ s) +ₛ o' zero) (prop._∧_.proj₂ (prop._∧_.proj₂ IH)))
  where
  ij = ⟦ t ⟧tm .idxf .sfunc gi
  j = proj₂ ij
  r₂ = proj₂ (fundamental-val c D rγ)
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
  o = ap (lam-out γ t') (inputs γ s x)

  o₀ : o zero ≈s (w ·ₛ s)
  o₀ = ≈-trans (ap-⊕₁-zero {width-env γ} (ctrl-row {1}) M.I (inputs γ s x)) (ap-ctrl-row {1} s zero)

  o-tail : ∀ k → o (suc k) ≈s x k
  o-tail k = ≈-trans (ap-⊕₁-suc {width-env γ} (ctrl-row {1}) M.I (inputs γ s x) k) (app-I x k)

  f = ⟦ lam t' ⟧tm .idxf .sfunc gi

  root : o zero ≈A proj₁ (F._+_ (σ [→] τ) f (ec (σ [→] τ) f s) (⟦ lam t' ⟧tm .famf .transf gi .func g))
  root = ≈-trans o₀ (≈-sym (≈-trans (+-cong (prop._∧_.proj₁ (ec-clo {σ} {τ} f s)) ≈-refl) +-runit))

  clause : ∀ (s' : Setoid.Carrier A) {v : Val σ} {j : Ix σ} (rv : ValRel σ v j)
             (z : ∣ 𝔽 (width v) ∣) (y : ∣ Fib σ j ∣) → DepRel σ rv z y →
           ∀ {u U} (D : γ · v , t' ⇓ u [ U ]) →
             DepRel τ (fundamental-val c D (rγ · rv)) (mat U .func (body-input γ v (s' +ₛ o zero) (λ k → o (suc k)) z))
               (F._+_ τ (f .idxf .sfunc j)
                 (ec τ (f .idxf .sfunc j) (s' +ₛ o zero))
                 (F._+_ τ (f .idxf .sfunc j)
                   (SP.evalΠ (⟦ τ ⟧ .fam indexed-family.[ f .idxf ]) j .func
                      (proj₂ (F._+_ (σ [→] τ) f (ec (σ [→] τ) f s) (⟦ lam t' ⟧tm .famf .transf gi .func g))))
                   (f .famf .transf j .func y)))
  clause s' {v} {j} rv z y hz {u} {U} D =
    DepRel-resp τ (fundamental-val c D (rγ · rv))
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
         (EnvDepRel-resp rγ (s' +ₛ (w ·ₛ s)) (λ k → ≈-sym (ap-p₁-++ x z k)) (EnvDepRel-mono rγ s s' rel) ,
          DepRel⊑-resp σ rv (s' +ₛ (w ·ₛ s)) (λ k → ≈-sym (ap-p₂-++ x z k)) (DepRel⊑-of σ rv (s' +ₛ (w ·ₛ s)) hz)))
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
  DepRel-resp τ r₃ (λ k → ≈-sym (app-op k)) (F.refl τ i₁)
    (DepRel-absorb τ r₃ s (DepRel-resp τ r₃ (λ k → ≈-refl) den-eq C) absG mulE)
  where
  f = ⟦ M ⟧tm .idxf .sfunc gi
  j = ⟦ N ⟧tm .idxf .sfunc gi
  i₁ = f .idxf .sfunc j
  r₁ = fundamental-val c₁ D₁ rγ
  r₂ = fundamental-val c₂ D₂ rγ
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
  C : DepRel τ r₃ (ap U (body-input γ' v ((w ·ₛ s) +ₛ o zero) (λ l → o (suc l)) z))
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
      F.trans τ i₁ (F.+-assoc τ i₁)
      (F.trans τ i₁ (F.+-cong τ i₁ (F.refl τ i₁) inner)
      (F.trans τ i₁ (F.sym τ i₁ (F.+-assoc τ i₁))
                    (F.+-cong τ i₁ (F.+-cong τ i₁ (F.refl τ i₁) (F.sym τ i₁ G-form)) (F.refl τ i₁))))
      where
      inner : F._≈_ τ i₁
                (F._+_ τ i₁ (ec τ i₁ a) (F._+_ τ i₁ (evalΠj .func m) (F._+_ τ i₁ E (f .famf .transf j .func yN))))
                (F._+_ τ i₁ (F._+_ τ i₁ (F._+_ τ i₁ (evalΠj .func m) (f .famf .transf j .func yN)) (ec τ i₁ a)) E)
      inner =
        F.sym τ i₁
          (F.trans τ i₁ (F.+-comm τ i₁)
          (F.trans τ i₁ (F.+-cong τ i₁ (F.refl τ i₁) (F.+-comm τ i₁))
          (F.trans τ i₁ (F.sym τ i₁ (F.+-assoc τ i₁))
          (F.trans τ i₁ (F.+-cong τ i₁ (F.+-comm τ i₁) (F.refl τ i₁))
          (F.trans τ i₁ (F.+-assoc τ i₁)
          (F.trans τ i₁ (F.+-cong τ i₁ (F.refl τ i₁) (F.sym τ i₁ (F.+-assoc τ i₁)))
          (F.trans τ i₁ (F.+-cong τ i₁ (F.refl τ i₁) (F.+-cong τ i₁ (F.+-comm τ i₁) (F.refl τ i₁)))
                        (F.+-cong τ i₁ (F.refl τ i₁) (F.+-assoc τ i₁)))))))))

  absG : F._⊑_ τ i₁ (ec τ i₁ s) G
  absG = F.trans τ i₁ (F.sym τ i₁ (F.+-assoc τ i₁)) (F.+-cong τ i₁ (ec-root τ i₁ s) (F.refl τ i₁))

  mulE : Multiple τ i₁ s E
  mulE = f .famf .transf j .func (ty-unit σ (λ ()) (λ ()) .at j .func ι) ,
         F.trans τ i₁
           (f .famf .transf j .SemiMod._⇒_.func-resp-≈ {ec σ j s}
              {F._·_ σ j (s ·ₛ w) (ty-unit σ (λ ()) (λ ()) .at j .func ι)}
              (F.trans σ j (ty-unit σ (λ ()) (λ ()) .at j .SemiMod._⇒_.func-resp-≈
                              {w ·ₛ s +ₛ ε} {(s ·ₛ w) ·ₛ ι} (≈-trans +-runit (≈-trans ·-comm (≈-sym ·-runit))))
                           (ty-unit σ (λ ()) (λ ()) .at j .SemiMod._⇒_.preserve-· {s ·ₛ w} {ι})))
           (f .famf .transf j .SemiMod._⇒_.preserve-· {s ·ₛ w} {ty-unit σ (λ ()) (λ ()) .at j .func ι})

  -- The application's relation reads the body's at the closure's root and the application's
  -- weighted source as source, and at the closure's cells and the argument as environment.
  app-op : ∀ k → ap (U ∘ (body-inputs γ γ' v ∘ ⟨ ⟨ M.I , R ⟩ , T ⟩)) (inputs γ s x) k
                 ≈s ap U (body-input γ' v ((w ·ₛ s) +ₛ o zero) (λ l → o (suc l)) z) k
  app-op k =
    ≈-trans (app-congₘ (MC.∘-cong₂ {f = U} split) y k)
    (≈-trans (app-∘ U ((from-source +ₘ (from-closure ∘ R)) +ₘ (from-argument ∘ T)) y k)
             (app-congᵥ U body-at k))
    where
    module MC = Category M.cat
    y = inputs γ s x
    from-source : M.Matrix (suc (width-env γ' + width v)) (suc (width-env γ))
    from-source = M.in₁ {1} ∘ wsrc
    from-closure : M.Matrix (suc (width-env γ' + width v)) (suc (width-env γ'))
    from-closure = M.I {1} ⊕ M.in₁ {width-env γ'} {width v}
    from-argument : M.Matrix (suc (width-env γ' + width v)) (width v)
    from-argument = M.in₂ {1} ∘ M.in₂ {width-env γ'} {width v}

    split : (body-inputs γ γ' v ∘ ⟨ ⟨ M.I , R ⟩ , T ⟩) M.≈ₘ ((from-source +ₘ (from-closure ∘ R)) +ₘ (from-argument ∘ T))
    split =
      ≈ₘ-trans (M.∥-pair (from-source M.∥ from-closure) from-argument ⟨ M.I , R ⟩ T)
               (M.+ₘ-cong (≈ₘ-trans (M.∥-pair from-source from-closure M.I R)
                                    (M.+ₘ-cong (MC.id-right {f = from-source}) ≈ₘ-refl))
                          ≈ₘ-refl)

    body-at : ∀ l → ap ((from-source +ₘ (from-closure ∘ R)) +ₘ (from-argument ∘ T)) y l ≈s
                    body-input γ' v ((w ·ₛ s) +ₛ o zero) (λ l' → o (suc l')) z l
    body-at zero =
      ≈-trans (app-+ₘ (from-source +ₘ (from-closure ∘ R)) (from-argument ∘ T) y zero)
      (≈-trans (+-cong (≈-trans (app-+ₘ from-source (from-closure ∘ R) y zero)
                                (+-cong (≈-trans (app-∘ (M.in₁ {1} {width-env γ' + width v}) wsrc y zero)
                                                 (≈-trans (ap-in₁-zero {width-env γ' + width v} (ap wsrc y))
                                                          (ap-wsrc {width-env γ} {1} y zero)))
                                        (≈-trans (app-∘ from-closure R y zero)
                                                 (≈-trans (ap-⊕₁-zero {width-env γ'} M.I (M.in₁ {width-env γ'} {width v}) o)
                                                          (app-I {1} (λ _ → o zero) zero)))))
                       (≈-trans (app-∘ from-argument T y zero)
                                (≈-trans (app-∘ (M.in₂ {1}) (M.in₂ {width-env γ'} {width v}) z zero)
                                         (ap-in₂-zero {width-env γ' + width v} _))))
               +-runit)
    body-at (suc l) =
      ≈-trans (app-+ₘ (from-source +ₘ (from-closure ∘ R)) (from-argument ∘ T) y (suc l))
      (≈-trans (+-cong (≈-trans (app-+ₘ from-source (from-closure ∘ R) y (suc l))
                                (≈-trans (+-cong (≈-trans (app-∘ (M.in₁ {1} {width-env γ' + width v}) wsrc y (suc l))
                                                          (ap-in₁-suc {width-env γ' + width v} (ap wsrc y) l))
                                                 (≈-trans (app-∘ from-closure R y (suc l))
                                                          (ap-⊕₁-suc {width-env γ'} M.I (M.in₁ {width-env γ'} {width v}) o l)))
                                         +-lunit))
                       (≈-trans (app-∘ from-argument T y (suc l))
                                (≈-trans (app-∘ (M.in₂ {1}) (M.in₂ {width-env γ'} {width v}) z (suc l))
                                         (ap-in₂-suc {width-env γ' + width v} _ l))))
               ≈-refl)
fundamental {Γ = Γ} {τ = base o} (bop {is = is} {ω = ω} {Ms = Ms} cs) {γ = γ} (⇓-bop {vs = vs} {R = Rs} D) {gi} rγ s x g rel k =
  ≈-trans (app-+ₘ wsrc (D-vs ∘ Rs) (inputs γ s x) k)
  (≈-trans (+-cong (ap-wsrc {width-env γ} {sort-width o} (inputs γ s x) k)
                   (≈-trans (app-∘ D-vs Rs (inputs γ s x) k)
                   (≈-trans (app-congᵥ D-vs IH k)
                   (≈-trans (app-+ᵥ D-vs (λ _ → w ·ₛ s) Z k)
                            (+-cong (≈-trans (app-congᵥ D-vs (λ _ → ≈-sym ·-runit) k)
                                             (≈-trans (model.app-· D-vs (w ·ₛ s) (λ _ → ι) k) (·-cong ·-comm ≈-refl)))
                                    ≈-refl)))))
  (≈-trans (≈-sym +-assoc)
  (≈-trans (+-cong (sw-absorb s (ap D-vs (λ _ → ι) k)) ≈-refl)
           (+-cong (≈-sym (ec-base i s k)) (≈-sym den)))))
  where
  i = ⟦ bop ω Ms ⟧tm .idxf .sfunc gi
  D-vs = op-deps ω .sfunc vs
  D-c = op-deps ω .sfunc (args-idx Ms gi)
  Z = args-vec Ms gi g
  p = ⟦ Ms ⟧tms .idxf .sfunc gi
  C = IP.collect is .FCμ.famf .transf (interp.𝒟-arg-product is .idxf .sfunc p)
  tp-elt = interp.𝒟-arg-product is .famf .transf p .func (⟦ Ms ⟧tms .famf .transf gi .func g)
  IH : ∀ l → ap Rs (inputs γ s x) l ≈s ((w ·ₛ s) +ₛ Z l)
  IH = fundamental-s cs D rγ s x g rel
  den : ⟦ bop ω Ms ⟧tm .famf .transf gi .func g k ≈s ap D-vs Z k
  den = ≈-trans (app-∘ M.I (D-c ∘ C) tp-elt k)
        (≈-trans (app-I (ap (D-c ∘ C) tp-elt) k)
        (≈-trans (app-∘ D-c C tp-elt k)
                 (app-congₘ (op-deps ω .prop-setoid._⇒_.func-resp-≈ (Prf.prf (fundamental-vals cs D rγ))) Z k)))
fundamental {Γ = Γ} (brel {is = is} {ω = ω} {Ms = Ms} cs) {γ = γ} (⇓-brel {vs = vs} {R = Rs} D) {gi} rγ s x g rel =
  DepRel-bool ω vs b e _ _ s Z op-side model-side
  where
  b = rel-pred ω .sfunc vs
  i = ⟦ brel ω Ms ⟧tm .idxf .sfunc gi
  Z = args-vec Ms gi g
  D-vs = rel-deps ω .sfunc vs
  args-eq = Prf.prf (fundamental-vals cs D rγ)
  e : Setoid._≈_ (⟦ unit [+] unit ⟧ .idx) i b
  e = Setoid.trans (⟦ unit [+] unit ⟧ .idx) {i} {rel-pred ω .sfunc (args-idx Ms gi)} {b}
        (bool-idx (rel-pred ω .sfunc (args-idx Ms gi))) (rel-pred ω .prop-setoid._⇒_.func-resp-≈ args-eq)
  IH : ∀ l → ap Rs (inputs γ s x) l ≈s ((w ·ₛ s) +ₛ Z l)
  IH = fundamental-s cs D rγ s x g rel
  op-side : ∀ k → ap (wsrc +ₘ (brel-deps ω vs b ∘ Rs)) (inputs γ s x) k
                  ≈s ((w ·ₛ s) +ₛ ap (brel-deps ω vs b) (λ l → (w ·ₛ s) +ₛ Z l) k)
  op-side k =
    ≈-trans (app-+ₘ wsrc (brel-deps ω vs b ∘ Rs) (inputs γ s x) k)
            (+-cong (ap-wsrc {width-env γ} {width (bool→val b)} (inputs γ s x) k)
                    (≈-trans (app-∘ (brel-deps ω vs b) Rs (inputs γ s x) k) (app-congᵥ (brel-deps ω vs b) IH k)))
  den = ⟦ brel ω Ms ⟧tm .famf .transf gi .func g
  model-side : F._≈_ (unit [+] unit) b
                 (⟦ unit [+] unit ⟧ .fam .subst {i} {b} e .func (F._+_ (unit [+] unit) i (ec (unit [+] unit) i s) den))
                 (F._+_ (unit [+] unit) b (ec (unit [+] unit) b s) (interp.bool-elt b (ap D-vs Z zero)))
  model-side =
    F.trans (unit [+] unit) b (⟦ unit [+] unit ⟧ .fam .subst {i} {b} e .SemiMod._⇒_.preserve-+ {ec (unit [+] unit) i s} {den})
      (F.+-cong (unit [+] unit) b (ec-natural (unit [+] unit) {i} {b} e s)
        (F.trans (unit [+] unit) b
          (interp.test.test-elt ω (⟦ Ms ⟧tms .idxf .sfunc gi) (⟦ Ms ⟧tms .famf .transf gi .func g) b e)
          (interp.bool-elt-cong b (app-congₘ (rel-deps ω .prop-setoid._⇒_.func-resp-≈ args-eq) Z zero))))

fundamental-s [] [] rγ s x g rel ()
fundamental-s {Ms = _} (c ∷ cs) {γ = γ} (_∷_ {i = i} {is = is} {v = v} {R = R₁} {Rs = Rs} {M = M} {Ms = Ms} D Ds) {gi}
              rγ s x g rel k =
  ≈-trans (app-+ₘ (u₁ ∘ R₁) (u₂ ∘ Rs) (inputs γ s x) k)
  (≈-trans (+-cong (≈-trans (app-∘ u₁ R₁ (inputs γ s x) k)
                            (≈-trans (app-congᵥ u₁ IH₁ k) (app-+ᵥ u₁ (λ _ → w ·ₛ s) y₁ k)))
                   (≈-trans (app-∘ u₂ Rs (inputs γ s x) k)
                            (≈-trans (app-congᵥ u₂ IH₂ k) (app-+ᵥ u₂ (λ _ → w ·ₛ s) Z k))))
  (≈-trans Sc.+-interchange
           (+-cong (in-const {sort-width i} {bases-width is} (w ·ₛ s) k)
                   (≈-sym (args-vec-cons M Ms gi g k)))))
  where
  u₁ = M.in₁ {sort-width i} {bases-width is}
  u₂ = M.in₂ {sort-width i} {bases-width is}
  y₁ = ⟦ M ⟧tm .famf .transf gi .func g
  Z = args-vec Ms gi g
  IH₁ : ∀ l → ap R₁ (inputs γ s x) l ≈s ((w ·ₛ s) +ₛ y₁ l)
  IH₁ l = ≈-trans (fundamental c D rγ s x g rel l) (+-cong (ec-base (⟦ M ⟧tm .idxf .sfunc gi) s l) ≈-refl)
  IH₂ : ∀ l → ap Rs (inputs γ s x) l ≈s ((w ·ₛ s) +ₛ Z l)
  IH₂ = fundamental-s cs Ds rγ s x g rel

-- The interpretation of first-order values and environments, read into the model through the
-- comparison isomorphisms. At a μ-free first-order type a value is related to its interpretation and
-- to no other index, so at such types the fundamental lemma says that a term's value is interpreted
-- as the term's index at the environment's interpretation.
open import value-interpretation S elim-weight Sig ℐ using (⟦_⟧val; ⟦_⟧env)
open Category.Iso using (fwd)

val-idx : ∀ {τ} (fo : first-order τ) → Val τ → Ix τ
val-idx fo v = interp.closed-iso fo .fwd .idxf .sfunc (⟦ fo ⟧val v)

env-idx : ∀ {Γ} (Γ-fo : first-order-ctxt Γ) → Env Γ → IxC Γ
env-idx Γ-fo γ = interp.⟦ Γ-fo ⟧ctxt-iso .fwd .idxf .sfunc (⟦ Γ-fo ⟧env γ)

μ-free : ∀ {Δ} {τ : type Δ} → first-order τ → Set
μ-free (var i)       = ⊤
μ-free unit          = ⊤
μ-free (base s)      = ⊤
μ-free (fo₁ [+] fo₂) = μ-free fo₁ × μ-free fo₂
μ-free (fo₁ [×] fo₂) = μ-free fo₁ × μ-free fo₂
μ-free (μ fo)        = ⊥

μ-free-ctxt : ∀ {Γ} → first-order-ctxt Γ → Set
μ-free-ctxt emp         = ⊤
μ-free-ctxt (Γ-fo ▸ fo) = μ-free-ctxt Γ-fo × μ-free fo

val-rel : ∀ {τ} (fo : first-order τ) → μ-free fo → (v : Val τ) → ValRel τ v (val-idx fo v)
val-rel unit          _         unit       = tt
val-rel (base s)      _         (const c)  = ⟪ Setoid.refl (sort-index s) ⟫
val-rel {τ₁ [+] τ₂} (fo₁ [+] fo₂) (m₁ , m₂) (inl v) =
  val-idx fo₁ v , val-rel fo₁ m₁ v , ⟪ Setoid.refl (⟦ τ₁ [+] τ₂ ⟧ .idx) {inj₁ (val-idx fo₁ v)} ⟫
val-rel {τ₁ [+] τ₂} (fo₁ [+] fo₂) (m₁ , m₂) (inr v) =
  val-idx fo₂ v , val-rel fo₂ m₂ v , ⟪ Setoid.refl (⟦ τ₁ [+] τ₂ ⟧ .idx) {inj₂ (val-idx fo₂ v)} ⟫
val-rel (fo₁ [×] fo₂) (m₁ , m₂) (pair v u) = val-rel fo₁ m₁ v , val-rel fo₂ m₂ u

env-rel : ∀ {Γ} (Γ-fo : first-order-ctxt Γ) → μ-free-ctxt Γ-fo → (γ : Env Γ) →
          EnvValRel γ (env-idx Γ-fo γ)
env-rel emp         _        emp     = emp
env-rel (Γ-fo ▸ fo) (mΓ , m) (γ · v) = env-rel Γ-fo mΓ γ · val-rel fo m v

val-rel-unique : ∀ {τ} (fo : first-order τ) → μ-free fo → {v : Val τ} {i : Ix τ} →
                 ValRel τ v i → Setoid._≈_ (⟦ τ ⟧ .idx) i (val-idx fo v)
val-rel-unique unit          _         {unit}      r = prop.tt
val-rel-unique (base s)      _         {const c}   ⟪ e ⟫ = e
val-rel-unique {τ₁ [+] τ₂} (fo₁ [+] fo₂) (m₁ , m₂) {inl v} {i} (i' , r , ⟪ e ⟫) =
  Setoid.trans (⟦ τ₁ [+] τ₂ ⟧ .idx) {i} {inj₁ i'} {inj₁ (val-idx fo₁ v)} e (val-rel-unique fo₁ m₁ r)
val-rel-unique {τ₁ [+] τ₂} (fo₁ [+] fo₂) (m₁ , m₂) {inr v} {i} (i' , r , ⟪ e ⟫) =
  Setoid.trans (⟦ τ₁ [+] τ₂ ⟧ .idx) {i} {inj₂ i'} {inj₂ (val-idx fo₂ v)} e (val-rel-unique fo₂ m₂ r)
val-rel-unique (fo₁ [×] fo₂) (m₁ , m₂) {pair v u} {i , j} (r , r') =
  val-rel-unique fo₁ m₁ r , val-rel-unique fo₂ m₂ r'

-- Soundness on values, at μ-free first-order types.
soundness-val : ∀ {Γ τ} (Γ-fo : first-order-ctxt Γ) (fo : first-order τ) →
                μ-free-ctxt Γ-fo → μ-free fo →
                ∀ {t : Γ ⊢ τ} (c : CoreTm t) {γ : Env Γ} {v R} (D : γ , t ⇓ v [ R ]) →
                Setoid._≈_ (⟦ τ ⟧ .idx) (⟦ t ⟧tm .idxf .sfunc (env-idx Γ-fo γ)) (val-idx fo v)
soundness-val Γ-fo fo mΓ m c D = val-rel-unique fo m (fundamental-val c D (env-rel Γ-fo mΓ _))

