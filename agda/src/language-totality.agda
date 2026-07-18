{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (_⊔_) renaming (suc to lsuc)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc; _+_; _<_; s≤s)
open import Data.Nat.Properties using (m≤m+n; m≤n+m; n<1+n)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Unit.Polymorphic using (tt) renaming (⊤ to ⊤ₛ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym) renaming (subst to ≡-subst)
open import Relation.Binary.PropositionalEquality.Properties using (subst-subst-sym)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import categories using (Category)
open import signature using (Signature)
open import signature-algebra using (Algebra)
import matrix

-- Computability (totality) predicate on values: the existence content of the
-- logical relation, without the denotational component. Its fundamental lemma
-- is normalisation, yielding a total evaluator.
module language-totality
  {ℓ ℓ'} (Sig : Signature ℓ) (𝒜 : Algebra Sig ℓ')
  {o e} {A : Setoid o e} (S : CommutativeSemiring A)
  (sort-width : Signature.sort Sig → ℕ)
  where

open Signature Sig
open Algebra 𝒜
open import language-syntax Sig renaming (_,_ to _▸_)
open import type-substitution Sig using (unfold₁; unfold₁-inst; size; arr-bound; arr-self; unfold₁-arr)
open import language-evaluation Sig 𝒜
  using (Val; Env; unit; const; inl; inr; pair; clo; roll; emp; _·_)
open import language-evaluation-mat Sig 𝒜 S sort-width
  using (width; width-env; bases-width; module WithOpMats)

private
  module M = matrix.Mat S

module WithOp
  (op-mat : ∀ {is o'} → op is o' → Category._⇒_ M.cat (bases-width is) (sort-width o'))
  where

  open WithOpMats op-mat

  private
    ℓT = ℓ ⊔ ℓ' ⊔ o ⊔ e

  TSpec : type 0 → Set (lsuc ℓT)
  TSpec τ = Val τ → Set ℓT

  data MuTotal (τ₀ : type 1)
               (T< : (σ : type 0) → size σ < size (μ τ₀) → TSpec σ) :
               (σ' : type 1) → Val (σ' [ μ τ₀ ]) → Set ℓT where
    mt-roll  : ∀ {w} → MuTotal τ₀ T< τ₀ w → MuTotal τ₀ T< (var Fin.zero) (roll w)
    mt-unit  : MuTotal τ₀ T< unit unit
    mt-base  : ∀ {s c} → MuTotal τ₀ T< (base s) (const c)
    mt-arrow : ∀ {σ₁ σ₂ : type 0} {v} →
               (p : size {1} (σ₁ [→] σ₂) < size (μ τ₀)) →
               T< (σ₁ [→] σ₂) p v →
               MuTotal τ₀ T< (σ₁ [→] σ₂) v
    mt-inl   : ∀ {σ₁ σ₂ : type 1} {v} →
               MuTotal τ₀ T< σ₁ v → MuTotal τ₀ T< (σ₁ [+] σ₂) (inl v)
    mt-inr   : ∀ {σ₁ σ₂ : type 1} {v} →
               MuTotal τ₀ T< σ₂ v → MuTotal τ₀ T< (σ₁ [+] σ₂) (inr v)
    mt-pair  : ∀ {σ₁ σ₂ : type 1} {v₁ v₂} →
               MuTotal τ₀ T< σ₁ v₁ → MuTotal τ₀ T< σ₂ v₂ →
               MuTotal τ₀ T< (σ₁ [×] σ₂) (pair v₁ v₂)
    mt-mu    : ∀ {τ' : type 2} {w} →
               MuTotal τ₀ T< (unfold₁ τ') w →
               MuTotal τ₀ T< (μ τ') (roll (≡-subst Val (unfold₁-inst τ' (μ τ₀)) w))

  Total-acc : (τ : type 0) → Acc _<_ (size τ) → TSpec τ
  Total-acc (var ())
  Total-acc unit _ v = ⊤ₛ {ℓT}
  Total-acc (base s) _ v = ⊤ₛ {ℓT}
  Total-acc (σ [+] τ) (acc rs) (inl v) =
    Total-acc σ (rs (s≤s (m≤m+n (size σ) (size τ)))) v
  Total-acc (σ [+] τ) (acc rs) (inr v) =
    Total-acc τ (rs (s≤s (m≤n+m (size τ) (size σ)))) v
  Total-acc (σ [×] τ) (acc rs) (pair v u) =
    Total-acc σ (rs (s≤s (m≤m+n (size σ) (size τ)))) v ×
    Total-acc τ (rs (s≤s (m≤n+m (size τ) (size σ)))) u
  Total-acc (σ [→] τ) (acc rs) (clo {Γ'} γ' t) =
    ∀ (v : Val σ) → Total-acc σ (rs (s≤s (m≤m+n (size σ) (size τ)))) v →
    Σ (Val τ) λ u →
    Σ (Category._⇒_ M.cat (width-env γ' + width v) (width u)) λ R →
    (γ' · v ,, t ⇓ u [ R ]) ×
    Total-acc τ (rs (s≤s (m≤n+m (size τ) (size σ)))) u
  Total-acc (μ τ₀) (acc rs) v =
    MuTotal τ₀ (λ σ p → Total-acc σ (rs p)) (var Fin.zero) v

  Total : (τ : type 0) → TSpec τ
  Total τ = Total-acc τ (<-wellFounded (size τ))

  TotalEnv : (Γ : ctxt) → Env Γ → Set ℓT
  TotalEnv emp emp = ⊤ₛ {ℓT}
  TotalEnv (Γ ▸ τ) (γ · v) = TotalEnv Γ γ × Total τ v

  mu-total-map : ∀ {τ₀} {T< T<' : (σ : type 0) → size σ < size (μ τ₀) → TSpec σ} →
                 (∀ σ p {v} → T< σ p v → T<' σ p v) →
                 ∀ {σ' v} → MuTotal τ₀ T< σ' v → MuTotal τ₀ T<' σ' v
  mu-total-map f (mt-roll m)     = mt-roll (mu-total-map f m)
  mu-total-map f mt-unit         = mt-unit
  mu-total-map f mt-base         = mt-base
  mu-total-map f (mt-arrow p t)  = mt-arrow p (f _ p t)
  mu-total-map f (mt-inl m)      = mt-inl (mu-total-map f m)
  mu-total-map f (mt-inr m)      = mt-inr (mu-total-map f m)
  mu-total-map f (mt-pair m m')  = mt-pair (mu-total-map f m) (mu-total-map f m')
  mu-total-map f (mt-mu m)       = mt-mu (mu-total-map f m)

  -- Total-acc does not depend on the accessibility proof.
  total-irr-acc : ∀ τ → Acc _<_ (size τ) →
                  ∀ {ac ac' : Acc _<_ (size τ)} {v} →
                  Total-acc τ ac v → Total-acc τ ac' v
  total-irr-acc unit _ t = t
  total-irr-acc (base s) _ t = t
  total-irr-acc (σ [+] τ) (acc as) {acc rs} {acc rs'} {inl v} t =
    total-irr-acc σ (as (s≤s (m≤m+n (size σ) (size τ)))) t
  total-irr-acc (σ [+] τ) (acc as) {acc rs} {acc rs'} {inr v} t =
    total-irr-acc τ (as (s≤s (m≤n+m (size τ) (size σ)))) t
  total-irr-acc (σ [×] τ) (acc as) {acc rs} {acc rs'} {pair v u} (t , t') =
    total-irr-acc σ (as (s≤s (m≤m+n (size σ) (size τ)))) t ,
    total-irr-acc τ (as (s≤s (m≤n+m (size τ) (size σ)))) t'
  total-irr-acc (σ [→] τ) (acc as) {acc rs} {acc rs'} {clo γ' t₀} f = λ v tv →
    let (u , R , D , tu) = f v (total-irr-acc σ (as (s≤s (m≤m+n (size σ) (size τ)))) tv)
    in u , R , D , total-irr-acc τ (as (s≤s (m≤n+m (size τ) (size σ)))) tu
  total-irr-acc (μ τ₀) (acc as) {acc rs} {acc rs'} m =
    mu-total-map (λ σ p t → total-irr-acc σ (as p) t) m

  total-irr : ∀ τ {ac ac' : Acc _<_ (size τ)} {v} →
              Total-acc τ ac v → Total-acc τ ac' v
  total-irr τ = total-irr-acc τ (<-wellFounded (size τ))

  -- Canonical mu family, with the totality predicate itself at arrow leaves.
  MuT : (τ₀ : type 1) (σ' : type 1) → Val (σ' [ μ τ₀ ]) → Set ℓT
  MuT τ₀ = MuTotal τ₀ (λ σ p → Total σ)

  -- Introduction and elimination for Total at each connective.
  sum-out₁ : ∀ {σ τ v} → Total (σ [+] τ) (inl v) → Total σ v
  sum-out₁ {σ} t = total-irr σ t

  sum-out₂ : ∀ {σ τ v} → Total (σ [+] τ) (inr v) → Total τ v
  sum-out₂ {σ} {τ} t = total-irr τ t

  sum-in₁ : ∀ {σ τ v} → Total σ v → Total (σ [+] τ) (inl v)
  sum-in₁ {σ} t = total-irr σ t

  sum-in₂ : ∀ {σ τ v} → Total τ v → Total (σ [+] τ) (inr v)
  sum-in₂ {σ} {τ} t = total-irr τ t

  prod-out : ∀ {σ τ v u} → Total (σ [×] τ) (pair v u) → Total σ v × Total τ u
  prod-out {σ} {τ} (t , t') = total-irr σ t , total-irr τ t'

  prod-in : ∀ {σ τ v u} → Total σ v → Total τ u → Total (σ [×] τ) (pair v u)
  prod-in {σ} {τ} t t' = total-irr σ t , total-irr τ t'

  mu-out : ∀ {τ₀ v} → Total (μ τ₀) v → MuT τ₀ (var Fin.zero) v
  mu-out m = mu-total-map (λ σ p t → total-irr σ t) m

  mu-in : ∀ {τ₀ v} → MuT τ₀ (var Fin.zero) v → Total (μ τ₀) v
  mu-in m = mu-total-map (λ σ p t → total-irr σ t) m

  -- Value size, invariant under transport; drives the mutual recursion below.
  vsize : ∀ {τ : type 0} → Val τ → ℕ
  vsize unit       = 1
  vsize (const c)  = 1
  vsize (clo γ t)  = 1
  vsize (inl v)    = suc (vsize v)
  vsize (inr v)    = suc (vsize v)
  vsize (pair v u) = suc (vsize v + vsize u)
  vsize (roll v)   = suc (vsize v)

  vsize-subst : ∀ {σ σ' : type 0} (e : σ ≡ σ') (w : Val σ) → vsize (≡-subst Val e w) ≡ vsize w
  vsize-subst refl w = refl

  total-coerce : ∀ {σ σ' : type 0} (e : σ ≡ σ') {v : Val σ} →
                 Total σ v → Total σ' (≡-subst Val e v)
  total-coerce refl t = t

  -- Totality at a substituted type versus membership of the mu family. The
  -- nested case crosses between the outer family and the family of the inner
  -- body through Total at the propositionally equal type.
  fold-tot-acc : ∀ (τ₀ σ' : type 1) → arr-bound (size (μ τ₀)) σ' →
                 ∀ {v : Val (σ' [ μ τ₀ ])} → Acc _<_ (vsize v) →
                 Total (σ' [ μ τ₀ ]) v → MuT τ₀ σ' v
  unfold-tot-acc : ∀ (τ₀ σ' : type 1) →
                   ∀ {v : Val (σ' [ μ τ₀ ])} → Acc _<_ (vsize v) →
                   MuT τ₀ σ' v → Total (σ' [ μ τ₀ ]) v

  fold-tot-acc τ₀ (var Fin.zero) b av t = mu-out t
  fold-tot-acc τ₀ unit b {unit} av t = mt-unit
  fold-tot-acc τ₀ (base s) b {const c} av t = mt-base
  fold-tot-acc τ₀ (σ₁ [+] σ₂) (b₁ , b₂) {inl v₁} (acc ra) t =
    mt-inl (fold-tot-acc τ₀ σ₁ b₁ (ra (n<1+n _)) (sum-out₁ {σ₁ [ μ τ₀ ]} {σ₂ [ μ τ₀ ]} t))
  fold-tot-acc τ₀ (σ₁ [+] σ₂) (b₁ , b₂) {inr v₂} (acc ra) t =
    mt-inr (fold-tot-acc τ₀ σ₂ b₂ (ra (n<1+n _)) (sum-out₂ {σ₁ [ μ τ₀ ]} {σ₂ [ μ τ₀ ]} t))
  fold-tot-acc τ₀ (σ₁ [×] σ₂) (b₁ , b₂) {pair v₁ v₂} (acc ra) t =
    mt-pair (fold-tot-acc τ₀ σ₁ b₁ (ra (s≤s (m≤m+n (vsize v₁) (vsize v₂)))) (Data.Product.proj₁ (prod-out {σ₁ [ μ τ₀ ]} {σ₂ [ μ τ₀ ]} t)))
            (fold-tot-acc τ₀ σ₂ b₂ (ra (s≤s (m≤n+m (vsize v₂) (vsize v₁)))) (Data.Product.proj₂ (prod-out {σ₁ [ μ τ₀ ]} {σ₂ [ μ τ₀ ]} t)))
    where import Data.Product
  fold-tot-acc τ₀ (σ₁ [→] σ₂) b av t = mt-arrow b t
  fold-tot-acc τ₀ (μ τ') b {roll w₂} (acc ra) t
    with mu-out {τ₀ = sub (sub-lift (push (μ τ₀))) τ'} t
  ... | mt-roll m₂ =
    ≡-subst (λ x → MuT τ₀ (μ τ') (roll x)) (subst-subst-sym (unfold₁-inst τ' (μ τ₀)))
      (mt-mu (fold-tot-acc τ₀ (unfold₁ τ') (unfold₁-arr τ' b)
               (ra (≡-subst (λ n → n < suc (vsize w₂))
                            (sym (vsize-subst (sym (unfold₁-inst τ' (μ τ₀))) w₂))
                            (n<1+n _)))
               (total-coerce (sym (unfold₁-inst τ' (μ τ₀)))
                 (unfold-tot-acc (sub (sub-lift (push (μ τ₀))) τ')
                                 (sub (sub-lift (push (μ τ₀))) τ')
                                 (ra (n<1+n _)) m₂))))

  unfold-tot-acc τ₀ (var Fin.zero) av m = mu-in m
  unfold-tot-acc τ₀ unit av m = tt
  unfold-tot-acc τ₀ (base s) av m = tt
  unfold-tot-acc τ₀ (σ₁ [+] σ₂) (acc ra) (mt-inl m) =
    sum-in₁ {σ₁ [ μ τ₀ ]} {σ₂ [ μ τ₀ ]} (unfold-tot-acc τ₀ σ₁ (ra (n<1+n _)) m)
  unfold-tot-acc τ₀ (σ₁ [+] σ₂) (acc ra) (mt-inr m) =
    sum-in₂ {σ₁ [ μ τ₀ ]} {σ₂ [ μ τ₀ ]} (unfold-tot-acc τ₀ σ₂ (ra (n<1+n _)) m)
  unfold-tot-acc τ₀ (σ₁ [×] σ₂) (acc ra) (mt-pair {v₁ = v₁} {v₂ = v₂} m₁ m₂) =
    prod-in {σ₁ [ μ τ₀ ]} {σ₂ [ μ τ₀ ]} (unfold-tot-acc τ₀ σ₁ (ra (s≤s (m≤m+n (vsize v₁) (vsize v₂)))) m₁)
      (unfold-tot-acc τ₀ σ₂ (ra (s≤s (m≤n+m (vsize v₂) (vsize v₁)))) m₂)
  unfold-tot-acc τ₀ (σ₁ [→] σ₂) av (mt-arrow p t) = t
  unfold-tot-acc τ₀ (μ τ') (acc ra) (mt-mu {w = w} m) =
    mu-in (mt-roll (fold-tot-acc B B (arr-self B) (ra (n<1+n _))
             (total-coerce E (unfold-tot-acc τ₀ (unfold₁ τ')
                (ra (≡-subst (λ n → n < suc (vsize (≡-subst Val E w))) (vsize-subst E w) (n<1+n _)))
                m))))
    where
    B : type 1
    B = sub (sub-lift (push (μ τ₀))) τ'
    E : (unfold₁ τ' [ μ τ₀ ]) ≡ (B [ μ B ])
    E = unfold₁-inst τ' (μ τ₀)

  fold-tot : ∀ (τ₀ σ' : type 1) → arr-bound (size (μ τ₀)) σ' →
             ∀ {v} → Total (σ' [ μ τ₀ ]) v → MuT τ₀ σ' v
  fold-tot τ₀ σ' b {v} = fold-tot-acc τ₀ σ' b (<-wellFounded (vsize v))

  unfold-tot : ∀ (τ₀ σ' : type 1) → ∀ {v} → MuT τ₀ σ' v → Total (σ' [ μ τ₀ ]) v
  unfold-tot τ₀ σ' {v} = unfold-tot-acc τ₀ σ' (<-wellFounded (vsize v))
