{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (0ℓ) renaming (suc to lsuc)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc; _+_; _<_; s≤s)
open import Data.Nat.Properties using (m≤m+n; m≤n+m; n<1+n)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import every using (Every; []; _∷_)
open import Data.Unit.Polymorphic using (tt) renaming (⊤ to ⊤ₛ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym) renaming (subst to ≡-subst)
open import Relation.Binary.PropositionalEquality.Properties using (subst-subst-sym)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import categories using (Category)
open import signature using (Signature)
open import signature.interpretation using (Interpretation)
import matrix

-- Computability (totality) predicate on values: the existence
-- content of the logical relation, without the denotational component. Its fundamental lemma is
-- normalisation, yielding a total evaluator.
module language-operational.totality
  {ℓ} (Sig : Signature ℓ)
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (ℐ : Interpretation S Sig) (ctrl-weight : Setoid.Carrier A) where

open Signature Sig
open Interpretation ℐ
open prop-setoid._⇒_ using (func)
open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.type-substitution Sig using (unfold₁; unfold₁-inst; size; arr-bound; arr-self; unfold₁-arr)
open import language-operational.evaluation Sig S ℐ ctrl-weight
  renaming (size to vsize; size-subst to vsize-subst)

private
  module M = matrix.Mat S

open Category M.cat using (_⇒_)
open M using (⟨_,_⟩)

private
  ℓT = ℓ

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
  Σ (Category._⇒_ M.cat (suc (width-env γ' + width v)) (width u)) λ R →
  (γ' · v , t ⇓ u [ R ]) ×
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

MuT : (τ₀ : type 1) (σ' : type 1) → Val (σ' [ μ τ₀ ]) → Set ℓT
MuT τ₀ = MuTotal τ₀ (λ σ p → Total σ)

mu-out : ∀ {τ₀ v} → Total (μ τ₀) v → MuT τ₀ (var Fin.zero) v
mu-out m = mu-total-map (λ σ p t → total-irr σ t) m

mu-in : ∀ {τ₀ v} → MuT τ₀ (var Fin.zero) v → Total (μ τ₀) v
mu-in m = mu-total-map (λ σ p t → total-irr σ t) m

total-coerce : ∀ {σ σ' : type 0} (e : σ ≡ σ') {v : Val σ} →
               Total σ v → Total σ' (≡-subst Val e v)
total-coerce refl t = t

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
  mt-inl (fold-tot-acc τ₀ σ₁ b₁ (ra (n<1+n _)) (total-irr (σ₁ [ μ τ₀ ]) t))
fold-tot-acc τ₀ (σ₁ [+] σ₂) (b₁ , b₂) {inr v₂} (acc ra) t =
  mt-inr (fold-tot-acc τ₀ σ₂ b₂ (ra (n<1+n _)) (total-irr (σ₂ [ μ τ₀ ]) t))
fold-tot-acc τ₀ (σ₁ [×] σ₂) (b₁ , b₂) {pair v₁ v₂} (acc ra) t =
  mt-pair (fold-tot-acc τ₀ σ₁ b₁ (ra (s≤s (m≤m+n (vsize v₁) (vsize v₂)))) (total-irr (σ₁ [ μ τ₀ ]) (Data.Product.proj₁ t)))
          (fold-tot-acc τ₀ σ₂ b₂ (ra (s≤s (m≤n+m (vsize v₂) (vsize v₁)))) (total-irr (σ₂ [ μ τ₀ ]) (Data.Product.proj₂ t)))
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
  total-irr (σ₁ [ μ τ₀ ]) (unfold-tot-acc τ₀ σ₁ (ra (n<1+n _)) m)
unfold-tot-acc τ₀ (σ₁ [+] σ₂) (acc ra) (mt-inr m) =
  total-irr (σ₂ [ μ τ₀ ]) (unfold-tot-acc τ₀ σ₂ (ra (n<1+n _)) m)
unfold-tot-acc τ₀ (σ₁ [×] σ₂) (acc ra) (mt-pair {v₁ = v₁} {v₂ = v₂} m₁ m₂) =
  total-irr (σ₁ [ μ τ₀ ]) (unfold-tot-acc τ₀ σ₁ (ra (s≤s (m≤m+n (vsize v₁) (vsize v₂)))) m₁) ,
  total-irr (σ₂ [ μ τ₀ ]) (unfold-tot-acc τ₀ σ₂ (ra (s≤s (m≤n+m (vsize v₂) (vsize v₁)))) m₂)
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

lookup-total : ∀ {Γ τ} (x : Γ ∋ τ) {γ : Env Γ} → TotalEnv Γ γ → Total τ (lookup x γ)
lookup-total zero     {γ · v} (tγ , tv) = tv
lookup-total (succ x) {γ · v} (tγ , tv) = lookup-total x tγ

bool-total : ∀ (b : _) → Total (unit [+] unit) (bool→val b)
bool-total (inj₁ _) = tt
bool-total (inj₂ _) = tt

ArrTot : (σ τ : type 0) {Γ' : ctxt} (γ' : Env Γ') (t : (Γ' ▸ σ) ⊢ τ) → Set ℓT
ArrTot σ τ {Γ'} γ' t =
  ∀ (v : Val σ) → Total σ v →
  Σ (Val τ) λ u → Σ (suc (width-env γ' + width v) ⇒ width u) λ R →
  ((γ' · v) , t ⇓ u [ R ]) × Total τ u

arr-in : ∀ {σ τ Γ'} {γ' : Env Γ'} {t : (Γ' ▸ σ) ⊢ τ} →
         ArrTot σ τ γ' t → Total (σ [→] τ) (clo γ' t)
arr-in {σ} {τ} f v tv =
  let (u , R , D , tu) = f v (total-irr σ tv) in u , R , D , total-irr τ tu

arr-out : ∀ {σ τ Γ'} {γ' : Env Γ'} {t : (Γ' ▸ σ) ⊢ τ} →
          Total (σ [→] τ) (clo γ' t) → ArrTot σ τ γ' t
arr-out {σ} {τ} f v tv =
  let (u , R , D , tu) = f v (total-irr σ tv) in u , R , D , total-irr τ tu

map-total : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : (Γ ▸ (τ₀ [ σr ])) ⊢ σr} →
            (∀ (w' : Val (τ₀ [ σr ])) → Total (τ₀ [ σr ]) w' →
             Σ (Val σr) λ u → Σ (suc (width-env γ + width w') ⇒ width u) λ S →
             ((γ · w') , s ⇓ u [ S ]) × Total σr u) →
            ∀ (σ' : type 1) {v : Val (σ' [ μ τ₀ ])} → MuT τ₀ σ' v →
            Σ (Val (σ' [ σr ])) λ v' →
            Σ ((suc (width-env γ) + width v) ⇒ width v') λ F →
            Map γ s σ' v v' F × Total (σ' [ σr ]) v'
map-total {γ = γ} f (var Fin.zero) (mt-roll m') =
  let (w' , F , Dm , tw') = map-total f _ m'
      (u , S , Ds , tu) = f w' tw'
  in u , _ , m-rec Dm Ds , tu
map-total f unit {v} mt-unit = v , _ , m-unit , tt
map-total f (base b) {v} mt-base = v , _ , m-base , tt
map-total f (σ₁ [→] σ₂) {v} (mt-arrow p tv) = v , _ , m-arrow , tv
map-total {σr = σr} f (σ₁ [+] σ₂) (mt-inl {v = v} m') =
  let (v' , F , Dm , tv') = map-total f σ₁ m'
  in inl v' , _ , m-inl Dm , total-irr (σ₁ [ σr ]) tv'
map-total {σr = σr} f (σ₁ [+] σ₂) (mt-inr {v = v} m') =
  let (v' , F , Dm , tv') = map-total f σ₂ m'
  in inr v' , _ , m-inr Dm , total-irr (σ₂ [ σr ]) tv'
map-total {σr = σr} f (σ₁ [×] σ₂) (mt-pair {v₁ = v₁} {v₂ = v₂} m₁ m₂) =
  let (v₁' , F , D₁ , t₁) = map-total f σ₁ m₁
      (v₂' , G , D₂ , t₂) = map-total f σ₂ m₂
  in pair v₁' v₂' , _ , m-pair D₁ D₂ , (total-irr (σ₁ [ σr ]) t₁ , total-irr (σ₂ [ σr ]) t₂)
map-total {γ = γ} {τ₀ = τ₀} {σr = σr} {s = s} f (μ τ') (mt-mu {τ'} {w} m') =
  let (w' , F , Dm , tw') = map-total f (unfold₁ τ') m'
  in roll (≡-subst Val (unfold₁-inst τ' σr) w') , _ , m-mu Dm ,
     mu-in (mt-roll (fold-tot (sub (sub-lift (push σr)) τ') (sub (sub-lift (push σr)) τ')
                      (arr-self (sub (sub-lift (push σr)) τ'))
                      (total-coerce (unfold₁-inst τ' σr) tw')))

Eval : ∀ {Γ} (γ : Env Γ) {τ} (t : Γ ⊢ τ) → Set ℓT
Eval γ {τ} t =
  Σ (Val τ) λ v → Σ (suc (width-env γ) ⇒ width v) λ R → (γ , t ⇓ v [ R ]) × Total τ v

fundamental : ∀ {Γ τ} (t : Γ ⊢ τ) (γ : Env Γ) → TotalEnv Γ γ → Eval γ t
fundamental-s : ∀ {Γ is} (Ms : Every (λ s₁ → Γ ⊢ base s₁) is) (γ : Env Γ) → TotalEnv Γ γ →
                Σ (sort-vals is) λ vs →
                Σ (suc (width-env γ) ⇒ bases-width is) λ Rs → γ , Ms ⇓s vs [ Rs ]

fundamental (var x) γ tγ =
  lookup x γ , _ , ⇓-var x , lookup-total x tγ
fundamental unit γ tγ = unit , _ , ⇓-unit , tt
fundamental (inl {τ₁ = τ₁} {τ₂ = τ₂} t) γ tγ =
  let (v , R , D , tv) = fundamental t γ tγ
  in inl v , _ , ⇓-inl D , total-irr τ₁ tv
fundamental (inr {τ₁ = τ₁} {τ₂ = τ₂} t) γ tγ =
  let (v , R , D , tv) = fundamental t γ tγ
  in inr v , _ , ⇓-inr D , total-irr τ₂ tv
fundamental (case {τ₁ = τ₁} {τ₂ = τ₂} s t₁ t₂) γ tγ with fundamental s γ tγ
... | inl v , R , D , ts =
  let (u , S , D₁ , tu) = fundamental t₁ (γ · v) (tγ , total-irr τ₁ ts)
  in u , _ , ⇓-case-l D D₁ , tu
... | inr v , R , D , ts =
  let (u , S , D₂ , tu) = fundamental t₂ (γ · v) (tγ , total-irr τ₂ ts)
  in u , _ , ⇓-case-r D D₂ , tu
fundamental (pair {τ₁ = τ₁} {τ₂ = τ₂} s t) γ tγ =
  let (v , R , D , tv) = fundamental s γ tγ
      (u , S , D' , tu) = fundamental t γ tγ
  in pair v u , _ , ⇓-pair D D' , (total-irr τ₁ tv , total-irr τ₂ tu)
fundamental (fst {τ₁ = τ₁} {τ₂ = τ₂} t) γ tγ with fundamental t γ tγ
... | pair v u , R , D , tv =
  v , _ , ⇓-fst D ,
  total-irr τ₁ (proj₁ tv)
fundamental (snd {τ₁ = τ₁} {τ₂ = τ₂} t) γ tγ with fundamental t γ tγ
... | pair v u , R , D , tv =
  u , _ , ⇓-snd D ,
  total-irr τ₂ (proj₂ tv)
fundamental (lam t) γ tγ =
  clo γ t , _ , ⇓-lam , arr-in (λ v tv → fundamental t (γ · v) (tγ , tv))
fundamental (app s t) γ tγ with fundamental s γ tγ
... | clo γ' t' , R , Ds , tf =
  let (v , S , Dt , tv) = fundamental t γ tγ
      (u , T , D' , tu) = arr-out tf v tv
  in u , _ , ⇓-app Ds Dt D' , tu
fundamental (bop ω Ms) γ tγ =
  let (vs , Rs , Dss) = fundamental-s Ms γ tγ
  in const (op-fun ω .func vs) , _ , ⇓-bop Dss , tt
fundamental (brel ω Ms) γ tγ =
  let (vs , Rs , Dss) = fundamental-s Ms γ tγ
  in bool→val (rel-pred ω .func vs) , _ , ⇓-brel Dss ,
     bool-total (rel-pred ω .func vs)
fundamental (roll {τ = τ₀} t) γ tγ =
  let (v , R , D , tv) = fundamental t γ tγ
  in roll v , _ , ⇓-roll D , mu-in (mt-roll (fold-tot τ₀ τ₀ (arr-self τ₀) tv))
fundamental (fold s t) γ tγ =
  let (v , R , D , tv) = fundamental t γ tγ
      (u , R' , Dm , tu) =
        map-total (λ w' tw' → fundamental s (γ · w') (tγ , tw'))
                  (var Fin.zero) (mu-out tv)
  in u , _ , ⇓-fold D Dm , tu

fundamental-s [] γ tγ = _ , _ , []
fundamental-s (M ∷ Ms) γ tγ with fundamental M γ tγ
... | const v , R , D , _ =
  let (vs , Rs , Dss) = fundamental-s Ms γ tγ
  in (v , vs) , _ , (D ∷ Dss)

val-total : ∀ {τ} (v : Val τ) → Total τ v
env-total : ∀ {Γ} (γ : Env Γ) → TotalEnv Γ γ

val-total unit = tt
val-total (const _) = tt
val-total (inl {τ₁ = τ₁} {τ₂ = τ₂} v) = total-irr τ₁ (val-total v)
val-total (inr {τ₁ = τ₁} {τ₂ = τ₂} v) = total-irr τ₂ (val-total v)
val-total (pair {τ₁ = τ₁} {τ₂ = τ₂} v u) = total-irr τ₁ (val-total v) , total-irr τ₂ (val-total u)
val-total (clo γ t) = arr-in (λ v tv → fundamental t (γ · v) (env-total γ , tv))
val-total (roll {τ = τ₀} v) = mu-in (mt-roll (fold-tot τ₀ τ₀ (arr-self τ₀) (val-total v)))

env-total emp = tt
env-total (γ · v) = env-total γ , val-total v

eval : ∀ {Γ τ} (t : Γ ⊢ τ) (γ : Env Γ) →
       Σ (Val τ) λ v → Σ (suc (width-env γ) ⇒ width v) λ R → γ , t ⇓ v [ R ]
eval t γ = let (v , R , D , _) = fundamental t γ (env-total γ) in v , R , D
