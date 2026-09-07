{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (0ℓ) renaming (suc to lsuc)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc; _+_; _<_; _≤_; s≤s)
open import Data.Nat.Properties using (≤-refl; m≤m+n; m≤n+m; n<1+n)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.List.Relation.Unary.All using ([]; _∷_) renaming (All to Every)
open import Data.Unit.Polymorphic using (tt) renaming (⊤ to ⊤ₛ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym) renaming (subst to ≡-subst)
open import Relation.Binary.PropositionalEquality.Properties using (subst-subst-sym)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import categories using (Category)
open import signature using (Signature)
open import signature.interpretation using (Interpretation)
import matrix-embedding
import semimodule

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
open import language-operational.type-substitution Sig using (unfold₁; unfold₁-inst)
open import language-operational.evaluation Sig S ℐ ctrl-weight
  renaming (size to vsize; size-subst to vsize-subst)

private
  module SemiMod = semimodule S

open import matrix-embedding S using (𝔽)
open Category SemiMod.cat using (_⇒_)

private
  ℓT = ℓ

Total′ : ∀ (N : ℕ) (τ : type 0) → arr-depth τ ≤ N → Val τ → Set ℓT
Total′ N unit p v = ⊤ₛ {ℓT}
Total′ N (base s) p v = ⊤ₛ {ℓT}
Total′ N (σ [+] τ) p (inl v) = Total′ N σ (bound₁ p) v
Total′ N (σ [+] τ) p (inr v) = Total′ N τ (bound₂ p) v
Total′ N (σ [×] τ) p (pair v u) = Total′ N σ (bound₁ p) v × Total′ N τ (bound₂ p) u
Total′ (suc N) (σ [→] τ) (s≤s p) (clo γ' t) =
  ∀ (v : Val σ) → Total′ N σ (bound₁ p) v →
  Σ (Val τ) λ u →
  Σ (𝔽 (suc (width-env γ' + width v)) ⇒ 𝔽 (width u)) λ R →
  (γ' · v , t ⇓ u [ R ]) × Total′ N τ (bound₂ p) u
Total′ N (μ τ) p (roll v) = Total′ N (τ [ μ τ ]) (bound-μ τ p) v

Total : (τ : type 0) → Val τ → Set ℓT
Total τ = Total′ (arr-depth τ) τ ≤-refl

TotalEnv : (Γ : ctxt) → Env Γ → Set ℓT
TotalEnv emp emp = ⊤ₛ {ℓT}
TotalEnv (Γ ▸ τ) (γ · v) = TotalEnv Γ γ × Total τ v

Total′-bounds : ∀ {N N'} τ {p : arr-depth τ ≤ N} {p' : arr-depth τ ≤ N'} {v : Val τ} →
                (Total′ N τ p v → Total′ N' τ p' v) × (Total′ N' τ p' v → Total′ N τ p v)
Total′-bounds unit = (λ t → t) , (λ t → t)
Total′-bounds (base s) = (λ t → t) , (λ t → t)
Total′-bounds (σ [+] τ) {v = inl v} = Total′-bounds σ
Total′-bounds (σ [+] τ) {v = inr v} = Total′-bounds τ
Total′-bounds (σ [×] τ) {v = pair v u} =
  (λ (t , t') → proj₁ (Total′-bounds σ) t , proj₁ (Total′-bounds τ) t') ,
  (λ (t , t') → proj₂ (Total′-bounds σ) t , proj₂ (Total′-bounds τ) t')
Total′-bounds {suc N} {suc N'} (σ [→] τ) {s≤s p} {s≤s p'} {clo γ' t₀} =
  (λ f v tv → let (u , R , D , tu) = f v (proj₂ (Total′-bounds σ) tv) in u , R , D , proj₁ (Total′-bounds τ) tu) ,
  (λ f v tv → let (u , R , D , tu) = f v (proj₁ (Total′-bounds σ) tv) in u , R , D , proj₂ (Total′-bounds τ) tu)
Total′-bounds (μ τ) {v = roll v} = Total′-bounds (τ [ μ τ ])

Total-at-bound : ∀ {N N'} τ {p : arr-depth τ ≤ N} {p' : arr-depth τ ≤ N'} {v : Val τ} →
                 Total′ N τ p v → Total′ N' τ p' v
Total-at-bound τ = proj₁ (Total′-bounds τ)

Total-cast : ∀ {σ σ' : type 0} (e : σ ≡ σ') {N} {p : arr-depth σ ≤ N} {v : Val σ} →
             Total′ N σ p v → Total′ N σ' (≡-subst (λ τ → arr-depth τ ≤ N) e p) (≡-subst Val e v)
Total-cast refl t = t

lookup-total : ∀ {Γ τ} (x : Γ ∋ τ) {γ : Env Γ} → TotalEnv Γ γ → Total τ (lookup x γ)
lookup-total zero     {γ · v} (tγ , tv) = tv
lookup-total (succ x) {γ · v} (tγ , tv) = lookup-total x tγ

bool-total : ∀ (b : _) → Total (unit [+] unit) (bool→val b)
bool-total (inj₁ _) = tt
bool-total (inj₂ _) = tt

ArrTot : (σ τ : type 0) {Γ' : ctxt} (γ' : Env Γ') (t : (Γ' ▸ σ) ⊢ τ) → Set ℓT
ArrTot σ τ {Γ'} γ' t =
  ∀ (v : Val σ) → Total σ v →
  Σ (Val τ) λ u → Σ (𝔽 (suc (width-env γ' + width v)) ⇒ 𝔽 (width u)) λ R →
  ((γ' · v) , t ⇓ u [ R ]) × Total τ u

arr-in : ∀ {σ τ Γ'} {γ' : Env Γ'} {t : (Γ' ▸ σ) ⊢ τ} → ArrTot σ τ γ' t → Total (σ [→] τ) (clo γ' t)
arr-in {σ} {τ} f v tv =
  let (u , R , D , tu) = f v (Total-at-bound σ tv) in u , R , D , Total-at-bound τ tu

arr-out : ∀ {σ τ Γ'} {γ' : Env Γ'} {t : (Γ' ▸ σ) ⊢ τ} → Total (σ [→] τ) (clo γ' t) → ArrTot σ τ γ' t
arr-out {σ} {τ} f v tv =
  let (u , R , D , tu) = f v (Total-at-bound σ tv) in u , R , D , Total-at-bound τ tu

map-total : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : (Γ ▸ (τ₀ [ σr ])) ⊢ σr} →
            ArrTot (τ₀ [ σr ]) σr γ s →
            ∀ (σ' : type 1) {N} {p : arr-depth (σ' [ μ τ₀ ]) ≤ N} {v : Val (σ' [ μ τ₀ ])} →
            Acc _<_ (vsize v) → Total′ N (σ' [ μ τ₀ ]) p v →
            Σ (Val (σ' [ σr ])) λ v' →
            Σ (𝔽 (suc (width-env γ) + width v) ⇒ 𝔽 (width v')) λ F →
            Map γ s σ' v v' F × Total (σ' [ σr ]) v'
map-total {τ₀ = τ₀} f (var Fin.zero) {v = roll w} (acc ra) t =
  let (w' , F , Dm , tw') = map-total f τ₀ (ra (n<1+n _)) t
      (u , S , Ds , tu) = f w' tw'
  in u , _ , m-rec Dm Ds , tu
map-total f unit {v = v} av t = v , _ , m-unit , tt
map-total f (base b) {v = v} av t = v , _ , m-base , tt
map-total f (σ₁ [→] σ₂) {p = p} {v = v} av t = v , _ , m-arrow , Total-at-bound (σ₁ [→] σ₂) {p = p} {p' = ≤-refl} t
map-total {σr = σr} f (σ₁ [+] σ₂) {v = inl v} (acc ra) t =
  let (v' , F , Dm , tv') = map-total f σ₁ (ra (n<1+n _)) t
  in inl v' , _ , m-inl Dm , Total-at-bound (σ₁ [ σr ]) tv'
map-total {σr = σr} f (σ₁ [+] σ₂) {v = inr v} (acc ra) t =
  let (v' , F , Dm , tv') = map-total f σ₂ (ra (n<1+n _)) t
  in inr v' , _ , m-inr Dm , Total-at-bound (σ₂ [ σr ]) tv'
map-total {σr = σr} f (σ₁ [×] σ₂) {v = pair v₁ v₂} (acc ra) (t₁ , t₂) =
  let (v₁' , F , D₁ , t₁') = map-total f σ₁ (ra (s≤s (m≤m+n (vsize v₁) (vsize v₂)))) t₁
      (v₂' , G , D₂ , t₂') = map-total f σ₂ (ra (s≤s (m≤n+m (vsize v₂) (vsize v₁)))) t₂
  in pair v₁' v₂' , _ , m-pair D₁ D₂ , (Total-at-bound (σ₁ [ σr ]) t₁' , Total-at-bound (σ₂ [ σr ]) t₂')
map-total {γ = γ} {τ₀ = τ₀} {σr = σr} {s = s} f (μ τ') {v = roll w} (acc ra) t =
  ≡-subst (λ (x : Val (B [ μ B ])) →
             Σ (Val ((μ τ') [ σr ])) λ v' → Σ (𝔽 (suc (width-env γ) + width (roll {τ = B} x)) ⇒ 𝔽 (width v')) λ F →
             Map γ s (μ τ') (roll {τ = B} x) v' F × Total ((μ τ') [ σr ]) v')
    (subst-subst-sym {P = Val} E {w})
    (let (w' , F , Dm , tw') =
           map-total {τ₀ = τ₀} {σr = σr} f (unfold₁ τ')
             (ra (≡-subst (λ n → n < suc (vsize w)) (sym (vsize-subst (sym E) w)) (n<1+n _)))
             (Total-cast (sym E) t)
     in roll (≡-subst Val (unfold₁-inst τ' σr) w') , _ , m-mu Dm ,
        Total-at-bound ((τ' [ σr ]₁) [ μ (τ' [ σr ]₁) ]) (Total-cast (unfold₁-inst τ' σr) tw'))
  where
  B = τ' [ μ τ₀ ]₁
  E = unfold₁-inst τ' (μ τ₀)

Eval : ∀ {Γ} (γ : Env Γ) {τ} (t : Γ ⊢ τ) → Set ℓT
Eval γ {τ} t = Σ (Val τ) λ v → Σ (𝔽 (suc (width-env γ)) ⇒ 𝔽 (width v)) λ R → (γ , t ⇓ v [ R ]) × Total τ v

fundamental : ∀ {Γ τ} (t : Γ ⊢ τ) (γ : Env Γ) → TotalEnv Γ γ → Eval γ t
fundamental-s : ∀ {Γ is} (Ms : Every (λ s₁ → Γ ⊢ base s₁) is) (γ : Env Γ) → TotalEnv Γ γ → Derivations γ Ms

fundamental (var x) γ tγ = lookup x γ , _ , ⇓-var x , lookup-total x tγ
fundamental unit γ tγ = unit , _ , ⇓-unit , tt
fundamental (inl {τ₁ = τ₁} t) γ tγ =
  let (v , R , D , tv) = fundamental t γ tγ
  in inl v , _ , ⇓-inl D , Total-at-bound τ₁ tv
fundamental (inr {τ₂ = τ₂} t) γ tγ =
  let (v , R , D , tv) = fundamental t γ tγ
  in inr v , _ , ⇓-inr D , Total-at-bound τ₂ tv
fundamental (case {τ₁ = τ₁} {τ₂ = τ₂} s t₁ t₂) γ tγ with fundamental s γ tγ
... | inl v , R , D , ts =
  let (u , S , D₁ , tu) = fundamental t₁ (γ · v) (tγ , Total-at-bound τ₁ ts)
  in u , _ , ⇓-case-l D D₁ , tu
... | inr v , R , D , ts =
  let (u , S , D₂ , tu) = fundamental t₂ (γ · v) (tγ , Total-at-bound τ₂ ts)
  in u , _ , ⇓-case-r D D₂ , tu
fundamental (pair {τ₁ = τ₁} {τ₂ = τ₂} s t) γ tγ =
  let (v , R , D , tv) = fundamental s γ tγ
      (u , S , D' , tu) = fundamental t γ tγ
  in pair v u , _ , ⇓-pair D D' , (Total-at-bound τ₁ tv , Total-at-bound τ₂ tu)
fundamental (fst {τ₁ = τ₁} t) γ tγ with fundamental t γ tγ
... | pair v u , R , D , tv = v , _ , ⇓-fst D , Total-at-bound τ₁ (proj₁ tv)
fundamental (snd {τ₂ = τ₂} t) γ tγ with fundamental t γ tγ
... | pair v u , R , D , tv = u , _ , ⇓-snd D , Total-at-bound τ₂ (proj₂ tv)
fundamental (lam t) γ tγ = clo γ t , _ , ⇓-lam , arr-in (λ v tv → fundamental t (γ · v) (tγ , tv))
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
  in roll v , _ , ⇓-roll D , Total-at-bound (τ₀ [ μ τ₀ ]) tv
fundamental (fold s t) γ tγ =
  let (v , R , D , tv) = fundamental t γ tγ
      (u , R' , Dm , tu) =
        map-total (λ w' tw' → fundamental s (γ · w') (tγ , tw'))
                  (var Fin.zero) (<-wellFounded (vsize v)) tv
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
val-total (inl {τ₁ = τ₁} v) = Total-at-bound τ₁ (val-total v)
val-total (inr {τ₂ = τ₂} v) = Total-at-bound τ₂ (val-total v)
val-total (pair {τ₁ = τ₁} {τ₂ = τ₂} v u) = Total-at-bound τ₁ (val-total v) , Total-at-bound τ₂ (val-total u)
val-total (clo γ t) = arr-in (λ v tv → fundamental t (γ · v) (env-total γ , tv))
val-total (roll {τ = τ₀} v) = Total-at-bound (τ₀ [ μ τ₀ ]) (val-total v)

env-total emp = tt
env-total (γ · v) = env-total γ , val-total v

eval : ∀ {Γ τ} (t : Γ ⊢ τ) (γ : Env Γ) → Derivation γ t
eval t γ = let (v , R , D , _) = fundamental t γ (env-total γ) in v , R , D
