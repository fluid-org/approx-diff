{-# OPTIONS --prop --postfix-projections --safe #-}

-- Values as indices of their types' interpretations, and the value of an index at a first-order type,
-- read off the tree under a substitution of closed types for the type variables and a matching sort
-- environment, extended at a nested μ-type by its own unfolding and sort.
open import Level using (0ℓ; lift)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Fin using (Fin; zero; suc; splitAt; _↑ˡ_)
open import Data.Fin.Properties using (splitAt⁻¹-↑ˡ)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import signature using (Signature)
open import signature.interpretation using (Interpretation)
open import polynomial-functor using (Poly; extend)
import ho-model

module value-interpretation
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A) (ctrl-weight : Setoid.Carrier A)
  (Sig : Signature 0ℓ) (ℐ : Interpretation S Sig)
  where

open Interpretation ℐ using (sort-index)
open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.type-substitution Sig using (sub-id; unfold-sub)
open import language-operational.evaluation Sig S ℐ ctrl-weight
  using (Val; Env; unit; const; inl; inr; pair; clo; roll; emp; _·_)

module model = ho-model S ctrl-weight
module interp = model.interp Sig ℐ
open interp using (∅𝒞; fo-as-poly; 𝒞⟦_⟧ty; 𝒟⟦_⟧ty; 𝒟⟦_⟧ctxt; 𝒟⟦_⟧tm; 𝒟roll-mor)
open prop-setoid._⇒_ using (func)
open model.Fam⟨𝒞⟩μ using (idx; ∣_∣; Sort; mkSort)
open Setoid using (Carrier)

private
  module T = model.Fam⟨𝒞⟩μ.Tree ∅𝒞

open T using (⟦_⟧shape; El; sup)

SortEnv : ℕ → Set₁
SortEnv n = Fin n → Fin 0 ⊎ Sort 0

η∅ : SortEnv 0
η∅ i = inj₁ i

private
  Var : ∀ {n} → (Fin n ⊎ Fin 0) → Poly model.Fam⟨𝒞⟩μ.cat n
  Var s = [ Poly.var , (λ j → Poly.const (∅𝒞 j)) ] s

data Binders : ∀ {n} → TySub (n + 0) 0 → SortEnv n → Set₁ where
  emp  : Binders var η∅
  bind : ∀ {n} {σ : TySub (n + 0) 0} {η : SortEnv n} {τ : type (suc n + 0)} (fo : first-order τ) →
         Binders σ η →
         Binders (extend σ (μ (sub (sub-lift σ) τ))) (extend η (inj₂ (mkSort ∣ fo-as-poly fo ∅𝒞 ∣ η)))

val-idx : ∀ {τ : type 0} → Val τ → Carrier (𝒟⟦ τ ⟧ty (λ ()) .model.Fam⟨𝒟⟩μ.idx)
env-idx : ∀ {Γ} → Env Γ → Carrier (𝒟⟦ Γ ⟧ctxt .model.Fam⟨𝒟⟩μ.idx)

val-idx unit             = lift tt
val-idx (const c)        = c
val-idx (inl v)          = inj₁ (val-idx v)
val-idx (inr v)          = inj₂ (val-idx v)
val-idx (pair v u)       = val-idx v , val-idx u
val-idx (clo γ t)        = 𝒟⟦ lam t ⟧tm .model.Fam⟨𝒟⟩μ.idxf .func (env-idx γ)
val-idx (roll {τ = τ} v) = 𝒟roll-mor τ .model.Fam⟨𝒟⟩μ.idxf .func (val-idx v)

env-idx emp     = lift tt
env-idx (γ · v) = env-idx γ , val-idx v

-- The value's type is given up to a propositional equality with the substituted type, so that the
-- payload of a rolled value is read without being transported along unfold-sub.
mutual
  val-shape : ∀ {n} {τ : type (n + 0)} (fo : first-order τ) (σ : TySub (n + 0) 0) (η : SortEnv n) →
              Binders σ η → ∀ {υ} → υ ≡ sub σ τ → ⟦ ∣ fo-as-poly fo ∅𝒞 ∣ ⟧shape η → Val υ
  val-shape {n} (var i) σ η r e x = val-var i σ η r (splitAt n i) refl e x
  val-shape unit σ η r refl x = unit
  val-shape (base s) σ η r refl x = const x
  val-shape (fo₁ [+] fo₂) σ η r refl (inj₁ x) = inl (val-shape fo₁ σ η r refl x)
  val-shape (fo₁ [+] fo₂) σ η r refl (inj₂ y) = inr (val-shape fo₂ σ η r refl y)
  val-shape (fo₁ [×] fo₂) σ η r refl (x , y) = pair (val-shape fo₁ σ η r refl x) (val-shape fo₂ σ η r refl y)
  val-shape (μ {τ = τ} fo) σ η r refl (sup x) =
    roll (val-shape fo (extend σ (μ (sub (sub-lift σ) τ))) (extend η (inj₂ (mkSort ∣ fo-as-poly fo ∅𝒞 ∣ η)))
            (bind fo r) (unfold-sub σ τ) x)

  val-var : ∀ {n} (i : Fin (n + 0)) (σ : TySub (n + 0) 0) (η : SortEnv n) → Binders σ η →
            (s : Fin n ⊎ Fin 0) → splitAt n i ≡ s → ∀ {υ} → υ ≡ σ i → ⟦ ∣ Var s ∣ ⟧shape η → Val υ
  val-var i σ η r (inj₁ j) eq e x = val-el r j (trans e (sym (cong σ (splitAt⁻¹-↑ˡ eq)))) x
  val-var i σ η r (inj₂ ()) eq e x

  val-el : ∀ {n} {σ : TySub (n + 0) 0} {η : SortEnv n} → Binders σ η → (j : Fin n) →
           ∀ {υ} → υ ≡ σ (j ↑ˡ 0) → El (η j) → Val υ
  val-el (bind {σ = σ} {η = η} fo r) zero    e t = val-shape (μ fo) σ η r e t
  val-el (bind fo r)                 (suc j) e x = val-el r j e x

idx-val : ∀ {τ : type 0} (fo : first-order τ) → Carrier (𝒞⟦ fo ⟧ty ∅𝒞 .idx) → Val τ
idx-val unit i = unit
idx-val (base s) c = const c
idx-val (fo₁ [+] fo₂) (inj₁ i) = inl (idx-val fo₁ i)
idx-val (fo₁ [+] fo₂) (inj₂ j) = inr (idx-val fo₂ j)
idx-val (fo₁ [×] fo₂) (i , j) = pair (idx-val fo₁ i) (idx-val fo₂ j)
idx-val (μ {τ = τ} fo) t = val-shape (μ fo) var η∅ emp (sym (sub-id (μ τ))) t


