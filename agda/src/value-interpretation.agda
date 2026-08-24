{-# OPTIONS --prop --postfix-projections --safe #-}

-- The interpretation of values at first-order types: an index of the type's interpretation on the
-- first-order side of the higher-order model, and of environments over first-order contexts. A value
-- of a μ-type is a tree whose shape is read off the value at the unfolded type; that value is read
-- under a substitution of closed types for the type variables, so a nested μ-type extends the
-- substitution by its own unfolding and the sort environment by its own sort. The value of an index
-- is read off the tree the same way, so the interpretation is injective at first-order types.
open import Level using (0ℓ; lift)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Fin using (Fin; zero; suc; splitAt; _↑ˡ_)
open import Data.Fin.Properties using (splitAt⁻¹-↑ˡ)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
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
  using (Val; Env; unit; const; inl; inr; pair; roll; emp; _·_)

module model = ho-model S ctrl-weight
module interp = model.interp Sig ℐ
open interp using (∅𝒞; fo-as-poly; 𝒞⟦_⟧ty; 𝒞⟦_⟧ctxt)
open model.Fam⟨𝒞⟩μ using (idx; ∣_∣; Sort; mkSort; module Srt)
open Setoid using (Carrier)

private
  module T = model.Fam⟨𝒞⟩μ.Tree ∅𝒞

open T using (⟦_⟧shape; El; W; sup)

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

-- The value's type is given up to a propositional equality with the substituted type, so that the
-- payload of a rolled value is read without being transported along unfold-sub.
mutual
  shape-val : ∀ {n} {τ : type (n + 0)} (fo : first-order τ) (σ : TySub (n + 0) 0) (η : SortEnv n) →
              Binders σ η → ∀ {υ} → υ ≡ sub σ τ → Val υ → ⟦ ∣ fo-as-poly fo ∅𝒞 ∣ ⟧shape η
  shape-val {n} (var i) σ η r e v = shape-var i σ η r (splitAt n i) refl e v
  shape-val unit σ η r refl unit = lift tt
  shape-val (base s) σ η r refl (const c) = c
  shape-val (fo₁ [+] fo₂) σ η r refl (inl v) = inj₁ (shape-val fo₁ σ η r refl v)
  shape-val (fo₁ [+] fo₂) σ η r refl (inr v) = inj₂ (shape-val fo₂ σ η r refl v)
  shape-val (fo₁ [×] fo₂) σ η r refl (pair v u) = shape-val fo₁ σ η r refl v , shape-val fo₂ σ η r refl u
  shape-val (μ {τ = τ} fo) σ η r refl (roll w) =
    sup (shape-val fo (extend σ (μ (sub (sub-lift σ) τ))) (extend η (inj₂ (mkSort ∣ fo-as-poly fo ∅𝒞 ∣ η)))
           (bind fo r) (unfold-sub σ τ) w)

  shape-var : ∀ {n} (i : Fin (n + 0)) (σ : TySub (n + 0) 0) (η : SortEnv n) → Binders σ η →
              (s : Fin n ⊎ Fin 0) → splitAt n i ≡ s → ∀ {υ} → υ ≡ σ i → Val υ → ⟦ ∣ Var s ∣ ⟧shape η
  shape-var i σ η r (inj₁ j) eq e v = read r j (trans e (sym (cong σ (splitAt⁻¹-↑ˡ eq)))) v
  shape-var i σ η r (inj₂ ()) eq e v

  read : ∀ {n} {σ : TySub (n + 0) 0} {η : SortEnv n} → Binders σ η → (j : Fin n) →
         ∀ {υ} → υ ≡ σ (j ↑ˡ 0) → Val υ → El (η j)
  read (bind {σ = σ} {η = η} fo r) zero    e v = shape-val (μ fo) σ η r e v
  read (bind fo r)                 (suc j) e v = read r j e v

⟦_⟧val : ∀ {τ : type 0} (fo : first-order τ) → Val τ → Carrier (𝒞⟦ fo ⟧ty ∅𝒞 .idx)
⟦ unit ⟧val unit = lift tt
⟦ base s ⟧val (const c) = c
⟦ fo₁ [+] fo₂ ⟧val (inl v) = inj₁ (⟦ fo₁ ⟧val v)
⟦ fo₁ [+] fo₂ ⟧val (inr v) = inj₂ (⟦ fo₂ ⟧val v)
⟦ fo₁ [×] fo₂ ⟧val (pair v u) = ⟦ fo₁ ⟧val v , ⟦ fo₂ ⟧val u
⟦ μ {τ = τ} fo ⟧val v = shape-val (μ fo) var η∅ emp (sym (sub-id (μ τ))) v

⟦_⟧env : ∀ {Γ} (Γ-fo : first-order-ctxt Γ) → Env Γ → Carrier (𝒞⟦ Γ-fo ⟧ctxt .idx)
⟦ emp ⟧env emp = lift tt
⟦ Γ-fo ▸ fo ⟧env (γ · v) = ⟦ Γ-fo ⟧env γ , ⟦ fo ⟧val v

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
  val-var i σ η r (inj₁ j) eq e x = read⁻¹ r j (trans e (sym (cong σ (splitAt⁻¹-↑ˡ eq)))) x
  val-var i σ η r (inj₂ ()) eq e x

  read⁻¹ : ∀ {n} {σ : TySub (n + 0) 0} {η : SortEnv n} → Binders σ η → (j : Fin n) →
           ∀ {υ} → υ ≡ σ (j ↑ˡ 0) → El (η j) → Val υ
  read⁻¹ (bind {σ = σ} {η = η} fo r) zero    e t = val-shape (μ fo) σ η r e t
  read⁻¹ (bind fo r)                 (suc j) e x = read⁻¹ r j e x

⟦_⟧val⁻¹ : ∀ {τ : type 0} (fo : first-order τ) → Carrier (𝒞⟦ fo ⟧ty ∅𝒞 .idx) → Val τ
⟦ unit ⟧val⁻¹ i = unit
⟦ base s ⟧val⁻¹ c = const c
⟦ fo₁ [+] fo₂ ⟧val⁻¹ (inj₁ i) = inl (⟦ fo₁ ⟧val⁻¹ i)
⟦ fo₁ [+] fo₂ ⟧val⁻¹ (inj₂ j) = inr (⟦ fo₂ ⟧val⁻¹ j)
⟦ fo₁ [×] fo₂ ⟧val⁻¹ (i , j) = pair (⟦ fo₁ ⟧val⁻¹ i) (⟦ fo₂ ⟧val⁻¹ j)
⟦ μ {τ = τ} fo ⟧val⁻¹ t = val-shape (μ fo) var η∅ emp (sym (sub-id (μ τ))) t

mutual
  val-shape-val : ∀ {n} {τ : type (n + 0)} (fo : first-order τ) (σ : TySub (n + 0) 0) (η : SortEnv n)
                  (r : Binders σ η) {υ} (e : υ ≡ sub σ τ) (v : Val υ) →
                  val-shape fo σ η r e (shape-val fo σ η r e v) ≡ v
  val-shape-val {n} (var i) σ η r e v = val-var-var i σ η r (splitAt n i) refl e v
  val-shape-val unit σ η r refl unit = refl
  val-shape-val (base s) σ η r refl (const c) = refl
  val-shape-val (fo₁ [+] fo₂) σ η r refl (inl v) = cong inl (val-shape-val fo₁ σ η r refl v)
  val-shape-val (fo₁ [+] fo₂) σ η r refl (inr v) = cong inr (val-shape-val fo₂ σ η r refl v)
  val-shape-val (fo₁ [×] fo₂) σ η r refl (pair v u) =
    cong₂ pair (val-shape-val fo₁ σ η r refl v) (val-shape-val fo₂ σ η r refl u)
  val-shape-val (μ {τ = τ} fo) σ η r refl (roll w) =
    cong roll (val-shape-val fo (extend σ (μ (sub (sub-lift σ) τ))) (extend η (inj₂ (mkSort ∣ fo-as-poly fo ∅𝒞 ∣ η)))
                 (bind fo r) (unfold-sub σ τ) w)

  val-var-var : ∀ {n} (i : Fin (n + 0)) (σ : TySub (n + 0) 0) (η : SortEnv n) (r : Binders σ η)
                (s : Fin n ⊎ Fin 0) (eq : splitAt n i ≡ s) {υ} (e : υ ≡ σ i) (v : Val υ) →
                val-var i σ η r s eq e (shape-var i σ η r s eq e v) ≡ v
  val-var-var i σ η r (inj₁ j) eq e v = read⁻¹-read r j (trans e (sym (cong σ (splitAt⁻¹-↑ˡ eq)))) v
  val-var-var i σ η r (inj₂ ()) eq e v

  read⁻¹-read : ∀ {n} {σ : TySub (n + 0) 0} {η : SortEnv n} (r : Binders σ η) (j : Fin n)
                {υ} (e : υ ≡ σ (j ↑ˡ 0)) (v : Val υ) → read⁻¹ r j e (read r j e v) ≡ v
  read⁻¹-read (bind {σ = σ} {η = η} fo r) zero    e v = val-shape-val (μ fo) σ η r e v
  read⁻¹-read (bind fo r)                 (suc j) e v = read⁻¹-read r j e v

⟦⟧val⁻¹-val : ∀ {τ : type 0} (fo : first-order τ) (v : Val τ) → ⟦ fo ⟧val⁻¹ (⟦ fo ⟧val v) ≡ v
⟦⟧val⁻¹-val unit unit = refl
⟦⟧val⁻¹-val (base s) (const c) = refl
⟦⟧val⁻¹-val (fo₁ [+] fo₂) (inl v) = cong inl (⟦⟧val⁻¹-val fo₁ v)
⟦⟧val⁻¹-val (fo₁ [+] fo₂) (inr v) = cong inr (⟦⟧val⁻¹-val fo₂ v)
⟦⟧val⁻¹-val (fo₁ [×] fo₂) (pair v u) = cong₂ pair (⟦⟧val⁻¹-val fo₁ v) (⟦⟧val⁻¹-val fo₂ u)
⟦⟧val⁻¹-val (μ {τ = τ} fo) v = val-shape-val (μ fo) var η∅ emp (sym (sub-id (μ τ))) v
