{-# OPTIONS --prop --postfix-projections --safe #-}

-- The interpretation of values at first-order types: an index of the type's interpretation on the
-- first-order side of the higher-order model, and of environments over first-order contexts. A value
-- of a μ-type is a tree whose shape is read off the value at the unfolded type; that value is read
-- under a substitution of closed types for the type variables, so a nested μ-type extends the
-- substitution by its own unfolding and the sort environment by its own sort.
open import Level using (0ℓ; lift)
open import Data.Nat using (ℕ; suc; _+_; _<_; s≤s)
open import Data.Nat.Properties using (≤-reflexive; <-trans; n<1+n; m≤m+n; m≤n+m)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Data.Fin using (Fin; zero; suc; splitAt; _↑ˡ_)
open import Data.Fin.Properties using (splitAt⁻¹-↑ˡ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import signature using (Signature)
open import primitives using (Primitives)
open import polynomial-functor using (extend)
import ho-model

module value-interpretation
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A) (elim-weight : Setoid.Carrier A)
  (Sig : Signature 0ℓ) (𝒫 : Primitives S Sig)
  where

open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.type-substitution Sig using (sub-sub; sub-ren; sub-id)
open import language-operational.evaluation Sig S 𝒫 elim-weight
  using (Val; Env; unit; const; inl; inr; pair; roll; emp; _·_; size; size-subst)

module model = ho-model S elim-weight
module interp = model.interp Sig 𝒫
open interp using (∅𝒞; fo-as-poly; 𝒞⟦_⟧ty; 𝒞⟦_⟧ctxt)
open model.Fam⟨𝒞⟩μ using (idx; ∣_∣; Sort; mkSort)
open Setoid using (Carrier)

private
  module T = model.Fam⟨𝒞⟩μ.Tree ∅𝒞

open T using (⟦_⟧shape; El; sup)

-- Instantiating the body of a μ-type, substituted under the binder, at the substituted μ-type is
-- substituting the body with the substitution extended by that μ-type.
unfold-sub : ∀ {n} (σ : TySub n 0) (τ : type (suc n)) →
             sub (sub-lift σ) τ [ μ (sub (sub-lift σ) τ) ] ≡ sub (extend σ (μ (sub (sub-lift σ) τ))) τ
unfold-sub σ τ =
  trans (sub-sub (push (μ B)) (sub-lift σ) τ)
        (sub-cong τ λ { zero → refl ; (suc i) → trans (sub-ren (push (μ B)) suc (σ i)) (sub-id (σ i)) })
  where B = sub (sub-lift σ) τ

-- The values at the substituted variables, as elements of the sort environment, for values below a
-- size bound.
Compat : ∀ {n} → TySub (n + 0) 0 → (Fin n → Fin 0 ⊎ Sort 0) → ℕ → Set
Compat {n} σ η N = ∀ (j : Fin n) (u : Val (σ (j ↑ˡ 0))) → size u < N → El (η j)

extend-compat : ∀ {n} {σ : TySub (n + 0) 0} {η : Fin n → Fin 0 ⊎ Sort 0} {N} {ρ : type 0} {s} →
                ((u : Val ρ) → size u < N → El s) → Compat σ η N → Compat (extend σ ρ) (extend η s) N
extend-compat f₀ f zero    = f₀
extend-compat f₀ f (suc j) = f j

-- A value at a first-order type under a substitution of closed types, as a shape of the type's
-- polynomial over a sort environment, given the values at the substituted variables. The bound lets
-- the body of a μ-type read the values at its own variable, which are smaller, by the same function.
shape-val : ∀ {n} {τ : type (n + 0)} (fo : first-order τ) (σ : TySub (n + 0) 0)
            (η : Fin n → Fin 0 ⊎ Sort 0) (N : ℕ) → Acc _<_ N → Compat σ η N →
            (v : Val (sub σ τ)) → size v < N → ⟦ ∣ fo-as-poly fo ∅𝒞 ∣ ⟧shape η
shape-val {n} (var i) σ η N a f v p with splitAt n i in eq
... | inj₁ j = f j (subst Val (cong σ (sym (splitAt⁻¹-↑ˡ eq))) v) (subst (_< N) (sym (size-subst _ v)) p)
... | inj₂ ()
shape-val unit σ η N a f unit p = lift tt
shape-val (base s) σ η N a f (const c) p = c
shape-val (fo₁ [+] fo₂) σ η N a f (inl v) p = inj₁ (shape-val fo₁ σ η N a f v (<-trans (n<1+n _) p))
shape-val (fo₁ [+] fo₂) σ η N a f (inr v) p = inj₂ (shape-val fo₂ σ η N a f v (<-trans (n<1+n _) p))
shape-val (fo₁ [×] fo₂) σ η N a f (pair v u) p =
  shape-val fo₁ σ η N a f v (<-trans (s≤s (m≤m+n (size v) (size u))) p) ,
  shape-val fo₂ σ η N a f u (<-trans (s≤s (m≤n+m (size u) (size v))) p)
shape-val (μ {τ = τ} fo) σ η N (acc rs) f (roll w) p =
  sup (shape-val fo (extend σ (μ B)) (extend η (inj₂ (mkSort ∣ fo-as-poly fo ∅𝒞 ∣ η)))
         (suc (size w)) (rs p)
         (extend-compat (shape-val (μ fo) σ η (suc (size w)) (rs p) (λ j u q → f j u (<-trans q p)))
                        (λ j u q → f j u (<-trans q p)))
         (subst Val (unfold-sub σ τ) w) (s≤s (≤-reflexive (size-subst (unfold-sub σ τ) w))))
  where B = sub (sub-lift σ) τ

⟦_⟧val : ∀ {τ : type 0} (fo : first-order τ) → Val τ → Carrier (𝒞⟦ fo ⟧ty ∅𝒞 .idx)
⟦ unit ⟧val unit = lift tt
⟦ base s ⟧val (const c) = c
⟦ fo₁ [+] fo₂ ⟧val (inl v) = inj₁ (⟦ fo₁ ⟧val v)
⟦ fo₁ [+] fo₂ ⟧val (inr v) = inj₂ (⟦ fo₂ ⟧val v)
⟦ fo₁ [×] fo₂ ⟧val (pair v u) = ⟦ fo₁ ⟧val v , ⟦ fo₂ ⟧val u
⟦ μ {τ = τ} fo ⟧val v =
  shape-val (μ fo) var (λ i → inj₁ i) (suc (size v')) (<-wellFounded _) (λ ()) v' (n<1+n _)
  where v' = subst Val (sym (sub-id (μ τ))) v

⟦_⟧env : ∀ {Γ} (Γ-fo : first-order-ctxt Γ) → Env Γ → Carrier (𝒞⟦ Γ-fo ⟧ctxt .idx)
⟦ emp ⟧env emp = lift tt
⟦ Γ-fo ▸ fo ⟧env (γ · v) = ⟦ Γ-fo ⟧env γ , ⟦ fo ⟧val v
