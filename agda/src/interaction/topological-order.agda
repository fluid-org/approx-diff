{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; map; filterᵇ; foldl)
import Data.List.Relation.Binary.Permutation.Propositional as ↭
open ↭ using (_↭_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Fin using (Fin)
import Data.Fin as F
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; m≤m+n; +-monoʳ-<; +-suc; <-trans; <-irrefl; <-asym)
open import every using (Every; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; cong to ≡-cong; cong₂ to ≡-cong₂)
open import signature using (Signature)
open import primitives using (Primitives)
import Data.Bool as Bool
import interaction.hide-algebra
import matrix
import two

-- Every edge of a rule-built graph runs strictly forward in completion rank, so the graphs the
-- rules produce are acyclic.
module interaction.topological-order {ℓ} (Sig : Signature ℓ) (𝒫 : Primitives two.semiring Sig) where

open Signature Sig
open Primitives 𝒫
open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.type-substitution Sig using (unfold₁)
open import language-operational.evaluation Sig 𝒫
open import interaction.path Sig 𝒫
open import interaction.graph Sig 𝒫
open import interaction.hide Sig 𝒫

private
  module M = matrix.Mat two.semiring

open import categories using (Category)
open Category M.cat using (_⇒_; _∘_)

-- Vertex rank: env below every path, each path above its premise offsets.
rank-v : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} → Vertex D → ℕ
rank-v env    = zero
rank-v (at p) = suc (rank p)

rank-v-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
           {D : γ , Ms ⇓s vs [ R ]} → VertexS D → ℕ
rank-v-s env    = zero
rank-v-s (at p) = suc (rank-s p)

rank-v-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
           {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
           {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
           {D : Map γ s σ' v R v' R'} → VertexM D → ℕ
rank-v-m env    = zero
rank-v-m input  = zero
rank-v-m (at p) = suc (rank-m p)

private
  src< : ∀ {n} → zero < suc n
  src< = s≤s z≤n

  under : ∀ {m n} → suc m < suc n → m < n
  under (s≤s h) = h

  emb : ∀ k {m n} → suc m < suc n → suc (k + m) < suc (k + n)
  emb k h = s≤s (+-monoʳ-< k (under h))

  root₁ : ∀ a b → suc a < suc (suc a + b)
  root₁ a b = s≤s (m≤m+n (suc a) b)

  root₂ : ∀ a b → suc (a + b) < suc (a + suc b)
  root₂ a b = s≤s (≤-reflexive (≡-sym (+-suc a b)))

  root₀ : ∀ a → suc a < suc (suc a)
  root₀ a = ≤-refl

  root₁₃ : ∀ a b c → suc a < suc ((suc a + b) + c)
  root₁₃ a b c = s≤s (≤-trans (m≤m+n (suc a) b) (m≤m+n (suc a + b) c))

  root₂₃ : ∀ a b c → suc (a + b) < suc ((a + suc b) + c)
  root₂₃ a b c = s≤s (≤-trans (≤-reflexive (≡-sym (+-suc a b))) (m≤m+n (a + suc b) c))

-- A non-zero value of a root-edge family locates the premise root.
private
  edge-ε : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} {m}
           {S : M.Matrix m (width v)} (p : Path D) (i : Fin m) (j : Fin (width-at p)) →
           edge S p i j ≡ two.I → p ≡ ε
  edge-ε ε i j h = ≡-refl
  edge-ε (inl p) i j ()
  edge-ε (inr p) i j ()
  edge-ε (case-l₁ p) i j ()
  edge-ε (case-l₂ p) i j ()
  edge-ε (case-r₁ p) i j ()
  edge-ε (case-r₂ p) i j ()
  edge-ε (pair₁ p) i j ()
  edge-ε (pair₂ p) i j ()
  edge-ε (fst p) i j ()
  edge-ε (snd p) i j ()
  edge-ε (app₁ p) i j ()
  edge-ε (app₂ p) i j ()
  edge-ε (app₃ p) i j ()
  edge-ε (bop p) i j ()
  edge-ε (brel p) i j ()
  edge-ε (roll p) i j ()
  edge-ε (fold₁ p) i j ()
  edge-ε (fold₂ p) i j ()

  edge-ε-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
             {D : γ , Ms ⇓s vs [ R ]} {m}
             {S : M.Matrix m (bases-width is)} (p : PathS D) (i : Fin m) (j : Fin (width-at-s p)) →
             edge-s S p i j ≡ two.I → p ≡ ε
  edge-ε-s ε i j h = ≡-refl
  edge-ε-s (hd p) i j ()
  edge-ε-s (tl p) i j ()

  edge-ε-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
             {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
             {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
             {D : Map γ s σ' v R v' R'} {m}
             {S : M.Matrix m (width v')} (p : PathM D) (i : Fin m) (j : Fin (width-at-m p)) →
             edge-m S p i j ≡ two.I → p ≡ ε
  edge-ε-m ε i j h = ≡-refl
  edge-ε-m (m-rec₁ p) i j ()
  edge-ε-m (m-rec₂ p) i j ()
  edge-ε-m (m-inl p) i j ()
  edge-ε-m (m-inr p) i j ()
  edge-ε-m (m-pair₁ p) i j ()
  edge-ε-m (m-pair₂ p) i j ()
  edge-ε-m (m-mu p) i j ()

-- Every edge runs strictly forward in rank.
mutual
  forward : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ])
            (x y : Vertex D) (i : Fin (vertex-width y)) (j : Fin (vertex-width x)) →
            graph D x y i j ≡ two.I → rank-v x < rank-v y
  forward (⇓-var x) env env i j ()
  forward (⇓-var x) env (at ε) i j _ = src<
  forward (⇓-var x) (at ε) env i j ()
  forward (⇓-var x) (at ε) (at ε) i j ()

  forward ⇓-unit env env i j ()
  forward ⇓-unit env (at ε) i j ()
  forward ⇓-unit (at ε) env i j ()
  forward ⇓-unit (at ε) (at ε) i j ()

  forward ⇓-lam env env i j ()
  forward ⇓-lam env (at ε) i j _ = src<
  forward ⇓-lam (at ε) env i j ()
  forward ⇓-lam (at ε) (at ε) i j ()

  forward (⇓-inl D) env env i j ()
  forward (⇓-inl D) env (at ε) i j ()
  forward (⇓-inl D) env (at (inl q)) i j _ = src<
  forward (⇓-inl D) (at ε) env i j ()
  forward (⇓-inl D) (at ε) (at ε) i j ()
  forward (⇓-inl D) (at ε) (at (inl q)) i j ()
  forward (⇓-inl D) (at (inl p)) env i j ()
  forward (⇓-inl D) (at (inl p)) (at ε) i j h with edge-ε p i j h
  forward (⇓-inl D) (at (inl p)) (at ε) i j h | ≡-refl = root₀ (psize D)
  forward (⇓-inl D) (at (inl p)) (at (inl q)) i j h = forward D (at p) (at q) i j h

  forward (⇓-inr D) env env i j ()
  forward (⇓-inr D) env (at ε) i j ()
  forward (⇓-inr D) env (at (inr q)) i j _ = src<
  forward (⇓-inr D) (at ε) env i j ()
  forward (⇓-inr D) (at ε) (at ε) i j ()
  forward (⇓-inr D) (at ε) (at (inr q)) i j ()
  forward (⇓-inr D) (at (inr p)) env i j ()
  forward (⇓-inr D) (at (inr p)) (at ε) i j h with edge-ε p i j h
  forward (⇓-inr D) (at (inr p)) (at ε) i j h | ≡-refl = root₀ (psize D)
  forward (⇓-inr D) (at (inr p)) (at (inr q)) i j h = forward D (at p) (at q) i j h

  forward (⇓-fst D) env env i j ()
  forward (⇓-fst D) env (at ε) i j ()
  forward (⇓-fst D) env (at (fst q)) i j _ = src<
  forward (⇓-fst D) (at ε) env i j ()
  forward (⇓-fst D) (at ε) (at ε) i j ()
  forward (⇓-fst D) (at ε) (at (fst q)) i j ()
  forward (⇓-fst D) (at (fst p)) env i j ()
  forward (⇓-fst D) (at (fst p)) (at ε) i j h with edge-ε p i j h
  forward (⇓-fst D) (at (fst p)) (at ε) i j h | ≡-refl = root₀ (psize D)
  forward (⇓-fst D) (at (fst p)) (at (fst q)) i j h = forward D (at p) (at q) i j h

  forward (⇓-snd D) env env i j ()
  forward (⇓-snd D) env (at ε) i j ()
  forward (⇓-snd D) env (at (snd q)) i j _ = src<
  forward (⇓-snd D) (at ε) env i j ()
  forward (⇓-snd D) (at ε) (at ε) i j ()
  forward (⇓-snd D) (at ε) (at (snd q)) i j ()
  forward (⇓-snd D) (at (snd p)) env i j ()
  forward (⇓-snd D) (at (snd p)) (at ε) i j h with edge-ε p i j h
  forward (⇓-snd D) (at (snd p)) (at ε) i j h | ≡-refl = root₀ (psize D)
  forward (⇓-snd D) (at (snd p)) (at (snd q)) i j h = forward D (at p) (at q) i j h

  forward (⇓-roll D) env env i j ()
  forward (⇓-roll D) env (at ε) i j ()
  forward (⇓-roll D) env (at (roll q)) i j _ = src<
  forward (⇓-roll D) (at ε) env i j ()
  forward (⇓-roll D) (at ε) (at ε) i j ()
  forward (⇓-roll D) (at ε) (at (roll q)) i j ()
  forward (⇓-roll D) (at (roll p)) env i j ()
  forward (⇓-roll D) (at (roll p)) (at ε) i j h with edge-ε p i j h
  forward (⇓-roll D) (at (roll p)) (at ε) i j h | ≡-refl = root₀ (psize D)
  forward (⇓-roll D) (at (roll p)) (at (roll q)) i j h = forward D (at p) (at q) i j h

  forward (⇓-case-l D₁ D₂) env env i j ()
  forward (⇓-case-l D₁ D₂) env (at ε) i j ()
  forward (⇓-case-l D₁ D₂) env (at (case-l₁ q)) i j _ = src<
  forward (⇓-case-l D₁ D₂) env (at (case-l₂ q)) i j _ = src<
  forward (⇓-case-l D₁ D₂) (at ε) env i j ()
  forward (⇓-case-l D₁ D₂) (at ε) (at ε) i j ()
  forward (⇓-case-l D₁ D₂) (at ε) (at (case-l₁ q)) i j ()
  forward (⇓-case-l D₁ D₂) (at ε) (at (case-l₂ q)) i j ()
  forward (⇓-case-l D₁ D₂) (at (case-l₁ p)) env i j ()
  forward (⇓-case-l D₁ D₂) (at (case-l₁ p)) (at ε) i j ()
  forward (⇓-case-l D₁ D₂) (at (case-l₁ p)) (at (case-l₁ q)) i j h = forward D₁ (at p) (at q) i j h
  forward (⇓-case-l D₁ D₂) (at (case-l₁ p)) (at (case-l₂ q)) i j h with edge-ε p i j h
  forward (⇓-case-l D₁ D₂) (at (case-l₁ p)) (at (case-l₂ q)) i j h | ≡-refl = root₁ (psize D₁) (rank q)
  forward (⇓-case-l D₁ D₂) (at (case-l₂ p)) env i j ()
  forward (⇓-case-l D₁ D₂) (at (case-l₂ p)) (at ε) i j h with edge-ε p i j h
  forward (⇓-case-l D₁ D₂) (at (case-l₂ p)) (at ε) i j h | ≡-refl = root₂ (size D₁) (psize D₂)
  forward (⇓-case-l D₁ D₂) (at (case-l₂ p)) (at (case-l₁ q)) i j ()
  forward (⇓-case-l D₁ D₂) (at (case-l₂ p)) (at (case-l₂ q)) i j h =
    emb (size D₁) (forward D₂ (at p) (at q) i j h)

  forward (⇓-case-r D₁ D₂) env env i j ()
  forward (⇓-case-r D₁ D₂) env (at ε) i j ()
  forward (⇓-case-r D₁ D₂) env (at (case-r₁ q)) i j _ = src<
  forward (⇓-case-r D₁ D₂) env (at (case-r₂ q)) i j _ = src<
  forward (⇓-case-r D₁ D₂) (at ε) env i j ()
  forward (⇓-case-r D₁ D₂) (at ε) (at ε) i j ()
  forward (⇓-case-r D₁ D₂) (at ε) (at (case-r₁ q)) i j ()
  forward (⇓-case-r D₁ D₂) (at ε) (at (case-r₂ q)) i j ()
  forward (⇓-case-r D₁ D₂) (at (case-r₁ p)) env i j ()
  forward (⇓-case-r D₁ D₂) (at (case-r₁ p)) (at ε) i j ()
  forward (⇓-case-r D₁ D₂) (at (case-r₁ p)) (at (case-r₁ q)) i j h = forward D₁ (at p) (at q) i j h
  forward (⇓-case-r D₁ D₂) (at (case-r₁ p)) (at (case-r₂ q)) i j h with edge-ε p i j h
  forward (⇓-case-r D₁ D₂) (at (case-r₁ p)) (at (case-r₂ q)) i j h | ≡-refl = root₁ (psize D₁) (rank q)
  forward (⇓-case-r D₁ D₂) (at (case-r₂ p)) env i j ()
  forward (⇓-case-r D₁ D₂) (at (case-r₂ p)) (at ε) i j h with edge-ε p i j h
  forward (⇓-case-r D₁ D₂) (at (case-r₂ p)) (at ε) i j h | ≡-refl = root₂ (size D₁) (psize D₂)
  forward (⇓-case-r D₁ D₂) (at (case-r₂ p)) (at (case-r₁ q)) i j ()
  forward (⇓-case-r D₁ D₂) (at (case-r₂ p)) (at (case-r₂ q)) i j h =
    emb (size D₁) (forward D₂ (at p) (at q) i j h)

  forward (⇓-pair D₁ D₂) env env i j ()
  forward (⇓-pair D₁ D₂) env (at ε) i j ()
  forward (⇓-pair D₁ D₂) env (at (pair₁ q)) i j _ = src<
  forward (⇓-pair D₁ D₂) env (at (pair₂ q)) i j _ = src<
  forward (⇓-pair D₁ D₂) (at ε) env i j ()
  forward (⇓-pair D₁ D₂) (at ε) (at ε) i j ()
  forward (⇓-pair D₁ D₂) (at ε) (at (pair₁ q)) i j ()
  forward (⇓-pair D₁ D₂) (at ε) (at (pair₂ q)) i j ()
  forward (⇓-pair D₁ D₂) (at (pair₁ p)) env i j ()
  forward (⇓-pair D₁ D₂) (at (pair₁ p)) (at ε) i j h with edge-ε p i j h
  forward (⇓-pair D₁ D₂) (at (pair₁ p)) (at ε) i j h | ≡-refl = root₁ (psize D₁) (size D₂)
  forward (⇓-pair D₁ D₂) (at (pair₁ p)) (at (pair₁ q)) i j h = forward D₁ (at p) (at q) i j h
  forward (⇓-pair D₁ D₂) (at (pair₁ p)) (at (pair₂ q)) i j ()
  forward (⇓-pair D₁ D₂) (at (pair₂ p)) env i j ()
  forward (⇓-pair D₁ D₂) (at (pair₂ p)) (at ε) i j h with edge-ε p i j h
  forward (⇓-pair D₁ D₂) (at (pair₂ p)) (at ε) i j h | ≡-refl = root₂ (size D₁) (psize D₂)
  forward (⇓-pair D₁ D₂) (at (pair₂ p)) (at (pair₁ q)) i j ()
  forward (⇓-pair D₁ D₂) (at (pair₂ p)) (at (pair₂ q)) i j h = emb (size D₁) (forward D₂ (at p) (at q) i j h)

  forward (⇓-app D₁ D₂ D₃) env env i j ()
  forward (⇓-app D₁ D₂ D₃) env (at ε) i j ()
  forward (⇓-app D₁ D₂ D₃) env (at (app₁ q)) i j _ = src<
  forward (⇓-app D₁ D₂ D₃) env (at (app₂ q)) i j _ = src<
  forward (⇓-app D₁ D₂ D₃) env (at (app₃ q)) i j ()
  forward (⇓-app D₁ D₂ D₃) (at ε) env i j ()
  forward (⇓-app D₁ D₂ D₃) (at ε) (at ε) i j ()
  forward (⇓-app D₁ D₂ D₃) (at ε) (at (app₁ q)) i j ()
  forward (⇓-app D₁ D₂ D₃) (at ε) (at (app₂ q)) i j ()
  forward (⇓-app D₁ D₂ D₃) (at ε) (at (app₃ q)) i j ()
  forward (⇓-app D₁ D₂ D₃) (at (app₁ p)) env i j ()
  forward (⇓-app D₁ D₂ D₃) (at (app₁ p)) (at ε) i j ()
  forward (⇓-app D₁ D₂ D₃) (at (app₁ p)) (at (app₁ q)) i j h = forward D₁ (at p) (at q) i j h
  forward (⇓-app D₁ D₂ D₃) (at (app₁ p)) (at (app₂ q)) i j ()
  forward (⇓-app D₁ D₂ D₃) (at (app₁ p)) (at (app₃ q)) i j h with edge-ε p i j h
  forward (⇓-app D₁ D₂ D₃) (at (app₁ p)) (at (app₃ q)) i j h | ≡-refl = root₁₃ (psize D₁) (size D₂) (rank q)
  forward (⇓-app D₁ D₂ D₃) (at (app₂ p)) env i j ()
  forward (⇓-app D₁ D₂ D₃) (at (app₂ p)) (at ε) i j ()
  forward (⇓-app D₁ D₂ D₃) (at (app₂ p)) (at (app₁ q)) i j ()
  forward (⇓-app D₁ D₂ D₃) (at (app₂ p)) (at (app₂ q)) i j h = emb (size D₁) (forward D₂ (at p) (at q) i j h)
  forward (⇓-app D₁ D₂ D₃) (at (app₂ p)) (at (app₃ q)) i j h with edge-ε p i j h
  forward (⇓-app D₁ D₂ D₃) (at (app₂ p)) (at (app₃ q)) i j h | ≡-refl = root₂₃ (size D₁) (psize D₂) (rank q)
  forward (⇓-app D₁ D₂ D₃) (at (app₃ p)) env i j ()
  forward (⇓-app D₁ D₂ D₃) (at (app₃ p)) (at ε) i j h with edge-ε p i j h
  forward (⇓-app D₁ D₂ D₃) (at (app₃ p)) (at ε) i j h | ≡-refl = root₂ (size D₁ + size D₂) (psize D₃)
  forward (⇓-app D₁ D₂ D₃) (at (app₃ p)) (at (app₁ q)) i j ()
  forward (⇓-app D₁ D₂ D₃) (at (app₃ p)) (at (app₂ q)) i j ()
  forward (⇓-app D₁ D₂ D₃) (at (app₃ p)) (at (app₃ q)) i j h =
    emb (size D₁ + size D₂) (forward D₃ (at p) (at q) i j h)

  forward (⇓-bop D) env env i j ()
  forward (⇓-bop D) env (at ε) i j ()
  forward (⇓-bop D) env (at (bop q)) i j _ = src<
  forward (⇓-bop D) (at ε) env i j ()
  forward (⇓-bop D) (at ε) (at ε) i j ()
  forward (⇓-bop D) (at ε) (at (bop q)) i j ()
  forward (⇓-bop D) (at (bop p)) env i j ()
  forward (⇓-bop D) (at (bop p)) (at ε) i j h with edge-ε-s p i j h
  forward (⇓-bop D) (at (bop p)) (at ε) i j h | ≡-refl = root₀ (psize-s D)
  forward (⇓-bop D) (at (bop p)) (at (bop q)) i j h = forward-s D (at p) (at q) i j h

  forward (⇓-brel D) env env i j ()
  forward (⇓-brel D) env (at ε) i j ()
  forward (⇓-brel D) env (at (brel q)) i j _ = src<
  forward (⇓-brel D) (at ε) env i j ()
  forward (⇓-brel D) (at ε) (at ε) i j ()
  forward (⇓-brel D) (at ε) (at (brel q)) i j ()
  forward (⇓-brel D) (at (brel p)) env i j ()
  forward (⇓-brel D) (at (brel p)) (at ε) i j h with edge-ε-s p i j h
  forward (⇓-brel D) (at (brel p)) (at ε) i j h | ≡-refl = root₀ (psize-s D)
  forward (⇓-brel D) (at (brel p)) (at (brel q)) i j h = forward-s D (at p) (at q) i j h

  forward (⇓-fold D₁ D₂) env env i j ()
  forward (⇓-fold D₁ D₂) env (at ε) i j ()
  forward (⇓-fold D₁ D₂) env (at (fold₁ q)) i j _ = src<
  forward (⇓-fold D₁ D₂) env (at (fold₂ q)) i j _ = src<
  forward (⇓-fold D₁ D₂) (at ε) env i j ()
  forward (⇓-fold D₁ D₂) (at ε) (at ε) i j ()
  forward (⇓-fold D₁ D₂) (at ε) (at (fold₁ q)) i j ()
  forward (⇓-fold D₁ D₂) (at ε) (at (fold₂ q)) i j ()
  forward (⇓-fold D₁ D₂) (at (fold₁ p)) env i j ()
  forward (⇓-fold D₁ D₂) (at (fold₁ p)) (at ε) i j ()
  forward (⇓-fold D₁ D₂) (at (fold₁ p)) (at (fold₁ q)) i j h = forward D₁ (at p) (at q) i j h
  forward (⇓-fold D₁ D₂) (at (fold₁ p)) (at (fold₂ q)) i j h with edge-ε p i j h
  forward (⇓-fold D₁ D₂) (at (fold₁ p)) (at (fold₂ q)) i j h | ≡-refl = root₁ (psize D₁) (rank-m q)
  forward (⇓-fold D₁ D₂) (at (fold₂ p)) env i j ()
  forward (⇓-fold D₁ D₂) (at (fold₂ p)) (at ε) i j h with edge-ε-m p i j h
  forward (⇓-fold D₁ D₂) (at (fold₂ p)) (at ε) i j h | ≡-refl = root₂ (size D₁) (psize-m D₂)
  forward (⇓-fold D₁ D₂) (at (fold₂ p)) (at (fold₁ q)) i j ()
  forward (⇓-fold D₁ D₂) (at (fold₂ p)) (at (fold₂ q)) i j h =
    emb (size D₁) (forward-m D₂ (at p) (at q) i j h)

  forward-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
              (D : γ , Ms ⇓s vs [ R ]) (x y : VertexS D)
              (i : Fin (vertex-width-s y)) (j : Fin (vertex-width-s x)) →
              graph-s D x y i j ≡ two.I → rank-v-s x < rank-v-s y
  forward-s [] env env i j ()
  forward-s [] env (at ε) i j ()
  forward-s [] (at ε) env i j ()
  forward-s [] (at ε) (at ε) i j ()

  forward-s (D₁ ∷ D₂) env env i j ()
  forward-s (D₁ ∷ D₂) env (at ε) i j ()
  forward-s (D₁ ∷ D₂) env (at (hd q)) i j _ = src<
  forward-s (D₁ ∷ D₂) env (at (tl q)) i j _ = src<
  forward-s (D₁ ∷ D₂) (at ε) env i j ()
  forward-s (D₁ ∷ D₂) (at ε) (at ε) i j ()
  forward-s (D₁ ∷ D₂) (at ε) (at (hd q)) i j ()
  forward-s (D₁ ∷ D₂) (at ε) (at (tl q)) i j ()
  forward-s (D₁ ∷ D₂) (at (hd p)) env i j ()
  forward-s (D₁ ∷ D₂) (at (hd p)) (at ε) i j h with edge-ε p i j h
  forward-s (D₁ ∷ D₂) (at (hd p)) (at ε) i j h | ≡-refl = root₁ (psize D₁) (size-s D₂)
  forward-s (D₁ ∷ D₂) (at (hd p)) (at (hd q)) i j h = forward D₁ (at p) (at q) i j h
  forward-s (D₁ ∷ D₂) (at (hd p)) (at (tl q)) i j ()
  forward-s (D₁ ∷ D₂) (at (tl p)) env i j ()
  forward-s (D₁ ∷ D₂) (at (tl p)) (at ε) i j h with edge-ε-s p i j h
  forward-s (D₁ ∷ D₂) (at (tl p)) (at ε) i j h | ≡-refl = root₂ (size D₁) (psize-s D₂)
  forward-s (D₁ ∷ D₂) (at (tl p)) (at (hd q)) i j ()
  forward-s (D₁ ∷ D₂) (at (tl p)) (at (tl q)) i j h = emb (size D₁) (forward-s D₂ (at p) (at q) i j h)

  forward-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
              {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
              {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
              (D : Map γ s σ' v R v' R') (x y : VertexM D)
              (i : Fin (vertex-width-m y)) (j : Fin (vertex-width-m x)) →
              graph-m D x y i j ≡ two.I → rank-v-m x < rank-v-m y
  forward-m (m-rec D₁ D₂) env env i j ()
  forward-m (m-rec D₁ D₂) env input i j ()
  forward-m (m-rec D₁ D₂) env (at ε) i j ()
  forward-m (m-rec D₁ D₂) env (at (m-rec₁ q)) i j _ = src<
  forward-m (m-rec D₁ D₂) env (at (m-rec₂ q)) i j _ = src<
  forward-m (m-rec D₁ D₂) input env i j ()
  forward-m (m-rec D₁ D₂) input input i j ()
  forward-m (m-rec D₁ D₂) input (at ε) i j ()
  forward-m (m-rec D₁ D₂) input (at (m-rec₁ q)) i j _ = src<
  forward-m (m-rec D₁ D₂) input (at (m-rec₂ q)) i j ()
  forward-m (m-rec D₁ D₂) (at ε) env i j ()
  forward-m (m-rec D₁ D₂) (at ε) input i j ()
  forward-m (m-rec D₁ D₂) (at ε) (at ε) i j ()
  forward-m (m-rec D₁ D₂) (at ε) (at (m-rec₁ q)) i j ()
  forward-m (m-rec D₁ D₂) (at ε) (at (m-rec₂ q)) i j ()
  forward-m (m-rec D₁ D₂) (at (m-rec₁ p)) env i j ()
  forward-m (m-rec D₁ D₂) (at (m-rec₁ p)) input i j ()
  forward-m (m-rec D₁ D₂) (at (m-rec₁ p)) (at ε) i j ()
  forward-m (m-rec D₁ D₂) (at (m-rec₁ p)) (at (m-rec₁ q)) i j h = forward-m D₁ (at p) (at q) i j h
  forward-m (m-rec D₁ D₂) (at (m-rec₁ p)) (at (m-rec₂ q)) i j h with edge-ε-m p i j h
  forward-m (m-rec D₁ D₂) (at (m-rec₁ p)) (at (m-rec₂ q)) i j h | ≡-refl = root₁ (psize-m D₁) (rank q)
  forward-m (m-rec D₁ D₂) (at (m-rec₂ p)) env i j ()
  forward-m (m-rec D₁ D₂) (at (m-rec₂ p)) input i j ()
  forward-m (m-rec D₁ D₂) (at (m-rec₂ p)) (at ε) i j h with edge-ε p i j h
  forward-m (m-rec D₁ D₂) (at (m-rec₂ p)) (at ε) i j h | ≡-refl = root₂ (size-m D₁) (psize D₂)
  forward-m (m-rec D₁ D₂) (at (m-rec₂ p)) (at (m-rec₁ q)) i j ()
  forward-m (m-rec D₁ D₂) (at (m-rec₂ p)) (at (m-rec₂ q)) i j h =
    emb (size-m D₁) (forward D₂ (at p) (at q) i j h)

  forward-m m-unit env env i j ()
  forward-m m-unit env input i j ()
  forward-m m-unit env (at ε) i j ()
  forward-m m-unit input env i j ()
  forward-m m-unit input input i j ()
  forward-m m-unit input (at ε) i j _ = src<
  forward-m m-unit (at ε) env i j ()
  forward-m m-unit (at ε) input i j ()
  forward-m m-unit (at ε) (at ε) i j ()

  forward-m m-base env env i j ()
  forward-m m-base env input i j ()
  forward-m m-base env (at ε) i j ()
  forward-m m-base input env i j ()
  forward-m m-base input input i j ()
  forward-m m-base input (at ε) i j _ = src<
  forward-m m-base (at ε) env i j ()
  forward-m m-base (at ε) input i j ()
  forward-m m-base (at ε) (at ε) i j ()

  forward-m m-arrow env env i j ()
  forward-m m-arrow env input i j ()
  forward-m m-arrow env (at ε) i j ()
  forward-m m-arrow input env i j ()
  forward-m m-arrow input input i j ()
  forward-m m-arrow input (at ε) i j _ = src<
  forward-m m-arrow (at ε) env i j ()
  forward-m m-arrow (at ε) input i j ()
  forward-m m-arrow (at ε) (at ε) i j ()

  forward-m (m-inl D) env env i j ()
  forward-m (m-inl D) env input i j ()
  forward-m (m-inl D) env (at ε) i j ()
  forward-m (m-inl D) env (at (m-inl q)) i j _ = src<
  forward-m (m-inl D) input env i j ()
  forward-m (m-inl D) input input i j ()
  forward-m (m-inl D) input (at ε) i j _ = src<
  forward-m (m-inl D) input (at (m-inl q)) i j _ = src<
  forward-m (m-inl D) (at ε) env i j ()
  forward-m (m-inl D) (at ε) input i j ()
  forward-m (m-inl D) (at ε) (at ε) i j ()
  forward-m (m-inl D) (at ε) (at (m-inl q)) i j ()
  forward-m (m-inl D) (at (m-inl p)) env i j ()
  forward-m (m-inl D) (at (m-inl p)) input i j ()
  forward-m (m-inl D) (at (m-inl p)) (at ε) i j h with edge-ε-m p i j h
  forward-m (m-inl D) (at (m-inl p)) (at ε) i j h | ≡-refl = root₀ (psize-m D)
  forward-m (m-inl D) (at (m-inl p)) (at (m-inl q)) i j h = forward-m D (at p) (at q) i j h

  forward-m (m-inr D) env env i j ()
  forward-m (m-inr D) env input i j ()
  forward-m (m-inr D) env (at ε) i j ()
  forward-m (m-inr D) env (at (m-inr q)) i j _ = src<
  forward-m (m-inr D) input env i j ()
  forward-m (m-inr D) input input i j ()
  forward-m (m-inr D) input (at ε) i j _ = src<
  forward-m (m-inr D) input (at (m-inr q)) i j _ = src<
  forward-m (m-inr D) (at ε) env i j ()
  forward-m (m-inr D) (at ε) input i j ()
  forward-m (m-inr D) (at ε) (at ε) i j ()
  forward-m (m-inr D) (at ε) (at (m-inr q)) i j ()
  forward-m (m-inr D) (at (m-inr p)) env i j ()
  forward-m (m-inr D) (at (m-inr p)) input i j ()
  forward-m (m-inr D) (at (m-inr p)) (at ε) i j h with edge-ε-m p i j h
  forward-m (m-inr D) (at (m-inr p)) (at ε) i j h | ≡-refl = root₀ (psize-m D)
  forward-m (m-inr D) (at (m-inr p)) (at (m-inr q)) i j h = forward-m D (at p) (at q) i j h

  forward-m (m-mu D) env env i j ()
  forward-m (m-mu D) env input i j ()
  forward-m (m-mu D) env (at ε) i j ()
  forward-m (m-mu D) env (at (m-mu q)) i j _ = src<
  forward-m (m-mu D) input env i j ()
  forward-m (m-mu D) input input i j ()
  forward-m (m-mu D) input (at ε) i j ()
  forward-m (m-mu D) input (at (m-mu q)) i j _ = src<
  forward-m (m-mu D) (at ε) env i j ()
  forward-m (m-mu D) (at ε) input i j ()
  forward-m (m-mu D) (at ε) (at ε) i j ()
  forward-m (m-mu D) (at ε) (at (m-mu q)) i j ()
  forward-m (m-mu D) (at (m-mu p)) env i j ()
  forward-m (m-mu D) (at (m-mu p)) input i j ()
  forward-m (m-mu D) (at (m-mu p)) (at ε) i j h with edge-ε-m p i j h
  forward-m (m-mu D) (at (m-mu p)) (at ε) i j h | ≡-refl = root₀ (psize-m D)
  forward-m (m-mu D) (at (m-mu p)) (at (m-mu q)) i j h = forward-m D (at p) (at q) i j h

  forward-m (m-pair D₁ D₂) env env i j ()
  forward-m (m-pair D₁ D₂) env input i j ()
  forward-m (m-pair D₁ D₂) env (at ε) i j ()
  forward-m (m-pair D₁ D₂) env (at (m-pair₁ q)) i j _ = src<
  forward-m (m-pair D₁ D₂) env (at (m-pair₂ q)) i j _ = src<
  forward-m (m-pair D₁ D₂) input env i j ()
  forward-m (m-pair D₁ D₂) input input i j ()
  forward-m (m-pair D₁ D₂) input (at ε) i j _ = src<
  forward-m (m-pair D₁ D₂) input (at (m-pair₁ q)) i j _ = src<
  forward-m (m-pair D₁ D₂) input (at (m-pair₂ q)) i j _ = src<
  forward-m (m-pair D₁ D₂) (at ε) env i j ()
  forward-m (m-pair D₁ D₂) (at ε) input i j ()
  forward-m (m-pair D₁ D₂) (at ε) (at ε) i j ()
  forward-m (m-pair D₁ D₂) (at ε) (at (m-pair₁ q)) i j ()
  forward-m (m-pair D₁ D₂) (at ε) (at (m-pair₂ q)) i j ()
  forward-m (m-pair D₁ D₂) (at (m-pair₁ p)) env i j ()
  forward-m (m-pair D₁ D₂) (at (m-pair₁ p)) input i j ()
  forward-m (m-pair D₁ D₂) (at (m-pair₁ p)) (at ε) i j h with edge-ε-m p i j h
  forward-m (m-pair D₁ D₂) (at (m-pair₁ p)) (at ε) i j h | ≡-refl = root₁ (psize-m D₁) (size-m D₂)
  forward-m (m-pair D₁ D₂) (at (m-pair₁ p)) (at (m-pair₁ q)) i j h = forward-m D₁ (at p) (at q) i j h
  forward-m (m-pair D₁ D₂) (at (m-pair₁ p)) (at (m-pair₂ q)) i j ()
  forward-m (m-pair D₁ D₂) (at (m-pair₂ p)) env i j ()
  forward-m (m-pair D₁ D₂) (at (m-pair₂ p)) input i j ()
  forward-m (m-pair D₁ D₂) (at (m-pair₂ p)) (at ε) i j h with edge-ε-m p i j h
  forward-m (m-pair D₁ D₂) (at (m-pair₂ p)) (at ε) i j h | ≡-refl = root₂ (size-m D₁) (psize-m D₂)
  forward-m (m-pair D₁ D₂) (at (m-pair₂ p)) (at (m-pair₁ q)) i j ()
  forward-m (m-pair D₁ D₂) (at (m-pair₂ p)) (at (m-pair₂ q)) i j h =
    emb (size-m D₁) (forward-m D₂ (at p) (at q) i j h)


-- A chain of one or more edges between vertices.
data Chain {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} : Vertex D → Vertex D → Set ℓ where
  step : ∀ {x y} (i : Fin (vertex-width y)) (j : Fin (vertex-width x)) →
         graph D x y i j ≡ two.I → Chain x y
  _∷_  : ∀ {x y z} → Chain x y → Chain y z → Chain x z

-- Chains climb strictly in rank, so no chain returns to its start: the graph is acyclic.
climb : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} {x y : Vertex D} →
        Chain x y → rank-v x < rank-v y
climb {D = D} {x} {y} (step i j h) = forward D x y i j h
climb (c ∷ c') = <-trans (climb c) (climb c')

acyclic : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} {x : Vertex D} →
          Chain x x → ⊥
acyclic c = <-irrefl ≡-refl (climb c)

-- Witnesses for non-zero entries of sums and composites.
private
  Σ-I : ∀ {n} (f : Fin n → two.Two) → M.Σ f ≡ two.I → Σ (Fin n) (λ k → f k ≡ two.I)
  Σ-I {suc n} f h with two.⊔-I (f F.zero) (M.Σ (λ k → f (F.suc k))) h
  ... | inj₁ e = F.zero , e
  ... | inj₂ e with Σ-I (λ k → f (F.suc k)) e
  ...   | (k , e') = F.suc k , e'

  ∘-I : ∀ {m n k} (A : M.Matrix m n) (B : M.Matrix n k) i l → (A ∘ B) i l ≡ two.I →
        Σ (Fin n) (λ j → (A i j ≡ two.I) × (B j l ≡ two.I))
  ∘-I A B i l h with Σ-I (λ j → A i j two.⊓ B j l) h
  ... | (j , e) with two.⊓-I (A i j) (B j l) e
  ...   | (e₁ , e₂) = j , (e₁ , e₂)

  Σ-I-at : ∀ {n} (f : Fin n → two.Two) (k : Fin n) → f k ≡ two.I → M.Σ f ≡ two.I
  Σ-I-at f F.zero    h = two.⊔-I-inl h
  Σ-I-at f (F.suc k) h = two.⊔-I-inr (f F.zero) (Σ-I-at (λ i → f (F.suc i)) k h)

  ∘-I-at : ∀ {m n k} (A : M.Matrix m n) (B : M.Matrix n k) i l j →
           A i j ≡ two.I → B j l ≡ two.I → (A ∘ B) i l ≡ two.I
  ∘-I-at A B i l j h₁ h₂ = Σ-I-at (λ j' → A i j' two.⊓ B j' l) j (two.⊓-I-pair h₁ h₂)

-- The forward-edge property of an arbitrary graph over a derivation.
Forward : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} → Graph D → Set ℓ
Forward {D = D} G = ∀ (x y : Vertex D) (i : Fin (vertex-width y)) (j : Fin (vertex-width x)) →
                    G x y i j ≡ two.I → rank-v x < rank-v y

-- Consequences of forwardness for hiding, proved once over an abstract ranked vertex set and
-- instantiated to the three graph families. Hiding preserves the property, since a new edge
-- composes edges through the hidden vertex; hiding two vertices commutes, since an entry of one
-- order decomposes into a term also present in the other order, except the residual routed
-- through an edge in each direction between the two hidden vertices, which forwardness rules
-- out; and hiding a list of vertices is therefore independent of the order, adjacent swaps being
-- commutation pushed through the rest of the fold by congruence.
private
  module Ranked (V : Set ℓ) (w : V → ℕ) (rk : V → ℕ) where
    open interaction.hide-algebra.Hide V w using (Gr; h; _≈g_; fold-cong)

    private
      Fwd : Gr → Set ℓ
      Fwd G = ∀ x y (i : Fin (w y)) (j : Fin (w x)) → G x y i j ≡ two.I → rk x < rk y

    fwd-h : ∀ {G} r → Fwd G → Fwd (h G r)
    fwd-h {G} r fwd x y i j e with two.⊔-I (G x y i j) ((G r y ∘ G x r) i j) e
    ... | inj₁ a = fwd x y i j a
    ... | inj₂ a with ∘-I (G r y) (G x r) i j a
    ...   | (k , (e₁ , e₂)) = <-trans (fwd x r k j e₂) (fwd r y i k e₁)

    fwd-fold : ∀ {G} rs → Fwd G → Fwd (foldl h G rs)
    fwd-fold []       fwd = fwd
    fwd-fold (r ∷ rs) fwd = fwd-fold rs (fwd-h r fwd)

    into : ∀ {G} → Fwd G → ∀ r r' x y (i : Fin (w y)) (j : Fin (w x)) →
           h (h G r) r' x y i j ≡ two.I → h (h G r') r x y i j ≡ two.I
    into {G} fwd r r' x y i j e
      with two.⊔-I (h G r x y i j) ((h G r r' y ∘ h G r x r') i j) e
    into {G} fwd r r' x y i j e | inj₁ a with two.⊔-I (G x y i j) ((G r y ∘ G x r) i j) a
    ... | inj₁ a₁ = two.⊔-I-inl (two.⊔-I-inl a₁)
    ... | inj₂ a₂ with ∘-I (G r y) (G x r) i j a₂
    ...   | (k , (e₁ , e₂)) =
      two.⊔-I-inr (h G r' x y i j)
        (∘-I-at (h G r' r y) (h G r' x r) i j k (two.⊔-I-inl e₁) (two.⊔-I-inl e₂))
    into {G} fwd r r' x y i j e | inj₂ b with ∘-I (h G r r' y) (h G r x r') i j b
    ... | (m , (c , d)) with two.⊔-I (G r' y i m) ((G r y ∘ G r' r) i m) c
                           | two.⊔-I (G x r' m j) ((G r r' ∘ G x r) m j) d
    ...   | inj₁ c₁ | inj₁ d₁ =
      two.⊔-I-inl (two.⊔-I-inr (G x y i j) (∘-I-at (G r' y) (G x r') i j m c₁ d₁))
    ...   | inj₁ c₁ | inj₂ d₂ with ∘-I (G r r') (G x r) m j d₂
    ...     | (k , (d₁' , d₂')) =
      two.⊔-I-inr (h G r' x y i j)
        (∘-I-at (h G r' r y) (h G r' x r) i j k
          (two.⊔-I-inr (G r y i k) (∘-I-at (G r' y) (G r r') i k m c₁ d₁'))
          (two.⊔-I-inl d₂'))
    into {G} fwd r r' x y i j e | inj₂ b | (m , (c , d)) | inj₂ c₂ | inj₁ d₁
      with ∘-I (G r y) (G r' r) i m c₂
    ...     | (k , (c₁' , c₂')) =
      two.⊔-I-inr (h G r' x y i j)
        (∘-I-at (h G r' r y) (h G r' x r) i j k
          (two.⊔-I-inl c₁')
          (two.⊔-I-inr (G x r k j) (∘-I-at (G r' r) (G x r') k j m c₂' d₁)))
    into {G} fwd r r' x y i j e | inj₂ b | (m , (c , d)) | inj₂ c₂ | inj₂ d₂
      with ∘-I (G r y) (G r' r) i m c₂ | ∘-I (G r r') (G x r) m j d₂
    ...     | (k , (_ , c₂')) | (k' , (d₁' , _)) =
      ⊥-elim (<-asym (fwd r' r k m c₂') (fwd r r' m k' d₁'))

    comm : ∀ {G} → Fwd G → ∀ r r' x y (i : Fin (w y)) (j : Fin (w x)) →
           h (h G r) r' x y i j ≡ h (h G r') r x y i j
    comm fwd r r' x y i j = two.I-antisym (into fwd r r' x y i j) (into fwd r' r x y i j)

    perm : ∀ {G rs rs'} → Fwd G → rs ↭ rs' → foldl h G rs ≈g foldl h G rs'
    perm fwd ↭.refl x y i j = ≡-refl
    perm fwd (↭.prep r p) = perm (fwd-h r fwd) p
    perm fwd (↭.swap {xs = rs} a b p) x y i j =
      ≡-trans (fold-cong rs (comm fwd a b) x y i j)
              (perm (fwd-h a (fwd-h b fwd)) p x y i j)
    perm fwd (↭.trans p q) x y i j = ≡-trans (perm fwd p x y i j) (perm fwd q x y i j)

hide-all-forward : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} {G : Graph D}
                   (rs : List (Vertex D)) → Forward G → Forward (hide-all G rs)
hide-all-forward {D = D} = Ranked.fwd-fold (Vertex D) vertex-width rank-v

-- The first-order dependence graph inherits the property.
fo-forward : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) → Forward (fo-graph D)
fo-forward D = hide-all-forward (map at (fo-hidden D)) (forward D)

hide-all-perm : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} {G : Graph D} →
                Forward G → ∀ {rs rs'} → rs ↭ rs' →
                ∀ (x y : Vertex D) i j → hide-all G rs x y i j ≡ hide-all G rs' x y i j
hide-all-perm {D = D} fwd = Ranked.perm (Vertex D) vertex-width rank-v fwd

