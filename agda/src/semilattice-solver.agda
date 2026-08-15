{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (_⊔_)
open import prop-setoid using (Setoid)
open import commutative-monoid using (CommutativeMonoid)

-- Equations in an idempotent commutative monoid on a setoid, decided by normalising both sides to
-- the set of variables they mention. An expression over n variables is evaluated at a vector of
-- carriers; solve takes the two expressions and a reflexivity proof that their normal forms agree.
module semilattice-solver where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Vec using (Vec; []; _∷_; lookup; zipWith; replicate)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl)

infixl 21 _⊕_

data Expr (n : ℕ) : Set where
  var : Fin n → Expr n
  nil : Expr n
  _⊕_ : Expr n → Expr n → Expr n

-- Normal forms: which variables occur.
NF : ℕ → Set
NF n = Vec Bool n

single : ∀ {n} → Fin n → NF n
single zero    = true ∷ replicate _ false
single (suc i) = false ∷ single i

norm : ∀ {n} → Expr n → NF n
norm (var i) = single i
norm nil     = replicate _ false
norm (a ⊕ b) = zipWith _∨_ (norm a) (norm b)

module Solver {o e} {A : Setoid o e} (M : CommutativeMonoid A)
  (let open CommutativeMonoid M) (let open Setoid A)
  (+-idem : ∀ {x} → (x + x) ≈ x) where

 Env : ℕ → Set o
 Env n = Vec Carrier n

 ⟦_⟧ : ∀ {n} → Expr n → Env n → Carrier
 ⟦ var i ⟧ ρ = lookup ρ i
 ⟦ nil ⟧   ρ = ε
 ⟦ a ⊕ b ⟧ ρ = ⟦ a ⟧ ρ + ⟦ b ⟧ ρ

 sel : Bool → Carrier → Carrier
 sel true  x = x
 sel false x = ε

 ⟦_⟧nf : ∀ {n} → NF n → Env n → Carrier
 ⟦ [] ⟧nf     []       = ε
 ⟦ b ∷ bs ⟧nf (x ∷ xs) = sel b x + ⟦ bs ⟧nf xs

 private
   +-runit : ∀ {x} → (x + ε) ≈ x
   +-runit = trans +-comm +-lunit

   nf-nil : ∀ {n} (ρ : Env n) → ⟦ replicate _ false ⟧nf ρ ≈ ε
   nf-nil []       = refl
   nf-nil (x ∷ ρ) = trans +-lunit (nf-nil ρ)

   nf-single : ∀ {n} (i : Fin n) (ρ : Env n) → ⟦ single i ⟧nf ρ ≈ lookup ρ i
   nf-single zero    (x ∷ ρ) = trans (+-cong refl (nf-nil ρ)) +-runit
   nf-single (suc i) (x ∷ ρ) = trans +-lunit (nf-single i ρ)

   sel-∨ : ∀ a b x → sel (a ∨ b) x ≈ (sel a x + sel b x)
   sel-∨ true  true  x = sym +-idem
   sel-∨ true  false x = sym +-runit
   sel-∨ false true  x = sym +-lunit
   sel-∨ false false x = sym +-lunit

   nf-⊕ : ∀ {n} (a b : NF n) (ρ : Env n) → ⟦ zipWith _∨_ a b ⟧nf ρ ≈ (⟦ a ⟧nf ρ + ⟦ b ⟧nf ρ)
   nf-⊕ []       []       []       = sym +-lunit
   nf-⊕ (p ∷ a) (q ∷ b) (x ∷ ρ) =
     trans (+-cong (sel-∨ p q x) (nf-⊕ a b ρ)) +-interchange

 sound : ∀ {n} (a : Expr n) (ρ : Env n) → ⟦ a ⟧ ρ ≈ ⟦ norm a ⟧nf ρ
 sound (var i) ρ = sym (nf-single i ρ)
 sound nil     ρ = sym (nf-nil ρ)
 sound (a ⊕ b) ρ = trans (+-cong (sound a ρ) (sound b ρ)) (sym (nf-⊕ (norm a) (norm b) ρ))

 private
   nf-cong : ∀ {n} {a b : NF n} → a ≡ b → (ρ : Env n) → ⟦ a ⟧nf ρ ≈ ⟦ b ⟧nf ρ
   nf-cong ≡-refl ρ = refl

 solve : ∀ {n} (a b : Expr n) → norm a ≡ norm b → ∀ (ρ : Env n) → ⟦ a ⟧ ρ ≈ ⟦ b ⟧ ρ
 solve a b eq ρ = trans (sound a ρ) (trans (nf-cong eq ρ) (sym (sound b ρ)))
