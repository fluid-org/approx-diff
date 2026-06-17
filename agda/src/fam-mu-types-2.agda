{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- HasMu instance for the Fam construction, against the polynomial-functor-2
-- interface (n-ary kinding contexts + nested μ). Builds initial algebras
-- (μ-types) for polynomial functors over Fam(𝒞) using setoid-indexed W-types.
--
-- Successor to fam-mu-types, which targets the single-variable, μ-free
-- polynomial-functor interface; that module is retained for reference.
------------------------------------------------------------------------------

open import Level using (_⊔_; lift) renaming (suc to lsuc)
open import Data.Nat using (ℕ; suc)
import Data.Fin as Fin
open Fin using (Fin)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import prop using (_,_; tt)
open import Data.Unit using (tt) renaming (⊤ to 𝟙S)
open import categories
  using (Category; HasTerminal; HasProducts; HasCoproducts; HasStrongCoproducts; strong-coproducts→coproducts;
         coKleisli-prod)
open import prop-setoid as PS
  using (IsEquivalence; Setoid; module ≈-Reasoning)
open import indexed-family using (Fam; _⇒f_; changeCat)
import fam
import polynomial-functor-2

open Setoid using (Carrier; isEquivalence) renaming (_≈_ to _≈s_)

module fam-mu-types-2 where

module _ {o e} where
  open import Data.Sum using (_⊎_)
  open import Data.Product using () renaming (_×_ to _×T_)
  open import prop using (_∧_; ⊥)

  ------------------------------------------------------------------------------
  -- Syntactic representation of polynomial functor but with constant slots holding a setoid rather than a
  -- category object. Used to define the W-type carrier of HasMu by structural recursion.
  data IdxPoly (n : ℕ) : Set (lsuc (o ⊔ e)) where
    param : Setoid o e → IdxPoly n
    var   : Fin n → IdxPoly n
    _+_   : IdxPoly n → IdxPoly n → IdxPoly n
    _×_   : IdxPoly n → IdxPoly n → IdxPoly n
    μ     : IdxPoly (suc n) → IdxPoly n

  _◁_ : ∀ {ℓ} {A : Set ℓ} {n} → (Fin n → A) → A → Fin (suc n) → A
  (ρ ◁ x) Fin.zero    = x
  (ρ ◁ x) (Fin.suc i) = ρ i

  -- Well-founded tree carrier (Martin-Löf W-types; see Wellorderings, pp. 43-47 of Intuitionistic Type Theory).
  mutual
    ⟦_⟧C : ∀ {n} → IdxPoly n → (Fin n → Set o) → Set o
    ⟦ param A ⟧C ρ = Carrier A
    ⟦ var i ⟧C   ρ = ρ i
    ⟦ P + Q ⟧C   ρ = ⟦ P ⟧C ρ ⊎ ⟦ Q ⟧C ρ
    ⟦ P × Q ⟧C   ρ = ⟦ P ⟧C ρ ×T ⟦ Q ⟧C ρ
    ⟦ μ P ⟧C     ρ = W P ρ

    -- P-shaped trees.
    data W {n} (P : IdxPoly (suc n)) (ρ : Fin n → Set o) : Set o where
      sup : ⟦ P ⟧C (ρ ◁ W P ρ) → W P ρ

------------------------------------------------------------------------------
-- HasMu instance for the Fam construction.
module WFam {o m e} (os es : _) {𝒞 : Category o m e} (T : HasTerminal 𝒞) (P : HasProducts 𝒞) where
  open Category 𝒞
  open IsEquivalence
  open HasTerminal
  open HasProducts P
  open fam.CategoryOfFamilies os es 𝒞
  open Obj
  open Mor
  open Fam
  private module Fam𝒞 = Category cat
  open products P  -- Fam-level products
  private module Fam𝒞-P = HasProducts products
  open _⇒f_
  open polynomial-functor-2 (terminal T) products strongCoproducts
    using (Poly; extend; fobj; HasMu; HasMuLaws)

  hasMu : HasMu
  hasMu .HasMu.μ-obj P δ = {!!}
  hasMu .HasMu.α P δ     = {!!}
  hasMu .HasMu.⦅_⦆ alg   = {!!}

  hasMuLaws : HasMuLaws hasMu
  hasMuLaws .HasMuLaws.⦅⦆-β alg     = {!!}
  hasMuLaws .HasMuLaws.⦅⦆-η alg h eq = {!!}
