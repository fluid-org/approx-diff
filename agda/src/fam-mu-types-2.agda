{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- HasMu instance for the Fam construction, against the polynomial-functor-2
-- interface (n-ary kinding contexts + nested μ). Builds initial algebras
-- (μ-types) for polynomial functors over Fam(𝒞) using setoid-indexed W-types.
--
-- Successor to fam-mu-types, which targets the single-variable, μ-free
-- polynomial-functor interface; that module is retained for reference.
--
-- Abbott, Altenkirch, Ghani. Containers: constructing strictly positive types. TCS 342(1), 2005.
-- Abbott, Altenkirch, Ghani. Representing nested inductive types using W-types. ICALP 2004.
-- Emmenegger. W-types in setoids. arXiv:1809.02375, 2018.
------------------------------------------------------------------------------

open import Level using (_⊔_; lift; Lift) renaming (suc to lsuc)
open import Data.Nat using (ℕ; suc)
import Data.Fin as Fin
open Fin using (Fin)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; Σ; Σ-syntax)
open import Data.Empty renaming (⊥ to ⊥S)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl)
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

------------------------------------------------------------------------------
-- HasMu instance for the Fam construction.
module WFam {o m e} (os es : _) {𝒞 : Category o m e} (T : HasTerminal 𝒞) (P : HasProducts 𝒞) where
  open Category 𝒞
  open IsEquivalence
  open HasTerminal
  open HasProducts P
  open fam.CategoryOfFamilies os (os ⊔ es) 𝒞
  open Obj
  open Mor
  open Fam
  private module Fam𝒞 = Category cat
  open products P  -- Fam-level products
  private module Fam𝒞-P = HasProducts products
  open _⇒f_
  open polynomial-functor-2 (terminal T) products strongCoproducts
    using (Poly; extend; fobj; HasMu; HasMuLaws)

  open import Data.Sum using (_⊎_)
  open import Data.Product using () renaming (_×_ to _×T_)
  open import prop using (_∧_; ⊤; ⊥)

  ------------------------------------------------------------------------------
  -- Syntactic representation of polynomial functor but with constant slots holding a setoid rather than a
  -- category object. Used to define the W-type carrier of HasMu by structural recursion.
  data IdxPoly (n : ℕ) : Set (lsuc (os ⊔ es)) where
    param : Setoid os (os ⊔ es) → IdxPoly n
    var   : Fin n → IdxPoly n
    _+_   : IdxPoly n → IdxPoly n → IdxPoly n
    _×_   : IdxPoly n → IdxPoly n → IdxPoly n
    μ     : IdxPoly (suc n) → IdxPoly n

  -- Polynomials denote containers (shapes + positions per variable). Shapes are closed in ρ, so the
  -- tree equality below recurses structurally rather than threading the variable interpretation.
  mutual
    Sh : ∀ {n} → IdxPoly n → Set os
    Sh (param A) = Carrier A
    Sh (var _)   = Lift os 𝟙S
    Sh (P + Q)   = Sh P ⊎ Sh Q
    Sh (P × Q)   = Sh P ×T Sh Q
    Sh (μ Q)     = Wsh Q

    Pos : ∀ {n} (P : IdxPoly n) → Sh P → Fin n → Set
    Pos (param A) _        i = ⊥S
    Pos (var j)   _        i = j ≡ i
    Pos (P + Q)   (inj₁ s) i = Pos P s i
    Pos (P + Q)   (inj₂ s) i = Pos Q s i
    Pos (P × Q)   (s , t)  i = Pos P s i ⊎ Pos Q t i
    Pos (μ Q)     w        i = WPos Q w i

    -- Shape of μ Q: a well-founded tree of Q-shapes (Martin-Löf W-types; see Wellorderings, pp. 43-47 of
    -- Intuitionistic Type Theory), branching on Q's variable-0 positions.
    data Wsh {n} (Q : IdxPoly (suc n)) : Set os where
      sup : (s : Sh Q) → (Pos Q s Fin.zero → Wsh Q) → Wsh Q

    -- Variable-i position in the tree: a variable-(suc i) position at the root, or a descent through a
    -- variable-0 position.
    WPos : ∀ {n} (Q : IdxPoly (suc n)) → Wsh Q → Fin n → Set
    WPos Q (sup s f) i = Pos Q s (Fin.suc i) ⊎ Σ[ r ∈ Pos Q s Fin.zero ] WPos Q (f r) i

  -- Carrier of the μ-type: a shape-tree with an assignment of each variable position to its interpretation.
  μ-carrier : ∀ {n} → IdxPoly (suc n) → (Fin n → Set os) → Set os
  μ-carrier {n} P ρ = Σ[ w ∈ Wsh P ] ((i : Fin n) → WPos P w i → ρ i)

  -- Element equality: recurse on the (ρ-free) shapes, comparing the position-functions in parallel; at each
  -- leaf both are applied at the canonical position, so positions align without transport. R relates the
  -- variable interpretations. The μ case recurses on the shape-tree (Wμ≈), descending into explicit subtrees.
  mutual
    Elt≈ : ∀ {n} {ρ : Fin n → Set os} (R : (i : Fin n) → ρ i → ρ i → Prop (os ⊔ es))
           (P : IdxPoly n) (s : Sh P) → ((i : Fin n) → Pos P s i → ρ i) →
           (s' : Sh P) → ((i : Fin n) → Pos P s' i → ρ i) → Prop (os ⊔ es)
    Elt≈ R (param A) a _ a' _ = _≈s_ A a a'
    Elt≈ R (var j) _ g _ g' = R j (g j ≡-refl) (g' j ≡-refl)
    Elt≈ R (P + Q) (inj₁ s) g (inj₁ s') g' = Elt≈ R P s g s' g'
    Elt≈ R (P + Q) (inj₁ _) _ (inj₂ _) _ = ⊥
    Elt≈ R (P + Q) (inj₂ _) _ (inj₁ _) _ = ⊥
    Elt≈ R (P + Q) (inj₂ t) g (inj₂ t') g' = Elt≈ R Q t g t' g'
    Elt≈ R (P × Q) (s , t) g (s' , t') g' =
      Elt≈ R P s (λ i p → g i (inj₁ p)) s' (λ i p → g' i (inj₁ p)) ∧
      Elt≈ R Q t (λ i q → g i (inj₂ q)) t' (λ i q → g' i (inj₂ q))
    Elt≈ R (μ Q) w g w' g' = Wμ≈ R Q w g w' g'

    Wμ≈ : ∀ {n} {ρ : Fin n → Set os} (R : (i : Fin n) → ρ i → ρ i → Prop (os ⊔ es))
          (Q : IdxPoly (suc n)) (w : Wsh Q) → ((i : Fin n) → WPos Q w i → ρ i) →
          (w' : Wsh Q) → ((i : Fin n) → WPos Q w' i → ρ i) → Prop (os ⊔ es)
    Wμ≈ R Q w g w' g' = {!!}

  hasMu : HasMu
  hasMu .HasMu.μ-obj P δ = {!!}
  hasMu .HasMu.α P δ     = {!!}
  hasMu .HasMu.⦅_⦆ alg   = {!!}

  hasMuLaws : HasMuLaws hasMu
  hasMuLaws .HasMuLaws.⦅⦆-β alg     = {!!}
  hasMuLaws .HasMuLaws.⦅⦆-η alg h eq = {!!}
