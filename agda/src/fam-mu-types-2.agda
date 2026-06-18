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

  -- Position correspondence: which variable-i positions of two shapes match up. R-free, so it carries no
  -- environment. Used to align subtrees in the shape equality and position-functions in the element equality.
  PosR : ∀ {n} (P : IdxPoly n) (s s' : Sh P) (i : Fin n) → Pos P s i → Pos P s' i → Prop (os ⊔ es)
  PosR (param A) _ _ _ ()
  PosR (var _) _ _ _ _ _ = ⊤
  PosR (P + Q) (inj₁ s) (inj₁ s') i p p' = PosR P s s' i p p'
  PosR (P + Q) (inj₁ _) (inj₂ _) _ _ _ = ⊥
  PosR (P + Q) (inj₂ _) (inj₁ _) _ _ _ = ⊥
  PosR (P + Q) (inj₂ t) (inj₂ t') i p p' = PosR Q t t' i p p'
  PosR (P × Q) (s , _) (s' , _) i (inj₁ p) (inj₁ p') = PosR P s s' i p p'
  PosR (P × Q) _ _ _ (inj₁ _) (inj₂ _) = ⊥
  PosR (P × Q) _ _ _ (inj₂ _) (inj₁ _) = ⊥
  PosR (P × Q) (_ , t) (_ , t') i (inj₂ q) (inj₂ q') = PosR Q t t' i q q'
  PosR (μ Q) (sup s _) (sup s' _) i (inj₁ p) (inj₁ p') = PosR Q s s' (Fin.suc i) p p'
  PosR (μ Q) (sup _ _) (sup _ _) _ (inj₁ _) (inj₂ _) = ⊥
  PosR (μ Q) (sup _ _) (sup _ _) _ (inj₂ _) (inj₁ _) = ⊥
  PosR (μ Q) (sup s f) (sup s' f') i (inj₂ (r , q)) (inj₂ (r' , q')) =
    PosR Q s s' Fin.zero r r' ∧ PosR (μ Q) (f r) (f' r') i q q'

  -- Shape equality: structural on the (ρ-free) shapes, matching (via Wsh≈) on μ shape-trees, aligning subtrees
  -- by PosR. R-free, hence no threading: refl/sym/trans recurse on the shape-trees directly.
  mutual
    Sh≈ : ∀ {n} (P : IdxPoly n) → Sh P → Sh P → Prop (os ⊔ es)
    Sh≈ (param A) a a' = _≈s_ A a a'
    Sh≈ (var _) _ _ = ⊤
    Sh≈ (P + Q) (inj₁ s) (inj₁ s') = Sh≈ P s s'
    Sh≈ (P + Q) (inj₁ _) (inj₂ _) = ⊥
    Sh≈ (P + Q) (inj₂ _) (inj₁ _) = ⊥
    Sh≈ (P + Q) (inj₂ t) (inj₂ t') = Sh≈ Q t t'
    Sh≈ (P × Q) (s , t) (s' , t') = Sh≈ P s s' ∧ Sh≈ Q t t'
    Sh≈ (μ Q) w w' = Wsh≈ Q w w'

    Wsh≈ : ∀ {n} (Q : IdxPoly (suc n)) → Wsh Q → Wsh Q → Prop (os ⊔ es)
    Wsh≈ Q (sup s f) (sup s' f') =
      Sh≈ Q s s' ∧ (∀ r r' → PosR Q s s' Fin.zero r r' → Wsh≈ Q (f r) (f' r'))

  -- Element equality: shapes equal, and the position-functions agree on every matching pair of positions.
  Elt≈ : ∀ {n} {ρ : Fin n → Set os} (R : (i : Fin n) → ρ i → ρ i → Prop (os ⊔ es))
         (P : IdxPoly n) (s : Sh P) → ((i : Fin n) → Pos P s i → ρ i) →
         (s' : Sh P) → ((i : Fin n) → Pos P s' i → ρ i) → Prop (os ⊔ es)
  Elt≈ R P s g s' g' =
    Sh≈ P s s' ∧ (∀ i (p : Pos P s i) (p' : Pos P s' i) → PosR P s s' i p p' → R i (g i p) (g' i p'))

  hasMu : HasMu
  hasMu .HasMu.μ-obj P δ = {!!}
  hasMu .HasMu.α P δ     = {!!}
  hasMu .HasMu.⦅_⦆ alg   = {!!}

  hasMuLaws : HasMuLaws hasMu
  hasMuLaws .HasMuLaws.⦅⦆-β alg     = {!!}
  hasMuLaws .HasMuLaws.⦅⦆-η alg h eq = {!!}
