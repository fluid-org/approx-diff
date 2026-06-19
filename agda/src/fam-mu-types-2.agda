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

open import Level using (_⊔_; lift) renaming (suc to lsuc)
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n) renaming (_+_ to _+ℕ_)
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
open import setoid-cat using (SetoidCat; Setoid-terminal; Setoid-products)
import setoid-cat-colimits
import colimit-mu-types
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
    using (Poly; const; var; _+_; _×_; μ; extend; fobj; HasMu; HasMuLaws)

  ------------------------------------------------------------------------------
  -- The index of the Fam μ-type is a setoid μ-type: SetoidCat is cocomplete
  -- (setoid-cat-colimits), so colimit-mu-types builds initial algebras there.
  -- A Fam-polynomial maps to a setoid-polynomial by sending each const's Fam-obj
  -- to its index setoid; the index of `μ-obj P δ` is the setoid μ of that image.
  private
    𝒮T   = Setoid-terminal os (os ⊔ es)
    𝒮P   = Setoid-products os (os ⊔ es)
    𝒮SC  = setoid-cat-colimits.strongCoproducts os es
    𝒮I   = setoid-cat-colimits.initial os es
    𝒮Col = setoid-cat-colimits.ωcolimits os es

  module SetoidPoly = polynomial-functor-2 𝒮T 𝒮P 𝒮SC
  module SμT = colimit-mu-types 𝒮T 𝒮P 𝒮SC 𝒮I 𝒮Col

  -- Index translation: replace each parameter object by its index setoid.
  tr : ∀ {n} → Poly n → SetoidPoly.Poly n
  tr (const A) = SetoidPoly.const (A .idx)
  tr (var i)   = SetoidPoly.var i
  tr (P + Q)   = tr P SetoidPoly.+ tr Q
  tr (P × Q)   = tr P SetoidPoly.× tr Q
  tr (μ P)     = SetoidPoly.μ (tr P)

  -- The index setoid of the Fam μ-type.
  idx-mu : ∀ {n} → Poly (suc n) → (Fin n → Obj) → Setoid os (os ⊔ es)
  idx-mu P δ = SμT.μ-carrier (tr P) (λ i → δ i .idx)

  open import Data.Sum using (_⊎_)
  open import Data.Product using () renaming (_×_ to _×T_)
  open import prop using (_∧_; ⊥)

  ------------------------------------------------------------------------------
  -- Syntactic representation of polynomial functor but with constant slots holding a setoid rather than a
  -- category object. Used to define the W-type carrier of HasMu by structural recursion.
  data IdxPoly (n : ℕ) : Set (lsuc (os ⊔ es)) where
    param : Setoid os (os ⊔ es) → IdxPoly n
    var   : Fin n → IdxPoly n
    _+_   : IdxPoly n → IdxPoly n → IdxPoly n
    _×_   : IdxPoly n → IdxPoly n → IdxPoly n
    μ     : IdxPoly (suc n) → IdxPoly n

  -- Well-founded tree carrier (Martin-Löf W-types; see Wellorderings, pp. 43-47 of Intuitionistic Type Theory).
  mutual
    ⟦_⟧C : ∀ {n} → IdxPoly n → (Fin n → Set os) → Set os
    ⟦ param A ⟧C ρ = Carrier A
    ⟦ var i ⟧C   ρ = ρ i
    ⟦ P + Q ⟧C   ρ = ⟦ P ⟧C ρ ⊎ ⟦ Q ⟧C ρ
    ⟦ P × Q ⟧C   ρ = ⟦ P ⟧C ρ ×T ⟦ Q ⟧C ρ
    ⟦ μ P ⟧C     ρ = W P ρ

    -- P-shaped trees.
    data W {n} (P : IdxPoly (suc n)) (ρ : Fin n → Set os) : Set os where
      sup : ⟦ P ⟧C (extend ρ (W P ρ)) → W P ρ

  extendR : ∀ {n} {ρ : Fin n → Set os} {X} →
            ((i : Fin n) → ρ i → ρ i → Prop (os ⊔ es)) → (X → X → Prop (os ⊔ es)) →
            (i : Fin (suc n)) → extend ρ X i → extend ρ X i → Prop (os ⊔ es)
  extendR R r Fin.zero    = r
  extendR R r (Fin.suc i) = R i

  -- Two trees are equal when their roots are equal and their subtrees on equal
  -- branches are equal: an inductively defined relation (cf. W-types in setoids).
  mutual
    data W-≈ {n} (P : IdxPoly (suc n)) {ρ : Fin n → Set os}
             (R : (i : Fin n) → ρ i → ρ i → Prop (os ⊔ es)) : W P ρ → W P ρ → Prop (os ⊔ es) where
      sup : ∀ {x y} → shape≈ P R P x y → W-≈ P R (sup x) (sup y)

    shape≈ : ∀ {n} (P : IdxPoly (suc n)) {ρ : Fin n → Set os}
             (R : (i : Fin n) → ρ i → ρ i → Prop (os ⊔ es)) (Q : IdxPoly (suc n)) →
             ⟦ Q ⟧C (extend ρ (W P ρ)) → ⟦ Q ⟧C (extend ρ (W P ρ)) → Prop (os ⊔ es)
    shape≈ P R (param A)         x y = _≈s_ A x y
    shape≈ P R (var Fin.zero)    x y = W-≈ P R x y
    shape≈ P R (var (Fin.suc i)) x y = R i x y
    shape≈ P R (Q₁ + Q₂) (inj₁ x) (inj₁ y) = shape≈ P R Q₁ x y
    shape≈ P R (Q₁ + Q₂) (inj₁ _) (inj₂ _) = ⊥
    shape≈ P R (Q₁ + Q₂) (inj₂ _) (inj₁ _) = ⊥
    shape≈ P R (Q₁ + Q₂) (inj₂ x) (inj₂ y) = shape≈ P R Q₂ x y
    shape≈ P R (Q₁ × Q₂) (x₁ , x₂) (y₁ , y₂) = shape≈ P R Q₁ x₁ y₁ ∧ shape≈ P R Q₂ x₂ y₂
    shape≈ P R (μ Q') x y = W-≈ Q' (extendR R (W-≈ P R)) x y

  -- Structural node-count of a tree. Recurses directly (variable 0 is the recursive position), so it has no
  -- higher-order environment and needs no well-founded justification; it is the measure for the proofs below.
  mutual
    size : ∀ {n} {Q : IdxPoly (suc n)} {ρ : Fin n → Set os} → W Q ρ → ℕ
    size {Q = Q} (sup x) = suc (contentSize {P = Q} Q x)

    contentSize : ∀ {n} {P : IdxPoly (suc n)} {ρ : Fin n → Set os} (Q : IdxPoly (suc n)) →
                  ⟦ Q ⟧C (extend ρ (W P ρ)) → ℕ
    contentSize (param A) _ = 0
    contentSize (var Fin.zero) t = size t
    contentSize (var (Fin.suc i)) _ = 0
    contentSize (Q₁ + Q₂) (inj₁ x) = contentSize Q₁ x
    contentSize (Q₁ + Q₂) (inj₂ y) = contentSize Q₂ y
    contentSize (Q₁ × Q₂) (x , y) = contentSize Q₁ x +ℕ contentSize Q₂ y
    contentSize (μ Q') t = size t

  hasMu : HasMu
  hasMu .HasMu.μ-obj P δ = {!!}
  hasMu .HasMu.α P δ     = {!!}
  hasMu .HasMu.⦅_⦆ alg   = {!!}

  hasMuLaws : HasMuLaws hasMu
  hasMuLaws .HasMuLaws.⦅⦆-β alg     = {!!}
  hasMuLaws .HasMuLaws.⦅⦆-η alg h eq = {!!}
