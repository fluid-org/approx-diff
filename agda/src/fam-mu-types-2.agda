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
  -- Indexed-W encoding of (nested) μ. A `Sort` is a defunctionalised μ-binder: a
  -- μ-body `Q` together with a resolution of each of its free variables to either
  -- an ambient parameter slot (Fin n) or another sort. The whole nested polynomial
  -- becomes one family indexed by `Sort`, tying the outer/inner-μ knot inductively
  -- rather than through a recursive environment of types.
  data Sort (n : ℕ) : Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
    mkSort : ∀ {k} → Poly (suc k) → (Fin k → Fin n ⊎ Sort n) → Sort n

  -- The carrier of the μ-type: trees indexed by sort. `⟦_⟧shape` interprets a body
  -- into a Set, resolving variables through `El`; nested μ lands at a fresh sort. The
  -- three are mutually recursive (induction-recursion), with `W` strictly positive.
  module _ {n} (δ : Fin n → Obj) where
    mutual
      data W {k} (Q : Poly (suc k)) (ρ : Fin k → Fin n ⊎ Sort n) : Set os where
        sup : ⟦ Q ⟧shape (extend ρ (inj₂ (mkSort Q ρ))) → W Q ρ

      ⟦_⟧shape : ∀ {k} → Poly k → (Fin k → Fin n ⊎ Sort n) → Set os
      ⟦ const A ⟧shape η = A .idx .Carrier
      ⟦ var j   ⟧shape η = El (η j)
      ⟦ P + Q   ⟧shape η = ⟦ P ⟧shape η ⊎ ⟦ Q ⟧shape η
      ⟦ P × Q   ⟧shape η = ⟦ P ⟧shape η ×T ⟦ Q ⟧shape η
      ⟦ μ Q'    ⟧shape η = W Q' η

      El : Fin n ⊎ Sort n → Set os
      El (inj₁ p)            = δ p .idx .Carrier
      El (inj₂ (mkSort Q ρ)) = W Q ρ

    -- Bisimilarity of trees: equal roots with equal subtrees on equal branches. The
    -- environment is syntactic, so `shape≈` carries no relation to thread; nested-μ and
    -- recursive positions recurse straight to `W-≈` on structurally-smaller subtrees.
    mutual
      data W-≈ {k} {Q : Poly (suc k)} {ρ : Fin k → Fin n ⊎ Sort n} : W Q ρ → W Q ρ → Prop (os ⊔ es) where
        sup : ∀ {x y} → shape≈ Q (extend ρ (inj₂ (mkSort Q ρ))) x y → W-≈ (sup x) (sup y)

      shape≈ : ∀ {j} (Q : Poly j) (η : Fin j → Fin n ⊎ Sort n) →
               ⟦ Q ⟧shape η → ⟦ Q ⟧shape η → Prop (os ⊔ es)
      shape≈ (const A) η x y = _≈s_ (A .idx) x y
      shape≈ (var j)   η x y = elEq (η j) x y
      shape≈ (P + Q) η (inj₁ x) (inj₁ y) = shape≈ P η x y
      shape≈ (P + Q) η (inj₁ _) (inj₂ _) = ⊥
      shape≈ (P + Q) η (inj₂ _) (inj₁ _) = ⊥
      shape≈ (P + Q) η (inj₂ x) (inj₂ y) = shape≈ Q η x y
      shape≈ (P × Q) η (x₁ , x₂) (y₁ , y₂) = shape≈ P η x₁ y₁ ∧ shape≈ Q η x₂ y₂
      shape≈ (μ Q') η x y = W-≈ x y

      elEq : (r : Fin n ⊎ Sort n) → El r → El r → Prop (os ⊔ es)
      elEq (inj₁ p)            x y = _≈s_ (δ p .idx) x y
      elEq (inj₂ (mkSort Q ρ)) x y = W-≈ x y

  hasMu : HasMu
  hasMu .HasMu.μ-obj P δ .idx = idx-mu P δ
  hasMu .HasMu.μ-obj P δ .fam = {!!}
  hasMu .HasMu.α P δ          = {!!}
  hasMu .HasMu.⦅_⦆ alg        = {!!}

  hasMuLaws : HasMuLaws hasMu
  hasMuLaws .HasMuLaws.⦅⦆-β alg     = {!!}
  hasMuLaws .HasMuLaws.⦅⦆-η alg h eq = {!!}
