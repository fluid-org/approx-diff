{-# OPTIONS --postfix-projections --prop --safe #-}

-- The higher-order model with SDSemiMod as the first-order model: families over self-dual
-- semimodules, interpreted in Fam(SemiMod S) via the forgetful functor U.
open import Level using (0ℓ)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import signature using (Signature; Model; PFPC[_,_,_,_])
open import categories using (Category)
open import prop using (_,_)
open import Data.Product using (_,_; Σ-syntax)
open import Data.Nat using (ℕ; _+_)
open import Data.Sum using (inj₁; inj₂)
import nat
import lists
import language-syntax
import language-syntax-2
import semimodule
import sd-semimodule
import ho-model

module ho-model-sd-semimod {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A) where

module SemiMod = semimodule S
module SDSemiMod = sd-semimodule S

open ho-model.Interpretation
  SDSemiMod.cat SDSemiMod.terminal SDSemiMod.products
  SemiMod.cat SemiMod.cmon-enriched SemiMod.limits SemiMod.terminal SemiMod.biproduct
  SDSemiMod.U SDSemiMod.U-preserve-terminal (λ {X} {Y} → SDSemiMod.U-preserve-products {X} {Y})
  (λ e → e) (λ h _ → h , Category.≈-refl SemiMod.cat)
  public

-- Self-dualities on first-order-data types.
module interp-sd (Sig : Signature 0ℓ)
                 (Impl : Model PFPC[ Fam⟨𝒞⟩.cat , Fam⟨𝒞⟩-terminal , Fam⟨𝒞⟩-products , Fam⟨𝒞⟩-bool ] Sig)
   where

  open interp Sig Impl public
  open language-syntax Sig using (_⊢_; first-order-data; unit; bool; base; _[×]_; _[+]_; list)
  open SDSemiMod using (SelfDual; 𝟘; _⊕_; _≅sd_; ≅sd-refl; ≅sd-trans; ⊕-≅sd; S^_; S^-+) public
  open Setoid using (Carrier)
  open Fam⟨𝒞⟩ using (fm)
  open Fam⟨𝒞⟩.Obj using (fam)
  open Model Impl using (⟦sort⟧)
  open lists Fam⟨𝒟⟩.cat Fam⟨𝒟⟩-terminal Fam⟨𝒟⟩-products Fam⟨𝒟⟩-exponentials Fam⟨𝒟⟩.bigCoproducts
    using (_^_)

  -- Fam(U) is the functor H in the paper.
  open FirstOrderConservativity
    (λ {X} {Y} → SDSemiMod.U-full {X} {Y})
    (λ {X} {Y} {f} {g} → SDSemiMod.U-faithful {X} {Y} {f} {g})
    Sig Impl public

  ty  : ∀ {τ} → first-order-data τ → (i : ⟦ τ ⟧ty .idx .Carrier) → SelfDual
  pow : ∀ {τ} → first-order-data τ → (n : nat.ℕ) → (i : (⟦ τ ⟧ty ^ n) .idx .Carrier) → SelfDual

  ty unit       _        = 𝟘
  ty bool       _        = 𝟘
  ty (base s)   i        = ⟦sort⟧ s .fam .fm i
  ty (a [×] b)  (i , j)  = ty a i ⊕ ty b j
  ty (a [+] b)  (inj₁ i) = ty a i
  ty (a [+] b)  (inj₂ j) = ty b j
  ty (list a)   (n , i)  = pow a n i

  pow a nat.zero     _        = 𝟘
  pow a (nat.succ n) (i , is) = ty a i ⊕ pow a n is

  -- Given tower isomorphisms for the base sorts, every first-order fibre is isomorphic,
  -- compatibly with the self-dualities, to a free semimodule S^n.
  module FreeFibres
    (base-free : ∀ s (i : ⟦ base s ⟧ty .idx .Carrier) →
                 Σ[ n ∈ ℕ ] (ty (base s) i ≅sd (S^ n)))
    where

    ty-free : ∀ {τ} (a : first-order-data τ) (i : ⟦ τ ⟧ty .idx .Carrier) →
              Σ[ n ∈ ℕ ] (ty a i ≅sd (S^ n))
    pow-free : ∀ {τ} (a : first-order-data τ) (n : nat.ℕ) (i : (⟦ τ ⟧ty ^ n) .idx .Carrier) →
               Σ[ m ∈ ℕ ] (pow a n i ≅sd (S^ m))

    ty-free unit _ = 0 , ≅sd-refl
    ty-free bool _ = 0 , ≅sd-refl
    ty-free (base s) i = base-free s i
    ty-free (a [×] b) (i , j) with ty-free a i | ty-free b j
    ... | m , em | n , en = m + n , ≅sd-trans (⊕-≅sd em en) (S^-+ m n)
    ty-free (a [+] b) (inj₁ i) = ty-free a i
    ty-free (a [+] b) (inj₂ j) = ty-free b j
    ty-free (list a) (n , i) = pow-free a n i

    pow-free a nat.zero _ = 0 , ≅sd-refl
    pow-free a (nat.succ n) (i , is) with ty-free a i | pow-free a n is
    ... | m , em | k , ek = m + k , ≅sd-trans (⊕-≅sd em ek) (S^-+ m k)

  open SemiMod._⇒_ using (func)

  -- Forward analysis: feed an input tangent, read the output tangent.
  fwd : ∀ {Γ τ} (M : Γ ⊢ τ) (env : ⟦ Γ ⟧ctxt .idx .Carrier) → _
  fwd M env = mor M env .func

-- Self-dualities on the first-order types of the language with general
-- recursive types: instantiate the generic fibre-object machinery at the
-- self-dual semimodules.
module interp-sd-2 (Sig : Signature 0ℓ)
                   (Impl : Model PFPC[ Fam⟨𝒞⟩.cat , Fam⟨𝒞⟩-terminal , Fam⟨𝒞⟩-products , Fam⟨𝒞⟩-bool ] Sig)
   where

  open interp-2 Sig Impl public
  open language-syntax-2 Sig using (_⊢_)
  open SDSemiMod using (SelfDual; 𝟘; _⊕_) public
  open Setoid using (Carrier)

  open SemiMod._⇒_ using (func)

  -- Forward analysis: feed an input tangent, read the output tangent.
  fwd : ∀ {Γ τ} (M : Γ ⊢ τ) (env : ⟦ Γ ⟧ctxt .idx .Carrier) → _
  fwd M env = mor M env .func
