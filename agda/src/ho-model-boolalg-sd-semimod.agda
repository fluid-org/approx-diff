{-# OPTIONS --postfix-projections --prop --safe #-}

-- The higher-order model with the self-dual Boolean algebras as the first-order model: families over
-- self-dual Boolean algebras, interpreted in Fam(SemiMod S) via the forgetful functor U.
open import Level using (0ℓ)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring; BooleanAlgebra)
open import signature using (Signature; Model; PFPC[_,_,_,_])
open import categories using (Category)
open import prop using (_,_)
import language-syntax-2
import semimodule
import boolalg-sd-semimodule
import ho-model

module ho-model-boolalg-sd-semimod {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A) (boolean : BooleanAlgebra S) where

module SemiMod = semimodule S
module BoolAlg = boolalg-sd-semimodule S boolean

open ho-model.Interpretation
  BoolAlg.cat BoolAlg.terminal BoolAlg.products
  SemiMod.cat SemiMod.cmon-enriched SemiMod.limits SemiMod.terminal SemiMod.biproduct
  BoolAlg.U BoolAlg.U-preserve-terminal (λ {X} {Y} → BoolAlg.U-preserve-products {X} {Y})
  (λ e → e) (λ h _ → h , Category.≈-refl SemiMod.cat)
  public

-- Self-dual Boolean algebras on the first-order types of the language with
-- general recursive types: instantiate the generic fibre-object machinery at
-- the Boolean algebras.
module interp-boolean-2 (Sig : Signature 0ℓ)
                        (Impl : Model PFPC[ Fam⟨𝒞⟩.cat , Fam⟨𝒞⟩-terminal , Fam⟨𝒞⟩-products , Fam⟨𝒞⟩-bool ] Sig)
   where

  open interp-2 Sig Impl public
  open language-syntax-2 Sig using (_⊢_)
  open BoolAlg using (SelfDualBooleanAlgebra; 𝟘; _⊕_; to-gal) public
  open Setoid using (Carrier)

  open SemiMod._⇒_ using (func)

  -- Forward analysis: feed an input tangent, read the output tangent.
  fwd : ∀ {Γ τ} (M : Γ ⊢ τ) (env : ⟦ Γ ⟧ctxt .idx .Carrier) → _
  fwd M env = mor M env .func
