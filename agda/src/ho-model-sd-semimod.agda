{-# OPTIONS --postfix-projections --prop --safe #-}

-- The higher-order model with SDSemiMod as the first-order model: families over self-dual
-- semimodules, interpreted in Fam(SemiMod S) via the forgetful functor U.
open import Level using (0ℓ)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import signature using (Signature; Model; PFPC[_,_,_,_])
open import categories using (Category)
open import prop using (_,_)
import language-syntax
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

-- Self-dualities on the first-order types of the language with general
-- recursive types: instantiate the generic fibre-object machinery at the
-- self-dual semimodules.
module interp-sd (Sig : Signature 0ℓ)
                   (Impl : Model PFPC[ Fam⟨𝒞⟩.cat , Fam⟨𝒞⟩-terminal , Fam⟨𝒞⟩-products , Fam⟨𝒞⟩-bool ] Sig)
   where

  open interp Sig Impl public
  open language-syntax Sig using (_⊢_)
  open SDSemiMod using (SelfDual; 𝟘; _⊕_) public
  open Setoid using (Carrier)

  open SemiMod._⇒_ using (func)

  -- Forward analysis: feed an input tangent, read the output tangent.
  fwd : ∀ {Γ τ} (M : Γ ⊢ τ) (env : ⟦ Γ ⟧ctxt .idx .Carrier) → _
  fwd M env = mor M env .func
