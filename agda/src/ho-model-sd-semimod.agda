{-# OPTIONS --postfix-projections --prop --safe #-}

-- The higher-order model with SDSemiMod as the first-order model: families over self-dual
-- semimodules, interpreted in Fam(SemiMod S) via the forgetful functor U.
open import Level using (0ℓ)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import signature using (Signature; Model; PFPC[_,_,_,_])
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
import nat
import lists
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
  public

-- Self-dualities on first-order-data types.
module interp-sd (Sig : Signature 0ℓ)
                 (Impl : Model PFPC[ Fam⟨𝒞⟩.cat , Fam⟨𝒞⟩-terminal , Fam⟨𝒞⟩-products , Fam⟨𝒞⟩-bool ] Sig)
   where

  open interp Sig Impl public
  open language-syntax Sig using (_⊢_; first-order-data; unit; bool; base; _[×]_; _[+]_; list)
  open SDSemiMod using (SelfDual; 𝟘; _⊕_) public
  open Setoid using (Carrier)
  open Fam⟨𝒞⟩ using (fm)
  open Fam⟨𝒞⟩.Obj using (fam)
  open Model Impl using (⟦sort⟧)
  open lists Fam⟨𝒟⟩.cat Fam⟨𝒟⟩-terminal Fam⟨𝒟⟩-products Fam⟨𝒟⟩-exponentials Fam⟨𝒟⟩.bigCoproducts
    using (_^_)

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

  open SemiMod._⇒_ using (func)

  -- Forward analysis: feed an input tangent, read the output tangent.
  fwd : ∀ {Γ τ} (M : Γ ⊢ τ) (env : ⟦ Γ ⟧ctxt .idx .Carrier) → _
  fwd M env = mor M env .func
