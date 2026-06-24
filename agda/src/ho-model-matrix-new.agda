{-# OPTIONS --postfix-projections --prop --safe #-}

-- The higher-order model over the Data.Vec matrix representation (matrix-new):
-- Fam(Mat S) interpreted in Fam(SemiMod S) via the embedding F : Mat ↪ SemiMod.
open import Level using (0ℓ)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import signature using (Signature; Model; PFPC[_,_,_,_])
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
import nat
import lists
import language-syntax
import matrix-new
import semimodule
import ho-model

module ho-model-matrix-new {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A) where

module E  = matrix-new.Embedding S
module FD = matrix-new.Mat S
module SM = semimodule S

open ho-model.Interpretation
  FD.cat FD.terminal FD.products
  SM.cat SM.cmon-enriched SM.limits SM.terminal SM.biproduct
  E.F E.F-preserve-terminal
  (λ {X} {Y} → E.F-preserve-products {X} {Y})
  public

-- Self-dualities on first-order-data types.
module interp-sd (Sig : Signature 0ℓ)
                 (Impl : Model PFPC[ Fam⟨𝒞⟩.cat , Fam⟨𝒞⟩-terminal , Fam⟨𝒞⟩-products , Fam⟨𝒞⟩-bool ] Sig)
   where

  open interp Sig Impl public
  open language-syntax Sig using (first-order-data; unit; bool; base; _[×]_; _[+]_; list)
  open SM using (SelfDual; 𝟘-sd; ⊕-sd)
  open Setoid using (Carrier)
  open Fam⟨𝒞⟩ using (fm)
  open Fam⟨𝒞⟩.Obj using (fam)
  private
    module ImplM = Model Impl
    module L = lists Fam⟨𝒟⟩.cat Fam⟨𝒟⟩-terminal Fam⟨𝒟⟩-products Fam⟨𝒟⟩-exponentials Fam⟨𝒟⟩.bigCoproducts

  ty-sd  : ∀ {τ} → first-order-data τ → (i : ⟦ τ ⟧ty .idx .Carrier) → SelfDual
  pow-sd : ∀ {τ} → first-order-data τ → (n : nat.ℕ) → (i : (L._^_ (⟦ τ ⟧ty) n) .idx .Carrier) → SelfDual

  ty-sd unit       _        = 𝟘-sd
  ty-sd bool       _        = 𝟘-sd
  ty-sd (base s)   i        = E.fobj-sd (ImplM.⟦sort⟧ s .fam .fm i)
  ty-sd (a [×] b)  (i , j)  = ⊕-sd (ty-sd a i) (ty-sd b j)
  ty-sd (a [+] b)  (inj₁ i) = ty-sd a i
  ty-sd (a [+] b)  (inj₂ j) = ty-sd b j
  ty-sd (list a)   (n , i)  = pow-sd a n i

  pow-sd a nat.zero     _        = 𝟘-sd
  pow-sd a (nat.succ n) (i , is) = ⊕-sd (ty-sd a i) (pow-sd a n is)

  -- Boolean self-dual lattices on first-order-data types, given that the scalar S is a Boolean algebra.
  module ty-bsddl-mod (bs : SM.BooleanSemiring) where
    open SM.BooleanSemiring bs
    private module JS = SM.JoinSemilattices (λ {x} → ⊤-add-top {x})
    open JS using (BooleanSDDL; to-gal) public
    open JS.DistribLattices (λ {x} → ∧-idem {x}) using (𝟘-bsddl; ⊕-bsddl)
    open matrix-new.DistribLattices.DistribLattice S (λ {x} → ∧-idem {x}) (λ {x} → ⊤-add-top {x}) using (vec-bsddl)

    ty-bsddl  : ∀ {τ} → first-order-data τ → (i : ⟦ τ ⟧ty .idx .Carrier) → BooleanSDDL
    pow-bsddl : ∀ {τ} → first-order-data τ → (n : nat.ℕ) → (i : (L._^_ (⟦ τ ⟧ty) n) .idx .Carrier) → BooleanSDDL

    ty-bsddl unit       _        = 𝟘-bsddl ¬ complement-∧ complement-∨
    ty-bsddl bool       _        = 𝟘-bsddl ¬ complement-∧ complement-∨
    ty-bsddl (base s)   i        = vec-bsddl ¬ complement-∧ complement-∨ (ImplM.⟦sort⟧ s .fam .fm i)
    ty-bsddl (a [×] b)  (i , j)  = ⊕-bsddl ¬ complement-∧ complement-∨ (ty-bsddl a i) (ty-bsddl b j)
    ty-bsddl (a [+] b)  (inj₁ i) = ty-bsddl a i
    ty-bsddl (a [+] b)  (inj₂ j) = ty-bsddl b j
    ty-bsddl (list a)   (n , i)  = pow-bsddl a n i

    pow-bsddl a nat.zero     _        = 𝟘-bsddl ¬ complement-∧ complement-∨
    pow-bsddl a (nat.succ n) (i , is) = ⊕-bsddl ¬ complement-∧ complement-∨ (ty-bsddl a i) (pow-bsddl a n is)
