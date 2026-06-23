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

  -- Boolean self-dual lattices on first-order-data types (for the Galois backward via to-gal), given that
  -- S is a Boolean lattice: ∧-idem, ⊤-add-top, and a scalar negation with complement laws.
  module ty-bsddl-mod
    (∧-idem    : ∀ {x} → SM.S._≈_ (SM.S._·_ x x) x)
    (⊤-add-top : ∀ {x} → SM.S._≈_ (SM.S._+_ SM.S.ι x) SM.S.ι)
    (let module JS = SM.JoinSemilattices ⊤-add-top)
    (¬ : SM.S.Carrier → SM.S.Carrier)
    (complement-∧ : ∀ {x} → JS._≤_ SM.𝕀 (SM.S._·_ x (¬ x)) SM.S.ε)
    (complement-∨ : ∀ {x} → JS._≤_ SM.𝕀 SM.S.ι (SM.S._+_ x (¬ x)))
    where
    open JS using (BooleanSDDL)
    open JS.DistribLattices ∧-idem using (𝟘-bsddl; ⊕-bsddl)
    open matrix-new.DistribLattices.DistribLattice S ∧-idem ⊤-add-top using (vec-bsddl)

    private
      𝟘b   = 𝟘-bsddl ¬ complement-∧ complement-∨
      ⊕b   = ⊕-bsddl ¬ complement-∧ complement-∨
      vecb = vec-bsddl ¬ complement-∧ complement-∨

    ty-bsddl  : ∀ {τ} → first-order-data τ → (i : ⟦ τ ⟧ty .idx .Carrier) → BooleanSDDL
    pow-bsddl : ∀ {τ} → first-order-data τ → (n : nat.ℕ) → (i : (L._^_ (⟦ τ ⟧ty) n) .idx .Carrier) → BooleanSDDL

    ty-bsddl unit       _        = 𝟘b
    ty-bsddl bool       _        = 𝟘b
    ty-bsddl (base s)   i        = vecb (ImplM.⟦sort⟧ s .fam .fm i)
    ty-bsddl (a [×] b)  (i , j)  = ⊕b (ty-bsddl a i) (ty-bsddl b j)
    ty-bsddl (a [+] b)  (inj₁ i) = ty-bsddl a i
    ty-bsddl (a [+] b)  (inj₂ j) = ty-bsddl b j
    ty-bsddl (list a)   (n , i)  = pow-bsddl a n i

    pow-bsddl a nat.zero     _        = 𝟘b
    pow-bsddl a (nat.succ n) (i , is) = ⊕b (ty-bsddl a i) (pow-bsddl a n is)
