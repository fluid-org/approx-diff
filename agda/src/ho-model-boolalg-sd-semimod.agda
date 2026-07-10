{-# OPTIONS --postfix-projections --prop --safe #-}

-- The higher-order model with the self-dual Boolean algebras as the first-order model: families over
-- self-dual Boolean algebras, interpreted in Fam(SemiMod S) via the forgetful functor U.
open import Level using (0ℓ; Lift; lift) renaming (suc to lsuc)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring; BooleanAlgebra)
open import signature using (Signature; Model; PFPC[_,_,_,_])
open import categories using (Category)
open import prop using (_,_)
open import Data.Nat using (suc)
import Data.Fin as Fin
open Fin using (Fin; splitAt)
open import Data.Product using (_,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit using (⊤; tt)
import nat
import lists
import language-syntax
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

-- Self-dual Boolean algebras on first-order-data types.
module interp-boolean (Sig : Signature 0ℓ)
                      (Impl : Model PFPC[ Fam⟨𝒞⟩.cat , Fam⟨𝒞⟩-terminal , Fam⟨𝒞⟩-products , Fam⟨𝒞⟩-bool ] Sig)
   where

  open interp Sig Impl public
  open language-syntax Sig using (_⊢_; first-order-data; unit; bool; base; _[×]_; _[+]_; list)
  open BoolAlg using (SelfDualBooleanAlgebra; 𝟘; _⊕_; to-gal) public
  open Setoid using (Carrier)
  open Fam⟨𝒞⟩ using (fm)
  open Fam⟨𝒞⟩.Obj using (fam)
  open Model Impl using (⟦sort⟧)
  open lists Fam⟨𝒟⟩.cat Fam⟨𝒟⟩-terminal Fam⟨𝒟⟩-products Fam⟨𝒟⟩-exponentials Fam⟨𝒟⟩.bigCoproducts
    using (_^_)

  open FirstOrderConservativity
    (λ {X} {Y} → BoolAlg.U-full {X} {Y})
    (λ {X} {Y} {f} {g} → BoolAlg.U-faithful {X} {Y} {f} {g})
    Sig Impl public

  ty  : ∀ {τ} → first-order-data τ → (i : ⟦ τ ⟧ty .idx .Carrier) → SelfDualBooleanAlgebra
  pow : ∀ {τ} → first-order-data τ → (n : nat.ℕ) → (i : (⟦ τ ⟧ty ^ n) .idx .Carrier) → SelfDualBooleanAlgebra

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

-- Self-dual Boolean algebras on the first-order types of the language with
-- general recursive types. At μ the fibres are indexed by W-trees, so the
-- algebra at each fibre is computed by the same recursion that computes the
-- fibre, from algebras given at the polynomial's const leaves.
module interp-boolean-2 (Sig : Signature 0ℓ)
                        (Impl : Model PFPC[ Fam⟨𝒞⟩.cat , Fam⟨𝒞⟩-terminal , Fam⟨𝒞⟩-products , Fam⟨𝒞⟩-bool ] Sig)
   where

  open interp-2 Sig Impl public
  open language-syntax-2 Sig using (type; first-order; var; unit; base; _[+]_; _[×]_; μ)
  open BoolAlg using (SelfDualBooleanAlgebra; 𝟘; _⊕_; to-gal) public
  open Setoid using (Carrier)
  open Fam⟨𝒞⟩ using (fm)
  open Fam⟨𝒞⟩.Obj using (fam)
  open Model Impl using (⟦sort⟧)

  module Pm = Fam⟨𝒟⟩-μ
  module T0 = Pm.Tree {n = 0} (λ ())

  -- For each const leaf of an index-erased polynomial, an assignment of an
  -- algebra to each element of its index set. This is the only input needed to
  -- determine an algebra at every fibre of the polynomial's μ-type.
  FibAlg : ∀ {k} → Pm.Sh.Poly k → Set (lsuc 0ℓ)
  FibAlg (Pm.const S) = (x : S .Carrier) → SelfDualBooleanAlgebra
  FibAlg (Pm.var j)   = Lift (lsuc 0ℓ) ⊤
  FibAlg (P Pm.+ Q)   = FibAlg P × FibAlg Q
  FibAlg (P Pm.× Q)   = FibAlg P × FibAlg Q
  FibAlg (Pm.μ Q)     = FibAlg Q

  mutual
    SortAlg : Pm.Sort 0 → Set (lsuc 0ℓ)
    SortAlg (Pm.mkSort Q ρ) = FibAlg Q × (∀ i → CtxAlg (ρ i))

    CtxAlg : Fin 0 ⊎ Pm.Sort 0 → Set (lsuc 0ℓ)
    CtxAlg (inj₁ ())
    CtxAlg (inj₂ s) = SortAlg s

  extAlg : ∀ {k} {ρ : Fin k → Fin 0 ⊎ Pm.Sort 0} {v} →
           (∀ i → CtxAlg (ρ i)) → CtxAlg v → ∀ i → CtxAlg (Pm.extend ρ v i)
  extAlg ca va Fin.zero    = va
  extAlg ca va (Fin.suc i) = ca i

  -- Assign an algebra to the fibre at each element of a μ-type, by the same
  -- recursion that computes the fibre.
  mutual
    mu : ∀ {k} {Q : Pm.Sh.Poly (suc k)} {ρ} → SortAlg (Pm.mkSort Q ρ) → T0.W Q ρ → SelfDualBooleanAlgebra
    mu {Q = Q} {ρ = ρ} (fa , ca) (T0.sup x) =
      mu-shape Q (Pm.extend ρ (inj₂ (Pm.mkSort Q ρ))) fa (extAlg ca (fa , ca)) x

    mu-shape : ∀ {j} (Q : Pm.Sh.Poly j) (η : Fin j → Fin 0 ⊎ Pm.Sort 0) →
                 FibAlg Q → (∀ i → CtxAlg (η i)) → T0.⟦_⟧shape Q η → SelfDualBooleanAlgebra
    mu-shape (Pm.const A) η fa ca x = fa x
    mu-shape (Pm.var j)   η fa ca x = mu-el (η j) (ca j) x
    mu-shape (P Pm.+ Q) η (fp , fq) ca (inj₁ x) = mu-shape P η fp ca x
    mu-shape (P Pm.+ Q) η (fp , fq) ca (inj₂ y) = mu-shape Q η fq ca y
    mu-shape (P Pm.× Q) η (fp , fq) ca (x , y) = mu-shape P η fp ca x ⊕ mu-shape Q η fq ca y
    mu-shape (Pm.μ Q)   η fa ca x = mu (fa , ca) x

    mu-el : (r : Fin 0 ⊎ Pm.Sort 0) → CtxAlg r → T0.El r → SelfDualBooleanAlgebra
    mu-el (inj₁ ()) ca x
    mu-el (inj₂ (Pm.mkSort Q ρ)) sa x = mu sa x

  -- Algebra data for the polynomial translation of a first-order type.
  polyAlg : ∀ {Δ n} {δ : Fin Δ → Fam⟨𝒟⟩.Obj} {τ : type (n Data.Nat.+ Δ)} → first-order τ →
            (∀ j (x : δ j .idx .Carrier) → SelfDualBooleanAlgebra) → FibAlg Pm.∣ as-poly {Δ} {n} τ δ ∣
  polyAlg {n = n} (var i) δᵃ with splitAt n i
  ... | inj₁ k = lift tt
  ... | inj₂ j = δᵃ j
  polyAlg unit      δᵃ = λ x → 𝟘
  polyAlg (base s)  δᵃ = λ i → ⟦sort⟧ s .fam .fm i
  polyAlg (f [+] g) δᵃ = polyAlg f δᵃ , polyAlg g δᵃ
  polyAlg (f [×] g) δᵃ = polyAlg f δᵃ , polyAlg g δᵃ
  polyAlg (μ f)     δᵃ = polyAlg f δᵃ

  -- Self-dual Boolean algebra at each fibre of a first-order type's interpretation.
  ty : ∀ {Δ} {δ : Fin Δ → Fam⟨𝒟⟩.Obj} {τ : type Δ} → first-order τ →
       (∀ j (x : δ j .idx .Carrier) → SelfDualBooleanAlgebra) →
       (i : ⟦ τ ⟧ty δ .idx .Carrier) → SelfDualBooleanAlgebra
  ty (var i)   δᵃ x        = δᵃ i x
  ty unit      δᵃ x        = 𝟘
  ty (base s)  δᵃ i        = ⟦sort⟧ s .fam .fm i
  ty (f [+] g) δᵃ (inj₁ i) = ty f δᵃ i
  ty (f [+] g) δᵃ (inj₂ j) = ty g δᵃ j
  ty (f [×] g) δᵃ (i , j)  = ty f δᵃ i ⊕ ty g δᵃ j
  ty (μ f)     δᵃ t        = mu (polyAlg f δᵃ , (λ ())) t

  -- Closed types have no environment to pin down.
  ty₀ : ∀ {τ : type 0} → first-order τ → (i : ⟦ τ ⟧ty (λ ()) .idx .Carrier) → SelfDualBooleanAlgebra
  ty₀ fo = ty {Δ = 0} {δ = λ ()} fo (λ ())
