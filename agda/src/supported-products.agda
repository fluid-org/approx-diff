{-# OPTIONS --prop --postfix-projections --safe #-}

-- Setoid-indexed products of supported semimodules, weakly. The product adjoins a root and admits
-- only the families whose components' supports the root dominates; its own support reads the root.
-- Projections are bounded by admission. The pairing takes the source's support as the root, one
-- choice among many, so the extensionality law fails; the functoriality laws hold because the
-- induced maps keep roots. At a one-point index this is the supported lifting's constraint, so the
-- product generalises the lifting's domination from one payload to a family of components.
open import Level using (0ℓ)
open import prop using (_∧_) renaming (_,_ to _,ₚ_)
open import prop-setoid using (Setoid; IsEquivalence) renaming (_⇒_ to _⇒s_; _≃m_ to _≃s_)
open import commutative-semiring using (CommutativeSemiring)
open import commutative-monoid using (CommutativeMonoid)
open import categories using (Category)
open import indexed-family using (Fam; _⇒f_; _≃f_; constantFam; HasWeakSetoidProducts)
import semimodule
import supported-semimod

module supported-products
  {A₀ : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A₀)
  (let module S = CommutativeSemiring S)
  (∨-idem : ∀ {x} → (x S.+ x) S.≈ x)
  where

module SemiMod = semimodule S
module SS = supported-semimod S ∨-idem

open SS.Sup using (Obj; Mor; carrier; supp; mor; bound)
open SemiMod using (Semimodule; 𝕀)
open SemiMod._⇒_
open SemiMod._≈m_
open indexed-family.Fam
open _⇒f_
open _≃f_

private
  +-inter : ∀ {a b c d} → ((a S.+ b) S.+ (c S.+ d)) S.≈ ((a S.+ c) S.+ (b S.+ d))
  +-inter =
    S.trans S.+-assoc
    (S.trans (S.+-cong S.refl (S.trans (S.sym S.+-assoc)
              (S.trans (S.+-cong S.+-comm S.refl) S.+-assoc)))
             (S.sym S.+-assoc))

module Dominated (A : Setoid 0ℓ 0ℓ) (P : Fam A SS.Sup.cat) where

  private
    module A = Setoid A
    module Fib (x : A.Carrier) = Semimodule (P .fm x .carrier)

  -- An admitted family: a root, components, their transport coherence, and the domination of every
  -- component's support by the root.
  record ΠsCarrier : Set where
    field
      root : Setoid.Carrier A₀
      part : (x : A.Carrier) → Fib.Carrier x
      part-natural : ∀ {x₁ x₂} (e : A._≈_ x₁ x₂) →
                     Fib._≈_ x₂ (P .subst e .mor .func (part x₁)) (part x₂)
      dominated : ∀ x → ((P .fm x .supp .func (part x)) S.+ root) S.≈ root

  open ΠsCarrier

  infix 4 _≈Π_

  _≈Π_ : ΠsCarrier → ΠsCarrier → Prop 0ℓ
  c₁ ≈Π c₂ = (c₁ .root S.≈ c₂ .root) ∧ (∀ x → Fib._≈_ x (c₁ .part x) (c₂ .part x))

  εΠ : ΠsCarrier
  εΠ .root = S.ε
  εΠ .part x = Fib.ε x
  εΠ .part-natural {x₁} {x₂} e = P .subst e .mor .preserve-ze
  εΠ .dominated x = S.trans (S.+-cong (P .fm x .supp .preserve-ze) S.refl) S.+-lunit

  addΠ : ΠsCarrier → ΠsCarrier → ΠsCarrier
  addΠ c₁ c₂ .root = c₁ .root S.+ c₂ .root
  addΠ c₁ c₂ .part x = Fib._+_ x (c₁ .part x) (c₂ .part x)
  addΠ c₁ c₂ .part-natural {x₁} {x₂} e =
    Fib.trans x₂ (P .subst e .mor .preserve-+)
                 (Fib.+-cong x₂ (c₁ .part-natural e) (c₂ .part-natural e))
  addΠ c₁ c₂ .dominated x =
    S.trans (S.+-cong (P .fm x .supp .preserve-+) S.refl)
    (S.trans +-inter (S.+-cong (c₁ .dominated x) (c₂ .dominated x)))

  mulΠ : Setoid.Carrier A₀ → ΠsCarrier → ΠsCarrier
  mulΠ s c .root = s S.· c .root
  mulΠ s c .part x = Fib._·_ x s (c .part x)
  mulΠ s c .part-natural {x₁} {x₂} e =
    Fib.trans x₂ (P .subst e .mor .preserve-·) (Fib.·-cong x₂ S.refl (c .part-natural e))
  mulΠ s c .dominated x =
    S.trans (S.+-cong (P .fm x .supp .preserve-·) S.refl)
    (S.trans (S.sym S.·-+-distribₗ) (S.·-cong S.refl (c .dominated x)))

  Πsm : Semimodule
  Πsm .Semimodule.setoid .Setoid.Carrier = ΠsCarrier
  Πsm .Semimodule.setoid .Setoid._≈_ = _≈Π_
  Πsm .Semimodule.setoid .Setoid.isEquivalence .IsEquivalence.refl =
    S.refl ,ₚ (λ x → Fib.refl x)
  Πsm .Semimodule.setoid .Setoid.isEquivalence .IsEquivalence.sym (er ,ₚ ep) =
    S.sym er ,ₚ (λ x → Fib.sym x (ep x))
  Πsm .Semimodule.setoid .Setoid.isEquivalence .IsEquivalence.trans (er ,ₚ ep) (er' ,ₚ ep') =
    S.trans er er' ,ₚ (λ x → Fib.trans x (ep x) (ep' x))
  Πsm .Semimodule.additive .CommutativeMonoid.ε = εΠ
  Πsm .Semimodule.additive .CommutativeMonoid._+_ = addΠ
  Πsm .Semimodule.additive .CommutativeMonoid.+-cong (er ,ₚ ep) (er' ,ₚ ep') =
    S.+-cong er er' ,ₚ (λ x → Fib.+-cong x (ep x) (ep' x))
  Πsm .Semimodule.additive .CommutativeMonoid.+-lunit =
    S.+-lunit ,ₚ (λ x → Fib.+-lunit x)
  Πsm .Semimodule.additive .CommutativeMonoid.+-assoc =
    S.+-assoc ,ₚ (λ x → Fib.+-assoc x)
  Πsm .Semimodule.additive .CommutativeMonoid.+-comm =
    S.+-comm ,ₚ (λ x → Fib.+-comm x)
  Πsm .Semimodule._·_ = mulΠ
  Πsm .Semimodule.·-cong es (er ,ₚ ep) = S.·-cong es er ,ₚ (λ x → Fib.·-cong x es (ep x))
  Πsm .Semimodule.·-mul = S.·-assoc ,ₚ (λ x → Fib.·-mul x)
  Πsm .Semimodule.·-unit = S.·-lunit ,ₚ (λ x → Fib.·-unit x)
  Πsm .Semimodule.+-distribʳ = S.·-+-distribᵣ ,ₚ (λ x → Fib.+-distribʳ x)
  Πsm .Semimodule.+-distribˡ = S.·-+-distribₗ ,ₚ (λ x → Fib.+-distribˡ x)
  Πsm .Semimodule.zero-distribʳ = S.ε-annihilₗ ,ₚ (λ x → Fib.zero-distribʳ x)
  Πsm .Semimodule.zero-distribˡ = S.ε-annihilᵣ ,ₚ (λ x → Fib.zero-distribˡ x)

  supp-Πs : SemiMod._⇒_ Πsm 𝕀
  supp-Πs .*→* ._⇒s_.func c = c .root
  supp-Πs .*→* ._⇒s_.func-resp-≈ (er ,ₚ _) = er
  supp-Πs .preserve-ze = S.refl
  supp-Πs .preserve-+ = S.refl
  supp-Πs .preserve-· = S.refl

  Πs : Obj
  Πs .carrier = Πsm
  Πs .supp = supp-Πs

  -- The projection at an index: bounded by admission.
  evalΠs : (a : A.Carrier) → Mor Πs (P .fm a)
  evalΠs a .mor .*→* ._⇒s_.func c = c .part a
  evalΠs a .mor .*→* ._⇒s_.func-resp-≈ (_ ,ₚ ep) = ep a
  evalΠs a .mor .preserve-ze = Fib.refl a
  evalΠs a .mor .preserve-+ = Fib.refl a
  evalΠs a .mor .preserve-· = Fib.refl a
  evalΠs a .bound .*≈* ._≃s_.func-eq {c₁} {c₂} (er ,ₚ ep) =
    S.trans (S.+-cong (P .fm a .supp .func-resp-≈ (ep a)) er) (c₂ .dominated a)

  evalΠs-cong : ∀ {a₁ a₂ : A.Carrier} (e : A._≈_ a₁ a₂) →
                Category._≈_ SS.Sup.cat (Category._∘_ SS.Sup.cat (P .subst e) (evalΠs a₁)) (evalΠs a₂)
  evalΠs-cong {a₁} {a₂} e .*≈* ._≃s_.func-eq {c₁} {c₂} (_ ,ₚ ep) =
    Fib.trans a₂ (c₁ .part-natural e) (ep a₂)

  -- The pairing: the source's support as the root, the cone's bounds as the domination.
  lambdaΠs : (x : Obj) (f : constantFam A SS.Sup.cat x ⇒f P) → Mor x Πs
  lambdaΠs x f .mor .*→* ._⇒s_.func u .root = x .supp .func u
  lambdaΠs x f .mor .*→* ._⇒s_.func u .part a = f .transf a .mor .func u
  lambdaΠs x f .mor .*→* ._⇒s_.func u .part-natural {x₁} {x₂} e =
    Fib.sym x₂ (f .natural e .*≈* ._≃s_.func-eq (Semimodule.refl (x .carrier)))
  lambdaΠs x f .mor .*→* ._⇒s_.func u .dominated a =
    f .transf a .bound .*≈* ._≃s_.func-eq (Semimodule.refl (x .carrier))
  lambdaΠs x f .mor .*→* ._⇒s_.func-resp-≈ e =
    x .supp .func-resp-≈ e ,ₚ (λ a → f .transf a .mor .func-resp-≈ e)
  lambdaΠs x f .mor .preserve-ze =
    x .supp .preserve-ze ,ₚ (λ a → f .transf a .mor .preserve-ze)
  lambdaΠs x f .mor .preserve-+ =
    x .supp .preserve-+ ,ₚ (λ a → f .transf a .mor .preserve-+)
  lambdaΠs x f .mor .preserve-· =
    x .supp .preserve-· ,ₚ (λ a → f .transf a .mor .preserve-·)
  lambdaΠs x f .bound .*≈* ._≃s_.func-eq {u₁} {u₂} e =
    S.trans ∨-idem (x .supp .func-resp-≈ e)

-- The weak setoid-indexed products on the supported semimodules.
supported-setoid-products : HasWeakSetoidProducts 0ℓ 0ℓ SS.Sup.cat
supported-setoid-products .HasWeakSetoidProducts.Π A P = Dominated.Πs A P
supported-setoid-products .HasWeakSetoidProducts.lambdaΠ {A} x P f = Dominated.lambdaΠs A P x f
supported-setoid-products .HasWeakSetoidProducts.lambdaΠ-cong {A} {x} {P} {f₁} {f₂} e
  .*≈* ._≃s_.func-eq ee =
  x .supp .func-resp-≈ ee ,ₚ (λ a → e .transf-eq {a} .*≈* ._≃s_.func-eq ee)
supported-setoid-products .HasWeakSetoidProducts.evalΠ {A} P a = Dominated.evalΠs A P a
supported-setoid-products .HasWeakSetoidProducts.evalΠ-cong {A} {P} {a₁} {a₂} e =
  Dominated.evalΠs-cong A P {a₁} {a₂} e
supported-setoid-products .HasWeakSetoidProducts.lambda-eval {A} {P} {x} {f} a
  .*≈* ._≃s_.func-eq e =
  f .transf a .mor .func-resp-≈ e
supported-setoid-products .HasWeakSetoidProducts.Π-map-id {A} {P}
  .*≈* ._≃s_.func-eq (er ,ₚ ep) = er ,ₚ ep
supported-setoid-products .HasWeakSetoidProducts.Π-map-comp {A} {P} {Q} {R} f g
  .*≈* ._≃s_.func-eq {c₁} {c₂} (er ,ₚ ep) =
  er ,ₚ (λ a → f .transf a .mor .func-resp-≈ (g .transf a .mor .func-resp-≈ (ep a)))
supported-setoid-products .HasWeakSetoidProducts.lambda-compose {A} {Q} {R} {x} f g
  .*≈* ._≃s_.func-eq e =
  x .supp .func-resp-≈ e ,ₚ (λ a → f .transf a .mor .func-resp-≈ (g .transf a .mor .func-resp-≈ e))
