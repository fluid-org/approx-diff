{-# OPTIONS --prop --postfix-projections --safe #-}

-- Setoid-indexed products of plain semimodules, directly: a family's product is the module of
-- coherent choice functions, pointwise. This is the dominated product without the root and without
-- the bounds, and with the root gone the pairing satisfies the extensionality law, so the products
-- are strong. The direct construction replaces the route through discrete limits, which paid for
-- functor-category plumbing on every application.
open import Level using (0ℓ)
open import prop using (_∧_) renaming (_,_ to _,ₚ_)
open import prop-setoid using (Setoid; IsEquivalence) renaming (_⇒_ to _⇒s_; _≃m_ to _≃s_)
open import commutative-semiring using (CommutativeSemiring)
open import commutative-monoid using (CommutativeMonoid)
open import categories using (Category)
open import indexed-family using (Fam; _⇒f_; _≃f_; constantFam; HasSetoidProducts)
import semimodule

module semimod-products
  {A₀ : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A₀)
  (let module S = CommutativeSemiring S)
  where

module SemiMod = semimodule S

open SemiMod using (Semimodule; _⇒_)
open Semimodule
open SemiMod._⇒_
open SemiMod._≈m_
open indexed-family.Fam
open _⇒f_
open _≃f_

module DirectΠ (A : Setoid 0ℓ 0ℓ) (P : Fam A SemiMod.cat) where

  private
    module A = Setoid A
    module Fib (x : A.Carrier) = Semimodule (P .fm x)

  -- A coherent choice of components: one element per index, respected by the transports.
  record ΠCarrier : Set where
    field
      part : (x : A.Carrier) → Fib.Carrier x
      part-natural : ∀ {x₁ x₂} (e : A._≈_ x₁ x₂) →
                     Fib._≈_ x₂ (P .subst e .func (part x₁)) (part x₂)

  open ΠCarrier

  infix 4 _≈Π_

  _≈Π_ : ΠCarrier → ΠCarrier → Prop 0ℓ
  c₁ ≈Π c₂ = ∀ x → Fib._≈_ x (c₁ .part x) (c₂ .part x)

  εΠ : ΠCarrier
  εΠ .part x = Fib.ε x
  εΠ .part-natural {x₁} {x₂} e = P .subst e .preserve-ze

  addΠ : ΠCarrier → ΠCarrier → ΠCarrier
  addΠ c₁ c₂ .part x = Fib._+_ x (c₁ .part x) (c₂ .part x)
  addΠ c₁ c₂ .part-natural {x₁} {x₂} e =
    Fib.trans x₂ (P .subst e .preserve-+)
                 (Fib.+-cong x₂ (c₁ .part-natural e) (c₂ .part-natural e))

  mulΠ : Setoid.Carrier A₀ → ΠCarrier → ΠCarrier
  mulΠ s c .part x = Fib._·_ x s (c .part x)
  mulΠ s c .part-natural {x₁} {x₂} e =
    Fib.trans x₂ (P .subst e .preserve-·) (Fib.·-cong x₂ S.refl (c .part-natural e))

  Πm : Semimodule
  Πm .setoid .Setoid.Carrier = ΠCarrier
  Πm .setoid .Setoid._≈_ = _≈Π_
  Πm .setoid .Setoid.isEquivalence .IsEquivalence.refl x = Fib.refl x
  Πm .setoid .Setoid.isEquivalence .IsEquivalence.sym e x = Fib.sym x (e x)
  Πm .setoid .Setoid.isEquivalence .IsEquivalence.trans e e' x = Fib.trans x (e x) (e' x)
  Πm .additive .CommutativeMonoid.ε = εΠ
  Πm .additive .CommutativeMonoid._+_ = addΠ
  Πm .additive .CommutativeMonoid.+-cong e e' x = Fib.+-cong x (e x) (e' x)
  Πm .additive .CommutativeMonoid.+-lunit x = Fib.+-lunit x
  Πm .additive .CommutativeMonoid.+-assoc x = Fib.+-assoc x
  Πm .additive .CommutativeMonoid.+-comm x = Fib.+-comm x
  Πm ._·_ = mulΠ
  Πm .·-cong es e x = Fib.·-cong x es (e x)
  Πm .·-mul x = Fib.·-mul x
  Πm .·-unit x = Fib.·-unit x
  Πm .+-distribʳ x = Fib.+-distribʳ x
  Πm .+-distribˡ x = Fib.+-distribˡ x
  Πm .zero-distribʳ x = Fib.zero-distribʳ x
  Πm .zero-distribˡ x = Fib.zero-distribˡ x

  evalΠs : (a : A.Carrier) → Πm ⇒ P .fm a
  evalΠs a .*→* ._⇒s_.func c = c .part a
  evalΠs a .*→* ._⇒s_.func-resp-≈ e = e a
  evalΠs a .preserve-ze = Fib.refl a
  evalΠs a .preserve-+ = Fib.refl a
  evalΠs a .preserve-· = Fib.refl a

  lambdaΠs : (x : Semimodule) (f : constantFam A SemiMod.cat x ⇒f P) → x ⇒ Πm
  lambdaΠs x f .*→* ._⇒s_.func u .part a = f .transf a .func u
  lambdaΠs x f .*→* ._⇒s_.func u .part-natural {x₁} {x₂} e =
    Fib.sym x₂ (f .natural e .*≈* ._≃s_.func-eq (Semimodule.refl x))
  lambdaΠs x f .*→* ._⇒s_.func-resp-≈ e a = f .transf a .func-resp-≈ e
  lambdaΠs x f .preserve-ze a = f .transf a .preserve-ze
  lambdaΠs x f .preserve-+ a = f .transf a .preserve-+
  lambdaΠs x f .preserve-· a = f .transf a .preserve-·

-- The strong setoid-indexed products on plain semimodules.
semimod-setoid-products : HasSetoidProducts 0ℓ 0ℓ SemiMod.cat
semimod-setoid-products .HasSetoidProducts.Π B P = DirectΠ.Πm B P
semimod-setoid-products .HasSetoidProducts.lambdaΠ {B} x P f = DirectΠ.lambdaΠs B P x f
semimod-setoid-products .HasSetoidProducts.lambdaΠ-cong {B} {x} {P} {f₁} {f₂} e
  .*≈* ._≃s_.func-eq ee a = e .transf-eq {a} .*≈* ._≃s_.func-eq ee
semimod-setoid-products .HasSetoidProducts.evalΠ {B} P a = DirectΠ.evalΠs B P a
semimod-setoid-products .HasSetoidProducts.evalΠ-cong {B} {P} {a₁} {a₂} e
  .*≈* ._≃s_.func-eq {c₁} {c₂} ep =
  Semimodule.trans (P .fm a₂) (DirectΠ.ΠCarrier.part-natural c₁ e) (ep a₂)
semimod-setoid-products .HasSetoidProducts.lambda-eval {B} {P} {x} {f} a
  .*≈* ._≃s_.func-eq e =
  f .transf a .func-resp-≈ e
semimod-setoid-products .HasSetoidProducts.lambda-ext {B} {P} {x} {f}
  .*≈* ._≃s_.func-eq e a =
  f .func-resp-≈ e a

------------------------------------------------------------------------------
-- The products restrict to the topped subcategory: the pointwise top is a coherent choice
-- because the transports are isomorphisms and the top absorbs.
module Topped (⊤-add-top : ∀ {x} → (S.ι S.+ x) S.≈ S.ι) where

  open SemiMod.Topped ⊤-add-top

  fam-mod : ∀ {A : Setoid 0ℓ 0ℓ} → Fam A cat-⊤ → Fam A SemiMod.cat
  fam-mod P .fm x = P .fm x .mod
  fam-mod P .subst = P .subst
  fam-mod P .refl* = P .refl*
  fam-mod P .trans* = P .trans*

  module DirectΠ-⊤ (A : Setoid 0ℓ 0ℓ) (P : Fam A cat-⊤) where
    private
      module A = Setoid A
      module D = DirectΠ A (fam-mod P)
      module Fib (x : A.Carrier) = Semimodule (P .fm x .mod)
    open D.ΠCarrier

    Πm-⊤ : Semimodule-⊤
    Πm-⊤ .mod = D.Πm
    Πm-⊤ .⊤m .part x = P .fm x .⊤m
    Πm-⊤ .⊤m .part-natural {x₁} {x₂} e =
      Fib.trans x₂ (P .subst e .func-resp-≈ (Fib.sym x₁ (P .fm x₁ .⊤m-absorb)))
        (Fib.trans x₂ (P .subst e .preserve-+)
          (Fib.trans x₂ (Fib.+-cong x₂ fg-elem (Fib.refl x₂))
            (Fib.trans x₂ (Fib.+-comm x₂) (P .fm x₂ .⊤m-absorb))))
      where
        fg-elem : Fib._≈_ x₂ (P .subst e .func (P .subst (A.sym e) .func (P .fm x₂ .⊤m)))
                             (P .fm x₂ .⊤m)
        fg-elem =
          Fib.trans x₂
            (Fib.sym x₂ (P .trans* e (A.sym e) .*≈* ._≃s_.func-eq (Fib.refl x₂)))
            (P .refl* .*≈* ._≃s_.func-eq (Fib.refl x₂))
    Πm-⊤ .⊤m-absorb x = P .fm x .⊤m-absorb

  semimod-setoid-products-⊤ : HasSetoidProducts 0ℓ 0ℓ cat-⊤
  semimod-setoid-products-⊤ .HasSetoidProducts.Π B P = DirectΠ-⊤.Πm-⊤ B P
  semimod-setoid-products-⊤ .HasSetoidProducts.lambdaΠ {B} x P f =
    DirectΠ.lambdaΠs B (fam-mod P) (x .mod)
      (record { transf = f .transf ; natural = f .natural })
  semimod-setoid-products-⊤ .HasSetoidProducts.lambdaΠ-cong {B} {x} {P} {f₁} {f₂} e
    .*≈* ._≃s_.func-eq ee a = e .transf-eq {a} .*≈* ._≃s_.func-eq ee
  semimod-setoid-products-⊤ .HasSetoidProducts.evalΠ {B} P a = DirectΠ.evalΠs B (fam-mod P) a
  semimod-setoid-products-⊤ .HasSetoidProducts.evalΠ-cong {B} {P} {a₁} {a₂} e
    .*≈* ._≃s_.func-eq {c₁} {c₂} ep =
    Semimodule.trans (P .fm a₂ .mod) (DirectΠ.ΠCarrier.part-natural c₁ e) (ep a₂)
  semimod-setoid-products-⊤ .HasSetoidProducts.lambda-eval {B} {P} {x} {f} a
    .*≈* ._≃s_.func-eq e =
    f .transf a .func-resp-≈ e
  semimod-setoid-products-⊤ .HasSetoidProducts.lambda-ext {B} {P} {x} {f}
    .*≈* ._≃s_.func-eq e a =
    f .func-resp-≈ e a
