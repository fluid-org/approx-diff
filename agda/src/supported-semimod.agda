{-# OPTIONS --prop --postfix-projections --safe #-}

-- Supported semimodules carry the lifting. The lift of a semimodule with support adjoins a root:
-- its elements pair a scalar with an element whose support the scalar dominates, its support reads
-- off the scalar, the root selects a scalar over the zero element, and the injection sends an
-- element to its own support paired with itself. Every map out of a lift splits into the constant
-- read by the root and the restriction along the injection, since an element (a, u) is the sum of
-- (a, 0) and (supp u, u).
open import Level using (0ℓ)
open import Data.Product using (_,_; _×_)
open import prop using (_∧_; proj₁; proj₂; ∃ₛ) renaming (_,_ to _,ₚ_)
open import prop-setoid using (Setoid; IsEquivalence)
open import commutative-monoid using (CommutativeMonoid)
open import commutative-semiring using (CommutativeSemiring)
open import categories using (Category)
open import cmon-enriched using (CMonEnriched)
open import lifting using (Lifting)
import semimodule
import supported

module supported-semimod
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (let module S = CommutativeSemiring S)
  (∨-idem : ∀ {x} → (x S.+ x) S.≈ x)
  where

module SemiMod = semimodule S
open SemiMod using (Semimodule; 𝕀; _⇒_; _≈m_; cmon-enriched)
open Semimodule
open SemiMod._⇒_
open SemiMod._≈m_

-- Addition in any semimodule is idempotent, through the unit and the idempotent scalar sum.
mod-+-idem : ∀ (X : Semimodule) {u : X .Carrier} → X ._≈_ (X ._+_ u u) u
mod-+-idem X {u} =
  X .trans (X .+-cong (X .sym (X .·-unit)) (X .sym (X .·-unit)))
  (X .trans (X .sym (X .+-distribʳ))
  (X .trans (X .·-cong ∨-idem (X .refl)) (X .·-unit)))

hom-+-idem : ∀ {M N : Semimodule} {f : M ⇒ N} →
             CMonEnriched._+m_ cmon-enriched f f ≈m f
hom-+-idem {M} {N} {f} .*≈* .prop-setoid._≃m_.func-eq e =
  N .trans (mod-+-idem N) (f .*→* .prop-setoid._⇒_.func-resp-≈ e)

module Sup = supported cmon-enriched (λ {M} {N} {f} → hom-+-idem {M} {N} {f}) 𝕀
open Sup using (Obj; Mor; carrier; supp; mor; bound)

-- The lifted semimodule: a scalar dominating the support of an element.
module Lift-module (X : Semimodule) (σ : X ⇒ 𝕀) where

  private
    module Xm = Semimodule X

  Dominated : S.Carrier × Xm.Carrier → Prop 0ℓ
  Dominated (a , u) = (σ .func u S.+ a) S.≈ a

  Lsm : Semimodule
  Lsm .setoid .Setoid.Carrier = ∃ₛ (S.Carrier × Xm.Carrier) Dominated
  Lsm .setoid .Setoid._≈_ ((a , u) ,ₚ _) ((b , v) ,ₚ _) = (a S.≈ b) ∧ (u Xm.≈ v)
  Lsm .setoid .Setoid.isEquivalence .IsEquivalence.refl = S.refl ,ₚ Xm.refl
  Lsm .setoid .Setoid.isEquivalence .IsEquivalence.sym (p ,ₚ q) = S.sym p ,ₚ Xm.sym q
  Lsm .setoid .Setoid.isEquivalence .IsEquivalence.trans (p ,ₚ q) (p' ,ₚ q') =
    S.trans p p' ,ₚ Xm.trans q q'
  Lsm .additive .CommutativeMonoid.ε =
    (S.ε , Xm.ε) ,ₚ S.trans (S.+-cong (σ .preserve-ze) S.refl) S.+-lunit
  Lsm .additive .CommutativeMonoid._+_ ((a , u) ,ₚ p) ((b , v) ,ₚ q) =
    (a S.+ b , u Xm.+ v) ,ₚ
    S.trans (S.+-cong (σ .preserve-+) S.refl) (S.trans S.+-interchange (S.+-cong p q))
  Lsm .additive .CommutativeMonoid.+-cong (p ,ₚ q) (p' ,ₚ q') =
    S.+-cong p p' ,ₚ Xm.+-cong q q'
  Lsm .additive .CommutativeMonoid.+-lunit = S.+-lunit ,ₚ Xm.+-lunit
  Lsm .additive .CommutativeMonoid.+-assoc = S.+-assoc ,ₚ Xm.+-assoc
  Lsm .additive .CommutativeMonoid.+-comm = S.+-comm ,ₚ Xm.+-comm
  Lsm ._·_ s ((a , u) ,ₚ p) =
    (s S.· a , s Xm.· u) ,ₚ
    S.trans (S.+-cong (σ .preserve-·) S.refl)
            (S.trans (S.sym S.·-+-distribₗ) (S.·-cong S.refl p))
  Lsm .·-cong e (p ,ₚ q) = S.·-cong e p ,ₚ Xm.·-cong e q
  Lsm .·-mul = S.·-assoc ,ₚ Xm.·-mul
  Lsm .·-unit = S.·-lunit ,ₚ Xm.·-unit
  Lsm .+-distribʳ = S.·-+-distribᵣ ,ₚ Xm.+-distribʳ
  Lsm .+-distribˡ = S.·-+-distribₗ ,ₚ Xm.+-distribˡ
  Lsm .zero-distribʳ = S.ε-annihilₗ ,ₚ Xm.zero-distribʳ
  Lsm .zero-distribˡ = S.ε-annihilᵣ ,ₚ Xm.zero-distribˡ

  supp-L : Lsm ⇒ 𝕀
  supp-L .*→* .prop-setoid._⇒_.func ((a , _) ,ₚ _) = a
  supp-L .*→* .prop-setoid._⇒_.func-resp-≈ (p ,ₚ _) = p
  supp-L .preserve-ze = S.refl
  supp-L .preserve-+ = S.refl
  supp-L .preserve-· = S.refl

-- The lifting on supported objects.
𝟙s : Obj
𝟙s .carrier = 𝕀
𝟙s .supp = SemiMod.id 𝕀

Ls : Obj → Obj
Ls X .carrier = Lift-module.Lsm (X .carrier) (X .supp)
Ls X .supp = Lift-module.supp-L (X .carrier) (X .supp)

private
  module LM (X : Obj) = Lift-module (X .carrier) (X .supp)

root-s : ∀ {X} → Mor 𝟙s (Ls X)
root-s {X} .mor .*→* .prop-setoid._⇒_.func s =
  (s , Xm.ε) ,ₚ S.trans (S.+-cong (X .supp .preserve-ze) S.refl) S.+-lunit
  where module Xm = Semimodule (X .carrier)
root-s {X} .mor .*→* .prop-setoid._⇒_.func-resp-≈ e = e ,ₚ Semimodule.refl (X .carrier)
root-s {X} .mor .preserve-ze = S.refl ,ₚ Semimodule.refl (X .carrier)
root-s {X} .mor .preserve-+ =
  S.refl ,ₚ Semimodule.sym (X .carrier) (Semimodule.+-lunit (X .carrier))
root-s {X} .mor .preserve-· =
  S.refl ,ₚ Semimodule.sym (X .carrier) (Semimodule.zero-distribˡ (X .carrier))
root-s {X} .bound .*≈* .prop-setoid._≃m_.func-eq e = S.trans ∨-idem e

inj-s : ∀ {X} → Mor X (Ls X)
inj-s {X} .mor .*→* .prop-setoid._⇒_.func u = (X .supp .func u , u) ,ₚ ∨-idem
inj-s {X} .mor .*→* .prop-setoid._⇒_.func-resp-≈ e = X .supp .*→* .prop-setoid._⇒_.func-resp-≈ e ,ₚ e
inj-s {X} .mor .preserve-ze = X .supp .preserve-ze ,ₚ Semimodule.refl (X .carrier)
inj-s {X} .mor .preserve-+ = X .supp .preserve-+ ,ₚ Semimodule.refl (X .carrier)
inj-s {X} .mor .preserve-· = X .supp .preserve-· ,ₚ Semimodule.refl (X .carrier)
inj-s {X} .bound .*≈* .prop-setoid._≃m_.func-eq e =
  S.trans ∨-idem (X .supp .*→* .prop-setoid._⇒_.func-resp-≈ e)

affine-s : ∀ {X C} → Mor 𝟙s C → Mor X C → Mor (Ls X) C
affine-s {X} {C} c M .mor .*→* .prop-setoid._⇒_.func ((a , u) ,ₚ _) =
  Cm._+_ (c .mor .func a) (M .mor .func u)
  where module Cm = Semimodule (C .carrier)
affine-s {X} {C} c M .mor .*→* .prop-setoid._⇒_.func-resp-≈ (p ,ₚ q) =
  Semimodule.+-cong (C .carrier)
    (c .mor .*→* .prop-setoid._⇒_.func-resp-≈ p)
    (M .mor .*→* .prop-setoid._⇒_.func-resp-≈ q)
affine-s {X} {C} c M .mor .preserve-ze =
  Cm.trans (Cm.+-cong (c .mor .preserve-ze) (M .mor .preserve-ze)) Cm.+-lunit
  where module Cm = Semimodule (C .carrier)
affine-s {X} {C} c M .mor .preserve-+ =
  Cm.trans (Cm.+-cong (c .mor .preserve-+) (M .mor .preserve-+)) Cm.+-interchange
  where module Cm = Semimodule (C .carrier)
affine-s {X} {C} c M .mor .preserve-· =
  Cm.trans (Cm.+-cong (c .mor .preserve-·) (M .mor .preserve-·)) (Cm.sym Cm.+-distribˡ)
  where module Cm = Semimodule (C .carrier)
affine-s {X} {C} c M .bound .*≈* .prop-setoid._≃m_.func-eq {(a₁ , u₁) ,ₚ p₁} {(a₂ , u₂) ,ₚ p₂} (e₁ ,ₚ e₂) =
  S.trans (S.+-cong (C .supp .preserve-+) (S.sym p₁))
  (S.trans (S.+-cong S.+-comm S.refl)
  (S.trans S.+-interchange
  (S.trans (S.+-cong (M .bound .*≈* .prop-setoid._≃m_.func-eq e₂)
                     (c .bound .*≈* .prop-setoid._≃m_.func-eq e₁))
           p₂)))

-- The lifting instance: every map out of a lift is the sum of its behaviour on the root and on the
-- injected payload, since (a, u) = (a, 0) + (supp u, u) when the support is dominated.
supported-lifting : Lifting Sup.cat 𝟙s
supported-lifting .Lifting.L = Ls
supported-lifting .Lifting.root {X} = root-s {X}
supported-lifting .Lifting.inj {X} = inj-s {X}
supported-lifting .Lifting.affine {X} {C} = affine-s {X} {C}
supported-lifting .Lifting.affine-cong {X} {C} {c} {c'} {M} {M'} ec eM
  .*≈* .prop-setoid._≃m_.func-eq (e₁ ,ₚ e₂) =
  Semimodule.+-cong (C .carrier)
    (ec .*≈* .prop-setoid._≃m_.func-eq e₁) (eM .*≈* .prop-setoid._≃m_.func-eq e₂)
supported-lifting .Lifting.affine-root {X} {C} c M .*≈* .prop-setoid._≃m_.func-eq e =
  Cm.trans (Cm.+-cong (c .mor .*→* .prop-setoid._⇒_.func-resp-≈ e) (M .mor .preserve-ze))
           (Cm.trans Cm.+-comm Cm.+-lunit)
  where module Cm = Semimodule (C .carrier)
supported-lifting .Lifting.affine-η {X} {C} h
  .*≈* .prop-setoid._≃m_.func-eq {(a₁ , u₁) ,ₚ p₁} {(a₂ , u₂) ,ₚ p₂} (e₁ ,ₚ e₂) =
  Cm.trans (Cm.sym (h .mor .preserve-+))
           (h .mor .*→* .prop-setoid._⇒_.func-resp-≈
             (S.trans (S.+-cong e₁ (X .supp .*→* .prop-setoid._⇒_.func-resp-≈ e₂))
                      (S.trans S.+-comm p₂)
              ,ₚ Xm.trans Xm.+-lunit e₂))
  where
  module Cm = Semimodule (C .carrier)
  module Xm = Semimodule (X .carrier)
