{-# OPTIONS --postfix-projections --prop --safe #-}

module fd-semimodule-embedding where

open import Data.Nat using (ℕ)
open import prop-setoid using (Setoid; IsEquivalence)
open import commutative-monoid using (CommutativeMonoid)
open import commutative-semiring using (CommutativeSemiring)
open import categories using (Category)
open import functor using (Functor)
import fd-semimodule
import semimodule

-- The inclusion of the free finitely-generated semimodules (FDSemiMod) into
-- all S-semimodules (SemiMod): Sⁿ becomes the semimodule on Vec n, and an
-- FDSemiMod morphism is already a SemiMod morphism.  This is the source-slot
-- functor F : 𝒞 → 𝒟 for the higher-order model.
module _ {o} {A : Setoid o o} (S : CommutativeSemiring A) where

  private
    module FD = fd-semimodule.FDSemiMod S
    module SM = semimodule.SemiMod S

  ----------------------------------------------------------------------------
  -- Object part: Sⁿ as a semimodule, with the pointwise structure of Vec n.

  ⟦_⟧ : ℕ → SM.SemiModule
  ⟦ n ⟧ .SM.SemiModule.carrier .Setoid.Carrier = FD.Vec n
  ⟦ n ⟧ .SM.SemiModule.carrier .Setoid._≈_ = FD._≈ᵥ_
  ⟦ n ⟧ .SM.SemiModule.carrier .Setoid.isEquivalence .IsEquivalence.refl i = FD.refl
  ⟦ n ⟧ .SM.SemiModule.carrier .Setoid.isEquivalence .IsEquivalence.sym u≈v i = FD.sym (u≈v i)
  ⟦ n ⟧ .SM.SemiModule.carrier .Setoid.isEquivalence .IsEquivalence.trans u≈v v≈w i = FD.trans (u≈v i) (v≈w i)
  ⟦ n ⟧ .SM.SemiModule.+-monoid .CommutativeMonoid.ε = FD.εᵥ
  ⟦ n ⟧ .SM.SemiModule.+-monoid .CommutativeMonoid._+_ = FD._+ᵥ_
  ⟦ n ⟧ .SM.SemiModule.+-monoid .CommutativeMonoid.+-cong u≈ v≈ i = FD.+-cong (u≈ i) (v≈ i)
  ⟦ n ⟧ .SM.SemiModule.+-monoid .CommutativeMonoid.+-lunit i = FD.+-lunit
  ⟦ n ⟧ .SM.SemiModule.+-monoid .CommutativeMonoid.+-assoc i = FD.+-assoc
  ⟦ n ⟧ .SM.SemiModule.+-monoid .CommutativeMonoid.+-comm i = FD.+-comm
  ⟦ n ⟧ .SM.SemiModule.scale = FD.scale
  ⟦ n ⟧ .SM.SemiModule.scale-cong a≈ u≈ i = FD.·-cong a≈ (u≈ i)
  ⟦ n ⟧ .SM.SemiModule.scale-+ᵣ i = FD.·-+-distribₗ
  ⟦ n ⟧ .SM.SemiModule.scale-+ₗ i = FD.·-+-distribᵣ
  ⟦ n ⟧ .SM.SemiModule.scale-· i = FD.·-assoc
  ⟦ n ⟧ .SM.SemiModule.scale-ι i = FD.·-lunit
  ⟦ n ⟧ .SM.SemiModule.scale-0ₗ i = FD.ε-annihilₗ
  ⟦ n ⟧ .SM.SemiModule.scale-0ᵣ i = FD.ε-annihilᵣ

  ----------------------------------------------------------------------------
  -- The functor.  An FDSemiMod morphism's fields are exactly a SemiMod
  -- morphism's, since ⟦ n ⟧'s structure is Vec's pointwise structure.

  F : Functor FD.cat SM.cat
  F .Functor.fobj = ⟦_⟧
  F .Functor.fmor f .SM._⇒_.func = f .FD.func
  F .Functor.fmor f .SM._⇒_.func-resp-≈ = f .FD.func-resp-≈
  F .Functor.fmor f .SM._⇒_.+-preserving = f .FD.+-preserving
  F .Functor.fmor f .SM._⇒_.ε-preserving = f .FD.ε-preserving
  F .Functor.fmor f .SM._⇒_.scale-preserving = f .FD.scale-preserving
  F .Functor.fmor-cong f₁≈f₂ = f₁≈f₂
  F .Functor.fmor-id v i = FD.refl
  F .Functor.fmor-comp f g v i = FD.refl
