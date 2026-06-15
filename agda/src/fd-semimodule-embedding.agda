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

  ----------------------------------------------------------------------------
  -- Product preservation.  The canonical map ⟦ m + n ⟧ → ⟦ m ⟧ ⊕ ⟦ n ⟧ is an
  -- iso: its inverse joins the two blocks back together (Vec splitAt/join).

  open import Data.Nat using () renaming (_+_ to _+ℕ_)
  open import Data.Fin using (splitAt; join)
  open import Data.Sum using (inj₁; inj₂; [_,_])
  open import Data.Product using (_,_)
  open import prop using (_,_; proj₁; proj₂)
  open import Data.Fin.Properties using (splitAt-↑ˡ; splitAt-↑ʳ; join-splitAt)
  open import Relation.Binary.PropositionalEquality using (cong) renaming (sym to ≡-sym; trans to ≡-trans)
  import finite-product-functor

  module FPF = finite-product-functor F

  -- The inverse: combine a pair of vectors into one over m + n.
  combine : ∀ {m n} → (⟦ m ⟧ SM.⊕ ⟦ n ⟧) SM.⇒ ⟦ m +ℕ n ⟧
  combine {m} .SM._⇒_.func (u , w) k = [ u , w ] (splitAt m k)
  combine {m} .SM._⇒_.func-resp-≈ (u≈ , w≈) k with splitAt m k
  ... | inj₁ i = u≈ i
  ... | inj₂ j = w≈ j
  combine {m} .SM._⇒_.+-preserving k with splitAt m k
  ... | inj₁ i = FD.refl
  ... | inj₂ j = FD.refl
  combine {m} .SM._⇒_.ε-preserving k with splitAt m k
  ... | inj₁ i = FD.refl
  ... | inj₂ j = FD.refl
  combine {m} .SM._⇒_.scale-preserving k with splitAt m k
  ... | inj₁ i = FD.refl
  ... | inj₂ j = FD.refl

  F-preserve-products : FPF.preserve-chosen-products FD.products SM.products
  F-preserve-products {m} {n} .Category.IsIso.inverse = combine {m} {n}
  F-preserve-products {m} {n} .Category.IsIso.f∘inverse≈id (u , w) .proj₁ i
    rewrite splitAt-↑ˡ m i n = FD.trans FD.+-comm FD.+-lunit
  F-preserve-products {m} {n} .Category.IsIso.f∘inverse≈id (u , w) .proj₂ j
    rewrite splitAt-↑ʳ m n j = FD.+-lunit
  F-preserve-products {m} {n} .Category.IsIso.inverse∘f≈id v k with splitAt m k in eq
  ... | inj₁ i rewrite ≡-trans (≡-sym (join-splitAt m n k)) (cong (join m n) eq) = FD.trans FD.+-comm FD.+-lunit
  ... | inj₂ j rewrite ≡-trans (≡-sym (join-splitAt m n k)) (cong (join m n) eq) = FD.+-lunit
