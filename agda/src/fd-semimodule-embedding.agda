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
-- functor F : 𝒞 → 𝒟 for the higher-order model.  The source is kept FD-qualified
-- throughout; the target SemiMod is opened, so its record fields are unqualified.
module _ {o} {A : Setoid o o} (S : CommutativeSemiring A) where

  private
    module FD = fd-semimodule.FDSemiMod S
    module SM = semimodule.SemiMod S
  open SM
  open SM.SemiModule
  open SM._⇒_
  open Category SM.cat using (IsIso)

  ----------------------------------------------------------------------------
  -- Object part: Sⁿ as a semimodule, with the pointwise structure of Vec n.

  ⟦_⟧ : ℕ → SemiModule
  ⟦ n ⟧ .carrier .Setoid.Carrier = FD.Vec n
  ⟦ n ⟧ .carrier .Setoid._≈_ = FD._≈ᵥ_
  ⟦ n ⟧ .carrier .Setoid.isEquivalence .IsEquivalence.refl i = FD.refl
  ⟦ n ⟧ .carrier .Setoid.isEquivalence .IsEquivalence.sym u≈v i = FD.sym (u≈v i)
  ⟦ n ⟧ .carrier .Setoid.isEquivalence .IsEquivalence.trans u≈v v≈w i = FD.trans (u≈v i) (v≈w i)
  ⟦ n ⟧ .+-monoid .CommutativeMonoid.ε = FD.εᵥ
  ⟦ n ⟧ .+-monoid .CommutativeMonoid._+_ = FD._+ᵥ_
  ⟦ n ⟧ .+-monoid .CommutativeMonoid.+-cong u≈ v≈ i = FD.+-cong (u≈ i) (v≈ i)
  ⟦ n ⟧ .+-monoid .CommutativeMonoid.+-lunit i = FD.+-lunit
  ⟦ n ⟧ .+-monoid .CommutativeMonoid.+-assoc i = FD.+-assoc
  ⟦ n ⟧ .+-monoid .CommutativeMonoid.+-comm i = FD.+-comm
  ⟦ n ⟧ .scale = FD.scale
  ⟦ n ⟧ .scale-cong a≈ u≈ i = FD.·-cong a≈ (u≈ i)
  ⟦ n ⟧ .scale-+ᵣ i = FD.·-+-distribₗ
  ⟦ n ⟧ .scale-+ₗ i = FD.·-+-distribᵣ
  ⟦ n ⟧ .scale-· i = FD.·-assoc
  ⟦ n ⟧ .scale-ι i = FD.·-lunit
  ⟦ n ⟧ .scale-0ₗ i = FD.ε-annihilₗ
  ⟦ n ⟧ .scale-0ᵣ i = FD.ε-annihilᵣ

  ----------------------------------------------------------------------------
  -- The functor.  An FDSemiMod morphism's fields are exactly a SemiMod
  -- morphism's, since ⟦ n ⟧'s structure is Vec's pointwise structure.

  F : Functor FD.cat SM.cat
  F .Functor.fobj = ⟦_⟧
  F .Functor.fmor f .func = f .FD.func
  F .Functor.fmor f .func-resp-≈ = f .FD.func-resp-≈
  F .Functor.fmor f .+-preserving = f .FD.+-preserving
  F .Functor.fmor f .ε-preserving = f .FD.ε-preserving
  F .Functor.fmor f .scale-preserving = f .FD.scale-preserving
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

  -- Terminal preservation: ⟦ 0 ⟧ (the one-point Vec 0) is isomorphic to 𝟘.
  term-inv : 𝟘 ⇒ ⟦ 0 ⟧
  term-inv .func _ ()
  term-inv .func-resp-≈ _ ()
  term-inv .+-preserving ()
  term-inv .ε-preserving ()
  term-inv .scale-preserving ()

  F-preserve-terminal : FPF.preserve-chosen-terminal FD.terminal SM.terminal
  F-preserve-terminal .IsIso.inverse = term-inv
  F-preserve-terminal .IsIso.f∘inverse≈id _ = _
  F-preserve-terminal .IsIso.inverse∘f≈id v ()

  -- The inverse: combine a pair of vectors into one over m + n.
  combine : ∀ {m n} → (⟦ m ⟧ ⊕ ⟦ n ⟧) ⇒ ⟦ m +ℕ n ⟧
  combine {m} .func (u , w) k = [ u , w ] (splitAt m k)
  combine {m} .func-resp-≈ (u≈ , w≈) k with splitAt m k
  ... | inj₁ i = u≈ i
  ... | inj₂ j = w≈ j
  combine {m} .+-preserving k with splitAt m k
  ... | inj₁ i = FD.refl
  ... | inj₂ j = FD.refl
  combine {m} .ε-preserving k with splitAt m k
  ... | inj₁ i = FD.refl
  ... | inj₂ j = FD.refl
  combine {m} .scale-preserving k with splitAt m k
  ... | inj₁ i = FD.refl
  ... | inj₂ j = FD.refl

  F-preserve-products : FPF.preserve-chosen-products FD.products SM.products
  F-preserve-products {m} {n} .IsIso.inverse = combine {m} {n}
  F-preserve-products {m} {n} .IsIso.f∘inverse≈id (u , w) .proj₁ i
    rewrite splitAt-↑ˡ m i n = FD.trans FD.+-comm FD.+-lunit
  F-preserve-products {m} {n} .IsIso.f∘inverse≈id (u , w) .proj₂ j
    rewrite splitAt-↑ʳ m n j = FD.+-lunit
  F-preserve-products {m} {n} .IsIso.inverse∘f≈id v k with splitAt m k in eq
  ... | inj₁ i rewrite ≡-trans (≡-sym (join-splitAt m n k)) (cong (join m n) eq) = FD.trans FD.+-comm FD.+-lunit
  ... | inj₂ j rewrite ≡-trans (≡-sym (join-splitAt m n k)) (cong (join m n) eq) = FD.+-lunit
