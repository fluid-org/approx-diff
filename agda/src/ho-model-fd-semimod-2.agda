{-# OPTIONS --postfix-projections --prop --safe #-}

-- As ho-model-fd-semimod, but the source is FDSemiMod₂ (Data.Vec carriers).
module ho-model-fd-semimod-2 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat using () renaming (_+_ to _+ℕ_)
import Data.Vec as V
open V using (_++_; _∷_)
open import Data.Product using (_,_)
open import prop using (_,_; proj₁; proj₂)
open import prop-setoid using (Setoid; IsEquivalence)
open import commutative-monoid using (CommutativeMonoid)
open import commutative-semiring using (CommutativeSemiring)
open import categories using (Category)
open import functor using (Functor)
import fd-semimodule-2
import semimodule
import two
import ho-model
import finite-product-functor

module _ {o} {A : Setoid o o} (S : CommutativeSemiring A) where

  private
    module FD = fd-semimodule-2.FDSemiMod₂ S
    module SM = semimodule.SemiMod S
  open SM
  open SM.SemiModule
  open SM._⇒_
  open Category SM.cat using (IsIso)

  ----------------------------------------------------------------------------
  -- Object part: Sⁿ as a semimodule, with Vec n's (Data.Vec) structure.

  ⟦_⟧ : ℕ → SemiModule
  ⟦ n ⟧ .carrier .Setoid.Carrier = FD.Vec n
  ⟦ n ⟧ .carrier .Setoid._≈_ = FD._≈ᵥ_
  ⟦ n ⟧ .carrier .Setoid.isEquivalence .IsEquivalence.refl = FD.≈ᵥ-refl
  ⟦ n ⟧ .carrier .Setoid.isEquivalence .IsEquivalence.sym = FD.≈ᵥ-sym
  ⟦ n ⟧ .carrier .Setoid.isEquivalence .IsEquivalence.trans = FD.≈ᵥ-trans
  ⟦ n ⟧ .+-monoid .CommutativeMonoid.ε = FD.εᵥ
  ⟦ n ⟧ .+-monoid .CommutativeMonoid._+_ = FD._+ᵥ_
  ⟦ n ⟧ .+-monoid .CommutativeMonoid.+-cong = FD.+ᵥ-cong
  ⟦ n ⟧ .+-monoid .CommutativeMonoid.+-lunit = FD.+ᵥ-lunit
  ⟦ n ⟧ .+-monoid .CommutativeMonoid.+-assoc = FD.+ᵥ-assoc
  ⟦ n ⟧ .+-monoid .CommutativeMonoid.+-comm = FD.+ᵥ-comm
  ⟦ n ⟧ .scale = FD.scale
  ⟦ n ⟧ .scale-cong = FD.scale-cong
  ⟦ n ⟧ .scale-+ᵣ = FD.scale-+ᵥ
  ⟦ n ⟧ .scale-+ₗ = FD.scale-+ₗ
  ⟦ n ⟧ .scale-· = FD.scale-·
  ⟦ n ⟧ .scale-ι = FD.scale-ι
  ⟦ n ⟧ .scale-0ₗ = FD.scale-0ₗ
  ⟦ n ⟧ .scale-0ᵣ = FD.scale-εᵥ

  ----------------------------------------------------------------------------
  -- The functor.

  F : Functor FD.cat SM.cat
  F .Functor.fobj = ⟦_⟧
  F .Functor.fmor f .func = f .FD.func
  F .Functor.fmor f .func-resp-≈ = f .FD.func-resp-≈
  F .Functor.fmor f .+-preserving = f .FD.+-preserving
  F .Functor.fmor f .ε-preserving = f .FD.ε-preserving
  F .Functor.fmor f .scale-preserving = f .FD.scale-preserving
  F .Functor.fmor-cong f₁≈f₂ = f₁≈f₂
  F .Functor.fmor-id v = FD.≈ᵥ-refl
  F .Functor.fmor-comp f g v = FD.≈ᵥ-refl

  module FPF = finite-product-functor F

  ----------------------------------------------------------------------------
  -- Terminal preservation: ⟦ 0 ⟧ (the one-point Vec 0) is isomorphic to 𝟘.

  term-inv : 𝟘 ⇒ ⟦ 0 ⟧
  term-inv .func _ = FD.εᵥ
  term-inv .func-resp-≈ _ = FD.≈ᵥ-refl
  term-inv .+-preserving = FD.≈ᵥ-refl
  term-inv .ε-preserving = FD.≈ᵥ-refl
  term-inv .scale-preserving = FD.≈ᵥ-refl

  F-preserve-terminal : FPF.preserve-chosen-terminal FD.terminal SM.terminal
  F-preserve-terminal .IsIso.inverse = term-inv
  F-preserve-terminal .IsIso.f∘inverse≈id _ = _
  F-preserve-terminal .IsIso.inverse∘f≈id v = FD.[]-≈ᵥ v

  ----------------------------------------------------------------------------
  -- Product preservation: ⟦ m + n ⟧ ≅ ⟦ m ⟧ ⊕ ⟦ n ⟧, the inverse being _++_.

  combine : ∀ {m n} → (⟦ m ⟧ ⊕ ⟦ n ⟧) ⇒ ⟦ m +ℕ n ⟧
  combine .func (u , w) = u ++ w
  combine .func-resp-≈ (u≈ , w≈) = FD.++-cong u≈ w≈
  combine {m} {n} .+-preserving {u , w} {u' , w'} = FD.++-+ᵥ {u = u} {u'} {w} {w'}
  combine {m} {n} .ε-preserving = FD.++-εᵥ {m} {n}
  combine {m} {n} .scale-preserving {a} {u , w} = FD.≈ᵥ-sym (FD.++-scale {u = u} {w})

  -- combine ∘ fwd ≈ id, by recursion on the split point.
  combine-fwd : ∀ m {n} {v : FD.Vec (m +ℕ n)} →
                ((FD.vtake m v FD.+ᵥ FD.εᵥ) ++ (FD.εᵥ FD.+ᵥ FD.vdrop m v)) FD.≈ᵥ v
  combine-fwd zero                    = FD.+ᵥ-lunit
  combine-fwd (suc m) {n} {v = x ∷ v} = FD.trans FD.+-comm FD.+-lunit , combine-fwd m {n}

  F-preserve-products : FPF.preserve-chosen-products FD.products SM.products
  F-preserve-products {m} {n} .IsIso.inverse = combine {m} {n}
  F-preserve-products {m} {n} .IsIso.f∘inverse≈id (u , w) .proj₁ =
    FD.≈ᵥ-trans (FD.+ᵥ-cong (FD.vtake-++ {m} {n} {u} {w}) FD.≈ᵥ-refl)
      FD.+ᵥ-runit
  F-preserve-products {m} {n} .IsIso.f∘inverse≈id (u , w) .proj₂ =
    FD.≈ᵥ-trans (FD.+ᵥ-cong FD.≈ᵥ-refl (FD.vdrop-++ {m} {n} {u} {w}))
      FD.+ᵥ-lunit
  F-preserve-products {m} {n} .IsIso.inverse∘f≈id v = combine-fwd m {n}

------------------------------------------------------------------------------
-- The higher-order model: Fam(FDSemiMod₂ Two) interpreted in Fam(SemiMod Two).

module FD = fd-semimodule-2.FDSemiMod₂ two.semiring
module SM = semimodule.SemiMod two.semiring

open ho-model.Interpretation
  FD.cat FD.terminal FD.products
  SM.cat SM.cmon SM.limits SM.terminal SM.biproduct
  (F two.semiring)
  (F-preserve-terminal two.semiring)
  (λ {X} {Y} → F-preserve-products two.semiring {X} {Y})
  public
