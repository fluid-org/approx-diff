{-# OPTIONS --postfix-projections --prop --safe #-}

-- As ho-model-fd-semimod, but the source is FDSemiMod₂ (Data.Vec carriers) and
-- the target is the (coauthor's) category of all S-semimodules.
module ho-model-fd-semimod-2 where

open import Level using (0ℓ)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat using () renaming (_+_ to _+ℕ_)
import Data.Vec as V
open V using (_++_; _∷_; [])
open import Data.Product using (_,_)
open import prop using (_,_; proj₁; proj₂; tt)
open import prop-setoid using (Setoid; IsEquivalence) renaming (_⇒_ to _⇒s_; _≃m_ to _≈s_)
open import commutative-monoid using (CommutativeMonoid)
open import commutative-semiring using (CommutativeSemiring)
open import categories using (Category)
open import cmon-enriched using (biproducts→products)
open import functor using (Functor)
import fd-semimodule-2
import semimodule
import two
import ho-model
import finite-product-functor

module _ {o} {A : Setoid o o} (S : CommutativeSemiring A) where

  private
    module FD = fd-semimodule-2.FDSemiMod₂ S
    module SM = semimodule {o} {o} S
  open SM
  open SM._⇒_
  open SM._≈m_
  open Category SM.cat using (IsIso; Iso-trans; Iso-sym)

  ----------------------------------------------------------------------------
  -- Object part: Sⁿ as a semimodule, with Vec n's (Data.Vec) structure.

  ⟦_⟧ : ℕ → Semimodule
  ⟦ n ⟧ .Semimodule.setoid .Setoid.Carrier = FD.Vec n
  ⟦ n ⟧ .Semimodule.setoid .Setoid._≈_ = FD._≈ᵥ_
  ⟦ n ⟧ .Semimodule.setoid .Setoid.isEquivalence .IsEquivalence.refl = FD.≈ᵥ-refl
  ⟦ n ⟧ .Semimodule.setoid .Setoid.isEquivalence .IsEquivalence.sym = FD.≈ᵥ-sym
  ⟦ n ⟧ .Semimodule.setoid .Setoid.isEquivalence .IsEquivalence.trans = FD.≈ᵥ-trans
  ⟦ n ⟧ .Semimodule.additive .CommutativeMonoid.ε = FD.εᵥ
  ⟦ n ⟧ .Semimodule.additive .CommutativeMonoid._+_ = FD._+ᵥ_
  ⟦ n ⟧ .Semimodule.additive .CommutativeMonoid.+-cong = FD.+ᵥ-cong
  ⟦ n ⟧ .Semimodule.additive .CommutativeMonoid.+-lunit = FD.+ᵥ-lunit
  ⟦ n ⟧ .Semimodule.additive .CommutativeMonoid.+-assoc = FD.+ᵥ-assoc
  ⟦ n ⟧ .Semimodule.additive .CommutativeMonoid.+-comm = FD.+ᵥ-comm
  ⟦ n ⟧ .Semimodule._·_ = FD.scale
  ⟦ n ⟧ .Semimodule.·-cong = FD.scale-cong
  ⟦ n ⟧ .Semimodule.·-mul = FD.scale-·
  ⟦ n ⟧ .Semimodule.·-unit = FD.scale-ι
  ⟦ n ⟧ .Semimodule.+-distribʳ = FD.scale-+ₗ
  ⟦ n ⟧ .Semimodule.+-distribˡ = FD.scale-+ᵥ
  ⟦ n ⟧ .Semimodule.zero-distribʳ = FD.scale-0ₗ
  ⟦ n ⟧ .Semimodule.zero-distribˡ = FD.scale-εᵥ

  ----------------------------------------------------------------------------
  -- The functor.

  F : Functor FD.cat SM.cat
  F .Functor.fobj = ⟦_⟧
  F .Functor.fmor f .*→* ._⇒s_.func = f .FD.func
  F .Functor.fmor f .*→* ._⇒s_.func-resp-≈ = f .FD.func-resp-≈
  F .Functor.fmor f .preserve-ze = f .FD.ε-preserving
  F .Functor.fmor f .preserve-+ = f .FD.+-preserving
  F .Functor.fmor f .preserve-· = f .FD.scale-preserving
  F .Functor.fmor-cong {f₂ = f₂} f₁≈f₂ .*≈* ._≈s_.func-eq u≈v =
    FD.≈ᵥ-trans (f₁≈f₂ _) (f₂ .FD.func-resp-≈ u≈v)
  F .Functor.fmor-id .*≈* ._≈s_.func-eq u≈v = u≈v
  F .Functor.fmor-comp f g .*≈* ._≈s_.func-eq u≈v =
    f .FD.func-resp-≈ (g .FD.func-resp-≈ u≈v)

  module FPF = finite-product-functor F

  ----------------------------------------------------------------------------
  -- Terminal preservation: ⟦ 0 ⟧ (the one-point Vec 0) is isomorphic to 𝟘.

  term-inv : 𝟘 ⇒ ⟦ 0 ⟧
  term-inv .*→* ._⇒s_.func _ = FD.εᵥ
  term-inv .*→* ._⇒s_.func-resp-≈ _ = FD.≈ᵥ-refl
  term-inv .preserve-ze = FD.≈ᵥ-refl
  term-inv .preserve-+ = FD.≈ᵥ-refl
  term-inv .preserve-· = FD.≈ᵥ-refl

  F-preserve-terminal : FPF.preserve-chosen-terminal FD.terminal SM.terminal
  F-preserve-terminal .IsIso.inverse = term-inv
  F-preserve-terminal .IsIso.f∘inverse≈id .*≈* ._≈s_.func-eq _ = tt
  F-preserve-terminal .IsIso.inverse∘f≈id .*≈* ._≈s_.func-eq {_} {v} _ = FD.[]-≈ᵥ v

  ----------------------------------------------------------------------------
  -- Product preservation: ⟦ m + n ⟧ ≅ ⟦ m ⟧ ⊕ ⟦ n ⟧, the inverse being _++_.

  combine : ∀ {m n} → (⟦ m ⟧ ⊕ ⟦ n ⟧) ⇒ ⟦ m +ℕ n ⟧
  combine .*→* ._⇒s_.func (u , w) = u ++ w
  combine .*→* ._⇒s_.func-resp-≈ (u≈ , w≈) = FD.++-cong u≈ w≈
  combine {m} {n} .preserve-ze = FD.++-εᵥ {m} {n}
  combine {m} {n} .preserve-+ {u , w} {u' , w'} = FD.++-+ᵥ {u = u} {u'} {w} {w'}
  combine {m} {n} .preserve-· {a} {u , w} = FD.≈ᵥ-sym (FD.++-scale {u = u} {w})

  -- combine ∘ fwd ≈ id, by recursion on the split point.  The biproduct-derived
  -- pairing adds εᵥ on each side, hence the +ᵥ εᵥ / εᵥ +ᵥ terms.
  combine-fwd : ∀ m {n} {v : FD.Vec (m +ℕ n)} →
                ((FD.vtake m v FD.+ᵥ FD.εᵥ) ++ (FD.εᵥ FD.+ᵥ FD.vdrop m v)) FD.≈ᵥ v
  combine-fwd zero                    = FD.+ᵥ-lunit
  combine-fwd (suc m) {n} {v = x ∷ v} = FD.trans FD.+-comm FD.+-lunit , combine-fwd m {n}

  F-preserve-products : FPF.preserve-chosen-products FD.products
                          (biproducts→products SM.cmon-enriched SM.biproduct)
  F-preserve-products {m} {n} .IsIso.inverse = combine {m} {n}
  F-preserve-products {m} {n} .IsIso.f∘inverse≈id .*≈* ._≈s_.func-eq {u₁ , w₁} {u₂ , w₂} (u≈ , w≈) =
    FD.≈ᵥ-trans (FD.+ᵥ-cong (FD.vtake-++ {m} {n} {u₁} {w₁}) FD.≈ᵥ-refl) (FD.≈ᵥ-trans FD.+ᵥ-runit u≈) ,
    FD.≈ᵥ-trans (FD.+ᵥ-cong FD.≈ᵥ-refl (FD.vdrop-++ {m} {n} {u₁} {w₁})) (FD.≈ᵥ-trans FD.+ᵥ-lunit w≈)
  F-preserve-products {m} {n} .IsIso.inverse∘f≈id .*≈* ._≈s_.func-eq {v} v≈ =
    FD.≈ᵥ-trans (combine-fwd m {n} {v}) v≈

------------------------------------------------------------------------------
-- The higher-order model: Fam(FDSemiMod₂ Two) interpreted in Fam(SemiMod Two).

module FD = fd-semimodule-2.FDSemiMod₂ two.semiring
module SM = semimodule {0ℓ} {0ℓ} two.semiring

open ho-model.Interpretation
  FD.cat FD.terminal FD.products
  SM.cat SM.cmon-enriched SM.limits SM.terminal SM.biproduct
  (F two.semiring)
  (F-preserve-terminal two.semiring)
  (λ {X} {Y} → F-preserve-products two.semiring {X} {Y})
  public
