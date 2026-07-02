{-# OPTIONS --postfix-projections --prop --safe #-}

open import Level using (0ℓ; suc)
open import prop-setoid using (Setoid; IsEquivalence)
open import categories using (Category; HasTerminal; IsTerminal)
open import commutative-semiring using (CommutativeSemiring)
open import cmon-enriched using (CMonEnriched; Biproduct)
open import commutative-monoid using (CommutativeMonoid)
open import functor using (Functor)
import matrix-new
import semimodule

-- Category SDSemiMod of self-dual semimodules and linear maps.
module sd-semimodule {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A) where

module SM = semimodule S
open SM using (SelfDual; 𝟘-sd; ⊕-sd; _⇒_; _≈m_; id; _∘_)
open SelfDual

cat : Category (suc 0ℓ) 0ℓ 0ℓ
cat .Category.obj = SelfDual
cat .Category._⇒_ X Y = X .obj ⇒ Y .obj
cat .Category._≈_ = _≈m_
cat .Category.isEquiv = SM.cat .Category.isEquiv
cat .Category.id X = id (X .obj)
cat .Category._∘_ = _∘_
cat .Category.∘-cong = SM.cat .Category.∘-cong
cat .Category.id-left = SM.cat .Category.id-left
cat .Category.id-right = SM.cat .Category.id-right
cat .Category.assoc = SM.cat .Category.assoc

open CMonEnriched SM.cmon-enriched
  using (homCM; εm; _+m_; comp-bilinear₁; comp-bilinear₂; comp-bilinear-ε₁; comp-bilinear-ε₂)
open CommutativeMonoid

cmon-enriched : CMonEnriched cat
cmon-enriched .CMonEnriched.homCM X Y .ε = εm
cmon-enriched .CMonEnriched.homCM X Y ._+_ = _+m_
cmon-enriched .CMonEnriched.homCM X Y .+-cong = homCM _ _ .+-cong
cmon-enriched .CMonEnriched.homCM X Y .+-lunit = homCM _ _ .+-lunit
cmon-enriched .CMonEnriched.homCM X Y .+-assoc = homCM _ _ .+-assoc
cmon-enriched .CMonEnriched.homCM X Y .+-comm = homCM _ _ .+-comm
cmon-enriched .CMonEnriched.comp-bilinear₁ = comp-bilinear₁
cmon-enriched .CMonEnriched.comp-bilinear₂ = comp-bilinear₂
cmon-enriched .CMonEnriched.comp-bilinear-ε₁ = comp-bilinear-ε₁
cmon-enriched .CMonEnriched.comp-bilinear-ε₂ = comp-bilinear-ε₂

terminal : HasTerminal cat
terminal .HasTerminal.witness = 𝟘-sd
terminal .HasTerminal.is-terminal .IsTerminal.to-terminal {X} =
  SM.terminal .HasTerminal.is-terminal .IsTerminal.to-terminal {X .obj}
terminal .HasTerminal.is-terminal .IsTerminal.to-terminal-ext =
  SM.terminal .HasTerminal.is-terminal .IsTerminal.to-terminal-ext

biproduct : ∀ X Y → Biproduct cmon-enriched X Y
biproduct X Y .Biproduct.prod = ⊕-sd X Y
biproduct X Y .Biproduct.p₁ = SM.biproduct (X .obj) (Y .obj) .Biproduct.p₁
biproduct X Y .Biproduct.p₂ = SM.biproduct (X .obj) (Y .obj) .Biproduct.p₂
biproduct X Y .Biproduct.in₁ = SM.biproduct (X .obj) (Y .obj) .Biproduct.in₁
biproduct X Y .Biproduct.in₂ = SM.biproduct (X .obj) (Y .obj) .Biproduct.in₂
biproduct X Y .Biproduct.id-1 = SM.biproduct (X .obj) (Y .obj) .Biproduct.id-1
biproduct X Y .Biproduct.id-2 = SM.biproduct (X .obj) (Y .obj) .Biproduct.id-2
biproduct X Y .Biproduct.zero-1 = SM.biproduct (X .obj) (Y .obj) .Biproduct.zero-1
biproduct X Y .Biproduct.zero-2 = SM.biproduct (X .obj) (Y .obj) .Biproduct.zero-2
biproduct X Y .Biproduct.id-+ = SM.biproduct (X .obj) (Y .obj) .Biproduct.id-+

-- Forgetful functor to SemiMod; full and faithful, so SDSemiMod is equivalent to the full subcategory of
-- SemiMod on the self-dualisable objects (objects for which some isomorphism to the dual exists).
U : Functor cat SM.cat
U .Functor.fobj = SelfDual.obj
U .Functor.fmor f = f
U .Functor.fmor-cong f₁≈f₂ = f₁≈f₂
U .Functor.fmor-id = SM.cat .Category.isEquiv .IsEquivalence.refl
U .Functor.fmor-comp f g = SM.cat .Category.isEquiv .IsEquivalence.refl

-- The embedding Mat(S) ↪ SemiMod(S) factors through SDSemiMod(S) as U ∘ F; each free semimodule carries the
-- self-duality induced by the dot product.
module Mat = matrix-new.Mat S
open matrix-new.Embedding S using (fobj-sd) renaming (F to 𝓕)

F : Functor Mat.cat cat
F .Functor.fobj = fobj-sd
F .Functor.fmor = 𝓕 .Functor.fmor
F .Functor.fmor-cong = 𝓕 .Functor.fmor-cong
F .Functor.fmor-id = 𝓕 .Functor.fmor-id
F .Functor.fmor-comp = 𝓕 .Functor.fmor-comp
