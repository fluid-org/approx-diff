{-# OPTIONS --postfix-projections --prop --safe #-}

open import Level using (0ℓ; suc)
open import prop-setoid using (Setoid; IsEquivalence)
open import categories using (Category; HasTerminal; IsTerminal; HasInitial; IsInitial; HasProducts)
open import commutative-semiring using (CommutativeSemiring)
open import cmon-enriched using (CMonEnriched; Biproduct; biproducts→products)
open import commutative-monoid using (CommutativeMonoid)
open import functor using (Functor)
import finite-product-functor
import matrix-new
import semimodule

-- Category SDSemiMod of self-dual semimodules and linear maps.
module sd-semimodule {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A) where

module SemiMod = semimodule S
open SemiMod public using (SelfDual)
open SemiMod using (𝟘-sd; ⊕-sd; 𝕀-sd; _⇒_; _≈m_; id; _∘_)
open SelfDual

-- The scalars as a one-dimensional object, the trivial object, and the biproduct of objects.
𝕀 : SelfDual
𝕀 = 𝕀-sd

𝟘 : SelfDual
𝟘 = 𝟘-sd

_⊕_ : SelfDual → SelfDual → SelfDual
_⊕_ = ⊕-sd

cat : Category (suc 0ℓ) 0ℓ 0ℓ
cat .Category.obj = SelfDual
cat .Category._⇒_ X Y = X .obj ⇒ Y .obj
cat .Category._≈_ = _≈m_
cat .Category.isEquiv = SemiMod.cat .Category.isEquiv
cat .Category.id X = id (X .obj)
cat .Category._∘_ = _∘_
cat .Category.∘-cong = SemiMod.cat .Category.∘-cong
cat .Category.id-left = SemiMod.cat .Category.id-left
cat .Category.id-right = SemiMod.cat .Category.id-right
cat .Category.assoc = SemiMod.cat .Category.assoc

open CMonEnriched SemiMod.cmon-enriched
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
terminal .HasTerminal.witness = 𝟘
terminal .HasTerminal.is-terminal .IsTerminal.to-terminal {X} =
  SemiMod.terminal .HasTerminal.is-terminal .IsTerminal.to-terminal {X .obj}
terminal .HasTerminal.is-terminal .IsTerminal.to-terminal-ext =
  SemiMod.terminal .HasTerminal.is-terminal .IsTerminal.to-terminal-ext

biproduct : ∀ X Y → Biproduct cmon-enriched X Y
biproduct X Y .Biproduct.prod = X ⊕ Y
biproduct X Y .Biproduct.p₁ = SemiMod.biproduct (X .obj) (Y .obj) .Biproduct.p₁
biproduct X Y .Biproduct.p₂ = SemiMod.biproduct (X .obj) (Y .obj) .Biproduct.p₂
biproduct X Y .Biproduct.in₁ = SemiMod.biproduct (X .obj) (Y .obj) .Biproduct.in₁
biproduct X Y .Biproduct.in₂ = SemiMod.biproduct (X .obj) (Y .obj) .Biproduct.in₂
biproduct X Y .Biproduct.id-1 = SemiMod.biproduct (X .obj) (Y .obj) .Biproduct.id-1
biproduct X Y .Biproduct.id-2 = SemiMod.biproduct (X .obj) (Y .obj) .Biproduct.id-2
biproduct X Y .Biproduct.zero-1 = SemiMod.biproduct (X .obj) (Y .obj) .Biproduct.zero-1
biproduct X Y .Biproduct.zero-2 = SemiMod.biproduct (X .obj) (Y .obj) .Biproduct.zero-2
biproduct X Y .Biproduct.id-+ = SemiMod.biproduct (X .obj) (Y .obj) .Biproduct.id-+

products : HasProducts cat
products = biproducts→products cmon-enriched biproduct

-- Forgetful functor to SemiMod; full and faithful, so SDSemiMod is equivalent to the full subcategory of
-- SemiMod on the self-dualisable objects (objects for which some isomorphism to the dual exists).
U : Functor cat SemiMod.cat
U .Functor.fobj = SelfDual.obj
U .Functor.fmor f = f
U .Functor.fmor-cong f₁≈f₂ = f₁≈f₂
U .Functor.fmor-id = SemiMod.cat .Category.isEquiv .IsEquivalence.refl
U .Functor.fmor-comp f g = SemiMod.cat .Category.isEquiv .IsEquivalence.refl

-- U preserves the chosen terminal and products, as required for the FO model.
private
  SemiMod-products : HasProducts SemiMod.cat
  SemiMod-products = biproducts→products SemiMod.cmon-enriched SemiMod.biproduct

open Category SemiMod.cat using (IsIso; ≈-refl; ≈-trans; ≈-sym; id-left; id-right; ∘-cong)
open IsTerminal (SemiMod.terminal .HasTerminal.is-terminal) using (to-terminal; to-terminal-unique)
open HasProducts SemiMod-products using (pair; p₁; p₂; pair-natural; pair-ext)
open finite-product-functor U using (preserve-chosen-terminal; preserve-chosen-products)

U-preserve-terminal : preserve-chosen-terminal terminal SemiMod.terminal
U-preserve-terminal .IsIso.inverse = to-terminal
U-preserve-terminal .IsIso.f∘inverse≈id = to-terminal-unique _ _
U-preserve-terminal .IsIso.inverse∘f≈id = to-terminal-unique _ _

U-preserve-products : preserve-chosen-products products SemiMod-products
U-preserve-products {X} {Y} .IsIso.inverse = id ((X .obj) SemiMod.⊕ (Y .obj))
U-preserve-products {X} {Y} .IsIso.f∘inverse≈id =
  ≈-trans (pair-natural (id ((X .obj) SemiMod.⊕ (Y .obj))) p₁ p₂)
    (pair-ext (id ((X .obj) SemiMod.⊕ (Y .obj))))
U-preserve-products {X} {Y} .IsIso.inverse∘f≈id = ≈-trans id-left pair-p≈id
  where
    pair-p≈id : pair (p₁ {X .obj} {Y .obj}) (p₂ {X .obj} {Y .obj}) ≈m id ((X .obj) SemiMod.⊕ (Y .obj))
    pair-p≈id =
      ≈-trans (≈-sym id-right)
        (≈-trans (pair-natural (id ((X .obj) SemiMod.⊕ (Y .obj))) p₁ p₂)
          (pair-ext (id ((X .obj) SemiMod.⊕ (Y .obj)))))

-- 𝟘 is also initial: any map out of it is the zero map, since id on 𝟘 is the zero map.
initial : HasInitial cat
initial .HasInitial.witness = 𝟘
initial .HasInitial.is-initial .IsInitial.from-initial = εm
initial .HasInitial.is-initial .IsInitial.from-initial-ext f =
  ≈-sym (≈-trans (≈-sym id-right)
    (≈-trans (∘-cong (≈-refl {f = f}) (to-terminal-unique (id (𝟘 .obj)) εm))
      (comp-bilinear-ε₂ f)))

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
