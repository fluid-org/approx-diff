{-# OPTIONS --postfix-projections --prop --safe #-}

open import Level using (0ℓ; suc)
open import prop-setoid using (Setoid; IsEquivalence)
open import categories using (Category; HasTerminal; IsTerminal; HasInitial; IsInitial; HasProducts)
open import commutative-semiring using (CommutativeSemiring; BooleanAlgebra)
open import cmon-enriched using (CMonEnriched; Biproduct; biproducts→products)
open import commutative-monoid using (CommutativeMonoid)
open import functor using (Functor; Full; Faithful)
open import prop using (∃ₛ)
import finite-product-functor
import lattice
import semimodule
import sd-semimodule

-- Category of self-dual Boolean algebras (self-dual S-semimodules whose induced lattice is Boolean)
-- and linear maps.
module boolalg-sd-semimodule {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A) (S-boolean : BooleanAlgebra S) where

module SemiMod = semimodule S
module SDSemiMod = sd-semimodule S
open SemiMod using (_⇒_; _≈m_; id; _∘_)
open BooleanAlgebra S-boolean
open SDSemiMod.DistributiveLattices ⊤-add-top ∧-idem
  using (SelfDualDistributiveLattice; 𝕀-lattice; 𝟘-lattice; ⊕-lattice; to-conj)
open import galois using (_⇒g_; conj→gal)
open import lattice using (bounded)
open import prop using (tt; _,_)
open import Data.Product using (_,_)

-- A self-dual distributive lattice with a Boolean negation.
record SelfDualBooleanAlgebra : Set (suc 0ℓ) where
  field selfDualLat : SelfDualDistributiveLattice
  open SelfDualDistributiveLattice selfDualLat public
  field boolean : lattice.BooleanAlgebra toObj
  open lattice.BooleanAlgebra boolean public using (¬; compl-∧; compl-∨)

open SelfDualBooleanAlgebra using (obj; toObj; boolean; selfDualLat)

-- The Galois connection of f: its Tarski conjugate pair (to-conj) read as adjoints via De Morgan.
to-gal : (X Y : SelfDualBooleanAlgebra) → obj X ⇒ obj Y → bounded (toObj Y) ⇒g bounded (toObj X)
to-gal X Y f = conj→gal (boolean X) (boolean Y) (to-conj (selfDualLat X) (selfDualLat Y) f)

𝕀 : SelfDualBooleanAlgebra
𝕀 .SelfDualBooleanAlgebra.selfDualLat = 𝕀-lattice
𝕀 .SelfDualBooleanAlgebra.boolean .lattice.BooleanAlgebra.¬ = ¬
𝕀 .SelfDualBooleanAlgebra.boolean .lattice.BooleanAlgebra.compl-∧ = compl-∧
𝕀 .SelfDualBooleanAlgebra.boolean .lattice.BooleanAlgebra.compl-∨ = compl-∨

𝟘 : SelfDualBooleanAlgebra
𝟘 .SelfDualBooleanAlgebra.selfDualLat = 𝟘-lattice
𝟘 .SelfDualBooleanAlgebra.boolean .lattice.BooleanAlgebra.¬ x = x
𝟘 .SelfDualBooleanAlgebra.boolean .lattice.BooleanAlgebra.compl-∧ = tt
𝟘 .SelfDualBooleanAlgebra.boolean .lattice.BooleanAlgebra.compl-∨ = tt

_⊕_ : SelfDualBooleanAlgebra → SelfDualBooleanAlgebra → SelfDualBooleanAlgebra
(X ⊕ Y) .SelfDualBooleanAlgebra.selfDualLat = ⊕-lattice (SelfDualBooleanAlgebra.selfDualLat X) (SelfDualBooleanAlgebra.selfDualLat Y)
(X ⊕ Y) .SelfDualBooleanAlgebra.boolean .lattice.BooleanAlgebra.¬ (a , b) = SelfDualBooleanAlgebra.¬ X a , SelfDualBooleanAlgebra.¬ Y b
(X ⊕ Y) .SelfDualBooleanAlgebra.boolean .lattice.BooleanAlgebra.compl-∧ {a , b} = SelfDualBooleanAlgebra.compl-∧ X , SelfDualBooleanAlgebra.compl-∧ Y
(X ⊕ Y) .SelfDualBooleanAlgebra.boolean .lattice.BooleanAlgebra.compl-∨ {a , b} = SelfDualBooleanAlgebra.compl-∨ X , SelfDualBooleanAlgebra.compl-∨ Y

cat : Category (suc 0ℓ) 0ℓ 0ℓ
cat .Category.obj = SelfDualBooleanAlgebra
cat .Category._⇒_ X Y = obj X ⇒ obj Y
cat .Category._≈_ = _≈m_
cat .Category.isEquiv = SemiMod.cat .Category.isEquiv
cat .Category.id X = id (obj X)
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
  SemiMod.terminal .HasTerminal.is-terminal .IsTerminal.to-terminal {obj X}
terminal .HasTerminal.is-terminal .IsTerminal.to-terminal-ext =
  SemiMod.terminal .HasTerminal.is-terminal .IsTerminal.to-terminal-ext

biproduct : ∀ X Y → Biproduct cmon-enriched X Y
biproduct X Y .Biproduct.prod = X ⊕ Y
biproduct X Y .Biproduct.p₁ = SemiMod.biproduct (obj X) (obj Y) .Biproduct.p₁
biproduct X Y .Biproduct.p₂ = SemiMod.biproduct (obj X) (obj Y) .Biproduct.p₂
biproduct X Y .Biproduct.in₁ = SemiMod.biproduct (obj X) (obj Y) .Biproduct.in₁
biproduct X Y .Biproduct.in₂ = SemiMod.biproduct (obj X) (obj Y) .Biproduct.in₂
biproduct X Y .Biproduct.id-1 = SemiMod.biproduct (obj X) (obj Y) .Biproduct.id-1
biproduct X Y .Biproduct.id-2 = SemiMod.biproduct (obj X) (obj Y) .Biproduct.id-2
biproduct X Y .Biproduct.zero-1 = SemiMod.biproduct (obj X) (obj Y) .Biproduct.zero-1
biproduct X Y .Biproduct.zero-2 = SemiMod.biproduct (obj X) (obj Y) .Biproduct.zero-2
biproduct X Y .Biproduct.id-+ = SemiMod.biproduct (obj X) (obj Y) .Biproduct.id-+

products : HasProducts cat
products = biproducts→products cmon-enriched biproduct

U : Functor cat SemiMod.cat
U .Functor.fobj = obj
U .Functor.fmor f = f
U .Functor.fmor-cong f₁≈f₂ = f₁≈f₂
U .Functor.fmor-id = SemiMod.cat .Category.isEquiv .IsEquivalence.refl
U .Functor.fmor-comp f g = SemiMod.cat .Category.isEquiv .IsEquivalence.refl

-- Both hold definitionally: a morphism of self-dual Boolean algebras is a linear map of the
-- underlying semimodules, with no compatibility condition on the Boolean structure.
U-faithful : Faithful U
U-faithful eq = eq

U-full : Full U
U-full h .∃ₛ.fst = h
U-full h .∃ₛ.snd = Category.≈-refl SemiMod.cat {f = h}

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
U-preserve-products {X} {Y} .IsIso.inverse = id ((obj X) SemiMod.⊕ (obj Y))
U-preserve-products {X} {Y} .IsIso.f∘inverse≈id =
  ≈-trans (pair-natural (id ((obj X) SemiMod.⊕ (obj Y))) p₁ p₂)
    (pair-ext (id ((obj X) SemiMod.⊕ (obj Y))))
U-preserve-products {X} {Y} .IsIso.inverse∘f≈id = ≈-trans id-left pair-p≈id
  where
    pair-p≈id : pair (p₁ {obj X} {obj Y}) (p₂ {obj X} {obj Y}) ≈m id ((obj X) SemiMod.⊕ (obj Y))
    pair-p≈id =
      ≈-trans (≈-sym id-right)
        (≈-trans (pair-natural (id ((obj X) SemiMod.⊕ (obj Y))) p₁ p₂)
          (pair-ext (id ((obj X) SemiMod.⊕ (obj Y)))))

-- 𝟘 is also initial: any map out of it is the zero map, since id on 𝟘 is the zero map.
initial : HasInitial cat
initial .HasInitial.witness = 𝟘
initial .HasInitial.is-initial .IsInitial.from-initial = εm
initial .HasInitial.is-initial .IsInitial.from-initial-ext f =
  ≈-sym (≈-trans (≈-sym id-right)
    (≈-trans (∘-cong (≈-refl {f = f}) (to-terminal-unique (id SemiMod.𝟘) εm))
      (comp-bilinear-ε₂ f)))
