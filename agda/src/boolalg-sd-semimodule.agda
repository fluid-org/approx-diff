{-# OPTIONS --postfix-projections --prop --safe #-}

open import Level using (0ℓ; suc)
open import prop-setoid using (Setoid; IsEquivalence)
open import categories using (Category; HasTerminal; IsTerminal; HasInitial; IsInitial; HasProducts)
open import commutative-semiring using (CommutativeSemiring; BooleanAlgebra)
open import cmon-enriched using (CMonEnriched; Biproduct; biproducts→products)
open import commutative-monoid using (CommutativeMonoid)
open import functor using (Functor)
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

-- The Galois connection of f: its Tarski conjugate pair (to-conj) read as adjoints via De Morgan.
module _ (X Y : SelfDualBooleanAlgebra) where
  private
    module X = SelfDualBooleanAlgebra X
    module Y = SelfDualBooleanAlgebra Y

  to-gal : X.obj ⇒ Y.obj → bounded Y.toObj ⇒g bounded X.toObj
  to-gal f = conj→gal X.boolean Y.boolean (to-conj X.selfDualLat Y.selfDualLat f)

open SelfDualBooleanAlgebra using (obj)

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

------------------------------------------------------------------------------
-- to-gal packaged as a contravariant functor to LatGal.

module _ where
  open import functor using (Functor)
  open import basics using (IsPreorder)
  import preorder
  open preorder._≃m_
  open preorder._=>_ using (fun)
  open SemiMod using (Semimodule)
  open SemiMod._⇒_ using (func)
  open SemiMod._≈m_
  open SemiMod.JoinSemilattices ⊤-add-top using (_≤_; ≈→≤; ≤-isPreorder)
  open SDSemiMod using (conjugate; conjugate-cong; conjugate-id; conjugate-comp)
  open import prop-setoid using () renaming (_≃m_ to _≈s_)
  open SelfDualBooleanAlgebra using (selfDual; boolean; ¬)

  private
    module _ (X : SelfDualBooleanAlgebra) where
      private
        module MX = Semimodule (obj X)
        module XB = lattice.BooleanAlgebra (boolean X)

      ≤-antisym : ∀ {a b} → _≤_ (obj X) a b → _≤_ (obj X) b a → a MX.≈ b
      ≤-antisym p q = MX.trans (MX.sym q) (MX.trans MX.+-comm p)

      ¬-cong : ∀ {a b} → a MX.≈ b → ¬ X a MX.≈ ¬ X b
      ¬-cong a≈b = ≤-antisym (XB.¬-antitone (≈→≤ (obj X) (MX.sym a≈b)))
                            (XB.¬-antitone (≈→≤ (obj X) a≈b))

      ≈-to-≤≥ : ∀ {a b} → a MX.≈ b → prop._∧_ (_≤_ (obj X) a b) (_≤_ (obj X) b a)
      ≈-to-≤≥ e = ≈→≤ (obj X) e , ≈→≤ (obj X) (MX.sym e)

      ¬¬-elim : ∀ {a} → ¬ X (¬ X a) MX.≈ a
      ¬¬-elim = ≤-antisym XB.¬-involutive (XB.#-↔-≤¬ .prop.proj₁ (XB.≤-#-¬ .prop.proj₁ (≤-refl' _)))
        where
          ≤-refl' : ∀ (a : MX.Carrier) → _≤_ (obj X) a a
          ≤-refl' _ = ≤-isPreorder (obj X) .IsPreorder.refl

  Gal : Functor cat (Category.opposite galois.cat)
  Gal .Functor.fobj X = bounded (SelfDualBooleanAlgebra.toObj X)
  Gal .Functor.fmor {X} {Y} f = to-gal X Y f
  Gal .Functor.fmor-cong {X} {Y} {f} {g} f≈g .galois._≃g_.right-eq .eqfun x =
    ≈-to-≤≥ X (¬-cong X (conjugate-cong (selfDual X) (selfDual Y) f≈g .*≈* ._≈s_.func-eq (Semimodule.refl (obj Y))))
  Gal .Functor.fmor-id {X} .galois._≃g_.right-eq .eqfun x = ≈-to-≤≥ X eq
    where
      eq : _
      eq = Semimodule.trans (obj X)
             (¬-cong X (conjugate-id (selfDual X) .*≈* ._≈s_.func-eq (Semimodule.refl (obj X))))
             (¬¬-elim X)
  Gal .Functor.fmor-comp {X} {Y} {Z} f g .galois._≃g_.right-eq .eqfun x = ≈-to-≤≥ X eq
    where
      eq : _
      eq = Semimodule.trans (obj X)
             (¬-cong X (conjugate-comp (selfDual X) (selfDual Y) (selfDual Z) f g .*≈* ._≈s_.func-eq (Semimodule.refl (obj Z))))
             (Semimodule.sym (obj X)
               (¬-cong X (SemiMod._⇒_.func-resp-≈ (conjugate (selfDual X) (selfDual Y) g) (¬¬-elim Y))))
