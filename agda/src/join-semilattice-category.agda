{-# OPTIONS --postfix-projections --prop --safe #-}

module join-semilattice-category where

open import Level using (suc; 0ℓ)
open import prop using (proj₁; proj₂; _,_; LiftS; liftS)
open import prop-setoid using (IsEquivalence; module ≈-Reasoning)
open import basics using (IsPreorder; IsBottom; IsJoin)
open import preorder using (Preorder; _=>_; _×_) renaming (_≃m_ to _≃P_)
open import join-semilattice
  using ( JoinSemilattice; 𝟙
        ; εm; _+m_; +m-cong; +m-comm; +m-assoc; +m-lunit
        ; comp-bilinear₁; comp-bilinear₂; comp-bilinear-ε₁; comp-bilinear-ε₂)
  renaming (_=>_ to _=>J_; _≃m_ to _≃J_; id to idJ; _∘_ to _∘J_;
            _⊕_ to _⊕J_;
            ≃m-isEquivalence to ≃J-isEquivalence)
open import categories using (Category; HasProducts; HasCoproducts; HasTerminal; HasInitial)
open import functor using (Functor; NatTrans; ≃-NatTrans; HasLimits; Limit; IsLimit; module Functor; module NatTrans; module ≃-NatTrans)
import two

record Obj : Set (suc 0ℓ) where
  no-eta-equality
  field
    carrier : Preorder
    joins   : JoinSemilattice carrier
  open Preorder carrier public
  open JoinSemilattice joins public
open Obj

record _⇒_ (X Y : Obj) : Set where
  no-eta-equality
  field
    *→* : X .joins =>J Y .joins
  open _=>J_ *→* public
  open preorder._=>_ func public
open _⇒_

record _≃m_ {X Y : Obj} (f g : X ⇒ Y) : Prop where
  no-eta-equality
  field
    f≃f : f .*→* ≃J g .*→*
  open _≃J_ f≃f public
  open preorder._≃m_ eqfunc public
open _≃m_

cat : Category (suc 0ℓ) 0ℓ 0ℓ
cat .Category.obj = Obj
cat .Category._⇒_ = _⇒_
cat .Category._≈_ = _≃m_
cat .Category.isEquiv .IsEquivalence.refl .f≃f = ≃J-isEquivalence .IsEquivalence.refl
cat .Category.isEquiv .IsEquivalence.sym f≃g .f≃f = ≃J-isEquivalence .IsEquivalence.sym (f≃g .f≃f)
cat .Category.isEquiv .IsEquivalence.trans f≃g g≃h .f≃f =
  ≃J-isEquivalence .IsEquivalence.trans (f≃g .f≃f) (g≃h .f≃f)
cat .Category.id X .*→* = idJ
cat .Category._∘_ f g .*→* = f .*→* ∘J g .*→*
cat .Category.∘-cong f₁≃f₂ g₁≃g₂ .f≃f = join-semilattice.∘-cong (f₁≃f₂ .f≃f) (g₁≃g₂ .f≃f)
cat .Category.id-left .f≃f = join-semilattice.id-left
cat .Category.id-right .f≃f = join-semilattice.id-right
cat .Category.assoc f g h .f≃f = join-semilattice.assoc (f .*→*) (g .*→*) (h .*→*)

------------------------------------------------------------------------------
-- CMon-enrichment

open import commutative-monoid using (CommutativeMonoid)
open import cmon-enriched using (CMonEnriched)

cmon-enriched : CMonEnriched cat
cmon-enriched .CMonEnriched.homCM x y .CommutativeMonoid.ε .*→* = εm
cmon-enriched .CMonEnriched.homCM x y .CommutativeMonoid._+_ f g .*→* = (f .*→*) +m (g .*→*)
cmon-enriched .CMonEnriched.homCM x y .CommutativeMonoid.+-cong f₁≃f₂ g₁≃g₂ .f≃f = +m-cong (f₁≃f₂ .f≃f) (g₁≃g₂ .f≃f)
cmon-enriched .CMonEnriched.homCM x y .CommutativeMonoid.+-lunit .f≃f = +m-lunit
cmon-enriched .CMonEnriched.homCM x y .CommutativeMonoid.+-assoc {f}{g}{h} .f≃f = +m-assoc {f = f .*→*} {g .*→*} {h .*→*}
cmon-enriched .CMonEnriched.homCM x y .CommutativeMonoid.+-comm {f}{g} .f≃f = +m-comm {f = f .*→*} {g .*→*}
cmon-enriched .CMonEnriched.comp-bilinear₁ f₁ f₂ g .f≃f = comp-bilinear₁ (f₁ .*→*) (f₂ .*→*) (g .*→*)
cmon-enriched .CMonEnriched.comp-bilinear₂ f g₁ g₂ .f≃f = comp-bilinear₂ (f .*→*) (g₁ .*→*) (g₂ .*→*)
cmon-enriched .CMonEnriched.comp-bilinear-ε₁ f .f≃f = comp-bilinear-ε₁ (f .*→*)
cmon-enriched .CMonEnriched.comp-bilinear-ε₂ f .f≃f = comp-bilinear-ε₂ (f .*→*)


coproducts : HasCoproducts cat
coproducts .HasCoproducts.coprod X Y .carrier = X .carrier × Y .carrier
coproducts .HasCoproducts.coprod X Y .joins = X .joins ⊕J Y .joins
coproducts .HasCoproducts.in₁ .*→* = join-semilattice.inject₁
coproducts .HasCoproducts.in₂ .*→* = join-semilattice.inject₂
coproducts .HasCoproducts.copair f g .*→* = join-semilattice.[ (f .*→*) , (g .*→*) ]
coproducts .HasCoproducts.copair-cong eq₁ eq₂ .f≃f = join-semilattice.[]-cong (eq₁ .f≃f) (eq₂ .f≃f)
coproducts .HasCoproducts.copair-in₁ f g .f≃f = join-semilattice.inj₁-copair (f .*→*) (g .*→*)
coproducts .HasCoproducts.copair-in₂ f g .f≃f = join-semilattice.inj₂-copair (f .*→*) (g .*→*)
coproducts .HasCoproducts.copair-ext f .f≃f = join-semilattice.copair-ext (f .*→*)

products : HasProducts cat
products .HasProducts.prod X Y .carrier = X .carrier × Y .carrier
products .HasProducts.prod X Y .joins = X .joins ⊕J Y .joins
products .HasProducts.p₁ .*→* = join-semilattice.project₁
products .HasProducts.p₂ .*→* = join-semilattice.project₂
products .HasProducts.pair f g .*→* = join-semilattice.⟨ (f .*→*) , (g .*→*) ⟩
products .HasProducts.pair-cong eq₁ eq₂ .f≃f = join-semilattice.⟨⟩-cong (eq₁ .f≃f) (eq₂ .f≃f)
products .HasProducts.pair-p₁ f g .f≃f = join-semilattice.pair-p₁ (f .*→*) (g .*→*)
products .HasProducts.pair-p₂ f g .f≃f = join-semilattice.pair-p₂ (f .*→*) (g .*→*)
products .HasProducts.pair-ext f .f≃f = join-semilattice.pair-ext (f .*→*)

initial : HasInitial cat
initial .HasInitial.witness = record { carrier = preorder.𝟙 ; joins = 𝟙 }
initial .HasInitial.is-initial .categories.IsInitial.from-initial .*→* = join-semilattice.initial
initial .HasInitial.is-initial .categories.IsInitial.from-initial-ext f .f≃f = join-semilattice.initial-unique _ _ _

terminal : HasTerminal cat
terminal .HasTerminal.witness = record { carrier = preorder.𝟙 ; joins = 𝟙 }
terminal .HasTerminal.is-terminal .categories.IsTerminal.to-terminal .*→* = join-semilattice.terminal
terminal .HasTerminal.is-terminal .categories.IsTerminal.to-terminal-ext f .f≃f = join-semilattice.terminal-unique _ _ _

TWO : Obj
TWO .carrier = two.Two-preorder
TWO .joins .JoinSemilattice._∨_ = two._⊔_
TWO .joins .JoinSemilattice.⊥ = two.O
TWO .joins .JoinSemilattice.∨-isJoin = two.⊔-isJoin
TWO .joins .JoinSemilattice.⊥-isBottom = two.O-isBottom

------------------------------------------------------------------------------
-- Limits.

module _ (𝒮 : Category 0ℓ 0ℓ 0ℓ) where

  private
    module 𝒮 = Category 𝒮

  open Functor
  open NatTrans
  open ≃-NatTrans
  open _≃J_
  open preorder._=>_
  open preorder._≃m_

  record Π-Carrier (D : Functor 𝒮 cat) : Set where
    field
      Π-func    : (x : 𝒮.obj) → D .fobj x .Carrier
      Π-natural : ∀ {x₁ x₂} (f : x₁ 𝒮.⇒ x₂) →
                  _≃_ (D .fobj x₂) (D .fmor f .fun (Π-func x₁)) (Π-func x₂)
  open Π-Carrier

  Π : Functor 𝒮 cat → Obj
  Π D .carrier .Preorder.Carrier = Π-Carrier D
  Π D .carrier .Preorder._≤_ α₁ α₂ = ∀ s → D .fobj s ._≤_ (α₁ .Π-func s) (α₂ .Π-func s)
  Π D .carrier .Preorder.≤-isPreorder .IsPreorder.refl s = D .fobj s .≤-refl
  Π D .carrier .Preorder.≤-isPreorder .IsPreorder.trans α≤β β≤γ s = D .fobj s .≤-trans (α≤β s) (β≤γ s)
  Π D .joins .JoinSemilattice._∨_ α₁ α₂ .Π-func s = D .fobj s ._∨_ (α₁ .Π-func s) (α₂ .Π-func s)
  Π D .joins .JoinSemilattice._∨_ α₁ α₂ .Π-natural {s₁}{s₂} f =
    S₂ .≤-trans (Df .∨-preserving)
      (S₂ .[_∨_] (S₂ .≤-trans (proj₁ (α₁ .Π-natural f)) (S₂ .inl))
                  (S₂ .≤-trans (proj₁ (α₂ .Π-natural f)) (S₂ .inr))) ,
    S₂ .[_∨_] (S₂ .≤-trans (proj₂ (α₁ .Π-natural f)) (Df .mono (D .fobj s₁ .inl)))
              (S₂ .≤-trans (proj₂ (α₂ .Π-natural f)) (Df .mono (D .fobj s₁ .inr)))
    where S₂ = D .fobj s₂; Df = D .fmor f
  Π D .joins .JoinSemilattice.⊥ .Π-func s = D .fobj s .⊥
  Π D .joins .JoinSemilattice.⊥ .Π-natural {s₁}{s₂} f = D .fmor f .⊥-preserving , D .fobj s₂ .≤-bottom
  Π D .joins .JoinSemilattice.∨-isJoin .IsJoin.inl s = D .fobj s .inl
  Π D .joins .JoinSemilattice.∨-isJoin .IsJoin.inr s = D .fobj s .inr
  Π D .joins .JoinSemilattice.∨-isJoin .IsJoin.[_,_] α≤β α≤γ s = D .fobj s .[_∨_] (α≤β s) (α≤γ s)
  Π D .joins .JoinSemilattice.⊥-isBottom .IsBottom.≤-bottom s = D .fobj s .≤-bottom

  limits : HasLimits 𝒮 cat
  limits D .Limit.apex = Π D
  limits D .Limit.cone .transf x .*→* ._=>J_.func .fun α = α .Π-func x
  limits D .Limit.cone .transf x .*→* ._=>J_.func .mono α₁≤α₂ = α₁≤α₂ x
  limits D .Limit.cone .transf x .*→* ._=>J_.∨-preserving = D .fobj x .≤-refl
  limits D .Limit.cone .transf x .*→* ._=>J_.⊥-preserving = D .fobj x .≤-refl
  limits D .Limit.cone .natural {x} {y} f .f≃f .eqfunc .eqfun α = α .Π-natural f
  limits D .Limit.isLimit .IsLimit.lambda X α .*→* ._=>J_.func .fun x .Π-func s = α .transf s .fun x
  limits D .Limit.isLimit .IsLimit.lambda X α .*→* ._=>J_.func .fun x .Π-natural f = α .natural f .eqfun x
  limits D .Limit.isLimit .IsLimit.lambda X α .*→* ._=>J_.func .mono x₁≤x₂ s = α .transf s .mono x₁≤x₂
  limits D .Limit.isLimit .IsLimit.lambda X α .*→* ._=>J_.∨-preserving s = α .transf s .∨-preserving
  limits D .Limit.isLimit .IsLimit.lambda X α .*→* ._=>J_.⊥-preserving s = α .transf s .⊥-preserving
  limits D .Limit.isLimit .IsLimit.lambda-cong α≃β .f≃f .eqfunc .eqfun x .proj₁ s = α≃β .transf-eq s .eqfun x .proj₁
  limits D .Limit.isLimit .IsLimit.lambda-cong α≃β .f≃f .eqfunc .eqfun x .proj₂ s = α≃β .transf-eq s .eqfun x .proj₂
  limits D .Limit.isLimit .IsLimit.lambda-eval {X} α .transf-eq s .f≃f .eqfunc .eqfun x = D .fobj s .≃-refl
  limits D .Limit.isLimit .IsLimit.lambda-ext {X} f .f≃f .eqfunc .eqfun x .proj₁ s = D .fobj s .≤-refl
  limits D .Limit.isLimit .IsLimit.lambda-ext {X} f .f≃f .eqfunc .eqfun x .proj₂ s = D .fobj s .≤-refl

------------------------------------------------------------------------------
-- HasSetoidProducts derived from limits.

open import indexed-family using (HasSetoidProducts)
open import functor using (limits→limits')

hasSetoidProducts : HasSetoidProducts 0ℓ 0ℓ cat
hasSetoidProducts =
  indexed-family.hasSetoidProducts 0ℓ 0ℓ cat
    (λ A → limits→limits' (limits (categories.setoid→category A)))
