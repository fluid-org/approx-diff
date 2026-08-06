{-# OPTIONS --prop --postfix-projections --safe #-}

-- The three-chain O < C < D as a distributive lattice and hence a commutative semiring, with
-- addition the join and multiplication the meet. Weights for dependence relations: D is value
-- flow and the multiplicative unit, C marks a path through a control point, O is no dependence.
module three where

open import prop using (⊤; ⊥; tt; _∨_; inj₁; inj₂)
open import basics using (IsPreorder; IsMeet; IsJoin; IsBottom; IsTop)

data Three : Set where
  O C D : Three

_≤_ : Three → Three → Prop
O ≤ y = ⊤
C ≤ O = ⊥
C ≤ C = ⊤
C ≤ D = ⊤
D ≤ D = ⊤
D ≤ _ = ⊥

≤-refl : ∀ {x} → x ≤ x
≤-refl {O} = tt
≤-refl {C} = tt
≤-refl {D} = tt

≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
≤-trans {O} _ _ = tt
≤-trans {C} {C} {C} _ _ = tt
≤-trans {C} {C} {D} _ _ = tt
≤-trans {C} {D} {D} _ _ = tt
≤-trans {D} {D} {D} _ _ = tt

≤-isPreorder : IsPreorder _≤_
≤-isPreorder .IsPreorder.refl = ≤-refl
≤-isPreorder .IsPreorder.trans = ≤-trans

open IsPreorder ≤-isPreorder public

open import preorder using (Preorder)

preorder : Preorder
preorder .Preorder.Carrier = Three
preorder .Preorder._≤_ = _≤_
preorder .Preorder.≤-isPreorder = ≤-isPreorder

D-isTop : IsTop ≤-isPreorder D
D-isTop .IsTop.≤-top {O} = tt
D-isTop .IsTop.≤-top {C} = tt
D-isTop .IsTop.≤-top {D} = tt

O-isBottom : IsBottom ≤-isPreorder O
O-isBottom .IsBottom.≤-bottom = tt

_⊓_ : Three → Three → Three
O ⊓ _ = O
C ⊓ O = O
C ⊓ C = C
C ⊓ D = C
D ⊓ x = x

_⊔_ : Three → Three → Three
O ⊔ x = x
C ⊔ O = C
C ⊔ C = C
C ⊔ D = D
D ⊔ _ = D

⊓-lower₁ : ∀ {x y} → (x ⊓ y) ≤ x
⊓-lower₁ {O} = tt
⊓-lower₁ {C} {O} = tt
⊓-lower₁ {C} {C} = tt
⊓-lower₁ {C} {D} = tt
⊓-lower₁ {D} {O} = tt
⊓-lower₁ {D} {C} = tt
⊓-lower₁ {D} {D} = tt

⊓-lower₂ : ∀ {x y} → (x ⊓ y) ≤ y
⊓-lower₂ {O} {O} = tt
⊓-lower₂ {O} {C} = tt
⊓-lower₂ {O} {D} = tt
⊓-lower₂ {C} {O} = tt
⊓-lower₂ {C} {C} = tt
⊓-lower₂ {C} {D} = tt
⊓-lower₂ {D} {y} = ≤-refl {y}

⊓-greatest : ∀ {x y z} → z ≤ x → z ≤ y → z ≤ (x ⊓ y)
⊓-greatest {x} {y} {O} _ _ = tt
⊓-greatest {C} {C} {C} _ _ = tt
⊓-greatest {C} {D} {C} _ _ = tt
⊓-greatest {D} {C} {C} _ _ = tt
⊓-greatest {D} {D} {C} _ _ = tt
⊓-greatest {D} {D} {D} _ _ = tt

⊓-isMeet : IsMeet ≤-isPreorder _⊓_
⊓-isMeet .IsMeet.π₁ = ⊓-lower₁
⊓-isMeet .IsMeet.π₂ = ⊓-lower₂
⊓-isMeet .IsMeet.⟨_,_⟩ = ⊓-greatest

⊔-upper₁ : ∀ {x y} → x ≤ (x ⊔ y)
⊔-upper₁ {O} = tt
⊔-upper₁ {C} {O} = tt
⊔-upper₁ {C} {C} = tt
⊔-upper₁ {C} {D} = tt
⊔-upper₁ {D} = tt

⊔-upper₂ : ∀ {x y} → y ≤ (x ⊔ y)
⊔-upper₂ {O} {y} = ≤-refl {y}
⊔-upper₂ {C} {O} = tt
⊔-upper₂ {C} {C} = tt
⊔-upper₂ {C} {D} = tt
⊔-upper₂ {D} {O} = tt
⊔-upper₂ {D} {C} = tt
⊔-upper₂ {D} {D} = tt

⊔-least : ∀ {x y z} → x ≤ z → y ≤ z → (x ⊔ y) ≤ z
⊔-least {O} {y} _ q = q
⊔-least {C} {O} p _ = p
⊔-least {C} {C} p _ = p
⊔-least {C} {D} _ q = q
⊔-least {D} p _ = p

⊔-isJoin : IsJoin ≤-isPreorder _⊔_
⊔-isJoin .IsJoin.inl = ⊔-upper₁
⊔-isJoin .IsJoin.inr = ⊔-upper₂
⊔-isJoin .IsJoin.[_,_] = ⊔-least

open import meet-semilattice using (MeetSemilattice)
open import join-semilattice using (JoinSemilattice)
open import lattice using (DistributiveLattice; asSemiring)
import commutative-semiring as CS

lattice : DistributiveLattice
lattice .DistributiveLattice.carrier = preorder
lattice .DistributiveLattice.meets .MeetSemilattice._∧_ = _⊓_
lattice .DistributiveLattice.meets .MeetSemilattice.⊤ = D
lattice .DistributiveLattice.meets .MeetSemilattice.∧-isMeet = ⊓-isMeet
lattice .DistributiveLattice.meets .MeetSemilattice.⊤-isTop = D-isTop
lattice .DistributiveLattice.joins .JoinSemilattice._∨_ = _⊔_
lattice .DistributiveLattice.joins .JoinSemilattice.⊥ = O
lattice .DistributiveLattice.joins .JoinSemilattice.∨-isJoin = ⊔-isJoin
lattice .DistributiveLattice.joins .JoinSemilattice.⊥-isBottom = O-isBottom
lattice .DistributiveLattice.∧-∨-distrib O y z = tt
lattice .DistributiveLattice.∧-∨-distrib C O O = tt
lattice .DistributiveLattice.∧-∨-distrib C O C = tt
lattice .DistributiveLattice.∧-∨-distrib C O D = tt
lattice .DistributiveLattice.∧-∨-distrib C C O = tt
lattice .DistributiveLattice.∧-∨-distrib C C C = tt
lattice .DistributiveLattice.∧-∨-distrib C C D = tt
lattice .DistributiveLattice.∧-∨-distrib C D O = tt
lattice .DistributiveLattice.∧-∨-distrib C D C = tt
lattice .DistributiveLattice.∧-∨-distrib C D D = tt
lattice .DistributiveLattice.∧-∨-distrib D O O = tt
lattice .DistributiveLattice.∧-∨-distrib D O C = tt
lattice .DistributiveLattice.∧-∨-distrib D O D = tt
lattice .DistributiveLattice.∧-∨-distrib D C O = tt
lattice .DistributiveLattice.∧-∨-distrib D C C = tt
lattice .DistributiveLattice.∧-∨-distrib D C D = tt
lattice .DistributiveLattice.∧-∨-distrib D D O = tt
lattice .DistributiveLattice.∧-∨-distrib D D C = tt
lattice .DistributiveLattice.∧-∨-distrib D D D = tt

semiring : CS.CommutativeSemiring _
semiring = asSemiring lattice

private
  module S = CS.CommutativeSemiring semiring

∨-idem : ∀ {x} → (x S.+ x) S.≈ x
∨-idem {O} = S.refl {O}
∨-idem {C} = S.refl {C}
∨-idem {D} = S.refl {D}

∧-idem : ∀ {x} → (x S.· x) S.≈ x
∧-idem {O} = S.refl {O}
∧-idem {C} = S.refl {C}
∧-idem {D} = S.refl {D}

⊤-add-top : ∀ {x} → (S.ι S.+ x) S.≈ S.ι
⊤-add-top {O} = S.refl {D}
⊤-add-top {C} = S.refl {D}
⊤-add-top {D} = S.refl {D}
