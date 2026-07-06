{-# OPTIONS --prop --postfix-projections --safe #-}
module two where

open import prop using (⊤; ⊥; tt; _∨_; inj₁; inj₂; _,_)
open import basics using (IsPreorder; IsMeet; IsJoin; IsBottom; IsTop)

data Two : Set where
  O I : Two

_≤_ : Two → Two → Prop
O ≤ y = ⊤
I ≤ O = ⊥
I ≤ I = ⊤

≤-refl : ∀ {x} → x ≤ x
≤-refl {O} = tt
≤-refl {I} = tt

≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
≤-trans {O} {O} {O} p q = tt
≤-trans {O} {O} {I} p q = tt
≤-trans {O} {I} {I} p q = tt
≤-trans {I} {I} {I} p q = tt

≤-total : ∀ x y → (x ≤ y) ∨ (y ≤ x)
≤-total O y = inj₁ tt
≤-total I O = inj₂ tt
≤-total I I = inj₁ tt

≤-isPreorder : IsPreorder _≤_
≤-isPreorder .IsPreorder.refl = ≤-refl
≤-isPreorder .IsPreorder.trans = ≤-trans

open IsPreorder ≤-isPreorder public

open import preorder using (Preorder)

preorder : Preorder
preorder .Preorder.Carrier = Two
preorder .Preorder._≤_ = _≤_
preorder .Preorder.≤-isPreorder = ≤-isPreorder

------------------------------------------------------------------------------
I-isTop : IsTop ≤-isPreorder I
I-isTop .IsTop.≤-top {O} = tt
I-isTop .IsTop.≤-top {I} = tt

_⊓_ : Two → Two → Two
O ⊓ x = O
I ⊓ x = x

⊓-lower₁ : ∀ {x y} → (x ⊓ y) ≤ x
⊓-lower₁ {O} {y} = tt
⊓-lower₁ {I} {y} = I-isTop .IsTop.≤-top

⊓-lower₂ : ∀ {x y} → (x ⊓ y) ≤ y
⊓-lower₂ {O} {y} = tt
⊓-lower₂ {I} {y} = ≤-refl

⊓-greatest : ∀ {x y z} → z ≤ x → z ≤ y → z ≤ (x ⊓ y)
⊓-greatest {x} {y} {O} tt tt = tt
⊓-greatest {I} {I} {I} tt tt = tt

⊓-isMeet : IsMeet ≤-isPreorder _⊓_
⊓-isMeet .IsMeet.π₁ = ⊓-lower₁
⊓-isMeet .IsMeet.π₂ = ⊓-lower₂
⊓-isMeet .IsMeet.⟨_,_⟩ = ⊓-greatest

------------------------------------------------------------------------------
O-isBottom : IsBottom ≤-isPreorder O
O-isBottom .IsBottom.≤-bottom = tt

_⊔_ : Two → Two → Two
O ⊔ x = x
I ⊔ x = I

⊔-upper₁ : ∀ {x y} → x ≤ (x ⊔ y)
⊔-upper₁ {O} {y} = tt
⊔-upper₁ {I} {y} = tt

⊔-upper₂ : ∀ {x y} → y ≤ (x ⊔ y)
⊔-upper₂ {O} {y} = ≤-refl
⊔-upper₂ {I} {y} = I-isTop .IsTop.≤-top

⊔-least : ∀ {x y z} → x ≤ z → y ≤ z → (x ⊔ y) ≤ z
⊔-least {O} {y} {z} p q = q
⊔-least {I} {y} {z} p q = p

⊔-isJoin : IsJoin ≤-isPreorder _⊔_
⊔-isJoin .IsJoin.inl = ⊔-upper₁
⊔-isJoin .IsJoin.inr = ⊔-upper₂
⊔-isJoin .IsJoin.[_,_] = ⊔-least

------------------------------------------------------------------------------
¬ : Two → Two
¬ O = I
¬ I = O

compl-∧ : ∀ {x} → (x ⊓ ¬ x) ≤ O
compl-∧ {O} = tt
compl-∧ {I} = tt

compl-∨ : ∀ {x} → I ≤ (x ⊔ ¬ x)
compl-∨ {O} = tt
compl-∨ {I} = tt

¬-involutive : ∀ {x} → x ≃ ¬ (¬ x)
¬-involutive {O} = ≃-refl {O}
¬-involutive {I} = ≃-refl {I}

¬-antitone : ∀ {x y} → x ≤ y → ¬ y ≤ ¬ x
¬-antitone {O} {O} _ = tt
¬-antitone {O} {I} _ = tt
¬-antitone {I} {I} _ = tt

-- FIXME: de Morgan, etc., should be derived from the fact that this
-- is a Boolean algebra.

------------------------------------------------------------------------------
-- Two as a distributive lattice with complement.

open import meet-semilattice using (MeetSemilattice)
open import join-semilattice using (JoinSemilattice)
open import lattice using (DistributiveLattice; BooleanAlgebra; asSemiring; asBoolean)
import commutative-semiring as CS

lattice : DistributiveLattice
lattice .DistributiveLattice.carrier = preorder
lattice .DistributiveLattice.meets .MeetSemilattice._∧_ = _⊓_
lattice .DistributiveLattice.meets .MeetSemilattice.⊤ = I
lattice .DistributiveLattice.meets .MeetSemilattice.∧-isMeet = ⊓-isMeet
lattice .DistributiveLattice.meets .MeetSemilattice.⊤-isTop = I-isTop
lattice .DistributiveLattice.joins .JoinSemilattice._∨_ = _⊔_
lattice .DistributiveLattice.joins .JoinSemilattice.⊥ = O
lattice .DistributiveLattice.joins .JoinSemilattice.∨-isJoin = ⊔-isJoin
lattice .DistributiveLattice.joins .JoinSemilattice.⊥-isBottom = O-isBottom
lattice .DistributiveLattice.∧-∨-distrib O y z = ≤-refl {O}
lattice .DistributiveLattice.∧-∨-distrib I y z = ≤-refl {y ⊔ z}

boolean : BooleanAlgebra lattice
boolean .BooleanAlgebra.¬ = ¬
boolean .BooleanAlgebra.compl-∨ {x} = compl-∨ {x}
boolean .BooleanAlgebra.compl-∧ {x} = compl-∧ {x}

semiring : CS.CommutativeSemiring _
semiring = asSemiring lattice

semiring-boolean : CS.BooleanAlgebra semiring
semiring-boolean = asBoolean lattice boolean
