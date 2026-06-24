{-# OPTIONS --postfix-projections --prop --safe #-}

module lattice where

open import Level using (suc; 0ℓ)
open import prop hiding (_∨_; ⊥; ⊤) renaming (_∧_ to _∧ₚ_)
open import preorder using (Preorder)
open import basics using (module Disjoint)
open import meet-semilattice using (MeetSemilattice)
open import join-semilattice using (JoinSemilattice)

record BoundedLattice : Set (suc 0ℓ) where
  no-eta-equality
  field
    carrier : Preorder
    meets   : MeetSemilattice carrier
    joins   : JoinSemilattice carrier

  open Preorder carrier public
  open MeetSemilattice meets renaming (idem to ∧-idem; interchange to ∧-interchange) public
  open JoinSemilattice joins renaming (idem to ∨-idem; interchange to ∨-interchange) public
  open Disjoint ≤-isPreorder ∧-isMeet ⊥-isBottom public

record DistributiveLattice : Set (suc 0ℓ) where
  no-eta-equality
  field
    carrier : Preorder
    meets   : MeetSemilattice carrier
    joins   : JoinSemilattice carrier

  open Preorder carrier public
  open MeetSemilattice meets renaming (idem to ∧-idem; interchange to ∧-interchange) public
  open JoinSemilattice joins renaming (idem to ∨-idem; interchange to ∨-interchange) public
  open Disjoint ≤-isPreorder ∧-isMeet ⊥-isBottom public

  field
    ∧-∨-distrib  : ∀ x y z → x ∧ (y ∨ z) ≤ (x ∧ y) ∨ (x ∧ z)

  ∨-∧-distrib : ∀ x y z → x ∨ (y ∧ z) ≤ (x ∨ y) ∧ (x ∨ z)
  ∨-∧-distrib x y z = [ ⟨ inl ∧ inl ⟩ ∨ ⟨ ≤-trans π₁ inr ∧ ≤-trans π₂ inr ⟩ ]

  #-distrib : ∀ {x y z} → x # y → x # z → x # (y ∨ z)
  #-distrib x#y x#z = ≤-trans (∧-∨-distrib _ _ _) (≤-trans (∨-mono x#y x#z) (∨-idem .proj₁))

record BooleanAlgebra (X : DistributiveLattice) : Set where
  open DistributiveLattice X

  field
    ¬ : Carrier → Carrier
    compl-∨ : ∀ {x} → ⊤ ≤ (x ∨ ¬ x)
    compl-∧ : ∀ {x} → (x ∧ ¬ x) ≤ ⊥

  #-↔-≤¬ : ∀ {x y} → (x # y) ⇔ (x ≤ ¬ y)
  #-↔-≤¬ {x} {y} .proj₁ x#y =
    ≤-trans ⟨ ≤-refl ∧ ≤-top ⟩
      (≤-trans (∧-mono ≤-refl compl-∨)
        (≤-trans (∧-∨-distrib x y (¬ y))
          [ ≤-trans x#y ≤-bottom ∨ π₂ ]))
  #-↔-≤¬ .proj₂ x≤¬y =
    ≤-trans (∧-mono x≤¬y ≤-refl) (≤-trans ∧-comm compl-∧)

  ¬-antitone : ∀ {x y} → x ≤ y → ¬ y ≤ ¬ x
  ¬-antitone x≤y =
    #-↔-≤¬ .proj₁ (#-sym (#-mono x≤y _ (#-sym (#-↔-≤¬ .proj₂ ≤-refl))))

  ¬-involutive : ∀ {x} → ¬ (¬ x) ≤ x
  ¬-involutive {x} =
    ≤-trans ⟨ ≤-refl ∧ ≤-top ⟩
      (≤-trans (∧-mono ≤-refl compl-∨)
        (≤-trans (∧-∨-distrib (¬ (¬ x)) x (¬ x))
          [ π₂ ∨ ≤-trans (≤-trans ∧-comm compl-∧) ≤-bottom ]))

  #-reflect : ∀ {x y} → (∀ z → y # z → x # z) → x ≤ y
  #-reflect {x} {y} h =
    ≤-trans (#-↔-≤¬ .proj₁ (h (¬ y) (#-sym (#-↔-≤¬ .proj₂ ≤-refl)))) ¬-involutive
