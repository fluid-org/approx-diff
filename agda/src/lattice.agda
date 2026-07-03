{-# OPTIONS --postfix-projections --prop --safe #-}

module lattice where

open import Level using (suc; 0ℓ)
open import prop hiding (_∨_; ⊥; ⊤) renaming (_∧_ to _∧ₚ_)
open import preorder using (Preorder)
open import basics using (module Disjoint; setoidOf; IsMeet; IsJoin; IsBottom; IsTop)
open import meet-semilattice using (MeetSemilattice)
open import join-semilattice using (JoinSemilattice)
open import commutative-monoid using (CommutativeMonoid)
import commutative-semiring as CS

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

bounded : DistributiveLattice → BoundedLattice
bounded X .BoundedLattice.carrier = DistributiveLattice.carrier X
bounded X .BoundedLattice.meets   = DistributiveLattice.meets X
bounded X .BoundedLattice.joins   = DistributiveLattice.joins X

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

  ≤-#-¬ : ∀ {a b} → (a ≤ b) ⇔ (a # ¬ b)
  ≤-#-¬ .proj₁ a≤b = ≤-trans (∧-mono a≤b ≤-refl) compl-∧
  ≤-#-¬ {a} {b} .proj₂ a#¬b =
    ≤-trans ⟨ ≤-refl ∧ ≤-top ⟩
      (≤-trans (∧-mono ≤-refl compl-∨)
        (≤-trans (∧-∨-distrib a b (¬ b))
          (≤-trans (∨-mono ≤-refl a#¬b) [ π₂ ∨ ≤-bottom ])))

  ¬-antitone : ∀ {x y} → x ≤ y → ¬ y ≤ ¬ x
  ¬-antitone x≤y =
    #-↔-≤¬ .proj₁ (#-sym (#-mono x≤y _ (#-sym (#-↔-≤¬ .proj₂ ≤-refl))))

  ¬¬-intro : ∀ {x} → x ≤ ¬ (¬ x)
  ¬¬-intro = #-↔-≤¬ .proj₁ (≤-#-¬ .proj₁ ≤-refl)

  ¬-involutive : ∀ {x} → ¬ (¬ x) ≤ x
  ¬-involutive {x} =
    ≤-trans ⟨ ≤-refl ∧ ≤-top ⟩
      (≤-trans (∧-mono ≤-refl compl-∨)
        (≤-trans (∧-∨-distrib (¬ (¬ x)) x (¬ x))
          [ π₂ ∨ ≤-trans (≤-trans ∧-comm compl-∧) ≤-bottom ]))

  #-reflect : ∀ {x y} → (∀ z → y # z → x # z) → x ≤ y
  #-reflect {x} {y} h =
    ≤-trans (#-↔-≤¬ .proj₁ (h (¬ y) (#-sym (#-↔-≤¬ .proj₂ ≤-refl)))) ¬-involutive

------------------------------------------------------------------------------
-- Every distributive lattice is a commutative semiring (+ = ∨, · = ∧), and a Boolean algebra on the
-- lattice is the semiring's BooleanAlgebra.  This is the lattice-to-semiring downcast.

module _ (X : DistributiveLattice) where
  open DistributiveLattice X
  private
    module M  = IsMeet ∧-isMeet
    module J  = IsJoin ∨-isJoin
    module Tp = IsTop ⊤-isTop
    module Bt = IsBottom ⊥-isBottom

    join-cmon : CommutativeMonoid (setoidOf ≤-isPreorder)
    join-cmon .CommutativeMonoid.ε = ⊥
    join-cmon .CommutativeMonoid._+_ = _∨_
    join-cmon .CommutativeMonoid.+-cong = J.cong
    join-cmon .CommutativeMonoid.+-lunit = J.[ Bt.≤-bottom , ≤-refl ] , J.inr
    join-cmon .CommutativeMonoid.+-assoc = J.assoc
    join-cmon .CommutativeMonoid.+-comm {x} {y} = J.comm {x} {y} , J.comm {y} {x}

    meet-cmon : CommutativeMonoid (setoidOf ≤-isPreorder)
    meet-cmon .CommutativeMonoid.ε = ⊤
    meet-cmon .CommutativeMonoid._+_ = _∧_
    meet-cmon .CommutativeMonoid.+-cong = M.cong
    meet-cmon .CommutativeMonoid.+-lunit = M.π₂ , M.⟨ Tp.≤-top , ≤-refl ⟩
    meet-cmon .CommutativeMonoid.+-assoc = M.assoc
    meet-cmon .CommutativeMonoid.+-comm {x} {y} = M.comm {x} {y} , M.comm {y} {x}

  asSemiring : CS.CommutativeSemiring (setoidOf ≤-isPreorder)
  asSemiring .CS.CommutativeSemiring.additive = join-cmon
  asSemiring .CS.CommutativeSemiring.multiplicative = meet-cmon
  asSemiring .CS.CommutativeSemiring.·-+-distribₗ {x} {y} {z} =
    ∧-∨-distrib x y z ,
    J.[ M.⟨ M.π₁ , ≤-trans M.π₂ J.inl ⟩ , M.⟨ M.π₁ , ≤-trans M.π₂ J.inr ⟩ ]
  asSemiring .CS.CommutativeSemiring.ε-annihilₗ {x} =
    M.π₁ , M.⟨ ≤-refl , Bt.≤-bottom ⟩

  asBoolean : BooleanAlgebra X → CS.BooleanAlgebra asSemiring
  asBoolean ba .CS.BooleanAlgebra.∧-idem = ∧-idem
  asBoolean ba .CS.BooleanAlgebra.⊤-add-top = J.[ ≤-refl , Tp.≤-top ] , J.inl
  asBoolean ba .CS.BooleanAlgebra.¬ = BooleanAlgebra.¬ ba
  asBoolean ba .CS.BooleanAlgebra.compl-∧ = J.[ BooleanAlgebra.compl-∧ ba , ≤-refl ] , J.inr
  asBoolean ba .CS.BooleanAlgebra.compl-∨ = J.[ BooleanAlgebra.compl-∨ ba , ≤-refl ] , J.inr
