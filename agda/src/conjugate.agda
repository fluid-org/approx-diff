{-# OPTIONS --postfix-projections --prop --safe #-}

module conjugate where

open import Level
open import Data.Unit using () renaming (tt to ttU)
open import prop hiding (_∨_; ⊥; ⊤) renaming (_∧_ to _∧ₚ_)
open import prop-setoid using (IsEquivalence)
open import preorder hiding (𝟙)
open import basics using (module Disjoint)
open import categories
open import meet-semilattice
  using (MeetSemilattice)
  renaming (_=>_ to _=>M_; _⊕_ to _⊕M_)
open import join-semilattice
  using (JoinSemilattice)
  renaming (_=>_ to _=>J_; _≃m_ to _≃J_; _⊕_ to _⊕J_)
open import cmon-enriched

-- Category LatConj of distributive lattices (with bounded meet and join) and Tarski conjugates between them.
open import lattice using (BooleanAlgebra) renaming (DistributiveLattice to Obj) public

open Obj

record _⇒c_ (X Y : Obj) : Set where
  no-eta-equality
  open _=>J_
  open preorder._=>_

  private
    module X = Obj X
    module Y = Obj Y
  field
    -- situation is symmetric, so names here just refer to direction relative to X ⇒c Y
    right : X .joins =>J Y .joins
    left  : Y .joins =>J X .joins
    conjugate : ∀ {x y} → y Y.# right .func .fun x ⇔ left .func .fun y X.# x

open _⇒c_

-- Wwhen both objects are Boolean algebras, join-preservation of right and left can be derived from conjugacy.
module _ {X Y : Obj} (X-bool : BooleanAlgebra X) (Y-bool : BooleanAlgebra Y) where
  open _=>J_
  open preorder._=>_

  private
    module X = Obj X
    module Y = Obj Y
    module XJ = JoinSemilattice (X .joins)
    module YJ = JoinSemilattice (Y .joins)
    module BX = BooleanAlgebra X-bool
    module BY = BooleanAlgebra Y-bool

  boolean-⇒c : (right : X .carrier preorder.=> Y .carrier)
               (left : Y .carrier preorder.=> X .carrier)
               (conjugate : ∀ {x y} → y Y.# right .fun x ⇔ left .fun y X.# x) →
               X ⇒c Y
  boolean-⇒c right l c .right .func = right
  boolean-⇒c right l c .right .∨-preserving {x} {x'} = BY.#-reflect suffices
       where
       suffices : ∀ y → (right .fun x YJ.∨ right .fun x') Y.# y → right .fun (x XJ.∨ x') Y.# y
       suffices y fx∨fx'#y =
         Y.#-sym (c .proj₂ (X.#-distrib
           (c .proj₁ (Y.#-sym (Y.#-mono (Y.inl) y fx∨fx'#y)))
           (c .proj₁ (Y.#-sym (Y.#-mono (Y.inr) y fx∨fx'#y)))))
  boolean-⇒c _ l c .right .⊥-preserving = BY.#-reflect (λ _ _ → Y.#-sym (c .proj₂ X.π₂))
  boolean-⇒c _ l c .left .func = l
  boolean-⇒c _ left c .left .∨-preserving {y} {y'} = BX.#-reflect suffices
       where
       suffices : ∀ x → (left .fun y XJ.∨ left .fun y') X.# x → left .fun (y YJ.∨ y') X.# x
       suffices x gy∨gy'#x =
         c .proj₁ (Y.#-sym (Y.#-distrib
           (Y.#-sym (c .proj₂ (X.#-mono (X.inl) x gy∨gy'#x)))
           (Y.#-sym (c .proj₂ (X.#-mono (X.inr) x gy∨gy'#x)))))
  boolean-⇒c _ _ c .left .⊥-preserving = BX.#-reflect (λ _ _ → c .proj₁ Y.π₁)
  boolean-⇒c _ _ c .conjugate = c

record _≃c_ {X Y : Obj} (f g : X ⇒c Y) : Prop where
  open preorder._=>_
  open _=>J_

  field
    right-eq : f .right ≃J g .right
    left-eq  : f .left  ≃J g .left

open _≃c_

open IsEquivalence
open preorder using (≃m-isEquivalence)

private
  module JS = join-semilattice

≃c-isEquivalence : ∀ {X Y} → IsEquivalence (_≃c_ {X} {Y})
≃c-isEquivalence .refl .right-eq = JS.≃m-isEquivalence .refl
≃c-isEquivalence .refl .left-eq = JS.≃m-isEquivalence .refl
≃c-isEquivalence .sym e .right-eq = JS.≃m-isEquivalence .sym (e .right-eq)
≃c-isEquivalence .sym e .left-eq = JS.≃m-isEquivalence .sym (e .left-eq)
≃c-isEquivalence .trans e₁ e₂ .right-eq = JS.≃m-isEquivalence .trans (e₁ .right-eq) (e₂ .right-eq)
≃c-isEquivalence .trans e₁ e₂ .left-eq = JS.≃m-isEquivalence .trans (e₁ .left-eq) (e₂ .left-eq)

idc : (X : Obj) → X ⇒c X
idc X .right = JS.id
idc X .left = JS.id
idc X .conjugate = refl-⇔

_∘c_ : ∀ {X Y Z : Obj} → Y ⇒c Z → X ⇒c Y → X ⇒c Z
(f ∘c g) .right = f .right JS.∘ g .right
(f ∘c g) .left = g .left JS.∘ f .left
(f ∘c g) .conjugate = trans-⇔ (f .conjugate) (g .conjugate)

∘c-cong : ∀ {X Y Z}{f₁ f₂ : Y ⇒c Z}{g₁ g₂ : X ⇒c Y} → f₁ ≃c f₂ → g₁ ≃c g₂ → (f₁ ∘c g₁) ≃c (f₂ ∘c g₂)
∘c-cong f₁≈f₂ g₁≈g₂ .right-eq = JS.∘-cong (f₁≈f₂ .right-eq) (g₁≈g₂ .right-eq)
∘c-cong f₁≈f₂ g₁≈g₂ .left-eq = JS.∘-cong (g₁≈g₂ .left-eq) (f₁≈f₂ .left-eq)

cat : Category (suc 0ℓ) 0ℓ 0ℓ
cat .Category.obj = Obj
cat .Category._⇒_ = _⇒c_
cat .Category._≈_ = _≃c_
cat .Category.isEquiv = ≃c-isEquivalence
cat .Category.id = idc
cat .Category._∘_ = _∘c_
cat .Category.∘-cong = ∘c-cong
cat .Category.id-left .right-eq = JS.id-left
cat .Category.id-left .left-eq = JS.id-right
cat .Category.id-right .right-eq = JS.id-right
cat .Category.id-right .left-eq = JS.id-left
cat .Category.assoc f g h .right-eq = JS.assoc (f .right) (g .right) (h .right)
cat .Category.assoc f g h .left-eq =
  JS.≃m-isEquivalence .sym (JS.assoc (h .left) (g .left) (f .left))

-- CMon enrichment
module _ {X Y : Obj} where
  open _=>_
  open preorder._=>_
  open preorder._≃m_

  private
    module YJ = JoinSemilattice (Y .joins)
    module XJ = JoinSemilattice (X .joins)

  εm : X ⇒c Y
  εm .right = join-semilattice.εm {X = X .joins} {Y = Y .joins}
  εm .left = join-semilattice.εm {X = Y .joins} {Y = X .joins}
  εm .conjugate .proj₁ _ = π₁ X
  εm .conjugate .proj₂ _ = π₂ Y

  _+m_ : X ⇒c Y → X ⇒c Y → X ⇒c Y
  (f +m g) .right = join-semilattice._+m_ (f .right) (g .right)
  (f +m g) .left = join-semilattice._+m_ (f .left) (g .left)
  (f +m g) .conjugate {x} {y} .proj₁ h =
    #-sym X (#-distrib X
      (#-sym X (conjugate f .proj₁ (≤-trans Y (∧-mono Y (≤-refl Y) (inl Y)) h)))
      (#-sym X (conjugate g .proj₁ (≤-trans Y (∧-mono Y (≤-refl Y) (inr Y)) h))))
  (f +m g) .conjugate {x} {y} .proj₂ h =
    #-distrib Y
      (conjugate f .proj₂ (#-mono X (inl X) x h))
      (conjugate g .proj₂ (#-mono X (inr X) x h))

  +m-cong : ∀ {f₁ f₂ g₁ g₂ : X ⇒c Y} → f₁ ≃c f₂ → g₁ ≃c g₂ → (f₁ +m g₁) ≃c (f₂ +m g₂)
  +m-cong f₁≃f₂ g₁≃g₂ .right-eq = join-semilattice.+m-cong (right-eq f₁≃f₂) (right-eq g₁≃g₂)
  +m-cong f₁≃f₂ g₁≃g₂ .left-eq = join-semilattice.+m-cong (left-eq f₁≃f₂) (left-eq g₁≃g₂)

  +m-comm : ∀ {f g} → (f +m g) ≃c (g +m f)
  +m-comm {f} {g} .right-eq = join-semilattice.+m-comm {f = f .right} {g .right}
  +m-comm {f} {g} .left-eq = join-semilattice.+m-comm {f = f .left} {g .left}

  +m-assoc : ∀ {f g h} → ((f +m g) +m h) ≃c (f +m (g +m h))
  +m-assoc {f} {g} {h} .right-eq = join-semilattice.+m-assoc {f = f .right} {g = g .right} {h = h .right}
  +m-assoc {f} {g} {h} .left-eq = join-semilattice.+m-assoc {f = f .left} {g = g .left} {h = h .left}

  +m-lunit : ∀ {f} → (εm +m f) ≃c f
  +m-lunit {f} .right-eq = join-semilattice.+m-lunit {f = f .right}
  +m-lunit {f} .left-eq = join-semilattice.+m-lunit {f = f .left}

module _ where
  open import commutative-monoid
  open CommutativeMonoid
  open _=>_
  open preorder._≃m_

  cmon-enriched : CMonEnriched cat
  cmon-enriched .CMonEnriched.homCM X Y .ε = εm
  cmon-enriched .CMonEnriched.homCM X Y ._+_ = _+m_
  cmon-enriched .CMonEnriched.homCM X Y .+-cong = +m-cong
  cmon-enriched .CMonEnriched.homCM X Y .+-lunit = +m-lunit
  cmon-enriched .CMonEnriched.homCM X Y .+-assoc = +m-assoc
  cmon-enriched .CMonEnriched.homCM X Y .+-comm = +m-comm
  cmon-enriched .CMonEnriched.comp-bilinear₁ {Z = Z} f₁ f₂ g .right-eq ._≃J_.eqfunc .eqfun x = Z .≃-refl
  cmon-enriched .CMonEnriched.comp-bilinear₁ f₁ f₂ g .left-eq ._≃J_.eqfunc .eqfun x = _=>J_.∨-preserving-≃ (g .left)
  cmon-enriched .CMonEnriched.comp-bilinear₂ {Z = Z} f g₁ g₂ .right-eq ._≃J_.eqfunc .eqfun x = _=>J_.∨-preserving-≃ (f .right)
  cmon-enriched .CMonEnriched.comp-bilinear₂ {X = X} f g₁ g₂ .left-eq ._≃J_.eqfunc .eqfun x = X .≃-refl
  cmon-enriched .CMonEnriched.comp-bilinear-ε₁ {Z = Z} f .right-eq ._≃J_.eqfunc .eqfun x = Z .≃-refl
  cmon-enriched .CMonEnriched.comp-bilinear-ε₁ f .left-eq ._≃J_.eqfunc .eqfun x = _=>J_.⊥-preserving-≃ (f .left)
  cmon-enriched .CMonEnriched.comp-bilinear-ε₂ {Z = Z} f .right-eq ._≃J_.eqfunc .eqfun x = _=>J_.⊥-preserving-≃ (f .right)
  cmon-enriched .CMonEnriched.comp-bilinear-ε₂ {X = X} f .left-eq ._≃J_.eqfunc .eqfun x = X .≃-refl

-- Terminal object
module _ where
  open IsTerminal
  open HasTerminal
  open preorder._≃m_

  𝟙 : Obj
  𝟙 .carrier = preorder.𝟙
  𝟙 .meets = meet-semilattice.𝟙
  𝟙 .joins = join-semilattice.𝟙
  𝟙 .∧-∨-distrib _ _ _ = tt

  𝟙-boolean : BooleanAlgebra 𝟙
  𝟙-boolean .BooleanAlgebra.¬ _ = ttU
  𝟙-boolean .BooleanAlgebra.complement-∨ = tt
  𝟙-boolean .BooleanAlgebra.complement-∧ = tt

  to-𝟙 : ∀ X → X ⇒c 𝟙
  to-𝟙 X .right = join-semilattice.terminal {X = X .joins}
  to-𝟙 X .left  = join-semilattice.initial  {X = X .joins}
  to-𝟙 X .conjugate .proj₁ _ = π₁ X
  to-𝟙 X .conjugate .proj₂ _ = tt

  terminal : HasTerminal cat
  terminal .witness = 𝟙
  terminal .is-terminal .to-terminal = to-𝟙 _
  terminal .is-terminal .to-terminal-ext {X} f .right-eq ._≃J_.eqfunc .eqfun _ = tt , tt
  terminal .is-terminal .to-terminal-ext {X} f .left-eq ._≃J_.eqfunc .eqfun _ =
    X .≤-bottom ,
    ≤-trans X (∧-idem X .proj₂) (#-mono X (≤-refl X) _ (f .conjugate .proj₁ tt))

-- Products
module _ where

  open HasProducts
  open import Data.Product using (proj₁; proj₂; _,_)
  open JoinSemilattice
  open MeetSemilattice
  open _=>_
  open preorder._≃m_

  _⊕_ : Obj → Obj → Obj
  (X ⊕ Y) .carrier = X .carrier × Y .carrier
  (X ⊕ Y) .meets = X .meets ⊕M Y .meets
  (X ⊕ Y) .joins = X .joins ⊕J Y .joins
  (X ⊕ Y) .∧-∨-distrib (x₁ , y₁) (x₂ , y₂) (x₃ , y₃) =
    ∧-∨-distrib X x₁ x₂ x₃ , ∧-∨-distrib Y y₁ y₂ y₃

  ⊕-boolean : ∀ {X Y} → BooleanAlgebra X → BooleanAlgebra Y → BooleanAlgebra (X ⊕ Y)
  ⊕-boolean BX BY .BooleanAlgebra.¬ (x , y) = BX .BooleanAlgebra.¬ x , BY .BooleanAlgebra.¬ y
  ⊕-boolean BX BY .BooleanAlgebra.complement-∨ = BX .BooleanAlgebra.complement-∨ , BY .BooleanAlgebra.complement-∨
  ⊕-boolean BX BY .BooleanAlgebra.complement-∧ = BX .BooleanAlgebra.complement-∧ , BY .BooleanAlgebra.complement-∧

  ⊕-# : ∀ {X Y} {x₁ x₂ y₁ y₂} → _#_ (X ⊕ Y) (x₁ , y₁) (x₂ , y₂) ⇔ _#_ X x₁ x₂ ∧ₚ _#_ Y y₁ y₂
  ⊕-# .proj₁ p = p
  ⊕-# .proj₂ p = p

  products : HasProducts cat
  products .prod = _⊕_
  products .p₁ {X} {Y} .right = join-semilattice.project₁ {X = X .joins} {Y = Y .joins}
  products .p₁ {X} {Y} .left = join-semilattice.inject₁ {X = X .joins} {Y = Y .joins}
  products .p₁ {X} {Y} .conjugate .proj₁ z#x = z#x , π₁ Y
  products .p₁ .conjugate .proj₂ = proj₁
  products .p₂ {X} {Y} .right = join-semilattice.project₂ {X = X .joins} {Y = Y .joins}
  products .p₂ {X} {Y} .left = join-semilattice.inject₂ {X = X .joins} {Y = Y .joins}
  products .p₂ {X} {Y} .conjugate .proj₁ z#y = π₁ X , z#y
  products .p₂ .conjugate .proj₂ = proj₂
  products .pair f g .right = join-semilattice.⟨ f .right , g .right ⟩
  products .pair f g .left = join-semilattice.[ f .left , g .left ]
  products .pair {X} {Y} {Z} f g .conjugate {x} {y₁ , y₂} .proj₁ h =
    #-sym X (#-distrib X
      (#-sym X (conjugate f .proj₁ (proj₁ (⊕-# {X = Y} {Y = Z} .proj₁ h))))
      (#-sym X (conjugate g .proj₁ (proj₂ (⊕-# {X = Y} {Y = Z} .proj₁ h)))))
  products .pair {X} {Y} {Z} f g .conjugate {x} {y₁ , y₂} .proj₂ h =
    ⊕-# {X = Y} {Y = Z} .proj₂
      (conjugate f .proj₂ (#-mono X (inl X) x h), conjugate g .proj₂ (#-mono X (inr X) x h))
  products .pair-cong f₁≈f₂ g₁≈g₂ .right-eq =
    join-semilattice.⟨⟩-cong (right-eq f₁≈f₂) (right-eq g₁≈g₂)
  products .pair-cong f₁≈f₂ g₁≈g₂ .left-eq =
    join-semilattice.[]-cong (left-eq f₁≈f₂) (left-eq g₁≈g₂)
  products .pair-p₁ f g .right-eq = join-semilattice.pair-p₁ (f .right) (g .right)
  products .pair-p₁ f g .left-eq = join-semilattice.inj₁-copair (f .left) (g .left)
  products .pair-p₂ f g .right-eq = join-semilattice.pair-p₂ (f .right) (g .right)
  products .pair-p₂ f g .left-eq = join-semilattice.inj₂-copair (f .left) (g .left)
  products .pair-ext f .right-eq = join-semilattice.pair-ext (f .right)
  products .pair-ext f .left-eq = join-semilattice.copair-ext (f .left)

  open HasProducts products

  -- CMon-enrichment means every object is a monoid
  conjunct : ∀ {X} → (X ⊕ X) ⇒c X
  conjunct = HasProducts.p₁ products +m HasProducts.p₂ products

  unit : ∀ {X} → 𝟙 ⇒c X
  unit = εm

  open import two using (Two; I; O)

  TWO : Obj
  TWO .carrier = two.Two-preorder
  TWO .meets .MeetSemilattice._∧_ = two._⊓_
  TWO .meets .MeetSemilattice.⊤ = I
  TWO .meets .MeetSemilattice.∧-isMeet = two.⊓-isMeet
  TWO .meets .MeetSemilattice.⊤-isTop = two.I-isTop
  TWO .joins .JoinSemilattice._∨_ = two._⊔_
  TWO .joins .JoinSemilattice.⊥ = O
  TWO .joins .JoinSemilattice.∨-isJoin = two.⊔-isJoin
  TWO .joins .JoinSemilattice.⊥-isBottom = two.O-isBottom
  TWO .∧-∨-distrib O _ _ = tt
  TWO .∧-∨-distrib I O O = tt
  TWO .∧-∨-distrib I O I = tt
  TWO .∧-∨-distrib I I _ = tt

  TWO-boolean : BooleanAlgebra TWO
  TWO-boolean .BooleanAlgebra.¬ = two.¬
  TWO-boolean .BooleanAlgebra.complement-∨ {x} = two.complement-∨ {x}
  TWO-boolean .BooleanAlgebra.complement-∧ {x} = two.complement-∧ {x}
