{-# OPTIONS --postfix-projections --safe --prop #-}

module join-semilattice where

open import Data.Product using (proj₁; proj₂; _,_)
open import Data.Unit using (tt) renaming (⊤ to Unit)
open import Level
open import basics
open import prop renaming (⊥ to ⊥p; _∨_ to _∨p_)
open import preorder using (Preorder; _×_)
open import prop-setoid using (IsEquivalence; module ≈-Reasoning)

record JoinSemilattice (A : Preorder) : Set (suc 0ℓ) where
  no-eta-equality
  open Preorder

  field
    _∨_          : A .Carrier → A .Carrier → A .Carrier
    ⊥            : A .Carrier
    ∨-isJoin     : IsJoin (A .≤-isPreorder) _∨_
    ⊥-isBottom   : IsBottom (A .≤-isPreorder) ⊥

  open IsJoin ∨-isJoin
    renaming (assoc to ∨-assoc; [_,_] to [_∨_]; mono to ∨-mono; comm to ∨-comm; cong to ∨-cong) public

  open IsBottom ⊥-isBottom public

  open IsMonoid (monoidOfJoin _ ∨-isJoin ⊥-isBottom)
    using (interchange)
    renaming (lunit to ∨-lunit; runit to ∨-runit)
    public

module _ {A B : Preorder} where
  open Preorder
  open preorder._=>_
  private
    module A = Preorder A
    module B = Preorder B

  record _=>_ (X : JoinSemilattice A) (Y : JoinSemilattice B) : Set where
    open JoinSemilattice
    open IsBottom
    field
      func : A preorder.=> B
      ∨-preserving : ∀ {x x'} → (func .fun (X ._∨_ x x')) B.≤ (Y ._∨_ (func .fun x) (func .fun x'))
      ⊥-preserving : func .fun (X .⊥) B.≤ Y .⊥

    ∨-preserving-≃ : ∀ {x x'} → func .fun (X ._∨_ x x') B.≃ Y ._∨_ (func .fun x) (func .fun x')
    ∨-preserving-≃ .proj₁ = ∨-preserving
    ∨-preserving-≃ .proj₂ = Y.[ func .mono X.inl , func .mono X.inr ]
      where module Y = IsJoin (Y .∨-isJoin)
            module X = IsJoin (X .∨-isJoin)

    ⊥-preserving-≃ : func .fun (X .⊥) B.≃ Y .⊥
    ⊥-preserving-≃ .proj₁ = ⊥-preserving
    ⊥-preserving-≃ .proj₂ = Y .⊥-isBottom .≤-bottom

  record _≃m_ {X : JoinSemilattice A} {Y : JoinSemilattice B} (f g : X => Y) : Prop where
    open _=>_
    field
      eqfunc : f .func preorder.≃m g .func

  open IsEquivalence
  open _≃m_
  open preorder._≃m_

  ≃m-isEquivalence : ∀ {X Y} → IsEquivalence (_≃m_ {X} {Y})
  ≃m-isEquivalence .refl .eqfunc .eqfun x = B.≃-refl
  ≃m-isEquivalence .sym e .eqfunc .eqfun x = B.≃-sym (e .eqfunc .eqfun x)
  ≃m-isEquivalence .trans e₁ e₂ .eqfunc .eqfun x = B.≃-trans (e₁ .eqfunc .eqfun x) (e₂ .eqfunc .eqfun x)

module _ where
  open Preorder
  open JoinSemilattice
  open _=>_
  open preorder._=>_

  id : ∀ {A}{X : JoinSemilattice A} → X => X
  id .func = preorder.id
  id {X} .∨-preserving = X .≤-refl
  id {X} .⊥-preserving = X .≤-refl

  _∘_ : ∀ {A B C}{X : JoinSemilattice A}{Y : JoinSemilattice B}{Z : JoinSemilattice C} →
           Y => Z → X => Y → X => Z
  (f ∘ g) .func = f .func preorder.∘ g .func
  _∘_ {C = C} f g .∨-preserving = C .≤-trans (f .func .mono (g .∨-preserving)) (f .∨-preserving)
  _∘_ {C = C} f g .⊥-preserving = C .≤-trans (f .func .mono (g .⊥-preserving)) (f .⊥-preserving)

  ⊥-map : ∀ {A}{B}{X : JoinSemilattice A}{Y : JoinSemilattice B} → X => Y
  ⊥-map {Y = Y} .func .fun y = Y .⊥
  ⊥-map {B = B} .func .mono _ = B .≤-refl
  ⊥-map {Y = Y} .∨-preserving = IsJoin.idem (Y .∨-isJoin) .proj₂
  ⊥-map {B = B} .⊥-preserving = B .≤-refl

  open _≃m_
  open preorder._≃m_

  ∘-cong : ∀ {A B C}{X : JoinSemilattice A}{Y : JoinSemilattice B}{Z : JoinSemilattice C}
             {f₁ f₂ : Y => Z} {g₁ g₂ : X => Y} →
             f₁ ≃m f₂ → g₁ ≃m g₂ → (f₁ ∘ g₁) ≃m (f₂ ∘ g₂)
  ∘-cong {A}{B}{C} {f₁ = f₁} f₁≃f₂ g₁≃g₂ .eqfunc .eqfun x =
    C .≃-trans (resp-≃ (f₁ .func) (g₁≃g₂ .eqfunc .eqfun x)) (f₁≃f₂ .eqfunc .eqfun _)

  id-left : ∀ {A B}{X : JoinSemilattice A}{Y : JoinSemilattice B} →
            {f : X => Y} → (id ∘ f) ≃m f
  id-left {A} {B} .eqfunc .eqfun x = B .≃-refl

  id-right : ∀ {A B}{X : JoinSemilattice A}{Y : JoinSemilattice B} →
            {f : X => Y} → (f ∘ id) ≃m f
  id-right {A} {B} .eqfunc .eqfun x = B .≃-refl

  assoc : ∀ {A B C D}
            {W : JoinSemilattice A}
            {X : JoinSemilattice B}
            {Y : JoinSemilattice C}
            {Z : JoinSemilattice D}
            (f : Y => Z) (g : X => Y) (h : W => X) →
            ((f ∘ g) ∘ h) ≃m (f ∘ (g ∘ h))
  assoc {D = D} f g h .eqfunc .eqfun x = D .≃-refl

  module _ {A B}{X : JoinSemilattice A}{Y : JoinSemilattice B} where
    private
      module B = Preorder B
      module Y = JoinSemilattice Y

    εm : X => Y
    εm .func .fun x = Y.⊥
    εm .func .mono _ = B.≤-refl
    εm .∨-preserving = Y.∨-lunit .proj₂
    εm .⊥-preserving = B.≤-refl

    _+m_ : X => Y → X => Y → X => Y
    (f +m g) .func .fun x = f .func .fun x Y.∨ g .func .fun x
    (f +m g) .func .mono x₁≤x₂ = Y.∨-mono (f .func .mono x₁≤x₂) (g .func .mono x₁≤x₂)
    (f +m g) .∨-preserving =
      B.≤-trans (Y.∨-mono (f .∨-preserving) (g .∨-preserving))
                (Y.interchange Y.∨-comm .proj₁)
    (f +m g) .⊥-preserving =
      B.≤-trans (Y.∨-mono (f .⊥-preserving) (g .⊥-preserving)) (Y.∨-lunit .proj₁)

    +m-cong : ∀ {f₁ f₂ g₁ g₂ : X => Y} → f₁ ≃m f₂ → g₁ ≃m g₂ → (f₁ +m g₁) ≃m (f₂ +m g₂)
    +m-cong f₁≃f₂ g₁≃g₂ .eqfunc .eqfun x = Y.∨-cong (f₁≃f₂ .eqfunc .eqfun x) (g₁≃g₂ .eqfunc .eqfun x)

    +m-comm : ∀ {f g} → (f +m g) ≃m (g +m f)
    +m-comm .eqfunc .eqfun x .proj₁ = Y.∨-comm
    +m-comm .eqfunc .eqfun x .proj₂ = Y.∨-comm

    +m-assoc : ∀ {f g h} → ((f +m g) +m h) ≃m (f +m (g +m h))
    +m-assoc .eqfunc .eqfun x = Y.∨-assoc

    +m-lunit : ∀ {f} → (εm +m f) ≃m f
    +m-lunit .eqfunc .eqfun x = Y.∨-lunit

  module _ {A B C}
           {X : JoinSemilattice A}{Y : JoinSemilattice B}{Z : JoinSemilattice C} where

    comp-bilinear₁ : ∀ (f₁ f₂ : Y => Z) (g : X => Y) →
                       ((f₁ +m f₂) ∘ g) ≃m ((f₁ ∘ g) +m (f₂ ∘ g))
    comp-bilinear₁ f₁ f₂ g .eqfunc .eqfun x = C .≃-refl

    comp-bilinear₂ : ∀ (f : Y => Z) (g₁ g₂ : X => Y) →
                       (f ∘ (g₁ +m g₂)) ≃m ((f ∘ g₁) +m (f ∘ g₂))
    comp-bilinear₂ f g₁ g₂ .eqfunc .eqfun x = ∨-preserving-≃ f

    comp-bilinear-ε₁ : ∀ (f : X => Y) → (εm ∘ f) ≃m εm {X = X} {Y = Z}
    comp-bilinear-ε₁ f .eqfunc .eqfun x = C .≃-refl

    comp-bilinear-ε₂ : ∀ (f : Y => Z) → (f ∘ εm) ≃m εm {X = X} {Y = Z}
    comp-bilinear-ε₂ f .eqfunc .eqfun x = ⊥-preserving-≃ f

------------------------------------------------------------------------------
-- One element semilattice, for use when there are no approximations
module _ where
  open Preorder
  open JoinSemilattice
  open _=>_
  open preorder._=>_

  𝟙 : JoinSemilattice preorder.𝟙
  𝟙 ._∨_ tt tt = tt
  𝟙 .⊥ = tt
  𝟙 .∨-isJoin .IsJoin.inl = tt
  𝟙 .∨-isJoin .IsJoin.inr = tt
  𝟙 .∨-isJoin .IsJoin.[_,_] tt tt = tt
  𝟙 .⊥-isBottom .IsBottom.≤-bottom = tt

  initial : ∀ {A}{X : JoinSemilattice A} → 𝟙 => X
  initial = ⊥-map

  terminal : ∀ {A}{X : JoinSemilattice A} → X => 𝟙
  terminal .func .fun _ = tt
  terminal .func .mono _ = tt
  terminal .∨-preserving = tt
  terminal .⊥-preserving = tt

  open _≃m_
  open preorder._≃m_

  terminal-unique : ∀ {A}(X : JoinSemilattice A) → (f g : X => 𝟙) → f ≃m g
  terminal-unique {A} X f g .eqfunc .eqfun x = _

  initial-unique : ∀ {A}(X : JoinSemilattice A) → (f g : 𝟙 => X) → f ≃m g
  initial-unique {A} X f g .eqfunc .eqfun tt =
    begin
      f .func .fun tt
    ≈⟨ ⊥-preserving-≃ f ⟩
      X .⊥
    ≈⟨ A .≃-sym (⊥-preserving-≃ g) ⟩
      g .func .fun tt
    ∎
    where open ≈-Reasoning (isEquivalence A)

------------------------------------------------------------------------------
-- Set-wide direct sums of JoinSemilattices
module _ (I : Set) {A : I -> Preorder} (X : (i : I) → JoinSemilattice (A i)) where
  open Preorder
  open JoinSemilattice
  open _=>_
  open preorder._=>_

  data FormalJoin : Set where
    bot  : FormalJoin
    el   : (i : I) → A i .Carrier → FormalJoin
    join : FormalJoin → FormalJoin → FormalJoin

  data _≤f_ : FormalJoin → FormalJoin → Set where
    ≤f-refl    : ∀ {j} → j ≤f j
    ≤f-trans   : ∀ {j₁ j₂ j₃} → j₁ ≤f j₂ → j₂ ≤f j₃ → j₁ ≤f j₃
    ≤f-el-mono : ∀ i {x₁ x₂} → A i ._≤_ x₁ x₂ → el i x₁ ≤f el i x₂
    ≤f-el-bot  : ∀ i → el i (X i .⊥) ≤f bot
    ≤f-el-join : ∀ i {x₁ x₂} → el i (X i ._∨_ x₁ x₂) ≤f join (el i x₁) (el i x₂)
    ≤f-bot     : ∀ {j} → bot ≤f j
    ≤f-inl     : ∀ {j₁ j₂} → j₁ ≤f join j₁ j₂
    ≤f-inr     : ∀ {j₁ j₂} → j₂ ≤f join j₁ j₂
    ≤f-case    : ∀ {j₁ j₂ j₃} → j₁ ≤f j₃ → j₂ ≤f j₃ → join j₁ j₂ ≤f j₃

  ⨁-preorder : Preorder
  ⨁-preorder .Carrier = FormalJoin
  ⨁-preorder ._≤_ j₁ j₂ = LiftS 0ℓ (j₁ ≤f j₂)
  ⨁-preorder .≤-isPreorder .IsPreorder.refl {x} = liftS (≤f-refl {x})
  ⨁-preorder .≤-isPreorder .IsPreorder.trans (liftS x) (liftS y) = liftS (≤f-trans x y)

  ⨁ : JoinSemilattice ⨁-preorder
  ⨁ ._∨_ = join
  ⨁ .⊥ = bot
  ⨁ .∨-isJoin .IsJoin.inl = liftS ≤f-inl
  ⨁ .∨-isJoin .IsJoin.inr = liftS ≤f-inr
  ⨁ .∨-isJoin .IsJoin.[_,_] (liftS x) (liftS y) = liftS (≤f-case x y)
  ⨁ .⊥-isBottom .IsBottom.≤-bottom = liftS ≤f-bot

  inj-⨁ : (i : I) → X i => ⨁
  inj-⨁ i .func .fun x = el i x
  inj-⨁ i .func .mono x = liftS (≤f-el-mono i x)
  inj-⨁ i .∨-preserving = liftS (≤f-el-join i)
  inj-⨁ i .⊥-preserving = liftS (≤f-el-bot i)

  module _ {B} (Z : JoinSemilattice B) (X=>Z : ∀ i → X i => Z) where
    private
      module Z = JoinSemilattice Z

    elim-⨁-func : ⨁-preorder .Carrier → B .Carrier
    elim-⨁-func bot = Z .⊥
    elim-⨁-func (el i x) = X=>Z i .func .fun x
    elim-⨁-func (join j₁ j₂) = Z ._∨_ (elim-⨁-func j₁) (elim-⨁-func j₂)

    elim-⨁-func-monotone : ∀ {j₁ j₂} → j₁ ≤f j₂ → B ._≤_ (elim-⨁-func j₁) (elim-⨁-func j₂)
    elim-⨁-func-monotone ≤f-refl = B .≤-refl
    elim-⨁-func-monotone (≤f-trans j₁≤j₂ j₂≤j₃) = B .≤-trans (elim-⨁-func-monotone j₁≤j₂) (elim-⨁-func-monotone j₂≤j₃)
    elim-⨁-func-monotone (≤f-el-mono i x₁≤x₂) = X=>Z i .func .mono x₁≤x₂
    elim-⨁-func-monotone (≤f-el-bot i) = X=>Z i .⊥-preserving
    elim-⨁-func-monotone (≤f-el-join i) = X=>Z i .∨-preserving
    elim-⨁-func-monotone ≤f-bot = Z.≤-bottom
    elim-⨁-func-monotone ≤f-inl = Z.inl
    elim-⨁-func-monotone ≤f-inr = Z.inr
    elim-⨁-func-monotone (≤f-case j₁≤j₃ j₂≤j₃) =
      Z.[ elim-⨁-func-monotone j₁≤j₃ ∨ elim-⨁-func-monotone j₂≤j₃ ]

    elim-⨁ : ⨁ => Z
    elim-⨁ .func .fun = elim-⨁-func
    elim-⨁ .func .mono (liftS x) = elim-⨁-func-monotone x
    elim-⨁ .∨-preserving = B .≤-refl
    elim-⨁ .⊥-preserving = B .≤-refl

------------------------------------------------------------------------------
-- Biproducts
module _ where
  open Preorder
  open JoinSemilattice
  open _=>_
  open preorder._=>_
  open _≃m_
  open preorder._≃m_

  _⊕_ : ∀ {A B} → JoinSemilattice A → JoinSemilattice B → JoinSemilattice (A × B)
  (X ⊕ Y) ._∨_ (x₁ , y₁) (x₂ , y₂) = (X ._∨_ x₁ x₂) , (Y ._∨_ y₁ y₂)
  (X ⊕ Y) .⊥ = X .⊥ , Y .⊥
  (X ⊕ Y) .∨-isJoin .IsJoin.inl = X .∨-isJoin .IsJoin.inl , Y .∨-isJoin .IsJoin.inl
  (X ⊕ Y) .∨-isJoin .IsJoin.inr = X .∨-isJoin .IsJoin.inr , Y .∨-isJoin .IsJoin.inr
  (X ⊕ Y) .∨-isJoin .IsJoin.[_,_] (x₁≤z₁ , y₁≤z₂) (x₂≤z₁ , y₂≤z₂) =
    X .∨-isJoin .IsJoin.[_,_] x₁≤z₁ x₂≤z₁ ,
    Y .∨-isJoin .IsJoin.[_,_] y₁≤z₂ y₂≤z₂
  (X ⊕ Y) .⊥-isBottom .IsBottom.≤-bottom = IsBottom.≤-bottom (X .⊥-isBottom) , IsBottom.≤-bottom (Y .⊥-isBottom)

  project₁ : ∀ {A B}{X : JoinSemilattice A}{Y : JoinSemilattice B} → (X ⊕ Y) => X
  project₁ .func .fun = proj₁
  project₁ .func .mono = proj₁
  project₁ {A} .∨-preserving = A .≤-refl
  project₁ {A} .⊥-preserving = A .≤-refl

  project₂ : ∀ {A B}{X : JoinSemilattice A}{Y : JoinSemilattice B} → (X ⊕ Y) => Y
  project₂ .func .fun = proj₂
  project₂ .func .mono = proj₂
  project₂ {B = B} .∨-preserving = B .≤-refl
  project₂ {B = B} .⊥-preserving = B .≤-refl

  ⟨_,_⟩ : ∀ {A B C}{X : JoinSemilattice A}{Y : JoinSemilattice B}{Z : JoinSemilattice C} → X => Y → X => Z → X => (Y ⊕ Z)
  ⟨ f , g ⟩ .func .fun x = f .func .fun x , g .func .fun x
  ⟨ f , g ⟩ .func .mono x≤x' = f .func .mono x≤x' , g .func .mono x≤x'
  ⟨ f , g ⟩ .∨-preserving = f .∨-preserving , g .∨-preserving
  ⟨ f , g ⟩ .⊥-preserving = f .⊥-preserving , g . ⊥-preserving

  ⟨⟩-cong : ∀ {A B C}{W : JoinSemilattice A} {X : JoinSemilattice B} {Y : JoinSemilattice C} →
           {f₁ f₂ : W => X} {g₁ g₂ : W => Y} →
           f₁ ≃m f₂ → g₁ ≃m g₂ → ⟨ f₁ , g₁ ⟩ ≃m ⟨ f₂ , g₂ ⟩
  ⟨⟩-cong f₁≈f₂ g₁≈g₂ .eqfunc .eqfun x .proj₁ .proj₁ = f₁≈f₂ .eqfunc .eqfun x .proj₁
  ⟨⟩-cong f₁≈f₂ g₁≈g₂ .eqfunc .eqfun x .proj₁ .proj₂ = g₁≈g₂ .eqfunc .eqfun x .proj₁
  ⟨⟩-cong f₁≈f₂ g₁≈g₂ .eqfunc .eqfun x .proj₂ .proj₁ = f₁≈f₂ .eqfunc .eqfun x .proj₂
  ⟨⟩-cong f₁≈f₂ g₁≈g₂ .eqfunc .eqfun x .proj₂ .proj₂ = g₁≈g₂ .eqfunc .eqfun x .proj₂

  pair-p₁ : ∀ {A B C}{X : JoinSemilattice A} {Y : JoinSemilattice B} {Z : JoinSemilattice C}
            (f : X => Y) (g : X => Z) →
            (project₁ ∘ ⟨ f , g ⟩) ≃m f
  pair-p₁ {B = B} f g .eqfunc .eqfun x = B .≃-refl

  pair-p₂ : ∀ {A B C}{X : JoinSemilattice A} {Y : JoinSemilattice B} {Z : JoinSemilattice C}
            (f : X => Y) (g : X => Z) →
            (project₂ ∘ ⟨ f , g ⟩) ≃m g
  pair-p₂ {C = C} f g .eqfunc .eqfun x = C .≃-refl

  pair-ext : ∀ {A B C}{X : JoinSemilattice A} {Y : JoinSemilattice B} {Z : JoinSemilattice C}
             (f : X => (Y ⊕ Z)) →
             ⟨ project₁ ∘ f , project₂ ∘ f ⟩ ≃m f
  pair-ext {B = B} {C = C} f .eqfunc .eqfun x = (B × C) .≃-refl

  inject₁ : ∀ {A B}{X : JoinSemilattice A}{Y : JoinSemilattice B} → X => (X ⊕ Y)
  inject₁ {Y = Y} .func .fun x = x , Y .⊥
  inject₁ {B = B} .func .mono x≤x' = x≤x' , B .≤-refl
  inject₁ {A}{Y = Y} .∨-preserving = A .≤-refl , IsJoin.idem (Y .∨-isJoin) .proj₂
  inject₁ {X}{Y} .⊥-preserving = X .≤-refl , Y .≤-refl

  inject₂ : ∀ {A B}{X : JoinSemilattice A}{Y : JoinSemilattice B} → Y => (X ⊕ Y)
  inject₂ {X = X} .func .fun y = X .⊥ , y
  inject₂ {A} .func .mono y≤y' = A. ≤-refl , y≤y'
  inject₂ {B = B}{X = X} .∨-preserving = IsJoin.idem (X .∨-isJoin) .proj₂ , B .≤-refl
  inject₂ {A}{B} .⊥-preserving = A .≤-refl , B .≤-refl

  [_,_] : ∀ {A B C}{X : JoinSemilattice A}{Y : JoinSemilattice B}{Z : JoinSemilattice C} →
          X => Z → Y => Z → (X ⊕ Y) => Z
  [_,_] {Z = Z} f g .func .fun (x , y) = Z ._∨_ (f .func .fun x) (g .func .fun y)
  [_,_] {Z = Z} f g .func .mono (x₁≤x₁' , x₂≤x₂') =
    IsJoin.mono (Z .∨-isJoin) (f .func .mono x₁≤x₁') (g .func .mono x₂≤x₂')
  [_,_] {C = C}{Z = Z} f g .∨-preserving {(x₁ , y₁)}{(x₂ , y₂)} =
    C .≤-trans (Z.∨-mono (f .∨-preserving) (g .∨-preserving))
               (Z.interchange Z.∨-comm .proj₁)
      where module Z = JoinSemilattice Z
  [_,_] {Z = Z} f g .⊥-preserving = Z[ f .⊥-preserving , g .⊥-preserving ]
    where open IsJoin (Z .∨-isJoin) renaming ([_,_] to Z[_,_])

  []-cong : ∀ {A B C}{X : JoinSemilattice A}{Y : JoinSemilattice B}{Z : JoinSemilattice C}
            {f₁ f₂ : X => Z} {g₁ g₂ : Y => Z} →
            f₁ ≃m f₂ → g₁ ≃m g₂ →
            [ f₁ , g₁ ] ≃m [ f₂ , g₂ ]
  []-cong {Z = Z} f₁≈f₂ g₁≈g₂ .eqfunc .eqfun (x , y) = Z.∨-cong (f₁≈f₂ .eqfunc .eqfun x) (g₁≈g₂ .eqfunc .eqfun y)
    where module Z = JoinSemilattice Z

  inj₁-copair : ∀ {A B C}
                  {X : JoinSemilattice A}{Y : JoinSemilattice B}{Z : JoinSemilattice C}
                  (f : X => Z) (g : Y => Z) →
                  ([ f , g ] ∘ inject₁) ≃m f
  inj₁-copair {C = C} {Y = Y} {Z = Z} f g .eqfunc .eqfun x =
    begin
      f .func .fun x Z.∨ g .func .fun (Y .⊥)
    ≈⟨ ∨-cong Z (C .≃-refl) (⊥-preserving-≃ g) ⟩
      f .func .fun x Z.∨ Z .⊥
    ≈⟨ ∨-runit Z ⟩
      f .func .fun x
    ∎
    where open ≈-Reasoning (isEquivalence C)
          module Z = JoinSemilattice Z

  inj₂-copair : ∀ {A B C}
                  {X : JoinSemilattice A}{Y : JoinSemilattice B}{Z : JoinSemilattice C}
                  (f : X => Z) (g : Y => Z) →
                  ([ f , g ] ∘ inject₂) ≃m g
  inj₂-copair {C = C} {X = X} {Z = Z} f g .eqfunc .eqfun y =
    begin
      f .func .fun (X .⊥) Z.∨ g .func .fun y
    ≈⟨ ∨-cong Z (⊥-preserving-≃ f) (C .≃-refl) ⟩
      Z .⊥ Z.∨ g .func .fun y
    ≈⟨ ∨-lunit Z ⟩
      g .func .fun y
    ∎
    where open ≈-Reasoning (isEquivalence C)
          module Z = JoinSemilattice Z

  copair-ext : ∀ {A B C}
                 {X : JoinSemilattice A}
                 {Y : JoinSemilattice B}
                 {Z : JoinSemilattice C}
                 (f : (X ⊕ Y) => Z) →
                 [ f ∘ inject₁ , f ∘ inject₂ ] ≃m f
  copair-ext {A} {B} {C} {X} {Y} {Z} f .eqfunc .eqfun (x , y) =
    begin
      f .func .fun (x , Y .⊥) Z.∨ f .func .fun (X .⊥ , y)
    ≈⟨ C .≃-sym (∨-preserving-≃ f) ⟩
      f .func .fun (x X.∨ X.⊥ , Y .⊥ Y.∨ y)
    ≈⟨ resp-≃ (f .func) (preorder.×-≃ {X = A} {Y = B} (∨-runit X) (∨-lunit Y)) ⟩
      f .func .fun (x , y)
    ∎
    where open ≈-Reasoning (isEquivalence C)
          module Z = JoinSemilattice Z
          module Y = JoinSemilattice Y
          module X = JoinSemilattice X

  proj₁-inverts-inj₁ : ∀ {A B}{X : JoinSemilattice A}{Y : JoinSemilattice B} → (project₁ {X = X}{Y} ∘ inject₁) ≃m id
  proj₁-inverts-inj₁ {A} ._≃m_.eqfunc .eqfun x = ≃-refl A

  proj₂-inverts-inj₂ : ∀ {A B}{X : JoinSemilattice A}{Y : JoinSemilattice B} → (project₂ {X = X}{Y} ∘ inject₂) ≃m id
  proj₂-inverts-inj₂ {A}{B} ._≃m_.eqfunc .eqfun x = ≃-refl B

  proj₁-zeroes-inj₂ : ∀ {A B}{X : JoinSemilattice A}{Y : JoinSemilattice B} → (project₁ {X = X}{Y} ∘ inject₂) ≃m ⊥-map
  proj₁-zeroes-inj₂ {A} ._≃m_.eqfunc .eqfun x = ≃-refl A

  proj₂-zeroes-inj₁ : ∀ {A B}{X : JoinSemilattice A}{Y : JoinSemilattice B} → (project₂ {X = X}{Y} ∘ inject₁) ≃m ⊥-map
  proj₂-zeroes-inj₁ {A}{B} ._≃m_.eqfunc .eqfun x = ≃-refl B

------------------------------------------------------------------------------
-- Lifting
module _ where
  open Preorder
  open preorder using (LCarrier; <_>; bottom)
  open JoinSemilattice
  open _=>_
  open preorder._=>_
  open _≃m_
  open preorder._≃m_

  -- The original preorder needn't have a bottom
  L₀ : ∀ {A _∨_} → IsJoin (A .≤-isPreorder) _∨_ → JoinSemilattice (preorder.L A)
  L₀ ∨-isJoin ._∨_ bottom bottom = bottom
  L₀ ∨-isJoin ._∨_ < x > bottom = < x >
  L₀ ∨-isJoin ._∨_ bottom < y > = < y >
  L₀ {A} {_∨_} ∨-isJoin ._∨_ < x >  < y > = < x ∨ y >
  L₀ ∨-isJoin .⊥ = bottom
  L₀ ∨-isJoin .∨-isJoin .IsJoin.inl {bottom} {bottom} = tt
  L₀ ∨-isJoin .∨-isJoin .IsJoin.inl {bottom} {< x >}  = tt
  L₀ {A} ∨-isJoin .∨-isJoin .IsJoin.inl {< x >}  {bottom} = A .≤-refl
  L₀ ∨-isJoin .∨-isJoin .IsJoin.inl {< x >}  {< y >}  = ∨-isJoin .IsJoin.inl
  L₀ ∨-isJoin .∨-isJoin .IsJoin.inr {bottom} {bottom} = tt
  L₀ {A} ∨-isJoin .∨-isJoin .IsJoin.inr {bottom} {< x >}  = A. ≤-refl
  L₀ ∨-isJoin .∨-isJoin .IsJoin.inr {< x >}  {bottom} = tt
  L₀ ∨-isJoin .∨-isJoin .IsJoin.inr {< x >}  {< y >}  = ∨-isJoin .IsJoin.inr
  L₀ ∨-isJoin .∨-isJoin .IsJoin.[_,_] {bottom}{bottom}{bottom} m₁ m₂ = tt
  L₀ ∨-isJoin .∨-isJoin .IsJoin.[_,_] {bottom}{bottom}{< z >}  m₁ m₂ = tt
  L₀ ∨-isJoin .∨-isJoin .IsJoin.[_,_] {bottom}{< y >} {z}      m₁ m₂ = m₂
  L₀ ∨-isJoin .∨-isJoin .IsJoin.[_,_] {< x >} {bottom}{z}      m₁ m₂ = m₁
  L₀ ∨-isJoin .∨-isJoin .IsJoin.[_,_] {< x >} {< y >} {< z >}  m₁ m₂ = ∨-isJoin .IsJoin.[_,_] m₁ m₂
  L₀ ∨-isJoin .⊥-isBottom .IsBottom.≤-bottom = tt

  L : ∀ {A} → JoinSemilattice A → JoinSemilattice (preorder.L A)
  L X = L₀ (X .∨-isJoin)

  L-map : ∀ {A B}{X : JoinSemilattice A}{Y : JoinSemilattice B} → X => Y → L X => L Y
  L-map m .func .fun bottom = bottom
  L-map m .func .fun < x > = < m .func .fun x >
  L-map m .func .mono {bottom} {bottom} _ = tt
  L-map m .func .mono {bottom} {< _ >} _ = tt
  L-map m .func .mono {< _ >} {< _ >} x₁≤x₂ = m .func .mono x₁≤x₂
  L-map m .∨-preserving {bottom} {bottom} = tt
  L-map {B = B} m .∨-preserving {bottom} {< _ >} = B .≤-refl
  L-map {B = B} m .∨-preserving {< x >} {bottom} = B .≤-refl
  L-map m .∨-preserving {< _ >} {< _ >} = m .∨-preserving
  L-map m .⊥-preserving = tt

  -- Lifting is /not/ a monad: L-unit is not ⊥-preserving

  L-join : ∀ {A}{X : JoinSemilattice A} → L (L X) => L X
  L-join .func .fun bottom = bottom
  L-join .func .fun < bottom > = bottom
  L-join .func .fun < < x > > = < x >
  L-join .func .mono {bottom} {bottom} _ = tt
  L-join .func .mono {bottom} {< bottom >} _ = tt
  L-join .func .mono {bottom} {< < _ > >} _ = tt
  L-join .func .mono {< bottom >} {< bottom >} _ = tt
  L-join .func .mono {< bottom >} {< < _ > >} _ = tt
  L-join .func .mono {< < _ > >} {< < _ > >} x≤x' = x≤x'
  L-join .∨-preserving {bottom} {bottom} = tt
  L-join .∨-preserving {bottom} {< bottom >} = tt
  L-join {A} .∨-preserving {bottom} {< < x > >} = A .≤-refl
  L-join .∨-preserving {< bottom >} {bottom} = tt
  L-join {A} .∨-preserving {< < _ > >} {bottom} = A .≤-refl
  L-join .∨-preserving {< bottom >} {< bottom >} = tt
  L-join {A} .∨-preserving {< bottom >} {< < x > >} = A .≤-refl
  L-join {A} .∨-preserving {< < _ > >} {< bottom >} = A .≤-refl
  L-join {A} .∨-preserving {< < _ > >} {< < _ > >} = A .≤-refl
  L-join .⊥-preserving = tt

  -- Lifting is a comonad in preorders with a bottom:
  L-counit : ∀ {A}{X : JoinSemilattice A} → L X => X
  L-counit {X = X} .func .fun bottom = X .⊥
  L-counit .func .fun < x > = x
  L-counit {X = X} .func .mono {bottom} _ = IsBottom.≤-bottom (X .⊥-isBottom)
  L-counit .func .mono {< _ >} {< _ >} x≤x' = x≤x'
  L-counit {X = X} .∨-preserving {bottom} {bottom} = IsJoin.idem (X .∨-isJoin) .proj₂
  L-counit {X = X} .∨-preserving {bottom} {< _ >} = ∨-lunit X .proj₂
  L-counit {X = X} .∨-preserving {< _ >} {bottom} = ∨-runit X .proj₂
  L-counit {A} .∨-preserving {< _ >} {< _ >} = A .≤-refl
  L-counit {A} .⊥-preserving = A .≤-refl

  L-dup : ∀ {A}{X : JoinSemilattice A} → L X => L (L X)
  L-dup .func .fun bottom = bottom
  L-dup .func .fun < x > = < < x > >
  L-dup .func .mono {bottom} {bottom} _ = tt
  L-dup .func .mono {bottom} {< _ >} _ = tt
  L-dup .func .mono {< _ >} {< _ >} x≤x' = x≤x'
  L-dup .∨-preserving {bottom} {bottom} = tt
  L-dup {A} .∨-preserving {bottom} {< _ >} = A .≤-refl
  L-dup {A} .∨-preserving {< _ >} {bottom} = A .≤-refl
  L-dup {A} .∨-preserving {< _ >} {< _ >} = A .≤-refl
  L-dup .⊥-preserving = tt

  L-costrength : ∀ {A B}{X : JoinSemilattice A}{Y : JoinSemilattice B} →
                 L (X ⊕ Y) => (X ⊕ L Y)
  L-costrength {X = X}{Y = Y} .func .fun bottom = (X ⊕ L Y) .⊥
  L-costrength .func .fun < x , y > = x , < y >
  L-costrength {A} .func .mono {bottom} {bottom} e = A .≤-refl , tt
  L-costrength {X = X} .func .mono {bottom} {< x >} e =
    X .⊥-isBottom .IsBottom.≤-bottom , tt
  L-costrength .func .mono {< x >} {< x₁ >} e = e
  L-costrength {X = X} .∨-preserving {bottom} {bottom} =
    (X .∨-isJoin .IsJoin.inr) , tt
  L-costrength {A} {B} {X} .∨-preserving {bottom} {< x >} =
    X .∨-isJoin .IsJoin.inr , B .≤-refl
  L-costrength {A} {B} {X} .∨-preserving {< x >} {bottom} =
    X .∨-isJoin .IsJoin.inl , B .≤-refl
  L-costrength {A} {B} .∨-preserving {< _ >} {< _ >} =
    A .≤-refl , B .≤-refl
  L-costrength {A} .⊥-preserving = A .≤-refl , tt

  L-costrength-natural : ∀ {A₁ A₂ B₁ B₂}
                         {X₁ : JoinSemilattice A₁} {X₂ : JoinSemilattice A₂}
                         {Y₁ : JoinSemilattice B₁} {Y₂ : JoinSemilattice B₂}
                         (f : X₁ => X₂) (g : Y₁ => Y₂) →
                         (⟨ f ∘ project₁ , L-map g ∘ project₂ ⟩ ∘ L-costrength {X = X₁} {Y = Y₁}) ≃m
                         (L-costrength {X = X₂} {Y = Y₂} ∘ L-map ⟨ f ∘ project₁ , g ∘ project₂ ⟩)
  L-costrength-natural {X₂ = X₂} f g .eqfunc .eqfun bottom .proj₁ =
    f .⊥-preserving , tt
  L-costrength-natural {X₂ = X₂} f g .eqfunc .eqfun bottom .proj₂ =
    X₂ .⊥-isBottom .IsBottom.≤-bottom , tt
  L-costrength-natural {A₂ = A₂} {B₂ = B₂} f g .eqfunc .eqfun < x , y > =
    (A₂ × B₂) .≃-refl

  L-costrength-p₂ : ∀ {A B}{X : JoinSemilattice A}{Y : JoinSemilattice B} →
                    (project₂ {X = X} {Y = L Y} ∘ L-costrength {X = X} {Y = Y}) ≃m L-map (project₂ {X = X} {Y = Y})
  L-costrength-p₂ .eqfunc .eqfun bottom = tt , tt
  L-costrength-p₂ {B = B} .eqfunc .eqfun < x , y > = B .≃-refl

  L-costrength-assoc : ∀ {A B}{X : JoinSemilattice A}{Y : JoinSemilattice B} →
                       ([ inject₁ {X = X} {Y = L Y} , L-costrength {X = X} {Y = Y} ] ∘ L-costrength {X = X} {Y = X ⊕ Y}) ≃m
                       (L-costrength {X = X} {Y = Y} ∘ L-map [ inject₁ {X = X} {Y = Y} , id {X = X ⊕ Y} ])
  L-costrength-assoc {A = A} {B = B} {X = X} {Y = Y} .eqfunc .eqfun bottom .proj₁ =
    X .∨-isJoin .IsJoin.[_,_] (A .≤-refl) (A .≤-refl) , tt
  L-costrength-assoc {A = A} {B = B} {X = X} {Y = Y} .eqfunc .eqfun bottom .proj₂ =
    X .∨-isJoin .IsJoin.inl , tt
  L-costrength-assoc {A = A} {B = B} {X = X} {Y = Y} .eqfunc .eqfun < x , (x' , y) > .proj₁ =
    A .≤-refl , Y .∨-isJoin .IsJoin.inr
  L-costrength-assoc {A = A} {B = B} {X = X} {Y = Y} .eqfunc .eqfun < x , (x' , y) > .proj₂ =
    A .≤-refl , Y .∨-isJoin .IsJoin.[_,_] (Y .⊥-isBottom .IsBottom.≤-bottom) (B .≤-refl)
