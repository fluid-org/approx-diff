{-# OPTIONS --prop --postfix-projections --safe #-}

module prop-setoid where

open import Level
open import prop
open import Data.Unit using (tt) renaming (⊤ to 𝟙S)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using () renaming (⊥ to 𝟘)
open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

record IsEquivalence {o e} {A : Set o} (_≈_ : A → A → Prop e) : Set (o ⊔ e) where
  field
    refl : ∀ {x} → x ≈ x
    sym  : ∀ {x y} → x ≈ y → y ≈ x
    trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
open IsEquivalence

⊤-isEquivalence : ∀ {o e} {A : Set o} → IsEquivalence {o} {e} {A} (λ _ _ → ⊤)
⊤-isEquivalence .refl = tt
⊤-isEquivalence .sym _ = tt
⊤-isEquivalence .trans _ _ = tt

⊎-isEquivalence : ∀ {o e} {A B : Set o} {_≈₁_ : A → A → Prop e} {_≈₂_ : B → B → Prop e} →
                  IsEquivalence _≈₁_ →
                  IsEquivalence _≈₂_ →
                  IsEquivalence (_≈₁_ ⊎R _≈₂_)
⊎-isEquivalence isEq₁ isEq₂ .refl {inj₁ x} = isEq₁ .refl
⊎-isEquivalence isEq₁ isEq₂ .refl {inj₂ y} = isEq₂ .refl
⊎-isEquivalence isEq₁ isEq₂ .sym {inj₁ a₁} {inj₁ a₂} = isEq₁ .sym
⊎-isEquivalence isEq₁ isEq₂ .sym {inj₂ b₁} {inj₂ b₂} = isEq₂ .sym
⊎-isEquivalence isEq₁ isEq₂ .trans {inj₁ _} {inj₁ _} {inj₁ _} = isEq₁ .trans
⊎-isEquivalence isEq₁ isEq₂ .trans {inj₂ _} {inj₂ _} {inj₂ _} = isEq₂ .trans

module ≈-Reasoning {o e} {A : Set o} {_≈_ : A → A → Prop e} (equiv : IsEquivalence _≈_) where

  infix  1 begin_
  infixr 2 _≈⟨_⟩_ _≈˘⟨_⟩_ _≡⟨⟩_
  infix  3 _∎

  begin_ : ∀ {x y : A}
    → x ≈ y
      -----
    → x ≈ y
  begin x≈y  =  x≈y

  _≡⟨⟩_ : ∀ (x : A) {y : A}
    → x ≈ y
      -----
    → x ≈ y
  x ≡⟨⟩ x≈y = x≈y

  _≈⟨_⟩_ : ∀ (x : A) {y z : A}
    → x ≈ y
    → y ≈ z
      -----
    → x ≈ z
  x ≈⟨ x≈y ⟩ y≈z  =  equiv .trans x≈y y≈z

  _≈˘⟨_⟩_ : ∀ (x : A) {y z : A}
    → y ≈ x
    → y ≈ z
      -----
    → x ≈ z
  x ≈˘⟨ y≈x ⟩ y≈z  =  equiv .trans (equiv .sym y≈x) y≈z

  _∎ : ∀ (x : A)
      -----
    → x ≈ x
  x ∎  =  equiv .refl

record Setoid o e : Set (suc (o ⊔ e)) where
  no-eta-equality
  infix 4 _≈_
  field
    Carrier : Set o
    _≈_     : Carrier → Carrier → Prop e
    isEquivalence : IsEquivalence _≈_
  open IsEquivalence isEquivalence public
open Setoid

record _⇒_ {o₁ e₁ o₂ e₂} (X : Setoid o₁ e₁) (Y : Setoid o₂ e₂) : Set (o₁ ⊔ o₂ ⊔ e₁ ⊔ e₂) where
  no-eta-equality
  private
    module X = Setoid X
    module Y = Setoid Y
  field
    func : X.Carrier → Y.Carrier
    func-resp-≈ : ∀ {x₁ x₂} → x₁ X.≈ x₂ → func x₁ Y.≈ func x₂
open _⇒_

module _ {o e} where

  record _≃m_ {X Y : Setoid o e} (f g : X ⇒ Y) : Prop (o ⊔ e) where
    private
      module X = Setoid X
      module Y = Setoid Y
    field
      func-eq : ∀ {x₁ x₂} → x₁ X.≈ x₂ → f .func x₁ Y.≈ g .func x₂
  open _≃m_

  ≃m-isEquivalence : ∀ {X Y : Setoid o e} → IsEquivalence (_≃m_ {X} {Y})
  ≃m-isEquivalence {X} {Y} .refl {f} .func-eq = f .func-resp-≈
  ≃m-isEquivalence {X} {Y} .sym {f} {g} f≈g .func-eq x₁≈x₂ =
    Setoid.sym Y (f≈g .func-eq (Setoid.sym X x₁≈x₂))
  ≃m-isEquivalence {X} {Y} .trans {f} {g} {h} f≈g g≈h .func-eq x₁≈x₂ =
    Setoid.trans Y (f≈g .func-eq x₁≈x₂) (g≈h .func-eq (Setoid.refl X))

  idS : ∀ (X : Setoid o e) → X ⇒ X
  idS X .func x = x
  idS X .func-resp-≈ e = e

  _∘S_ : ∀ {X Y Z : Setoid o e} → Y ⇒ Z → X ⇒ Y → X ⇒ Z
  (f ∘S g) .func x = f .func (g .func x)
  (f ∘S g) .func-resp-≈ e = f .func-resp-≈ (g .func-resp-≈ e)

  ∘S-cong : ∀ {X Y Z : Setoid o e} {f₁ f₂ : Y ⇒ Z} {g₁ g₂ : X ⇒ Y} →
    f₁ ≃m f₂  → g₁ ≃m g₂ → (f₁ ∘S g₁) ≃m (f₂ ∘S g₂)
  ∘S-cong f₁≈f₂ g₁≈g₂ .func-eq x₁≈x₂ =
    f₁≈f₂ .func-eq (g₁≈g₂ .func-eq x₁≈x₂)

  id-left : ∀ {X Y : Setoid o e} {f : X ⇒ Y} → (idS Y ∘S f) ≃m f
  id-left {X} {Y} {f} .func-eq = f .func-resp-≈

  id-right : ∀ {X Y : Setoid o e} {f : X ⇒ Y} → (f ∘S idS X) ≃m f
  id-right {X} {Y} {f} .func-eq = f .func-resp-≈

  assoc : ∀ {W X Y Z : Setoid o e} (f : Y ⇒ Z) (g : X ⇒ Y) (h : W ⇒ X) →
      ((f ∘S g) ∘S h) ≃m (f ∘S (g ∘S h))
  assoc f g h .func-eq w₁≈w₂ = f .func-resp-≈ (g .func-resp-≈ (h .func-resp-≈ w₁≈w₂))

module _ {o e} where

  𝟙 : Setoid o e
  𝟙 .Carrier = Lift _ 𝟙S
  𝟙 ._≈_ _ _ = ⊤
  𝟙 .isEquivalence .refl = tt
  𝟙 .isEquivalence .sym _ = tt
  𝟙 .isEquivalence .trans _ _ = tt

  to-𝟙 : ∀ {X : Setoid o e} → X ⇒ 𝟙
  to-𝟙 .func _ = lift tt
  to-𝟙 .func-resp-≈ _ = tt

  to-𝟙-unique : ∀ {X : Setoid o e} (f g : X ⇒ 𝟙) → f ≃m g
  to-𝟙-unique f g ._≃m_.func-eq _ = tt

  const : (X : Setoid o e) → X .Carrier → 𝟙 ⇒ X
  const X x .func _ = x
  const X x .func-resp-≈ tt = X .refl

open _≃m_

+-setoid : ∀ {a b} (X : Setoid a b) (Y : Setoid a b) → Setoid a b
+-setoid X Y .Carrier = X .Carrier ⊎ Y .Carrier
+-setoid X Y ._≈_ = X ._≈_ ⊎R Y ._≈_
+-setoid X Y .isEquivalence = ⊎-isEquivalence (X .isEquivalence) (Y .isEquivalence)

inject₁ : ∀ {o e} {X Y : Setoid o e} → X ⇒ +-setoid X Y
inject₁ .func = inj₁
inject₁ .func-resp-≈ p = p

inject₂ : ∀ {o e} {X Y : Setoid o e} → Y ⇒ +-setoid X Y
inject₂ .func = inj₂
inject₂ .func-resp-≈ p = p

copair : ∀ {o e} {X Y Z : Setoid o e} → X ⇒ Z → Y ⇒ Z → +-setoid X Y ⇒ Z
copair f g .func (inj₁ x) = f .func x
copair f g .func (inj₂ y) = g .func y
copair f g .func-resp-≈ {inj₁ x} {inj₁ x₁} e = f .func-resp-≈ e
copair f g .func-resp-≈ {inj₂ y} {inj₂ y₁} e = g .func-resp-≈ e

copair-cong : ∀ {o e} {X Y Z : Setoid o e}
                {f₁ f₂ : X ⇒ Z} {g₁ g₂ : Y ⇒ Z} →
                f₁ ≃m f₂ → g₁ ≃m g₂ →
                copair f₁ g₁ ≃m copair f₂ g₂
copair-cong f₁≈f₂ g₁≈g₂ .func-eq {inj₁ x} {inj₁ x₁} = f₁≈f₂ .func-eq
copair-cong f₁≈f₂ g₁≈g₂ .func-eq {inj₂ y} {inj₂ y₁} = g₁≈g₂ .func-eq

copair-in₁ : ∀ {o e} {X Y Z : Setoid o e}
               (f : X ⇒ Z) (g : Y ⇒ Z) →
               (copair f g ∘S inject₁) ≃m f
copair-in₁ f g .func-eq = f .func-resp-≈

copair-in₂ : ∀ {o e} {X Y Z : Setoid o e}
               (f : X ⇒ Z) (g : Y ⇒ Z) →
               (copair f g ∘S inject₂) ≃m g
copair-in₂ f g .func-eq = g .func-resp-≈

copair-ext : ∀ {o e} {X Y Z : Setoid o e}
             (f : +-setoid X Y ⇒ Z) →
             copair (f ∘S inject₁) (f ∘S inject₂) ≃m f
copair-ext f .func-eq {inj₁ x} {inj₁ x₁} = f .func-resp-≈
copair-ext f .func-eq {inj₂ y} {inj₂ y₁} = f .func-resp-≈

⊗-setoid : ∀ {a b c d} → Setoid a b → Setoid c d → Setoid (a ⊔ c) (b ⊔ d)
⊗-setoid X Y .Carrier = X .Carrier × Y .Carrier
⊗-setoid X Y ._≈_ (x₁ , y₁) (x₂ , y₂) = X ._≈_ x₁ x₂ ∧ Y ._≈_ y₁ y₂
⊗-setoid X Y .isEquivalence .refl .proj₁ = X .isEquivalence .refl
⊗-setoid X Y .isEquivalence .refl .proj₂ = Y .isEquivalence .refl
⊗-setoid X Y .isEquivalence .sym (x₁≈y₁ , _) .proj₁ = X .isEquivalence .sym x₁≈y₁
⊗-setoid X Y .isEquivalence .sym (_ , x₂≈y₂) .proj₂ = Y .isEquivalence .sym x₂≈y₂
⊗-setoid X Y .isEquivalence .trans (x₁≈y₁ , _) (y₁≈z₁ , _) .proj₁ = X .isEquivalence .trans x₁≈y₁ y₁≈z₁
⊗-setoid X Y .isEquivalence .trans (_ , x₂≈y₂) (_ , y₂≈z₂) .proj₂ = Y .isEquivalence .trans x₂≈y₂ y₂≈z₂

project₁ : ∀ {o e} {X Y : Setoid o e} → ⊗-setoid X Y ⇒ X
project₁ .func = proj₁
project₁ .func-resp-≈ = proj₁

project₂ : ∀ {o e} {X Y : Setoid o e} → ⊗-setoid X Y ⇒ Y
project₂ .func = proj₂
project₂ .func-resp-≈ = proj₂

pair : ∀ {o e} {X Y Z : Setoid o e} → X ⇒ Y → X ⇒ Z → X ⇒ ⊗-setoid Y Z
pair f g .func x = f .func x , g .func x
pair f g .func-resp-≈ e = f .func-resp-≈ e , g .func-resp-≈ e

pair-cong : ∀ {o e} {X Y Z : Setoid o e} {f₁ f₂ : X ⇒ Y} {g₁ g₂ : X ⇒ Z} →
  f₁ ≃m f₂ → g₁ ≃m g₂ → pair f₁ g₁ ≃m pair f₂ g₂
pair-cong f₁≈f₂ g₁≈g₂ .func-eq x₁≈x₂ .proj₁ = f₁≈f₂ .func-eq x₁≈x₂
pair-cong f₁≈f₂ g₁≈g₂ .func-eq x₁≈x₂ .proj₂ = g₁≈g₂ .func-eq x₁≈x₂

-- Strong coproducts
case : ∀ {o e} {W X Y Z : Setoid o e} →
          (⊗-setoid W X) ⇒ Z →
          (⊗-setoid W Y) ⇒ Z →
          (⊗-setoid W (+-setoid X Y)) ⇒ Z
case f g .func (w , inj₁ x) = f .func (w , x)
case f g .func (w , inj₂ y) = g .func (w , y)
case f g .func-resp-≈ {w₁ , inj₁ x₁} {w₂ , inj₁ x₂} (w₁≈w₂ , x₁≈x₂) = f .func-resp-≈ (w₁≈w₂ , x₁≈x₂)
case f g .func-resp-≈ {w₁ , inj₂ y₁} {w₂ , inj₂ y₂} (w₁≈w₂ , y₁≈y₂) = g .func-resp-≈ (w₁≈w₂ , y₁≈y₂)

-- Lists
--
-- FIXME: do this for a larger range of inductive datatypes
module _ {o e} where

  open import Data.List using (List; []; _∷_)

  List-≈ : (A : Setoid o e) → List (A .Carrier) → List (A .Carrier) → Prop e
  List-≈ A [] [] = ⊤
  List-≈ A [] (_ ∷ _) = ⊥
  List-≈ A (x ∷ xs) [] = ⊥
  List-≈ A (x ∷ xs) (y ∷ ys) = A ._≈_ x y ∧ List-≈ A xs ys

  List-≈-refl : ∀ A {xs : List (A .Carrier)} → List-≈ A xs xs
  List-≈-refl A {[]} = tt
  List-≈-refl A {x ∷ xs} = A .refl , List-≈-refl A

  List-≈-sym : ∀ A {xs ys : List (A .Carrier)} → List-≈ A xs ys → List-≈ A ys xs
  List-≈-sym A {[]} {[]} tt = tt
  List-≈-sym A {x ∷ xs} {y ∷ ys} (x≈y , xs≈ys)  = A .sym x≈y , List-≈-sym A xs≈ys

  List-≈-trans : ∀ A {xs ys zs : List (A .Carrier)} → List-≈ A xs ys → List-≈ A ys zs → List-≈ A xs zs
  List-≈-trans A {[]} {[]} {[]} tt tt = tt
  List-≈-trans A {x ∷ xs} {y ∷ ys} {z ∷ zs} (x≈y , xs≈ys) (y≈z , ys≈zs) =
    A .trans x≈y y≈z , List-≈-trans A xs≈ys ys≈zs

  ListS : Setoid o e → Setoid o e
  ListS A .Carrier = List (A .Carrier)
  ListS A ._≈_ = List-≈ A
  ListS A .isEquivalence .refl = List-≈-refl A
  ListS A .isEquivalence .sym = List-≈-sym A
  ListS A .isEquivalence .trans = List-≈-trans A

  nil : ∀ {A : Setoid o e} → (𝟙 {o} {e}) ⇒ ListS A
  nil .func _ = []
  nil .func-resp-≈ _ = tt

  cons : ∀ {A : Setoid o e} → ⊗-setoid A (ListS A) ⇒ ListS A
  cons .func (x , xs) = x ∷ xs
  cons .func-resp-≈ e = e

  foldr : ∀ {A B : Setoid o e} →
          𝟙 {o} {e} ⇒ B →
          ⊗-setoid A B ⇒ B →
          ListS A ⇒ B
  foldr nilCase consCase .func [] = nilCase .func (lift tt)
  foldr nilCase consCase .func (x ∷ xs) = consCase .func (x , foldr nilCase consCase .func xs)
  foldr nilCase consCase .func-resp-≈ {[]} {[]} tt = nilCase .func-resp-≈ tt
  foldr nilCase consCase .func-resp-≈ {x₁ ∷ xs₁} {x₂ ∷ xs₂} (x₁≈x₂ , xs₁≈xs₂) =
    consCase .func-resp-≈ (x₁≈x₂ , (foldr nilCase consCase .func-resp-≈ xs₁≈xs₂))

  foldrP : ∀ {A B C : Setoid o e} →
           C ⇒ B →
           ⊗-setoid (⊗-setoid C A) B ⇒ B →
           ⊗-setoid C (ListS A) ⇒ B
  foldrP nilCase consCase .func (c , []) = nilCase .func c
  foldrP nilCase consCase .func (c , x ∷ xs) = consCase .func ((c , x) , foldrP nilCase consCase .func (c , xs))
  foldrP nilCase consCase .func-resp-≈ {c₁ , []}       {c₂ , []}        (c₁≈c₂ , tt) = nilCase .func-resp-≈ c₁≈c₂
  foldrP nilCase consCase .func-resp-≈ {c₁ , x₁ ∷ xs₁} {c₂ , x₂ ∷ xs₂} (c₁≈c₂ , x₁≈x₂ , xs₁≈xs₂) =
    consCase .func-resp-≈ ((c₁≈c₂ , x₁≈x₂) , foldrP nilCase consCase .func-resp-≈ (c₁≈c₂ , xs₁≈xs₂))

  -- FIXME: the equations...

-- Structural polynomial functors on Setoid (idx-side description). An
-- IdxPoly is the idx-side projection of a Poly: parameter slots (base)
-- hold setoids rather than full Fam-objects. The interpretation
-- WIdx-of P P' "applies P' to the carrier W P" and so embeds the
-- recursive position (var) as W P. Equality is defined by structural
-- recursion on the polynomial, matching the List-≈ idiom and avoiding
-- any opaque shape comparison.
module _ {o e} where
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Product using (_×_; _,_; proj₁; proj₂)

  data IdxPoly : Set (suc (o ⊔ e)) where
    one  : IdxPoly
    param : Setoid o e → IdxPoly
    var  : IdxPoly
    _⊕_  : IdxPoly → IdxPoly → IdxPoly
    _⊗_  : IdxPoly → IdxPoly → IdxPoly

  mutual
    data W (P : IdxPoly) : Set (o ⊔ e) where
      sup : WIdx-of P P → W P

    WIdx-of : IdxPoly → IdxPoly → Set (o ⊔ e)
    WIdx-of P one         = Lift (o ⊔ e) 𝟙S
    WIdx-of P (param A)    = Lift e (A .Carrier)
    WIdx-of P var         = W P
    WIdx-of P (Q₁ ⊕ Q₂)   = WIdx-of P Q₁ ⊎ WIdx-of P Q₂
    WIdx-of P (Q₁ ⊗ Q₂)   = WIdx-of P Q₁ × WIdx-of P Q₂

  mutual
    W-≈ : (P : IdxPoly) → W P → W P → Prop (o ⊔ e)
    W-≈ P (sup i₁) (sup i₂) = WIdx-≈-of P P i₁ i₂

    WIdx-≈-of : (P Q : IdxPoly) → WIdx-of P Q → WIdx-of P Q → Prop (o ⊔ e)
    WIdx-≈-of P one         _          _          = ⊤
    WIdx-≈-of P (param A)    (lift x)   (lift y)   = LiftP o (A ._≈_ x y)
    WIdx-≈-of P var         w₁         w₂         = W-≈ P w₁ w₂
    WIdx-≈-of P (Q₁ ⊕ Q₂)   (inj₁ x₁)  (inj₁ x₂)  = WIdx-≈-of P Q₁ x₁ x₂
    WIdx-≈-of P (Q₁ ⊕ Q₂)   (inj₁ _)   (inj₂ _)   = ⊥
    WIdx-≈-of P (Q₁ ⊕ Q₂)   (inj₂ _)   (inj₁ _)   = ⊥
    WIdx-≈-of P (Q₁ ⊕ Q₂)   (inj₂ y₁)  (inj₂ y₂)  = WIdx-≈-of P Q₂ y₁ y₂
    WIdx-≈-of P (Q₁ ⊗ Q₂)   (x₁ , y₁)  (x₂ , y₂)  = WIdx-≈-of P Q₁ x₁ x₂ ∧ WIdx-≈-of P Q₂ y₁ y₂

  mutual
    W-≈-refl : ∀ P {w} → W-≈ P w w
    W-≈-refl P {sup i} = WIdx-≈-of-refl P P {i}

    WIdx-≈-of-refl : ∀ P Q {x} → WIdx-≈-of P Q x x
    WIdx-≈-of-refl P one          = tt
    WIdx-≈-of-refl P (param A) {lift x} = lift (A .refl {x})
    WIdx-≈-of-refl P var      {w}  = W-≈-refl P {w}
    WIdx-≈-of-refl P (Q₁ ⊕ Q₂) {inj₁ x} = WIdx-≈-of-refl P Q₁ {x}
    WIdx-≈-of-refl P (Q₁ ⊕ Q₂) {inj₂ y} = WIdx-≈-of-refl P Q₂ {y}
    WIdx-≈-of-refl P (Q₁ ⊗ Q₂) {x , y}  = WIdx-≈-of-refl P Q₁ {x} , WIdx-≈-of-refl P Q₂ {y}

  mutual
    W-≈-sym : ∀ P {w₁ w₂} → W-≈ P w₁ w₂ → W-≈ P w₂ w₁
    W-≈-sym P {sup i₁} {sup i₂} eq = WIdx-≈-of-sym P P {i₁} {i₂} eq

    WIdx-≈-of-sym : ∀ P Q {x y} → WIdx-≈-of P Q x y → WIdx-≈-of P Q y x
    WIdx-≈-of-sym P one         _  = tt
    WIdx-≈-of-sym P (param A) {lift x} {lift y} (lift eq) = lift (A .sym eq)
    WIdx-≈-of-sym P var       {w₁} {w₂} eq = W-≈-sym P {w₁} {w₂} eq
    WIdx-≈-of-sym P (Q₁ ⊕ Q₂) {inj₁ x₁} {inj₁ x₂} eq = WIdx-≈-of-sym P Q₁ eq
    WIdx-≈-of-sym P (Q₁ ⊕ Q₂) {inj₂ y₁} {inj₂ y₂} eq = WIdx-≈-of-sym P Q₂ eq
    WIdx-≈-of-sym P (Q₁ ⊗ Q₂) {x₁ , y₁} {x₂ , y₂} (e₁ , e₂) = WIdx-≈-of-sym P Q₁ e₁ , WIdx-≈-of-sym P Q₂ e₂

  mutual
    W-≈-trans : ∀ P {w₁ w₂ w₃} → W-≈ P w₁ w₂ → W-≈ P w₂ w₃ → W-≈ P w₁ w₃
    W-≈-trans P {sup _} {sup _} {sup _} e₁ e₂ = WIdx-≈-of-trans P P e₁ e₂

    WIdx-≈-of-trans : ∀ P Q {x y z} →
                      WIdx-≈-of P Q x y → WIdx-≈-of P Q y z → WIdx-≈-of P Q x z
    WIdx-≈-of-trans P one        _  _  = tt
    WIdx-≈-of-trans P (param A) {lift x} {lift y} {lift z} (lift e₁) (lift e₂) = lift (A .trans e₁ e₂)
    WIdx-≈-of-trans P var       {x} {y} {z} e₁ e₂ = W-≈-trans P {x} {y} {z} e₁ e₂
    WIdx-≈-of-trans P (Q₁ ⊕ Q₂) {inj₁ _} {inj₁ _} {inj₁ _} e₁ e₂ = WIdx-≈-of-trans P Q₁ e₁ e₂
    WIdx-≈-of-trans P (Q₁ ⊕ Q₂) {inj₂ _} {inj₂ _} {inj₂ _} e₁ e₂ = WIdx-≈-of-trans P Q₂ e₁ e₂
    WIdx-≈-of-trans P (Q₁ ⊗ Q₂) {_ , _} {_ , _} {_ , _} (e₁ , f₁) (e₂ , f₂) =
      WIdx-≈-of-trans P Q₁ e₁ e₂ , WIdx-≈-of-trans P Q₂ f₁ f₂

  WSetoid : IdxPoly → Setoid (o ⊔ e) (o ⊔ e)
  WSetoid P .Carrier = W P
  WSetoid P ._≈_     = W-≈ P
  WSetoid P .isEquivalence .refl {w}              = W-≈-refl P {w}
  WSetoid P .isEquivalence .sym {w₁} {w₂}         = W-≈-sym P {w₁} {w₂}
  WSetoid P .isEquivalence .trans {w₁} {w₂} {w₃}  = W-≈-trans P {w₁} {w₂} {w₃}

-- Equivalence relations from relations
module _ {o e} (A : Set o) (R : A → A → Prop e) where
  data EquivOfS : A → A → Set (o ⊔ e) where
    c-refl  : ∀ {a} → EquivOfS a a
    c-sym   : ∀ {a b} → EquivOfS a b → EquivOfS b a
    c-trans : ∀ {a b c} → EquivOfS a b → EquivOfS b c → EquivOfS a c
    c-base  : ∀ {a b} → R a b → EquivOfS a b

  EquivOf : A → A → Prop (o ⊔ e)
  EquivOf a₁ a₂ = LiftS (o ⊔ e) (EquivOfS a₁ a₂)

  EquivOf-isEquivalence : IsEquivalence EquivOf
  EquivOf-isEquivalence .refl = liftS c-refl
  EquivOf-isEquivalence .sym (liftS eq) = liftS (c-sym eq)
  EquivOf-isEquivalence .trans (liftS eq₁) (liftS eq₂) = liftS (c-trans eq₁ eq₂)

  rel→Setoid : Setoid o (o ⊔ e)
  rel→Setoid .Carrier = A
  rel→Setoid ._≈_ = EquivOf
  rel→Setoid .isEquivalence = EquivOf-isEquivalence

module _ {o e} {A : Set o} {R : A → A → Prop e} where
  EquivOf-intro : ∀ {a₁ a₂} → R a₁ a₂ → EquivOf A R a₁ a₂
  EquivOf-intro r = liftS (c-base r)

  elim-EquivOfS : ∀ {o' e'}
                    (X : Setoid o' e') (f : A → X .Carrier) →
                 (∀ {a₁ a₂} → R a₁ a₂ → X ._≈_ (f a₁) (f a₂)) →
                 ∀ {a₁} {a₂} → EquivOfS A R a₁ a₂ → X ._≈_ (f a₁) (f a₂)
  elim-EquivOfS X f base c-refl = X .refl
  elim-EquivOfS X f base (c-sym eq) = X .sym (elim-EquivOfS X f base eq)
  elim-EquivOfS X f base (c-trans eq₁ eq₂) =
    X .trans (elim-EquivOfS X f base eq₁) (elim-EquivOfS X f base eq₂)
  elim-EquivOfS X f base (c-base r) = base r

  rel-preserving-func : ∀ {o' e'}
                          (X : Setoid o' e')
                          (f : A → X .Carrier) →
                          (∀ {a₁ a₂} → R a₁ a₂ → X ._≈_ (f a₁) (f a₂)) →
                          rel→Setoid A R ⇒ X
  rel-preserving-func X f r .func = f
  rel-preserving-func X f r .func-resp-≈ (liftS eq) = elim-EquivOfS X f r eq
