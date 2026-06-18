{-# OPTIONS --prop --postfix-projections --safe #-}

module stable where

open import Level using (suc; 0ℓ)
open import Data.Unit using (tt) renaming (⊤ to Unit)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import prop using (∃ₛ; _∧_; _,_; ⊥; proj₁; proj₂)
open import basics using (IsPreorder; IsBottom; IsTop; IsMeet; IsJoin)
open import prop-setoid using (IsEquivalence; Setoid) renaming (_⇒_ to _⇒S_; _≃m_ to _≈s_)
open import categories using (Category; HasProducts)
open import functor using (Functor)
open import setoid-cat using (SetoidCat)

-- FIXME: this lot should be in preorder.agda
module _ {A : Set} {_≤_ : A → A → Prop} (≤-isPreorder : IsPreorder _≤_) where

  open IsPreorder ≤-isPreorder
    renaming (refl to ≤-refl; trans to ≤-trans)
    using (isEquivalence; _≃_)
  open IsEquivalence isEquivalence
    renaming (refl to ≃-refl; sym to ≃-sym; trans to ≃-trans)

  record IsMeetOf (x y meet : A) : Prop where
    field
      lower₁   : meet ≤ x
      lower₂   : meet ≤ y
      greatest : ∀ {z} → z ≤ x → z ≤ y → z ≤ meet
  open IsMeetOf

  meet-unique : ∀ {x y m₁ m₂} → IsMeetOf x y m₁ → IsMeetOf x y m₂ → m₁ ≃ m₂
  meet-unique is-meet₁ is-meet₂ .proj₁ = is-meet₂ .greatest (is-meet₁ .lower₁) (is-meet₁ .lower₂)
  meet-unique is-meet₁ is-meet₂ .proj₂ = is-meet₁ .greatest (is-meet₂ .lower₁) (is-meet₂ .lower₂)

  record HasMeetOf (x y : A) : Set where
    field
      meet    : A
      is-meet : IsMeetOf x y meet
    open IsMeetOf is-meet public

  record IsJoinOf (x y join : A) : Prop where
    field
      upper₁ : x ≤ join
      upper₂ : y ≤ join
      least  : ∀ {z} → x ≤ z → y ≤ z → join ≤ z

  record HasJoinOf (x y : A) : Set where
    field
      join    : A
      is-join : IsJoinOf x y join
    open IsJoinOf is-join public

  record HasRelativeBottom (x : A) : Set where
    field
      bot    : A
      is-bot : ∀ y → y ≤ x → bot ≤ y

------------------------------------------------------------------------------
-- LPosets are posets such that every principal downset is a bounded
-- lattice. Curiously, distributivity is not required?
record LPoset : Set (suc 0ℓ) where
  no-eta-equality
  field
    Carrier      : Set
    _≤_          : Carrier → Carrier → Prop
    ≤-isPreorder : IsPreorder _≤_

    bounded-⊥    : ∀ x → HasRelativeBottom ≤-isPreorder x
    bounded-∨    : ∀ {x y z} → x ≤ z → y ≤ z → HasJoinOf ≤-isPreorder x y
    bounded-∧    : ∀ {x y z} → x ≤ z → y ≤ z → HasMeetOf ≤-isPreorder x y

    -- FIXME: add a subset of "total" elements

  open IsPreorder ≤-isPreorder
    renaming (refl to ≤-refl; trans to ≤-trans)
    using (isEquivalence; _≃_) public
  open IsEquivalence isEquivalence
    renaming (refl to ≃-refl; sym to ≃-sym; trans to ≃-trans) public
open LPoset


-- Stable functions are monotone functions that satisfy a stability
-- property.
record Stable (A B : LPoset) : Set where
  private
    module A = LPoset A
    module B = LPoset B
  field
    func : A.Carrier → B.Carrier
    mono : ∀ {a₁ a₂} → a₁ A.≤ a₂ → func a₁ B.≤ func a₂
    stable : ∀ a b₀ → b₀ B.≤ func a →
               ∃ₛ A.Carrier λ a₀ →
                 (a₀ A.≤ a) ∧ (b₀ B.≤ func a₀) ∧
                 (∀ a₀' → a₀' A.≤ a → b₀ B.≤ func a₀' → a₀ A.≤ a₀')
  func-resp-≈ : ∀ {a₁ a₂} → a₁ A.≃ a₂ → func a₁ B.≃ func a₂
  func-resp-≈ a₁≈a₂ .proj₁ = mono (a₁≈a₂ .proj₁)
  func-resp-≈ a₁≈a₂ .proj₂ = mono (a₁≈a₂ .proj₂)
open Stable

record _≈_ {A B : LPoset} (f g : Stable A B) : Prop where
  private
    module B = LPoset B
  field
    *≈* : ∀ {a} → f .func a B.≃ g .func a
open _≈_

-- TODO: if two functions are equal (up to the preorder), then their
-- stability witnesses are equal too.
--
-- Also, we get a galois connection on the principal downsets


id : ∀ A → Stable A A
id A .func a = a
id A .mono a₁≤a₂ = a₁≤a₂
id A .stable a b₀ b₀≤a = b₀ , b₀≤a , A .≤-refl , λ a₀' a₀'≤a b₀≤a₀' → b₀≤a₀'

_∘_ : ∀ {A B C} → Stable B C → Stable A B → Stable A C
_∘_ {A} {B} {C} f g .func a = f .func (g .func a)
_∘_ {A} {B} {C} f g .mono a₁≤a₂ = f .mono (g .mono a₁≤a₂)
_∘_ {A} {B} {C} f g .stable a c₀ c₀≤fga =
  let b₀ , b₀≤ga , c₀≤fb₀ , b₀-least = f .stable (g .func a) c₀ c₀≤fga in
  let a₀ , a₀≤a  , b₀≤ga₀ , a₀-least = g .stable a b₀ b₀≤ga in
  a₀ , a₀≤a , C .≤-trans c₀≤fb₀ (f .mono b₀≤ga₀) ,
  λ a₀' a₀'≤a c₀≤fga₀' → a₀-least a₀' a₀'≤a (b₀-least (g .func a₀') (g .mono a₀'≤a) c₀≤fga₀')

cat : Category (suc 0ℓ) 0ℓ 0ℓ
cat .Category.obj = LPoset
cat .Category._⇒_ = Stable
cat .Category._≈_ = _≈_
cat .Category.isEquiv {A} {B} .IsEquivalence.refl .*≈* = B .≃-refl
cat .Category.isEquiv {A} {B} .IsEquivalence.sym eq .*≈* = B .≃-sym (eq .*≈*)
cat .Category.isEquiv {A} {B} .IsEquivalence.trans eq₁ eq₂ .*≈* = B .≃-trans (eq₁ .*≈*) (eq₂ .*≈*)
cat .Category.id = id
cat .Category._∘_ = _∘_
cat .Category.∘-cong {A} {B} {C} {f₁} f₁≈f₂ g₁≈g₂ .*≈* = C .≃-trans (func-resp-≈ f₁ (g₁≈g₂ .*≈*)) (f₁≈f₂ .*≈*)
cat .Category.id-left {A} {B} .*≈* = B .≃-refl
cat .Category.id-right {A} {B} .*≈* = B .≃-refl
cat .Category.assoc {A} {B} {C} {D} f g h .*≈* = D .≃-refl

------------------------------------------------------------------------------
-- Products

open HasMeetOf
open IsMeetOf
open HasRelativeBottom
open HasJoinOf
open IsJoinOf

_[×]_ : LPoset → LPoset → LPoset
(X [×] Y) .Carrier = X .Carrier × Y .Carrier
(A [×] B) ._≤_ (x₁ , y₁) (x₂ , y₂) = (A ._≤_ x₁ x₂) ∧ (B ._≤_ y₁ y₂)
(A [×] B) .≤-isPreorder .IsPreorder.refl = A .≤-refl , B .≤-refl
(A [×] B) .≤-isPreorder .IsPreorder.trans (x₁≤y₁ , x₂≤y₂) (y₁≤z₁ , y₂≤z₂) =
    A .≤-trans x₁≤y₁ y₁≤z₁ , B .≤-trans x₂≤y₂ y₂≤z₂
(A [×] B) .bounded-∧ {x₁ , y₁} {x₂ , y₂} {x , y} (x₁≤x , y₁≤y) (x₂≤x , y₂≤y) .meet =
  A .bounded-∧ x₁≤x x₂≤x .meet ,
  B .bounded-∧ y₁≤y y₂≤y .meet
(A [×] B) .bounded-∧ {x₁ , y₁} {x₂ , y₂} {x , y} (x₁≤x , y₁≤y) (x₂≤x , y₂≤y) .is-meet .lower₁ =
  A .bounded-∧ x₁≤x x₂≤x .is-meet .lower₁ ,
  B .bounded-∧ y₁≤y y₂≤y .is-meet .lower₁
(A [×] B) .bounded-∧ {x₁ , y₁} {x₂ , y₂} {x , y} (x₁≤x , y₁≤y) (x₂≤x , y₂≤y) .is-meet .lower₂ =
  A .bounded-∧ x₁≤x x₂≤x .is-meet .lower₂ ,
  B .bounded-∧ y₁≤y y₂≤y .is-meet .lower₂
(A [×] B) .bounded-∧ {x₁ , y₁} {x₂ , y₂} {x , y} (x₁≤x , y₁≤y) (x₂≤x , y₂≤y) .is-meet .greatest {xz , yz} (xz≤x₁ , yz≤y₁) (xz≤x₂ , yz≤y₂) =
  A .bounded-∧ _ _ .is-meet .greatest xz≤x₁ xz≤x₂ ,
  B .bounded-∧ _ _ .is-meet .greatest yz≤y₁ yz≤y₂
(X [×] Y) .bounded-⊥ (x , y) .bot = (X .bounded-⊥ x .bot) , (Y .bounded-⊥ y .bot)
(X [×] Y) .bounded-⊥ (x , y) .is-bot (x' , y') (x'≤x , y'≤y) =
  bounded-⊥ X x .is-bot x' x'≤x , bounded-⊥ Y y .is-bot y' y'≤y
(X [×] Y) .bounded-∨ {x₁ , y₁} {x₂ , y₂} {x , y} (x₁≤x , y₁≤y) (x₂≤x , y₂≤y) .join = (X .bounded-∨ x₁≤x x₂≤x .join) , (Y .bounded-∨ y₁≤y y₂≤y .join)
(X [×] Y) .bounded-∨ {x₁ , y₁} {x₂ , y₂} {x , y} (x₁≤x , y₁≤y) (x₂≤x , y₂≤y) .is-join .upper₁ = (bounded-∨ X _ _ .is-join .upper₁) , (bounded-∨ Y _ _ .is-join .upper₁)
(X [×] Y) .bounded-∨ {x₁ , y₁} {x₂ , y₂} {x , y} (x₁≤x , y₁≤y) (x₂≤x , y₂≤y) .is-join .upper₂ = bounded-∨ X _ _ .is-join .upper₂ , bounded-∨ Y _ _ .is-join .upper₂
(X [×] Y) .bounded-∨ {x₁ , y₁} {x₂ , y₂} {x , y} (x₁≤x , y₁≤y) (x₂≤x , y₂≤y) .is-join .least (x₁≤z , y₁≤z) (x₂≤z , y₂≤z) =
  (bounded-∨ X _ _ .is-join .least x₁≤z x₂≤z) , (bounded-∨ Y _ _ .is-join .least y₁≤z y₂≤z)

project₁ : ∀ {A B} → Stable (A [×] B) A
project₁ .func = proj₁
project₁ .mono (a≤a' , _) = a≤a'
project₁ {A} {B} .stable (a , b) a₀ a₀≤a =
  (a₀ , B .bounded-⊥ b .bot) , (a₀≤a , B .bounded-⊥ b .is-bot b (B .≤-refl)) , (A .≤-refl) ,
  (λ (a₀' , b') (a₀'≤a , b'≤b) a₀≤a₀' → a₀≤a₀' , B .bounded-⊥ b .is-bot b' b'≤b)

project₂ : ∀ {A B} → Stable (A [×] B) B
project₂ .func = proj₂
project₂ .mono (_ , b≤b') = b≤b'
project₂ {A} {B} .stable (a , b) b₀ b₀≤b =
  let ⊥a = A .bounded-⊥ a in
  (⊥a .bot , b₀) , (⊥a .is-bot _ (A .≤-refl) , b₀≤b) , (B .≤-refl) ,
  (λ (a₀' , b') (a₀'≤a , b'≤b) b₀≤b' → ⊥a .is-bot a₀' a₀'≤a , b₀≤b')

pair : ∀ {A B C} → Stable A B → Stable A C → Stable A (B [×] C)
pair {A} {B} {C} f g .func a = f .func a , g .func a
pair {A} {B} {C} f g .mono z = f .mono z , g .mono z
pair {A} {B} {C} f g .stable a (b₀ , c₀) (b₀≤fa , c₀≤ga) =
  let a₁ , a₁≤a , b₀≤fa₁ , a₁-least = f .stable a b₀ b₀≤fa in
  let a₂ , a₂≤a , c₀≤ga₂ , a₂-least = g .stable a c₀ c₀≤ga in
  let a₁∨a₂ = A .bounded-∨ a₁≤a a₂≤a in
  a₁∨a₂ .join , a₁∨a₂ .least a₁≤a a₂≤a ,
  (B .≤-trans b₀≤fa₁ (f .mono (a₁∨a₂ .upper₁)) , C .≤-trans c₀≤ga₂ (g .mono (a₁∨a₂ .upper₂))) ,
  λ a₀' a₀'≤a ϕ → a₁∨a₂ .least (a₁-least a₀' a₀'≤a (ϕ .proj₁)) (a₂-least a₀' a₀'≤a (ϕ .proj₂))

pair-cong : ∀ {A B C} {f₁ f₂ : Stable A B} {g₁ g₂ : Stable A C} → f₁ ≈ f₂ → g₁ ≈ g₂ → pair f₁ g₁ ≈ pair f₂ g₂
pair-cong f₁≈f₂ g₁≈g₂ .*≈* .proj₁ = f₁≈f₂ .*≈* .proj₁ , g₁≈g₂ .*≈* .proj₁
pair-cong f₁≈f₂ g₁≈g₂ .*≈* .proj₂ = f₁≈f₂ .*≈* .proj₂ , g₁≈g₂ .*≈* .proj₂

products : HasProducts cat
products .HasProducts.prod = _[×]_
products .HasProducts.p₁ = project₁
products .HasProducts.p₂ = project₂
products .HasProducts.pair = pair
products .HasProducts.pair-cong = pair-cong
products .HasProducts.pair-p₁ {A} {B} {C} f g .*≈* = B .≃-refl
products .HasProducts.pair-p₂ {A} {B} {C} f g .*≈* = C .≃-refl
products .HasProducts.pair-ext {A} {B} {C} f .*≈* = (B [×] C) .≃-refl

-- terminal object
𝟙 : LPoset
𝟙 .Carrier = Unit
𝟙 ._≤_ _ _ = prop.⊤
𝟙 .≤-isPreorder = record
                   { refl = λ {x} → prop.tt ; trans = λ {x} {y} {z} _ _ → prop.tt }
𝟙 .bounded-⊥ = λ x → record { bot = tt ; is-bot = λ y _ → prop.tt }
𝟙 .bounded-∨ = λ _ _ →
                  record
                  { join = tt
                  ; is-join =
                      record
                      { upper₁ = prop.tt
                      ; upper₂ = prop.tt
                      ; least = λ {z = z₁} _ _ → prop.tt
                      }
                  }
𝟙 .bounded-∧ = λ _ _ →
                  record
                  { meet = tt
                  ; is-meet =
                      record
                      { lower₁ = prop.tt
                      ; lower₂ = prop.tt
                      ; greatest = λ {z = z₁} _ _ → prop.tt
                      }
                  }

-- Need a ⊥ element under every element
terminal : ∀ {A} → Stable A 𝟙
terminal .func _ = _
terminal .mono _ = _
terminal {A} .stable a _ _ =
  A .bounded-⊥ a .bot , A. bounded-⊥ a .is-bot a (A .≤-refl) , _ , λ ⊥' ⊥'≤a _ → A .bounded-⊥ a .is-bot ⊥' ⊥'≤a

------------------------------------------------------------------------------
-- Sums are where the bottom elements start to separate. There is not
-- necessarily a "global" ⊥, or "global" joins.

open import Data.Sum using (inj₁; inj₂; _⊎_)

-- FIXME: this extends to Set-wide coproducts. What about colimits?

_[+]_ : LPoset → LPoset → LPoset
(X [+] Y) .Carrier = X .Carrier ⊎ Y .Carrier
(X [+] Y) ._≤_ (inj₁ x₁) (inj₁ x₂) = X ._≤_ x₁ x₂
(X [+] Y) ._≤_ (inj₂ y₁) (inj₁ x₂) = ⊥
(X [+] Y) ._≤_ (inj₁ x₁) (inj₂ y₂) = ⊥
(X [+] Y) ._≤_ (inj₂ y₁) (inj₂ y₂) = Y ._≤_ y₁ y₂
(X [+] Y) .≤-isPreorder .IsPreorder.refl {inj₁ x} = X .≤-refl
(X [+] Y) .≤-isPreorder .IsPreorder.refl {inj₂ y} = Y .≤-refl
(X [+] Y) .≤-isPreorder .IsPreorder.trans {inj₁ x} {inj₁ y} {inj₁ z} x≤y y≤z = X .≤-trans x≤y y≤z
(X [+] Y) .≤-isPreorder .IsPreorder.trans {inj₂ x} {inj₂ y} {inj₂ z} x≤y y≤z = Y .≤-trans x≤y y≤z
(X [+] Y) .bounded-⊥ (inj₁ x) .bot = inj₁ (X .bounded-⊥ x .bot)
(X [+] Y) .bounded-⊥ (inj₁ x) .is-bot (inj₁ x') x'≤x = bounded-⊥ X x .is-bot x' x'≤x
(X [+] Y) .bounded-⊥ (inj₂ y) .bot = inj₂ (Y .bounded-⊥ y .bot)
(X [+] Y) .bounded-⊥ (inj₂ y) .is-bot (inj₂ y') y'≤y = bounded-⊥ Y y .is-bot y' y'≤y
(X [+] Y) .bounded-∧ {inj₁ x₁} {inj₁ x₂} {inj₁ x} x₁≤x x₂≤x .meet = inj₁ (X .bounded-∧ x₁≤x x₂≤x .meet)
(X [+] Y) .bounded-∧ {inj₁ x₁} {inj₁ x₂} {inj₁ x} x₁≤x x₂≤x .is-meet .lower₁ = X .bounded-∧ _ _ .lower₁
(X [+] Y) .bounded-∧ {inj₁ x₁} {inj₁ x₂} {inj₁ x} x₁≤x x₂≤x .is-meet .lower₂ = X .bounded-∧ _ _ .lower₂
(X [+] Y) .bounded-∧ {inj₁ x₁} {inj₁ x₂} {inj₁ x} x₁≤x x₂≤x .is-meet .greatest {inj₁ z} z≤x₁ z≤x₂ = X. bounded-∧ _ _ .greatest z≤x₁ z≤x₂
(X [+] Y) .bounded-∧ {inj₂ y₁} {inj₂ y₂} {inj₂ y} y₁≤y y₂≤y .meet = inj₂ (Y .bounded-∧ y₁≤y y₂≤y .meet)
(X [+] Y) .bounded-∧ {inj₂ y₁} {inj₂ y₂} {inj₂ y} y₁≤y y₂≤y .is-meet .lower₁ = Y .bounded-∧ _ _ .lower₁
(X [+] Y) .bounded-∧ {inj₂ y₁} {inj₂ y₂} {inj₂ y} y₁≤y y₂≤y .is-meet .lower₂ = Y .bounded-∧ _ _ .lower₂
(X [+] Y) .bounded-∧ {inj₂ y₁} {inj₂ y₂} {inj₂ y} y₁≤y y₂≤y .is-meet .greatest {inj₂ z} z≤y₁ z≤y₂ = Y .bounded-∧ _ _ .greatest z≤y₁ z≤y₂
(X [+] Y) .bounded-∨ {inj₁ x₁} {inj₁ x₂} {inj₁ x} x₁≤x x₂≤x .join = inj₁ (X .bounded-∨ x₁≤x x₂≤x .join)
(X [+] Y) .bounded-∨ {inj₁ x₁} {inj₁ x₂} {inj₁ x} x₁≤x x₂≤x .is-join .upper₁ = X .bounded-∨ _ _ .upper₁
(X [+] Y) .bounded-∨ {inj₁ x₁} {inj₁ x₂} {inj₁ x} x₁≤x x₂≤x .is-join .upper₂ = X .bounded-∨ _ _ .upper₂
(X [+] Y) .bounded-∨ {inj₁ x₁} {inj₁ x₂} {inj₁ x} x₁≤x x₂≤x .is-join .least {inj₁ z} x₁≤z x₂≤z = X .bounded-∨ _ _ .least x₁≤z x₂≤z
(X [+] Y) .bounded-∨ {inj₂ y₁} {inj₂ y₂} {inj₂ y} y₁≤y y₂≤y .join = inj₂ (Y .bounded-∨ y₁≤y y₂≤y .join)
(X [+] Y) .bounded-∨ {inj₂ y₁} {inj₂ y₂} {inj₂ y} y₁≤y y₂≤y .is-join .upper₁ = Y .bounded-∨ _ _ .upper₁
(X [+] Y) .bounded-∨ {inj₂ y₁} {inj₂ y₂} {inj₂ y} y₁≤y y₂≤y .is-join .upper₂ = Y .bounded-∨ _ _ .upper₂
(X [+] Y) .bounded-∨ {inj₂ y₁} {inj₂ y₂} {inj₂ y} y₁≤y y₂≤y .is-join .least {inj₂ z} y₁≤z y₂≤z = Y .bounded-∨ _ _ .least y₁≤z y₂≤z

inject₁ : ∀ {A B} → Stable A (A [+] B)
inject₁ .func = inj₁
inject₁ .mono a≤a' = a≤a'
inject₁ {A} {B} .stable a (inj₁ a₀) a₀≤a =
  a₀ , a₀≤a , A .≤-refl , λ a₀' _ a₀≤a₀' → a₀≤a₀'

inject₂ : ∀ {A B} → Stable B (A [+] B)
inject₂ .func = inj₂
inject₂ .mono b≤b' = b≤b'
inject₂ {A} {B} .stable b (inj₂ b₀) b₀≤b =
  b₀ , b₀≤b , B .≤-refl , λ b₀' _ b₀≤b₀' → b₀≤b₀'

copair : ∀ {A B C} → Stable A C → Stable B C → Stable (A [+] B) C
copair {A} {B} {C} f g .func (inj₁ a) = f .func a
copair {A} {B} {C} f g .func (inj₂ b) = g .func b
copair {A} {B} {C} f g .mono {inj₁ a} {inj₁ a'} a≤a' = f .mono a≤a'
copair {A} {B} {C} f g .mono {inj₂ b} {inj₂ b'} b≤b' = g .mono b≤b'
copair {A} {B} {C} f g .stable (inj₁ a) c₀ c₀≤fa =
  let a₀ , a₀≤a , c₀≤fa , a₀-least = f .stable a c₀ c₀≤fa in
  inj₁ a₀ , a₀≤a , c₀≤fa , λ { (inj₁ x) y z → a₀-least x y z }
copair {A} {B} {C} f g .stable (inj₂ b) c₀ c₀≤gb =
  let a₀ , a₀≤a , c₀≤gb , b₀-least = g .stable b c₀ c₀≤gb in
  inj₂ a₀ , a₀≤a , c₀≤gb , (λ { (inj₂ x) y z → b₀-least x y z })

-- Conjecture: if we take the full subcategory of preorders with
-- bounded meets and joins then it is a (reverse) tangent category.

------------------------------------------------------------------------------
-- Every setoid gives a "flat" LPoset with no approximation information

Flat : Setoid 0ℓ 0ℓ → LPoset
Flat A .Carrier = A .Setoid.Carrier
Flat A ._≤_ = A .Setoid._≈_
Flat A .≤-isPreorder .IsPreorder.refl = A .Setoid.refl
Flat A .≤-isPreorder .IsPreorder.trans = A .Setoid.trans
Flat A .bounded-⊥ a .bot = a
Flat A .bounded-⊥ a .is-bot _ = A .Setoid.sym
Flat A .bounded-∨ {x₁}{x₂}{x} x₁≈x x₂≈x .join = x
Flat A .bounded-∨ {x₁} {x₂} {x} x₁≈x x₂≈x .is-join .upper₁ = x₁≈x
Flat A .bounded-∨ {x₁} {x₂} {x} x₁≈x x₂≈x .is-join .upper₂ = x₂≈x
Flat A .bounded-∨ {x₁} {x₂} {x} x₁≈x x₂≈x .is-join .least x₁≈z x₂≈z = A .Setoid.trans (A .Setoid.sym x₁≈x) x₁≈z
Flat A .bounded-∧ {x₁} {x₂} {x} x₁≈x x₂≈x .meet = x
Flat A .bounded-∧ {x₁} {x₂} {x} x₁≈x x₂≈x .is-meet .lower₁ = A .Setoid.sym x₁≈x
Flat A .bounded-∧ {x₁} {x₂} {x} x₁≈x x₂≈x .is-meet .lower₂ = A .Setoid.sym x₂≈x
Flat A .bounded-∧ {x₁} {x₂} {x} x₁≈x x₂≈x .is-meet .greatest z≈x₁ z≈x₂ = A .Setoid.trans z≈x₁ x₁≈x

FlatF : ∀ {A B} → A ⇒S B → Stable (Flat A) (Flat B)
FlatF {A} {B} f .func = f ._⇒S_.func
FlatF {A} {B} f .mono = f ._⇒S_.func-resp-≈
FlatF {A} {B} f .stable a b₀ b₀≈fa = a , A .Setoid.refl , b₀≈fa , λ a₀' z z₁ → A .Setoid.sym z

FlatF-cong : ∀ {A B} {f₁ f₂ : A ⇒S B} → f₁ ≈s f₂ → FlatF f₁ ≈ FlatF f₂
FlatF-cong {A} {B} f₁≈f₂ .*≈* =
  f₁≈f₂ ._≈s_.func-eq (A .Setoid.refl) ,
  B .Setoid.sym (f₁≈f₂ ._≈s_.func-eq (A .Setoid.refl))

Setoid→LPoset : Functor (SetoidCat 0ℓ 0ℓ) cat
Setoid→LPoset .Functor.fobj = Flat
Setoid→LPoset .Functor.fmor = FlatF
Setoid→LPoset .Functor.fmor-cong = FlatF-cong
Setoid→LPoset .Functor.fmor-id {A} .*≈* = A .Setoid.refl , A .Setoid.refl
Setoid→LPoset .Functor.fmor-comp {A} {B} {C} f g .*≈* .proj₁ = C .Setoid.refl
Setoid→LPoset .Functor.fmor-comp {A} {B} {C} f g .*≈* .proj₂ = C .Setoid.refl

-- FIXME: preserves products and coproducts

------------------------------------------------------------------------------
-- Lifting. Adds a new global bottom element

data L-carrier (A : Set) : Set where
  `⊥ : L-carrier A
  `↑ : A → L-carrier A

L : LPoset → LPoset
L A .Carrier = L-carrier (A .Carrier)
L A ._≤_ `⊥     _     = prop.⊤
L A ._≤_ (`↑ x) `⊥     = prop.⊥
L A ._≤_ (`↑ x) (`↑ y) = A ._≤_ x y
L A .≤-isPreorder .IsPreorder.refl {`⊥} = _
L A .≤-isPreorder .IsPreorder.refl {`↑ x} = A .≤-refl
L A .≤-isPreorder .IsPreorder.trans {`⊥} {y} {z} x≤y y≤z = _
L A .≤-isPreorder .IsPreorder.trans {`↑ x} {`↑ y} {`↑ z} x≤y y≤z = A .≤-trans x≤y y≤z
L A .bounded-⊥ x .bot = `⊥
L A .bounded-⊥ x .is-bot y _ = prop.tt
L A .bounded-∨ {`⊥} {`⊥} {`⊥} _ _ .join = `⊥
L A .bounded-∨ {`⊥} {`⊥} {`⊥} _ _ .is-join = record { }
L A .bounded-∨ {`⊥} {`⊥} {`↑ x} _ _ .join = `⊥
L A .bounded-∨ {`⊥} {`⊥} {`↑ x} _ _ .is-join = record { }
L A .bounded-∨ {`⊥} {`↑ x₂} {`↑ x} _ x₂≤x .join = `↑ x₂
L A .bounded-∨ {`⊥} {`↑ x₂} {`↑ x} _ x₂≤x .is-join = record { upper₁ = prop.tt; upper₂ = A .≤-refl; least = λ {z} z₁ z₂ → z₂ }
L A .bounded-∨ {`↑ x₁} {`⊥} {`↑ x} x₁≤x _ .join = `↑ x₁
L A .bounded-∨ {`↑ x₁} {`⊥} {`↑ x} x₁≤x _ .is-join = record { upper₁ = A .≤-refl; upper₂ = prop.tt; least = λ {z} z₁ z₂ → z₁ }
L A .bounded-∨ {`↑ x₁} {`↑ x₂} {`↑ x} x₁≤x x₂≤x .join = `↑ (A .bounded-∨ x₁≤x x₂≤x .join)
L A .bounded-∨ {`↑ x₁} {`↑ x₂} {`↑ x} x₁≤x x₂≤x .is-join .upper₁ = bounded-∨ A _ _ .is-join .upper₁
L A .bounded-∨ {`↑ x₁} {`↑ x₂} {`↑ x} x₁≤x x₂≤x .is-join .upper₂ = bounded-∨ A _ _ .is-join .upper₂
L A .bounded-∨ {`↑ x₁} {`↑ x₂} {`↑ x} x₁≤x x₂≤x .is-join .least {`↑ z} x₁≤z x₂≤z = bounded-∨ A _ _ .is-join .least x₁≤z x₂≤z
L A .bounded-∧ {`⊥} {_} {_} x₁≤x x₂≤x .meet = `⊥
L A .bounded-∧ {`⊥} {_} {_} x₁≤x x₂≤x .is-meet .lower₁ = _
L A .bounded-∧ {`⊥} {_} {_} x₁≤x x₂≤x .is-meet .lower₂ = _
L A .bounded-∧ {`⊥} {_} {_} x₁≤x x₂≤x .is-meet .greatest {`⊥} = _
L A .bounded-∧ {`↑ x₁} {`⊥} {`↑ x} _ _ .meet = `⊥
L A .bounded-∧ {`↑ x₁} {`⊥} {`↑ x} _ _ .is-meet .lower₁ = _
L A .bounded-∧ {`↑ x₁} {`⊥} {`↑ x} _ _ .is-meet .lower₂ = _
L A .bounded-∧ {`↑ x₁} {`⊥} {`↑ x} _ _ .is-meet .greatest _ ϕ = ϕ
L A .bounded-∧ {`↑ x₁} {`↑ x₂} {`↑ x} x₁≤x x₂≤x .meet = `↑ (A .bounded-∧ x₁≤x x₂≤x .meet)
L A .bounded-∧ {`↑ x₁} {`↑ x₂} {`↑ x} x₁≤x x₂≤x .is-meet .lower₁ = bounded-∧ A _ _ .is-meet .lower₁
L A .bounded-∧ {`↑ x₁} {`↑ x₂} {`↑ x} x₁≤x x₂≤x .is-meet .lower₂ = bounded-∧ A _ _ .is-meet .lower₂
L A .bounded-∧ {`↑ x₁} {`↑ x₂} {`↑ x} x₁≤x x₂≤x .is-meet .greatest {`⊥} ϕ ψ = _
L A .bounded-∧ {`↑ x₁} {`↑ x₂} {`↑ x} x₁≤x x₂≤x .is-meet .greatest {`↑ x₃} = bounded-∧ A _ _ .is-meet .greatest

L-unit : ∀ {A} → Stable A (L A)
L-unit .func = `↑
L-unit .mono a≤a' = a≤a'
L-unit {A} .stable a `⊥ _ = bounded-⊥ A a .bot ,
                             bounded-⊥ A a .is-bot a (≤-isPreorder A .IsPreorder.refl) ,
                             prop.tt , (λ a₀' z z₁ → bounded-⊥ A a .is-bot a₀' z)
L-unit {A} .stable a (`↑ a₀) a₀≤a =
  a₀ , a₀≤a , ≤-isPreorder A .IsPreorder.refl , (λ a₀' z z₁ → z₁)

L-functorial : ∀ {A B} → Stable A B → Stable (L A) (L B)
L-functorial f .func `⊥ = `⊥
L-functorial f .func (`↑ x) = `↑ (f .func x)
L-functorial f .mono {`⊥} {_} _ = _
L-functorial f .mono {`↑ x₁} {`↑ x₂} ϕ = f .mono ϕ
L-functorial f .stable `⊥ `⊥ x = `⊥ , prop.tt , prop.tt , (λ a₀' _ _ → prop.tt)
L-functorial f .stable (`↑ x₁) `⊥ x = `⊥ , prop.tt , prop.tt , (λ a₀' _ _ → prop.tt)
L-functorial f .stable (`↑ a) (`↑ b₀) b₀≤fa =
  let a₀ , a₀≤a , b₀≤fa₀ , a₀-least = f .stable a b₀ b₀≤fa in
  `↑ a₀ , a₀≤a , b₀≤fa₀ , λ { (`↑ a₀') → a₀-least a₀' }

L-join : ∀ {A} → Stable (L (L A)) (L A)
L-join .func `⊥ = `⊥
L-join .func (`↑ `⊥) = `⊥
L-join .func (`↑ (`↑ x)) = `↑ x
L-join .mono {`⊥} {_} ϕ = _
L-join .mono {`↑ `⊥} {`↑ x₁} ϕ = _
L-join .mono {`↑ (`↑ x)} {`↑ (`↑ x₁)} ϕ = ϕ
L-join .stable `⊥ `⊥ x = `⊥ , _ , _ , λ a₀' _ _ → prop.tt
L-join .stable (`↑ `⊥) `⊥ x = `⊥ , _ , _ , λ a₀' _ _ → prop.tt
L-join .stable (`↑ (`↑ x₁)) `⊥ x = `⊥ , prop.tt , prop.tt , (λ a₀' _ _ → prop.tt)
L-join {A} .stable (`↑ (`↑ x₁)) (`↑ x₂) x₂≤x₁ = `↑ (`↑ x₂) , x₂≤x₁ , A .≤-refl , λ { (`↑ (`↑ _)) _ ϕ → ϕ }

L-strong : ∀ {A B} → Stable (A [×] L B) (L (A [×] B))
L-strong .func (a , `⊥) = `⊥
L-strong .func (a , `↑ b) = `↑ (a , b)
L-strong .mono {a₁ , `⊥} {_} ϕ = _
L-strong .mono {a₁ , `↑ b₁} {a₂ , `↑ b₂} ϕ = ϕ
L-strong {A} {B} .stable (a , `⊥) `⊥ x =
  (A .bounded-⊥ a .bot , `⊥) ,
  (A .bounded-⊥ a .is-bot a (A .≤-refl) , _) ,
  _ ,
  λ { (a₀' , `⊥) (a₀'≤a , _) z → (bounded-⊥ A a .is-bot a₀' a₀'≤a) , _ }
L-strong {A} {B} .stable (a , `↑ b) `⊥ x =
  (A .bounded-⊥ a .bot , `⊥) ,
  (A .bounded-⊥ a .is-bot a (A .≤-refl) , _) ,
  _ ,
  λ { (a₀' , `⊥) (a₀'≤a , _) z → (bounded-⊥ A a .is-bot a₀' a₀'≤a) , _;
      (a₀' , `↑ b₀') (a₀≤a , b≤b₀') _ → (bounded-⊥ A a .is-bot a₀' a₀≤a) , _ }
L-strong {A} {B} .stable (a , `↑ b) (`↑ (a₀ , b₀)) ϕ =
  (a₀ , `↑ b₀) , ϕ , (A .≤-refl , B .≤-refl) ,
  λ { (a₀' , `↑ b₀') y z → z }


-- Plan:
--   3. Embed fully faithfully into Fam(LatGal)
--      which relies on every downset being a lattice
--   4. What properties and structure are preserved?
--      - sum
--      - product ?
--      - flat sets
--      - is lifting laxly preserved?

------------------------------------------------------------------------------
-- Getting the Lattice for each element of an LPoset

import galois
import preorder
open import meet-semilattice using (MeetSemilattice)
open import join-semilattice using (JoinSemilattice)

open galois using (_⇒g_; Obj)
open _⇒g_

-- Every element of the LPoset has an associated lattice of approximations
lattice : (X : LPoset) → X .Carrier → galois.Obj
lattice X x .Obj.carrier .preorder.Preorder.Carrier = ∃ₛ (X .Carrier) λ δx → X ._≤_ δx x
lattice X x .Obj.carrier .preorder.Preorder._≤_ (δx₁ , _) (δx₂ , _) = X ._≤_ δx₁ δx₂
lattice X x .Obj.carrier .preorder.Preorder.≤-isPreorder .IsPreorder.refl = X .≤-refl
lattice X x .Obj.carrier .preorder.Preorder.≤-isPreorder .IsPreorder.trans = X .≤-trans
lattice X x .Obj.meets .MeetSemilattice._∧_ (x₁ , x₁≤x) (x₂ , x₂≤x) =
  X .bounded-∧ x₁≤x x₂≤x .meet ,
  X .≤-trans (bounded-∧ X _ _ .is-meet .lower₂) x₂≤x
lattice X x .Obj.meets .MeetSemilattice.⊤ = x , X .≤-refl
lattice X x .Obj.meets .MeetSemilattice.∧-isMeet .IsMeet.π₁ = bounded-∧ X _ _ .is-meet .lower₁
lattice X x .Obj.meets .MeetSemilattice.∧-isMeet .IsMeet.π₂ = bounded-∧ X _ _ .is-meet .lower₂
lattice X x .Obj.meets .MeetSemilattice.∧-isMeet .IsMeet.⟨_,_⟩ = bounded-∧ X _ _ .is-meet .greatest
lattice X x .Obj.meets .MeetSemilattice.⊤-isTop .IsTop.≤-top {_ , x₁≤x} = x₁≤x
lattice X x .Obj.joins .JoinSemilattice._∨_ (x₁ , x₁≤x) (x₂ , x₂≤x) =
  X .bounded-∨ x₁≤x x₂≤x .join ,
  X .bounded-∨ x₁≤x x₂≤x .least x₁≤x x₂≤x
lattice X x .Obj.joins .JoinSemilattice.⊥ =
  X .bounded-⊥ x .bot , X .bounded-⊥ x .is-bot x (X .≤-refl)
lattice X x .Obj.joins .JoinSemilattice.∨-isJoin .IsJoin.inl = bounded-∨ X _ _ .is-join .upper₁
lattice X x .Obj.joins .JoinSemilattice.∨-isJoin .IsJoin.inr = bounded-∨ X _ _ .is-join .upper₂
lattice X x .Obj.joins .JoinSemilattice.∨-isJoin .IsJoin.[_,_] = bounded-∨ X _ _ .is-join .least
lattice X x .Obj.joins .JoinSemilattice.⊥-isBottom .IsBottom.≤-bottom {x₁ , x₁≤x} = bounded-⊥ X x .is-bot x₁ x₁≤x


-- Every morphism of LPosets yields a Galois connection!
morphism : ∀ (X Y : LPoset) (f : Stable X Y) x → lattice X x ⇒g lattice Y (f .func x)
morphism X Y f x .right .preorder._=>_.fun (δx , δx≤x) = f .func δx , f .mono δx≤x
morphism X Y f x .right .preorder._=>_.mono = f .mono
morphism X Y f x .left .preorder._=>_.fun (δy , δy≤fx) =
  f .stable x δy δy≤fx .∃ₛ.fst , f .stable x δy _ .∃ₛ.snd .proj₁
morphism X Y f x .left .preorder._=>_.mono {δy₁ , δy₁≤fx} {δy₂ , δy₂≤fx} δy₁≤δy₂ =
  f .stable x δy₁ _ .∃ₛ.snd .proj₂ .proj₂
    (f .stable x δy₂ _ .∃ₛ.fst)
    (f .stable x δy₂ _ .∃ₛ.snd .proj₁)
    (Y .≤-trans δy₁≤δy₂ (f .stable x δy₂ _ .∃ₛ.snd .proj₂ .proj₁))
morphism X Y f x .left⊣right {δx , δx≤x} {δy , δy≤fx} .proj₁ = f .stable x δy _ .∃ₛ.snd .proj₂ .proj₂ δx δx≤x
morphism X Y f x .left⊣right {δx , δx≤x} {δy , δy≤fx} .proj₂ left≤δx = Y .≤-trans (f .stable x δy _ .∃ₛ.snd .proj₂ .proj₁) (f .mono left≤δx)

-- Now need to prove that this assignment is invariant under equality
-- of elements so that we get a setoid-indexed family
