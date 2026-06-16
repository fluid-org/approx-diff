{-# OPTIONS --postfix-projections --prop --safe #-}

open import Level using (0ℓ; suc; _⊔_)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import prop using (_,_; LiftS; liftS; tt)
open import prop-setoid
  using (Setoid; idS; _∘S_; ∘S-cong; IsEquivalence; ⊗-setoid; project₁; project₂; 𝟙)
  renaming (_⇒_ to _⇒s_; _≃m_ to _≈s_; ≃m-isEquivalence to ≈s-isEquivalence; id-left to idS-left; id-right to idS-right; assoc to assocS; pair to pairS; pair-cong to pairS-cong)
open import categories using (Category; HasProducts; HasCoproducts; HasTerminal; IsTerminal)
open import commutative-monoid using (CommutativeMonoid; 𝟙cm) renaming (_⊗_ to _×CM_)
open import commutative-semiring using (CommutativeSemiring)
open import functor using (Functor; NatTrans; ≃-NatTrans; HasLimits)


-- FIXME: should probably just have one level?
module semimodule {o ℓ} {A : Setoid (o ⊔ ℓ) (o ⊔ ℓ)} (S : CommutativeSemiring A) where

module S = CommutativeSemiring S

record Semimodule : Set (suc o ⊔ suc ℓ) where
  no-eta-equality
  field
    setoid : Setoid (o ⊔ ℓ) (o ⊔ ℓ)
  open Setoid setoid public

  field
    additive : CommutativeMonoid setoid
    _·_     : S.Carrier → Carrier → Carrier

  open CommutativeMonoid additive public
  field
    ·-cong : ∀ {s₁ s₂ x₁ x₂} → s₁ S.≈ s₂ → x₁ ≈ x₂ → s₁ · x₁ ≈ s₂ · x₂

    ·-mul         : ∀ {s₁ s₂ x} → (s₁ S.· s₂) · x ≈ s₁ · (s₂ · x)
    ·-unit        : ∀ {x} → (S.ι · x) ≈ x
    +-distribʳ    : ∀ {s₁ s₂ x} → (s₁ S.+ s₂) · x ≈ (s₁ · x) + (s₂ · x)
    +-distribˡ    : ∀ {s x₁ x₂} → s · (x₁ + x₂) ≈ (s · x₁) + (s · x₂)
    zero-distribʳ : ∀ {x} → S.ε · x ≈ ε
    zero-distribˡ : ∀ {s} → s · ε ≈ ε
open Semimodule

record _⇒_ (X Y : Semimodule) : Set (o ⊔ ℓ) where
  private
    module X = Semimodule X
    module Y = Semimodule Y
  field
    *→* : X.setoid ⇒s Y.setoid
  open _⇒s_ *→* public
  field
    preserve-ze : func X.ε Y.≈ Y.ε
    preserve-+  : ∀ {x₁ x₂} → func (x₁ X.+ x₂) Y.≈ func x₁ Y.+ func x₂
    preserve-·  : ∀ {s x} → func (s X.· x) Y.≈ s Y.· func x
open _⇒_

record _≈m_ {X Y : Semimodule} (f g : X ⇒ Y) : Prop (o ⊔ ℓ) where
  field
    *≈* : f .*→* ≈s g .*→*
  open _≈s_ *≈* public
open _≈m_

------------------------------------------------------------------------------
-- Category of semimodules and semilinear maps
id : ∀ X → X ⇒ X
id X .*→* = idS _
id X .preserve-ze = X .refl
id X .preserve-+ = X .refl
id X .preserve-· = X .refl

module _ {X Y Z} where
  _∘_ : Y ⇒ Z → X ⇒ Y → X ⇒ Z
  (f ∘ g) .*→* = f .*→* ∘S g .*→*
  (f ∘ g) .preserve-ze = Z .trans (f .func-resp-≈ (g .preserve-ze)) (f .preserve-ze)
  (f ∘ g) .preserve-+ = Z .trans (f .func-resp-≈ (g .preserve-+)) (f .preserve-+)
  (f ∘ g) .preserve-· = Z .trans (f .func-resp-≈ (g .preserve-·)) (f .preserve-·)

cat : Category (suc o ⊔ suc ℓ) (o ⊔ ℓ) (o ⊔ ℓ)
cat .Category.obj = Semimodule
cat .Category._⇒_ = _⇒_
cat .Category._≈_ = _≈m_
cat .Category.isEquiv .IsEquivalence.refl .*≈* = ≈s-isEquivalence .IsEquivalence.refl
cat .Category.isEquiv .IsEquivalence.sym f≈g .*≈* = ≈s-isEquivalence .IsEquivalence.sym (f≈g .*≈*)
cat .Category.isEquiv .IsEquivalence.trans f≈g g≈h .*≈* = ≈s-isEquivalence .IsEquivalence.trans (f≈g .*≈*) (g≈h .*≈*)
cat .Category.id = id
cat .Category._∘_ = _∘_
cat .Category.∘-cong f₁≈f₂ g₁≈g₂ .*≈* = ∘S-cong (f₁≈f₂ .*≈*) (g₁≈g₂ .*≈*)
cat .Category.id-left .*≈* = idS-left
cat .Category.id-right .*≈* = idS-right
cat .Category.assoc f g h .*≈* = assocS (f .*→*) (g .*→*) (h .*→*)

------------------------------------------------------------------------------
open import cmon-enriched using (CMonEnriched; Biproduct; biproduct-iso; biproducts→coproducts)

ε-map : ∀ X Y → X ⇒ Y
ε-map X Y .*→* ._⇒s_.func x = Y .ε
ε-map X Y .*→* ._⇒s_.func-resp-≈ _ = Y .refl
ε-map X Y .preserve-ze = Y .refl
ε-map X Y .preserve-+ = sym Y (Y .+-lunit)
ε-map X Y .preserve-· = sym Y (zero-distribˡ Y)

+-map : ∀ X Y → X ⇒ Y → X ⇒ Y → X ⇒ Y
+-map X Y f g .*→* ._⇒s_.func x = Y ._+_ (f .func x) (g .func x)
+-map X Y f g .*→* ._⇒s_.func-resp-≈ x₁≈x₂ = +-cong Y (_⇒s_.func-resp-≈ (f .*→*) x₁≈x₂)
                                              (_⇒s_.func-resp-≈ (g .*→*) x₁≈x₂)
+-map X Y f g .preserve-ze = trans Y (+-cong Y (f .preserve-ze) (g .preserve-ze)) (+-lunit Y)
+-map X Y f g .preserve-+ = Y .trans (Y .+-cong (f .preserve-+) (g .preserve-+)) (+-interchange Y)
+-map X Y f g .preserve-· = trans Y (+-cong Y (f .preserve-·) (g .preserve-·))
                             (sym Y (+-distribˡ Y))

cmon-enriched : CMonEnriched cat
cmon-enriched .CMonEnriched.homCM M N .CommutativeMonoid.ε = ε-map M N
cmon-enriched .CMonEnriched.homCM M N .CommutativeMonoid._+_ = +-map M N
cmon-enriched .CMonEnriched.homCM M N .CommutativeMonoid.+-cong f₁≈f₂ g₁≈g₂ .*≈* ._≈s_.func-eq x = +-cong N (f₁≈f₂ .func-eq x) (g₁≈g₂ .func-eq x)
cmon-enriched .CMonEnriched.homCM M N .CommutativeMonoid.+-lunit {f} .*≈* ._≈s_.func-eq x₁≈x₂ = N .trans (N .+-lunit) (f .func-resp-≈ x₁≈x₂)
cmon-enriched .CMonEnriched.homCM M N .CommutativeMonoid.+-assoc {f} {g} {h} .*≈* ._≈s_.func-eq {m}{n} m≈n = N .trans (N .+-cong (N .+-cong (f .func-resp-≈ m≈n) (g .func-resp-≈ m≈n)) (h .func-resp-≈ m≈n)) (N .+-assoc)
cmon-enriched .CMonEnriched.homCM M N .CommutativeMonoid.+-comm {f} {g} .*≈* ._≈s_.func-eq {m}{n} m≈n = N .trans (N .+-cong (f .func-resp-≈ m≈n) (g .func-resp-≈ m≈n)) (N .+-comm)
cmon-enriched .CMonEnriched.comp-bilinear₁ {M}{N}{O} f₁ f₂ g .*≈* ._≈s_.func-eq x₁≈x₂ = O .+-cong (f₁ .func-resp-≈ (g .func-resp-≈ x₁≈x₂)) (f₂ .func-resp-≈ (g .func-resp-≈ x₁≈x₂))
cmon-enriched .CMonEnriched.comp-bilinear₂ {M} {N} {O} f g₁ g₂ .*≈* ._≈s_.func-eq x₁≈x₂ = O .trans (f .preserve-+) (O .+-cong (f .func-resp-≈ (g₁ .func-resp-≈ x₁≈x₂)) (f .func-resp-≈ (g₂ .func-resp-≈ x₁≈x₂)))
cmon-enriched .CMonEnriched.comp-bilinear-ε₁ {M}{N}{O} f .*≈* ._≈s_.func-eq _ = O .refl
cmon-enriched .CMonEnriched.comp-bilinear-ε₂ {M} {N} {O} f .*≈* ._≈s_.func-eq _ = f .preserve-ze

------------------------------------------------------------------------------
-- (Bi)products

_⊕_ : Semimodule → Semimodule → Semimodule
(M ⊕ N) .setoid = ⊗-setoid (M .setoid) (N .setoid)
(M ⊕ N) .additive = (M .additive) ×CM (N .additive)
(M ⊕ N) ._·_ s (m , n) = (M ._·_ s m) , (N ._·_ s n)
(M ⊕ N) .·-cong s₁≈s₂ (m₁≈m₂ , n₁≈n₂) = ·-cong M s₁≈s₂ m₁≈m₂ , ·-cong N s₁≈s₂ n₁≈n₂
(M ⊕ N) .·-mul = ·-mul M , ·-mul N
(M ⊕ N) .·-unit = ·-unit M , ·-unit N
(M ⊕ N) .+-distribʳ = +-distribʳ M , +-distribʳ N
(M ⊕ N) .+-distribˡ = +-distribˡ M , +-distribˡ N
(M ⊕ N) .zero-distribʳ = zero-distribʳ M , zero-distribʳ N
(M ⊕ N) .zero-distribˡ = zero-distribˡ M , zero-distribˡ N

p₁ : ∀ {X Y} → (X ⊕ Y) ⇒ X
p₁ .*→* = project₁
p₁ {X} {Y} .preserve-ze = refl X
p₁ {X} {Y} .preserve-+ = refl X
p₁ {X} {Y} .preserve-· = refl X

p₂ : ∀ {X Y} → (X ⊕ Y) ⇒ Y
p₂ .*→* = project₂
p₂ {X} {Y} .preserve-ze = refl Y
p₂ {X} {Y} .preserve-+ = refl Y
p₂ {X} {Y} .preserve-· = refl Y

pair : ∀ {X Y Z} → (X ⇒ Y) → (X ⇒ Z) → X ⇒ (Y ⊕ Z)
pair {X} {Y} {Z} f g .*→* = pairS (f .*→*) (g .*→*)
pair {X} {Y} {Z} f g .preserve-ze = f .preserve-ze , g .preserve-ze
pair {X} {Y} {Z} f g .preserve-+ = f .preserve-+ , g .preserve-+
pair {X} {Y} {Z} f g .preserve-· = f .preserve-· , g .preserve-·

products : HasProducts cat
products .HasProducts.prod M N = M ⊕ N
products .HasProducts.p₁ = p₁
products .HasProducts.p₂ = p₂
products .HasProducts.pair = pair
products .HasProducts.pair-cong f₁≈f₂ g₁≈g₂ .*≈* = pairS-cong (f₁≈f₂ .*≈*) (g₁≈g₂ .*≈*)
products .HasProducts.pair-p₁ f g .*≈* ._≈s_.func-eq = _⇒s_.func-resp-≈ (f .*→*)
products .HasProducts.pair-p₂ f g .*≈* ._≈s_.func-eq = _⇒s_.func-resp-≈ (g .*→*)
products .HasProducts.pair-ext f .*≈* ._≈s_.func-eq = _⇒s_.func-resp-≈ (f .*→*)

------------------------------------------------------------------------------
-- Terminal object (the one-point / zero semimodule)

𝟘 : Semimodule
𝟘 .setoid = 𝟙
𝟘 .additive = 𝟙cm
𝟘 ._·_ _ x = x
𝟘 .·-cong _ _ = tt
𝟘 .·-mul = tt
𝟘 .·-unit = tt
𝟘 .+-distribʳ = tt
𝟘 .+-distribˡ = tt
𝟘 .zero-distribʳ = tt
𝟘 .zero-distribˡ = tt

terminal : HasTerminal cat
terminal .HasTerminal.witness = 𝟘
terminal .HasTerminal.is-terminal .IsTerminal.to-terminal {X} = ε-map X 𝟘
terminal .HasTerminal.is-terminal .IsTerminal.to-terminal-ext f .*≈* ._≈s_.func-eq _ = tt

------------------------------------------------------------------------------
-- Biproducts (the products above, packaged with injections)

biproduct : ∀ X Y → Biproduct cmon-enriched X Y
biproduct X Y .Biproduct.prod = X ⊕ Y
biproduct X Y .Biproduct.p₁ = p₁
biproduct X Y .Biproduct.p₂ = p₂
biproduct X Y .Biproduct.in₁ = pair (id X) (ε-map X Y)
biproduct X Y .Biproduct.in₂ = pair (ε-map Y X) (id Y)
biproduct X Y .Biproduct.id-1 = products .HasProducts.pair-p₁ (id X) (ε-map X Y)
biproduct X Y .Biproduct.id-2 = products .HasProducts.pair-p₂ (ε-map Y X) (id Y)
biproduct X Y .Biproduct.zero-1 = products .HasProducts.pair-p₁ (ε-map Y X) (id Y)
biproduct X Y .Biproduct.zero-2 = products .HasProducts.pair-p₂ (id X) (ε-map X Y)
biproduct X Y .Biproduct.id-+ .*≈* ._≈s_.func-eq (x₁≈x₂ , y₁≈y₂) =
  X .trans (X .+-comm) (X .trans (X .+-lunit) x₁≈x₂) , Y .trans (Y .+-lunit) y₁≈y₂

------------------------------------------------------------------------------
-- Tensor products

𝕀 : Semimodule
𝕀 .setoid = A
𝕀 .additive = S.additive
𝕀 ._·_ = S._·_
𝕀 .·-cong = S.·-cong
𝕀 .·-mul = S.·-assoc
𝕀 .·-unit = S.·-lunit
𝕀 .+-distribʳ = S.·-+-distribᵣ
𝕀 .+-distribˡ = S.·-+-distribₗ
𝕀 .zero-distribʳ = S.ε-annihilₗ
𝕀 .zero-distribˡ = S.ε-annihilᵣ

data ⊗-elt (M N : Semimodule) : Set (o ⊔ ℓ) where
  el    : M .Carrier → N .Carrier -> ⊗-elt M N
  _`+`_ : ⊗-elt M N → ⊗-elt M N → ⊗-elt M N
  _`·`_ : S.Carrier → ⊗-elt M N → ⊗-elt M N
  `ε    : ⊗-elt M N

data ⊗-eq {M N} : ⊗-elt M N → ⊗-elt M N → Set (o ⊔ ℓ) where
  ⊗-eq-refl    : ∀ {x} → ⊗-eq x x
  ⊗-eq-sym     : ∀ {x y} → ⊗-eq x y → ⊗-eq y x
  ⊗-eq-trans   : ∀ {x y z} → ⊗-eq x y → ⊗-eq y z → ⊗-eq x z
  ⊗-eq-+-cong  : ∀ {x₁ x₂ y₁ y₂} → ⊗-eq x₁ x₂ → ⊗-eq y₁ y₂ → ⊗-eq (x₁ `+` y₁) (x₂ `+` y₂)
  ⊗-eq-+-lunit : ∀ {x} → ⊗-eq (`ε `+` x) x
  ⊗-eq-+-assoc : ∀ {x y z} → ⊗-eq ((x `+` y) `+` z) (x `+` (y `+` z))
  ⊗-eq-+-comm  : ∀ {x y} → ⊗-eq (x `+` y) (y `+` x)
  ⊗-eq-·-cong  : ∀ {s₁ s₂ x₁ x₂} → s₁ S.≈ s₂ → ⊗-eq x₁ x₂ → ⊗-eq (s₁ `·` x₁) (s₂ `·` x₂)
  ⊗-eq-·-mul   : ∀ {s₁ s₂ x} → ⊗-eq ((s₁ S.· s₂) `·` x) (s₁ `·` (s₂ `·` x))
  ⊗-eq-·-unit  : ∀ {x} → ⊗-eq (S.ι `·` x) x
  ⊗-eq-+-distribʳ : ∀ {s₁ s₂ x} → ⊗-eq ((s₁ S.+ s₂) `·` x) ((s₁ `·` x) `+` (s₂ `·` x))
  ⊗-eq-+-distribˡ : ∀ {s x₁ x₂} → ⊗-eq (s `·` (x₁ `+` x₂)) ((s `·` x₁) `+` (s `·` x₂))
  ⊗-eq-zero-distribʳ : ∀ {x} → ⊗-eq (S.ε `·` x) `ε
  ⊗-eq-zero-distribˡ : ∀ {s} → ⊗-eq (s `·` `ε) `ε
  ⊗-eq-el-cong : ∀ {m₁ m₂ n₁ n₂} → M ._≈_ m₁ m₂ → N ._≈_ n₁ n₂ → ⊗-eq (el m₁ n₁) (el m₂ n₂)
  ⊗-eq-el-+    : ∀ {m₁ m₂ n₁ n₂} → ⊗-eq (el m₁ n₁ `+` el m₂ n₂) (el (M ._+_ m₁ m₂) (N ._+_ n₁ n₂))
  ⊗-eq-el-·    : ∀ {m n s}       → ⊗-eq (s `·` el m n) (el (M ._·_ s m) (N ._·_ s n))

_⊗_ : Semimodule → Semimodule → Semimodule
(M ⊗ N) .setoid .Setoid.Carrier = ⊗-elt M N
(M ⊗ N) .setoid .Setoid._≈_ x y = LiftS ℓ (⊗-eq x y)
(M ⊗ N) .setoid .Setoid.isEquivalence .IsEquivalence.refl = liftS ⊗-eq-refl
(M ⊗ N) .setoid .Setoid.isEquivalence .IsEquivalence.sym (liftS eq) = liftS (⊗-eq-sym eq)
(M ⊗ N) .setoid .Setoid.isEquivalence .IsEquivalence.trans (liftS eq₁) (liftS eq₂) = liftS (⊗-eq-trans eq₁ eq₂)
(M ⊗ N) .additive .CommutativeMonoid.ε = `ε
(M ⊗ N) .additive .CommutativeMonoid._+_ = _`+`_
(M ⊗ N) .additive .CommutativeMonoid.+-cong (liftS x₁≈x₂) (liftS y₁≈y₂) = liftS (⊗-eq-+-cong x₁≈x₂ y₁≈y₂)
(M ⊗ N) .additive .CommutativeMonoid.+-lunit = liftS ⊗-eq-+-lunit
(M ⊗ N) .additive .CommutativeMonoid.+-assoc = liftS ⊗-eq-+-assoc
(M ⊗ N) .additive .CommutativeMonoid.+-comm = liftS ⊗-eq-+-comm
(M ⊗ N) ._·_ = _`·`_
(M ⊗ N) .·-cong s₁≈s₂ (liftS x₁≈x₂) = liftS (⊗-eq-·-cong s₁≈s₂ x₁≈x₂)
(M ⊗ N) .·-mul = liftS ⊗-eq-·-mul
(M ⊗ N) .·-unit = liftS ⊗-eq-·-unit
(M ⊗ N) .+-distribʳ = liftS ⊗-eq-+-distribʳ
(M ⊗ N) .+-distribˡ = liftS ⊗-eq-+-distribˡ
(M ⊗ N) .zero-distribʳ = liftS ⊗-eq-zero-distribʳ
(M ⊗ N) .zero-distribˡ = liftS ⊗-eq-zero-distribˡ

-- Universal property: bilinear functions M, N ⇒ O are iso to linear functions M ⊗ N ⇒ O
--
-- Presumably this would help with proving that the above is a monoidal product?


_⊸_ : Semimodule → Semimodule → Semimodule
(M ⊸ N) .setoid = Category.hom-setoid cat M N
(M ⊸ N) .additive = cmon-enriched .CMonEnriched.homCM M N
(M ⊸ N) ._·_ s f .*→* ._⇒s_.func x = N ._·_ s (f .func x)
(M ⊸ N) ._·_ s f .*→* ._⇒s_.func-resp-≈ = λ z → N .·-cong S.refl (f .func-resp-≈ z)
(M ⊸ N) ._·_ s f .preserve-ze = trans N (·-cong N S.refl (f .preserve-ze)) (zero-distribˡ N)
(M ⊸ N) ._·_ s f .preserve-+ = trans N (·-cong N S.refl (f .preserve-+)) (+-distribˡ N)
(M ⊸ N) ._·_ s f .preserve-· {s₁}{x} =
  N .trans (N .·-cong S.refl (f .preserve-·))
 (N .trans (N .sym (N .·-mul))
 (N .trans (N .·-cong S.·-comm (N .refl))
           (N .·-mul)))
(M ⊸ N) .·-cong x x₁ .*≈* ._≈s_.func-eq = λ z → ·-cong N x (x₁ .*≈* ._≈s_.func-eq z)
(M ⊸ N) .·-mul {s₁} {s₂} {f} .*≈* ._≈s_.func-eq x = trans N (·-cong N S.refl (f .func-resp-≈ x)) (·-mul N)
(M ⊸ N) .·-unit {f} .*≈* ._≈s_.func-eq x₁≈x₂ = N .trans (N .·-unit) (f .func-resp-≈ x₁≈x₂)
(M ⊸ N) .+-distribʳ {s₁} {s₂} {f} .*≈* ._≈s_.func-eq x₁≈x₂ =
  N .trans (N .·-cong S.refl (f .func-resp-≈ x₁≈x₂)) (+-distribʳ N)
(M ⊸ N) .+-distribˡ {s} {f₁} {f₂} .*≈* ._≈s_.func-eq x₁≈x₂ =
  N .trans (N .·-cong S.refl (N .+-cong (f₁ .func-resp-≈ x₁≈x₂) (f₂ .func-resp-≈ x₁≈x₂)))
           (N .+-distribˡ)
(M ⊸ N) .zero-distribʳ {f} .*≈* ._≈s_.func-eq x₁≈x₂ = zero-distribʳ N
(M ⊸ N) .zero-distribˡ {s} .*≈* ._≈s_.func-eq x₁≈x₂ = zero-distribˡ N

-- TODO: Tensor products and adjointness, or could just state that the
-- category is closed without the tensor.

------------------------------------------------------------------------------
-- Duality

Dual : Semimodule → Semimodule
Dual M = M ⊸ 𝕀

-- Isomorphisms M ≅ Dual M are equivalent to certain kinds of
--
--   M ⇒ M ⊸ 𝕀
-- ≅ M ⊗ M ⇒ 𝕀
--
-- i.e. a bilinear map.
--
-- When the original map is an isomorphism, then can this property be
-- stated in terms of the bilinear map?
--
-- Non-degeneracy: ∀ x → x ≠ ε → ∃ y → ⟨ x , y ⟩ ≠ ε

-- forward map: M ⇒ M ⊸ I
--              x ↦ y ↦ ⟨ x , y ⟩
--
-- backward map: (M ⊸ I) ⇒ M
--               f ↦ Σ f(eᵢ) eᵢ
-- In finite dimensions, equivalent to unimodularity?

------------------------------------------------------------------------------
-- Transpose: the contravariant action of Dual, f ↦ (_ ∘ f).

open Category cat using (≈-trans; ≈-sym; ≈-refl; ∘-cong; assoc; id-left; Iso; IsIso→Iso)
open CMonEnriched cmon-enriched using (homCM; _+m_; εm; comp-bilinear₁; comp-bilinear-ε₁; comp-bilinear-ε₂)

infix 25 _ᵀ

_ᵀ : ∀ {X Y} → X ⇒ Y → Dual Y ⇒ Dual X
(f ᵀ) .*→* ._⇒s_.func φ = φ ∘ f
(f ᵀ) .*→* ._⇒s_.func-resp-≈ φ≈φ' .*≈* ._≈s_.func-eq x≈x' =
  φ≈φ' .*≈* ._≈s_.func-eq (f .func-resp-≈ x≈x')
(f ᵀ) .preserve-ze = comp-bilinear-ε₁ f
(f ᵀ) .preserve-+ {φ} {ψ} = comp-bilinear₁ φ ψ f
(f ᵀ) .preserve-· {s} {φ} .*≈* ._≈s_.func-eq x≈x' =
  S.·-cong S.refl (φ .func-resp-≈ (f .func-resp-≈ x≈x'))

ᵀ-cong : ∀ {X Y} {f g : X ⇒ Y} → (f ≈m g) → ((f ᵀ) ≈m (g ᵀ))
ᵀ-cong f≈g .*≈* ._≈s_.func-eq φ≈ψ .*≈* ._≈s_.func-eq x≈x' =
  φ≈ψ .*≈* ._≈s_.func-eq (f≈g .*≈* ._≈s_.func-eq x≈x')

ᵀ-id : ∀ {X} → ((id X) ᵀ) ≈m id (Dual X)
ᵀ-id .*≈* ._≈s_.func-eq φ≈ψ .*≈* ._≈s_.func-eq x≈x' = φ≈ψ .*≈* ._≈s_.func-eq x≈x'

ᵀ-comp : ∀ {X Y Z} (g : Y ⇒ Z) (f : X ⇒ Y) → ((g ∘ f) ᵀ) ≈m ((f ᵀ) ∘ (g ᵀ))
ᵀ-comp g f .*≈* ._≈s_.func-eq φ≈ψ .*≈* ._≈s_.func-eq x≈x' =
  φ≈ψ .*≈* ._≈s_.func-eq (g .func-resp-≈ (f .func-resp-≈ x≈x'))

-- Additivity.
ᵀ-+ : ∀ {X Y} (f g : X ⇒ Y) → ((f +m g) ᵀ) ≈m ((f ᵀ) +m (g ᵀ))
ᵀ-+ f g .*≈* ._≈s_.func-eq {φ} φ≈ψ .*≈* ._≈s_.func-eq x≈x' =
  trans 𝕀 (φ .preserve-+)
    (+-cong 𝕀 (φ≈ψ .*≈* ._≈s_.func-eq (f .func-resp-≈ x≈x'))
              (φ≈ψ .*≈* ._≈s_.func-eq (g .func-resp-≈ x≈x')))

ᵀ-ε : ∀ {X Y} → ((εm {X} {Y}) ᵀ) ≈m εm
ᵀ-ε .*≈* ._≈s_.func-eq {φ} _ = comp-bilinear-ε₂ φ

------------------------------------------------------------------------------
-- Dual preserves biproducts: transport the biproduct laws through _ᵀ (swapping
-- p ↔ in by contravariance).  Apex Dual(X⊕Y) is then a biproduct of Dual X, Dual Y.

Dual-preserves-⊕ : ∀ {X Y} → Biproduct cmon-enriched (Dual X) (Dual Y)
Dual-preserves-⊕ {X} {Y} = D
  where
    open Biproduct (biproduct X Y) using (in₁; in₂; id-1; id-2; zero-1; zero-2; id-+)
    D : Biproduct cmon-enriched (Dual X) (Dual Y)
    D .Biproduct.prod = Dual (X ⊕ Y)
    D .Biproduct.p₁ = in₁ ᵀ
    D .Biproduct.p₂ = in₂ ᵀ
    D .Biproduct.in₁ = p₁ ᵀ
    D .Biproduct.in₂ = p₂ ᵀ
    D .Biproduct.id-1 = ≈-trans (≈-sym (ᵀ-comp p₁ in₁)) (≈-trans (ᵀ-cong id-1) ᵀ-id)
    D .Biproduct.id-2 = ≈-trans (≈-sym (ᵀ-comp p₂ in₂)) (≈-trans (ᵀ-cong id-2) ᵀ-id)
    D .Biproduct.zero-1 = ≈-trans (≈-sym (ᵀ-comp p₂ in₁)) (≈-trans (ᵀ-cong zero-2) ᵀ-ε)
    D .Biproduct.zero-2 = ≈-trans (≈-sym (ᵀ-comp p₁ in₂)) (≈-trans (ᵀ-cong zero-1) ᵀ-ε)
    D .Biproduct.id-+ =
      ≈-trans (homCM _ _ .CommutativeMonoid.+-cong (≈-sym (ᵀ-comp in₁ p₁)) (≈-sym (ᵀ-comp in₂ p₂)))
      (≈-trans (≈-sym (ᵀ-+ (in₁ ∘ p₁) (in₂ ∘ p₂)))
      (≈-trans (ᵀ-cong id-+) ᵀ-id))

------------------------------------------------------------------------------
-- Base case 𝕀 ≅ Dual 𝕀 for self-duality.

private
  ·-runit : ∀ {x} → (x S.· S.ι) S.≈ x
  ·-runit = S.trans S.·-comm S.·-lunit

𝕀≅𝕀* : Iso 𝕀 (Dual 𝕀)
𝕀≅𝕀* .Iso.fwd .*→* ._⇒s_.func a .*→* ._⇒s_.func x = a S.· x
𝕀≅𝕀* .Iso.fwd .*→* ._⇒s_.func a .*→* ._⇒s_.func-resp-≈ x≈x' = S.·-cong S.refl x≈x'
𝕀≅𝕀* .Iso.fwd .*→* ._⇒s_.func a .preserve-ze = S.ε-annihilᵣ
𝕀≅𝕀* .Iso.fwd .*→* ._⇒s_.func a .preserve-+ = S.·-+-distribₗ
𝕀≅𝕀* .Iso.fwd .*→* ._⇒s_.func a .preserve-· =
  S.trans (S.sym S.·-assoc) (S.trans (S.·-cong S.·-comm S.refl) S.·-assoc)
𝕀≅𝕀* .Iso.fwd .*→* ._⇒s_.func-resp-≈ a≈a' .*≈* ._≈s_.func-eq x≈x' = S.·-cong a≈a' x≈x'
𝕀≅𝕀* .Iso.fwd .preserve-ze .*≈* ._≈s_.func-eq _ = S.ε-annihilₗ
𝕀≅𝕀* .Iso.fwd .preserve-+ .*≈* ._≈s_.func-eq x≈x' =
  S.trans S.·-+-distribᵣ (S.+-cong (S.·-cong S.refl x≈x') (S.·-cong S.refl x≈x'))
𝕀≅𝕀* .Iso.fwd .preserve-· .*≈* ._≈s_.func-eq x≈x' =
  S.trans S.·-assoc (S.·-cong S.refl (S.·-cong S.refl x≈x'))
𝕀≅𝕀* .Iso.bwd .*→* ._⇒s_.func φ = φ .func S.ι
𝕀≅𝕀* .Iso.bwd .*→* ._⇒s_.func-resp-≈ φ≈φ' = φ≈φ' .*≈* ._≈s_.func-eq S.refl
𝕀≅𝕀* .Iso.bwd .preserve-ze = S.refl
𝕀≅𝕀* .Iso.bwd .preserve-+ = S.refl
𝕀≅𝕀* .Iso.bwd .preserve-· = S.refl
𝕀≅𝕀* .Iso.fwd∘bwd≈id .*≈* ._≈s_.func-eq {φ} φ≈ψ .*≈* ._≈s_.func-eq {x} x≈x' =
  S.trans S.·-comm
    (S.trans (S.sym (φ .preserve-· {x} {S.ι})) (φ≈ψ .*≈* ._≈s_.func-eq (S.trans ·-runit x≈x')))
𝕀≅𝕀* .Iso.bwd∘fwd≈id .*≈* ._≈s_.func-eq a≈a' = S.trans ·-runit a≈a'

------------------------------------------------------------------------------
-- Dual preserves isomorphisms (contravariantly) and the zero object.

Dual-iso : ∀ {X Y} → Iso X Y → Iso (Dual Y) (Dual X)
Dual-iso iso .Iso.fwd = (iso .Iso.fwd) ᵀ
Dual-iso iso .Iso.bwd = (iso .Iso.bwd) ᵀ
Dual-iso iso .Iso.fwd∘bwd≈id =
  ≈-trans (≈-sym (ᵀ-comp (iso .Iso.bwd) (iso .Iso.fwd))) (≈-trans (ᵀ-cong (iso .Iso.bwd∘fwd≈id)) ᵀ-id)
Dual-iso iso .Iso.bwd∘fwd≈id =
  ≈-trans (≈-sym (ᵀ-comp (iso .Iso.fwd) (iso .Iso.bwd))) (≈-trans (ᵀ-cong (iso .Iso.fwd∘bwd≈id)) ᵀ-id)

-- Dual 𝟘 ≅ 𝟘: both are the zero object.
Dual-𝟘 : Iso (Dual 𝟘) 𝟘
Dual-𝟘 .Iso.fwd = HasTerminal.to-terminal terminal
Dual-𝟘 .Iso.bwd = εm
Dual-𝟘 .Iso.fwd∘bwd≈id = HasTerminal.to-terminal-unique terminal _ _
Dual-𝟘 .Iso.bwd∘fwd≈id .*≈* ._≈s_.func-eq {_} {ψ} _ .*≈* ._≈s_.func-eq _ =
  sym 𝕀 (trans 𝕀 (ψ .func-resp-≈ tt) (ψ .preserve-ze))

-- Dual(X⊕Y) ≅ Dual X ⊕ Dual Y, and ⊕ acting on isos (via biproducts).
private
  coproducts : HasCoproducts cat
  coproducts = biproducts→coproducts cmon-enriched biproduct

Dual-⊕-iso : ∀ {X Y} → Iso (Dual (X ⊕ Y)) (Dual X ⊕ Dual Y)
Dual-⊕-iso {X} {Y} = IsIso→Iso (biproduct-iso cmon-enriched Dual-preserves-⊕ (biproduct (Dual X) (Dual Y)))

⊕-iso : ∀ {X X' Y Y'} → Iso X X' → Iso Y Y' → Iso (X ⊕ Y) (X' ⊕ Y')
⊕-iso = HasCoproducts.coproduct-preserve-iso coproducts

------------------------------------------------------------------------------
-- Conjugate of a morphism w.r.t. chosen self-dualities d : X ≅ Dual X.

conj : ∀ {X Y} → Iso X (Dual X) → Iso Y (Dual Y) → (X ⇒ Y) → (Y ⇒ X)
conj X≅X* Y≅Y* f = X≅X* .Iso.bwd ∘ ((f ᵀ) ∘ (Y≅Y* .Iso.fwd))

-- conj f transported back through d_X is fᵀ ∘ d_Y: the conjugate relation, in
-- morphism form (d_X ∘ conj f ≈ fᵀ ∘ d_Y).
conj-transpose : ∀ {X Y} (X≅X* : Iso X (Dual X)) (Y≅Y* : Iso Y (Dual Y)) (f : X ⇒ Y) →
                 ((X≅X* .Iso.fwd) ∘ conj X≅X* Y≅Y* f) ≈m ((f ᵀ) ∘ (Y≅Y* .Iso.fwd))
conj-transpose X≅X* Y≅Y* f =
  ≈-trans (≈-sym (assoc (X≅X* .Iso.fwd) (X≅X* .Iso.bwd) ((f ᵀ) ∘ (Y≅Y* .Iso.fwd))))
          (≈-trans (∘-cong (X≅X* .Iso.fwd∘bwd≈id) (≈-refl {f = (f ᵀ) ∘ (Y≅Y* .Iso.fwd)})) id-left)

-- Pairing ⟨ x , y ⟩ = (d x) y induced by a self-duality, and pointwise conjugate relation
-- ⟨ conj f y , x ⟩ ≈ ⟨ y , f x ⟩.
pairing : ∀ {X} → Iso X (Dual X) → X .Carrier → X .Carrier → S.Carrier
pairing X≅X* x y = ((X≅X* .Iso.fwd) .*→* ._⇒s_.func x) .*→* ._⇒s_.func y

conj-pairing : ∀ {X Y} (X≅X* : Iso X (Dual X)) (Y≅Y* : Iso Y (Dual Y)) (f : X ⇒ Y) {x y} →
               S._≈_ (pairing X≅X* ((conj X≅X* Y≅Y* f) .*→* ._⇒s_.func y) x) (pairing Y≅Y* y (f .*→* ._⇒s_.func x))
conj-pairing {X} {Y} X≅X* Y≅Y* f =
  conj-transpose X≅X* Y≅Y* f .*≈* ._≈s_.func-eq (refl Y) .*≈* ._≈s_.func-eq (refl X)

------------------------------------------------------------------------------
module _ (𝒮 : Category 0ℓ 0ℓ 0ℓ) where
  private
    module 𝒮 = Category 𝒮

  open Functor
  open NatTrans
  open ≃-NatTrans

  -- Set of Natural Transformations Id ⇒ D
  record Π-Carrier (D : Functor 𝒮 cat) : Set (o ⊔ ℓ) where
    field
      Π-func : (x : 𝒮.obj) → D .fobj x .Carrier
      Π-natural : ∀ {x₁ x₂} (f : x₁ 𝒮.⇒ x₂) → _≈_ (D .fobj x₂) (D .fmor f .func (Π-func x₁)) (Π-func x₂)
  open Π-Carrier

  Π : Functor 𝒮 cat → Semimodule
  Π D .setoid .Setoid.Carrier = Π-Carrier D
  Π D .setoid .Setoid._≈_ α β = ∀ x → D .fobj x ._≈_ (α .Π-func x) (β .Π-func x)
  Π D .setoid .Setoid.isEquivalence .IsEquivalence.refl x = refl (fobj D x)
  Π D .setoid .Setoid.isEquivalence .IsEquivalence.sym x x₁ = sym (fobj D x₁) (x x₁)
  Π D .setoid .Setoid.isEquivalence .IsEquivalence.trans z₁ z₂ x₁ = trans (fobj D x₁) (z₁ x₁) (z₂ x₁)
  Π D .additive .CommutativeMonoid.ε .Π-func x = D .fobj x .ε
  Π D .additive .CommutativeMonoid.ε .Π-natural f = D .fmor f .preserve-ze
  Π D .additive .CommutativeMonoid._+_ α₁ α₂ .Π-func x = D .fobj x ._+_ (α₁ .Π-func x) (α₂ .Π-func x)
  Π D .additive .CommutativeMonoid._+_ α₁ α₂ .Π-natural = λ f →
                                                             trans (fobj D _) (D .fmor f .preserve-+)
                                                             (+-cong (fobj D _) (α₁ .Π-natural f) (α₂ .Π-natural f))
  Π D .additive .CommutativeMonoid.+-cong = λ z z₁ x → +-cong (fobj D x) (z x) (z₁ x)
  Π D .additive .CommutativeMonoid.+-lunit = λ x₁ → +-lunit (fobj D x₁)
  Π D .additive .CommutativeMonoid.+-assoc = λ x₁ → +-assoc (fobj D x₁)
  Π D .additive .CommutativeMonoid.+-comm = λ x₁ → +-comm (fobj D x₁)
  Π D ._·_ s α .Π-func x = D .fobj x ._·_ s (α .Π-func x)
  Π D ._·_ s α .Π-natural f =
    D .fobj _ .trans (D .fmor f .preserve-·) (D .fobj _ .·-cong S.refl (α .Π-natural f))
  Π D .·-cong = λ z z₁ x → ·-cong (D .fobj x) z (z₁ x)
  Π D .·-mul = λ x₁ → ·-mul (D .fobj x₁)
  Π D .·-unit = λ x₁ → ·-unit (D .fobj x₁)
  Π D .+-distribʳ = λ x₁ → +-distribʳ (D .fobj x₁)
  Π D .+-distribˡ = λ x → +-distribˡ (D .fobj x)
  Π D .zero-distribʳ = λ x₁ → zero-distribʳ (D .fobj x₁)
  Π D .zero-distribˡ = λ x → zero-distribˡ (D .fobj x)

  limits : HasLimits 𝒮 cat
  limits D .functor.Limit.apex = Π D
  limits D .functor.Limit.cone .transf x .*→* ._⇒s_.func α = α .Π-func x
  limits D .functor.Limit.cone .transf x .*→* ._⇒s_.func-resp-≈ α₁≈α₂ = α₁≈α₂ x
  limits D .functor.Limit.cone .transf x .preserve-ze = D .fobj x .refl
  limits D .functor.Limit.cone .transf x .preserve-+ = D .fobj x .refl
  limits D .functor.Limit.cone .transf x .preserve-· = D .fobj x .refl
  limits D .functor.Limit.cone .natural f .*≈* ._≈s_.func-eq {α₁} {α₂} α₁≈α₂ =
    D .fobj _ .trans (α₁ .Π-natural f) (α₁≈α₂ _)
  limits D .functor.Limit.isLimit .functor.IsLimit.lambda M α .*→* ._⇒s_.func m .Π-func x = α .transf x .func m
  limits D .functor.Limit.isLimit .functor.IsLimit.lambda M α .*→* ._⇒s_.func m .Π-natural f = α .natural f .*≈* ._≈s_.func-eq (M .refl)
  limits D .functor.Limit.isLimit .functor.IsLimit.lambda M α .*→* ._⇒s_.func-resp-≈ m≈n x = α .transf x .func-resp-≈ m≈n
  limits D .functor.Limit.isLimit .functor.IsLimit.lambda M α .preserve-ze x = α .transf x .preserve-ze
  limits D .functor.Limit.isLimit .functor.IsLimit.lambda M α .preserve-+ x = α .transf x .preserve-+
  limits D .functor.Limit.isLimit .functor.IsLimit.lambda M α .preserve-· x = α .transf x .preserve-·
  limits D .functor.Limit.isLimit .functor.IsLimit.lambda-cong {M} α≃β .*≈* ._≈s_.func-eq {m}{n} m≈n x = α≃β .transf-eq x .*≈* ._≈s_.func-eq m≈n
  limits D .functor.Limit.isLimit .functor.IsLimit.lambda-eval α .transf-eq x .*≈* ._≈s_.func-eq = α .transf x .func-resp-≈
  limits D .functor.Limit.isLimit .functor.IsLimit.lambda-ext f .*≈* ._≈s_.func-eq {m}{n} m≈n x = f .func-resp-≈ m≈n x
