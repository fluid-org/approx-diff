{-# OPTIONS --postfix-projections --prop --safe #-}

open import Level using (0ℓ; suc)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; _×_)
open import prop using (_,_; proj₁; proj₂; LiftS; liftS; tt; _⇔_; sym-⇔; trans-⇔)
open import prop-setoid
  using (Setoid; idS; _∘S_; ∘S-cong; IsEquivalence; ⊗-setoid; project₁; project₂; 𝟙)
  renaming (_⇒_ to _⇒s_; _≃m_ to _≈s_; ≃m-isEquivalence to ≈s-isEquivalence; id-left to idS-left; id-right to idS-right; assoc to assocS; pair to pairS; pair-cong to pairS-cong)
open import categories using (Category; HasProducts; HasCoproducts; HasTerminal; IsTerminal)
open import commutative-monoid using (CommutativeMonoid; 𝟙cm) renaming (_⊗_ to _×CM_)
open import commutative-semiring using (CommutativeSemiring)
open import functor using (Functor; NatTrans; ≃-NatTrans; HasLimits)


module semimodule {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A) where

module S = CommutativeSemiring S

record Semimodule : Set (suc 0ℓ) where
  no-eta-equality
  field
    setoid : Setoid (0ℓ) (0ℓ)
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

record _⇒_ (M N : Semimodule) : Set (0ℓ) where
  private
    module M = Semimodule M
    module N = Semimodule N
  field
    *→* : M.setoid ⇒s N.setoid
  open _⇒s_ *→* public
  field
    preserve-ze : func M.ε N.≈ N.ε
    preserve-+  : ∀ {x₁ x₂} → func (x₁ M.+ x₂) N.≈ func x₁ N.+ func x₂
    preserve-·  : ∀ {s x} → func (s M.· x) N.≈ s N.· func x
open _⇒_

infix 4 _≈m_
record _≈m_ {M N : Semimodule} (f g : M ⇒ N) : Prop (0ℓ) where
  field
    *≈* : f .*→* ≈s g .*→*
  open _≈s_ *≈* public
open _≈m_

------------------------------------------------------------------------------
-- Category of semimodules and semilinear maps
id : ∀ M → M ⇒ M
id M .*→* = idS _
id M .preserve-ze = M .refl
id M .preserve-+ = M .refl
id M .preserve-· = M .refl

module _ {M N O} where
  infixl 21 _∘_
  _∘_ : N ⇒ O → M ⇒ N → M ⇒ O
  (f ∘ g) .*→* = f .*→* ∘S g .*→*
  (f ∘ g) .preserve-ze = O .trans (f .func-resp-≈ (g .preserve-ze)) (f .preserve-ze)
  (f ∘ g) .preserve-+ = O .trans (f .func-resp-≈ (g .preserve-+)) (f .preserve-+)
  (f ∘ g) .preserve-· = O .trans (f .func-resp-≈ (g .preserve-·)) (f .preserve-·)

cat : Category (suc 0ℓ) (0ℓ) (0ℓ)
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

ε-map : ∀ M N → M ⇒ N
ε-map M N .*→* ._⇒s_.func x = N .ε
ε-map M N .*→* ._⇒s_.func-resp-≈ _ = N .refl
ε-map M N .preserve-ze = N .refl
ε-map M N .preserve-+ = sym N (N .+-lunit)
ε-map M N .preserve-· = sym N (zero-distribˡ N)

+-map : ∀ M N → M ⇒ N → M ⇒ N → M ⇒ N
+-map M N f g .*→* ._⇒s_.func x = N ._+_ (f .func x) (g .func x)
+-map M N f g .*→* ._⇒s_.func-resp-≈ x₁≈x₂ = +-cong N (_⇒s_.func-resp-≈ (f .*→*) x₁≈x₂)
                                              (_⇒s_.func-resp-≈ (g .*→*) x₁≈x₂)
+-map M N f g .preserve-ze = trans N (+-cong N (f .preserve-ze) (g .preserve-ze)) (+-lunit N)
+-map M N f g .preserve-+ = N .trans (N .+-cong (f .preserve-+) (g .preserve-+)) (+-interchange N)
+-map M N f g .preserve-· = trans N (+-cong N (f .preserve-·) (g .preserve-·))
                             (sym N (+-distribˡ N))

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

p₁ : ∀ {M N} → (M ⊕ N) ⇒ M
p₁ .*→* = project₁
p₁ {M} {N} .preserve-ze = refl M
p₁ {M} {N} .preserve-+ = refl M
p₁ {M} {N} .preserve-· = refl M

p₂ : ∀ {M N} → (M ⊕ N) ⇒ N
p₂ .*→* = project₂
p₂ {M} {N} .preserve-ze = refl N
p₂ {M} {N} .preserve-+ = refl N
p₂ {M} {N} .preserve-· = refl N

pair : ∀ {M N O} → (M ⇒ N) → (M ⇒ O) → M ⇒ (N ⊕ O)
pair {M} {N} {O} f g .*→* = pairS (f .*→*) (g .*→*)
pair {M} {N} {O} f g .preserve-ze = f .preserve-ze , g .preserve-ze
pair {M} {N} {O} f g .preserve-+ = f .preserve-+ , g .preserve-+
pair {M} {N} {O} f g .preserve-· = f .preserve-· , g .preserve-·

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
terminal .HasTerminal.is-terminal .IsTerminal.to-terminal {M} = ε-map M 𝟘
terminal .HasTerminal.is-terminal .IsTerminal.to-terminal-ext f .*≈* ._≈s_.func-eq _ = tt

------------------------------------------------------------------------------
-- Biproducts (the products above, packaged with injections)

biproduct : ∀ M N → Biproduct cmon-enriched M N
biproduct M N .Biproduct.prod = M ⊕ N
biproduct M N .Biproduct.p₁ = p₁
biproduct M N .Biproduct.p₂ = p₂
biproduct M N .Biproduct.in₁ = pair (id M) (ε-map M N)
biproduct M N .Biproduct.in₂ = pair (ε-map N M) (id N)
biproduct M N .Biproduct.id-1 = products .HasProducts.pair-p₁ (id M) (ε-map M N)
biproduct M N .Biproduct.id-2 = products .HasProducts.pair-p₂ (ε-map N M) (id N)
biproduct M N .Biproduct.zero-1 = products .HasProducts.pair-p₁ (ε-map N M) (id N)
biproduct M N .Biproduct.zero-2 = products .HasProducts.pair-p₂ (id M) (ε-map M N)
biproduct M N .Biproduct.id-+ .*≈* ._≈s_.func-eq (x₁≈x₂ , y₁≈y₂) =
  M .trans (M .+-comm) (M .trans (M .+-lunit) x₁≈x₂) , N .trans (N .+-lunit) y₁≈y₂

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

data ⊗-elt (M N : Semimodule) : Set (0ℓ) where
  el    : M .Carrier → N .Carrier -> ⊗-elt M N
  _`+`_ : ⊗-elt M N → ⊗-elt M N → ⊗-elt M N
  _`·`_ : S.Carrier → ⊗-elt M N → ⊗-elt M N
  `ε    : ⊗-elt M N

data ⊗-eq {M N} : ⊗-elt M N → ⊗-elt M N → Set (0ℓ) where
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
(M ⊗ N) .setoid .Setoid._≈_ x y = LiftS 0ℓ (⊗-eq x y)
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

-- The linear measurements of M.
Dual : Semimodule → Semimodule
Dual M = M ⊸ 𝕀

open Category cat using (≈-trans; ≈-sym; ≈-refl; ∘-cong; assoc; id-left; Iso; IsIso→Iso; Iso-trans; Iso-sym)

-- Pairing ⟨ x , y ⟩ = (d x) y induced by a self-duality; a measure of the extent to which x and y overlap.
pairing : ∀ {M} → Iso M (Dual M) → M .Carrier → M .Carrier → S.Carrier
pairing M≅M* x y = M≅M* .Iso.fwd .*→* ._⇒s_.func x .*→* ._⇒s_.func y

-- Isomorphisms M ≅ Dual M are equivalent to certain kinds of bilinear maps:
--
--   M ⇒ M ⊸ 𝕀
-- ≅ M ⊗ M ⇒ 𝕀
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

open CMonEnriched cmon-enriched using (homCM; _+m_; εm; comp-bilinear₁; comp-bilinear-ε₁; comp-bilinear-ε₂)

infix 25 _ᵀ

_ᵀ : ∀ {M N} → M ⇒ N → Dual N ⇒ Dual M
(f ᵀ) .*→* ._⇒s_.func φ = φ ∘ f
(f ᵀ) .*→* ._⇒s_.func-resp-≈ φ≈ψ .*≈* ._≈s_.func-eq x≈y =
  φ≈ψ .*≈* ._≈s_.func-eq (f .func-resp-≈ x≈y)
(f ᵀ) .preserve-ze = comp-bilinear-ε₁ f
(f ᵀ) .preserve-+ {φ} {ψ} = comp-bilinear₁ φ ψ f
(f ᵀ) .preserve-· {s} {φ} .*≈* ._≈s_.func-eq x≈y =
  S.·-cong S.refl (φ .func-resp-≈ (f .func-resp-≈ x≈y))

ᵀ-cong : ∀ {M N} {f g : M ⇒ N} → f ≈m g → f ᵀ ≈m g ᵀ
ᵀ-cong f≈g .*≈* ._≈s_.func-eq φ≈ψ .*≈* ._≈s_.func-eq x≈y =
  φ≈ψ .*≈* ._≈s_.func-eq (f≈g .*≈* ._≈s_.func-eq x≈y)

ᵀ-id : ∀ {M} → (id M) ᵀ ≈m id (Dual M)
ᵀ-id .*≈* ._≈s_.func-eq φ≈ψ .*≈* ._≈s_.func-eq x≈y = φ≈ψ .*≈* ._≈s_.func-eq x≈y

ᵀ-comp : ∀ {M N O} (g : N ⇒ O) (f : M ⇒ N) → (g ∘ f) ᵀ ≈m f ᵀ ∘ g ᵀ
ᵀ-comp g f .*≈* ._≈s_.func-eq φ≈ψ .*≈* ._≈s_.func-eq x≈y =
  φ≈ψ .*≈* ._≈s_.func-eq (g .func-resp-≈ (f .func-resp-≈ x≈y))

-- Additivity.
ᵀ-+ : ∀ {M N} (f g : M ⇒ N) → (f +m g) ᵀ ≈m f ᵀ +m g ᵀ
ᵀ-+ f g .*≈* ._≈s_.func-eq {φ} φ≈ψ .*≈* ._≈s_.func-eq x≈y =
  trans 𝕀 (φ .preserve-+)
    (+-cong 𝕀 (φ≈ψ .*≈* ._≈s_.func-eq (f .func-resp-≈ x≈y)) (φ≈ψ .*≈* ._≈s_.func-eq (g .func-resp-≈ x≈y)))

ᵀ-ε : ∀ {M N} → (εm {M} {N}) ᵀ ≈m εm
ᵀ-ε .*≈* ._≈s_.func-eq {φ} _ = comp-bilinear-ε₂ φ

module _ {M N} where
  open Biproduct (biproduct M N) using (in₁; in₂; id-1; id-2; zero-1; zero-2; id-+)

  Dual-preserves-⊕ : Biproduct cmon-enriched (Dual M) (Dual N)
  Dual-preserves-⊕ .Biproduct.prod = Dual (M ⊕ N)
  Dual-preserves-⊕ .Biproduct.p₁ = in₁ ᵀ
  Dual-preserves-⊕ .Biproduct.p₂ = in₂ ᵀ
  Dual-preserves-⊕ .Biproduct.in₁ = p₁ ᵀ
  Dual-preserves-⊕ .Biproduct.in₂ = p₂ ᵀ
  Dual-preserves-⊕ .Biproduct.id-1 = ≈-trans (≈-sym (ᵀ-comp p₁ in₁)) (≈-trans (ᵀ-cong id-1) ᵀ-id)
  Dual-preserves-⊕ .Biproduct.id-2 = ≈-trans (≈-sym (ᵀ-comp p₂ in₂)) (≈-trans (ᵀ-cong id-2) ᵀ-id)
  Dual-preserves-⊕ .Biproduct.zero-1 = ≈-trans (≈-sym (ᵀ-comp p₂ in₁)) (≈-trans (ᵀ-cong zero-2) ᵀ-ε)
  Dual-preserves-⊕ .Biproduct.zero-2 = ≈-trans (≈-sym (ᵀ-comp p₁ in₂)) (≈-trans (ᵀ-cong zero-1) ᵀ-ε)
  Dual-preserves-⊕ .Biproduct.id-+ =
    ≈-trans (homCM _ _ .CommutativeMonoid.+-cong (≈-sym (ᵀ-comp in₁ p₁)) (≈-sym (ᵀ-comp in₂ p₂)))
      (≈-trans (≈-sym (ᵀ-+ (in₁ ∘ p₁) (in₂ ∘ p₂))) (≈-trans (ᵀ-cong id-+) ᵀ-id))

------------------------------------------------------------------------------
-- Base case 𝕀 ≅ Dual 𝕀 for self-duality.

𝕀≅𝕀* : Iso 𝕀 (Dual 𝕀)
𝕀≅𝕀* .Iso.fwd .*→* ._⇒s_.func a .*→* ._⇒s_.func x = a S.· x
𝕀≅𝕀* .Iso.fwd .*→* ._⇒s_.func a .*→* ._⇒s_.func-resp-≈ x≈y = S.·-cong S.refl x≈y
𝕀≅𝕀* .Iso.fwd .*→* ._⇒s_.func a .preserve-ze = S.ε-annihilᵣ
𝕀≅𝕀* .Iso.fwd .*→* ._⇒s_.func a .preserve-+ = S.·-+-distribₗ
𝕀≅𝕀* .Iso.fwd .*→* ._⇒s_.func a .preserve-· =
  S.trans (S.sym S.·-assoc) (S.trans (S.·-cong S.·-comm S.refl) S.·-assoc)
𝕀≅𝕀* .Iso.fwd .*→* ._⇒s_.func-resp-≈ a≈b .*≈* ._≈s_.func-eq x≈y = S.·-cong a≈b x≈y
𝕀≅𝕀* .Iso.fwd .preserve-ze .*≈* ._≈s_.func-eq _ = S.ε-annihilₗ
𝕀≅𝕀* .Iso.fwd .preserve-+ .*≈* ._≈s_.func-eq x≈y =
  S.trans S.·-+-distribᵣ (S.+-cong (S.·-cong S.refl x≈y) (S.·-cong S.refl x≈y))
𝕀≅𝕀* .Iso.fwd .preserve-· .*≈* ._≈s_.func-eq x≈y =
  S.trans S.·-assoc (S.·-cong S.refl (S.·-cong S.refl x≈y))
𝕀≅𝕀* .Iso.bwd .*→* ._⇒s_.func φ = φ .func S.ι
𝕀≅𝕀* .Iso.bwd .*→* ._⇒s_.func-resp-≈ φ≈ψ = φ≈ψ .*≈* ._≈s_.func-eq S.refl
𝕀≅𝕀* .Iso.bwd .preserve-ze = S.refl
𝕀≅𝕀* .Iso.bwd .preserve-+ = S.refl
𝕀≅𝕀* .Iso.bwd .preserve-· = S.refl
𝕀≅𝕀* .Iso.fwd∘bwd≈id .*≈* ._≈s_.func-eq {φ} φ≈ψ .*≈* ._≈s_.func-eq {x} x≈y =
  S.trans S.·-comm
    (S.trans (S.sym (φ .preserve-· {x} {S.ι}))
      (φ≈ψ .*≈* ._≈s_.func-eq (S.trans (S.trans S.·-comm S.·-lunit) x≈y)))
𝕀≅𝕀* .Iso.bwd∘fwd≈id .*≈* ._≈s_.func-eq a≈b = S.trans (S.trans S.·-comm S.·-lunit) a≈b

------------------------------------------------------------------------------
-- Dual preserves isomorphisms (contravariantly) and the zero object.

Dual-iso : ∀ {M N} → Iso M N → Iso (Dual N) (Dual M)
Dual-iso iso .Iso.fwd = (iso .Iso.fwd) ᵀ
Dual-iso iso .Iso.bwd = (iso .Iso.bwd) ᵀ
Dual-iso iso .Iso.fwd∘bwd≈id =
  ≈-trans (≈-sym (ᵀ-comp (iso .Iso.bwd) (iso .Iso.fwd))) (≈-trans (ᵀ-cong (iso .Iso.bwd∘fwd≈id)) ᵀ-id)
Dual-iso iso .Iso.bwd∘fwd≈id =
  ≈-trans (≈-sym (ᵀ-comp (iso .Iso.fwd) (iso .Iso.bwd))) (≈-trans (ᵀ-cong (iso .Iso.fwd∘bwd≈id)) ᵀ-id)

𝟘≅𝟘* : Iso 𝟘 (Dual 𝟘)
𝟘≅𝟘* .Iso.fwd = εm
𝟘≅𝟘* .Iso.bwd = HasTerminal.to-terminal terminal
𝟘≅𝟘* .Iso.fwd∘bwd≈id .*≈* ._≈s_.func-eq {_} {ψ} _ .*≈* ._≈s_.func-eq _ =
  sym 𝕀 (trans 𝕀 (ψ .func-resp-≈ tt) (ψ .preserve-ze))
𝟘≅𝟘* .Iso.bwd∘fwd≈id = HasTerminal.to-terminal-unique terminal _ _

Dual-⊕-iso : ∀ {M N} → Iso (Dual (M ⊕ N)) (Dual M ⊕ Dual N)
Dual-⊕-iso {M} {N} = IsIso→Iso (biproduct-iso cmon-enriched Dual-preserves-⊕ (biproduct (Dual M) (Dual N)))

⊕-iso : ∀ {M M' N N'} → Iso M M' → Iso N N' → Iso (M ⊕ N) (M' ⊕ N')
⊕-iso = HasCoproducts.coproduct-preserve-iso (biproducts→coproducts cmon-enriched biproduct)

-- The biproduct of two self-dualities is a self-duality of the biproduct.
⊕-self-dual : ∀ {M N} → Iso M (Dual M) → Iso N (Dual N) → Iso (M ⊕ N) (Dual (M ⊕ N))
⊕-self-dual M≅M* N≅N* = Iso-trans (⊕-iso M≅M* N≅N*) (Iso-sym Dual-⊕-iso)

⊕-iso-fwd : ∀ {M N} (M≅M* : Iso M (Dual M)) (N≅N* : Iso N (Dual N)) {x : M .Carrier} {y : N .Carrier} →
            (Dual M ⊕ Dual N) ._≈_ (⊕-iso M≅M* N≅N* .Iso.fwd .func (x , y))
                                   (M≅M* .Iso.fwd .func x , N≅N* .Iso.fwd .func y)
⊕-iso-fwd {M} {N} M≅M* N≅N* .proj₁ = trans (Dual M) (+-comm (Dual M)) (+-lunit (Dual M))
⊕-iso-fwd {M} {N} M≅M* N≅N* .proj₂ = +-lunit (Dual N)

pairing-⊕ : ∀ {M N} (M≅M* : Iso M (Dual M)) (N≅N* : Iso N (Dual N)) {x x' : M .Carrier} {y y' : N .Carrier} →
            pairing (⊕-self-dual M≅M* N≅N*) (x , y) (x' , y') S.≈ ((pairing M≅M* x x') S.+ (pairing N≅N* y y'))
pairing-⊕ {M} {N} M≅M* N≅N* {x} {x'} {y} {y'} =
  S.trans (Dual-⊕-iso .Iso.bwd .func-resp-≈ (⊕-iso-fwd M≅M* N≅N* {x} {y}) .*≈* ._≈s_.func-eq (refl (M ⊕ N)))
          S.refl

------------------------------------------------------------------------------
-- Conjugate of a morphism w.r.t. chosen self-dualities d : M ≅ Dual M.

module _ {M N} (M≅M* : Iso M (Dual M)) (N≅N* : Iso N (Dual N)) where

  conj : (M ⇒ N) → (N ⇒ M)
  conj f = M≅M* .Iso.bwd ∘ (f ᵀ ∘ N≅N* .Iso.fwd)

  conj-transpose : (f : M ⇒ N) → M≅M* .Iso.fwd ∘ conj f ≈m f ᵀ ∘ N≅N* .Iso.fwd
  conj-transpose f =
    ≈-trans (≈-sym (assoc (M≅M* .Iso.fwd) (M≅M* .Iso.bwd) (f ᵀ ∘ N≅N* .Iso.fwd)))
            (≈-trans (∘-cong (M≅M* .Iso.fwd∘bwd≈id) (≈-refl {f = f ᵀ ∘ N≅N* .Iso.fwd})) id-left)

  -- Pointwise conjugate equivalence ⟨ conj f y , x ⟩ ≈ ⟨ y , f x ⟩.
  conj-pairing : ∀ (f : M ⇒ N) {x y} →
                 pairing M≅M* (conj f .*→* ._⇒s_.func y) x S.≈ pairing N≅N* y (f .*→* ._⇒s_.func x)
  conj-pairing f =
    conj-transpose f .*≈* ._≈s_.func-eq (refl N) .*≈* ._≈s_.func-eq (refl M)

  -- conj swaps pairing-orthogonality: (⟨ y , f x ⟩ ≈ ε ⇔ ⟨ conj f y , x ⟩ ≈ ε).
  conj-⊥ : ∀ (f : M ⇒ N) {x y} →
           (pairing N≅N* y (f .*→* ._⇒s_.func x) S.≈ S.ε) ⇔ (pairing M≅M* (conj f .*→* ._⇒s_.func y) x S.≈ S.ε)
  conj-⊥ f .proj₁ p = S.trans (conj-pairing f) p
  conj-⊥ f .proj₂ q = S.trans (S.sym (conj-pairing f)) q

------------------------------------------------------------------------------
-- Semimodule with a chosen self-duality.

record SelfDual : Set (suc 0ℓ) where
  field
    obj  : Semimodule
    dual : Iso obj (Dual obj)
-- local open so the obj/dual projections don't leak to SelfDualDistributiveLattice below.
module _ where
  open SelfDual

  𝕀-sd : SelfDual
  𝕀-sd .obj = 𝕀
  𝕀-sd .dual = 𝕀≅𝕀*

  𝟘-sd : SelfDual
  𝟘-sd .obj = 𝟘
  𝟘-sd .dual = 𝟘≅𝟘*

  ⊕-sd : SelfDual → SelfDual → SelfDual
  ⊕-sd X Y .obj = X .obj ⊕ Y .obj
  ⊕-sd X Y .dual = ⊕-self-dual (X .dual) (Y .dual)

  -- The conjugate of a morphism, with self-dualities read off the objects.
  conjugate : (X Y : SelfDual) → (X .obj ⇒ Y .obj) → (Y .obj ⇒ X .obj)
  conjugate X Y = conj (X .dual) (Y .dual)

------------------------------------------------------------------------------
module _ (𝒮 : Category 0ℓ 0ℓ 0ℓ) where
  private
    module 𝒮 = Category 𝒮

  open Functor
  open NatTrans
  open ≃-NatTrans

  -- Set of Natural Transformations Id ⇒ D
  record Π-Carrier (D : Functor 𝒮 cat) : Set (0ℓ) where
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

-- The data making the scalar S a Boolean algebra: idempotent meet, top-absorbing join, and a complemented
-- negation.  The complement laws are the 𝕀-order `_≤_ 𝕀` unfolded (`(a + b) ≈ b`), stated here so the record
-- needs nothing from JoinSemilattices below.
record BooleanSemiring : Set where
  field
    ∧-idem       : ∀ {x} → (x S.· x) S.≈ x
    ⊤-add-top    : ∀ {x} → (S.ι S.+ x) S.≈ S.ι
    ¬            : S.Carrier → S.Carrier
    complement-∧ : ∀ {x} → ((x S.· ¬ x) S.+ S.ε) S.≈ S.ε
    complement-∨ : ∀ {x} → (S.ι S.+ (x S.+ ¬ x)) S.≈ (x S.+ ¬ x)

------------------------------------------------------------------------------
-- Top-absorption makes addition idempotent, so every S-semimodule is a bounded join-semilattice and every
-- morphism join-preserving.

module JoinSemilattices
  (⊤-add-top : ∀ {x} → (S.ι S.+ x) S.≈ S.ι)
  where

  open import preorder using (Preorder)
  open import basics using (IsPreorder; IsJoin; IsBottom; IsMeet; IsTop; module Disjoint)
  open import join-semilattice using (JoinSemilattice) renaming (_=>_ to _=>J_)
  open import meet-semilattice using (MeetSemilattice) renaming (_⊕_ to _⊕ₘ_)
  open import lattice using (DistributiveLattice; BooleanAlgebra)
  open import conjugate using (_⇒c_)

  module _ (M : Semimodule) where
    private module M = Semimodule M

    +-idem : {x : M.Carrier} → (x M.+ x) M.≈ x
    +-idem =
      M.trans (M.+-cong (M.sym M.·-unit) (M.sym M.·-unit))
        (M.trans (M.sym M.+-distribʳ)
          (M.trans (M.·-cong ⊤-add-top M.refl) M.·-unit))

    infix 4 _≤_

    _≤_ : M.Carrier → M.Carrier → Prop
    x ≤ y = (x M.+ y) M.≈ y

    ≤-isPreorder : IsPreorder _≤_
    ≤-isPreorder .IsPreorder.refl = +-idem
    ≤-isPreorder .IsPreorder.trans x≤y y≤z =
      M.trans (M.+-cong M.refl (M.sym y≤z)) (M.trans (M.sym M.+-assoc) (M.trans (M.+-cong x≤y M.refl) y≤z))

    ≈→≤ : ∀ {x y} → x M.≈ y → x ≤ y
    ≈→≤ x≈y = M.trans (M.+-cong x≈y M.refl) +-idem

    preorder : Preorder
    preorder .Preorder.Carrier = M.Carrier
    preorder .Preorder._≤_ = _≤_
    preorder .Preorder.≤-isPreorder = ≤-isPreorder

    ∨-isJoin : IsJoin ≤-isPreorder (M._+_)
    ∨-isJoin .IsJoin.inl = M.trans (M.sym M.+-assoc) (M.+-cong +-idem M.refl)
    ∨-isJoin .IsJoin.inr =
      M.trans (M.+-cong M.refl M.+-comm)
        (M.trans (M.sym M.+-assoc) (M.trans (M.+-cong +-idem M.refl) M.+-comm))
    ∨-isJoin .IsJoin.[_,_] x≤z y≤z = M.trans M.+-assoc (M.trans (M.+-cong M.refl y≤z) x≤z)

    ⊥-isBottom : IsBottom ≤-isPreorder (M.ε)
    ⊥-isBottom .IsBottom.≤-bottom = M.+-lunit

    joins : JoinSemilattice preorder
    joins .JoinSemilattice._∨_ = M._+_
    joins .JoinSemilattice.⊥ = M.ε
    joins .JoinSemilattice.∨-isJoin = ∨-isJoin
    joins .JoinSemilattice.⊥-isBottom = ⊥-isBottom

    -- x + y ≈ ε forces each summand to ε.
    zero-sum-free : ∀ {x y} → (x M.+ y) M.≈ M.ε → prop._∧_ (x M.≈ M.ε) (y M.≈ M.ε)
    zero-sum-free h .proj₁ =
      M.trans (M.sym (M.trans M.+-comm M.+-lunit))
              (≤-isPreorder .IsPreorder.trans (∨-isJoin .IsJoin.inl) (≈→≤ h))
    zero-sum-free h .proj₂ =
      M.trans (M.sym (M.trans M.+-comm M.+-lunit))
              (≤-isPreorder .IsPreorder.trans (∨-isJoin .IsJoin.inr) (≈→≤ h))

  -- Semimodule morphisms are now join-preserving.
  joins-map : ∀ {M N} → (M ⇒ N) → joins M =>J joins N
  joins-map {M} {N} f ._=>J_.func .preorder._=>_.fun = f .func
  joins-map {M} {N} f ._=>J_.func .preorder._=>_.mono x≤y = trans N (sym N (f .preserve-+)) (f .func-resp-≈ x≤y)
  joins-map {M} {N} f ._=>J_.∨-preserving = ≈→≤ N (f .preserve-+)
  joins-map {M} {N} f ._=>J_.⊥-preserving = ≈→≤ N (f .preserve-ze)

  -- Now extend a semimodule's join-semilattice to a self-dual bounded distributive lattice with the condition
  -- that lattice-level disjointness agrees with semimodule-level orthogonality.
  record SelfDualDistributiveLattice : Set (suc 0ℓ) where
    no-eta-equality
    field
      selfDual : SelfDual
    open SelfDual selfDual public

    field
      meets : MeetSemilattice (preorder obj)

    open MeetSemilattice meets using (_∧_)
    open JoinSemilattice (joins obj) using (_∨_)
    open Disjoint (≤-isPreorder obj) (MeetSemilattice.∧-isMeet meets) (JoinSemilattice.⊥-isBottom (joins obj)) using (_#_)

    field
      ∧-∨-distrib : ∀ x y z → _≤_ obj (x ∧ (y ∨ z)) ((x ∧ y) ∨ (x ∧ z))
      align       : ∀ {a b} → (a # b) ⇔ (pairing dual a b S.≈ S.ε)

  -- Embedding of objects into LatConj.
    toObj : DistributiveLattice
    toObj .DistributiveLattice.carrier     = preorder obj
    toObj .DistributiveLattice.meets       = meets
    toObj .DistributiveLattice.joins       = joins obj
    toObj .DistributiveLattice.∧-∨-distrib = ∧-∨-distrib

  -- Embedding of morphisms into LatConj.
  module _ (X Y : SelfDualDistributiveLattice) where
    private
      module X = SelfDualDistributiveLattice X
      module Y = SelfDualDistributiveLattice Y
      module MX = MeetSemilattice X.meets
      module MY = MeetSemilattice Y.meets

    -- Componentwise meet on the biproduct (the meet-semilattice product, but indexed by preorder (X.obj ⊕ Y.obj)).
    meets-⊕ : MeetSemilattice (preorder (X.obj ⊕ Y.obj))
    meets-⊕ .MeetSemilattice._∧_ (x₁ , y₁) (x₂ , y₂) = MX._∧_ x₁ x₂ , MY._∧_ y₁ y₂
    meets-⊕ .MeetSemilattice.⊤ = MX.⊤ , MY.⊤
    meets-⊕ .MeetSemilattice.∧-isMeet .IsMeet.π₁ = MX.∧-isMeet .IsMeet.π₁ , MY.∧-isMeet .IsMeet.π₁
    meets-⊕ .MeetSemilattice.∧-isMeet .IsMeet.π₂ = MX.∧-isMeet .IsMeet.π₂ , MY.∧-isMeet .IsMeet.π₂
    meets-⊕ .MeetSemilattice.∧-isMeet .IsMeet.⟨_,_⟩ (x₁≤y₁ , x₂≤y₂) (x₁≤z₁ , x₂≤z₂) =
      MX.∧-isMeet .IsMeet.⟨_,_⟩ x₁≤y₁ x₁≤z₁ , MY.∧-isMeet .IsMeet.⟨_,_⟩ x₂≤y₂ x₂≤z₂
    meets-⊕ .MeetSemilattice.⊤-isTop .IsTop.≤-top = MX.⊤-isTop .IsTop.≤-top , MY.⊤-isTop .IsTop.≤-top

    ⊕-sddl : SelfDualDistributiveLattice
    ⊕-sddl .SelfDualDistributiveLattice.selfDual    = ⊕-sd X.selfDual Y.selfDual
    ⊕-sddl .SelfDualDistributiveLattice.meets       = meets-⊕
    ⊕-sddl .SelfDualDistributiveLattice.∧-∨-distrib (x₁ , x₂) (y₁ , y₂) (z₁ , z₂) =
      X.∧-∨-distrib x₁ y₁ z₁ , Y.∧-∨-distrib x₂ y₂ z₂
    ⊕-sddl .SelfDualDistributiveLattice.align {x₁ , x₂} {y₁ , y₂} .proj₁ (d₁ , d₂) =
      S.trans (pairing-⊕ X.dual Y.dual)
              (S.trans (S.+-cong (X.align .proj₁ d₁) (Y.align .proj₁ d₂)) S.+-lunit)
    ⊕-sddl .SelfDualDistributiveLattice.align {x₁ , x₂} {y₁ , y₂} .proj₂ h =
      let p₁ , p₂ = zero-sum-free 𝕀 (S.trans (S.sym (pairing-⊕ X.dual Y.dual)) h)
      in X.align .proj₂ p₁ , Y.align .proj₂ p₂

    to-conj : X.obj ⇒ Y.obj → X.toObj ⇒c Y.toObj
    to-conj f ._⇒c_.right = joins-map f
    to-conj f ._⇒c_.left = joins-map (conjugate X.selfDual Y.selfDual f)
    to-conj f ._⇒c_.conjugate =
      trans-⇔ Y.align (trans-⇔ (conj-⊥ X.dual Y.dual f) (sym-⇔ X.align))

  -- A self-dual distributive lattice with a Boolean negation, following unused/matrix.agda's BooleanAlgebra
  -- (¬, complement-∨, complement-∧).  Heyting weakens these to a residual ⇨, but then the Galois right
  -- adjoint is the entry-wise ⊓ᵢ (M i j ⇨ x i) rather than this coordinate-free ¬ ∘ conjugate ∘ ¬.
  record BooleanSDDL : Set (suc 0ℓ) where
    field selfDualLat : SelfDualDistributiveLattice
    open SelfDualDistributiveLattice selfDualLat public
    private
      module MM = MeetSemilattice meets
      module JM = JoinSemilattice (joins obj)
    open MM using (_∧_; ⊤; ∧-mono; π₁; π₂; ≤-top) renaming (⟨_∧_⟩ to ⟨_,_⟩∧)
    open JM using (_∨_; ⊥; ∨-mono; [_∨_]; ≤-bottom)
    open IsPreorder (≤-isPreorder obj) using () renaming (refl to ≤-refl; trans to ≤-trans)
    open Disjoint (≤-isPreorder obj) (MeetSemilattice.∧-isMeet meets) (JoinSemilattice.⊥-isBottom (joins obj))
      using (_#_; #-sym) public
    field
      boolean : BooleanAlgebra toObj
    open BooleanAlgebra boolean public
      using (¬; complement-∧; complement-∨; ¬-antitone) renaming (#-↔-≤¬ to #-≤-¬)

    ≤-#-¬ : ∀ {a b} → (_≤_ obj a b) ⇔ (a # ¬ b)
    ≤-#-¬ .proj₁ a≤b = ≤-trans (∧-mono a≤b ≤-refl) complement-∧
    ≤-#-¬ {a} {b} .proj₂ a#¬b =
      ≤-trans ⟨ ≤-refl , ≤-top ⟩∧
        (≤-trans (∧-mono ≤-refl complement-∨)
          (≤-trans (∧-∨-distrib a b (¬ b))
            (≤-trans (∨-mono ≤-refl a#¬b) [ π₂ ∨ ≤-bottom ])))

  import galois

  -- The galois object underlying a BooleanSDDL (galois.Obj = DistributiveLattice without the ∧-∨-distrib field).
  toObjG : BooleanSDDL → galois.Obj
  toObjG X .galois.Obj.carrier = preorder (BooleanSDDL.obj X)
  toObjG X .galois.Obj.meets   = BooleanSDDL.meets X
  toObjG X .galois.Obj.joins   = joins (BooleanSDDL.obj X)

  -- Galois-connection embedding: left = the forward action, right = ¬ ∘ conjugate ∘ ¬ (the De Morgan dual
  -- of the transpose, which is the meet-preserving Galois adjoint).
  module _ (X Y : BooleanSDDL) where
    private
      module X = BooleanSDDL X
      module Y = BooleanSDDL Y

    to-gal : X.obj ⇒ Y.obj → galois._⇒g_ (toObjG Y) (toObjG X)
    to-gal f .galois._⇒g_.left = joins-map f ._=>J_.func
    to-gal f .galois._⇒g_.right .preorder._=>_.fun x =
      X.¬ (joins-map (conjugate X.selfDual Y.selfDual f) ._=>J_.func .preorder._=>_.fun (Y.¬ x))
    to-gal f .galois._⇒g_.right .preorder._=>_.mono x≤x' =
      X.¬-antitone (joins-map (conjugate X.selfDual Y.selfDual f) ._=>J_.func .preorder._=>_.mono (Y.¬-antitone x≤x'))
    to-gal f .galois._⇒g_.left⊣right =
      sym-⇔ (trans-⇔ Y.≤-#-¬
            (trans-⇔ (record { proj₁ = Y.#-sym ; proj₂ = Y.#-sym })
            (trans-⇔ Y.align
            (trans-⇔ (conj-⊥ X.dual Y.dual f)
            (trans-⇔ (sym-⇔ X.align)
            (trans-⇔ (record { proj₁ = X.#-sym ; proj₂ = X.#-sym }) X.#-≤-¬))))))

  -- A self-dual distributive lattice structure transports along any semimodule isomorphism.
  module _ (P : SelfDualDistributiveLattice) {N : Semimodule}
           (N≅M : Iso N (SelfDualDistributiveLattice.obj P)) where
    open SelfDualDistributiveLattice
    open SelfDual
    private
      module P  = SelfDualDistributiveLattice P
      module MP = MeetSemilattice P.meets
      module M  = Semimodule P.obj
      module N  = Semimodule N
      open Iso N≅M

      fwd∘bwd : ∀ {z} → fwd .func (bwd .func z) M.≈ z
      fwd∘bwd = fwd∘bwd≈id .*≈* ._≈s_.func-eq M.refl

      bwd∘fwd : ∀ {a} → bwd .func (fwd .func a) N.≈ a
      bwd∘fwd = bwd∘fwd≈id .*≈* ._≈s_.func-eq N.refl

      -- fwd preserves and reflects the order.
      ≤-fwd : ∀ {x y} → _≤_ N x y → _≤_ P.obj (fwd .func x) (fwd .func y)
      ≤-fwd x≤y = M.trans (M.sym (fwd .preserve-+)) (fwd .func-resp-≈ x≤y)
      ≤-bwd : ∀ {x y} → _≤_ P.obj (fwd .func x) (fwd .func y) → _≤_ N x y
      ≤-bwd {x} {y} h =
        N.trans (N.sym (bwd∘fwd {x N.+ y}))
          (N.trans (bwd .func-resp-≈ (fwd .preserve-+))
            (N.trans (bwd .func-resp-≈ h) (bwd∘fwd {y})))

      ≤M-resp : ∀ {x x' y y'} → x M.≈ x' → y M.≈ y' → _≤_ P.obj x y → _≤_ P.obj x' y'
      ≤M-resp x≈x' y≈y' h = M.trans (M.+-cong (M.sym x≈x') (M.sym y≈y')) (M.trans h y≈y')

      ≤-antisym : ∀ {x y} → _≤_ P.obj x y → _≤_ P.obj y x → x M.≈ y
      ≤-antisym x≤y y≤x = M.trans (M.sym y≤x) (M.trans M.+-comm x≤y)

      ∧≈ : ∀ {a a' b b'} → a M.≈ a' → b M.≈ b' → MP._∧_ a b M.≈ MP._∧_ a' b'
      ∧≈ a≈a' b≈b' =
        ≤-antisym (MP.∧-mono (≈→≤ P.obj a≈a') (≈→≤ P.obj b≈b'))
                  (MP.∧-mono (≈→≤ P.obj (M.sym a≈a')) (≈→≤ P.obj (M.sym b≈b')))

      meets' : MeetSemilattice (preorder N)
      meets' .MeetSemilattice._∧_ a b = bwd .func (MP._∧_ (fwd .func a) (fwd .func b))
      meets' .MeetSemilattice.⊤ = bwd .func MP.⊤
      meets' .MeetSemilattice.∧-isMeet .IsMeet.π₁ =
        ≤-bwd (≤M-resp (M.sym fwd∘bwd) M.refl (MP.∧-isMeet .IsMeet.π₁))
      meets' .MeetSemilattice.∧-isMeet .IsMeet.π₂ =
        ≤-bwd (≤M-resp (M.sym fwd∘bwd) M.refl (MP.∧-isMeet .IsMeet.π₂))
      meets' .MeetSemilattice.∧-isMeet .IsMeet.⟨_,_⟩ a≤b a≤c =
        ≤-bwd (≤M-resp M.refl (M.sym fwd∘bwd) (MP.∧-isMeet .IsMeet.⟨_,_⟩ (≤-fwd a≤b) (≤-fwd a≤c)))
      meets' .MeetSemilattice.⊤-isTop .IsTop.≤-top =
        ≤-bwd (≤M-resp M.refl (M.sym fwd∘bwd) (MP.⊤-isTop .IsTop.≤-top))

      -- Disjointness transports: a # b iff fwd a # fwd b.
      #⇔# : ∀ {a b} → _≤_ N (bwd .func (MP._∧_ (fwd .func a) (fwd .func b))) N.ε ⇔
                      _≤_ P.obj (MP._∧_ (fwd .func a) (fwd .func b)) M.ε
      #⇔# .proj₁ h = ≤M-resp fwd∘bwd (fwd .preserve-ze) (≤-fwd h)
      #⇔# .proj₂ h = ≤-bwd (≤M-resp (M.sym fwd∘bwd) (M.sym (fwd .preserve-ze)) h)

    transport-sddl : SelfDualDistributiveLattice
    transport-sddl .selfDual .obj  = N
    transport-sddl .selfDual .dual = Iso-trans N≅M (Iso-trans P.dual (Dual-iso N≅M))
    transport-sddl .meets     = meets'
    transport-sddl .∧-∨-distrib x y z =
      ≤-bwd (≤M-resp (M.sym (M.trans fwd∘bwd (∧≈ M.refl (fwd .preserve-+))))
                     (M.sym (M.trans (fwd .preserve-+) (M.+-cong fwd∘bwd fwd∘bwd)))
                     (P.∧-∨-distrib (fwd .func x) (fwd .func y) (fwd .func z)))
    transport-sddl .align {a} {b} = trans-⇔ #⇔# P.align

  -- A BooleanSDDL transports along an iso likewise: the SDDL via transport-sddl, the negation conjugated
  -- through the iso (¬' = bwd ∘ ¬ ∘ fwd), complements carried along.
  module _ (P : BooleanSDDL) {N : Semimodule}
           (N≅M : Iso N (BooleanSDDL.obj P)) where
    open SelfDualDistributiveLattice
    private
      module P  = BooleanSDDL P
      module MP = MeetSemilattice P.meets
      module M  = Semimodule P.obj
      module N  = Semimodule N
      open Iso N≅M

      fwd∘bwd : ∀ {z} → fwd .func (bwd .func z) M.≈ z
      fwd∘bwd = fwd∘bwd≈id .*≈* ._≈s_.func-eq M.refl
      bwd∘fwd : ∀ {a} → bwd .func (fwd .func a) N.≈ a
      bwd∘fwd = bwd∘fwd≈id .*≈* ._≈s_.func-eq N.refl
      ≤-fwd : ∀ {x y} → _≤_ N x y → _≤_ P.obj (fwd .func x) (fwd .func y)
      ≤-fwd x≤y = M.trans (M.sym (fwd .preserve-+)) (fwd .func-resp-≈ x≤y)
      ≤-bwd : ∀ {x y} → _≤_ P.obj (fwd .func x) (fwd .func y) → _≤_ N x y
      ≤-bwd {x} {y} h =
        N.trans (N.sym (bwd∘fwd {x N.+ y}))
          (N.trans (bwd .func-resp-≈ (fwd .preserve-+))
            (N.trans (bwd .func-resp-≈ h) (bwd∘fwd {y})))
      ≤M-resp : ∀ {x x' y y'} → x M.≈ x' → y M.≈ y' → _≤_ P.obj x y → _≤_ P.obj x' y'
      ≤M-resp x≈x' y≈y' h = M.trans (M.+-cong (M.sym x≈x') (M.sym y≈y')) (M.trans h y≈y')
      ≤-antisym : ∀ {x y} → _≤_ P.obj x y → _≤_ P.obj y x → x M.≈ y
      ≤-antisym x≤y y≤x = M.trans (M.sym y≤x) (M.trans M.+-comm x≤y)
      ∧≈ : ∀ {a a' b b'} → a M.≈ a' → b M.≈ b' → MP._∧_ a b M.≈ MP._∧_ a' b'
      ∧≈ a≈a' b≈b' =
        ≤-antisym (MP.∧-mono (≈→≤ P.obj a≈a') (≈→≤ P.obj b≈b'))
                  (MP.∧-mono (≈→≤ P.obj (M.sym a≈a')) (≈→≤ P.obj (M.sym b≈b')))

    transport-bsddl : BooleanSDDL
    transport-bsddl .BooleanSDDL.selfDualLat = transport-sddl P.selfDualLat N≅M
    transport-bsddl .BooleanSDDL.boolean .BooleanAlgebra.¬ a = bwd .func (P.¬ (fwd .func a))
    transport-bsddl .BooleanSDDL.boolean .BooleanAlgebra.complement-∧ =
      ≤-bwd (≤M-resp (M.sym (M.trans fwd∘bwd (∧≈ M.refl fwd∘bwd)))
                     (M.sym (fwd .preserve-ze))
                     P.complement-∧)
    transport-bsddl .BooleanSDDL.boolean .BooleanAlgebra.complement-∨ =
      ≤-bwd (≤M-resp (M.sym fwd∘bwd)
                     (M.sym (M.trans (fwd .preserve-+) (M.+-cong M.refl fwd∘bwd)))
                     P.complement-∨)

  -- With S a bounded distributive lattice, 𝕀 (and every n-ary biproduct of it) is one too, with
  -- multiplication as the meet.
  module DistribLattices (∧-idem : ∀ {x} → (x S.· x) S.≈ x) where

    private
      ∨-∧-absorption : ∀ {a b} → (a S.+ (a S.· b)) S.≈ a
      ∨-∧-absorption =
        S.trans (S.+-cong (S.trans (S.sym S.·-lunit) S.·-comm) S.refl)
                (S.trans (S.sym S.·-+-distribₗ)
                         (S.trans (S.·-cong S.refl ⊤-add-top) (S.trans S.·-comm S.·-lunit)))

      ∧-monoʳ : ∀ {a b c} → _≤_ 𝕀 a b → _≤_ 𝕀 (c S.· a) (c S.· b)
      ∧-monoʳ a≤b = S.trans (S.sym S.·-+-distribₗ) (S.·-cong S.refl a≤b)

      ∧-monoˡ : ∀ {a b c} → _≤_ 𝕀 a b → _≤_ 𝕀 (a S.· c) (b S.· c)
      ∧-monoˡ a≤b = S.trans (S.sym S.·-+-distribᵣ) (S.·-cong a≤b S.refl)

    𝕀-meet : MeetSemilattice (preorder 𝕀)
    𝕀-meet .MeetSemilattice._∧_ = S._·_
    𝕀-meet .MeetSemilattice.⊤ = S.ι
    𝕀-meet .MeetSemilattice.∧-isMeet .IsMeet.π₁ = S.trans S.+-comm ∨-∧-absorption
    𝕀-meet .MeetSemilattice.∧-isMeet .IsMeet.π₂ =
      S.trans (S.+-cong S.·-comm S.refl) (S.trans S.+-comm ∨-∧-absorption)
    𝕀-meet .MeetSemilattice.∧-isMeet .IsMeet.⟨_,_⟩ x≤y x≤z =
      ≤-isPreorder 𝕀 .IsPreorder.trans
        (S.trans (S.+-cong (S.sym ∧-idem) S.refl) (∧-monoʳ x≤z)) (∧-monoˡ x≤y)
    𝕀-meet .MeetSemilattice.⊤-isTop .IsTop.≤-top = S.trans S.+-comm ⊤-add-top

    𝕀-sddl : SelfDualDistributiveLattice
    𝕀-sddl .SelfDualDistributiveLattice.selfDual    = 𝕀-sd
    𝕀-sddl .SelfDualDistributiveLattice.meets       = 𝕀-meet
    𝕀-sddl .SelfDualDistributiveLattice.∧-∨-distrib x y z = ≈→≤ 𝕀 S.·-+-distribₗ
    𝕀-sddl .SelfDualDistributiveLattice.align .proj₁ h = S.trans (S.sym (S.trans S.+-comm S.+-lunit)) h
    𝕀-sddl .SelfDualDistributiveLattice.align .proj₂ h = ≈→≤ 𝕀 h

    -- 𝟘 (= ⊕⁰ 𝕀) is trivially a self-dual distributive lattice.
    𝟘-sddl : SelfDualDistributiveLattice
    𝟘-sddl .SelfDualDistributiveLattice.selfDual                                   = 𝟘-sd
    𝟘-sddl .SelfDualDistributiveLattice.meets .MeetSemilattice._∧_ _ _             = 𝟘 .ε
    𝟘-sddl .SelfDualDistributiveLattice.meets .MeetSemilattice.⊤                   = 𝟘 .ε
    𝟘-sddl .SelfDualDistributiveLattice.meets .MeetSemilattice.∧-isMeet .IsMeet.π₁ = tt
    𝟘-sddl .SelfDualDistributiveLattice.meets .MeetSemilattice.∧-isMeet .IsMeet.π₂ = tt
    𝟘-sddl .SelfDualDistributiveLattice.meets .MeetSemilattice.∧-isMeet .IsMeet.⟨_,_⟩ _ _ = tt
    𝟘-sddl .SelfDualDistributiveLattice.meets .MeetSemilattice.⊤-isTop .IsTop.≤-top = tt
    𝟘-sddl .SelfDualDistributiveLattice.∧-∨-distrib _ _ _                          = tt
    𝟘-sddl .SelfDualDistributiveLattice.align .proj₁ _                             = S.refl
    𝟘-sddl .SelfDualDistributiveLattice.align .proj₂ _                             = tt

    -- n-fold biproduct of 𝕀: the free self-dual distributive lattice on n generators.
    ⊕ⁿ : ℕ → SelfDualDistributiveLattice
    ⊕ⁿ ℕ.zero    = 𝟘-sddl
    ⊕ⁿ (ℕ.suc n) = ⊕-sddl 𝕀-sddl (⊕ⁿ n)

    -- Given a Boolean negation on the scalar, every free lattice 𝕀/𝟘/⊕ⁿ is a BooleanSDDL (¬ pointwise).
    module _ (¬ : S.Carrier → S.Carrier)
             (complement-∧ : ∀ {x} → _≤_ 𝕀 (x S.· ¬ x) S.ε)
             (complement-∨ : ∀ {x} → _≤_ 𝕀 S.ι (x S.+ ¬ x)) where
      𝕀-bsddl : BooleanSDDL
      𝕀-bsddl .BooleanSDDL.selfDualLat = 𝕀-sddl
      𝕀-bsddl .BooleanSDDL.boolean .BooleanAlgebra.¬ = ¬
      𝕀-bsddl .BooleanSDDL.boolean .BooleanAlgebra.complement-∧ = complement-∧
      𝕀-bsddl .BooleanSDDL.boolean .BooleanAlgebra.complement-∨ = complement-∨

      𝟘-bsddl : BooleanSDDL
      𝟘-bsddl .BooleanSDDL.selfDualLat = 𝟘-sddl
      𝟘-bsddl .BooleanSDDL.boolean .BooleanAlgebra.¬ x = x
      𝟘-bsddl .BooleanSDDL.boolean .BooleanAlgebra.complement-∧ = tt
      𝟘-bsddl .BooleanSDDL.boolean .BooleanAlgebra.complement-∨ = tt

      ⊕-bsddl : BooleanSDDL → BooleanSDDL → BooleanSDDL
      ⊕-bsddl X Y .BooleanSDDL.selfDualLat = ⊕-sddl (BooleanSDDL.selfDualLat X) (BooleanSDDL.selfDualLat Y)
      ⊕-bsddl X Y .BooleanSDDL.boolean .BooleanAlgebra.¬ (a , b) = BooleanSDDL.¬ X a , BooleanSDDL.¬ Y b
      ⊕-bsddl X Y .BooleanSDDL.boolean .BooleanAlgebra.complement-∧ {a , b} = BooleanSDDL.complement-∧ X , BooleanSDDL.complement-∧ Y
      ⊕-bsddl X Y .BooleanSDDL.boolean .BooleanAlgebra.complement-∨ {a , b} = BooleanSDDL.complement-∨ X , BooleanSDDL.complement-∨ Y

      ⊕ⁿ-bsddl : ℕ → BooleanSDDL
      ⊕ⁿ-bsddl ℕ.zero    = 𝟘-bsddl
      ⊕ⁿ-bsddl (ℕ.suc n) = ⊕-bsddl 𝕀-bsddl (⊕ⁿ-bsddl n)
