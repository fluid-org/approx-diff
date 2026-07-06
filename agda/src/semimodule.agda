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

-- Unit and associativity isomorphisms for the biproduct, constructed concretely on the pair
-- representation.
module _ where
  open Category cat using (Iso)
  open _⇒_
  open _≈m_
  import Level
  import Agda.Builtin.Unit
  open import prop-setoid using () renaming (_≃m_ to _≈s_)

  ⊕-lunit-iso : ∀ {N} → Iso (𝟘 ⊕ N) N
  ⊕-lunit-iso {N} .Iso.fwd .*→* ._⇒s_.func (_ , n) = n
  ⊕-lunit-iso {N} .Iso.fwd .*→* ._⇒s_.func-resp-≈ (_ , e) = e
  ⊕-lunit-iso {N} .Iso.fwd .preserve-ze = refl N
  ⊕-lunit-iso {N} .Iso.fwd .preserve-+ = refl N
  ⊕-lunit-iso {N} .Iso.fwd .preserve-· = refl N
  ⊕-lunit-iso {N} .Iso.bwd .*→* ._⇒s_.func n = Level.lift Agda.Builtin.Unit.tt , n
  ⊕-lunit-iso {N} .Iso.bwd .*→* ._⇒s_.func-resp-≈ e = tt , e
  ⊕-lunit-iso {N} .Iso.bwd .preserve-ze = tt , refl N
  ⊕-lunit-iso {N} .Iso.bwd .preserve-+ = tt , refl N
  ⊕-lunit-iso {N} .Iso.bwd .preserve-· = tt , refl N
  ⊕-lunit-iso {N} .Iso.fwd∘bwd≈id .*≈* ._≈s_.func-eq e = e
  ⊕-lunit-iso {N} .Iso.bwd∘fwd≈id .*≈* ._≈s_.func-eq (_ , e) = tt , e

  ⊕-assoc-iso : ∀ {M N P} → Iso ((M ⊕ N) ⊕ P) (M ⊕ (N ⊕ P))
  ⊕-assoc-iso {M} {N} {P} .Iso.fwd .*→* ._⇒s_.func ((m , n) , p) = m , (n , p)
  ⊕-assoc-iso {M} {N} {P} .Iso.fwd .*→* ._⇒s_.func-resp-≈ ((em , en) , ep) = em , (en , ep)
  ⊕-assoc-iso {M} {N} {P} .Iso.fwd .preserve-ze = refl M , (refl N , refl P)
  ⊕-assoc-iso {M} {N} {P} .Iso.fwd .preserve-+ = refl M , (refl N , refl P)
  ⊕-assoc-iso {M} {N} {P} .Iso.fwd .preserve-· = refl M , (refl N , refl P)
  ⊕-assoc-iso {M} {N} {P} .Iso.bwd .*→* ._⇒s_.func (m , (n , p)) = (m , n) , p
  ⊕-assoc-iso {M} {N} {P} .Iso.bwd .*→* ._⇒s_.func-resp-≈ (em , (en , ep)) = (em , en) , ep
  ⊕-assoc-iso {M} {N} {P} .Iso.bwd .preserve-ze = (refl M , refl N) , refl P
  ⊕-assoc-iso {M} {N} {P} .Iso.bwd .preserve-+ = (refl M , refl N) , refl P
  ⊕-assoc-iso {M} {N} {P} .Iso.bwd .preserve-· = (refl M , refl N) , refl P
  ⊕-assoc-iso {M} {N} {P} .Iso.fwd∘bwd≈id .*≈* ._≈s_.func-eq (em , (en , ep)) = em , (en , ep)
  ⊕-assoc-iso {M} {N} {P} .Iso.bwd∘fwd≈id .*≈* ._≈s_.func-eq ((em , en) , ep) = (em , en) , ep


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

------------------------------------------------------------------------------
-- Top-absorption makes addition idempotent, so every S-semimodule is a bounded join-semilattice and every
-- morphism join-preserving.

module JoinSemilattices
  (⊤-add-top : ∀ {x} → (S.ι S.+ x) S.≈ S.ι)
  where

  import commutative-monoid

  open import preorder using (Preorder)
  open import basics using (IsPreorder; IsJoin; IsBottom)
  open import join-semilattice using (JoinSemilattice) renaming (_=>_ to _=>J_)

  module _ (M : Semimodule) where
    private module M = Semimodule M

    +-idem : {x : M.Carrier} → (x M.+ x) M.≈ x
    +-idem =
      M.trans (M.+-cong (M.sym M.·-unit) (M.sym M.·-unit))
        (M.trans (M.sym M.+-distribʳ)
          (M.trans (M.·-cong ⊤-add-top M.refl) M.·-unit))

    open commutative-monoid.AdditivePreorder (M .Semimodule.additive) +-idem public
      using (⊑-isPreorder; ∨-isJoin; ⊥-isBottom)
      renaming (_⊑_ to _≤_; ≈→⊑ to ≈→≤; ⊑-antisym to ≤-antisym)

    ≤-isPreorder : IsPreorder _≤_
    ≤-isPreorder = ⊑-isPreorder

    preorder : Preorder
    preorder .Preorder.Carrier = M.Carrier
    preorder .Preorder._≤_ = _≤_
    preorder .Preorder.≤-isPreorder = ≤-isPreorder

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
