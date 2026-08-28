{-# OPTIONS --postfix-projections --prop --safe #-}

module matrix where

open import Level using (0ℓ)
open import prop-setoid using (Setoid)
import Relation.Binary.PropositionalEquality as ≡
open import commutative-semiring using (CommutativeSemiring)

-- Matrices over a commutative semiring S. (Commutativity means the dot product is commutative, which means
-- transpose preserves composition, i.e. AB^T = B^T A^T.)
module Mat {o ℓ} {A : Setoid o ℓ} (S : CommutativeSemiring A) where

  open CommutativeSemiring S public
  open import Data.Nat using (ℕ; zero; suc)
  open import Data.Fin using (Fin; zero; suc)

  Vec : ℕ → Set o
  Vec n = Fin n → Carrier

  e : ∀ {n} → Fin n → Vec n
  e zero zero = ι
  e zero (suc _) = ε
  e (suc i) zero = ε
  e (suc i) (suc j) = e i j

  Σ : ∀ {n} → (Fin n → Carrier) → Carrier
  Σ {zero} _ = ε
  Σ {suc n} f = f zero + Σ {n} (λ i → f (suc i))

  infixl 21 _⋅_
  _⋅_ : ∀ {n} → Vec n → Vec n → Carrier
  _⋅_ {n} u v = Σ {n} λ i → u i · v i

  Matrix : ℕ → ℕ → Set o
  Matrix m n = Fin m → Fin n → Carrier

  I : ∀ {n} → Matrix n n
  I = e

  _∘_ : ∀ {m n k} → Matrix m n → Matrix n k → Matrix m k
  (M ∘ N) i k = Σ (λ j → M i j · N j k)

  infixl 21 _∘_

  _ᵀ : ∀ {m n} → Matrix m n → Matrix n m
  (M ᵀ) i j = M j i

  _≈ₘ_ : ∀ {m n} → Matrix m n → Matrix m n → Prop ℓ
  M ≈ₘ N = ∀ i j → M i j ≈ N i j

  open import Level using (Level; _⊔_)
  open import prop using (tt)
  open import prop-setoid using (IsEquivalence)
  open import categories using (Category)

  module +-to-Σ
    {p} (_~_ : Carrier → Carrier → Prop p)
    (~-refl : ∀ {x} → x ~ x)
    (+-preserves : ∀ {x₁ x₂ y₁ y₂} → x₁ ~ x₂ → y₁ ~ y₂ → (x₁ + y₁) ~ (x₂ + y₂))
    where

    Σ-preserves : ∀ {n} {f g : Fin n → Carrier} → (∀ i → f i ~ g i) → Σ {n} f ~ Σ {n} g
    Σ-preserves {zero} _ = ~-refl
    Σ-preserves {suc n} h = +-preserves (h zero) (Σ-preserves {n} (λ i → h (suc i)))

  Σ-cong : ∀ {n} {f g : Fin n → Carrier} → (∀ i → f i ≈ g i) → Σ {n} f ≈ Σ {n} g
  Σ-cong = +-to-Σ.Σ-preserves _≈_ refl +-cong

  -- Equality version; not an instance of Σ-preserves, which takes Prop-valued relations.
  Σ-cong-≡ : ∀ {n} {f g : Fin n → Carrier} → (∀ i → f i ≡.≡ g i) → Σ {n} f ≡.≡ Σ {n} g
  Σ-cong-≡ {zero}  p = ≡.refl
  Σ-cong-≡ {suc n} p = ≡.cong₂ _+_ (p zero) (Σ-cong-≡ {n} (λ i → p (suc i)))

  e-sym : ∀ {n} (i j : Fin n) → e i j ≈ e j i
  e-sym zero zero = refl
  e-sym zero (suc _) = refl
  e-sym (suc _) zero = refl
  e-sym (suc i) (suc j) = e-sym i j

  Σ-ε : ∀ {n} → Σ {n} (λ _ → ε) ≈ ε
  Σ-ε {zero} = refl
  Σ-ε {suc n} = trans +-lunit (Σ-ε {n})

  private
    Σ-ε· : ∀ {n} (f : Fin n → Carrier) → Σ {n} (λ j → ε · f j) ≈ ε
    Σ-ε· {n} f = trans (Σ-cong {n} (λ j → ε-annihilₗ)) (Σ-ε {n})

    ·ε-Σ : ∀ {n} (f : Fin n → Carrier) → Σ {n} (λ j → f j · ε) ≈ ε
    ·ε-Σ {n} f = trans (Σ-cong {n} (λ j → ε-annihilᵣ)) (Σ-ε {n})

    ε·+ : ∀ {x y} → ((ε · x) + y) ≈ y
    ε·+ = trans (+-cong ε-annihilₗ refl) +-lunit

  Σ-unit : ∀ {n} (i : Fin n) (f : Fin n → Carrier) → Σ {n} (λ j → e i j · f j) ≈ f i
  Σ-unit {suc n} zero f = trans (+-cong ·-lunit (Σ-ε· {n} _)) +-runit
  Σ-unit {suc n} (suc i) f = trans ε·+ (Σ-unit i (λ j → f (suc j)))

  Σ-·-distribᵣ : ∀ {n} (f : Fin n → Carrier) (x : Carrier) → Σ {n} f · x ≈ Σ {n} (λ j → f j · x)
  Σ-·-distribᵣ {zero} f x = ε-annihilₗ
  Σ-·-distribᵣ {suc n} f x = trans ·-+-distribᵣ (+-cong refl (Σ-·-distribᵣ {n} (λ j → f (suc j)) x))

  Σ-·-distribₗ : ∀ {n} (x : Carrier) (f : Fin n → Carrier) → x · Σ {n} f ≈ Σ {n} (λ j → x · f j)
  Σ-·-distribₗ {n} x f = trans ·-comm (trans (Σ-·-distribᵣ f x) (Σ-cong {n} (λ j → ·-comm)))

  Σ-+ : ∀ {n} (g h : Fin n → Carrier) → Σ {n} g + Σ {n} h ≈ Σ {n} (λ j → g j + h j)
  Σ-+ {zero} g h = +-lunit
  Σ-+ {suc n} g h = trans +-interchange (+-cong refl (Σ-+ {n} (λ j → g (suc j)) (λ j → h (suc j))))

  Σ-interchange : ∀ {m n} (f : Fin m → Fin n → Carrier) → Σ {m} (λ i → Σ {n} (f i)) ≈ Σ {n} (λ j → Σ {m} (λ i → f i j))
  Σ-interchange {zero} {n} f = sym (Σ-ε {n})
  Σ-interchange {suc m} {n} f =
    trans (+-cong refl (Σ-interchange {m} {n} (λ i → f (suc i))))
          (Σ-+ {n} (f zero) (λ j → Σ {m} (λ i → f (suc i) j)))

  ≈ₘ-isEquiv : ∀ {m n} → IsEquivalence (_≈ₘ_ {m} {n})
  ≈ₘ-isEquiv .IsEquivalence.refl i j = refl
  ≈ₘ-isEquiv .IsEquivalence.sym p i j = sym (p i j)
  ≈ₘ-isEquiv .IsEquivalence.trans p q i j = trans (p i j) (q i j)

  ∘-cong : ∀ {m n k} {M₁ M₂ : Matrix m n} {N₁ N₂ : Matrix n k} → M₁ ≈ₘ M₂ → N₁ ≈ₘ N₂ → M₁ ∘ N₁ ≈ₘ M₂ ∘ N₂
  ∘-cong {m} {n} p q i k = Σ-cong {n} (λ j → ·-cong (p i j) (q j k))

  ᵀ-∘ : ∀ {m n k} (M : Matrix m n) (N : Matrix n k) → ((M ∘ N) ᵀ) ≈ₘ ((N ᵀ) ∘ (M ᵀ))
  ᵀ-∘ {n = n} M N k i = Σ-cong {n} (λ j → ·-comm)

  id-left : ∀ {m n} {M : Matrix m n} → I ∘ M ≈ₘ M
  id-left {M = M} i k = Σ-unit i (λ j → M j k)

  id-right : ∀ {m n} {M : Matrix m n} → M ∘ I ≈ₘ M
  id-right {n = n} {M = M} i k =
    trans (Σ-cong {n} (λ j → ·-cong refl (e-sym j k)))
          (trans (Σ-cong {n} (λ j → ·-comm)) (Σ-unit k (M i)))

  assoc : ∀ {m n k l} (M : Matrix m n) (N : Matrix n k) (P : Matrix k l) → (M ∘ N) ∘ P ≈ₘ M ∘ (N ∘ P)
  assoc {n = n} {k} M N P i l =
    trans (Σ-cong {k} (λ j → Σ-·-distribᵣ (λ r → M i r · N r j) (P j l)))
      (trans (Σ-cong {k} (λ j → Σ-cong {n} (λ r → ·-assoc)))
        (trans (Σ-interchange {k} {n} (λ j r → M i r · (N r j · P j l)))
          (Σ-cong {n} (λ r → sym (Σ-·-distribₗ (M i r) (λ j → N r j · P j l))))))

  cat : Category _ _ _
  cat .Category.obj = ℕ
  cat .Category._⇒_ m n = Matrix n m
  cat .Category._≈_ = _≈ₘ_
  cat .Category.isEquiv = ≈ₘ-isEquiv
  cat .Category.id n = I
  cat .Category._∘_ = _∘_
  cat .Category.∘-cong = ∘-cong
  cat .Category.id-left = id-left
  cat .Category.id-right = id-right
  cat .Category.assoc = assoc

  open import categories using (HasTerminal; IsTerminal)

  terminal : HasTerminal cat
  terminal .HasTerminal.witness = 0
  terminal .HasTerminal.is-terminal .IsTerminal.to-terminal ()
  terminal .HasTerminal.is-terminal .IsTerminal.to-terminal-ext f ()

  import cmon-enriched
  open cmon-enriched using (CMonEnriched; Biproduct)
  open import categories using (HasProducts)
  open import commutative-monoid using (CommutativeMonoid)
  open import Data.Nat using () renaming (_+_ to _+ℕ_)

  _+ₘ_ : ∀ {m n} → Matrix m n → Matrix m n → Matrix m n
  (M +ₘ N) i j = M i j + N i j

  infixl 21 _+ₘ_

  εₘ : ∀ {m n} → Matrix m n
  εₘ _ _ = ε

  comp-bilinear₁ : ∀ {m n k} (M₁ M₂ : Matrix m n) (N : Matrix n k) → (M₁ +ₘ M₂) ∘ N ≈ₘ (M₁ ∘ N) +ₘ (M₂ ∘ N)
  comp-bilinear₁ {n = n} M₁ M₂ N i k =
    trans (Σ-cong {n} (λ j → ·-+-distribᵣ))
          (sym (Σ-+ {n} (λ j → M₁ i j · N j k) (λ j → M₂ i j · N j k)))

  comp-bilinear₂ : ∀ {m n k} (M : Matrix m n) (N₁ N₂ : Matrix n k) → M ∘ (N₁ +ₘ N₂) ≈ₘ (M ∘ N₁) +ₘ (M ∘ N₂)
  comp-bilinear₂ {n = n} M N₁ N₂ i k =
    trans (Σ-cong {n} (λ j → ·-+-distribₗ))
          (sym (Σ-+ {n} (λ j → M i j · N₁ j k) (λ j → M i j · N₂ j k)))

  comp-bilinear-ε₁ : ∀ {m n k} (N : Matrix n k) → εₘ ∘ N ≈ₘ εₘ {m} {k}
  comp-bilinear-ε₁ {n = n} N i k = Σ-ε· {n} _

  comp-bilinear-ε₂ : ∀ {m n k} (M : Matrix m n) → M ∘ εₘ ≈ₘ εₘ {m} {k}
  comp-bilinear-ε₂ {n = n} M i k = ·ε-Σ {n} _

  cmon : CMonEnriched cat
  cmon .CMonEnriched.homCM m n .CommutativeMonoid.ε = εₘ
  cmon .CMonEnriched.homCM m n .CommutativeMonoid._+_ = _+ₘ_
  cmon .CMonEnriched.homCM m n .CommutativeMonoid.+-cong p q i j = +-cong (p i j) (q i j)
  cmon .CMonEnriched.homCM m n .CommutativeMonoid.+-lunit i j = +-lunit
  cmon .CMonEnriched.homCM m n .CommutativeMonoid.+-assoc i j = +-assoc
  cmon .CMonEnriched.homCM m n .CommutativeMonoid.+-comm i j = +-comm
  cmon .CMonEnriched.comp-bilinear₁ = comp-bilinear₁
  cmon .CMonEnriched.comp-bilinear₂ = comp-bilinear₂
  cmon .CMonEnriched.comp-bilinear-ε₁ = comp-bilinear-ε₁
  cmon .CMonEnriched.comp-bilinear-ε₂ = comp-bilinear-ε₂

  p₁ : ∀ {m n} → Matrix m (m +ℕ n)
  p₁ {suc m} zero zero = ι
  p₁ {suc m} zero (suc _) = ε
  p₁ {suc m} (suc i) zero = ε
  p₁ {suc m} (suc i) (suc j) = p₁ {m} i j

  p₂ : ∀ {m n} → Matrix n (m +ℕ n)
  p₂ {zero} i j = e i j
  p₂ {suc m} i zero = ε
  p₂ {suc m} i (suc j) = p₂ {m} i j

  in₁ : ∀ {m n} → Matrix (m +ℕ n) m
  in₁ = p₁ ᵀ

  in₂ : ∀ {m n} → Matrix (m +ℕ n) n
  in₂ = p₂ ᵀ

  id-1 : ∀ m n → p₁ {m} {n} ∘ in₁ {m} {n} ≈ₘ I
  id-1 (suc m) n zero zero = trans (+-cong ·-lunit (Σ-ε· {m +ℕ n} _)) +-runit
  id-1 (suc m) n zero (suc k) = trans (+-cong ε-annihilᵣ (Σ-ε· {m +ℕ n} _)) +-lunit
  id-1 (suc m) n (suc i) zero = trans (+-cong ε-annihilₗ (·ε-Σ {m +ℕ n} _)) +-lunit
  id-1 (suc m) n (suc i) (suc k) = trans ε·+ (id-1 m n i k)

  id-2 : ∀ m n → p₂ {m} {n} ∘ in₂ {m} {n} ≈ₘ I
  id-2 zero n i j = trans (Σ-unit i (λ k → e j k)) (e-sym j i)
  id-2 (suc m) n i j = trans ε·+ (id-2 m n i j)

  zero-1 : ∀ m n → p₁ {m} {n} ∘ in₂ {m} {n} ≈ₘ εₘ
  zero-1 zero n ()
  zero-1 (suc m) n zero j = trans (+-cong ε-annihilᵣ (Σ-ε· {m +ℕ n} _)) +-lunit
  zero-1 (suc m) n (suc i) j = trans ε·+ (zero-1 m n i j)

  zero-2 : ∀ m n → p₂ {m} {n} ∘ in₁ {m} {n} ≈ₘ εₘ
  zero-2 zero n _ ()
  zero-2 (suc m) n i zero = trans (+-cong ε-annihilₗ (·ε-Σ {m +ℕ n} _)) +-lunit
  zero-2 (suc m) n i (suc j) = trans ε·+ (zero-2 m n i j)

  id-+ : ∀ m n → (in₁ {m} {n} ∘ p₁ {m} {n}) +ₘ (in₂ {m} {n} ∘ p₂ {m} {n}) ≈ₘ I {m +ℕ n}
  id-+ zero n i j =
    trans +-lunit (trans (Σ-cong {n} (λ k → ·-cong (e-sym k i) refl)) (Σ-unit i (λ k → e k j)))
  id-+ (suc m) n zero zero =
    trans (+-cong (+-cong ·-lunit (Σ-ε· {m} _)) (Σ-ε· {n} _)) (trans (+-cong +-runit refl) +-runit)
  id-+ (suc m) n zero (suc j) =
    trans (+-cong (+-cong ε-annihilᵣ (Σ-ε· {m} _)) (Σ-ε· {n} _)) (trans (+-cong +-lunit refl) +-lunit)
  id-+ (suc m) n (suc i) zero =
    trans (+-cong (+-cong ε-annihilₗ (·ε-Σ {m} _)) (·ε-Σ {n} _)) (trans (+-cong +-lunit refl) +-lunit)
  id-+ (suc m) n (suc i) (suc j) = trans (+-cong ε·+ refl) (id-+ m n i j)

  biproduct : ∀ m n → Biproduct cmon m n
  biproduct m n .Biproduct.prod = m +ℕ n
  biproduct m n .Biproduct.p₁ = p₁ {m} {n}
  biproduct m n .Biproduct.p₂ = p₂ {m} {n}
  biproduct m n .Biproduct.in₁ = in₁ {m} {n}
  biproduct m n .Biproduct.in₂ = in₂ {m} {n}
  biproduct m n .Biproduct.id-1 = id-1 m n
  biproduct m n .Biproduct.id-2 = id-2 m n
  biproduct m n .Biproduct.zero-1 = zero-1 m n
  biproduct m n .Biproduct.zero-2 = zero-2 m n
  biproduct m n .Biproduct.id-+ = id-+ m n

  _∥_ : ∀ {m n k} → Matrix k m → Matrix k n → Matrix k (m +ℕ n)
  _∥_ {m} {n} f g = Biproduct.copair (biproduct m n) f g

  products : HasProducts cat
  products = cmon-enriched.biproducts→products cmon biproduct

  open HasProducts products using () renaming (pair to ⟨_,_⟩) public

  block : Carrier → Matrix 1 1
  block c _ _ = c

  concat : ∀ {x y} → Vec x → Vec y → Vec (x +ℕ y)
  concat {zero} u v = v
  concat {suc x} u v zero = u zero
  concat {suc x} u v (suc i) = concat {x} (λ j → u (suc j)) v i

  concat-preserves : ∀ {x y p} (_~_ : Carrier → Carrier → Prop p) {u₁ u₂ : Vec x} {v₁ v₂ : Vec y} →
                     (∀ i → u₁ i ~ u₂ i) → (∀ j → v₁ j ~ v₂ j) →
                     ∀ i → concat u₁ v₁ i ~ concat u₂ v₂ i
  concat-preserves {zero} _ _ v-eq i = v-eq i
  concat-preserves {suc x} _ u-eq _ zero = u-eq zero
  concat-preserves {suc x} _~_ u-eq v-eq (suc i) = concat-preserves {x} _~_ (λ j → u-eq (suc j)) v-eq i

  concat-+ : ∀ {x y} (u₁ u₂ : Vec x) (v₁ v₂ : Vec y) i →
             concat (λ k → u₁ k + u₂ k) (λ k → v₁ k + v₂ k) i ≈ (concat u₁ v₁ i + concat u₂ v₂ i)
  concat-+ {zero} u₁ u₂ v₁ v₂ i = refl
  concat-+ {suc x} u₁ u₂ v₁ v₂ zero = refl
  concat-+ {suc x} u₁ u₂ v₁ v₂ (suc i) = concat-+ {x} _ _ _ _ i

  concat-ε : ∀ {x y} i → concat {x} {y} (λ _ → ε) (λ _ → ε) i ≈ ε
  concat-ε {zero} i = refl
  concat-ε {suc x} zero = refl
  concat-ε {suc x} (suc i) = concat-ε {x} i

  split₁ : ∀ {x y} → Vec (x +ℕ y) → Vec x
  split₁ {zero} w ()
  split₁ {suc x} w zero = w zero
  split₁ {suc x} w (suc i) = split₁ {x} (λ j → w (suc j)) i

  split₂ : ∀ {x y} → Vec (x +ℕ y) → Vec y
  split₂ {zero} w = w
  split₂ {suc x} w i = split₂ {x} (λ j → w (suc j)) i

  split₁-concat : ∀ {x y} (u : Vec x) (v : Vec y) i → split₁ {x} {y} (concat u v) i ≈ u i
  split₁-concat {suc x} u v zero = refl
  split₁-concat {suc x} u v (suc i) = split₁-concat {x} (λ j → u (suc j)) v i

  split₂-concat : ∀ {x y} (u : Vec x) (v : Vec y) i → split₂ {x} {y} (concat u v) i ≈ v i
  split₂-concat {zero} u v i = refl
  split₂-concat {suc x} u v i = split₂-concat {x} (λ j → u (suc j)) v i

  concat-split : ∀ {x y} (w : Vec (x +ℕ y)) (i : Fin (x +ℕ y)) → concat (split₁ {x} w) (split₂ {x} w) i ≈ w i
  concat-split {zero} w i = refl
  concat-split {suc x} w zero = refl
  concat-split {suc x} w (suc i) = concat-split {x} (λ j → w (suc j)) i

  Σ-p₁ : ∀ {x y} (w : Vec (x +ℕ y)) (i : Fin x) → Σ {x +ℕ y} (λ j → p₁ {x} {y} i j · w j) ≈ split₁ {x} w i
  Σ-p₁ {suc x} w zero = trans (+-cong ·-lunit (Σ-ε· {x +ℕ _} _)) +-runit
  Σ-p₁ {suc x} w (suc i) = trans ε·+ (Σ-p₁ {x} (λ j → w (suc j)) i)

  Σ-p₂ : ∀ {x y} (w : Vec (x +ℕ y)) (i : Fin y) → Σ {x +ℕ y} (λ j → p₂ {x} {y} i j · w j) ≈ split₂ {x} w i
  Σ-p₂ {zero} w i = Σ-unit i w
  Σ-p₂ {suc x} w i = trans ε·+ (Σ-p₂ {x} (λ j → w (suc j)) i)

  Σ-in₁ : ∀ {x y} (u : Vec x) (i : Fin (x +ℕ y)) →
          Σ {x} (λ j → in₁ {x} {y} i j · u j) ≈ concat {x} {y} u (λ _ → ε) i
  Σ-in₁ {zero} u i = refl
  Σ-in₁ {suc x} u zero = trans (+-cong ·-lunit (Σ-ε· {x} _)) +-runit
  Σ-in₁ {suc x} u (suc i) = trans ε·+ (Σ-in₁ {x} (λ j → u (suc j)) i)

  Σ-in₂ : ∀ {x y} (w : Vec y) (i : Fin (x +ℕ y)) →
          Σ {y} (λ j → in₂ {x} {y} i j · w j) ≈ concat {x} {y} (λ _ → ε) w i
  Σ-in₂ {zero} {y} w i = trans (Σ-cong {y} (λ j → ·-cong (e-sym j i) refl)) (Σ-unit i w)
  Σ-in₂ {suc x} {y} w zero = Σ-ε· {y} _
  Σ-in₂ {suc x} w (suc i) = Σ-in₂ {x} w i

  open Category cat public using (∘-cong₁; ∘-cong₂)
    renaming (≈-refl to ≈ₘ-refl; ≈-sym to ≈ₘ-sym; ≈-trans to ≈ₘ-trans)

  +ₘ-cong : ∀ {m n} {M₁ M₂ N₁ N₂ : Matrix m n} → M₁ ≈ₘ M₂ → N₁ ≈ₘ N₂ → (M₁ +ₘ N₁) ≈ₘ (M₂ +ₘ N₂)
  +ₘ-cong p q i j = +-cong (p i j) (q i j)

  +ₘ-lunit : ∀ {m n} (M : Matrix m n) → (εₘ +ₘ M) ≈ₘ M
  +ₘ-lunit M i j = +-lunit {x = M i j}

  +ₘ-runit : ∀ {m n} (M : Matrix m n) → (M +ₘ εₘ) ≈ₘ M
  +ₘ-runit M i j = trans (+-comm {x = M i j} {y = ε}) (+-lunit {x = M i j})

  +ₘ-comm : ∀ {m n} (M N : Matrix m n) → (M +ₘ N) ≈ₘ (N +ₘ M)
  +ₘ-comm M N i j = +-comm {x = M i j} {y = N i j}

  +ₘ-assoc : ∀ {m n} (M N P : Matrix m n) → ((M +ₘ N) +ₘ P) ≈ₘ (M +ₘ (N +ₘ P))
  +ₘ-assoc M N P i j = +-assoc {x = M i j} {y = N i j} {z = P i j}

  +ₘ-swap-mid : ∀ {m n} (M N P : Matrix m n) → (M +ₘ (N +ₘ P)) ≈ₘ (N +ₘ (M +ₘ P))
  +ₘ-swap-mid M N P =
    ≈ₘ-trans (≈ₘ-sym (+ₘ-assoc M N P))
             (≈ₘ-trans (+ₘ-cong (+ₘ-comm M N) ≈ₘ-refl) (+ₘ-assoc N M P))

  absorb₁ : ∀ {m n k} (M : Matrix m n) (N : Matrix k n) → (M +ₘ (εₘ ∘ N)) ≈ₘ M
  absorb₁ M N = ≈ₘ-trans (+ₘ-cong ≈ₘ-refl (comp-bilinear-ε₁ N)) (+ₘ-runit M)

  absorb₂ : ∀ {m n k} (M : Matrix m n) (N : Matrix m k) → (M +ₘ (N ∘ εₘ)) ≈ₘ M
  absorb₂ M N = ≈ₘ-trans (+ₘ-cong ≈ₘ-refl (comp-bilinear-ε₂ N)) (+ₘ-runit M)

  ∘-pair : ∀ {m n k l} (A : Matrix l (m +ℕ n)) (X : Matrix m k) (Y : Matrix n k) →
           (A ∘ ⟨ X , Y ⟩) ≈ₘ (((A ∘ in₁) ∘ X) +ₘ ((A ∘ in₂) ∘ Y))
  ∘-pair A X Y =
    ≈ₘ-trans (comp-bilinear₂ A (in₁ ∘ X) (in₂ ∘ Y)) (+ₘ-cong (≈ₘ-sym (assoc A in₁ X)) (≈ₘ-sym (assoc A in₂ Y)))

  ∥-pair : ∀ {m n k l} (F : Matrix l m) (G : Matrix l n) (X : Matrix m k) (Y : Matrix n k) →
           ((F ∥ G) ∘ ⟨ X , Y ⟩) ≈ₘ ((F ∘ X) +ₘ (G ∘ Y))
  ∥-pair {m} {n} F G X Y =
    ≈ₘ-trans (∘-pair (F ∥ G) X Y)
             (+ₘ-cong (∘-cong₁ (Biproduct.copair-in₁ (biproduct m n) F G))
                      (∘-cong₁ (Biproduct.copair-in₂ (biproduct m n) F G)))
