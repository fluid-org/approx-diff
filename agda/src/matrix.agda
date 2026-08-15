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

  -- Vectors S^n.
  Vec : ℕ → Set o
  Vec n = Fin n → Carrier

  -- Standard basis vector: ι at position i, ε elsewhere.
  e : ∀ {n} → Fin n → Vec n
  e zero zero = ι
  e zero (suc _) = ε
  e (suc i) zero = ε
  e (suc i) (suc j) = e i j

  -- Finite sum: Σᵢ f(i), using addition of S.
  Σ : ∀ {n} → (Fin n → Carrier) → Carrier
  Σ {zero} _ = ε
  Σ {suc n} f = f zero + Σ {n} (λ i → f (suc i))

  -- Dot product (sum of multiplications).
  infixl 21 _⋅_
  _⋅_ : ∀ {n} → Vec n → Vec n → Carrier
  _⋅_ {n} u v = Σ {n} λ i → u i · v i

  Matrix : ℕ → ℕ → Set o
  Matrix m n = Fin m → Fin n → Carrier

  -- Identity matrix (Kronecker delta).
  I : ∀ {n} → Matrix n n
  I = e

  -- Matrix composition: (M ∘ N)ᵢₖ = Σⱼ Mᵢⱼ · Nⱼₖ.
  _∘_ : ∀ {m n k} → Matrix m n → Matrix n k → Matrix m k
  (M ∘ N) i k = Σ (λ j → M i j · N j k)

  infixl 21 _∘_

  _ᵀ : ∀ {m n} → Matrix m n → Matrix n m
  (M ᵀ) i j = M j i

  -- Pointwise equality of matrices.
  _≈ₘ_ : ∀ {m n} → Matrix m n → Matrix m n → Prop ℓ
  M ≈ₘ N = ∀ i j → M i j ≈ N i j

  open import Level using (Level; _⊔_)
  open import prop using (tt)
  open import prop-setoid using (IsEquivalence)
  open import categories using (Category)

  -- Any reflexive relation preserved by + is preserved by Σ.
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

  -- Kronecker delta is symmetric.
  e-sym : ∀ {n} (i j : Fin n) → e i j ≈ e j i
  e-sym zero zero = refl
  e-sym zero (suc _) = refl
  e-sym (suc _) zero = refl
  e-sym (suc i) (suc j) = e-sym i j

  -- Σ of zeros is zero.
  Σ-ε : ∀ {n} → Σ {n} (λ _ → ε) ≈ ε
  Σ-ε {zero} = refl
  Σ-ε {suc n} = trans +-lunit (Σ-ε {n})

  -- Picking out the i-th element: Σⱼ e(i,j) · f(j) ≈ f(i).
  Σ-unit : ∀ {n} (i : Fin n) (f : Fin n → Carrier) → Σ {n} (λ j → e i j · f j) ≈ f i
  Σ-unit {suc n} zero f =
    trans (+-cong ·-lunit (trans (Σ-cong {n} (λ j → ε-annihilₗ)) (Σ-ε {n})))
          (trans +-comm +-lunit)
  Σ-unit {suc n} (suc i) f =
    trans (+-cong ε-annihilₗ refl)
          (trans +-lunit (Σ-unit i (λ j → f (suc j))))

  -- Distributing · over Σ on the right: (Σⱼ fⱼ) · x ≈ Σⱼ (fⱼ · x).
  Σ-·-distribᵣ : ∀ {n} (f : Fin n → Carrier) (x : Carrier) → Σ {n} f · x ≈ Σ {n} (λ j → f j · x)
  Σ-·-distribᵣ {zero} f x = ε-annihilₗ
  Σ-·-distribᵣ {suc n} f x =
    trans ·-+-distribᵣ (+-cong refl (Σ-·-distribᵣ {n} (λ j → f (suc j)) x))

  -- Distributing · over Σ on the left: x · (Σⱼ fⱼ) ≈ Σⱼ (x · fⱼ).
  Σ-·-distribₗ : ∀ {n} (x : Carrier) (f : Fin n → Carrier) → x · Σ {n} f ≈ Σ {n} (λ j → x · f j)
  Σ-·-distribₗ {n} x f =
    trans ·-comm (trans (Σ-·-distribᵣ f x) (Σ-cong {n} (λ j → ·-comm)))

  -- Σ distributes over +: Σ g + Σ h ≈ Σ (λ j → g j + h j).
  Σ-+ : ∀ {n} (g h : Fin n → Carrier) → Σ {n} g + Σ {n} h ≈ Σ {n} (λ j → g j + h j)
  Σ-+ {zero} g h = +-lunit
  Σ-+ {suc n} g h =
    trans +-interchange (+-cong refl (Σ-+ {n} (λ j → g (suc j)) (λ j → h (suc j))))

  -- Swapping two finite sums.
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

  open import cmon-enriched using (CMonEnriched; Biproduct)
  open import commutative-monoid using (CommutativeMonoid)
  open import Data.Nat using () renaming (_+_ to _+ℕ_)

  -- Pointwise addition of matrices.
  _+ₘ_ : ∀ {m n} → Matrix m n → Matrix m n → Matrix m n
  (M +ₘ N) i j = M i j + N i j

  infixl 21 _+ₘ_

  -- Zero matrix.
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
  comp-bilinear-ε₁ {n = n} N i k =
    trans (Σ-cong {n} (λ j → ε-annihilₗ)) (Σ-ε {n})

  comp-bilinear-ε₂ : ∀ {m n k} (M : Matrix m n) → M ∘ εₘ ≈ₘ εₘ {m} {k}
  comp-bilinear-ε₂ {n = n} M i k =
    trans (Σ-cong {n} (λ j → ε-annihilᵣ)) (Σ-ε {n})


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

  -- Biproducts.
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

  private
    Σ-ε· : ∀ {n} (f : Fin n → Carrier) → Σ {n} (λ j → ε · f j) ≈ ε
    Σ-ε· {n} f = trans (Σ-cong {n} (λ j → ε-annihilₗ)) (Σ-ε {n})

    ·ε-Σ : ∀ {n} (f : Fin n → Carrier) → Σ {n} (λ j → f j · ε) ≈ ε
    ·ε-Σ {n} f = trans (Σ-cong {n} (λ j → ε-annihilᵣ)) (Σ-ε {n})

  id-1 : ∀ m n → p₁ {m} {n} ∘ in₁ {m} {n} ≈ₘ I
  id-1 (suc m) n zero zero = trans (+-cong ·-lunit (Σ-ε· {m +ℕ n} _)) (trans +-comm +-lunit)
  id-1 (suc m) n zero (suc k) = trans (+-cong ε-annihilᵣ (Σ-ε· {m +ℕ n} _)) +-lunit
  id-1 (suc m) n (suc i) zero = trans (+-cong ε-annihilₗ (·ε-Σ {m +ℕ n} _)) +-lunit
  id-1 (suc m) n (suc i) (suc k) = trans (+-cong ε-annihilₗ refl) (trans +-lunit (id-1 m n i k))

  id-2 : ∀ m n → p₂ {m} {n} ∘ in₂ {m} {n} ≈ₘ I
  id-2 zero n i j = trans (Σ-unit i (λ k → e j k)) (e-sym j i)
  id-2 (suc m) n i j = trans (+-cong ε-annihilₗ refl) (trans +-lunit (id-2 m n i j))

  zero-1 : ∀ m n → p₁ {m} {n} ∘ in₂ {m} {n} ≈ₘ εₘ
  zero-1 zero n ()
  zero-1 (suc m) n zero j = trans (+-cong ε-annihilᵣ (Σ-ε· {m +ℕ n} _)) +-lunit
  zero-1 (suc m) n (suc i) j = trans (+-cong ε-annihilₗ refl) (trans +-lunit (zero-1 m n i j))

  zero-2 : ∀ m n → p₂ {m} {n} ∘ in₁ {m} {n} ≈ₘ εₘ
  zero-2 zero n _ ()
  zero-2 (suc m) n i zero = trans (+-cong ε-annihilₗ (·ε-Σ {m +ℕ n} _)) +-lunit
  zero-2 (suc m) n i (suc j) = trans (+-cong ε-annihilₗ refl) (trans +-lunit (zero-2 m n i j))

  id-+ : ∀ m n → (in₁ {m} {n} ∘ p₁ {m} {n}) +ₘ (in₂ {m} {n} ∘ p₂ {m} {n}) ≈ₘ I {m +ℕ n}
  id-+ zero n i j =
    trans +-lunit (trans (Σ-cong {n} (λ k → ·-cong (e-sym k i) refl)) (Σ-unit i (λ k → e k j)))
  id-+ (suc m) n zero zero =
    trans (+-cong (+-cong ·-lunit (Σ-ε· {m} _)) (Σ-ε· {n} _))
          (trans (+-cong (trans +-comm +-lunit) refl) (trans +-comm +-lunit))
  id-+ (suc m) n zero (suc j) =
    trans (+-cong (+-cong ε-annihilᵣ (Σ-ε· {m} _)) (Σ-ε· {n} _)) (trans (+-cong +-lunit refl) +-lunit)
  id-+ (suc m) n (suc i) zero =
    trans (+-cong (+-cong ε-annihilₗ (·ε-Σ {m} _)) (·ε-Σ {n} _)) (trans (+-cong +-lunit refl) +-lunit)
  id-+ (suc m) n (suc i) (suc j) =
    trans (+-cong (+-cong ε-annihilₗ refl) refl) (trans (+-cong +-lunit refl) (id-+ m n i j))

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

  -- Copairing of blocks: [ f , g ] as a matrix into the summed domain.
  _∥_ : ∀ {m n k} → Matrix k m → Matrix k n → Matrix k (m +ℕ n)
  _∥_ {m} {n} f g = Biproduct.copair (biproduct m n) f g

  -- A scalar as a 1-by-1 block.
  block : Carrier → Matrix 1 1
  block c _ _ = c

  -- Vector concatenation, a monoid homomorphism preserving pointwise additive structure.
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

  -- Matrix multiplication by p₁/p₂ computes split₁/split₂.
  Σ-p₁ : ∀ {x y} (w : Vec (x +ℕ y)) (i : Fin x) → Σ {x +ℕ y} (λ j → p₁ {x} {y} i j · w j) ≈ split₁ {x} w i
  Σ-p₁ {suc x} w zero =
    trans (+-cong ·-lunit (trans (Σ-cong {x +ℕ _} (λ j → ε-annihilₗ)) (Σ-ε {x +ℕ _})))
          (trans +-comm +-lunit)
  Σ-p₁ {suc x} w (suc i) =
    trans (+-cong ε-annihilₗ refl) (trans +-lunit (Σ-p₁ {x} (λ j → w (suc j)) i))

  Σ-p₂ : ∀ {x y} (w : Vec (x +ℕ y)) (i : Fin y) → Σ {x +ℕ y} (λ j → p₂ {x} {y} i j · w j) ≈ split₂ {x} w i
  Σ-p₂ {zero} w i = Σ-unit i w
  Σ-p₂ {suc x} w i =
    trans (+-cong ε-annihilₗ refl) (trans +-lunit (Σ-p₂ {x} (λ j → w (suc j)) i))

  Σ-in₁ : ∀ {x y} (u : Vec x) (i : Fin (x +ℕ y)) →
          Σ {x} (λ j → in₁ {x} {y} i j · u j) ≈ concat {x} {y} u (λ _ → ε) i
  Σ-in₁ {zero} u i = refl
  Σ-in₁ {suc x} u zero =
    trans (+-cong ·-lunit (trans (Σ-cong {x} (λ j → ε-annihilₗ)) (Σ-ε {x})))
          (trans +-comm +-lunit)
  Σ-in₁ {suc x} u (suc i) =
    trans (+-cong ε-annihilₗ refl) (trans +-lunit (Σ-in₁ {x} (λ j → u (suc j)) i))

  Σ-in₂ : ∀ {x y} (w : Vec y) (i : Fin (x +ℕ y)) →
          Σ {y} (λ j → in₂ {x} {y} i j · w j) ≈ concat {x} {y} (λ _ → ε) w i
  Σ-in₂ {zero} {y} w i = trans (Σ-cong {y} (λ j → ·-cong (e-sym j i) refl)) (Σ-unit i w)
  Σ-in₂ {suc x} {y} w zero = trans (Σ-cong {y} (λ j → ε-annihilₗ)) (Σ-ε {y})
  Σ-in₂ {suc x} w (suc i) = Σ-in₂ {x} w i


  ≈ₘ-refl : ∀ {m n} {M : Matrix m n} → M ≈ₘ M
  ≈ₘ-refl = ≈ₘ-isEquiv .IsEquivalence.refl

  ≈ₘ-trans : ∀ {m n} {M N P : Matrix m n} → M ≈ₘ N → N ≈ₘ P → M ≈ₘ P
  ≈ₘ-trans = ≈ₘ-isEquiv .IsEquivalence.trans

  ≈ₘ-sym : ∀ {m n} {M N : Matrix m n} → M ≈ₘ N → N ≈ₘ M
  ≈ₘ-sym = ≈ₘ-isEquiv .IsEquivalence.sym

  ∘-cong₁ : ∀ {m n k} {M₁ M₂ : Matrix m n} {N : Matrix n k} → M₁ ≈ₘ M₂ → M₁ ∘ N ≈ₘ M₂ ∘ N
  ∘-cong₁ p = ∘-cong p ≈ₘ-refl

  ∘-cong₂ : ∀ {m n k} {M : Matrix m n} {N₁ N₂ : Matrix n k} → N₁ ≈ₘ N₂ → M ∘ N₁ ≈ₘ M ∘ N₂
  ∘-cong₂ = ∘-cong ≈ₘ-refl

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

  +ₘ-interchange : ∀ {m n} (M N P Q : Matrix m n) →
                   ((M +ₘ N) +ₘ (P +ₘ Q)) ≈ₘ ((M +ₘ P) +ₘ (N +ₘ Q))
  +ₘ-interchange M N P Q i j = +-interchange {w = M i j} {x = N i j} {y = P i j} {z = Q i j}

  +ₘ-swap-mid : ∀ {m n} (M N P : Matrix m n) → (M +ₘ (N +ₘ P)) ≈ₘ (N +ₘ (M +ₘ P))
  +ₘ-swap-mid M N P =
    ≈ₘ-trans (≈ₘ-sym (+ₘ-assoc M N P))
             (≈ₘ-trans (+ₘ-cong (+ₘ-comm M N) ≈ₘ-refl) (+ₘ-assoc N M P))

  -- A composite with a zero factor drops out of a sum.
  absorb₁ : ∀ {m n k} (M : Matrix m n) (N : Matrix k n) → (M +ₘ (εₘ ∘ N)) ≈ₘ M
  absorb₁ M N = ≈ₘ-trans (+ₘ-cong ≈ₘ-refl (comp-bilinear-ε₁ N)) (+ₘ-runit M)

  absorb₂ : ∀ {m n k} (M : Matrix m n) (N : Matrix m k) → (M +ₘ (N ∘ εₘ)) ≈ₘ M
  absorb₂ M N = ≈ₘ-trans (+ₘ-cong ≈ₘ-refl (comp-bilinear-ε₂ N)) (+ₘ-runit M)

  distrib-root : ∀ {m n k l} (P : Matrix m n) (X : Matrix n k) (Y : Matrix n l) (Z : Matrix l k) →
                 ((P ∘ X) +ₘ ((P ∘ Y) ∘ Z)) ≈ₘ (P ∘ (X +ₘ (Y ∘ Z)))
  distrib-root P X Y Z =
    ≈ₘ-trans (+ₘ-cong ≈ₘ-refl (assoc P Y Z)) (≈ₘ-sym (comp-bilinear₂ P X (Y ∘ Z)))

  offset-distrib : ∀ {m n l k} (K : Matrix m k) (P : Matrix m n) (X : Matrix n k)
                   (Y : Matrix n l) (Z : Matrix l k) →
                   ((K +ₘ (P ∘ X)) +ₘ ((P ∘ Y) ∘ Z)) ≈ₘ (K +ₘ (P ∘ (X +ₘ (Y ∘ Z))))
  offset-distrib K P X Y Z =
    ≈ₘ-trans (+ₘ-assoc K (P ∘ X) ((P ∘ Y) ∘ Z)) (+ₘ-cong ≈ₘ-refl (distrib-root P X Y Z))

  -- One step of hiding a vertex, on entries whose columns factor through P.
  root-step : ∀ {m n l k} {P : Matrix m n} {G₁ : Matrix m k} {X : Matrix n k}
              {G₂ : Matrix m l} {Y : Matrix n l} {G₃ Z : Matrix l k} →
              G₁ ≈ₘ (P ∘ X) → G₂ ≈ₘ (P ∘ Y) → G₃ ≈ₘ Z →
              (G₁ +ₘ (G₂ ∘ G₃)) ≈ₘ (P ∘ (X +ₘ (Y ∘ Z)))
  root-step {P = P} {X = X} {Y = Y} {Z = Z} a b c =
    ≈ₘ-trans (+ₘ-cong a (∘-cong b c)) (distrib-root P X Y Z)

  offset-step : ∀ {m n l k} {K : Matrix m k} {P : Matrix m n} {G₁ : Matrix m k}
                {X : Matrix n k} {G₂ : Matrix m l} {Y : Matrix n l} {G₃ Z : Matrix l k} →
                G₁ ≈ₘ (K +ₘ (P ∘ X)) → G₂ ≈ₘ (P ∘ Y) → G₃ ≈ₘ Z →
                (G₁ +ₘ (G₂ ∘ G₃)) ≈ₘ (K +ₘ (P ∘ (X +ₘ (Y ∘ Z))))
  offset-step {K = K} {P} {X = X} {Y = Y} {Z = Z} a b c =
    ≈ₘ-trans (+ₘ-cong a (∘-cong b c)) (offset-distrib K P X Y Z)

  -- Linear maps on families of columns indexed by a set of input positions: the routing by which a
  -- premise's inputs are reached from the conclusion's.
  record Linear {ℓ'} {Inp' : Set ℓ'} (iw' : Inp' → ℕ) {Inp : Set ℓ'} (iw : Inp → ℕ) :
                Set (o ⊔ ℓ ⊔ ℓ') where
    field
      ap      : ∀ {m} → ((i' : Inp') → Matrix m (iw' i')) → (i : Inp) → Matrix m (iw i)
      ap-+    : ∀ {m} (f g : (i' : Inp') → Matrix m (iw' i')) (i : Inp) →
                ap (λ i' → f i' +ₘ g i') i ≈ₘ (ap f i +ₘ ap g i)
      ap-∘    : ∀ {m k} (X : Matrix k m) (f : (i' : Inp') → Matrix m (iw' i')) (i : Inp) →
                ap (λ i' → X ∘ f i') i ≈ₘ (X ∘ ap f i)
      ap-cong : ∀ {m} {f g : (i' : Inp') → Matrix m (iw' i')} → (∀ i' → f i' ≈ₘ g i') →
                ∀ i → ap f i ≈ₘ ap g i

  open Linear public

  -- The same into a single column: how a premise's inputs are reached from an earlier root.
  record Link {ℓ'} {Inp' : Set ℓ'} (iw' : Inp' → ℕ) (n : ℕ) : Set (o ⊔ ℓ ⊔ ℓ') where
    field
      at      : ∀ {m} → ((i' : Inp') → Matrix m (iw' i')) → Matrix m n
      at-+    : ∀ {m} (f g : (i' : Inp') → Matrix m (iw' i')) →
                at (λ i' → f i' +ₘ g i') ≈ₘ (at f +ₘ at g)
      at-∘    : ∀ {m k} (X : Matrix k m) (f : (i' : Inp') → Matrix m (iw' i')) →
                at (λ i' → X ∘ f i') ≈ₘ (X ∘ at f)
      at-cong : ∀ {m} {f g : (i' : Inp') → Matrix m (iw' i')} → (∀ i' → f i' ≈ₘ g i') →
                at f ≈ₘ at g

  open Link public

  id-linear : ∀ {ℓ'} {Inp : Set ℓ'} (iw : Inp → ℕ) → Linear iw iw
  id-linear iw .ap f i = f i
  id-linear iw .ap-+ f g i = ≈ₘ-refl
  id-linear iw .ap-∘ X f i = ≈ₘ-refl
  id-linear iw .ap-cong e i = e i

  no-link : ∀ {ℓ'} {Inp' : Set ℓ'} (iw' : Inp' → ℕ) (n : ℕ) → Link iw' n
  no-link iw' n .at {m} _ = εₘ {m} {n}
  no-link iw' n .at-+ {m} f g = ≈ₘ-sym (+ₘ-lunit (εₘ {m} {n}))
  no-link iw' n .at-∘ {m} {k} X f = ≈ₘ-sym (comp-bilinear-ε₂ X)
  no-link iw' n .at-cong {m} e = ≈ₘ-refl {M = εₘ {m} {n}}

  -- A routing with a further contribution reaching the premise through the column c, as when an
  -- earlier premise has collapsed onto its root.
  extend : ∀ {ℓ'} {Inp' : Set ℓ'} {iw' : Inp' → ℕ} {Inp : Set ℓ'} {iw : Inp → ℕ} {n₀ : ℕ} →
           Linear iw' iw → Link iw' n₀ → ((i : Inp) → Matrix n₀ (iw i)) → Linear iw' iw
  extend R L c .ap f i = R .ap f i +ₘ (L .at f ∘ c i)
  extend R L c .ap-+ f g i =
    ≈ₘ-trans (+ₘ-cong (R .ap-+ f g i)
                      (≈ₘ-trans (∘-cong₁ (L .at-+ f g))
                                (comp-bilinear₁ (L .at f) (L .at g) (c i))))
             (+ₘ-interchange (R .ap f i) (R .ap g i) (L .at f ∘ c i) (L .at g ∘ c i))
  extend R L c .ap-∘ X f i =
    ≈ₘ-trans (+ₘ-cong (R .ap-∘ X f i)
                      (≈ₘ-trans (∘-cong₁ (L .at-∘ X f)) (assoc X (L .at f) (c i))))
             (≈ₘ-sym (comp-bilinear₂ X (R .ap f i) (L .at f ∘ c i)))
  extend R L c .ap-cong e i = +ₘ-cong (R .ap-cong e i) (∘-cong₁ (L .at-cong e))

  -- The column a rule contributes at each input position, as a function of its premises' columns.
  -- Used both to state a rule's relation and to state what its block collapses to.
  one-result : ∀ {ℓ'} {Inp' : Set ℓ'} {iw' : Inp' → ℕ} {Inp : Set ℓ'} {iw : Inp → ℕ} {n n₀} →
               Linear iw' iw → ((i : Inp) → Matrix n (iw i)) → Matrix n n₀ →
               ((i' : Inp') → Matrix n₀ (iw' i')) → (i : Inp) → Matrix n (iw i)
  one-result route out up c i = out i +ₘ (up ∘ route .ap c i)

  seq-result : ∀ {ℓ'} {Inp₁ : Set ℓ'} {iw₁ : Inp₁ → ℕ} {Inp₂ : Set ℓ'} {iw₂ : Inp₂ → ℕ}
               {Inp : Set ℓ'} {iw : Inp → ℕ} {n n₁ n₂} →
               Linear iw₁ iw → Linear iw₂ iw → Link iw₂ n₁ →
               ((i : Inp) → Matrix n (iw i)) → Matrix n n₁ → Matrix n n₂ →
               ((i' : Inp₁) → Matrix n₁ (iw₁ i')) → ((i' : Inp₂) → Matrix n₂ (iw₂ i')) →
               (i : Inp) → Matrix n (iw i)
  seq-result r₁ r₂ l out u₁ u₂ c₁ c₂ i =
    one-result r₁ out u₁ c₁ i +ₘ (u₂ ∘ extend r₂ l (λ j → r₁ .ap c₁ j) .ap c₂ i)

  seq3-result : ∀ {ℓ'} {Inp₁ : Set ℓ'} {iw₁ : Inp₁ → ℕ} {Inp₂ : Set ℓ'} {iw₂ : Inp₂ → ℕ}
                {Inp₃ : Set ℓ'} {iw₃ : Inp₃ → ℕ} {Inp : Set ℓ'} {iw : Inp → ℕ} {n n₁ n₂ n₃} →
                Linear iw₁ iw → Linear iw₂ iw → Linear iw₃ iw → Link iw₃ n₁ → Link iw₃ n₂ →
                ((i : Inp) → Matrix n (iw i)) → Matrix n n₁ → Matrix n n₂ → Matrix n n₃ →
                ((i' : Inp₁) → Matrix n₁ (iw₁ i')) → ((i' : Inp₂) → Matrix n₂ (iw₂ i')) →
                ((i' : Inp₃) → Matrix n₃ (iw₃ i')) → (i : Inp) → Matrix n (iw i)
  seq3-result r₁ r₂ r₃ l₁ l₂ out u₁ u₂ u₃ c₁ c₂ c₃ i =
    (one-result r₁ out u₁ c₁ i +ₘ (u₂ ∘ r₂ .ap c₂ i))
    +ₘ (u₃ ∘ extend (extend r₃ l₁ (λ j → r₁ .ap c₁ j)) l₂ (λ j → r₂ .ap c₂ j) .ap c₃ i)

  one-result-cong : ∀ {ℓ'} {Inp' : Set ℓ'} {iw' : Inp' → ℕ} {Inp : Set ℓ'} {iw : Inp → ℕ} {n n₀}
                    (route : Linear iw' iw) {out : (i : Inp) → Matrix n (iw i)} {up : Matrix n n₀}
                    {c c' : (i' : Inp') → Matrix n₀ (iw' i')} → (∀ i' → c i' ≈ₘ c' i') →
                    ∀ i → one-result route out up c i ≈ₘ one-result route out up c' i
  one-result-cong route e i = +ₘ-cong ≈ₘ-refl (∘-cong₂ (route .ap-cong e i))

  seq-result-cong : ∀ {ℓ'} {Inp₁ : Set ℓ'} {iw₁ : Inp₁ → ℕ} {Inp₂ : Set ℓ'} {iw₂ : Inp₂ → ℕ}
                    {Inp : Set ℓ'} {iw : Inp → ℕ} {n n₁ n₂}
                    (r₁ : Linear iw₁ iw) (r₂ : Linear iw₂ iw) (l : Link iw₂ n₁)
                    {out : (i : Inp) → Matrix n (iw i)} {u₁ : Matrix n n₁} {u₂ : Matrix n n₂}
                    {c₁ c₁' : (i' : Inp₁) → Matrix n₁ (iw₁ i')}
                    {c₂ c₂' : (i' : Inp₂) → Matrix n₂ (iw₂ i')} →
                    (∀ i' → c₁ i' ≈ₘ c₁' i') → (∀ i' → c₂ i' ≈ₘ c₂' i') →
                    ∀ i → seq-result r₁ r₂ l out u₁ u₂ c₁ c₂ i
                          ≈ₘ seq-result r₁ r₂ l out u₁ u₂ c₁' c₂' i
  seq-result-cong r₁ r₂ l {out = out} {u₁ = u₁} e₁ e₂ i =
    +ₘ-cong (one-result-cong r₁ {out = out} {up = u₁} e₁ i)
            (∘-cong₂ (+ₘ-cong (r₂ .ap-cong e₂ i)
                              (∘-cong (l .at-cong e₂) (r₁ .ap-cong e₁ i))))

  seq3-result-cong : ∀ {ℓ'} {Inp₁ : Set ℓ'} {iw₁ : Inp₁ → ℕ} {Inp₂ : Set ℓ'} {iw₂ : Inp₂ → ℕ}
                     {Inp₃ : Set ℓ'} {iw₃ : Inp₃ → ℕ} {Inp : Set ℓ'} {iw : Inp → ℕ} {n n₁ n₂ n₃}
                     (r₁ : Linear iw₁ iw) (r₂ : Linear iw₂ iw) (r₃ : Linear iw₃ iw)
                     (l₁ : Link iw₃ n₁) (l₂ : Link iw₃ n₂)
                     {out : (i : Inp) → Matrix n (iw i)}
                     {u₁ : Matrix n n₁} {u₂ : Matrix n n₂} {u₃ : Matrix n n₃}
                     {c₁ c₁' : (i' : Inp₁) → Matrix n₁ (iw₁ i')}
                     {c₂ c₂' : (i' : Inp₂) → Matrix n₂ (iw₂ i')}
                     {c₃ c₃' : (i' : Inp₃) → Matrix n₃ (iw₃ i')} →
                     (∀ i' → c₁ i' ≈ₘ c₁' i') → (∀ i' → c₂ i' ≈ₘ c₂' i') →
                     (∀ i' → c₃ i' ≈ₘ c₃' i') →
                     ∀ i → seq3-result r₁ r₂ r₃ l₁ l₂ out u₁ u₂ u₃ c₁ c₂ c₃ i
                           ≈ₘ seq3-result r₁ r₂ r₃ l₁ l₂ out u₁ u₂ u₃ c₁' c₂' c₃' i
  seq3-result-cong r₁ r₂ r₃ l₁ l₂ {out = out} {u₁ = u₁} e₁ e₂ e₃ i =
    +ₘ-cong (+ₘ-cong (one-result-cong r₁ {out = out} {up = u₁} e₁ i) (∘-cong₂ (r₂ .ap-cong e₂ i)))
            (∘-cong₂ (+ₘ-cong (+ₘ-cong (r₃ .ap-cong e₃ i)
                                       (∘-cong (l₁ .at-cong e₃) (r₁ .ap-cong e₁ i)))
                              (∘-cong (l₂ .at-cong e₃) (r₂ .ap-cong e₂ i))))
