{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (0ℓ)
open import Data.Nat using (ℕ; suc) renaming (_+_ to _+ℕ_)
open import Data.Fin using (Fin; zero; suc)
open import prop-setoid using (Setoid; IsEquivalence)
open import commutative-semiring using (CommutativeSemiring)
open import basics using (IsPreorder; IsJoin; IsBottom; IsTop)
open import categories using (Category; HasTerminal; IsTerminal)
open import commutative-monoid using (CommutativeMonoid)
open import cmon-enriched using (CMonEnriched; Biproduct)
import matrix

-- Position orders as matrices. Over a commutative semiring whose addition is idempotent, the matrix of
-- a preorder on positions (entry (q, p) is ⊤ when q ≤ p) is idempotent under composition, and the
-- vectors it fixes are the down-closed selections of positions. Objects pair a dimension with such a
-- matrix, morphisms are the matrices absorbed by the order matrices at either end, and the order matrix
-- is the identity: the Karoubi envelope of Mat(S) at the order idempotents. Transposition sends an
-- order to its opposite, so conjugation pairs each object with its opposite order.
module order-idempotent
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (let open CommutativeSemiring S hiding (_≈_; trans; sym; refl); open Setoid A)
  (∨-idem    : ∀ {x} → x + x ≈ x)
  (∧-idem    : ∀ {x} → x · x ≈ x)
  (⊤-add-top : ∀ {x} → ι + x ≈ ι)
  where

open matrix.Mat S
  using (Matrix; I; _ᵀ; _≈ₘ_; ∘-cong; assoc; id-left; id-right; Σ-cong; _+ₘ_; εₘ;
         comp-bilinear₁; comp-bilinear₂; comp-bilinear-ε₁; comp-bilinear-ε₂;
         p₁; p₂; in₁; in₂; id-1; id-2; zero-1; zero-2; id-+)
  renaming (_∘_ to _∘ₘ_)
module L = matrix.DistributiveLattice S ∨-idem ∧-idem ⊤-add-top
open IsPreorder L.≤-isPreorder using () renaming (refl to ≤-refl; trans to ≤-trans)

≈ₘ-refl : ∀ {m n} {M : Matrix m n} → M ≈ₘ M
≈ₘ-refl i j = refl

≈ₘ-sym : ∀ {m n} {M N : Matrix m n} → M ≈ₘ N → N ≈ₘ M
≈ₘ-sym p i j = sym (p i j)

≈ₘ-trans : ∀ {m n} {M N O : Matrix m n} → M ≈ₘ N → N ≈ₘ O → M ≈ₘ O
≈ₘ-trans p q i j = trans (p i j) (q i j)

-- The induced order is antisymmetric, since x ∨ y computes both bounds.
≤-antisym : ∀ {x y} → x L.≤ y → y L.≤ x → x ≈ y
≤-antisym x≤y y≤x = trans (sym y≤x) (trans +-comm x≤y)

-- A position order: a dimension together with a reflexive, transitive matrix over it.
record Pos : Set where
  field
    dim : ℕ
    ord : Matrix dim dim
    ord-refl  : ∀ i → ι L.≤ ord i i
    ord-trans : ∀ i j k → (ord i j · ord j k) L.≤ ord i k

  -- The order matrix is idempotent: transitivity bounds each composite term, and reflexivity
  -- recovers each entry through the diagonal.
  ord-idem : (ord ∘ₘ ord) ≈ₘ ord
  ord-idem i k =
    ≤-antisym
      (L.Σ-lub _ (λ j → ord-trans i j k))
      (≤-trans (L.≈→≤ (sym ·-lunit))
      (≤-trans (L.∧-monoˡ (ord-refl i))
               (L.Σ-ub (λ j → ord i j · ord j k) i)))

open Pos public

-- A matrix absorbed by the order matrices at either end. Columns are indexed by the source, as in
-- Mat.cat.
record _⇒_ (P Q : Pos) : Set where
  field
    mat : Matrix (Q .dim) (P .dim)
    absorbed : (Q .ord ∘ₘ mat ∘ₘ P .ord) ≈ₘ mat

open _⇒_ public

infix 4 _≈p_

_≈p_ : ∀ {P Q} → P ⇒ Q → P ⇒ Q → Prop 0ℓ
f ≈p g = f .mat ≈ₘ g .mat

-- Either order matrix alone already absorbs.
absorb-left : ∀ {P Q} (f : P ⇒ Q) → (Q .ord ∘ₘ f .mat) ≈ₘ f .mat
absorb-left {P} {Q} f =
  ≈ₘ-trans (∘-cong (≈ₘ-refl {M = Q .ord}) (≈ₘ-sym (f .absorbed)))
  (≈ₘ-trans (≈ₘ-sym (assoc (Q .ord) (Q .ord ∘ₘ f .mat) (P .ord)))
  (≈ₘ-trans (∘-cong (≈ₘ-sym (assoc (Q .ord) (Q .ord) (f .mat))) (≈ₘ-refl {M = P .ord}))
  (≈ₘ-trans (∘-cong (∘-cong (ord-idem Q) (≈ₘ-refl {M = f .mat})) (≈ₘ-refl {M = P .ord}))
            (f .absorbed))))

absorb-right : ∀ {P Q} (f : P ⇒ Q) → (f .mat ∘ₘ P .ord) ≈ₘ f .mat
absorb-right {P} {Q} f =
  ≈ₘ-trans (∘-cong (≈ₘ-sym (f .absorbed)) (≈ₘ-refl {M = P .ord}))
  (≈ₘ-trans (assoc (Q .ord ∘ₘ f .mat) (P .ord) (P .ord))
  (≈ₘ-trans (∘-cong (≈ₘ-refl {M = Q .ord ∘ₘ f .mat}) (ord-idem P))
            (f .absorbed)))

-- Every matrix induces a morphism by closing under the orders at either end; the result is
-- absorbed because the orders are idempotent.
close : ∀ {P Q} → Matrix (Q .dim) (P .dim) → P ⇒ Q
close {P} {Q} X .mat = (Q .ord ∘ₘ X) ∘ₘ P .ord
close {P} {Q} X .absorbed = ≈ₘ-trans (∘-cong left (≈ₘ-refl {M = P .ord})) right
  where
  left : (Q .ord ∘ₘ ((Q .ord ∘ₘ X) ∘ₘ P .ord)) ≈ₘ ((Q .ord ∘ₘ X) ∘ₘ P .ord)
  left =
    ≈ₘ-trans (≈ₘ-sym (assoc (Q .ord) (Q .ord ∘ₘ X) (P .ord)))
    (≈ₘ-trans (∘-cong (≈ₘ-sym (assoc (Q .ord) (Q .ord) X)) (≈ₘ-refl {M = P .ord}))
              (∘-cong (∘-cong (ord-idem Q) (≈ₘ-refl {M = X})) (≈ₘ-refl {M = P .ord})))

  right : (((Q .ord ∘ₘ X) ∘ₘ P .ord) ∘ₘ P .ord) ≈ₘ ((Q .ord ∘ₘ X) ∘ₘ P .ord)
  right = ≈ₘ-trans (assoc (Q .ord ∘ₘ X) (P .ord) (P .ord))
                   (∘-cong (≈ₘ-refl {M = Q .ord ∘ₘ X}) (ord-idem P))

close-cong : ∀ {P Q} {X Y : Matrix (Q .dim) (P .dim)} → X ≈ₘ Y → close {P} {Q} X ≈p close {P} {Q} Y
close-cong {P} {Q} X≈Y =
  ∘-cong (∘-cong (≈ₘ-refl {M = Q .ord}) X≈Y) (≈ₘ-refl {M = P .ord})

id : (P : Pos) → P ⇒ P
id P .mat = P .ord
id P .absorbed = ≈ₘ-trans (∘-cong (ord-idem P) (≈ₘ-refl {M = P .ord})) (ord-idem P)

_∘_ : ∀ {P Q R} → Q ⇒ R → P ⇒ Q → P ⇒ R
_∘_ {P} {Q} {R} g f .mat = g .mat ∘ₘ f .mat
_∘_ {P} {Q} {R} g f .absorbed =
  ≈ₘ-trans (∘-cong (≈ₘ-sym (assoc (R .ord) (g .mat) (f .mat))) (≈ₘ-refl {M = P .ord}))
  (≈ₘ-trans (∘-cong (∘-cong (absorb-left g) (≈ₘ-refl {M = f .mat})) (≈ₘ-refl {M = P .ord}))
  (≈ₘ-trans (assoc (g .mat) (f .mat) (P .ord))
            (∘-cong (≈ₘ-refl {M = g .mat}) (absorb-right f))))

infixl 21 _∘_

cat : Category 0ℓ 0ℓ 0ℓ
cat .Category.obj = Pos
cat .Category._⇒_ = _⇒_
cat .Category._≈_ = _≈p_
cat .Category.isEquiv .IsEquivalence.refl = ≈ₘ-refl
cat .Category.isEquiv .IsEquivalence.sym = ≈ₘ-sym
cat .Category.isEquiv .IsEquivalence.trans = ≈ₘ-trans
cat .Category.id = id
cat .Category._∘_ = _∘_
cat .Category.∘-cong = ∘-cong
cat .Category.id-left {f = f} = absorb-left f
cat .Category.id-right {f = f} = absorb-right f
cat .Category.assoc f g h = assoc (f .mat) (g .mat) (h .mat)

+ₘ-cong : ∀ {m n} {M₁ M₂ N₁ N₂ : Matrix m n} → M₁ ≈ₘ M₂ → N₁ ≈ₘ N₂ → (M₁ +ₘ N₁) ≈ₘ (M₂ +ₘ N₂)
+ₘ-cong p q i j = +-cong (p i j) (q i j)

-- Absorption is closed under the additive structure of matrices, since composition annihilates the
-- zero matrix and distributes over sums, so the category is CMon-enriched.
εp : ∀ {P Q} → P ⇒ Q
εp {P} {Q} .mat = εₘ
εp {P} {Q} .absorbed =
  ≈ₘ-trans (∘-cong (comp-bilinear-ε₂ (Q .ord)) (≈ₘ-refl {M = P .ord}))
           (comp-bilinear-ε₁ (P .ord))

_+p_ : ∀ {P Q} → P ⇒ Q → P ⇒ Q → P ⇒ Q
_+p_ {P} {Q} f g .mat = f .mat +ₘ g .mat
_+p_ {P} {Q} f g .absorbed =
  ≈ₘ-trans (∘-cong (comp-bilinear₂ (Q .ord) (f .mat) (g .mat)) (≈ₘ-refl {M = P .ord}))
  (≈ₘ-trans (comp-bilinear₁ (Q .ord ∘ₘ f .mat) (Q .ord ∘ₘ g .mat) (P .ord))
            (+ₘ-cong (f .absorbed) (g .absorbed)))

infixl 21 _+p_

cmon : CMonEnriched cat
cmon .CMonEnriched.homCM P Q .CommutativeMonoid.ε = εp
cmon .CMonEnriched.homCM P Q .CommutativeMonoid._+_ = _+p_
cmon .CMonEnriched.homCM P Q .CommutativeMonoid.+-cong = +ₘ-cong
cmon .CMonEnriched.homCM P Q .CommutativeMonoid.+-lunit i j = +-lunit
cmon .CMonEnriched.homCM P Q .CommutativeMonoid.+-assoc i j = +-assoc
cmon .CMonEnriched.homCM P Q .CommutativeMonoid.+-comm i j = +-comm
cmon .CMonEnriched.comp-bilinear₁ f₁ f₂ g = comp-bilinear₁ (f₁ .mat) (f₂ .mat) (g .mat)
cmon .CMonEnriched.comp-bilinear₂ f g₁ g₂ = comp-bilinear₂ (f .mat) (g₁ .mat) (g₂ .mat)
cmon .CMonEnriched.comp-bilinear-ε₁ f = comp-bilinear-ε₁ (f .mat)
cmon .CMonEnriched.comp-bilinear-ε₂ f = comp-bilinear-ε₂ (f .mat)

ᵀ-cong : ∀ {m n} {M N : Matrix m n} → M ≈ₘ N → (M ᵀ) ≈ₘ (N ᵀ)
ᵀ-cong p i j = p j i

∘-ᵀ : ∀ {m n k} (M : Matrix m n) (N : Matrix n k) → ((M ∘ₘ N) ᵀ) ≈ₘ ((N ᵀ) ∘ₘ (M ᵀ))
∘-ᵀ {n = n} M N k i = Σ-cong {n} (λ j → ·-comm)

-- The opposite order: same diagonal, composite bound by commuting the factors.
op : Pos → Pos
op P .dim = P .dim
op P .ord = P .ord ᵀ
op P .ord-refl = P .ord-refl
op P .ord-trans i j k = ≤-trans (L.≈→≤ ·-comm) (P .ord-trans k j i)

-- Conjugation: an absorbed matrix transposes to a matrix absorbed by the opposite orders, so each
-- object pairs with its opposite.
_ᵀp : ∀ {P Q} → P ⇒ Q → op Q ⇒ op P
_ᵀp {P} {Q} f .mat = f .mat ᵀ
_ᵀp {P} {Q} f .absorbed =
  ≈ₘ-trans (∘-cong (≈ₘ-sym (∘-ᵀ (f .mat) (P .ord))) (≈ₘ-refl {M = Q .ord ᵀ}))
  (≈ₘ-trans (≈ₘ-sym (∘-ᵀ (Q .ord) (f .mat ∘ₘ P .ord)))
            (ᵀ-cong (≈ₘ-trans (≈ₘ-sym (assoc (Q .ord) (f .mat) (P .ord))) (f .absorbed))))

ᵀp-involutive : ∀ {P Q} (f : P ⇒ Q) → (_ᵀp {op Q} {op P} (f ᵀp)) ≈p f
ᵀp-involutive f = ≈ₘ-refl

ᵀp-id : ∀ (P : Pos) → (id P ᵀp) ≈p id (op P)
ᵀp-id P = ≈ₘ-refl

ᵀp-∘ : ∀ {P Q R} (g : Q ⇒ R) (f : P ⇒ Q) → ((g ∘ f) ᵀp) ≈p ((f ᵀp) ∘ (g ᵀp))
ᵀp-∘ g f = ∘-ᵀ (g .mat) (f .mat)

ᵀp-+ : ∀ {P Q} (f g : P ⇒ Q) → ((f +p g) ᵀp) ≈p ((f ᵀp) +p (g ᵀp))
ᵀp-+ f g = ≈ₘ-refl

-- Pointwise order on matrices.
infix 4 _≤ₘ_
_≤ₘ_ : ∀ {m n} → Matrix m n → Matrix m n → Prop 0ℓ
M ≤ₘ N = ∀ i j → M i j L.≤ N i j

≈ₘ→≤ₘ : ∀ {m n} {M N : Matrix m n} → M ≈ₘ N → M ≤ₘ N
≈ₘ→≤ₘ p i j = L.≈→≤ (p i j)

≤ₘ-refl : ∀ {m n} {M : Matrix m n} → M ≤ₘ M
≤ₘ-refl i j = ≤-refl

≤ₘ-trans : ∀ {m n} {M N O : Matrix m n} → M ≤ₘ N → N ≤ₘ O → M ≤ₘ O
≤ₘ-trans p q i j = ≤-trans (p i j) (q i j)

∘ₘ-mono : ∀ {m n k} {M₁ M₂ : Matrix m n} {N₁ N₂ : Matrix n k} →
          M₁ ≤ₘ M₂ → N₁ ≤ₘ N₂ → (M₁ ∘ₘ N₁) ≤ₘ (M₂ ∘ₘ N₂)
∘ₘ-mono {n = n} p q i k = L.Σ-mono (λ j → ≤-trans (L.∧-monoˡ (p i j)) (L.∧-monoʳ (q j k)))

+ₘ-mono : ∀ {m n} {M₁ M₂ N₁ N₂ : Matrix m n} → M₁ ≤ₘ M₂ → N₁ ≤ₘ N₂ → (M₁ +ₘ N₁) ≤ₘ (M₂ +ₘ N₂)
+ₘ-mono p q i j = IsJoin.mono L.∨-isJoin (p i j) (q i j)

+ₘ-runit : ∀ {m n} {M : Matrix m n} → (M +ₘ εₘ) ≈ₘ M
+ₘ-runit i j = trans +-comm +-lunit

-- The identity matrix has unit diagonal and lies below any matrix with reflexive diagonal.
I-diag : ∀ {n} (i : Fin n) → I i i ≈ ι
I-diag zero = refl
I-diag (suc i) = I-diag i

I-≤-diag : ∀ {n} (M : Matrix n n) → (∀ k → ι L.≤ M k k) → I ≤ₘ M
I-≤-diag M h zero    zero    = h zero
I-≤-diag M h zero    (suc j) = IsBottom.≤-bottom L.⊥-isBottom
I-≤-diag M h (suc i) zero    = IsBottom.≤-bottom L.⊥-isBottom
I-≤-diag M h (suc i) (suc j) = I-≤-diag (λ i' j' → M (suc i') (suc j')) (λ k → h (suc k)) i j

-- A composition-idempotent matrix is transitive entrywise.
idem-trans : ∀ {n} {M : Matrix n n} → (M ∘ₘ M) ≈ₘ M → ∀ i j k → (M i j · M j k) L.≤ M i k
idem-trans {n} {M} h i j k = ≤-trans (L.Σ-ub (λ j' → M i j' · M j' k) j) (L.≈→≤ (h i k))

-- The block-diagonal order on a sum of position sets: each block keeps its order, with no order
-- across the blocks. The matrix biproduct structure commutes with it.
module _ (P Q : Pos) where

  private
    m = P .dim
    n = Q .dim

  B : Matrix (m +ℕ n) (m +ℕ n)
  B = ((in₁ {m} {n}) ∘ₘ P .ord ∘ₘ (p₁ {m} {n})) +ₘ ((in₂ {m} {n}) ∘ₘ Q .ord ∘ₘ (p₂ {m} {n}))

  p₁-B : ((p₁ {m} {n}) ∘ₘ B) ≈ₘ (P .ord ∘ₘ (p₁ {m} {n}))
  p₁-B =
    ≈ₘ-trans (comp-bilinear₂ (p₁ {m} {n}) ((in₁ {m} {n}) ∘ₘ P .ord ∘ₘ (p₁ {m} {n})) ((in₂ {m} {n}) ∘ₘ Q .ord ∘ₘ (p₂ {m} {n})))
    (≈ₘ-trans (+ₘ-cong first second) (+ₘ-runit {M = P .ord ∘ₘ (p₁ {m} {n})}))
    where
    first : ((p₁ {m} {n}) ∘ₘ ((in₁ {m} {n}) ∘ₘ P .ord ∘ₘ (p₁ {m} {n}))) ≈ₘ (P .ord ∘ₘ (p₁ {m} {n}))
    first =
      ≈ₘ-trans (≈ₘ-sym (assoc (p₁ {m} {n}) ((in₁ {m} {n}) ∘ₘ P .ord) (p₁ {m} {n})))
      (≈ₘ-trans (∘-cong (≈ₘ-sym (assoc (p₁ {m} {n}) (in₁ {m} {n}) (P .ord))) (≈ₘ-refl {M = (p₁ {m} {n})}))
      (≈ₘ-trans (∘-cong (∘-cong (id-1 m n) (≈ₘ-refl {M = P .ord})) (≈ₘ-refl {M = (p₁ {m} {n})}))
                (∘-cong (id-left {M = P .ord}) (≈ₘ-refl {M = (p₁ {m} {n})}))))

    second : ((p₁ {m} {n}) ∘ₘ ((in₂ {m} {n}) ∘ₘ Q .ord ∘ₘ (p₂ {m} {n}))) ≈ₘ εₘ
    second =
      ≈ₘ-trans (≈ₘ-sym (assoc (p₁ {m} {n}) ((in₂ {m} {n}) ∘ₘ Q .ord) (p₂ {m} {n})))
      (≈ₘ-trans (∘-cong (≈ₘ-sym (assoc (p₁ {m} {n}) (in₂ {m} {n}) (Q .ord))) (≈ₘ-refl {M = (p₂ {m} {n})}))
      (≈ₘ-trans (∘-cong (∘-cong (zero-1 m n) (≈ₘ-refl {M = Q .ord})) (≈ₘ-refl {M = (p₂ {m} {n})}))
      (≈ₘ-trans (∘-cong (comp-bilinear-ε₁ (Q .ord)) (≈ₘ-refl {M = (p₂ {m} {n})}))
                (comp-bilinear-ε₁ (p₂ {m} {n})))))

  p₂-B : ((p₂ {m} {n}) ∘ₘ B) ≈ₘ (Q .ord ∘ₘ (p₂ {m} {n}))
  p₂-B =
    ≈ₘ-trans (comp-bilinear₂ (p₂ {m} {n}) ((in₁ {m} {n}) ∘ₘ P .ord ∘ₘ (p₁ {m} {n})) ((in₂ {m} {n}) ∘ₘ Q .ord ∘ₘ (p₂ {m} {n})))
    (≈ₘ-trans (+ₘ-cong first second)
              (≈ₘ-trans (λ i j → +-comm) (+ₘ-runit {M = Q .ord ∘ₘ (p₂ {m} {n})})))
    where
    first : ((p₂ {m} {n}) ∘ₘ ((in₁ {m} {n}) ∘ₘ P .ord ∘ₘ (p₁ {m} {n}))) ≈ₘ εₘ
    first =
      ≈ₘ-trans (≈ₘ-sym (assoc (p₂ {m} {n}) ((in₁ {m} {n}) ∘ₘ P .ord) (p₁ {m} {n})))
      (≈ₘ-trans (∘-cong (≈ₘ-sym (assoc (p₂ {m} {n}) (in₁ {m} {n}) (P .ord))) (≈ₘ-refl {M = (p₁ {m} {n})}))
      (≈ₘ-trans (∘-cong (∘-cong (zero-2 m n) (≈ₘ-refl {M = P .ord})) (≈ₘ-refl {M = (p₁ {m} {n})}))
      (≈ₘ-trans (∘-cong (comp-bilinear-ε₁ (P .ord)) (≈ₘ-refl {M = (p₁ {m} {n})}))
                (comp-bilinear-ε₁ (p₁ {m} {n})))))

    second : ((p₂ {m} {n}) ∘ₘ ((in₂ {m} {n}) ∘ₘ Q .ord ∘ₘ (p₂ {m} {n}))) ≈ₘ (Q .ord ∘ₘ (p₂ {m} {n}))
    second =
      ≈ₘ-trans (≈ₘ-sym (assoc (p₂ {m} {n}) ((in₂ {m} {n}) ∘ₘ Q .ord) (p₂ {m} {n})))
      (≈ₘ-trans (∘-cong (≈ₘ-sym (assoc (p₂ {m} {n}) (in₂ {m} {n}) (Q .ord))) (≈ₘ-refl {M = (p₂ {m} {n})}))
      (≈ₘ-trans (∘-cong (∘-cong (id-2 m n) (≈ₘ-refl {M = Q .ord})) (≈ₘ-refl {M = (p₂ {m} {n})}))
                (∘-cong (id-left {M = Q .ord}) (≈ₘ-refl {M = (p₂ {m} {n})}))))

  B-in₁ : (B ∘ₘ (in₁ {m} {n})) ≈ₘ ((in₁ {m} {n}) ∘ₘ P .ord)
  B-in₁ =
    ≈ₘ-trans (comp-bilinear₁ ((in₁ {m} {n}) ∘ₘ P .ord ∘ₘ (p₁ {m} {n})) ((in₂ {m} {n}) ∘ₘ Q .ord ∘ₘ (p₂ {m} {n})) (in₁ {m} {n}))
    (≈ₘ-trans (+ₘ-cong first second) (+ₘ-runit {M = (in₁ {m} {n}) ∘ₘ P .ord}))
    where
    first : (((in₁ {m} {n}) ∘ₘ P .ord ∘ₘ (p₁ {m} {n})) ∘ₘ (in₁ {m} {n})) ≈ₘ ((in₁ {m} {n}) ∘ₘ P .ord)
    first =
      ≈ₘ-trans (assoc ((in₁ {m} {n}) ∘ₘ P .ord) (p₁ {m} {n}) (in₁ {m} {n}))
      (≈ₘ-trans (∘-cong (≈ₘ-refl {M = (in₁ {m} {n}) ∘ₘ P .ord}) (id-1 m n))
                (id-right {M = (in₁ {m} {n}) ∘ₘ P .ord}))

    second : (((in₂ {m} {n}) ∘ₘ Q .ord ∘ₘ (p₂ {m} {n})) ∘ₘ (in₁ {m} {n})) ≈ₘ εₘ
    second =
      ≈ₘ-trans (assoc ((in₂ {m} {n}) ∘ₘ Q .ord) (p₂ {m} {n}) (in₁ {m} {n}))
      (≈ₘ-trans (∘-cong (≈ₘ-refl {M = (in₂ {m} {n}) ∘ₘ Q .ord}) (zero-2 m n))
                (comp-bilinear-ε₂ ((in₂ {m} {n}) ∘ₘ Q .ord)))

  B-in₂ : (B ∘ₘ (in₂ {m} {n})) ≈ₘ ((in₂ {m} {n}) ∘ₘ Q .ord)
  B-in₂ =
    ≈ₘ-trans (comp-bilinear₁ ((in₁ {m} {n}) ∘ₘ P .ord ∘ₘ (p₁ {m} {n})) ((in₂ {m} {n}) ∘ₘ Q .ord ∘ₘ (p₂ {m} {n})) (in₂ {m} {n}))
    (≈ₘ-trans (+ₘ-cong first second)
              (≈ₘ-trans (λ i j → +-comm) (+ₘ-runit {M = (in₂ {m} {n}) ∘ₘ Q .ord})))
    where
    first : (((in₁ {m} {n}) ∘ₘ P .ord ∘ₘ (p₁ {m} {n})) ∘ₘ (in₂ {m} {n})) ≈ₘ εₘ
    first =
      ≈ₘ-trans (assoc ((in₁ {m} {n}) ∘ₘ P .ord) (p₁ {m} {n}) (in₂ {m} {n}))
      (≈ₘ-trans (∘-cong (≈ₘ-refl {M = (in₁ {m} {n}) ∘ₘ P .ord}) (zero-1 m n))
                (comp-bilinear-ε₂ ((in₁ {m} {n}) ∘ₘ P .ord)))

    second : (((in₂ {m} {n}) ∘ₘ Q .ord ∘ₘ (p₂ {m} {n})) ∘ₘ (in₂ {m} {n})) ≈ₘ ((in₂ {m} {n}) ∘ₘ Q .ord)
    second =
      ≈ₘ-trans (assoc ((in₂ {m} {n}) ∘ₘ Q .ord) (p₂ {m} {n}) (in₂ {m} {n}))
      (≈ₘ-trans (∘-cong (≈ₘ-refl {M = (in₂ {m} {n}) ∘ₘ Q .ord}) (id-2 m n))
                (id-right {M = (in₂ {m} {n}) ∘ₘ Q .ord}))

  B-idem : (B ∘ₘ B) ≈ₘ B
  B-idem =
    ≈ₘ-trans (comp-bilinear₁ ((in₁ {m} {n}) ∘ₘ P .ord ∘ₘ (p₁ {m} {n})) ((in₂ {m} {n}) ∘ₘ Q .ord ∘ₘ (p₂ {m} {n})) B)
             (+ₘ-cong first second)
    where
    first : (((in₁ {m} {n}) ∘ₘ P .ord ∘ₘ (p₁ {m} {n})) ∘ₘ B) ≈ₘ ((in₁ {m} {n}) ∘ₘ P .ord ∘ₘ (p₁ {m} {n}))
    first =
      ≈ₘ-trans (assoc ((in₁ {m} {n}) ∘ₘ P .ord) (p₁ {m} {n}) B)
      (≈ₘ-trans (∘-cong (≈ₘ-refl {M = (in₁ {m} {n}) ∘ₘ P .ord}) p₁-B)
      (≈ₘ-trans (≈ₘ-sym (assoc ((in₁ {m} {n}) ∘ₘ P .ord) (P .ord) (p₁ {m} {n})))
      (≈ₘ-trans (∘-cong (assoc (in₁ {m} {n}) (P .ord) (P .ord)) (≈ₘ-refl {M = (p₁ {m} {n})}))
                (∘-cong (∘-cong (≈ₘ-refl {M = (in₁ {m} {n})}) (ord-idem P)) (≈ₘ-refl {M = (p₁ {m} {n})})))))

    second : (((in₂ {m} {n}) ∘ₘ Q .ord ∘ₘ (p₂ {m} {n})) ∘ₘ B) ≈ₘ ((in₂ {m} {n}) ∘ₘ Q .ord ∘ₘ (p₂ {m} {n}))
    second =
      ≈ₘ-trans (assoc ((in₂ {m} {n}) ∘ₘ Q .ord) (p₂ {m} {n}) B)
      (≈ₘ-trans (∘-cong (≈ₘ-refl {M = (in₂ {m} {n}) ∘ₘ Q .ord}) p₂-B)
      (≈ₘ-trans (≈ₘ-sym (assoc ((in₂ {m} {n}) ∘ₘ Q .ord) (Q .ord) (p₂ {m} {n})))
      (≈ₘ-trans (∘-cong (assoc (in₂ {m} {n}) (Q .ord) (Q .ord)) (≈ₘ-refl {M = (p₂ {m} {n})}))
                (∘-cong (∘-cong (≈ₘ-refl {M = (in₂ {m} {n})}) (ord-idem Q)) (≈ₘ-refl {M = (p₂ {m} {n})})))))

  I-≤-B : I ≤ₘ B
  I-≤-B =
    ≤ₘ-trans (≈ₘ→≤ₘ (≈ₘ-sym (id-+ m n)))
             (+ₘ-mono (∘ₘ-mono below₁ (≤ₘ-refl {M = (p₁ {m} {n})}))
                      (∘ₘ-mono below₂ (≤ₘ-refl {M = (p₂ {m} {n})})))
    where
    below₁ : (in₁ {m} {n}) ≤ₘ ((in₁ {m} {n}) ∘ₘ P .ord)
    below₁ = ≤ₘ-trans (≈ₘ→≤ₘ (≈ₘ-sym (id-right {M = (in₁ {m} {n})})))
                      (∘ₘ-mono (≤ₘ-refl {M = (in₁ {m} {n})}) (I-≤-diag (P .ord) (P .ord-refl)))

    below₂ : (in₂ {m} {n}) ≤ₘ ((in₂ {m} {n}) ∘ₘ Q .ord)
    below₂ = ≤ₘ-trans (≈ₘ→≤ₘ (≈ₘ-sym (id-right {M = (in₂ {m} {n})})))
                      (∘ₘ-mono (≤ₘ-refl {M = (in₂ {m} {n})}) (I-≤-diag (Q .ord) (Q .ord-refl)))

_⊕_ : Pos → Pos → Pos
(P ⊕ Q) .dim = P .dim +ℕ Q .dim
(P ⊕ Q) .ord = B P Q
(P ⊕ Q) .ord-refl i = ≤-trans (L.≈→≤ (sym (I-diag i))) (I-≤-B P Q i i)
(P ⊕ Q) .ord-trans = idem-trans (B-idem P Q)

-- Projections and injections, corrected by the block orders to be absorbed.
π₁ : ∀ (P Q : Pos) → (P ⊕ Q) ⇒ P
π₁ P Q .mat = P .ord ∘ₘ (p₁ {P .dim} {Q .dim})
π₁ P Q .absorbed =
  ≈ₘ-trans (∘-cong left (≈ₘ-refl {M = B P Q})) right
  where
  left : (P .ord ∘ₘ (P .ord ∘ₘ (p₁ {P .dim} {Q .dim}))) ≈ₘ (P .ord ∘ₘ (p₁ {P .dim} {Q .dim}))
  left = ≈ₘ-trans (≈ₘ-sym (assoc (P .ord) (P .ord) (p₁ {P .dim} {Q .dim})))
                  (∘-cong (ord-idem P) (≈ₘ-refl {M = (p₁ {P .dim} {Q .dim})}))

  right : ((P .ord ∘ₘ (p₁ {P .dim} {Q .dim})) ∘ₘ B P Q) ≈ₘ (P .ord ∘ₘ (p₁ {P .dim} {Q .dim}))
  right =
    ≈ₘ-trans (assoc (P .ord) (p₁ {P .dim} {Q .dim}) (B P Q))
    (≈ₘ-trans (∘-cong (≈ₘ-refl {M = P .ord}) (p₁-B P Q))
    (≈ₘ-trans (≈ₘ-sym (assoc (P .ord) (P .ord) (p₁ {P .dim} {Q .dim})))
              (∘-cong (ord-idem P) (≈ₘ-refl {M = (p₁ {P .dim} {Q .dim})}))))

π₂ : ∀ (P Q : Pos) → (P ⊕ Q) ⇒ Q
π₂ P Q .mat = Q .ord ∘ₘ (p₂ {P .dim} {Q .dim})
π₂ P Q .absorbed =
  ≈ₘ-trans (∘-cong left (≈ₘ-refl {M = B P Q})) right
  where
  left : (Q .ord ∘ₘ (Q .ord ∘ₘ (p₂ {P .dim} {Q .dim}))) ≈ₘ (Q .ord ∘ₘ (p₂ {P .dim} {Q .dim}))
  left = ≈ₘ-trans (≈ₘ-sym (assoc (Q .ord) (Q .ord) (p₂ {P .dim} {Q .dim})))
                  (∘-cong (ord-idem Q) (≈ₘ-refl {M = (p₂ {P .dim} {Q .dim})}))

  right : ((Q .ord ∘ₘ (p₂ {P .dim} {Q .dim})) ∘ₘ B P Q) ≈ₘ (Q .ord ∘ₘ (p₂ {P .dim} {Q .dim}))
  right =
    ≈ₘ-trans (assoc (Q .ord) (p₂ {P .dim} {Q .dim}) (B P Q))
    (≈ₘ-trans (∘-cong (≈ₘ-refl {M = Q .ord}) (p₂-B P Q))
    (≈ₘ-trans (≈ₘ-sym (assoc (Q .ord) (Q .ord) (p₂ {P .dim} {Q .dim})))
              (∘-cong (ord-idem Q) (≈ₘ-refl {M = (p₂ {P .dim} {Q .dim})}))))

ι₁ : ∀ (P Q : Pos) → P ⇒ (P ⊕ Q)
ι₁ P Q .mat = (in₁ {P .dim} {Q .dim}) ∘ₘ P .ord
ι₁ P Q .absorbed =
  ≈ₘ-trans (∘-cong left (≈ₘ-refl {M = P .ord})) right
  where
  left : (B P Q ∘ₘ ((in₁ {P .dim} {Q .dim}) ∘ₘ P .ord)) ≈ₘ ((in₁ {P .dim} {Q .dim}) ∘ₘ P .ord)
  left =
    ≈ₘ-trans (≈ₘ-sym (assoc (B P Q) (in₁ {P .dim} {Q .dim}) (P .ord)))
    (≈ₘ-trans (∘-cong (B-in₁ P Q) (≈ₘ-refl {M = P .ord}))
    (≈ₘ-trans (assoc (in₁ {P .dim} {Q .dim}) (P .ord) (P .ord))
              (∘-cong (≈ₘ-refl {M = (in₁ {P .dim} {Q .dim})}) (ord-idem P))))

  right : (((in₁ {P .dim} {Q .dim}) ∘ₘ P .ord) ∘ₘ P .ord) ≈ₘ ((in₁ {P .dim} {Q .dim}) ∘ₘ P .ord)
  right = ≈ₘ-trans (assoc (in₁ {P .dim} {Q .dim}) (P .ord) (P .ord))
                   (∘-cong (≈ₘ-refl {M = (in₁ {P .dim} {Q .dim})}) (ord-idem P))

ι₂ : ∀ (P Q : Pos) → Q ⇒ (P ⊕ Q)
ι₂ P Q .mat = (in₂ {P .dim} {Q .dim}) ∘ₘ Q .ord
ι₂ P Q .absorbed =
  ≈ₘ-trans (∘-cong left (≈ₘ-refl {M = Q .ord})) right
  where
  left : (B P Q ∘ₘ ((in₂ {P .dim} {Q .dim}) ∘ₘ Q .ord)) ≈ₘ ((in₂ {P .dim} {Q .dim}) ∘ₘ Q .ord)
  left =
    ≈ₘ-trans (≈ₘ-sym (assoc (B P Q) (in₂ {P .dim} {Q .dim}) (Q .ord)))
    (≈ₘ-trans (∘-cong (B-in₂ P Q) (≈ₘ-refl {M = Q .ord}))
    (≈ₘ-trans (assoc (in₂ {P .dim} {Q .dim}) (Q .ord) (Q .ord))
              (∘-cong (≈ₘ-refl {M = (in₂ {P .dim} {Q .dim})}) (ord-idem Q))))

  right : (((in₂ {P .dim} {Q .dim}) ∘ₘ Q .ord) ∘ₘ Q .ord) ≈ₘ ((in₂ {P .dim} {Q .dim}) ∘ₘ Q .ord)
  right = ≈ₘ-trans (assoc (in₂ {P .dim} {Q .dim}) (Q .ord) (Q .ord))
                   (∘-cong (≈ₘ-refl {M = (in₂ {P .dim} {Q .dim})}) (ord-idem Q))

-- The five biproduct laws, with the order matrices as the identities.
biproduct : ∀ (P Q : Pos) → Biproduct cmon P Q
biproduct P Q .Biproduct.prod = P ⊕ Q
biproduct P Q .Biproduct.p₁ = π₁ P Q
biproduct P Q .Biproduct.p₂ = π₂ P Q
biproduct P Q .Biproduct.in₁ = ι₁ P Q
biproduct P Q .Biproduct.in₂ = ι₂ P Q
biproduct P Q .Biproduct.id-1 =
  ≈ₘ-trans (assoc (P .ord) (p₁ {P .dim} {Q .dim}) ((in₁ {P .dim} {Q .dim}) ∘ₘ P .ord))
  (≈ₘ-trans (∘-cong (≈ₘ-refl {M = P .ord}) (≈ₘ-sym (assoc (p₁ {P .dim} {Q .dim}) (in₁ {P .dim} {Q .dim}) (P .ord))))
  (≈ₘ-trans (∘-cong (≈ₘ-refl {M = P .ord}) (∘-cong (id-1 (P .dim) (Q .dim)) (≈ₘ-refl {M = P .ord})))
  (≈ₘ-trans (∘-cong (≈ₘ-refl {M = P .ord}) (id-left {M = P .ord}))
            (ord-idem P))))
biproduct P Q .Biproduct.id-2 =
  ≈ₘ-trans (assoc (Q .ord) (p₂ {P .dim} {Q .dim}) ((in₂ {P .dim} {Q .dim}) ∘ₘ Q .ord))
  (≈ₘ-trans (∘-cong (≈ₘ-refl {M = Q .ord}) (≈ₘ-sym (assoc (p₂ {P .dim} {Q .dim}) (in₂ {P .dim} {Q .dim}) (Q .ord))))
  (≈ₘ-trans (∘-cong (≈ₘ-refl {M = Q .ord}) (∘-cong (id-2 (P .dim) (Q .dim)) (≈ₘ-refl {M = Q .ord})))
  (≈ₘ-trans (∘-cong (≈ₘ-refl {M = Q .ord}) (id-left {M = Q .ord}))
            (ord-idem Q))))
biproduct P Q .Biproduct.zero-1 =
  ≈ₘ-trans (assoc (P .ord) (p₁ {P .dim} {Q .dim}) ((in₂ {P .dim} {Q .dim}) ∘ₘ Q .ord))
  (≈ₘ-trans (∘-cong (≈ₘ-refl {M = P .ord}) (≈ₘ-sym (assoc (p₁ {P .dim} {Q .dim}) (in₂ {P .dim} {Q .dim}) (Q .ord))))
  (≈ₘ-trans (∘-cong (≈ₘ-refl {M = P .ord}) (∘-cong (zero-1 (P .dim) (Q .dim)) (≈ₘ-refl {M = Q .ord})))
  (≈ₘ-trans (∘-cong (≈ₘ-refl {M = P .ord}) (comp-bilinear-ε₁ (Q .ord)))
            (comp-bilinear-ε₂ (P .ord)))))
biproduct P Q .Biproduct.zero-2 =
  ≈ₘ-trans (assoc (Q .ord) (p₂ {P .dim} {Q .dim}) ((in₁ {P .dim} {Q .dim}) ∘ₘ P .ord))
  (≈ₘ-trans (∘-cong (≈ₘ-refl {M = Q .ord}) (≈ₘ-sym (assoc (p₂ {P .dim} {Q .dim}) (in₁ {P .dim} {Q .dim}) (P .ord))))
  (≈ₘ-trans (∘-cong (≈ₘ-refl {M = Q .ord}) (∘-cong (zero-2 (P .dim) (Q .dim)) (≈ₘ-refl {M = P .ord})))
  (≈ₘ-trans (∘-cong (≈ₘ-refl {M = Q .ord}) (comp-bilinear-ε₁ (P .ord)))
            (comp-bilinear-ε₂ (Q .ord)))))
biproduct P Q .Biproduct.id-+ = +ₘ-cong first second
  where
  first : (((in₁ {P .dim} {Q .dim}) ∘ₘ P .ord) ∘ₘ (P .ord ∘ₘ (p₁ {P .dim} {Q .dim}))) ≈ₘ ((in₁ {P .dim} {Q .dim}) ∘ₘ P .ord ∘ₘ (p₁ {P .dim} {Q .dim}))
  first =
    ≈ₘ-trans (≈ₘ-sym (assoc ((in₁ {P .dim} {Q .dim}) ∘ₘ P .ord) (P .ord) (p₁ {P .dim} {Q .dim})))
    (≈ₘ-trans (∘-cong (assoc (in₁ {P .dim} {Q .dim}) (P .ord) (P .ord)) (≈ₘ-refl {M = (p₁ {P .dim} {Q .dim})}))
              (∘-cong (∘-cong (≈ₘ-refl {M = (in₁ {P .dim} {Q .dim})}) (ord-idem P)) (≈ₘ-refl {M = (p₁ {P .dim} {Q .dim})})))

  second : (((in₂ {P .dim} {Q .dim}) ∘ₘ Q .ord) ∘ₘ (Q .ord ∘ₘ (p₂ {P .dim} {Q .dim}))) ≈ₘ ((in₂ {P .dim} {Q .dim}) ∘ₘ Q .ord ∘ₘ (p₂ {P .dim} {Q .dim}))
  second =
    ≈ₘ-trans (≈ₘ-sym (assoc ((in₂ {P .dim} {Q .dim}) ∘ₘ Q .ord) (Q .ord) (p₂ {P .dim} {Q .dim})))
    (≈ₘ-trans (∘-cong (assoc (in₂ {P .dim} {Q .dim}) (Q .ord) (Q .ord)) (≈ₘ-refl {M = (p₂ {P .dim} {Q .dim})}))
              (∘-cong (∘-cong (≈ₘ-refl {M = (in₂ {P .dim} {Q .dim})}) (ord-idem Q)) (≈ₘ-refl {M = (p₂ {P .dim} {Q .dim})})))

-- The discrete order: the identity matrix, so every matrix between discrete orders is absorbed
-- and the free first-order model is the special case at discrete orders.
disc : ℕ → Pos
disc n .dim = n
disc n .ord = I
disc n .ord-refl i = L.≈→≤ (sym (I-diag i))
disc n .ord-trans = idem-trans (id-left {M = I})

-- The block order on two discrete orders is discrete.
B-disc : ∀ m n → B (disc m) (disc n) ≈ₘ I
B-disc m n =
  ≈ₘ-trans (+ₘ-cong (∘-cong (id-right {M = in₁ {m} {n}}) (≈ₘ-refl {M = p₁ {m} {n}}))
                    (∘-cong (id-right {M = in₂ {m} {n}}) (≈ₘ-refl {M = p₂ {m} {n}})))
           (id-+ m n)

-- So the identity matrix mediates an isomorphism between the biproduct of discrete orders and the
-- discrete order on the sum.
disc-⊕ : ∀ m n → Category.Iso cat (disc m ⊕ disc n) (disc (m +ℕ n))
disc-⊕ m n .Category.Iso.fwd .mat = I
disc-⊕ m n .Category.Iso.fwd .absorbed =
  ≈ₘ-trans (∘-cong (id-left {M = I}) (≈ₘ-refl {M = B (disc m) (disc n)}))
           (≈ₘ-trans (id-left {M = B (disc m) (disc n)}) (B-disc m n))
disc-⊕ m n .Category.Iso.bwd .mat = I
disc-⊕ m n .Category.Iso.bwd .absorbed =
  ≈ₘ-trans (id-right {M = B (disc m) (disc n) ∘ₘ I})
           (≈ₘ-trans (id-right {M = B (disc m) (disc n)}) (B-disc m n))
disc-⊕ m n .Category.Iso.fwd∘bwd≈id = id-left {M = I}
disc-⊕ m n .Category.Iso.bwd∘fwd≈id = ≈ₘ-trans (id-left {M = I}) (≈ₘ-sym (B-disc m n))

-- The empty position order is terminal: a morphism into it is a matrix with no rows, so any two
-- agree vacuously.
𝟘p : Pos
𝟘p = disc 0

terminal : HasTerminal cat
terminal .HasTerminal.witness = 𝟘p
terminal .HasTerminal.is-terminal .IsTerminal.to-terminal .mat = εₘ
terminal .HasTerminal.is-terminal .IsTerminal.to-terminal .absorbed ()
terminal .HasTerminal.is-terminal .IsTerminal.to-terminal-ext f ()

-- Lift a position order by a new root: a fresh position, an ancestor of every position (the
-- order-theoretic lifting). A down-closed selection that keeps any position keeps the root, so a
-- constructor cell is the lift of the biproduct of its arguments' orders.
lift : Pos → Pos
lift P .dim = suc (P .dim)
lift P .ord zero    p       = ι
lift P .ord (suc q) zero    = ε
lift P .ord (suc q) (suc p) = P .ord q p
lift P .ord-refl zero    = ≤-refl
lift P .ord-refl (suc i) = P .ord-refl i
lift P .ord-trans zero    j k = IsTop.≤-top L.⊤-isTop
lift P .ord-trans (suc i) zero k =
  ≤-trans (L.≈→≤ ε-annihilₗ) (IsBottom.≤-bottom L.⊥-isBottom)
lift P .ord-trans (suc i) (suc j) zero = L.≈→≤ ε-annihilᵣ
lift P .ord-trans (suc i) (suc j) (suc k) = P .ord-trans i j k

-- The action on morphisms: root tracks root, the inner block tracks the morphism, and closure
-- under the orders makes the root row dominate its columns.
lift-block : ∀ {P Q} → P ⇒ Q → Matrix (suc (Q .dim)) (suc (P .dim))
lift-block f zero    zero    = ι
lift-block f zero    (suc p) = ε
lift-block f (suc q) zero    = ε
lift-block f (suc q) (suc p) = f .mat q p

lift-mor : ∀ {P Q} → P ⇒ Q → lift P ⇒ lift Q
lift-mor {P} {Q} f = close {lift P} {lift Q} (lift-block f)
