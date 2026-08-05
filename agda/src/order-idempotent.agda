{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (0ℓ)
open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Data.Fin using (Fin; zero; suc)
import Data.Vec as DV
open import Data.Vec.Properties using (lookup∘tabulate)
open import Relation.Binary.PropositionalEquality using () renaming (_≡_ to _≡p_; refl to ≡p-refl)
open import prop using (∃ₛ) renaming (_,_ to _,ₚ_)
open import prop-setoid using (Setoid; IsEquivalence) renaming (_⇒_ to _⇒s_; _≃m_ to _≃s_)
open import commutative-semiring using (CommutativeSemiring)
open import basics using (IsPreorder; IsJoin; IsBottom; IsTop)
open import categories using (Category; HasTerminal; IsTerminal)
open import commutative-monoid using (CommutativeMonoid)
open import cmon-enriched using (CMonEnriched; Biproduct)
open import functor using (Functor)
import matrix
import semimodule

-- Position orders as matrices. Over a commutative semiring whose addition is idempotent, the matrix
-- of a preorder on positions (entry (q, p) is ⊤ when q ≤ p) is idempotent under composition, and
-- the vectors it fixes are the down-closed selections of positions. Objects pair a dimension with
-- such a matrix; morphisms are the semimodule maps between the semimodules of down-closed
-- selections. Matrix action is a bijection between morphisms and the matrices the orders at either
-- end absorb, so the category is the Karoubi envelope of Mat(S) at the order idempotents, realised
-- on the fixed vectors; identity, composition and the CMon enrichment are inherited from the
-- semimodules, and the absorbed matrix is a presentation.
module order-idempotent
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (let open CommutativeSemiring S hiding (_≈_; trans; sym; refl); open Setoid A)
  (∨-idem    : ∀ {x} → x + x ≈ x)
  (∧-idem    : ∀ {x} → x · x ≈ x)
  (⊤-add-top : ∀ {x} → ι + x ≈ ι)
  where

open matrix.Mat S
  using (Matrix; Vec; Σ; I; _ᵀ; _≈ₘ_; ∘-cong; assoc; id-left; id-right;
         Σ-cong; Σ-ε; Σ-+; Σ-·-distribₗ; Σ-·-distribᵣ; Σ-interchange; _+ₘ_; εₘ;
         comp-bilinear₁; comp-bilinear₂; comp-bilinear-ε₁; comp-bilinear-ε₂;
         p₁; p₂; in₁; in₂; id-1; id-2; zero-1; zero-2; id-+)
  renaming (_∘_ to _∘ₘ_)
module L = matrix.DistributiveLattice S ∨-idem ∧-idem ⊤-add-top
open IsPreorder L.≤-isPreorder using () renaming (refl to ≤-refl; trans to ≤-trans)
module SemiMod = semimodule S
open SemiMod using (Semimodule)
open SemiMod._⇒_
open SemiMod._≈m_

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

+ₘ-cong : ∀ {m n} {M₁ M₂ N₁ N₂ : Matrix m n} → M₁ ≈ₘ M₂ → N₁ ≈ₘ N₂ → (M₁ +ₘ N₁) ≈ₘ (M₂ +ₘ N₂)
+ₘ-cong p q i j = +-cong (p i j) (q i j)

ᵀ-cong : ∀ {m n} {M N : Matrix m n} → M ≈ₘ N → (M ᵀ) ≈ₘ (N ᵀ)
ᵀ-cong p i j = p j i

∘-ᵀ : ∀ {m n k} (M : Matrix m n) (N : Matrix n k) → ((M ∘ₘ N) ᵀ) ≈ₘ ((N ᵀ) ∘ₘ (M ᵀ))
∘-ᵀ {n = n} M N k i = Σ-cong {n} (λ j → ·-comm)

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

-- A matrix acting on a vector, and the vectors an order fixes: the down-closed selections.
app : ∀ {m n} → Matrix m n → Vec n → Vec m
app {m} {n} M v i = Σ {n} (λ j → M i j · v j)

Fixed : ∀ (P : Pos) → Vec (P .dim) → Prop 0ℓ
Fixed P v = ∀ i → app (P .ord) v i ≈ v i

-- The action is linear in the vector and additive in the matrix.
app-+ : ∀ {m n} (R : Matrix m n) (u v : Vec n) (i : Fin m) →
        app R (λ j → u j + v j) i ≈ (app R u i + app R v i)
app-+ {m} {n} R u v i =
  trans (Σ-cong {n} (λ j → ·-+-distribₗ))
        (sym (Σ-+ {n} (λ j → R i j · u j) (λ j → R i j · v j)))

app-· : ∀ {m n} (R : Matrix m n) (s : Setoid.Carrier A) (u : Vec n) (i : Fin m) →
        app R (λ j → s · u j) i ≈ (s · app R u i)
app-· {m} {n} R s u i =
  trans (Σ-cong {n} (λ j → trans (sym ·-assoc) (trans (·-cong ·-comm refl) ·-assoc)))
        (sym (Σ-·-distribₗ {n} s (λ j → R i j · u j)))

app-ε : ∀ {m n} (R : Matrix m n) (i : Fin m) → app R (λ _ → ε) i ≈ ε
app-ε {m} {n} R i = trans (Σ-cong {n} (λ j → ε-annihilᵣ)) (Σ-ε {n})

app-congₘ : ∀ {m n} {R R' : Matrix m n} → R ≈ₘ R' →
            ∀ (v : Vec n) (i : Fin m) → app R v i ≈ app R' v i
app-congₘ {m} {n} h v i = Σ-cong {n} (λ j → ·-cong (h i j) refl)

app-∘ : ∀ {m n k} (R : Matrix m n) (T : Matrix n k) (v : Vec k) (i : Fin m) →
        app (R ∘ₘ T) v i ≈ app R (app T v) i
app-∘ {m} {n} {k} R T v i =
  trans (Σ-cong {k} (λ j → Σ-·-distribᵣ (λ l → R i l · T l j) (v j)))
  (trans (Σ-cong {k} (λ j → Σ-cong {n} (λ l → ·-assoc)))
  (trans (Σ-interchange {k} {n} (λ j l → R i l · (T l j · v j)))
         (Σ-cong {n} (λ l → sym (Σ-·-distribₗ (R i l) (λ j → T l j · v j))))))

app-+ₘ : ∀ {m n} (R T : Matrix m n) (v : Vec n) (i : Fin m) →
         app (R +ₘ T) v i ≈ (app R v i + app T v i)
app-+ₘ {m} {n} R T v i =
  trans (Σ-cong {n} (λ j → ·-+-distribᵣ))
        (sym (Σ-+ {n} (λ j → R i j · v j) (λ j → T i j · v j)))

-- The support of a selection: the join of the coordinates. No matrix increases it, since each
-- entry is below ι.
supp : ∀ {n} → Vec n → Setoid.Carrier A
supp {n} v = Σ {n} v

supp-+ : ∀ {n} (u v : Vec n) → supp {n} (λ i → u i + v i) ≈ (supp {n} u + supp {n} v)
supp-+ {n} u v = sym (Σ-+ u v)

supp-· : ∀ {n} (s : Setoid.Carrier A) (v : Vec n) → supp {n} (λ i → s · v i) ≈ (s · supp {n} v)
supp-· {n} s v = sym (Σ-·-distribₗ s v)

supp-mono : ∀ {m n} (M : Matrix m n) (v : Vec n) → supp {m} (app M v) L.≤ supp {n} v
supp-mono {m} {n} M v =
  L.Σ-lub {m} (λ i → app M v i)
    (λ i → L.Σ-lub {n} (λ j → M i j · v j)
             (λ j → ≤-trans (L.∧-monoˡ (IsTop.≤-top L.⊤-isTop))
                    (≤-trans (L.≈→≤ ·-lunit) (L.Σ-ub {n} v j))))

-- The semimodule of down-closed selections, pointwise.
𝒟 : Pos → Semimodule
𝒟 P .Semimodule.setoid .Setoid.Carrier = ∃ₛ (Vec (P .dim)) (Fixed P)
𝒟 P .Semimodule.setoid .Setoid._≈_ (u ,ₚ _) (v ,ₚ _) = ∀ i → u i ≈ v i
𝒟 P .Semimodule.setoid .Setoid.isEquivalence .IsEquivalence.refl i = refl
𝒟 P .Semimodule.setoid .Setoid.isEquivalence .IsEquivalence.sym e i = sym (e i)
𝒟 P .Semimodule.setoid .Setoid.isEquivalence .IsEquivalence.trans e e' i = trans (e i) (e' i)
𝒟 P .Semimodule.additive .CommutativeMonoid.ε = (λ _ → ε) ,ₚ (λ i → app-ε (P .ord) i)
𝒟 P .Semimodule.additive .CommutativeMonoid._+_ (u ,ₚ p) (v ,ₚ q) =
  (λ i → u i + v i) ,ₚ (λ i → trans (app-+ (P .ord) u v i) (+-cong (p i) (q i)))
𝒟 P .Semimodule.additive .CommutativeMonoid.+-cong e e' i = +-cong (e i) (e' i)
𝒟 P .Semimodule.additive .CommutativeMonoid.+-lunit i = +-lunit
𝒟 P .Semimodule.additive .CommutativeMonoid.+-assoc i = +-assoc
𝒟 P .Semimodule.additive .CommutativeMonoid.+-comm i = +-comm
𝒟 P .Semimodule._·_ s (u ,ₚ p) =
  (λ i → s · u i) ,ₚ (λ i → trans (app-· (P .ord) s u i) (·-cong refl (p i)))
𝒟 P .Semimodule.·-cong e e' i = ·-cong e (e' i)
𝒟 P .Semimodule.·-mul i = ·-assoc
𝒟 P .Semimodule.·-unit i = ·-lunit
𝒟 P .Semimodule.+-distribʳ i = ·-+-distribᵣ
𝒟 P .Semimodule.+-distribˡ i = ·-+-distribₗ
𝒟 P .Semimodule.zero-distribʳ i = ε-annihilₗ
𝒟 P .Semimodule.zero-distribˡ i = ε-annihilᵣ

vec : ∀ (P : Pos) → ∃ₛ (Vec (P .dim)) (Fixed P) → Vec (P .dim)
vec P (u ,ₚ _) = u

fxd : ∀ (P : Pos) (x : ∃ₛ (Vec (P .dim)) (Fixed P)) → Fixed P (vec P x)
fxd P (u ,ₚ p) = p

-- The down-closure of a basis vector is a selection, fixed by idempotence of the order.
colv : ∀ (P : Pos) (p : Fin (P .dim)) → ∃ₛ (Vec (P .dim)) (Fixed P)
colv P p = (λ i → P .ord i p) ,ₚ (λ i → ord-idem P i p)

-- The same column, tabulated: each order entry is computed once and read back by lookup, so the
-- many coordinate reads an evaluation makes do not each recompute a block-order entry.
private
  ≡→≈ : ∀ {x y : Setoid.Carrier A} → x ≡p y → x ≈ y
  ≡→≈ ≡p-refl = refl

colv-tab : ∀ (P : Pos) (p : Fin (P .dim)) → ∃ₛ (Vec (P .dim)) (Fixed P)
colv-tab P p = v' ,ₚ fixed
  where
  t = DV.tabulate (λ i → P .ord i p)

  v' : Vec (P .dim)
  v' i = DV.lookup t i

  v'-col : ∀ i → v' i ≡p P .ord i p
  v'-col i = lookup∘tabulate (λ j → P .ord j p) i

  fixed : Fixed P v'
  fixed i =
    trans (Σ-cong {P .dim} (λ j → ·-cong refl (≡→≈ (v'-col j))))
          (trans (ord-idem P i p) (sym (≡→≈ (v'-col i))))

-- A matrix absorbed by the order matrices at either end: a presentation of a morphism. Columns are
-- indexed by the source, as in Mat.cat.
record _⇒ₘ_ (P Q : Pos) : Set where
  field
    mat : Matrix (Q .dim) (P .dim)
    absorbed : (Q .ord ∘ₘ mat ∘ₘ P .ord) ≈ₘ mat

open _⇒ₘ_ public

-- Either order matrix alone already absorbs.
absorb-left : ∀ {P Q} (f : P ⇒ₘ Q) → (Q .ord ∘ₘ f .mat) ≈ₘ f .mat
absorb-left {P} {Q} f =
  ≈ₘ-trans (∘-cong (≈ₘ-refl {M = Q .ord}) (≈ₘ-sym (f .absorbed)))
  (≈ₘ-trans (≈ₘ-sym (assoc (Q .ord) (Q .ord ∘ₘ f .mat) (P .ord)))
  (≈ₘ-trans (∘-cong (≈ₘ-sym (assoc (Q .ord) (Q .ord) (f .mat))) (≈ₘ-refl {M = P .ord}))
  (≈ₘ-trans (∘-cong (∘-cong (ord-idem Q) (≈ₘ-refl {M = f .mat})) (≈ₘ-refl {M = P .ord}))
            (f .absorbed))))

absorb-right : ∀ {P Q} (f : P ⇒ₘ Q) → (f .mat ∘ₘ P .ord) ≈ₘ f .mat
absorb-right {P} {Q} f =
  ≈ₘ-trans (∘-cong (≈ₘ-sym (f .absorbed)) (≈ₘ-refl {M = P .ord}))
  (≈ₘ-trans (assoc (Q .ord ∘ₘ f .mat) (P .ord) (P .ord))
  (≈ₘ-trans (∘-cong (≈ₘ-refl {M = Q .ord ∘ₘ f .mat}) (ord-idem P))
            (f .absorbed)))

-- Every matrix presents a morphism after closing under the orders at either end; the result is
-- absorbed because the orders are idempotent.
close : ∀ {P Q} → Matrix (Q .dim) (P .dim) → P ⇒ₘ Q
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

close-cong : ∀ {P Q} {X Y : Matrix (Q .dim) (P .dim)} →
             X ≈ₘ Y → close {P} {Q} X .mat ≈ₘ close {P} {Q} Y .mat
close-cong {P} {Q} X≈Y =
  ∘-cong (∘-cong (≈ₘ-refl {M = Q .ord}) X≈Y) (≈ₘ-refl {M = P .ord})

-- The order presents the identity, and matrix product the composite.
ordₘ : (P : Pos) → P ⇒ₘ P
ordₘ P .mat = P .ord
ordₘ P .absorbed = ≈ₘ-trans (∘-cong (ord-idem P) (≈ₘ-refl {M = P .ord})) (ord-idem P)

compₘ : ∀ {P Q R} → Q ⇒ₘ R → P ⇒ₘ Q → P ⇒ₘ R
compₘ {P} {Q} {R} g f .mat = g .mat ∘ₘ f .mat
compₘ {P} {Q} {R} g f .absorbed =
  ≈ₘ-trans (∘-cong (≈ₘ-sym (assoc (R .ord) (g .mat) (f .mat))) (≈ₘ-refl {M = P .ord}))
  (≈ₘ-trans (∘-cong (∘-cong (absorb-left g) (≈ₘ-refl {M = f .mat})) (≈ₘ-refl {M = P .ord}))
  (≈ₘ-trans (assoc (g .mat) (f .mat) (P .ord))
            (∘-cong (≈ₘ-refl {M = g .mat}) (absorb-right f))))

-- Morphisms are the semimodule maps between the selection semimodules.
_⇒_ : Pos → Pos → Set
P ⇒ Q = SemiMod._⇒_ (𝒟 P) (𝒟 Q)

-- The equality, composition and additive structure are stated over the underlying semimodules, so
-- that implicit arguments are recovered from morphism types rather than through 𝒟.
infix 4 _≈p_

_≈p_ : ∀ {M N : Semimodule} → SemiMod._⇒_ M N → SemiMod._⇒_ M N → Prop 0ℓ
_≈p_ = SemiMod._≈m_

module SMC = Category SemiMod.cat

≈p-refl : ∀ {M N} {f : SemiMod._⇒_ M N} → f ≈p f
≈p-refl {M} {N} {f} = SMC.≈-refl {M} {N} {f}

≈p-sym : ∀ {M N} {f g : SemiMod._⇒_ M N} → f ≈p g → g ≈p f
≈p-sym {M} {N} = SMC.≈-sym {M} {N}

≈p-trans : ∀ {M N} {f g h : SemiMod._⇒_ M N} → f ≈p g → g ≈p h → f ≈p h
≈p-trans {M} {N} = SMC.≈-trans {M} {N}

id : (P : Pos) → P ⇒ P
id P = SemiMod.id (𝒟 P)

_∘_ : ∀ {M N O : Semimodule} → SemiMod._⇒_ N O → SemiMod._⇒_ M N → SemiMod._⇒_ M O
_∘_ = SemiMod._∘_

infixl 21 _∘_

∘p-cong : ∀ {M N O} {f₁ f₂ : SemiMod._⇒_ N O} {g₁ g₂ : SemiMod._⇒_ M N} →
          f₁ ≈p f₂ → g₁ ≈p g₂ → (f₁ ∘ g₁) ≈p (f₂ ∘ g₂)
∘p-cong = SMC.∘-cong

cat : Category 0ℓ 0ℓ 0ℓ
cat .Category.obj = Pos
cat .Category._⇒_ = _⇒_
cat .Category._≈_ = _≈p_
cat .Category.isEquiv {P} {Q} = Category.isEquiv SemiMod.cat {𝒟 P} {𝒟 Q}
cat .Category.id = id
cat .Category._∘_ = _∘_
cat .Category.∘-cong = Category.∘-cong SemiMod.cat
cat .Category.id-left {P} {Q} {f} = Category.id-left SemiMod.cat {𝒟 P} {𝒟 Q} {f}
cat .Category.id-right {P} {Q} {f} = Category.id-right SemiMod.cat {𝒟 P} {𝒟 Q} {f}
cat .Category.assoc f g h = Category.assoc SemiMod.cat f g h

-- The CMon enrichment is inherited pointwise.
εp : ∀ {P Q} → P ⇒ Q
εp {P} {Q} = SemiMod.ε-map (𝒟 P) (𝒟 Q)

_+p_ : ∀ {M N : Semimodule} → SemiMod._⇒_ M N → SemiMod._⇒_ M N → SemiMod._⇒_ M N
_+p_ {M} {N} = SemiMod.+-map M N

infixl 21 _+p_

+p-cong : ∀ {M N} {f₁ f₂ g₁ g₂ : SemiMod._⇒_ M N} →
          f₁ ≈p f₂ → g₁ ≈p g₂ → (f₁ +p g₁) ≈p (f₂ +p g₂)
+p-cong {M} {N} =
  CommutativeMonoid.+-cong (CMonEnriched.homCM SemiMod.cmon-enriched M N)

+p-lunit : ∀ {M N} {f : SemiMod._⇒_ M N} → (SemiMod.ε-map M N +p f) ≈p f
+p-lunit {M} {N} {f} =
  CommutativeMonoid.+-lunit (CMonEnriched.homCM SemiMod.cmon-enriched M N) {f}

+p-runit : ∀ {M N} {f : SemiMod._⇒_ M N} → (f +p SemiMod.ε-map M N) ≈p f
+p-runit {M} {N} {f} =
  ≈p-trans
    (CommutativeMonoid.+-comm (CMonEnriched.homCM SemiMod.cmon-enriched M N)
      {f} {SemiMod.ε-map M N})
    (+p-lunit {M} {N} {f})

private
  homCM𝒟 : ∀ P Q → CommutativeMonoid (Category.hom-setoid SemiMod.cat (𝒟 P) (𝒟 Q))
  homCM𝒟 P Q = CMonEnriched.homCM SemiMod.cmon-enriched (𝒟 P) (𝒟 Q)

cmon : CMonEnriched cat
cmon .CMonEnriched.homCM P Q .CommutativeMonoid.ε = εp
cmon .CMonEnriched.homCM P Q .CommutativeMonoid._+_ = _+p_
cmon .CMonEnriched.homCM P Q .CommutativeMonoid.+-cong = +p-cong
cmon .CMonEnriched.homCM P Q .CommutativeMonoid.+-lunit {f} =
  CommutativeMonoid.+-lunit (homCM𝒟 P Q) {f}
cmon .CMonEnriched.homCM P Q .CommutativeMonoid.+-assoc {f} {g} {h} =
  CommutativeMonoid.+-assoc (homCM𝒟 P Q) {f} {g} {h}
cmon .CMonEnriched.homCM P Q .CommutativeMonoid.+-comm {f} {g} =
  CommutativeMonoid.+-comm (homCM𝒟 P Q) {f} {g}
cmon .CMonEnriched.comp-bilinear₁ f₁ f₂ g = CMonEnriched.comp-bilinear₁ SemiMod.cmon-enriched f₁ f₂ g
cmon .CMonEnriched.comp-bilinear₂ f g₁ g₂ = CMonEnriched.comp-bilinear₂ SemiMod.cmon-enriched f g₁ g₂
cmon .CMonEnriched.comp-bilinear-ε₁ f = CMonEnriched.comp-bilinear-ε₁ SemiMod.cmon-enriched f
cmon .CMonEnriched.comp-bilinear-ε₂ f = CMonEnriched.comp-bilinear-ε₂ SemiMod.cmon-enriched f

-- A presented morphism acts by matrix application, which fixedness survives since the matrix is
-- absorbed on the left.
mat→mor : ∀ {P Q} → P ⇒ₘ Q → P ⇒ Q
mat→mor {P} {Q} f .*→* ._⇒s_.func (v ,ₚ fx) =
  app (f .mat) v ,ₚ
  (λ i → trans (sym (app-∘ (Q .ord) (f .mat) v i)) (app-congₘ (absorb-left f) v i))
mat→mor {P} {Q} f .*→* ._⇒s_.func-resp-≈ {u ,ₚ _} {v ,ₚ _} e i =
  Σ-cong {P .dim} (λ j → ·-cong refl (e j))
mat→mor {P} {Q} f .preserve-ze i = app-ε (f .mat) i
mat→mor {P} {Q} f .preserve-+ {u ,ₚ _} {v ,ₚ _} i = app-+ (f .mat) u v i
mat→mor {P} {Q} f .preserve-· {s} {u ,ₚ _} i = app-· (f .mat) s u i

-- The action respects the calculus of matrices: equal presentations act equally, the order acts as
-- the identity, matrix product as composition, the zero matrix as the zero morphism and matrix sum
-- as morphism sum.
mat→mor-congₘ : ∀ {P Q} {f g : P ⇒ₘ Q} → f .mat ≈ₘ g .mat → mat→mor f ≈p mat→mor g
mat→mor-congₘ {P} {Q} h .*≈* ._≃s_.func-eq {v₁ ,ₚ _} {v₂ ,ₚ _} e i =
  Σ-cong {P .dim} (λ j → ·-cong (h i j) (e j))

mat→mor-id : ∀ {P} {f : P ⇒ₘ P} → f .mat ≈ₘ P .ord → mat→mor f ≈p id P
mat→mor-id {P} {f} h .*≈* ._≃s_.func-eq {v₁ ,ₚ fx₁} {v₂ ,ₚ _} e i =
  trans (Σ-cong {P .dim} (λ j → ·-cong (h i j) refl)) (trans (fx₁ i) (e i))

mat→mor-comp : ∀ {P Q R} (g : Q ⇒ₘ R) (f : P ⇒ₘ Q) {gf : P ⇒ₘ R} →
               gf .mat ≈ₘ (g .mat ∘ₘ f .mat) →
               mat→mor gf ≈p (mat→mor g ∘ mat→mor f)
mat→mor-comp {P} {Q} {R} g f {gf} h .*≈* ._≃s_.func-eq {v₁ ,ₚ _} {v₂ ,ₚ _} e i =
  trans (app-congₘ h v₁ i)
  (trans (app-∘ (g .mat) (f .mat) v₁ i)
         (Σ-cong {Q .dim} (λ j → ·-cong refl (Σ-cong {P .dim} (λ k → ·-cong refl (e k))))))

mat→mor-εₘ : ∀ {P Q} {f : P ⇒ₘ Q} → f .mat ≈ₘ εₘ → mat→mor f ≈p εp {P} {Q}
mat→mor-εₘ {P} {Q} h .*≈* ._≃s_.func-eq {v₁ ,ₚ _} {v₂ ,ₚ _} e i =
  trans (app-congₘ h v₁ i) (trans (Σ-cong {P .dim} (λ j → ε-annihilₗ)) (Σ-ε {P .dim}))

mat→mor-+ₘ : ∀ {P Q} {h f g : P ⇒ₘ Q} → h .mat ≈ₘ (f .mat +ₘ g .mat) →
             mat→mor h ≈p (mat→mor f +p mat→mor g)
mat→mor-+ₘ {P} {Q} {h} {f} {g} hyp .*≈* ._≃s_.func-eq {v₁ ,ₚ _} {v₂ ,ₚ _} e i =
  trans (app-congₘ hyp v₁ i)
  (trans (app-+ₘ (f .mat) (g .mat) v₁ i)
         (+-cong (Σ-cong {P .dim} (λ j → ·-cong refl (e j)))
                 (Σ-cong {P .dim} (λ j → ·-cong refl (e j)))))

-- Every morphism is presented: its matrix is read off on the closed basis columns, since every
-- selection is the finite sum of its scaled closed columns and morphisms preserve finite sums.
private
  msum : ∀ (P : Pos) {n} → (Fin n → ∃ₛ (Vec (P .dim)) (Fixed P)) → ∃ₛ (Vec (P .dim)) (Fixed P)
  msum P {zero}  f = 𝒟 P .Semimodule.additive .CommutativeMonoid.ε
  msum P {suc n} f =
    𝒟 P .Semimodule.additive .CommutativeMonoid._+_ (f zero) (msum P (λ i → f (suc i)))

  msum-vec : ∀ (P : Pos) {n} (f : Fin n → ∃ₛ (Vec (P .dim)) (Fixed P)) (q : Fin (P .dim)) →
             vec P (msum P f) q ≈ Σ {n} (λ p → vec P (f p) q)
  msum-vec P {zero}  f q = refl
  msum-vec P {suc n} f q = +-cong refl (msum-vec P (λ i → f (suc i)) q)

  mor-msum : ∀ {P Q} (h : P ⇒ Q) {n} (f : Fin n → ∃ₛ (Vec (P .dim)) (Fixed P)) (q : Fin (Q .dim)) →
             vec Q (h .func (msum P f)) q ≈ vec Q (msum Q (λ i → h .func (f i))) q
  mor-msum {P} {Q} h {zero}  f q = h .preserve-ze q
  mor-msum {P} {Q} h {suc n} f q =
    trans (h .preserve-+ q) (+-cong refl (mor-msum h (λ i → f (suc i)) q))

  -- A selection is the sum of its scaled closed columns, and so is each closed column against the
  -- order, which is what absorption of the recovered matrix needs.
  decomp : ∀ (P : Pos) (v : Vec (P .dim)) (fx : Fixed P v) (q : Fin (P .dim)) →
           v q ≈ vec P (msum P (λ p → Semimodule._·_ (𝒟 P) (v p) (colv P p))) q
  decomp P v fx q =
    trans (sym (fx q))
    (trans (Σ-cong {P .dim} (λ p → ·-comm))
           (sym (msum-vec P (λ p → Semimodule._·_ (𝒟 P) (v p) (colv P p)) q)))

  decomp-col : ∀ (P : Pos) (p : Fin (P .dim)) (q : Fin (P .dim)) →
               P .ord q p ≈ vec P (msum P (λ j → Semimodule._·_ (𝒟 P) (P .ord j p) (colv P j))) q
  decomp-col P p q =
    trans (sym (ord-idem P q p))
    (trans (Σ-cong {P .dim} (λ j → ·-comm))
           (sym (msum-vec P (λ j → Semimodule._·_ (𝒟 P) (P .ord j p) (colv P j)) q)))

mor→mat : ∀ {P Q} → P ⇒ Q → P ⇒ₘ Q
mor→mat {P} {Q} h .mat q p = vec Q (h .func (colv P p)) q
mor→mat {P} {Q} h .absorbed =
  ≈ₘ-trans (∘-cong left (≈ₘ-refl {M = P .ord})) right
  where
  left : (Q .ord ∘ₘ (λ q p → vec Q (h .func (colv P p)) q))
         ≈ₘ (λ q p → vec Q (h .func (colv P p)) q)
  left q p = fxd Q (h .func (colv P p)) q

  right : ((λ q p → vec Q (h .func (colv P p)) q) ∘ₘ P .ord)
          ≈ₘ (λ q p → vec Q (h .func (colv P p)) q)
  right q p =
    sym
      (trans (h .func-resp-≈ (decomp-col P p) q)
      (trans (mor-msum h (λ j → Semimodule._·_ (𝒟 P) (P .ord j p) (colv P j)) q)
      (trans (msum-vec Q (λ j → h .func (Semimodule._·_ (𝒟 P) (P .ord j p) (colv P j))) q)
      (trans (Σ-cong {P .dim} (λ j → h .preserve-· {P .ord j p} {colv P j} q))
             (Σ-cong {P .dim} (λ j → ·-comm))))))

mat→mor-full : ∀ {P Q} (h : P ⇒ Q) → mat→mor (mor→mat h) ≈p h
mat→mor-full {P} {Q} h .*≈* ._≃s_.func-eq {v₁ ,ₚ fx₁} {v₂ ,ₚ _} e q =
  trans (Σ-cong {P .dim} (λ p → ·-comm))
  (trans (Σ-cong {P .dim} (λ p → sym (h .preserve-· {v₁ p} {colv P p} q)))
  (trans (sym (msum-vec Q (λ p → h .func (Semimodule._·_ (𝒟 P) (v₁ p) (colv P p))) q))
  (trans (sym (mor-msum h (λ p → Semimodule._·_ (𝒟 P) (v₁ p) (colv P p)) q))
         (h .func-resp-≈ (λ q' → trans (sym (decomp P v₁ fx₁ q')) (e q')) q))))

-- Reading the matrix back off a presented morphism recovers the presentation, so presentations and
-- morphisms are in bijection.
mor→mat-mat : ∀ {P Q} (f : P ⇒ₘ Q) → mor→mat (mat→mor f) .mat ≈ₘ f .mat
mor→mat-mat f q p = absorb-right f q p

mat→mor-faithful : ∀ {P Q} {f g : P ⇒ₘ Q} → mat→mor f ≈p mat→mor g → f .mat ≈ₘ g .mat
mat→mor-faithful {P} {Q} {f} {g} h q p =
  trans (sym (absorb-right f q p))
  (trans (h .func-eq {colv P p} {colv P p} (λ i → refl) q)
         (absorb-right g q p))

mor→mat-cong : ∀ {P Q} {h k : P ⇒ Q} → h ≈p k → mor→mat h .mat ≈ₘ mor→mat k .mat
mor→mat-cong e q p = e .func-eq (λ i → refl) q

mor→mat-comp : ∀ {P Q R} (g : Q ⇒ R) (f : P ⇒ Q) →
               mor→mat (g ∘ f) .mat ≈ₘ (mor→mat g .mat ∘ₘ mor→mat f .mat)
mor→mat-comp {P} {Q} {R} g f =
  mat→mor-faithful
    (≈p-trans (mat→mor-full (g ∘ f))
    (≈p-trans (SMC.∘-cong (≈p-sym (mat→mor-full g)) (≈p-sym (mat→mor-full f)))
              (≈p-sym (mat→mor-comp (mor→mat g) (mor→mat f)
                        {compₘ (mor→mat g) (mor→mat f)} ≈ₘ-refl))))

-- No morphism increases the support, read off through its presentation.
mor-supp : ∀ {P Q} (h : P ⇒ Q) (x : ∃ₛ (Vec (P .dim)) (Fixed P)) →
           supp {Q .dim} (vec Q (h .func x)) L.≤ supp {P .dim} (vec P x)
mor-supp {P} {Q} h (v ,ₚ fx) =
  ≤-trans
    (L.≈→≤ (Σ-cong {Q .dim}
      (λ q → sym (mat→mor-full h .func-eq {v ,ₚ fx} {v ,ₚ fx} (λ i → refl) q))))
    (supp-mono (mor→mat h .mat) v)

-- The opposite order: same diagonal, composite bound by commuting the factors.
op : Pos → Pos
op P .dim = P .dim
op P .ord = P .ord ᵀ
op P .ord-refl = P .ord-refl
op P .ord-trans i j k = ≤-trans (L.≈→≤ ·-comm) (P .ord-trans k j i)

-- An absorbed matrix transposes to a matrix absorbed by the opposite orders, so conjugation pairs
-- each object with its opposite; on morphisms it acts through the presentation.
_ᵀₘ : ∀ {P Q} → P ⇒ₘ Q → op Q ⇒ₘ op P
_ᵀₘ {P} {Q} f .mat = f .mat ᵀ
_ᵀₘ {P} {Q} f .absorbed =
  ≈ₘ-trans (∘-cong (≈ₘ-sym (∘-ᵀ (f .mat) (P .ord))) (≈ₘ-refl {M = Q .ord ᵀ}))
  (≈ₘ-trans (≈ₘ-sym (∘-ᵀ (Q .ord) (f .mat ∘ₘ P .ord)))
            (ᵀ-cong (≈ₘ-trans (≈ₘ-sym (assoc (Q .ord) (f .mat) (P .ord))) (f .absorbed))))

_ᵀp : ∀ {P Q} → P ⇒ Q → op Q ⇒ op P
_ᵀp h = mat→mor ((mor→mat h) ᵀₘ)

ᵀp-involutive : ∀ {P Q} (f : P ⇒ Q) → (_ᵀp {op Q} {op P} (f ᵀp)) ≈p f
ᵀp-involutive {P} {Q} f =
  ≈p-trans
    (mat→mor-congₘ {f = (mor→mat (f ᵀp)) ᵀₘ} {g = mor→mat f}
      (λ q p → mor→mat-mat ((mor→mat f) ᵀₘ) p q))
    (mat→mor-full f)

ᵀp-id : ∀ (P : Pos) → (id P ᵀp) ≈p id (op P)
ᵀp-id P = mat→mor-id (λ q p → refl)

ᵀp-∘ : ∀ {P Q R} (g : Q ⇒ R) (f : P ⇒ Q) → ((g ∘ f) ᵀp) ≈p ((f ᵀp) ∘ (g ᵀp))
ᵀp-∘ {P} {Q} {R} g f =
  mat→mor-comp ((mor→mat f) ᵀₘ) ((mor→mat g) ᵀₘ) {(mor→mat (g ∘ f)) ᵀₘ}
    (λ q p → trans (mor→mat-comp g f p q) (∘-ᵀ (mor→mat g .mat) (mor→mat f .mat) q p))

ᵀp-+ : ∀ {P Q} (f g : P ⇒ Q) → ((f +p g) ᵀp) ≈p ((f ᵀp) +p (g ᵀp))
ᵀp-+ {P} {Q} f g =
  mat→mor-+ₘ {h = (mor→mat (f +p g)) ᵀₘ} {f = (mor→mat f) ᵀₘ} {g = (mor→mat g) ᵀₘ}
    (λ q p → refl)

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

-- Projections and injections, presented by the block matrices corrected by the block orders.
π₁ₘ : ∀ (P Q : Pos) → (P ⊕ Q) ⇒ₘ P
π₁ₘ P Q .mat = P .ord ∘ₘ (p₁ {P .dim} {Q .dim})
π₁ₘ P Q .absorbed =
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

π₂ₘ : ∀ (P Q : Pos) → (P ⊕ Q) ⇒ₘ Q
π₂ₘ P Q .mat = Q .ord ∘ₘ (p₂ {P .dim} {Q .dim})
π₂ₘ P Q .absorbed =
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

ι₁ₘ : ∀ (P Q : Pos) → P ⇒ₘ (P ⊕ Q)
ι₁ₘ P Q .mat = (in₁ {P .dim} {Q .dim}) ∘ₘ P .ord
ι₁ₘ P Q .absorbed =
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

ι₂ₘ : ∀ (P Q : Pos) → Q ⇒ₘ (P ⊕ Q)
ι₂ₘ P Q .mat = (in₂ {P .dim} {Q .dim}) ∘ₘ Q .ord
ι₂ₘ P Q .absorbed =
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

π₁ : ∀ (P Q : Pos) → (P ⊕ Q) ⇒ P
π₁ P Q = mat→mor (π₁ₘ P Q)

π₂ : ∀ (P Q : Pos) → (P ⊕ Q) ⇒ Q
π₂ P Q = mat→mor (π₂ₘ P Q)

ι₁ : ∀ (P Q : Pos) → P ⇒ (P ⊕ Q)
ι₁ P Q = mat→mor (ι₁ₘ P Q)

ι₂ : ∀ (P Q : Pos) → Q ⇒ (P ⊕ Q)
ι₂ P Q = mat→mor (ι₂ₘ P Q)

-- The five biproduct laws hold on the presenting matrices, with the order matrices as the
-- identities, and transport along the action.
private
  id-1ₘ : ∀ (P Q : Pos) → (π₁ₘ P Q .mat ∘ₘ ι₁ₘ P Q .mat) ≈ₘ P .ord
  id-1ₘ P Q =
    ≈ₘ-trans (assoc (P .ord) (p₁ {P .dim} {Q .dim}) ((in₁ {P .dim} {Q .dim}) ∘ₘ P .ord))
    (≈ₘ-trans (∘-cong (≈ₘ-refl {M = P .ord}) (≈ₘ-sym (assoc (p₁ {P .dim} {Q .dim}) (in₁ {P .dim} {Q .dim}) (P .ord))))
    (≈ₘ-trans (∘-cong (≈ₘ-refl {M = P .ord}) (∘-cong (id-1 (P .dim) (Q .dim)) (≈ₘ-refl {M = P .ord})))
    (≈ₘ-trans (∘-cong (≈ₘ-refl {M = P .ord}) (id-left {M = P .ord}))
              (ord-idem P))))

  id-2ₘ : ∀ (P Q : Pos) → (π₂ₘ P Q .mat ∘ₘ ι₂ₘ P Q .mat) ≈ₘ Q .ord
  id-2ₘ P Q =
    ≈ₘ-trans (assoc (Q .ord) (p₂ {P .dim} {Q .dim}) ((in₂ {P .dim} {Q .dim}) ∘ₘ Q .ord))
    (≈ₘ-trans (∘-cong (≈ₘ-refl {M = Q .ord}) (≈ₘ-sym (assoc (p₂ {P .dim} {Q .dim}) (in₂ {P .dim} {Q .dim}) (Q .ord))))
    (≈ₘ-trans (∘-cong (≈ₘ-refl {M = Q .ord}) (∘-cong (id-2 (P .dim) (Q .dim)) (≈ₘ-refl {M = Q .ord})))
    (≈ₘ-trans (∘-cong (≈ₘ-refl {M = Q .ord}) (id-left {M = Q .ord}))
              (ord-idem Q))))

  zero-1ₘ : ∀ (P Q : Pos) → (π₁ₘ P Q .mat ∘ₘ ι₂ₘ P Q .mat) ≈ₘ εₘ
  zero-1ₘ P Q =
    ≈ₘ-trans (assoc (P .ord) (p₁ {P .dim} {Q .dim}) ((in₂ {P .dim} {Q .dim}) ∘ₘ Q .ord))
    (≈ₘ-trans (∘-cong (≈ₘ-refl {M = P .ord}) (≈ₘ-sym (assoc (p₁ {P .dim} {Q .dim}) (in₂ {P .dim} {Q .dim}) (Q .ord))))
    (≈ₘ-trans (∘-cong (≈ₘ-refl {M = P .ord}) (∘-cong (zero-1 (P .dim) (Q .dim)) (≈ₘ-refl {M = Q .ord})))
    (≈ₘ-trans (∘-cong (≈ₘ-refl {M = P .ord}) (comp-bilinear-ε₁ (Q .ord)))
              (comp-bilinear-ε₂ (P .ord)))))

  zero-2ₘ : ∀ (P Q : Pos) → (π₂ₘ P Q .mat ∘ₘ ι₁ₘ P Q .mat) ≈ₘ εₘ
  zero-2ₘ P Q =
    ≈ₘ-trans (assoc (Q .ord) (p₂ {P .dim} {Q .dim}) ((in₁ {P .dim} {Q .dim}) ∘ₘ P .ord))
    (≈ₘ-trans (∘-cong (≈ₘ-refl {M = Q .ord}) (≈ₘ-sym (assoc (p₂ {P .dim} {Q .dim}) (in₁ {P .dim} {Q .dim}) (P .ord))))
    (≈ₘ-trans (∘-cong (≈ₘ-refl {M = Q .ord}) (∘-cong (zero-2 (P .dim) (Q .dim)) (≈ₘ-refl {M = P .ord})))
    (≈ₘ-trans (∘-cong (≈ₘ-refl {M = Q .ord}) (comp-bilinear-ε₁ (P .ord)))
              (comp-bilinear-ε₂ (Q .ord)))))

  id-+ₘ : ∀ (P Q : Pos) →
          ((ι₁ₘ P Q .mat ∘ₘ π₁ₘ P Q .mat) +ₘ (ι₂ₘ P Q .mat ∘ₘ π₂ₘ P Q .mat)) ≈ₘ B P Q
  id-+ₘ P Q = +ₘ-cong first second
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

biproduct : ∀ (P Q : Pos) → Biproduct cmon P Q
biproduct P Q .Biproduct.prod = P ⊕ Q
biproduct P Q .Biproduct.p₁ = π₁ P Q
biproduct P Q .Biproduct.p₂ = π₂ P Q
biproduct P Q .Biproduct.in₁ = ι₁ P Q
biproduct P Q .Biproduct.in₂ = ι₂ P Q
biproduct P Q .Biproduct.id-1 =
  ≈p-trans (≈p-sym (mat→mor-comp (π₁ₘ P Q) (ι₁ₘ P Q) {ordₘ P} (≈ₘ-sym (id-1ₘ P Q))))
           (mat→mor-id ≈ₘ-refl)
biproduct P Q .Biproduct.id-2 =
  ≈p-trans (≈p-sym (mat→mor-comp (π₂ₘ P Q) (ι₂ₘ P Q) {ordₘ Q} (≈ₘ-sym (id-2ₘ P Q))))
           (mat→mor-id ≈ₘ-refl)
biproduct P Q .Biproduct.zero-1 =
  ≈p-trans (≈p-sym (mat→mor-comp (π₁ₘ P Q) (ι₂ₘ P Q) {compₘ (π₁ₘ P Q) (ι₂ₘ P Q)} ≈ₘ-refl))
           (mat→mor-εₘ (zero-1ₘ P Q))
biproduct P Q .Biproduct.zero-2 =
  ≈p-trans (≈p-sym (mat→mor-comp (π₂ₘ P Q) (ι₁ₘ P Q) {compₘ (π₂ₘ P Q) (ι₁ₘ P Q)} ≈ₘ-refl))
           (mat→mor-εₘ (zero-2ₘ P Q))
biproduct P Q .Biproduct.id-+ =
  ≈p-trans (+p-cong
             (≈p-sym (mat→mor-comp (ι₁ₘ P Q) (π₁ₘ P Q) {compₘ (ι₁ₘ P Q) (π₁ₘ P Q)} ≈ₘ-refl))
             (≈p-sym (mat→mor-comp (ι₂ₘ P Q) (π₂ₘ P Q) {compₘ (ι₂ₘ P Q) (π₂ₘ P Q)} ≈ₘ-refl)))
  (≈p-trans (≈p-sym (mat→mor-+ₘ {h = ordₘ (P ⊕ Q)}
                      {f = compₘ (ι₁ₘ P Q) (π₁ₘ P Q)} {g = compₘ (ι₂ₘ P Q) (π₂ₘ P Q)}
                      (≈ₘ-sym (id-+ₘ P Q))))
            (mat→mor-id ≈ₘ-refl))

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
disc-⊕ m n = iso
  where
  fwdₘ : (disc m ⊕ disc n) ⇒ₘ disc (m +ℕ n)
  fwdₘ .mat = I
  fwdₘ .absorbed =
    ≈ₘ-trans (∘-cong (id-left {M = I}) (≈ₘ-refl {M = B (disc m) (disc n)}))
             (≈ₘ-trans (id-left {M = B (disc m) (disc n)}) (B-disc m n))

  bwdₘ : disc (m +ℕ n) ⇒ₘ (disc m ⊕ disc n)
  bwdₘ .mat = I
  bwdₘ .absorbed =
    ≈ₘ-trans (id-right {M = B (disc m) (disc n) ∘ₘ I})
             (≈ₘ-trans (id-right {M = B (disc m) (disc n)}) (B-disc m n))

  iso : Category.Iso cat (disc m ⊕ disc n) (disc (m +ℕ n))
  iso .Category.Iso.fwd = mat→mor fwdₘ
  iso .Category.Iso.bwd = mat→mor bwdₘ
  iso .Category.Iso.fwd∘bwd≈id =
    ≈p-trans (≈p-sym (mat→mor-comp fwdₘ bwdₘ {ordₘ (disc (m +ℕ n))} (≈ₘ-sym (id-left {M = I}))))
             (mat→mor-id ≈ₘ-refl)
  iso .Category.Iso.bwd∘fwd≈id =
    ≈p-trans (≈p-sym (mat→mor-comp bwdₘ fwdₘ {ordₘ (disc m ⊕ disc n)}
                       (≈ₘ-trans (B-disc m n) (≈ₘ-sym (id-left {M = I})))))
             (mat→mor-id ≈ₘ-refl)

-- The empty position order is terminal: its only selection is the empty vector.
𝟘p : Pos
𝟘p = disc 0

terminal : HasTerminal cat
terminal .HasTerminal.witness = 𝟘p
terminal .HasTerminal.is-terminal .IsTerminal.to-terminal .*→* ._⇒s_.func _ = (λ ()) ,ₚ (λ ())
terminal .HasTerminal.is-terminal .IsTerminal.to-terminal .*→* ._⇒s_.func-resp-≈ _ ()
terminal .HasTerminal.is-terminal .IsTerminal.to-terminal .preserve-ze ()
terminal .HasTerminal.is-terminal .IsTerminal.to-terminal .preserve-+ ()
terminal .HasTerminal.is-terminal .IsTerminal.to-terminal .preserve-· ()
terminal .HasTerminal.is-terminal .IsTerminal.to-terminal-ext f .*≈* ._≃s_.func-eq _ ()

-- Lifting: a new root position, an ancestor of every position, so a new global bottom in the
-- order (cf. L on join semilattices, whose downsets it mirrors: a down-closed selection of the
-- lifted order is empty or the root plus a down-closed selection). A constructor cell is the
-- lifting of the biproduct of its arguments' orders.
Lp : Pos → Pos
Lp P .dim = suc (P .dim)
Lp P .ord zero    p       = ι
Lp P .ord (suc q) zero    = ε
Lp P .ord (suc q) (suc p) = P .ord q p
Lp P .ord-refl zero    = ≤-refl
Lp P .ord-refl (suc i) = P .ord-refl i
Lp P .ord-trans zero    j k = IsTop.≤-top L.⊤-isTop
Lp P .ord-trans (suc i) zero k =
  ≤-trans (L.≈→≤ ε-annihilₗ) (IsBottom.≤-bottom L.⊥-isBottom)
Lp P .ord-trans (suc i) (suc j) zero = L.≈→≤ ε-annihilᵣ
Lp P .ord-trans (suc i) (suc j) (suc k) = P .ord-trans i j k

head : ∀ {n} → Vec (suc n) → Setoid.Carrier A
head v = v zero

tail : ∀ {n} → Vec (suc n) → Vec n
tail v i = v (suc i)

private
  cons : ∀ {n} → Setoid.Carrier A → Vec n → Vec (suc n)
  cons a u zero    = a
  cons a u (suc i) = u i

-- Acting by a lifted order: the root entry gains the tail's support, and the tail is acted on by
-- the order itself.
Lp-app-root : ∀ (P : Pos) (v : Vec (suc (P .dim))) →
              app (Lp P .ord) v zero ≈ (head v + supp {P .dim} (tail v))
Lp-app-root P v = +-cong ·-lunit (Σ-cong {P .dim} (λ i → ·-lunit))

Lp-app-tail : ∀ (P : Pos) (v : Vec (suc (P .dim))) (i : Fin (P .dim)) →
              app (Lp P .ord) v (suc i) ≈ app (P .ord) (tail v) i
Lp-app-tail P v i = trans (+-cong ε-annihilₗ refl) +-lunit

-- So the selections of a lifted order are exactly the pairs of a root entry and a selection whose
-- support the root entry dominates.
Lp-fixed-tail : ∀ (P : Pos) (v : Vec (suc (P .dim))) → Fixed (Lp P) v → Fixed P (tail v)
Lp-fixed-tail P v h i = trans (sym (Lp-app-tail P v i)) (h (suc i))

Lp-fixed-root : ∀ (P : Pos) (v : Vec (suc (P .dim))) →
                Fixed (Lp P) v → supp {P .dim} (tail v) L.≤ head v
Lp-fixed-root P v h = trans +-comm (trans (sym (Lp-app-root P v)) (h zero))

Lp-fixed : ∀ (P : Pos) (v : Vec (suc (P .dim))) →
           Fixed P (tail v) → supp {P .dim} (tail v) L.≤ head v → Fixed (Lp P) v
Lp-fixed P v ht hr zero    = trans (Lp-app-root P v) (trans +-comm hr)
Lp-fixed P v ht hr (suc i) = trans (Lp-app-tail P v i) (ht i)

-- The support of a lifted selection is its root entry, since the root dominates the tail.
Lp-supp : ∀ (P : Pos) (v : Vec (suc (P .dim))) →
          Fixed (Lp P) v → supp {suc (P .dim)} v ≈ head v
Lp-supp P v h = trans +-comm (Lp-fixed-root P v h)

-- The action on morphisms keeps the root and maps the tail; the root still dominates because no
-- morphism increases the support.
Lp-map : ∀ {P Q} → P ⇒ Q → Lp P ⇒ Lp Q
Lp-map {P} {Q} h .*→* ._⇒s_.func (v ,ₚ fx) =
  cons (head v) (vec Q (h .func (tail v ,ₚ Lp-fixed-tail P v fx))) ,ₚ
  Lp-fixed Q _
    (fxd Q (h .func (tail v ,ₚ Lp-fixed-tail P v fx)))
    (≤-trans (mor-supp h (tail v ,ₚ Lp-fixed-tail P v fx)) (Lp-fixed-root P v fx))
Lp-map {P} {Q} h .*→* ._⇒s_.func-resp-≈ {v₁ ,ₚ _} {v₂ ,ₚ _} e = λ where
  zero    → e zero
  (suc i) → h .func-resp-≈ (λ j → e (suc j)) i
Lp-map {P} {Q} h .preserve-ze = λ where
  zero    → refl
  (suc i) → h .preserve-ze i
Lp-map {P} {Q} h .preserve-+ {u ,ₚ _} {v ,ₚ _} = λ where
  zero    → refl
  (suc i) → h .preserve-+ i
Lp-map {P} {Q} h .preserve-· {s} {u ,ₚ _} = λ where
  zero    → refl
  (suc i) → h .preserve-· i

-- The lifting is functorial.
Lp-map-cong : ∀ {P Q} {f g : P ⇒ Q} → f ≈p g → Lp-map f ≈p Lp-map g
Lp-map-cong {P} {Q} {f} {g} h .*≈* ._≃s_.func-eq {v₁ ,ₚ _} {v₂ ,ₚ _} e = λ where
  zero    → e zero
  (suc i) → h .func-eq (λ j → e (suc j)) i

Lp-map-id : ∀ (P : Pos) → Lp-map (id P) ≈p id (Lp P)
Lp-map-id P .*≈* ._≃s_.func-eq {v₁ ,ₚ _} {v₂ ,ₚ _} e = λ where
  zero    → e zero
  (suc i) → e (suc i)

Lp-map-comp : ∀ {P Q R} (g : Q ⇒ R) (f : P ⇒ Q) →
                Lp-map (g ∘ f) ≈p (Lp-map g ∘ Lp-map f)
Lp-map-comp {P} {Q} {R} g f .*≈* ._≃s_.func-eq {v₁ ,ₚ _} {v₂ ,ₚ _} e = λ where
  zero    → e zero
  (suc i) → g .func-resp-≈ (f .func-resp-≈ (λ j → e (suc j))) i

-- The lifting packaged as an endofunctor: the cell structure for inductive types.
Lp-functor : Functor cat cat
Lp-functor .Functor.fobj = Lp
Lp-functor .Functor.fmor = Lp-map
Lp-functor .Functor.fmor-cong = Lp-map-cong
Lp-functor .Functor.fmor-id {P} = Lp-map-id P
Lp-functor .Functor.fmor-comp = Lp-map-comp
