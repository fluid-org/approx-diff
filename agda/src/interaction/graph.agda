{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.Bool using (Bool; true; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map; foldl; filterᵇ)
open import Data.List.Relation.Unary.All using (All; []; _∷_; universal) renaming (map to All-map)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_) renaming (map to AllPairs-map)
import Data.List.Relation.Unary.All.Properties as AllP
import Data.List.Relation.Unary.AllPairs.Properties as AllPairsP
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
import Data.List.Relation.Binary.Permutation.Propositional as ↭
open ↭ using (_↭_)
open import Data.Unit using (tt) renaming (⊤ to Unit)

open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; cong to ≡-cong; cong₂ to ≡-cong₂)
open import Relation.Nullary.Decidable using (yes)
import Data.Sum.Properties as SumP
open import basics using (IsStrictOrder)
import matrix
import two

-- A dependence graph as a value rather than a family indexed by a derivation: a graph is a set of
-- interior vertices with widths, a distinguished root of given width, and the dependence relation
-- between each pair. The root has no outgoing relation, so it is a sink by construction.
module interaction.graph where

private
  module M = matrix.Mat two.semiring

open two using (Two; O; I; _⊔_; ⊔-idem; ⊔-comm; ⊔-runit; ⊔-assoc)
open import categories using (Category)
open Category M.cat using (_∘_; _≈_; ∘-cong; ∘-cong₁; ∘-cong₂; assoc; id-left; id-right; ≈-refl; ≈-sym; ≈-trans)

data Input : Set where
  input : Input

-- The branching of a derivation, and the paths into it. A vertex names a premise and then either
-- descends into it or stops at its result, so the vertices of a rule are its premises' vertices
-- with each premise's result adjoined.
data Shape : Set where
  node : List Shape → Shape

data Root : Set where
  root : Root

mutual
  Vertex : Shape → Set
  Vertex (node ss) = Vertices ss

  Vertices : List Shape → Set
  Vertices []           = ⊥
  Vertices (s ∷ [])     = Vertex s ⊎ Root
  Vertices (s ∷ t ∷ ss) = (Vertex s ⊎ Root) ⊎ Vertices (t ∷ ss)

root-≟ : DecidableEquality Root
root-≟ root root = yes ≡-refl

mutual
  _≟_ : ∀ {s} → DecidableEquality (Vertex s)
  _≟_ {node ss} = _≟s_ {ss}

  _≟s_ : ∀ {ss} → DecidableEquality (Vertices ss)
  _≟s_ {s ∷ []}     = SumP.≡-dec (_≟_ {s}) root-≟
  _≟s_ {s ∷ t ∷ ss} = SumP.≡-dec (SumP.≡-dec (_≟_ {s}) root-≟) (_≟s_ {t ∷ ss})

-- The vertices of a shape, each premise's result first, then its interior, then the premises after
-- it. This fixes the order in which they are hidden.
mutual
  vertices : (s : Shape) → List (Vertex s)
  vertices (node ss) = vertices-of ss

  vertices-of : (ss : List Shape) → List (Vertices ss)
  vertices-of []           = []
  vertices-of (s ∷ [])     = inj₂ root ∷ map inj₁ (vertices s)
  vertices-of (s ∷ t ∷ ss) =
    map inj₁ (inj₂ root ∷ map inj₁ (vertices s)) ++ map inj₂ (vertices-of (t ∷ ss))

private
  sum-distinct : {A B : Set} {xs : List A} {ys : List B} →
                 AllPairs _≢_ xs → AllPairs _≢_ ys →
                 AllPairs _≢_ (map inj₁ xs ++ map inj₂ ys)
  sum-distinct {xs = xs} {ys = ys} dx dy =
    AllPairsP.++⁺ (AllPairsP.map⁺ (AllPairs-map (λ h e → h (SumP.inj₁-injective e)) dx))
                  (AllPairsP.map⁺ (AllPairs-map (λ h e → h (SumP.inj₂-injective e)) dy))
                  (AllP.map⁺ (universal (λ _ → AllP.map⁺ (universal (λ _ ()) ys)) xs))

mutual
  distinct : (s : Shape) → AllPairs _≢_ (vertices s)
  distinct (node ss) = distinct-of ss

  distinct-of : (ss : List Shape) → AllPairs _≢_ (vertices-of ss)
  distinct-of []           = []
  distinct-of (s ∷ [])     =
    AllP.map⁺ (universal (λ _ ()) (vertices s))
    ∷ AllPairsP.map⁺ (AllPairs-map (λ h e → h (SumP.inj₁-injective e)) (distinct s))
  distinct-of (s ∷ t ∷ ss) =
    sum-distinct (AllP.map⁺ (universal (λ _ ()) (vertices s))
                  ∷ AllPairsP.map⁺ (AllPairs-map (λ h e → h (SumP.inj₁-injective e)) (distinct s)))
                 (distinct-of (t ∷ ss))

-- The completion order: a premise's interior before its result, and every premise before those
-- after it. The shape is explicit, since it cannot be recovered from a vertex.
mutual
  lt : (s : Shape) → Vertex s → Vertex s → Set
  lt (node ss) = lts ss

  lts : (ss : List Shape) → Vertices ss → Vertices ss → Set
  lts (s ∷ [])     (inj₁ u)        (inj₁ v)        = lt s u v
  lts (s ∷ [])     (inj₁ _)        (inj₂ _)        = Unit
  lts (s ∷ [])     (inj₂ _)        _               = ⊥
  lts (s ∷ t ∷ ss) (inj₁ (inj₁ u)) (inj₁ (inj₁ v)) = lt s u v
  lts (s ∷ t ∷ ss) (inj₁ (inj₁ _)) (inj₁ (inj₂ _)) = Unit
  lts (s ∷ t ∷ ss) (inj₁ (inj₂ _)) (inj₁ _)        = ⊥
  lts (s ∷ t ∷ ss) (inj₁ _)        (inj₂ _)        = Unit
  lts (s ∷ t ∷ ss) (inj₂ _)        (inj₁ _)        = ⊥
  lts (s ∷ t ∷ ss) (inj₂ u)        (inj₂ v)        = lts (t ∷ ss) u v

mutual
  lt-trans : (s : Shape) (u v w : Vertex s) → lt s u v → lt s v w → lt s u w
  lt-trans (node ss) = lts-trans ss

  lts-trans : (ss : List Shape) (u v w : Vertices ss) → lts ss u v → lts ss v w → lts ss u w
  lts-trans (s ∷ [])     (inj₁ u)        (inj₁ v)        (inj₁ w)        a b = lt-trans s u v w a b
  lts-trans (s ∷ [])     (inj₁ u)        (inj₁ v)        (inj₂ _)        a b = tt
  lts-trans (s ∷ [])     (inj₁ u)        (inj₂ _)        w               a ()
  lts-trans (s ∷ [])     (inj₂ _)        v               w               () b
  lts-trans (s ∷ t ∷ ss) (inj₁ (inj₁ u)) (inj₁ (inj₁ v)) (inj₁ (inj₁ w)) a b = lt-trans s u v w a b
  lts-trans (s ∷ t ∷ ss) (inj₁ (inj₁ u)) (inj₁ (inj₁ v)) (inj₁ (inj₂ _)) a b = tt
  lts-trans (s ∷ t ∷ ss) (inj₁ (inj₁ u)) (inj₁ (inj₁ v)) (inj₂ _)        a b = tt
  lts-trans (s ∷ t ∷ ss) (inj₁ (inj₁ u)) (inj₁ (inj₂ _)) (inj₁ _)        a ()
  lts-trans (s ∷ t ∷ ss) (inj₁ (inj₁ u)) (inj₁ (inj₂ _)) (inj₂ _)        a b = tt
  lts-trans (s ∷ t ∷ ss) (inj₁ (inj₁ u)) (inj₂ _)        (inj₁ _)        a ()
  lts-trans (s ∷ t ∷ ss) (inj₁ (inj₁ u)) (inj₂ _)        (inj₂ _)        a b = tt
  lts-trans (s ∷ t ∷ ss) (inj₁ (inj₂ _)) (inj₁ _)        w               () b
  lts-trans (s ∷ t ∷ ss) (inj₁ (inj₂ _)) (inj₂ _)        (inj₁ _)        a ()
  lts-trans (s ∷ t ∷ ss) (inj₁ (inj₂ _)) (inj₂ _)        (inj₂ _)        a b = tt
  lts-trans (s ∷ t ∷ ss) (inj₂ _)        (inj₁ _)        w               () b
  lts-trans (s ∷ t ∷ ss) (inj₂ _)        (inj₂ _)        (inj₁ _)        a ()
  lts-trans (s ∷ t ∷ ss) (inj₂ u)        (inj₂ v)        (inj₂ w)        a b =
    lts-trans (t ∷ ss) u v w a b

mutual
  lt-asym : (s : Shape) (u v : Vertex s) → lt s u v → lt s v u → ⊥
  lt-asym (node ss) = lts-asym ss

  lts-asym : (ss : List Shape) (u v : Vertices ss) → lts ss u v → lts ss v u → ⊥
  lts-asym (s ∷ [])     (inj₁ u)        (inj₁ v)        a b = lt-asym s u v a b
  lts-asym (s ∷ [])     (inj₁ _)        (inj₂ _)        a ()
  lts-asym (s ∷ [])     (inj₂ _)        v               () b
  lts-asym (s ∷ t ∷ ss) (inj₁ (inj₁ u)) (inj₁ (inj₁ v)) a b = lt-asym s u v a b
  lts-asym (s ∷ t ∷ ss) (inj₁ (inj₁ _)) (inj₁ (inj₂ _)) a ()
  lts-asym (s ∷ t ∷ ss) (inj₁ (inj₁ _)) (inj₂ _)        a ()
  lts-asym (s ∷ t ∷ ss) (inj₁ (inj₂ _)) (inj₁ _)        () b
  lts-asym (s ∷ t ∷ ss) (inj₁ (inj₂ _)) (inj₂ _)        a ()
  lts-asym (s ∷ t ∷ ss) (inj₂ _)        (inj₁ _)        () b
  lts-asym (s ∷ t ∷ ss) (inj₂ u)        (inj₂ v)        a b = lts-asym (t ∷ ss) u v a b

lt-order : (s : Shape) → IsStrictOrder (lt s)
lt-order s .IsStrictOrder.trans = lt-trans s
lt-order s .IsStrictOrder.asym = lt-asym s

lts-order : (ss : List Shape) → IsStrictOrder (lts ss)
lts-order ss .IsStrictOrder.trans = lts-trans ss
lts-order ss .IsStrictOrder.asym = lts-asym ss


≈-of-≡ : ∀ {m n} {X Y : M.Matrix m n} → X ≡ Y → X ≈ Y
≈-of-≡ ≡-refl = ≈-refl

Void : Set
Void = ⊥

-- The completion order on a coproduct: every vertex of the first summand precedes every vertex of
-- the second.
sum-< : {A B : Set} → (A → A → Set) → (B → B → Set) → A ⊎ B → A ⊎ B → Set
sum-< R S (inj₁ p) (inj₁ q) = R p q
sum-< R S (inj₁ _) (inj₂ _) = Unit
sum-< R S (inj₂ _) (inj₁ _) = Void
sum-< R S (inj₂ p) (inj₂ q) = S p q

none-order : {A : Set} → IsStrictOrder {A = A} (λ _ _ → Void)
none-order .IsStrictOrder.trans _ _ _ ()
none-order .IsStrictOrder.asym _ _ ()

sum-<-order : {A B : Set} {R : A → A → Set} {S : B → B → Set} →
              IsStrictOrder R → IsStrictOrder S → IsStrictOrder (sum-< R S)
sum-<-order o₁ o₂ .IsStrictOrder.trans (inj₁ p) (inj₁ q) (inj₁ r) a b =
  o₁ .IsStrictOrder.trans p q r a b
sum-<-order o₁ o₂ .IsStrictOrder.trans (inj₁ p) (inj₁ q) (inj₂ r) a b = tt
sum-<-order o₁ o₂ .IsStrictOrder.trans (inj₁ p) (inj₂ q) (inj₁ r) a ()
sum-<-order o₁ o₂ .IsStrictOrder.trans (inj₁ p) (inj₂ q) (inj₂ r) a b = tt
sum-<-order o₁ o₂ .IsStrictOrder.trans (inj₂ p) (inj₁ q) r        () b
sum-<-order o₁ o₂ .IsStrictOrder.trans (inj₂ p) (inj₂ q) (inj₁ r) a ()
sum-<-order o₁ o₂ .IsStrictOrder.trans (inj₂ p) (inj₂ q) (inj₂ r) a b =
  o₂ .IsStrictOrder.trans p q r a b
sum-<-order o₁ o₂ .IsStrictOrder.asym (inj₁ p) (inj₁ q) a b = o₁ .IsStrictOrder.asym p q a b
sum-<-order o₁ o₂ .IsStrictOrder.asym (inj₁ p) (inj₂ q) a ()
sum-<-order o₁ o₂ .IsStrictOrder.asym (inj₂ p) (inj₁ q) () b
sum-<-order o₁ o₂ .IsStrictOrder.asym (inj₂ p) (inj₂ q) a b = o₂ .IsStrictOrder.asym p q a b

record Graph (m n : ℕ) : Set₁ where
  field
    shape   : Shape
    width   : Vertex shape → ℕ
    fo      : Vertex shape → Bool
    into    : (q : Vertex shape) → M.Matrix (width q) m
    inside  : (p q : Vertex shape) → M.Matrix (width q) (width p)
    -- Every entry between interior vertices runs strictly forward in the completion order. The
    -- inputs and the root need no condition, being below and above everything.
    <-inside : ∀ p q (k : Fin (width q)) (l : Fin (width p)) →
               inside p q k l ≡ two.I → lt shape p q
    fo-root : Bool
    out     : M.Matrix n m
    up      : (p : Vertex shape) → M.Matrix n (width p)

-- A dependence relation over an arbitrary vertex set: on pairs of a vertex and a position in the
-- value there. The inputs, the interior vertices and the root are not distinguished.
Relation : {V : Set} → (V → ℕ) → Set
Relation {V} vertex-width = (x y : V) → M.Matrix (vertex-width y) (vertex-width x)

hide : {V : Set} (vertex-width : V → ℕ) → Relation vertex-width → V → Relation vertex-width
hide vertex-width G r x y = G x y M.+ₘ (G r y ∘ G x r)

hide-all : {V : Set} (vertex-width : V → ℕ) → Relation vertex-width → List V → Relation vertex-width
hide-all vertex-width = foldl (hide vertex-width)

_≐_ : {V : Set} {vertex-width : V → ℕ} → Relation vertex-width → Relation vertex-width → Prop
_≐_ {V} G G' = ∀ x y → G x y ≈ G' x y

hide-cong : {V : Set} (vertex-width : V → ℕ) {G G' : Relation vertex-width} (r : V) →
            G ≐ G' → hide vertex-width G r ≐ hide vertex-width G' r
hide-cong vertex-width r e x y = M.+ₘ-cong (e x y) (∘-cong (e r y) (e x r))

hide-all-cong : {V : Set} (vertex-width : V → ℕ) {G G' : Relation vertex-width} (rs : List V) →
                G ≐ G' → hide-all vertex-width G rs ≐ hide-all vertex-width G' rs
hide-all-cong vertex-width []       e = e
hide-all-cong vertex-width (r ∷ rs) e = hide-all-cong vertex-width rs (hide-cong vertex-width r e)

-- Hiding a sink leaves every entry unchanged.
hide-sink : {V : Set} (vertex-width : V → ℕ) (G : Relation vertex-width) (r : V) →
            (∀ y → G r y ≈ M.εₘ) → hide vertex-width G r ≐ G
hide-sink vertex-width G r z x y = ≈-trans (M.+ₘ-cong ≈-refl (∘-cong₁ (z y))) (M.absorb₁ (G x y) (G x r))

hide-all-++ : {V : Set} (vertex-width : V → ℕ) (G : Relation vertex-width) (xs ys : List V) →
              hide-all vertex-width G (xs ++ ys) ≡ hide-all vertex-width (hide-all vertex-width G xs) ys
hide-all-++ vertex-width G []       ys = ≡-refl
hide-all-++ vertex-width G (x ∷ xs) ys = hide-all-++ vertex-width (hide vertex-width G x) xs ys

-- Entrywise laws for hiding a list of vertices on graphs that agree on the hidden rows and
-- columns. No rank or forwardness is assumed.
module Hide (V : Set) (w : V → ℕ) where
  Gr : Set
  Gr = Relation w

  h : Gr → V → Gr
  h = hide w

  _≈g_ : Gr → Gr → Set
  G ≈g G' = ∀ x y (i : Fin (w y)) (j : Fin (w x)) → G x y i j ≡ G' x y i j

  private
    ⊔-absorbˡ : ∀ a b → (a ⊔ (a ⊔ b)) ≡ (a ⊔ b)
    ⊔-absorbˡ O b = ≡-refl
    ⊔-absorbˡ I b = ≡-refl

    ⊔-absorbʳ : ∀ a b → (a ⊔ (b ⊔ a)) ≡ (b ⊔ a)
    ⊔-absorbʳ O b = ≡-refl
    ⊔-absorbʳ I O = ≡-refl
    ⊔-absorbʳ I I = ≡-refl

    absorb-mono : ∀ x y z → x ≡ (y ⊔ x) → (z ⊔ y) ≡ y → x ≡ (z ⊔ x)
    absorb-mono x y O p q = ≡-refl
    absorb-mono x O I p ()
    absorb-mono x I I p ≡-refl = p

    ⊔-shift : ∀ a s c → ((a ⊔ s) ⊔ c) ≡ ((a ⊔ c) ⊔ s)
    ⊔-shift O s c = ⊔-comm s c
    ⊔-shift I s c = ≡-refl

    ⊔-insert : ∀ a b c → (a ⊔ b) ≡ b → (b ⊔ c) ≡ (b ⊔ (a ⊔ c))
    ⊔-insert O b c q = ≡-refl
    ⊔-insert I O c ()
    ⊔-insert I I c ≡-refl = ≡-refl

  private
    Σ-O : ∀ {n} (f : Fin n → Two) → (∀ k → f k ≡ O) → M.Σ f ≡ O
    Σ-O {ℕ.zero}  f z = ≡-refl
    Σ-O {ℕ.suc n} f z =
      ≡-cong₂ _⊔_ (z Fin.zero) (Σ-O (λ k → f (Fin.suc k)) (λ k → z (Fin.suc k)))

    ⊓-O : ∀ x → (x two.⊓ O) ≡ O
    ⊓-O O = ≡-refl
    ⊓-O I = ≡-refl

  -- Zero rows and columns persist under hiding: every new entry into the row or column of r₀
  -- factors through an entry of that row or column.
  zero-fold : ∀ {G : Gr} rs r₀ →
              (((z : V) (i : Fin (w z)) (j : Fin (w r₀)) → G r₀ z i j ≡ O) ×
               ((z : V) (i : Fin (w r₀)) (j : Fin (w z)) → G z r₀ i j ≡ O)) →
              (((z : V) (i : Fin (w z)) (j : Fin (w r₀)) → foldl h G rs r₀ z i j ≡ O) ×
               ((z : V) (i : Fin (w r₀)) (j : Fin (w z)) → foldl h G rs z r₀ i j ≡ O))
  zero-fold []           r₀ zz        = zz
  zero-fold {G} (r ∷ rs) r₀ (zr , zc) = zero-fold {h G r} rs r₀ (zr' , zc')
    where
    zr' : (z : V) (i : Fin (w z)) (j : Fin (w r₀)) → h G r r₀ z i j ≡ O
    zr' z i j =
      ≡-cong₂ _⊔_ (zr z i j)
        (Σ-O (λ k → G r z i k two.⊓ G r₀ r k j)
             (λ k → ≡-trans (≡-cong (G r z i k two.⊓_) (zr r k j)) (⊓-O (G r z i k))))

    zc' : (z : V) (i : Fin (w r₀)) (j : Fin (w z)) → h G r z r₀ i j ≡ O
    zc' z i j =
      ≡-cong₂ _⊔_ (zc z i j)
        (Σ-O (λ k → G r r₀ i k two.⊓ G z r k j)
             (λ k → ≡-cong (two._⊓ G z r k j) (zc r i k)))

  -- Hiding only adds entries.
  increasing : ∀ {G : Gr} rs x y (i : Fin (w y)) (j : Fin (w x)) →
               foldl h G rs x y i j ≡ (G x y i j ⊔ foldl h G rs x y i j)
  increasing []           x y i j = ≡-sym ⊔-idem
  increasing {G} (r ∷ rs) x y i j =
    absorb-mono (foldl h (h G r) rs x y i j) (h G r x y i j) (G x y i j)
                (increasing rs x y i j)
                (⊔-absorbˡ (G x y i j) ((G r y ∘ G x r) i j))

  h-cong : ∀ {G G'} r → G ≈g G' → h G r ≈g h G' r
  h-cong r p x y i j =
    ≡-cong₂ _⊔_ (p x y i j) (M.Σ-cong-≡ (λ k → ≡-cong₂ two._⊓_ (p r y i k) (p x r k j)))

  fold-cong : ∀ {G G'} rs → G ≈g G' → foldl h G rs ≈g foldl h G' rs
  fold-cong []       p = p
  fold-cong (r ∷ rs) p = fold-cong rs (h-cong r p)

  -- A summand with no entries at the hidden vertices passes through hiding them: every new
  -- composite routes through a hidden row and column, which the summand lacks.
  add-inert : ∀ {G S : Gr} rs →
              All (λ r → ((z : V) (i : Fin (w z)) (j : Fin (w r)) → S r z i j ≡ O)
                       × ((z : V) (i : Fin (w r)) (j : Fin (w z)) → S z r i j ≡ O)) rs →
              ∀ x y (i : Fin (w y)) (j : Fin (w x)) →
              foldl h (λ x' y' → G x' y' M.+ₘ S x' y') rs x y i j ≡
              (foldl h G rs x y i j ⊔ S x y i j)
  add-inert []               []               x y i j = ≡-refl
  add-inert {G} {S} (r ∷ rs) ((zr , zc) ∷ zs) x y i j =
    ≡-trans (fold-cong rs step x y i j) (add-inert {h G r} {S} rs zs x y i j)
    where
    step : h (λ x' y' → G x' y' M.+ₘ S x' y') r ≈g (λ x' y' → h G r x' y' M.+ₘ S x' y')
    step x' y' i' j' =
      ≡-trans
        (≡-cong ((G x' y' i' j' ⊔ S x' y' i' j') ⊔_)
          (M.Σ-cong-≡ (λ k → ≡-cong₂ two._⊓_
            (≡-trans (≡-cong (G r y' i' k ⊔_) (zr y' i' k)) (⊔-runit {G r y' i' k}))
            (≡-trans (≡-cong (G x' r k j' ⊔_) (zc x' k j')) (⊔-runit {G x' r k j'})))))
        (⊔-shift (G x' y' i' j') (S x' y' i' j') ((G r y' ∘ G x' r) i' j'))

  -- Hiding vertices at which a larger graph agrees with a smaller one adds only its extra
  -- entries: every new composite routes through agreed rows and columns, so already arises in
  -- the smaller graph.
  agree-add : ∀ {G G' : Gr} rs →
              (∀ x y (i : Fin (w y)) (j : Fin (w x)) → (G x y i j ⊔ G' x y i j) ≡ G' x y i j) →
              All (λ r → ((z : V) (i : Fin (w z)) (j : Fin (w r)) → G' r z i j ≡ G r z i j)
                       × ((z : V) (i : Fin (w r)) (j : Fin (w z)) → G' z r i j ≡ G z r i j)) rs →
              ∀ x y (i : Fin (w y)) (j : Fin (w x)) →
              foldl h G' rs x y i j ≡ (G' x y i j ⊔ foldl h G rs x y i j)
  agree-add {G} {G'} []       sub _              x y i j =
    ≡-sym (≡-trans (⊔-comm (G' x y i j) (G x y i j)) (sub x y i j))
  agree-add {G} {G'} (r ∷ rs) sub ((ar , ac) ∷ as) x y i j =
    ≡-trans (agree-add {h G r} {h G' r} rs sub' all' x y i j)
    (≡-trans (≡-cong (_⊔ foldl h (h G r) rs x y i j) (step x y i j))
    (≡-trans (⊔-assoc (G' x y i j) (h G r x y i j) (foldl h (h G r) rs x y i j))
             (≡-cong (G' x y i j ⊔_) (≡-sym (increasing rs x y i j)))))
    where
    step : ∀ x' y' (i' : Fin (w y')) (j' : Fin (w x')) →
           h G' r x' y' i' j' ≡ (G' x' y' i' j' ⊔ h G r x' y' i' j')
    step x' y' i' j' =
      ≡-trans
        (≡-cong (G' x' y' i' j' ⊔_)
          (M.Σ-cong-≡ (λ k → ≡-cong₂ two._⊓_ (ar y' i' k) (ac x' k j'))))
        (⊔-insert (G x' y' i' j') (G' x' y' i' j') ((G r y' ∘ G x' r) i' j')
                  (sub x' y' i' j'))

    sub' : ∀ x' y' (i' : Fin (w y')) (j' : Fin (w x')) →
           (h G r x' y' i' j' ⊔ h G' r x' y' i' j') ≡ h G' r x' y' i' j'
    sub' x' y' i' j' =
      ≡-trans (≡-cong (h G r x' y' i' j' ⊔_) (step x' y' i' j'))
      (≡-trans (⊔-absorbʳ (h G r x' y' i' j') (G' x' y' i' j')) (≡-sym (step x' y' i' j')))

    all' : All (λ r' → ((z : V) (i' : Fin (w z)) (j' : Fin (w r')) →
                        h G' r r' z i' j' ≡ h G r r' z i' j')
                     × ((z : V) (i' : Fin (w r')) (j' : Fin (w z)) →
                        h G' r z r' i' j' ≡ h G r z r' i' j')) rs
    all' = All-map
      (λ {r'} (ar' , ac') →
        (λ z i' j' → ≡-trans (step r' z i' j')
                     (≡-trans (≡-cong (_⊔ h G r r' z i' j') (ar' z i' j'))
                              (⊔-absorbˡ (G r' z i' j') ((G r z ∘ G r' r) i' j')))) ,
        (λ z i' j' → ≡-trans (step z r' i' j')
                     (≡-trans (≡-cong (_⊔ h G r z r' i' j') (ac' z i' j'))
                              (⊔-absorbˡ (G z r' i' j') ((G r r' ∘ G z r) i' j')))))
      as

-- Witnesses for non-zero entries of sums and composites.
private
  Σ-I : ∀ {n} (f : Fin n → two.Two) → M.Σ f ≡ two.I → Σ (Fin n) (λ k → f k ≡ two.I)
  Σ-I {ℕ.suc n} f h with two.⊔-I (f Fin.zero) (M.Σ (λ k → f (Fin.suc k))) h
  ... | inj₁ e = Fin.zero , e
  ... | inj₂ e with Σ-I (λ k → f (Fin.suc k)) e
  ...   | (k , e') = Fin.suc k , e'

  ∘-I : ∀ {m n k} (A : M.Matrix m n) (B : M.Matrix n k) i l → (A ∘ B) i l ≡ two.I →
        Σ (Fin n) (λ j → (A i j ≡ two.I) × (B j l ≡ two.I))
  ∘-I A B i l h with Σ-I (λ j → A i j two.⊓ B j l) h
  ... | (j , e) with two.⊓-I (A i j) (B j l) e
  ...   | (e₁ , e₂) = j , (e₁ , e₂)

  Σ-I-at : ∀ {n} (f : Fin n → two.Two) (k : Fin n) → f k ≡ two.I → M.Σ f ≡ two.I
  Σ-I-at f Fin.zero    h = two.⊔-I-inl h
  Σ-I-at f (Fin.suc k) h = two.⊔-I-inr (f Fin.zero) (Σ-I-at (λ i → f (Fin.suc i)) k h)

  ∘-I-at : ∀ {m n k} (A : M.Matrix m n) (B : M.Matrix n k) i l j →
           A i j ≡ two.I → B j l ≡ two.I → (A ∘ B) i l ≡ two.I
  ∘-I-at A B i l j h₁ h₂ = Σ-I-at (λ j' → A i j' two.⊓ B j' l) j (two.⊓-I-pair h₁ h₂)

-- Consequences of the forward-edge property, over an abstract ordered vertex set. Hiding preserves
-- it, since a new entry composes entries through the hidden vertex; hiding two vertices commutes,
-- since an entry of one order decomposes into a term also present in the other, except the residual
-- routed through an entry in each direction between the two, which the order rules out; and hiding
-- a list is therefore independent of its order, adjacent swaps being commutation pushed through the
-- rest of the fold.
module Ordered {V : Set} (vertex-width : V → ℕ) (_<_ : V → V → Set) (o : IsStrictOrder _<_) where

  open IsStrictOrder o using (trans; asym)

  Fwd : Relation vertex-width → Set
  Fwd G = ∀ x y (i : Fin (vertex-width y)) (j : Fin (vertex-width x)) → G x y i j ≡ two.I → x < y

  private
    _≐e_ : Relation vertex-width → Relation vertex-width → Set
    G ≐e G' = ∀ x y (i : Fin (vertex-width y)) (j : Fin (vertex-width x)) → G x y i j ≡ G' x y i j

    fold-cong : ∀ {G G'} rs → G ≐e G' → hide-all vertex-width G rs ≐e hide-all vertex-width G' rs
    fold-cong []       e = e
    fold-cong (r ∷ rs) e =
      fold-cong rs (λ x y i j → ≡-cong₂ two._⊔_ (e x y i j)
                                 (M.Σ-cong-≡ (λ k → ≡-cong₂ two._⊓_ (e r y i k) (e x r k j))))

  fwd-hide : ∀ {G} r → Fwd G → Fwd (hide vertex-width G r)
  fwd-hide {G} r fwd x y i j e with two.⊔-I (G x y i j) ((G r y ∘ G x r) i j) e
  ... | inj₁ a = fwd x y i j a
  ... | inj₂ a with ∘-I (G r y) (G x r) i j a
  ...   | (k , (e₁ , e₂)) = trans x r y (fwd x r k j e₂) (fwd r y i k e₁)

  fwd-hide-all : ∀ {G} rs → Fwd G → Fwd (hide-all vertex-width G rs)
  fwd-hide-all []       fwd = fwd
  fwd-hide-all (r ∷ rs) fwd = fwd-hide-all rs (fwd-hide r fwd)

  private
    into : ∀ {G} → Fwd G → ∀ r r' x y (i : Fin (vertex-width y)) (j : Fin (vertex-width x)) →
           hide vertex-width (hide vertex-width G r) r' x y i j ≡ two.I →
           hide vertex-width (hide vertex-width G r') r x y i j ≡ two.I
    into {G} fwd r r' x y i j e
      with two.⊔-I (hide vertex-width G r x y i j) ((hide vertex-width G r r' y ∘ hide vertex-width G r x r') i j) e
    into {G} fwd r r' x y i j e | inj₁ a with two.⊔-I (G x y i j) ((G r y ∘ G x r) i j) a
    ... | inj₁ a₁ = two.⊔-I-inl (two.⊔-I-inl a₁)
    ... | inj₂ a₂ with ∘-I (G r y) (G x r) i j a₂
    ...   | (k , (e₁ , e₂)) =
      two.⊔-I-inr (hide vertex-width G r' x y i j)
        (∘-I-at (hide vertex-width G r' r y) (hide vertex-width G r' x r) i j k (two.⊔-I-inl e₁) (two.⊔-I-inl e₂))
    into {G} fwd r r' x y i j e | inj₂ b
      with ∘-I (hide vertex-width G r r' y) (hide vertex-width G r x r') i j b
    ... | (m , (c , d)) with two.⊔-I (G r' y i m) ((G r y ∘ G r' r) i m) c
                           | two.⊔-I (G x r' m j) ((G r r' ∘ G x r) m j) d
    ...   | inj₁ c₁ | inj₁ d₁ =
      two.⊔-I-inl (two.⊔-I-inr (G x y i j) (∘-I-at (G r' y) (G x r') i j m c₁ d₁))
    ...   | inj₁ c₁ | inj₂ d₂ with ∘-I (G r r') (G x r) m j d₂
    ...     | (k , (d₁' , d₂')) =
      two.⊔-I-inr (hide vertex-width G r' x y i j)
        (∘-I-at (hide vertex-width G r' r y) (hide vertex-width G r' x r) i j k
          (two.⊔-I-inr (G r y i k) (∘-I-at (G r' y) (G r r') i k m c₁ d₁'))
          (two.⊔-I-inl d₂'))
    into {G} fwd r r' x y i j e | inj₂ b | (m , (c , d)) | inj₂ c₂ | inj₁ d₁
      with ∘-I (G r y) (G r' r) i m c₂
    ...     | (k , (c₁' , c₂')) =
      two.⊔-I-inr (hide vertex-width G r' x y i j)
        (∘-I-at (hide vertex-width G r' r y) (hide vertex-width G r' x r) i j k
          (two.⊔-I-inl c₁')
          (two.⊔-I-inr (G x r k j) (∘-I-at (G r' r) (G x r') k j m c₂' d₁)))
    into {G} fwd r r' x y i j e | inj₂ b | (m , (c , d)) | inj₂ c₂ | inj₂ d₂
      with ∘-I (G r y) (G r' r) i m c₂ | ∘-I (G r r') (G x r) m j d₂
    ...     | (k , (_ , c₂')) | (k' , (d₁' , _)) =
      ⊥-elim (asym r' r (fwd r' r k m c₂') (fwd r r' m k' d₁'))

    comm : ∀ {G} → Fwd G → ∀ r r' x y (i : Fin (vertex-width y)) (j : Fin (vertex-width x)) →
           hide vertex-width (hide vertex-width G r) r' x y i j ≡ hide vertex-width (hide vertex-width G r') r x y i j
    comm fwd r r' x y i j = two.I-antisym (into fwd r r' x y i j) (into fwd r' r x y i j)

  hide-all-perm : ∀ {G rs rs'} → Fwd G → rs ↭ rs' → hide-all vertex-width G rs ≐e hide-all vertex-width G rs'
  hide-all-perm fwd ↭.refl x y i j = ≡-refl
  hide-all-perm fwd (↭.prep r p) = hide-all-perm (fwd-hide r fwd) p
  hide-all-perm fwd (↭.swap {xs = rs} a b p) x y i j =
    ≡-trans (fold-cong rs (comm fwd a b) x y i j)
            (hide-all-perm (fwd-hide a (fwd-hide b fwd)) p x y i j)
  hide-all-perm fwd (↭.trans p q) x y i j =
    ≡-trans (hide-all-perm fwd p x y i j) (hide-all-perm fwd q x y i j)

module _ {m n : ℕ} (B : Graph m n) where
  open Graph B

  -- The interior vertices with the root adjoined: what a graph contributes to a larger graph.
  Path⁺ : Set
  Path⁺ = Vertex shape ⊎ Root

  width⁺ : Path⁺ → ℕ
  width⁺ = [ width , (λ _ → n) ]

  fo⁺ : Path⁺ → Bool
  fo⁺ = [ fo , (λ _ → fo-root) ]

  into⁺ : (q : Path⁺) → M.Matrix (width⁺ q) m
  into⁺ (inj₁ q) = into q
  into⁺ (inj₂ _) = out

  inside⁺ : (p q : Path⁺) → M.Matrix (width⁺ q) (width⁺ p)
  inside⁺ (inj₁ p) (inj₁ q) = inside p q
  inside⁺ (inj₁ p) (inj₂ _) = up p
  inside⁺ (inj₂ _) _        = M.εₘ

  _<⁺_ : Path⁺ → Path⁺ → Set
  _<⁺_ = lts (shape ∷ [])

  <⁺-order : IsStrictOrder _<⁺_
  <⁺-order = lts-order (shape ∷ [])

  <⁺-inside : ∀ p q (k : Fin (width⁺ q)) (l : Fin (width⁺ p)) →
              inside⁺ p q k l ≡ two.I → p <⁺ q
  <⁺-inside (inj₁ p) (inj₁ q) k l h = <-inside p q k l h
  <⁺-inside (inj₁ p) (inj₂ _) k l h = tt
  <⁺-inside (inj₂ _) q        k l ()

  paths⁺ : List Path⁺
  paths⁺ = inj₂ root ∷ map inj₁ (vertices shape)

  V : Set
  V = Input ⊎ Path⁺

  vertex-width : V → ℕ
  vertex-width = [ (λ _ → m) , width⁺ ]

  gr : Relation vertex-width
  gr (inj₁ _) (inj₂ q) = into⁺ q
  gr (inj₂ p) (inj₂ q) = inside⁺ p q
  gr _        (inj₁ _) = M.εₘ

  collapse : M.Matrix n m
  collapse = hide-all vertex-width gr (map (λ q → inj₂ (inj₁ q)) (vertices shape)) (inj₁ input) (inj₂ (inj₂ root))

  -- The interior vertices whose values are first-order, and their complement.
  FO : List (Vertex shape)
  FO = filterᵇ fo (vertices shape)

  fo-hidden : List (Vertex shape)
  fo-hidden = filterᵇ (λ q → not (fo q)) (vertices shape)

  -- The first-order graph: every intermediate whose value is not first-order is hidden, so the
  -- live vertices are the inputs, the root and FO.
  fo-graph : Relation vertex-width
  fo-graph = hide-all vertex-width gr (map (λ q → inj₂ (inj₁ q)) fo-hidden)

  -- The completion order on all the vertices: the inputs first, then the interior, then the root.
  _<ᵥ_ : V → V → Set
  _<ᵥ_ = sum-< (λ _ _ → Void) _<⁺_

  <ᵥ-order : IsStrictOrder _<ᵥ_
  <ᵥ-order = sum-<-order none-order <⁺-order

  private
    module O = Ordered vertex-width _<ᵥ_ <ᵥ-order

  open O public using (Fwd; fwd-hide; fwd-hide-all; hide-all-perm)

  -- Every entry of a graph runs strictly forward, and the first-order graph inherits it.
  gr-forward : Fwd gr
  gr-forward (inj₁ _) (inj₂ q) k l h = tt
  gr-forward (inj₂ p) (inj₂ q) k l h = <⁺-inside p q k l h
  gr-forward (inj₁ _) (inj₁ _) k l ()
  gr-forward (inj₂ p) (inj₁ _) k l ()

  fo-forward : Fwd fo-graph
  fo-forward = fwd-hide-all (map (λ q → inj₂ (inj₁ q)) fo-hidden) gr-forward

-- One step of hiding a vertex, on entries whose columns factor through P.
private
  distrib-root : ∀ {m n k l} (P : M.Matrix m n) (X : M.Matrix n k) (Y : M.Matrix n l) (Z : M.Matrix l k) →
                 ((P ∘ X) M.+ₘ ((P ∘ Y) ∘ Z)) ≈ (P ∘ (X M.+ₘ (Y ∘ Z)))
  distrib-root P X Y Z =
    ≈-trans (M.+ₘ-cong ≈-refl (assoc P Y Z)) (≈-sym (M.comp-bilinear₂ P X (Y ∘ Z)))

  root-step : ∀ {m n l k} {P : M.Matrix m n} {G₁ : M.Matrix m k} {X : M.Matrix n k}
              {G₂ : M.Matrix m l} {Y : M.Matrix n l} {G₃ Z : M.Matrix l k} →
              G₁ ≈ (P ∘ X) → G₂ ≈ (P ∘ Y) → G₃ ≈ Z →
              (G₁ M.+ₘ (G₂ ∘ G₃)) ≈ (P ∘ (X M.+ₘ (Y ∘ Z)))
  root-step {P = P} {X = X} {Y = Y} {Z = Z} a b c =
    ≈-trans (M.+ₘ-cong a (∘-cong b c)) (distrib-root P X Y Z)

  offset-step : ∀ {m n l k} {K : M.Matrix m k} {P : M.Matrix m n} {G₁ : M.Matrix m k}
                {X : M.Matrix n k} {G₂ : M.Matrix m l} {Y : M.Matrix n l} {G₃ Z : M.Matrix l k} →
                G₁ ≈ (K M.+ₘ (P ∘ X)) → G₂ ≈ (P ∘ Y) → G₃ ≈ Z →
                (G₁ M.+ₘ (G₂ ∘ G₃)) ≈ (K M.+ₘ (P ∘ (X M.+ₘ (Y ∘ Z))))
  offset-step {K = K} {P} {X = X} {Y = Y} {Z = Z} a b c =
    ≈-trans (M.+ₘ-cong a (∘-cong b c))
            (≈-trans (M.+ₘ-assoc K (P ∘ X) ((P ∘ Y) ∘ Z)) (M.+ₘ-cong ≈-refl (distrib-root P X Y Z)))

-- Hiding one premise's vertices, one at a time, inside the conclusion's graph. The state records
-- the premise's own relations as they accumulate; Φ carries the premise's input columns to the
-- conclusion's, which for a premise evaluated in a substituted environment is not the identity.
module HidePremise
  {V : Set} (vertex-width : V → ℕ)
  (inp : V)
  {Q : Set} (blk : Q ⊎ Root → V)
  {T : Set} (tgt : T → V)
  {m' : ℕ} (Φ : M.Matrix m' (vertex-width inp))
  (P : (t : T) → M.Matrix (vertex-width (tgt t)) (vertex-width (blk (inj₂ root))))
  (K : (t : T) → M.Matrix (vertex-width (tgt t)) (vertex-width inp))
  where

  record St : Set where
    field
      into   : (q : Q ⊎ Root) → M.Matrix (vertex-width (blk q)) m'
      inside : (p q : Q ⊎ Root) → M.Matrix (vertex-width (blk q)) (vertex-width (blk p))

  open St public

  step : St → (Q ⊎ Root) → St
  step H w .into q = H .into q M.+ₘ (H .inside w q ∘ H .into w)
  step H w .inside p q = H .inside p q M.+ₘ (H .inside w q ∘ H .inside p w)

  steps : St → List (Q ⊎ Root) → St
  steps = foldl step

  folds : ∀ {A V' : Set} (prem : A → St) (ι : Q ⊎ Root → V') (h' : A → V' → A) →
          (∀ G w → step (prem G) w ≡ prem (h' G (ι w))) →
          (ws : List (Q ⊎ Root)) (G : A) → steps (prem G) ws ≡ prem (foldl h' G (map ι ws))
  folds prem ι h' ok []       G = ≡-refl
  folds prem ι h' ok (w ∷ ws) G =
    ≡-trans (≡-cong (λ H → steps H ws) (ok G w)) (folds prem ι h' ok ws (h' G (ι w)))

  private
    Φ-step : ∀ (H : St) (w : (Q ⊎ Root)) (q : Q ⊎ Root) →
             (step H w .into q ∘ Φ)
             ≈ ((H .into q ∘ Φ) M.+ₘ (H .inside w q ∘ (H .into w ∘ Φ)))
    Φ-step H w q =
      ≈-trans (M.comp-bilinear₁ (H .into q) (H .inside w q ∘ H .into w) Φ)
              (M.+ₘ-cong ≈-refl (assoc (H .inside w q) (H .into w) Φ))

  record Agrees (G : Relation vertex-width) (H : St) : Set where
    field
      into-ok   : ∀ q → G inp (blk q) ≈ (H .into q ∘ Φ)
      inside-ok : ∀ p q → G (blk p) (blk q) ≈ H .inside p q
      tgt-ok    : ∀ t → G inp (tgt t) ≈ (K t M.+ₘ (P t ∘ (H .into (inj₂ root) ∘ Φ)))
      up-ok     : ∀ t (p : Q) → G (blk (inj₁ p)) (tgt t)
                                ≈ (P t ∘ H .inside (inj₁ p) (inj₂ root))

  open Agrees public

  agrees-hide : ∀ {G H} (w : Q) → Agrees G H → Agrees (hide vertex-width G (blk (inj₁ w))) (step H (inj₁ w))
  agrees-hide {H = H} w s .into-ok q =
    ≈-trans (M.+ₘ-cong (s .into-ok q) (∘-cong (s .inside-ok (inj₁ w) q) (s .into-ok (inj₁ w))))
            (≈-sym (Φ-step H (inj₁ w) q))
  agrees-hide w s .inside-ok p q =
    M.+ₘ-cong (s .inside-ok p q) (∘-cong (s .inside-ok (inj₁ w) q) (s .inside-ok p (inj₁ w)))
  agrees-hide {H = H} w s .tgt-ok t =
    ≈-trans (offset-step {K = K t} {P = P t}
                         {X = H .into (inj₂ root) ∘ Φ}
                         {Y = H .inside (inj₁ w) (inj₂ root)}
                         {Z = H .into (inj₁ w) ∘ Φ}
              (s .tgt-ok t) (s .up-ok t w) (s .into-ok (inj₁ w)))
            (M.+ₘ-cong ≈-refl (∘-cong₂ (≈-sym (Φ-step H (inj₁ w) (inj₂ root)))))
  agrees-hide {H = H} w s .up-ok t p =
    root-step {P = P t} {X = H .inside (inj₁ p) (inj₂ root)}
              {Y = H .inside (inj₁ w) (inj₂ root)} {Z = H .inside (inj₁ p) (inj₁ w)}
      (s .up-ok t p) (s .up-ok t w) (s .inside-ok (inj₁ p) (inj₁ w))

  agrees-hide-all : ∀ {G H} (ws : List (Q)) → Agrees G H →
                    Agrees (hide-all vertex-width G (map (λ w → blk (inj₁ w)) ws)) (steps H (map inj₁ ws))
  agrees-hide-all []       s = s
  agrees-hide-all (w ∷ ws) s = agrees-hide-all ws (agrees-hide w s)

  -- The relations a rule contributes, before the graph's root is hidden. Every edge from the graph to
  -- a target leaves the graph's root, which here is a matter of the vertex set rather than a lemma.
  record Start (G : Relation vertex-width) (H : St) : Set where
    field
      into-start   : ∀ q → G inp (blk q) ≈ (H .into q ∘ Φ)
      inside-start : ∀ p q → G (blk p) (blk q) ≈ H .inside p q
      tgt-start    : ∀ t → G inp (tgt t) ≈ K t
      up-start     : ∀ t → G (blk (inj₂ root)) (tgt t) ≈ P t
      off-start    : ∀ t (p : Q) → G (blk (inj₁ p)) (tgt t) ≈ M.εₘ
      sink         : ∀ q → H .inside (inj₂ root) q ≈ M.εₘ

  open Start public

  agrees-start : ∀ {G H} → Start G H →
                 Agrees (hide vertex-width G (blk (inj₂ root))) (step H (inj₂ root))
  agrees-start {H = H} r .into-ok q =
    ≈-trans (M.+ₘ-cong (r .into-start q)
                     (∘-cong (r .inside-start (inj₂ root) q) (r .into-start (inj₂ root))))
            (≈-sym (Φ-step H (inj₂ root) q))
  agrees-start r .inside-ok p q =
    M.+ₘ-cong (r .inside-start p q)
            (∘-cong (r .inside-start (inj₂ root) q) (r .inside-start p (inj₂ root)))
  agrees-start {H = H} r .tgt-ok t =
    ≈-trans (M.+ₘ-cong (r .tgt-start t)
                     (∘-cong (r .up-start t) (r .into-start (inj₂ root))))
            (M.+ₘ-cong ≈-refl (∘-cong₂ (≈-sym unchanged)))
    where
    unchanged : (step H (inj₂ root) .into (inj₂ root) ∘ Φ) ≈ (H .into (inj₂ root) ∘ Φ)
    unchanged =
      ≈-trans (Φ-step H (inj₂ root) (inj₂ root))
              (≈-trans (M.+ₘ-cong ≈-refl (∘-cong₁ (r .sink (inj₂ root))))
                       (M.absorb₁ (H .into (inj₂ root) ∘ Φ) (H .into (inj₂ root) ∘ Φ)))
  agrees-start {H = H} r .up-ok t p =
    ≈-trans (M.+ₘ-cong (r .off-start t p)
                     (∘-cong (r .up-start t) (r .inside-start (inj₁ p) (inj₂ root))))
    (≈-trans (M.+ₘ-lunit (P t ∘ H .inside (inj₁ p) (inj₂ root)))
             (∘-cong₂ (≈-sym unchanged)))
    where
    unchanged : step H (inj₂ root) .inside (inj₁ p) (inj₂ root)
                ≈ H .inside (inj₁ p) (inj₂ root)
    unchanged =
      ≈-trans (M.+ₘ-cong ≈-refl (∘-cong₁ (r .sink (inj₂ root))))
              (M.absorb₁ (H .inside (inj₁ p) (inj₂ root)) (H .inside (inj₁ p) (inj₂ root)))

-- Rows out of vertices with no relation into the hidden set survive hiding.
module Behind
  {V : Set} (vertex-width : V → ℕ)
  {W : Set} (hid : W → V)
  {S : Set} (src : S → V)
  {T : Set} (col : T → V)
  (B : (s : S) (t : T) → M.Matrix (vertex-width (col t)) (vertex-width (src s)))
  where

  record Keeps (G : Relation vertex-width) : Set where
    field
      keeps : ∀ s t → G (src s) (col t) ≈ B s t
      blind : ∀ s w → G (src s) (hid w) ≈ M.εₘ

  open Keeps public

  keeps-hide : ∀ {G} (w : W) → Keeps G → Keeps (hide vertex-width G (hid w))
  keeps-hide {G} w k .keeps s t =
    ≈-trans (M.+ₘ-cong (k .keeps s t) (∘-cong₂ (k .blind s w)))
            (M.absorb₂ (B s t) (G (hid w) (col t)))
  keeps-hide {G} w k .blind s w' =
    ≈-trans (M.+ₘ-cong (k .blind s w') (∘-cong₂ (k .blind s w)))
            (M.absorb₂ M.εₘ (G (hid w) (hid w')))

  keeps-hide-all : ∀ {G} {W' : Set} (f : W' → W) (ws : List W') →
                   Keeps G → Keeps (hide-all vertex-width G (map (λ w → hid (f w)) ws))
  keeps-hide-all f []       k = k
  keeps-hide-all f (w ∷ ws) k = keeps-hide-all f ws (keeps-hide (f w) k)

private
  map-map : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} (g : B → C) (f : A → B) (xs : List A) →
            map g (map f xs) ≡ map (λ x → g (f x)) xs
  map-map g f []       = ≡-refl
  map-map g f (x ∷ xs) = ≡-cong (g (f x) ∷_) (map-map g f xs)

  map-++ : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (xs ys : List A) →
           map f (xs ++ ys) ≡ map f xs ++ map f ys
  map-++ f []       ys = ≡-refl
  map-++ f (x ∷ xs) ys = ≡-cong (f x ∷_) (map-++ f xs ys)

-- Hiding a graph's own vertices, its root first, computes its collapse: the root has no outgoing
-- relation, so hiding it changes nothing.
module _ {m n : ℕ} (B : Graph m n) where

  root-row : ∀ y → gr B (inj₂ (inj₂ root)) y ≈ M.εₘ
  root-row (inj₁ _) = ≈-refl {f = M.εₘ}
  root-row (inj₂ _) = ≈-refl {f = M.εₘ}

  hide-paths⁺ : hide-all (vertex-width B) (gr B) (map inj₂ (paths⁺ B)) (inj₁ input) (inj₂ (inj₂ root))
                ≈ collapse B
  hide-paths⁺ =
    ≈-trans (≈-of-≡ (≡-cong (λ l → hide-all (vertex-width B) (gr B) l (inj₁ input) (inj₂ (inj₂ root)))
                            (≡-cong (inj₂ (inj₂ root) ∷_) (map-map inj₂ inj₁ (vertices (Graph.shape B))))))
            (hide-all-cong (vertex-width B) (map (λ q → inj₂ (inj₁ q)) (vertices (Graph.shape B)))
                           (hide-sink (vertex-width B) (gr B) (inj₂ (inj₂ root)) root-row)
                           (inj₁ input) (inj₂ (inj₂ root)))

-- A premise's inputs from the conclusion's and from an earlier root, read after the earlier root
-- has collapsed.
private
  factor : ∀ {x y z w v} (A : M.Matrix z y) (r : M.Matrix y x) (l : M.Matrix y w)
           {h c : M.Matrix w v} (ρ : M.Matrix v x) → h ≈ c →
           ((A ∘ r) M.+ₘ ((A ∘ l) ∘ (h ∘ ρ))) ≈ (A ∘ (r M.+ₘ (l ∘ (c ∘ ρ))))
  factor A r l ρ e =
    ≈-trans (M.+ₘ-cong ≈-refl (≈-trans (∘-cong₂ (∘-cong₁ e)) (assoc A l (_ ∘ ρ))))
            (≈-sym (M.comp-bilinear₂ A r (l ∘ (_ ∘ ρ))))

-- Columns into vertices the hidden set has no relation into survive hiding.
module Frozen
  {V : Set} (vertex-width : V → ℕ)
  {W : Set} (hid : W → V)
  {S : Set} (src : S → V)
  {T : Set} (col : T → V)
  (B : (s : S) (t : T) → M.Matrix (vertex-width (col t)) (vertex-width (src s)))
  where

  record Keeps (G : Relation vertex-width) : Set where
    field
      keeps : ∀ s t → G (src s) (col t) ≈ B s t
      blind : ∀ w t → G (hid w) (col t) ≈ M.εₘ

  open Keeps public

  keeps-hide : ∀ {G} (w : W) → Keeps G → Keeps (hide vertex-width G (hid w))
  keeps-hide {G} w k .keeps s t =
    ≈-trans (M.+ₘ-cong (k .keeps s t) (∘-cong₁ (k .blind w t)))
            (M.absorb₁ (B s t) (G (src s) (hid w)))
  keeps-hide {G} w k .blind w' t =
    ≈-trans (M.+ₘ-cong (k .blind w' t) (∘-cong₁ (k .blind w t)))
            (M.absorb₁ M.εₘ (G (hid w') (hid w)))

  keeps-hide-all : ∀ {G} {W' : Set} (f : W' → W) (ws : List W') →
                   Keeps G → Keeps (hide-all vertex-width G (map (λ w → hid (f w)) ws))
  keeps-hide-all f []       k = k
  keeps-hide-all f (w ∷ ws) k = keeps-hide-all f ws (keeps-hide (f w) k)


-- A rule with no premises: the root and the inputs, and nothing between.
module Rule₀
  {m n : ℕ} (fo-root : Bool)
  (out-root : M.Matrix n m)
  where

  E : Graph m n
  E .Graph.shape = node []
  E .Graph.width ()
  E .Graph.fo ()
  E .Graph.<-inside ()
  E .Graph.fo-root = fo-root
  E .Graph.into ()
  E .Graph.inside ()
  E .Graph.out = out-root
  E .Graph.up ()

  agree : collapse E ≈ out-root
  agree = ≈-refl {f = out-root}

-- A rule with one premise: the conclusion's root is the premise's root through up-root, offset by
-- out-root, and the premise's inputs are the conclusion's through inputs.
module Rule₁
  {m : ℕ}
  {m' n₀ : ℕ} (B : Graph m' n₀)
  {n : ℕ}
  (inputs : M.Matrix m' m)
  (fo-root : Bool)
  (out-root : M.Matrix n m)
  (up-root : M.Matrix n n₀)
  where

  E : Graph m n
  E .Graph.shape = node (Graph.shape B ∷ [])
  E .Graph.width = width⁺ B
  E .Graph.fo = fo⁺ B
  E .Graph.into q = into⁺ B q ∘ inputs
  E .Graph.inside = inside⁺ B
  E .Graph.<-inside = <⁺-inside B
  E .Graph.fo-root = fo-root
  E .Graph.out = out-root
  E .Graph.up (inj₁ _) = M.εₘ
  E .Graph.up (inj₂ _) = up-root

  private
    b : Path⁺ B → V E
    b q = inj₂ (inj₁ q)

    er : V E
    er = inj₂ (inj₂ root)

    module S = HidePremise (vertex-width E) (inj₁ input) b (λ (_ : Root) → er) inputs (λ _ → up-root) (λ _ → out-root)

    H⁰ : S.St
    H⁰ .S.into q = into⁺ B q
    H⁰ .S.inside p q = inside⁺ B p q

    start : S.Start (gr E) H⁰
    start .S.into-start q = ≈-refl
    start .S.inside-start p q = ≈-refl
    start .S.tgt-start _ = ≈-refl {f = out-root}
    start .S.up-start _ = ≈-refl {f = up-root}
    start .S.off-start _ p = ≈-refl {f = M.εₘ}
    start .S.sink q = ≈-refl {f = M.εₘ}

    H : S.St
    H = S.steps (S.step H⁰ (inj₂ root)) (map inj₁ (vertices (Graph.shape B)))

    done : S.Agrees (hide-all (vertex-width E) (hide (vertex-width E) (gr E) (b (inj₂ root)))
                              (map (λ w → b (inj₁ w)) (vertices (Graph.shape B)))) H
    done = S.agrees-hide-all (vertices (Graph.shape B)) (S.agrees-start start)

    prem : Relation (vertex-width B) → S.St
    prem G .S.into q = G (inj₁ input) (inj₂ q)
    prem G .S.inside p q = G (inj₂ p) (inj₂ q)

    κ : H .S.into (inj₂ root) ≈ collapse B
    κ =
      ≈-trans (≈-of-≡ (≡-cong (λ H' → H' .S.into (inj₂ root))
                              (S.folds prem inj₂ (hide (vertex-width B)) (λ G w → ≡-refl)
                                       (paths⁺ B) (gr B))))
              (hide-paths⁺ B)

    plumb : collapse E
            ≡ hide-all (vertex-width E) (hide (vertex-width E) (gr E) (b (inj₂ root)))
                       (map (λ w → b (inj₁ w)) (vertices (Graph.shape B))) (inj₁ input) er
    plumb = ≡-cong (λ l → hide-all (vertex-width E) (gr E) l (inj₁ input) er)
                   (≡-cong (b (inj₂ root) ∷_) (map-map b inj₁ (vertices (Graph.shape B))))

  agree : collapse E ≈ (out-root M.+ₘ (up-root ∘ (collapse B ∘ inputs)))
  agree =
    ≈-trans (≈-of-≡ plumb)
            (≈-trans (done .S.tgt-ok root)
                     (M.+ₘ-cong ≈-refl (∘-cong₂ (∘-cong₁ κ))))

-- Two premises in sequence: the first's inputs come from the conclusion's, the second's from the
-- conclusion's and the first's root. Both roots feed the conclusion's.
module Rule₂
  {m : ℕ}
  {m₁ n₁ : ℕ} (B₁ : Graph m₁ n₁)
  {m₂ n₂ : ℕ} (B₂ : Graph m₂ n₂)
  {n : ℕ}
  (inputs₁ : M.Matrix m₁ m)
  (inputs₂ : M.Matrix m₂ (m + n₁))
  (fo-root : Bool)
  (out-root : M.Matrix n m)
  (up₁ : M.Matrix n n₁)
  (up₂ : M.Matrix n n₂)
  where

  private
    from-inputs₂ : M.Matrix m₂ m
    from-inputs₂ = inputs₂ ∘ M.in₁ {m} {n₁}

    from-root₁ : M.Matrix m₂ n₁
    from-root₁ = inputs₂ ∘ M.in₂ {m} {n₁}

    ps₁ = vertices (Graph.shape B₁)
    ps₂ = vertices (Graph.shape B₂)

    upE : (s : Path⁺ B₂) → M.Matrix n (width⁺ B₂ s)
    upE (inj₁ _) = M.εₘ
    upE (inj₂ _) = up₂

  E : Graph m n
  E .Graph.shape = node (Graph.shape B₁ ∷ Graph.shape B₂ ∷ [])
  E .Graph.width = [ width⁺ B₁ , width⁺ B₂ ]
  E .Graph.fo = [ fo⁺ B₁ , fo⁺ B₂ ]
  E .Graph.into (inj₁ q) = into⁺ B₁ q ∘ inputs₁
  E .Graph.into (inj₂ q) = into⁺ B₂ q ∘ from-inputs₂
  E .Graph.inside (inj₁ p)        (inj₁ q) = inside⁺ B₁ p q
  E .Graph.inside (inj₁ (inj₁ p)) (inj₂ q) = M.εₘ
  E .Graph.inside (inj₁ (inj₂ _)) (inj₂ q) = into⁺ B₂ q ∘ from-root₁
  E .Graph.inside (inj₂ p)        (inj₁ q) = M.εₘ
  E .Graph.inside (inj₂ p)        (inj₂ q) = inside⁺ B₂ p q
  E .Graph.fo-root = fo-root
  E .Graph.<-inside (inj₁ (inj₁ p)) (inj₁ (inj₁ q)) k l h = Graph.<-inside B₁ p q k l h
  E .Graph.<-inside (inj₁ (inj₁ p)) (inj₁ (inj₂ _)) k l h = tt
  E .Graph.<-inside (inj₁ (inj₂ _)) (inj₁ _)        k l ()
  E .Graph.<-inside (inj₁ (inj₁ p)) (inj₂ q)        k l h = tt
  E .Graph.<-inside (inj₁ (inj₂ _)) (inj₂ q)        k l h = tt
  E .Graph.<-inside (inj₂ p)        (inj₁ q)        k l ()
  E .Graph.<-inside (inj₂ (inj₁ p)) (inj₂ (inj₁ q)) k l h = Graph.<-inside B₂ p q k l h
  E .Graph.<-inside (inj₂ (inj₁ p)) (inj₂ (inj₂ _)) k l h = tt
  E .Graph.<-inside (inj₂ (inj₂ _)) (inj₂ _)        k l ()
  E .Graph.out = out-root
  E .Graph.up (inj₁ (inj₁ p)) = M.εₘ
  E .Graph.up (inj₁ (inj₂ _)) = up₁
  E .Graph.up (inj₂ s) = upE s

  private
    b1 : Path⁺ B₁ → V E
    b1 q = inj₂ (inj₁ (inj₁ q))

    b2 : Path⁺ B₂ → V E
    b2 q = inj₂ (inj₁ (inj₂ q))

    er : V E
    er = inj₂ (inj₂ root)

    tgt₁ : Path⁺ B₂ ⊎ Root → V E
    tgt₁ (inj₁ q) = b2 q
    tgt₁ (inj₂ _) = er

    P₁ : (t : Path⁺ B₂ ⊎ Root) → M.Matrix (vertex-width E (tgt₁ t)) n₁
    P₁ (inj₁ q) = into⁺ B₂ q ∘ from-root₁
    P₁ (inj₂ _) = up₁

    K₁ : (t : Path⁺ B₂ ⊎ Root) → M.Matrix (vertex-width E (tgt₁ t)) m
    K₁ (inj₁ q) = into⁺ B₂ q ∘ from-inputs₂
    K₁ (inj₂ _) = out-root

    module S1 = HidePremise (vertex-width E) (inj₁ input) b1 tgt₁ inputs₁ P₁ K₁

    H₁⁰ : S1.St
    H₁⁰ .S1.into q = into⁺ B₁ q
    H₁⁰ .S1.inside p q = inside⁺ B₁ p q

    start₁ : S1.Start (gr E) H₁⁰
    start₁ .S1.into-start q = ≈-refl
    start₁ .S1.inside-start p q = ≈-refl
    start₁ .S1.tgt-start (inj₁ q) = ≈-refl
    start₁ .S1.tgt-start (inj₂ _) = ≈-refl {f = out-root}
    start₁ .S1.up-start (inj₁ q) = ≈-refl
    start₁ .S1.up-start (inj₂ _) = ≈-refl {f = up₁}
    start₁ .S1.off-start (inj₁ q) p = ≈-refl {f = M.εₘ}
    start₁ .S1.off-start (inj₂ _) p = ≈-refl {f = M.εₘ}
    start₁ .S1.sink q = ≈-refl {f = M.εₘ}

    G₁ : Relation (vertex-width E)
    G₁ = hide-all (vertex-width E) (hide (vertex-width E) (gr E) (b1 (inj₂ root))) (map (λ w → b1 (inj₁ w)) ps₁)

    H₁ : S1.St
    H₁ = S1.steps (S1.step H₁⁰ (inj₂ root)) (map inj₁ ps₁)

    done₁ : S1.Agrees G₁ H₁
    done₁ = S1.agrees-hide-all ps₁ (S1.agrees-start start₁)

    prem₁ : Relation (vertex-width B₁) → S1.St
    prem₁ G .S1.into q = G (inj₁ input) (inj₂ q)
    prem₁ G .S1.inside p q = G (inj₂ p) (inj₂ q)

    κ₁ : H₁ .S1.into (inj₂ root) ≈ collapse B₁
    κ₁ =
      ≈-trans (≈-of-≡ (≡-cong (λ H → H .S1.into (inj₂ root))
                              (S1.folds prem₁ inj₂ (hide (vertex-width B₁)) (λ G w → ≡-refl)
                                        (paths⁺ B₁) (gr B₁))))
              (hide-paths⁺ B₁)

  -- The second premise's inputs once the first premise has collapsed.
  Φ₂ : M.Matrix m₂ m
  Φ₂ = inputs₂ ∘ M.⟨ M.I , collapse B₁ ∘ inputs₁ ⟩

  private
    Φ₂' : M.Matrix m₂ m
    Φ₂' = from-inputs₂ M.+ₘ (from-root₁ ∘ (collapse B₁ ∘ inputs₁))

    Φ₂-split : Φ₂' ≈ Φ₂
    Φ₂-split = ≈-sym (≈-trans (M.∘-pair inputs₂ M.I (collapse B₁ ∘ inputs₁))
                              (M.+ₘ-cong (id-right {f = from-inputs₂}) (≈-refl {f = from-root₁ ∘ (collapse B₁ ∘ inputs₁)})))

    P₂ : (t : Root) → M.Matrix n n₂
    P₂ _ = up₂

    K₂ : (t : Root) → M.Matrix n m
    K₂ _ = out-root M.+ₘ (up₁ ∘ (collapse B₁ ∘ inputs₁))

    module S2 = HidePremise (vertex-width E) (inj₁ input) b2 (λ (_ : Root) → er) Φ₂' P₂ K₂

    col₂ : Path⁺ B₂ ⊎ Root → V E
    col₂ (inj₁ q) = b2 q
    col₂ (inj₂ _) = er

    Bh : (s : Path⁺ B₂) (t : Path⁺ B₂ ⊎ Root) → M.Matrix (vertex-width E (col₂ t)) (width⁺ B₂ s)
    Bh s (inj₁ q) = inside⁺ B₂ s q
    Bh s (inj₂ _) = upE s

    module Bd = Behind (vertex-width E) b1 b2 col₂ Bh

    keeps₀ : Bd.Keeps (gr E)
    keeps₀ .Bd.keeps s (inj₁ q) = ≈-refl
    keeps₀ .Bd.keeps s (inj₂ _) = ≈-refl {f = upE s}
    keeps₀ .Bd.blind s w = ≈-refl {f = M.εₘ}

    keeps₁ : Bd.Keeps G₁
    keeps₁ = Bd.keeps-hide-all inj₁ ps₁ (Bd.keeps-hide (inj₂ root) keeps₀)

    H₂⁰ : S2.St
    H₂⁰ .S2.into q = into⁺ B₂ q
    H₂⁰ .S2.inside p q = inside⁺ B₂ p q

    start₂ : S2.Start G₁ H₂⁰
    start₂ .S2.into-start q =
      ≈-trans (done₁ .S1.tgt-ok (inj₁ q)) (factor (into⁺ B₂ q) from-inputs₂ from-root₁ inputs₁ κ₁)
    start₂ .S2.inside-start p q = keeps₁ .Bd.keeps p (inj₁ q)
    start₂ .S2.tgt-start _ =
      ≈-trans (done₁ .S1.tgt-ok (inj₂ root))
              (M.+ₘ-cong ≈-refl (∘-cong₂ (∘-cong₁ κ₁)))
    start₂ .S2.up-start _ = keeps₁ .Bd.keeps (inj₂ root) (inj₂ root)
    start₂ .S2.off-start _ p = keeps₁ .Bd.keeps (inj₁ p) (inj₂ root)
    start₂ .S2.sink q = ≈-refl {f = M.εₘ}

    G₂ : Relation (vertex-width E)
    G₂ = hide-all (vertex-width E) (hide (vertex-width E) G₁ (b2 (inj₂ root))) (map (λ w → b2 (inj₁ w)) ps₂)

    H₂ : S2.St
    H₂ = S2.steps (S2.step H₂⁰ (inj₂ root)) (map inj₁ ps₂)

    done₂ : S2.Agrees G₂ H₂
    done₂ = S2.agrees-hide-all ps₂ (S2.agrees-start start₂)

    prem₂ : Relation (vertex-width B₂) → S2.St
    prem₂ G .S2.into q = G (inj₁ input) (inj₂ q)
    prem₂ G .S2.inside p q = G (inj₂ p) (inj₂ q)

    κ₂ : H₂ .S2.into (inj₂ root) ≈ collapse B₂
    κ₂ =
      ≈-trans (≈-of-≡ (≡-cong (λ H → H .S2.into (inj₂ root))
                              (S2.folds prem₂ inj₂ (hide (vertex-width B₂)) (λ G w → ≡-refl)
                                        (paths⁺ B₂) (gr B₂))))
              (hide-paths⁺ B₂)

    lst : map (λ q → inj₂ {A = Input} (inj₁ q)) (vertices (Graph.shape E))
          ≡ (b1 (inj₂ root) ∷ map (λ w → b1 (inj₁ w)) ps₁)
            ++ (b2 (inj₂ root) ∷ map (λ w → b2 (inj₁ w)) ps₂)
    lst =
      ≡-trans (map-++ (λ q → inj₂ (inj₁ q)) (map inj₁ (paths⁺ B₁)) (map inj₂ (paths⁺ B₂)))
              (≡-cong₂ _++_
                (≡-trans (map-map (λ q → inj₂ (inj₁ q)) inj₁ (paths⁺ B₁))
                         (≡-cong (b1 (inj₂ root) ∷_) (map-map b1 inj₁ ps₁)))
                (≡-trans (map-map (λ q → inj₂ (inj₁ q)) inj₂ (paths⁺ B₂))
                         (≡-cong (b2 (inj₂ root) ∷_) (map-map b2 inj₁ ps₂))))

    plumb : collapse E ≡ G₂ (inj₁ input) er
    plumb =
      ≡-trans (≡-cong (λ l → hide-all (vertex-width E) (gr E) l (inj₁ input) er) lst)
              (≡-cong (λ G → G (inj₁ input) er)
                      (hide-all-++ (vertex-width E) (gr E)
                        (b1 (inj₂ root) ∷ map (λ w → b1 (inj₁ w)) ps₁)
                        (b2 (inj₂ root) ∷ map (λ w → b2 (inj₁ w)) ps₂)))

  agree : collapse E
          ≈ ((out-root M.+ₘ (up₁ ∘ (collapse B₁ ∘ inputs₁))) M.+ₘ (up₂ ∘ (collapse B₂ ∘ Φ₂)))
  agree =
    ≈-trans (≈-of-≡ plumb)
            (≈-trans (done₂ .S2.tgt-ok root)
                     (M.+ₘ-cong ≈-refl (∘-cong₂ (∘-cong κ₂ Φ₂-split))))

-- Three premises in sequence: the first two take their inputs from the conclusion's and have no
-- relation between them; the third takes its from the conclusion's and both earlier roots.
module Rule₃
  {m : ℕ}
  {m₁ n₁ : ℕ} (B₁ : Graph m₁ n₁)
  {m₂ n₂ : ℕ} (B₂ : Graph m₂ n₂)
  {m₃ n₃ : ℕ} (B₃ : Graph m₃ n₃)
  {n : ℕ}
  (inputs₁ : M.Matrix m₁ m)
  (inputs₂ : M.Matrix m₂ m)
  (inputs₃ : M.Matrix m₃ ((m + n₁) + n₂))
  (fo-root : Bool)
  (out-root : M.Matrix n m)
  (up₁ : M.Matrix n n₁)
  (up₂ : M.Matrix n n₂)
  (up₃ : M.Matrix n n₃)
  where

  private
    from-inputs₃ : M.Matrix m₃ m
    from-inputs₃ = (inputs₃ ∘ M.in₁ {m + n₁} {n₂}) ∘ M.in₁ {m} {n₁}

    from-root₁ : M.Matrix m₃ n₁
    from-root₁ = (inputs₃ ∘ M.in₁ {m + n₁} {n₂}) ∘ M.in₂ {m} {n₁}

    from-root₂ : M.Matrix m₃ n₂
    from-root₂ = inputs₃ ∘ M.in₂ {m + n₁} {n₂}

    ps₁ = vertices (Graph.shape B₁)
    ps₂ = vertices (Graph.shape B₂)
    ps₃ = vertices (Graph.shape B₃)

    r₁ : (q : Path⁺ B₁) → M.Matrix n (width⁺ B₁ q)
    r₁ (inj₁ _) = M.εₘ
    r₁ (inj₂ _) = up₁

    r₂ : (q : Path⁺ B₂) → M.Matrix n (width⁺ B₂ q)
    r₂ (inj₁ _) = M.εₘ
    r₂ (inj₂ _) = up₂

    r₃ : (q : Path⁺ B₃) → M.Matrix n (width⁺ B₃ q)
    r₃ (inj₁ _) = M.εₘ
    r₃ (inj₂ _) = up₃

    e₁₃ : (p : Path⁺ B₁) (q : Path⁺ B₃) → M.Matrix (width⁺ B₃ q) (width⁺ B₁ p)
    e₁₃ (inj₁ _) q = M.εₘ
    e₁₃ (inj₂ _) q = into⁺ B₃ q ∘ from-root₁

    e₂₃ : (p : Path⁺ B₂) (q : Path⁺ B₃) → M.Matrix (width⁺ B₃ q) (width⁺ B₂ p)
    e₂₃ (inj₁ _) q = M.εₘ
    e₂₃ (inj₂ _) q = into⁺ B₃ q ∘ from-root₂

  E : Graph m n
  E .Graph.shape = node (Graph.shape B₁ ∷ Graph.shape B₂ ∷ Graph.shape B₃ ∷ [])
  E .Graph.width = [ width⁺ B₁ , [ width⁺ B₂ , width⁺ B₃ ] ]
  E .Graph.fo = [ fo⁺ B₁ , [ fo⁺ B₂ , fo⁺ B₃ ] ]
  E .Graph.into (inj₁ q)        = into⁺ B₁ q ∘ inputs₁
  E .Graph.into (inj₂ (inj₁ q)) = into⁺ B₂ q ∘ inputs₂
  E .Graph.into (inj₂ (inj₂ q)) = into⁺ B₃ q ∘ from-inputs₃
  E .Graph.inside (inj₁ p)        (inj₁ q)        = inside⁺ B₁ p q
  E .Graph.inside (inj₁ p)        (inj₂ (inj₁ q)) = M.εₘ
  E .Graph.inside (inj₁ p)        (inj₂ (inj₂ q)) = e₁₃ p q
  E .Graph.inside (inj₂ (inj₁ p)) (inj₁ q)        = M.εₘ
  E .Graph.inside (inj₂ (inj₂ p)) (inj₁ q)        = M.εₘ
  E .Graph.inside (inj₂ (inj₁ p)) (inj₂ (inj₁ q)) = inside⁺ B₂ p q
  E .Graph.inside (inj₂ (inj₂ p)) (inj₂ (inj₁ q)) = M.εₘ
  E .Graph.inside (inj₂ (inj₁ p)) (inj₂ (inj₂ q)) = e₂₃ p q
  E .Graph.inside (inj₂ (inj₂ p)) (inj₂ (inj₂ q)) = inside⁺ B₃ p q
  E .Graph.fo-root = fo-root
  E .Graph.<-inside (inj₁ (inj₁ p)) (inj₁ (inj₁ q)) k l h = Graph.<-inside B₁ p q k l h
  E .Graph.<-inside (inj₁ (inj₁ p)) (inj₁ (inj₂ _)) k l h = tt
  E .Graph.<-inside (inj₁ (inj₂ _)) (inj₁ _)        k l ()
  E .Graph.<-inside (inj₁ (inj₁ p)) (inj₂ q)        k l h = tt
  E .Graph.<-inside (inj₁ (inj₂ _)) (inj₂ q)        k l h = tt
  E .Graph.<-inside (inj₂ (inj₁ p)) (inj₁ q)        k l ()
  E .Graph.<-inside (inj₂ (inj₂ p)) (inj₁ q)        k l ()
  E .Graph.<-inside (inj₂ (inj₁ (inj₁ p))) (inj₂ (inj₁ (inj₁ q))) k l h = Graph.<-inside B₂ p q k l h
  E .Graph.<-inside (inj₂ (inj₁ (inj₁ p))) (inj₂ (inj₁ (inj₂ _))) k l h = tt
  E .Graph.<-inside (inj₂ (inj₁ (inj₂ _))) (inj₂ (inj₁ _))        k l ()
  E .Graph.<-inside (inj₂ (inj₁ (inj₁ p))) (inj₂ (inj₂ _))        k l h = tt
  E .Graph.<-inside (inj₂ (inj₁ (inj₂ _))) (inj₂ (inj₂ _))        k l h = tt
  E .Graph.<-inside (inj₂ (inj₂ _))        (inj₂ (inj₁ _))        k l ()
  E .Graph.<-inside (inj₂ (inj₂ (inj₁ p))) (inj₂ (inj₂ (inj₁ q))) k l h = Graph.<-inside B₃ p q k l h
  E .Graph.<-inside (inj₂ (inj₂ (inj₁ p))) (inj₂ (inj₂ (inj₂ _))) k l h = tt
  E .Graph.<-inside (inj₂ (inj₂ (inj₂ _))) (inj₂ (inj₂ _))        k l ()
  E .Graph.out = out-root
  E .Graph.up (inj₁ p)        = r₁ p
  E .Graph.up (inj₂ (inj₁ p)) = r₂ p
  E .Graph.up (inj₂ (inj₂ p)) = r₃ p

  private
    b1 : Path⁺ B₁ → V E
    b1 q = inj₂ (inj₁ (inj₁ q))

    b2 : Path⁺ B₂ → V E
    b2 q = inj₂ (inj₁ (inj₂ (inj₁ q)))

    b3 : Path⁺ B₃ → V E
    b3 q = inj₂ (inj₁ (inj₂ (inj₂ q)))

    er : V E
    er = inj₂ (inj₂ root)

    tgt : Path⁺ B₃ ⊎ Root → V E
    tgt (inj₁ q) = b3 q
    tgt (inj₂ _) = er

    c₁ : M.Matrix n₁ m
    c₁ = collapse B₁ ∘ inputs₁

    c₂ : M.Matrix n₂ m
    c₂ = collapse B₂ ∘ inputs₂

    P₁ : (t : Path⁺ B₃ ⊎ Root) → M.Matrix (vertex-width E (tgt t)) n₁
    P₁ (inj₁ q) = into⁺ B₃ q ∘ from-root₁
    P₁ (inj₂ _) = up₁

    K₁ : (t : Path⁺ B₃ ⊎ Root) → M.Matrix (vertex-width E (tgt t)) m
    K₁ (inj₁ q) = into⁺ B₃ q ∘ from-inputs₃
    K₁ (inj₂ _) = out-root

    module S1 = HidePremise (vertex-width E) (inj₁ input) b1 tgt inputs₁ P₁ K₁

    H₁⁰ : S1.St
    H₁⁰ .S1.into q = into⁺ B₁ q
    H₁⁰ .S1.inside p q = inside⁺ B₁ p q

    start₁ : S1.Start (gr E) H₁⁰
    start₁ .S1.into-start q = ≈-refl
    start₁ .S1.inside-start p q = ≈-refl
    start₁ .S1.tgt-start (inj₁ q) = ≈-refl
    start₁ .S1.tgt-start (inj₂ _) = ≈-refl {f = out-root}
    start₁ .S1.up-start (inj₁ q) = ≈-refl
    start₁ .S1.up-start (inj₂ _) = ≈-refl {f = up₁}
    start₁ .S1.off-start (inj₁ q) p = ≈-refl {f = M.εₘ}
    start₁ .S1.off-start (inj₂ _) p = ≈-refl {f = M.εₘ}
    start₁ .S1.sink q = ≈-refl {f = M.εₘ}

    G₁ : Relation (vertex-width E)
    G₁ = hide-all (vertex-width E) (hide (vertex-width E) (gr E) (b1 (inj₂ root))) (map (λ w → b1 (inj₁ w)) ps₁)

    H₁ : S1.St
    H₁ = S1.steps (S1.step H₁⁰ (inj₂ root)) (map inj₁ ps₁)

    done₁ : S1.Agrees G₁ H₁
    done₁ = S1.agrees-hide-all ps₁ (S1.agrees-start start₁)

    prem₁ : Relation (vertex-width B₁) → S1.St
    prem₁ G .S1.into q = G (inj₁ input) (inj₂ q)
    prem₁ G .S1.inside p q = G (inj₂ p) (inj₂ q)

    κ₁ : H₁ .S1.into (inj₂ root) ≈ collapse B₁
    κ₁ =
      ≈-trans (≈-of-≡ (≡-cong (λ H → H .S1.into (inj₂ root))
                              (S1.folds prem₁ inj₂ (hide (vertex-width B₁)) (λ G w → ≡-refl)
                                        (paths⁺ B₁) (gr B₁))))
              (hide-paths⁺ B₁)

    -- The second premise's columns are untouched by the first premise's sweep.
    module Fz = Frozen (vertex-width E) b1 (inj₁ {A = Input}) b2 (λ _ q → into⁺ B₂ q ∘ inputs₂)

    keeps₀ : Fz.Keeps (gr E)
    keeps₀ .Fz.keeps _ q = ≈-refl
    keeps₀ .Fz.blind w q = ≈-refl {f = M.εₘ}

    keeps₁ : Fz.Keeps G₁
    keeps₁ = Fz.keeps-hide-all inj₁ ps₁ (Fz.keeps-hide (inj₂ root) keeps₀)

    -- The second and third premises' rows are untouched by earlier sweeps.
    cols₂ : Path⁺ B₂ ⊎ (Path⁺ B₃ ⊎ Root) → V E
    cols₂ (inj₁ q) = b2 q
    cols₂ (inj₂ t) = tgt t

    Bh₂ : (s : Path⁺ B₂) (t : Path⁺ B₂ ⊎ (Path⁺ B₃ ⊎ Root)) → M.Matrix (vertex-width E (cols₂ t)) (width⁺ B₂ s)
    Bh₂ s (inj₁ q)        = inside⁺ B₂ s q
    Bh₂ s (inj₂ (inj₁ q)) = e₂₃ s q
    Bh₂ s (inj₂ (inj₂ _)) = r₂ s

    module Bd₂ = Behind (vertex-width E) b1 b2 cols₂ Bh₂

    behind₂ : Bd₂.Keeps G₁
    behind₂ = Bd₂.keeps-hide-all inj₁ ps₁ (Bd₂.keeps-hide (inj₂ root) k₀)
      where
      k₀ : Bd₂.Keeps (gr E)
      k₀ .Bd₂.keeps s (inj₁ q)        = ≈-refl
      k₀ .Bd₂.keeps s (inj₂ (inj₁ q)) = ≈-refl {f = e₂₃ s q}
      k₀ .Bd₂.keeps s (inj₂ (inj₂ _)) = ≈-refl {f = r₂ s}
      k₀ .Bd₂.blind s w = ≈-refl {f = M.εₘ}

    Φ₃₁ : M.Matrix m₃ m
    Φ₃₁ = from-inputs₃ M.+ₘ (from-root₁ ∘ c₁)

    P₂ : (t : Path⁺ B₃ ⊎ Root) → M.Matrix (vertex-width E (tgt t)) n₂
    P₂ (inj₁ q) = into⁺ B₃ q ∘ from-root₂
    P₂ (inj₂ _) = up₂

    K₂ : (t : Path⁺ B₃ ⊎ Root) → M.Matrix (vertex-width E (tgt t)) m
    K₂ (inj₁ q) = into⁺ B₃ q ∘ Φ₃₁
    K₂ (inj₂ _) = out-root M.+ₘ (up₁ ∘ c₁)

    module S2 = HidePremise (vertex-width E) (inj₁ input) b2 tgt inputs₂ P₂ K₂

    H₂⁰ : S2.St
    H₂⁰ .S2.into q = into⁺ B₂ q
    H₂⁰ .S2.inside p q = inside⁺ B₂ p q

    start₂ : S2.Start G₁ H₂⁰
    start₂ .S2.into-start q = keeps₁ .Fz.keeps input q
    start₂ .S2.inside-start p q = behind₂ .Bd₂.keeps p (inj₁ q)
    start₂ .S2.tgt-start (inj₁ q) =
      ≈-trans (done₁ .S1.tgt-ok (inj₁ q)) (factor (into⁺ B₃ q) from-inputs₃ from-root₁ inputs₁ κ₁)
    start₂ .S2.tgt-start (inj₂ _) =
      ≈-trans (done₁ .S1.tgt-ok (inj₂ root))
              (M.+ₘ-cong ≈-refl (∘-cong₂ (∘-cong₁ κ₁)))
    start₂ .S2.up-start (inj₁ q) = behind₂ .Bd₂.keeps (inj₂ root) (inj₂ (inj₁ q))
    start₂ .S2.up-start (inj₂ _) = behind₂ .Bd₂.keeps (inj₂ root) (inj₂ (inj₂ root))
    start₂ .S2.off-start (inj₁ q) p = behind₂ .Bd₂.keeps (inj₁ p) (inj₂ (inj₁ q))
    start₂ .S2.off-start (inj₂ _) p = behind₂ .Bd₂.keeps (inj₁ p) (inj₂ (inj₂ root))
    start₂ .S2.sink q = ≈-refl {f = M.εₘ}

    G₂ : Relation (vertex-width E)
    G₂ = hide-all (vertex-width E) (hide (vertex-width E) G₁ (b2 (inj₂ root))) (map (λ w → b2 (inj₁ w)) ps₂)

    H₂ : S2.St
    H₂ = S2.steps (S2.step H₂⁰ (inj₂ root)) (map inj₁ ps₂)

    done₂ : S2.Agrees G₂ H₂
    done₂ = S2.agrees-hide-all ps₂ (S2.agrees-start start₂)

    prem₂ : Relation (vertex-width B₂) → S2.St
    prem₂ G .S2.into q = G (inj₁ input) (inj₂ q)
    prem₂ G .S2.inside p q = G (inj₂ p) (inj₂ q)

    κ₂ : H₂ .S2.into (inj₂ root) ≈ collapse B₂
    κ₂ =
      ≈-trans (≈-of-≡ (≡-cong (λ H → H .S2.into (inj₂ root))
                              (S2.folds prem₂ inj₂ (hide (vertex-width B₂)) (λ G w → ≡-refl)
                                        (paths⁺ B₂) (gr B₂))))
              (hide-paths⁺ B₂)

    hid₁₂ : Path⁺ B₁ ⊎ Path⁺ B₂ → V E
    hid₁₂ (inj₁ q) = b1 q
    hid₁₂ (inj₂ q) = b2 q

    cols₃ : Path⁺ B₃ ⊎ Root → V E
    cols₃ = tgt

    Bh₃ : (s : Path⁺ B₃) (t : Path⁺ B₃ ⊎ Root) → M.Matrix (vertex-width E (cols₃ t)) (width⁺ B₃ s)
    Bh₃ s (inj₁ q) = inside⁺ B₃ s q
    Bh₃ s (inj₂ _) = r₃ s

    module Bd₃ = Behind (vertex-width E) hid₁₂ b3 cols₃ Bh₃

    behind₃ : Bd₃.Keeps G₂
    behind₃ =
      Bd₃.keeps-hide-all (λ w → inj₂ (inj₁ w)) ps₂
        (Bd₃.keeps-hide (inj₂ (inj₂ root))
          (Bd₃.keeps-hide-all (λ w → inj₁ (inj₁ w)) ps₁
            (Bd₃.keeps-hide (inj₁ (inj₂ root)) k₀)))
      where
      k₀ : Bd₃.Keeps (gr E)
      k₀ .Bd₃.keeps s (inj₁ q) = ≈-refl
      k₀ .Bd₃.keeps s (inj₂ _) = ≈-refl {f = r₃ s}
      k₀ .Bd₃.blind s (inj₁ w) = ≈-refl {f = M.εₘ}
      k₀ .Bd₃.blind s (inj₂ w) = ≈-refl {f = M.εₘ}

  Φ₃ : M.Matrix m₃ m
  Φ₃ = inputs₃ ∘ M.⟨ M.⟨ M.I , c₁ ⟩ , c₂ ⟩

  private
    Φ₃' : M.Matrix m₃ m
    Φ₃' = Φ₃₁ M.+ₘ (from-root₂ ∘ c₂)

    Φ₃-split : Φ₃' ≈ Φ₃
    Φ₃-split =
      ≈-sym (≈-trans (M.∘-pair inputs₃ M.⟨ M.I , c₁ ⟩ c₂)
                     (M.+ₘ-cong (≈-trans (M.∘-pair (inputs₃ ∘ M.in₁ {m + n₁} {n₂}) M.I c₁)
                                         (M.+ₘ-cong (id-right {f = from-inputs₃}) (≈-refl {f = from-root₁ ∘ c₁})))
                                (≈-refl {f = from-root₂ ∘ c₂})))

    P₃ : (t : Root) → M.Matrix n n₃
    P₃ _ = up₃

    K₃ : (t : Root) → M.Matrix n m
    K₃ _ = (out-root M.+ₘ (up₁ ∘ c₁)) M.+ₘ (up₂ ∘ c₂)

    module S3 = HidePremise (vertex-width E) (inj₁ input) b3 (λ (_ : Root) → er) Φ₃' P₃ K₃

    H₃⁰ : S3.St
    H₃⁰ .S3.into q = into⁺ B₃ q
    H₃⁰ .S3.inside p q = inside⁺ B₃ p q

    start₃ : S3.Start G₂ H₃⁰
    start₃ .S3.into-start q =
      ≈-trans (done₂ .S2.tgt-ok (inj₁ q)) (factor (into⁺ B₃ q) Φ₃₁ from-root₂ inputs₂ κ₂)
    start₃ .S3.inside-start p q = behind₃ .Bd₃.keeps p (inj₁ q)
    start₃ .S3.tgt-start _ =
      ≈-trans (done₂ .S2.tgt-ok (inj₂ root))
              (M.+ₘ-cong ≈-refl (∘-cong₂ (∘-cong₁ κ₂)))
    start₃ .S3.up-start _ = behind₃ .Bd₃.keeps (inj₂ root) (inj₂ root)
    start₃ .S3.off-start _ p = behind₃ .Bd₃.keeps (inj₁ p) (inj₂ root)
    start₃ .S3.sink q = ≈-refl {f = M.εₘ}

    G₃ : Relation (vertex-width E)
    G₃ = hide-all (vertex-width E) (hide (vertex-width E) G₂ (b3 (inj₂ root))) (map (λ w → b3 (inj₁ w)) ps₃)

    H₃ : S3.St
    H₃ = S3.steps (S3.step H₃⁰ (inj₂ root)) (map inj₁ ps₃)

    done₃ : S3.Agrees G₃ H₃
    done₃ = S3.agrees-hide-all ps₃ (S3.agrees-start start₃)

    prem₃ : Relation (vertex-width B₃) → S3.St
    prem₃ G .S3.into q = G (inj₁ input) (inj₂ q)
    prem₃ G .S3.inside p q = G (inj₂ p) (inj₂ q)

    κ₃ : H₃ .S3.into (inj₂ root) ≈ collapse B₃
    κ₃ =
      ≈-trans (≈-of-≡ (≡-cong (λ H → H .S3.into (inj₂ root))
                              (S3.folds prem₃ inj₂ (hide (vertex-width B₃)) (λ G w → ≡-refl)
                                        (paths⁺ B₃) (gr B₃))))
              (hide-paths⁺ B₃)

    l₁ l₂ l₃ : List (V E)
    l₁ = b1 (inj₂ root) ∷ map (λ w → b1 (inj₁ w)) ps₁
    l₂ = b2 (inj₂ root) ∷ map (λ w → b2 (inj₁ w)) ps₂
    l₃ = b3 (inj₂ root) ∷ map (λ w → b3 (inj₁ w)) ps₃

    lst : map (λ q → inj₂ {A = Input} (inj₁ q)) (vertices (Graph.shape E)) ≡ l₁ ++ (l₂ ++ l₃)
    lst =
      ≡-trans (map-++ (λ q → inj₂ (inj₁ q)) (map inj₁ (paths⁺ B₁))
                      (map inj₂ (map inj₁ (paths⁺ B₂) ++ map inj₂ (paths⁺ B₃))))
              (≡-cong₂ _++_
                (≡-trans (map-map (λ q → inj₂ (inj₁ q)) inj₁ (paths⁺ B₁))
                         (≡-cong (b1 (inj₂ root) ∷_) (map-map b1 inj₁ ps₁)))
                (≡-trans (map-map (λ q → inj₂ (inj₁ q)) inj₂
                                  (map inj₁ (paths⁺ B₂) ++ map inj₂ (paths⁺ B₃)))
                (≡-trans (map-++ (λ q → inj₂ (inj₁ (inj₂ q))) (map inj₁ (paths⁺ B₂))
                                 (map inj₂ (paths⁺ B₃)))
                         (≡-cong₂ _++_
                           (≡-trans (map-map (λ q → inj₂ (inj₁ (inj₂ q))) inj₁ (paths⁺ B₂))
                                    (≡-cong (b2 (inj₂ root) ∷_) (map-map b2 inj₁ ps₂)))
                           (≡-trans (map-map (λ q → inj₂ (inj₁ (inj₂ q))) inj₂ (paths⁺ B₃))
                                    (≡-cong (b3 (inj₂ root) ∷_) (map-map b3 inj₁ ps₃)))))))

    plumb : collapse E ≡ G₃ (inj₁ input) er
    plumb =
      ≡-trans (≡-cong (λ l → hide-all (vertex-width E) (gr E) l (inj₁ input) er) lst)
              (≡-trans (≡-cong (λ G → G (inj₁ input) er)
                               (hide-all-++ (vertex-width E) (gr E) l₁ (l₂ ++ l₃)))
                       (≡-cong (λ G → G (inj₁ input) er)
                               (hide-all-++ (vertex-width E) G₁ l₂ l₃)))

  agree : collapse E
          ≈ (((out-root M.+ₘ (up₁ ∘ c₁)) M.+ₘ (up₂ ∘ c₂)) M.+ₘ (up₃ ∘ (collapse B₃ ∘ Φ₃)))
  agree =
    ≈-trans (≈-of-≡ plumb)
            (≈-trans (done₃ .S3.tgt-ok root)
                     (M.+ₘ-cong ≈-refl (∘-cong₂ (∘-cong κ₃ Φ₃-split))))
