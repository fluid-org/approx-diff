{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.Bool using (Bool; true; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map; foldl; filterᵇ)
open import Data.List.Properties using (map-++; map-∘; foldl-++)
open import Data.List.Relation.Unary.All using (All; []; _∷_; universal) renaming (map to All-map)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_) renaming (map to AllPairs-map)
import Data.List.Relation.Unary.All.Properties as AllP
import Data.List.Relation.Unary.AllPairs.Properties as AllPairsP
open import Data.Nat using (ℕ; _+_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
import Data.List.Relation.Binary.Permutation.Propositional as ↭
open ↭ using (_↭_)
open import Data.Unit using (tt) renaming (⊤ to Unit)

open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; cong to ≡-cong; cong₂ to ≡-cong₂)
open import Relation.Nullary.Decidable using (yes)
import Data.Sum.Properties as SumP
open import Level using (0ℓ)
open import prop using (Prf; ⟪_⟫; _∧_; _,_; proj₁; proj₂)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import basics using (IsStrictOrder)
import matrix

-- A dependence graph as a value rather than a family indexed by a derivation: a graph is a set of
-- interior vertices with widths, a distinguished root of given width, and the dependence relation
-- between each pair. The root has no outgoing relation, so it is a sink by construction.
module interaction.graph {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (let module Semiring = CommutativeSemiring S) (+-idem : ∀ x → (x Semiring.+ x) Semiring.≈ x) where

private
  module M = matrix.Mat S

open Semiring using (Carrier; +-cong; +-assoc; +-comm; +-lunit; +-runit; ·-cong; ε-annihilₗ; ε-annihilᵣ)
  renaming (_≈_ to _≈ₛ_; refl to ≈ₛ-refl; sym to ≈ₛ-sym; trans to ≈ₛ-trans; _+_ to _+ₛ_; _·_ to _·ₛ_; ε to εₛ)
open import categories using (Category)
open Category M.cat
  using (_∘_; _≈_; ∘-cong; ∘-cong₁; ∘-cong₂; assoc; id-left; id-right; ≈-refl; ≈-sym; ≈-trans; ≡-to-≈)

data Input : Set where
  input : Input

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
  vertices-of (s ∷ t ∷ ss) = map inj₁ (inj₂ root ∷ map inj₁ (vertices s)) ++ map inj₂ (vertices-of (t ∷ ss))

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

sum-< : {A B : Set} → (A → A → Set) → (B → B → Set) → A ⊎ B → A ⊎ B → Set
sum-< R S (inj₁ p) (inj₁ q) = R p q
sum-< R S (inj₁ _) (inj₂ _) = Unit
sum-< R S (inj₂ _) (inj₁ _) = ⊥
sum-< R S (inj₂ p) (inj₂ q) = S p q

none-order : {A : Set} → IsStrictOrder {A = A} (λ _ _ → ⊥)
none-order .IsStrictOrder.trans _ _ _ ()
none-order .IsStrictOrder.asym _ _ ()

sum-<-order : {A B : Set} {R : A → A → Set} {S : B → B → Set} →
              IsStrictOrder R → IsStrictOrder S → IsStrictOrder (sum-< R S)
sum-<-order o₁ o₂ .IsStrictOrder.trans (inj₁ p) (inj₁ q) (inj₁ r) a b = o₁ .IsStrictOrder.trans p q r a b
sum-<-order o₁ o₂ .IsStrictOrder.trans (inj₁ p) (inj₁ q) (inj₂ r) a b = tt
sum-<-order o₁ o₂ .IsStrictOrder.trans (inj₁ p) (inj₂ q) (inj₁ r) a ()
sum-<-order o₁ o₂ .IsStrictOrder.trans (inj₁ p) (inj₂ q) (inj₂ r) a b = tt
sum-<-order o₁ o₂ .IsStrictOrder.trans (inj₂ p) (inj₁ q) r        () b
sum-<-order o₁ o₂ .IsStrictOrder.trans (inj₂ p) (inj₂ q) (inj₁ r) a ()
sum-<-order o₁ o₂ .IsStrictOrder.trans (inj₂ p) (inj₂ q) (inj₂ r) a b = o₂ .IsStrictOrder.trans p q r a b
sum-<-order o₁ o₂ .IsStrictOrder.asym (inj₁ p) (inj₁ q) a b = o₁ .IsStrictOrder.asym p q a b
sum-<-order o₁ o₂ .IsStrictOrder.asym (inj₁ p) (inj₂ q) a ()
sum-<-order o₁ o₂ .IsStrictOrder.asym (inj₂ p) (inj₁ q) () b
sum-<-order o₁ o₂ .IsStrictOrder.asym (inj₂ p) (inj₂ q) a b = o₂ .IsStrictOrder.asym p q a b

-- The completion order: a premise's interior before its result, and every premise before those
-- after it. The shape is explicit, since it cannot be recovered from a vertex.
mutual
  lt : (s : Shape) → Vertex s → Vertex s → Set
  lt (node ss) = lts ss

  lts : (ss : List Shape) → Vertices ss → Vertices ss → Set
  lts []           ()
  lts (s ∷ [])     = sum-< (lt s) (λ _ _ → ⊥)
  lts (s ∷ t ∷ ss) = sum-< (sum-< (lt s) (λ _ _ → ⊥)) (lts (t ∷ ss))

mutual
  lt-order : (s : Shape) → IsStrictOrder (lt s)
  lt-order (node ss) = lts-order ss

  lts-order : (ss : List Shape) → IsStrictOrder (lts ss)
  lts-order []           .IsStrictOrder.trans ()
  lts-order []           .IsStrictOrder.asym ()
  lts-order (s ∷ [])     = sum-<-order (lt-order s) none-order
  lts-order (s ∷ t ∷ ss) = sum-<-order (sum-<-order (lt-order s) none-order) (lts-order (t ∷ ss))

record Graph (m n : ℕ) : Set₁ where
  field
    shape   : Shape
    width   : Vertex shape → ℕ
    fo      : Vertex shape → Bool
    into    : (q : Vertex shape) → M.Matrix (width q) m
    inside  : (p q : Vertex shape) → M.Matrix (width q) (width p)
    -- Every non-zero entry between interior vertices runs strictly forward in the completion order.
    -- The inputs and the root need no condition, being below and above everything.
    <-inside : ∀ p q (k : Fin (width q)) (l : Fin (width p)) →
               lt shape p q ⊎ Prf (inside p q k l ≈ₛ εₛ)
    fo-root : Bool
    out     : M.Matrix n m
    up      : (p : Vertex shape) → M.Matrix n (width p)

Relation : {V : Set} → (V → ℕ) → Set
Relation {V} vertex-width = (x y : V) → M.Matrix (vertex-width y) (vertex-width x)

hide : {V : Set} (vertex-width : V → ℕ) → Relation vertex-width → V → Relation vertex-width
hide vertex-width G r x y = G x y M.+ₘ (G r y ∘ G x r)

hide-all : {V : Set} (vertex-width : V → ℕ) → Relation vertex-width → List V → Relation vertex-width
hide-all vertex-width = foldl (hide vertex-width)

flip : {V : Set} {vertex-width : V → ℕ} → Relation vertex-width → Relation vertex-width
flip G x y = (G y x) M.ᵀ

_≐_ : {V : Set} {vertex-width : V → ℕ} → Relation vertex-width → Relation vertex-width → Prop
_≐_ {V} G G' = ∀ x y → G x y ≈ G' x y

hide-cong : {V : Set} (vertex-width : V → ℕ) {G G' : Relation vertex-width} (r : V) →
            G ≐ G' → hide vertex-width G r ≐ hide vertex-width G' r
hide-cong vertex-width r e x y = M.+ₘ-cong (e x y) (∘-cong (e r y) (e x r))

flip-hide : {V : Set} (vertex-width : V → ℕ) (G : Relation vertex-width) (r : V) →
            hide vertex-width (flip G) r ≐ flip (hide vertex-width G r)
flip-hide vertex-width G r x y = M.+ₘ-cong ≈-refl (≈-sym (M.ᵀ-∘ (G r x) (G y r)))

hide-all-cong : {V : Set} (vertex-width : V → ℕ) {G G' : Relation vertex-width} (rs : List V) →
                G ≐ G' → hide-all vertex-width G rs ≐ hide-all vertex-width G' rs
hide-all-cong vertex-width []       e = e
hide-all-cong vertex-width (r ∷ rs) e = hide-all-cong vertex-width rs (hide-cong vertex-width r e)

hide-sink : {V : Set} (vertex-width : V → ℕ) (G : Relation vertex-width) (r : V) →
            (∀ y → G r y ≈ M.εₘ) → hide vertex-width G r ≐ G
hide-sink vertex-width G r z x y = ≈-trans (M.+ₘ-cong ≈-refl (∘-cong₁ (z y))) (M.absorb₁ (G x y) (G x r))

module Hide (V : Set) (w : V → ℕ) where
  Gr : Set
  Gr = Relation w

  h : Gr → V → Gr
  h = hide w

  private
    absorbˡ : ∀ a b → (a +ₛ (a +ₛ b)) ≈ₛ (a +ₛ b)
    absorbˡ a b = ≈ₛ-trans (≈ₛ-sym +-assoc) (+-cong (+-idem a) ≈ₛ-refl)

    absorbʳ : ∀ a b → (a +ₛ (b +ₛ a)) ≈ₛ (b +ₛ a)
    absorbʳ a b = ≈ₛ-trans (+-cong ≈ₛ-refl +-comm) (≈ₛ-trans (absorbˡ a b) +-comm)

    absorb-mono : ∀ x y z → x ≈ₛ (y +ₛ x) → (z +ₛ y) ≈ₛ y → x ≈ₛ (z +ₛ x)
    absorb-mono x y z p q =
      ≈ₛ-trans p (≈ₛ-trans (+-cong (≈ₛ-sym q) ≈ₛ-refl) (≈ₛ-trans +-assoc (+-cong ≈ₛ-refl (≈ₛ-sym p))))

    shift : ∀ a s c → ((a +ₛ s) +ₛ c) ≈ₛ ((a +ₛ c) +ₛ s)
    shift a s c = ≈ₛ-trans +-assoc (≈ₛ-trans (+-cong ≈ₛ-refl +-comm) (≈ₛ-sym +-assoc))

    insert : ∀ a b c → (a +ₛ b) ≈ₛ b → (b +ₛ c) ≈ₛ (b +ₛ (a +ₛ c))
    insert a b c q = ≈ₛ-sym (≈ₛ-trans (≈ₛ-sym +-assoc) (+-cong (≈ₛ-trans +-comm q) ≈ₛ-refl))

    Σ-zero : ∀ {n} (f : Fin n → Carrier) → (∀ k → f k ≈ₛ εₛ) → M.Σ f ≈ₛ εₛ
    Σ-zero {n} f z = ≈ₛ-trans (M.Σ-cong z) (M.Σ-ε {n})

  zero-fold : ∀ {G : Gr} rs r₀ →
              (((z : V) (i : Fin (w z)) (j : Fin (w r₀)) → G r₀ z i j ≈ₛ εₛ) ∧
               ((z : V) (i : Fin (w r₀)) (j : Fin (w z)) → G z r₀ i j ≈ₛ εₛ)) →
              (((z : V) (i : Fin (w z)) (j : Fin (w r₀)) → foldl h G rs r₀ z i j ≈ₛ εₛ) ∧
               ((z : V) (i : Fin (w r₀)) (j : Fin (w z)) → foldl h G rs z r₀ i j ≈ₛ εₛ))
  zero-fold []           r₀ zz        = zz
  zero-fold {G} (r ∷ rs) r₀ (zr , zc) = zero-fold {h G r} rs r₀ (zr' , zc')
    where
    zr' : (z : V) (i : Fin (w z)) (j : Fin (w r₀)) → h G r r₀ z i j ≈ₛ εₛ
    zr' z i j =
      ≈ₛ-trans (+-cong (zr z i j)
                 (Σ-zero (λ k → G r z i k ·ₛ G r₀ r k j)
                         (λ k → ≈ₛ-trans (·-cong ≈ₛ-refl (zr r k j)) ε-annihilᵣ)))
               +-lunit

    zc' : (z : V) (i : Fin (w r₀)) (j : Fin (w z)) → h G r z r₀ i j ≈ₛ εₛ
    zc' z i j =
      ≈ₛ-trans (+-cong (zc z i j)
                 (Σ-zero (λ k → G r r₀ i k ·ₛ G z r k j)
                         (λ k → ≈ₛ-trans (·-cong (zc r i k) ≈ₛ-refl) ε-annihilₗ)))
               +-lunit

  increasing : ∀ {G : Gr} rs x y (i : Fin (w y)) (j : Fin (w x)) →
               foldl h G rs x y i j ≈ₛ (G x y i j +ₛ foldl h G rs x y i j)
  increasing {G} []       x y i j = ≈ₛ-sym (+-idem (G x y i j))
  increasing {G} (r ∷ rs) x y i j =
    absorb-mono (foldl h (h G r) rs x y i j) (h G r x y i j) (G x y i j)
                (increasing {h G r} rs x y i j)
                (absorbˡ (G x y i j) ((G r y ∘ G x r) i j))

  h-cong : ∀ {G G'} r → G ≐ G' → h G r ≐ h G' r
  h-cong = hide-cong w

  fold-cong : ∀ {G G'} rs → G ≐ G' → foldl h G rs ≐ foldl h G' rs
  fold-cong = hide-all-cong w

  add-inert : ∀ {G T : Gr} rs →
              All (λ r → Prf (((z : V) (i : Fin (w z)) (j : Fin (w r)) → T r z i j ≈ₛ εₛ)
                            ∧ ((z : V) (i : Fin (w r)) (j : Fin (w z)) → T z r i j ≈ₛ εₛ))) rs →
              ∀ x y (i : Fin (w y)) (j : Fin (w x)) →
              foldl h (λ x' y' → G x' y' M.+ₘ T x' y') rs x y i j ≈ₛ
              (foldl h G rs x y i j +ₛ T x y i j)
  add-inert []               []                   x y i j = ≈ₛ-refl
  add-inert {G} {T} (r ∷ rs) (⟪ (zr , zc) ⟫ ∷ zs) x y i j =
    ≈ₛ-trans (fold-cong rs step x y i j) (add-inert {h G r} {T} rs zs x y i j)
    where
    step : h (λ x' y' → G x' y' M.+ₘ T x' y') r ≐ (λ x' y' → h G r x' y' M.+ₘ T x' y')
    step x' y' i' j' =
      ≈ₛ-trans
        (+-cong ≈ₛ-refl
          (M.Σ-cong (λ k → ·-cong
            (≈ₛ-trans (+-cong ≈ₛ-refl (zr y' i' k)) +-runit)
            (≈ₛ-trans (+-cong ≈ₛ-refl (zc x' k j')) +-runit))))
        (shift (G x' y' i' j') (T x' y' i' j') ((G r y' ∘ G x' r) i' j'))

  agree-add : ∀ {G G' : Gr} rs →
              (∀ x y (i : Fin (w y)) (j : Fin (w x)) → (G x y i j +ₛ G' x y i j) ≈ₛ G' x y i j) →
              All (λ r → Prf (((z : V) (i : Fin (w z)) (j : Fin (w r)) → G' r z i j ≈ₛ G r z i j)
                            ∧ ((z : V) (i : Fin (w r)) (j : Fin (w z)) → G' z r i j ≈ₛ G z r i j))) rs →
              ∀ x y (i : Fin (w y)) (j : Fin (w x)) →
              foldl h G' rs x y i j ≈ₛ (G' x y i j +ₛ foldl h G rs x y i j)
  agree-add {G} {G'} []       sub _                   x y i j = ≈ₛ-sym (≈ₛ-trans +-comm (sub x y i j))
  agree-add {G} {G'} (r ∷ rs) sub (⟪ (ar , ac) ⟫ ∷ as) x y i j =
    ≈ₛ-trans (agree-add {h G r} {h G' r} rs sub' all' x y i j)
    (≈ₛ-trans (+-cong (step x y i j) ≈ₛ-refl)
    (≈ₛ-trans +-assoc
              (+-cong ≈ₛ-refl (≈ₛ-sym (increasing {h G r} rs x y i j)))))
    where
    step : ∀ x' y' (i' : Fin (w y')) (j' : Fin (w x')) →
           h G' r x' y' i' j' ≈ₛ (G' x' y' i' j' +ₛ h G r x' y' i' j')
    step x' y' i' j' =
      ≈ₛ-trans
        (+-cong ≈ₛ-refl (M.Σ-cong (λ k → ·-cong (ar y' i' k) (ac x' k j'))))
        (insert (G x' y' i' j') (G' x' y' i' j') ((G r y' ∘ G x' r) i' j') (sub x' y' i' j'))

    sub' : ∀ x' y' (i' : Fin (w y')) (j' : Fin (w x')) →
           (h G r x' y' i' j' +ₛ h G' r x' y' i' j') ≈ₛ h G' r x' y' i' j'
    sub' x' y' i' j' =
      ≈ₛ-trans (+-cong ≈ₛ-refl (step x' y' i' j'))
      (≈ₛ-trans (absorbʳ (h G r x' y' i' j') (G' x' y' i' j')) (≈ₛ-sym (step x' y' i' j')))

    all' : All (λ r' → Prf (((z : V) (i' : Fin (w z)) (j' : Fin (w r')) →
                             h G' r r' z i' j' ≈ₛ h G r r' z i' j')
                          ∧ ((z : V) (i' : Fin (w r')) (j' : Fin (w z)) →
                             h G' r z r' i' j' ≈ₛ h G r z r' i' j'))) rs
    all' = All-map
      (λ {r'} pq →
        ⟪
          (λ z i' j' → ≈ₛ-trans (step r' z i' j')
                       (≈ₛ-trans (+-cong (proj₁ (Prf.prf pq) z i' j') ≈ₛ-refl)
                                 (absorbˡ (G r' z i' j') ((G r z ∘ G r' r) i' j')))) ,
          (λ z i' j' → ≈ₛ-trans (step z r' i' j')
                       (≈ₛ-trans (+-cong (proj₂ (Prf.prf pq) z i' j') ≈ₛ-refl)
                                 (absorbˡ (G z r' i' j') ((G r r' ∘ G z r) i' j')))) ⟫)
      as

module Ordered {V : Set} (vertex-width : V → ℕ) (_<_ : V → V → Set) (o : IsStrictOrder _<_) where

  open IsStrictOrder o using (trans; asym)

  Fwd : Relation vertex-width → Set
  Fwd G = ∀ x y (i : Fin (vertex-width y)) (j : Fin (vertex-width x)) → (x < y) ⊎ Prf (G x y i j ≈ₛ εₛ)

  private
    ⊥-elimₚ : ∀ {P : Prop} → ⊥ → P
    ⊥-elimₚ ()

    Σ-or : ∀ {n} (f : Fin n → Carrier) {P : Set} → (∀ k → P ⊎ Prf (f k ≈ₛ εₛ)) → P ⊎ Prf (M.Σ f ≈ₛ εₛ)
    Σ-or {ℕ.zero}  f h = inj₂ ⟪ ≈ₛ-refl ⟫
    Σ-or {ℕ.suc n} f h with h Fin.zero | Σ-or (λ k → f (Fin.suc k)) (λ k → h (Fin.suc k))
    ... | inj₁ p     | _            = inj₁ p
    ... | inj₂ _     | inj₁ p       = inj₁ p
    ... | inj₂ ⟪ z ⟫ | inj₂ ⟪ zs ⟫ = inj₂ ⟪ ≈ₛ-trans (+-cong z zs) +-lunit ⟫

    term : ∀ {G} → Fwd G → ∀ r x y (i : Fin (vertex-width y)) (j : Fin (vertex-width x)) k →
           (x < y) ⊎ Prf ((G r y i k ·ₛ G x r k j) ≈ₛ εₛ)
    term fwd r x y i j k with fwd r y i k | fwd x r k j
    ... | inj₁ a     | inj₁ b     = inj₁ (trans x r y b a)
    ... | inj₂ ⟪ e ⟫ | _          = inj₂ ⟪ ≈ₛ-trans (·-cong e ≈ₛ-refl) ε-annihilₗ ⟫
    ... | inj₁ _     | inj₂ ⟪ e ⟫ = inj₂ ⟪ ≈ₛ-trans (·-cong ≈ₛ-refl e) ε-annihilᵣ ⟫

  fwd-hide : ∀ {G} r → Fwd G → Fwd (hide vertex-width G r)
  fwd-hide {G} r fwd x y i j with fwd x y i j | Σ-or (λ k → G r y i k ·ₛ G x r k j) (term fwd r x y i j)
  ... | inj₁ a     | _            = inj₁ a
  ... | inj₂ _     | inj₁ a       = inj₁ a
  ... | inj₂ ⟪ z ⟫ | inj₂ ⟪ zs ⟫ = inj₂ ⟪ ≈ₛ-trans (+-cong z zs) +-lunit ⟫

  fwd-hide-all : ∀ {G} rs → Fwd G → Fwd (hide-all vertex-width G rs)
  fwd-hide-all []       fwd = fwd
  fwd-hide-all (r ∷ rs) fwd = fwd-hide-all rs (fwd-hide r fwd)

  private
    cycle : ∀ {G} → Fwd G → ∀ r r' → (G r' r ∘ G r r') ≈ M.εₘ
    cycle {G} fwd r r' i j = ≈ₛ-trans (M.Σ-cong term') (M.Σ-ε {vertex-width r'})
      where
      term' : ∀ k → (G r' r i k ·ₛ G r r' k j) ≈ₛ εₛ
      term' k with fwd r' r i k | fwd r r' k j
      ... | inj₁ a     | inj₁ b     = ⊥-elimₚ (asym r' r a b)
      ... | inj₂ ⟪ e ⟫ | _          = ≈ₛ-trans (·-cong e ≈ₛ-refl) ε-annihilₗ
      ... | inj₁ _     | inj₂ ⟪ e ⟫ = ≈ₛ-trans (·-cong ≈ₛ-refl e) ε-annihilᵣ

    both : ∀ (G : Relation vertex-width) r r' x y → M.Matrix (vertex-width y) (vertex-width x)
    both G r r' x y =
      (G x y M.+ₘ (G r y ∘ G x r)) M.+ₘ
      (((G r' y ∘ G x r') M.+ₘ (G r' y ∘ (G r r' ∘ G x r))) M.+ₘ ((G r y ∘ G r' r) ∘ G x r'))

    expand : ∀ {G} → Fwd G → ∀ r r' x y → hide vertex-width (hide vertex-width G r) r' x y ≈ both G r r' x y
    expand {G} fwd r r' x y =
      ≈-trans (M.+ₘ-cong ≈-refl (M.comp-bilinear₁ (G r' y) (G r y ∘ G r' r) (G x r' M.+ₘ (G r r' ∘ G x r))))
      (≈-trans (M.+ₘ-cong ≈-refl (M.+ₘ-cong (M.comp-bilinear₂ (G r' y) (G x r') (G r r' ∘ G x r))
                                            (M.comp-bilinear₂ (G r y ∘ G r' r) (G x r') (G r r' ∘ G x r))))
               (M.+ₘ-cong ≈-refl (M.+ₘ-cong ≈-refl
                 (≈-trans (M.+ₘ-cong ≈-refl vanish) (M.+ₘ-runit ((G r y ∘ G r' r) ∘ G x r'))))))
      where
      vanish : ((G r y ∘ G r' r) ∘ (G r r' ∘ G x r)) ≈ M.εₘ
      vanish =
        ≈-trans (assoc (G r y) (G r' r) (G r r' ∘ G x r))
        (≈-trans (∘-cong₂ (≈-sym (assoc (G r' r) (G r r') (G x r))))
        (≈-trans (∘-cong₂ (∘-cong₁ (cycle fwd r r')))
        (≈-trans (∘-cong₂ (M.comp-bilinear-ε₁ {m = vertex-width r} (G x r)))
                 (M.comp-bilinear-ε₂ {k = vertex-width x} (G r y)))))

    swap : ∀ G r r' x y → both G r r' x y ≈ both G r' r x y
    swap G r r' x y =
      ≈-trans (M.+ₘ-assoc a b ((c M.+ₘ d) M.+ₘ e))
      (≈-trans (M.+ₘ-cong ≈-refl (M.+ₘ-cong ≈-refl (M.+ₘ-assoc c d e)))
      (≈-trans (M.+ₘ-cong ≈-refl (M.+ₘ-swap-mid b c (d M.+ₘ e)))
      (≈-trans (M.+ₘ-cong ≈-refl (M.+ₘ-cong ≈-refl (M.+ₘ-cong ≈-refl (M.+ₘ-comm d e))))
      (≈-trans (M.+ₘ-cong ≈-refl (M.+ₘ-cong ≈-refl (≈-sym (M.+ₘ-assoc b e d))))
      (≈-trans (≈-sym (M.+ₘ-assoc a c ((b M.+ₘ e) M.+ₘ d)))
               (M.+ₘ-cong ≈-refl (M.+ₘ-cong (M.+ₘ-cong ≈-refl (assoc (G r y) (G r' r) (G x r')))
                                             (≈-sym (assoc (G r' y) (G r r') (G x r))))))))))
      where
      a = G x y
      b = G r y ∘ G x r
      c = G r' y ∘ G x r'
      d = G r' y ∘ (G r r' ∘ G x r)
      e = (G r y ∘ G r' r) ∘ G x r'

    comm : ∀ {G} → Fwd G → ∀ r r' →
           hide vertex-width (hide vertex-width G r) r' ≐ hide vertex-width (hide vertex-width G r') r
    comm {G} fwd r r' x y =
      ≈-trans (expand fwd r r' x y) (≈-trans (swap G r r' x y) (≈-sym (expand fwd r' r x y)))

  hide-all-perm : ∀ {G rs rs'} → Fwd G → rs ↭ rs' → hide-all vertex-width G rs ≐ hide-all vertex-width G rs'
  hide-all-perm fwd ↭.refl x y = ≈-refl
  hide-all-perm fwd (↭.prep r p) = hide-all-perm (fwd-hide r fwd) p
  hide-all-perm fwd (↭.swap {xs = rs} a b p) x y =
    ≈-trans (hide-all-cong vertex-width rs (comm fwd a b) x y)
            (hide-all-perm (fwd-hide a (fwd-hide b fwd)) p x y)
  hide-all-perm fwd (↭.trans p q) x y = ≈-trans (hide-all-perm fwd p x y) (hide-all-perm fwd q x y)

module _ {m n : ℕ} (B : Graph m n) where
  open Graph B

  Path⁺ : Set
  Path⁺ = Vertex shape ⊎ Root

  width⁺ : Path⁺ → ℕ
  width⁺ = [ width , (λ _ → n) ]

  fo⁺ : Path⁺ → Bool
  fo⁺ = [ fo , (λ _ → fo-root) ]

  into⁺ : (q : Path⁺) → M.Matrix (width⁺ q) m
  into⁺ (inj₁ q) = into q
  into⁺ (inj₂ _) = out

  up-root⁺ : ∀ {k} → M.Matrix k n → (q : Path⁺) → M.Matrix k (width⁺ q)
  up-root⁺ u (inj₁ _) = M.εₘ
  up-root⁺ u (inj₂ _) = u

  inside⁺ : (p q : Path⁺) → M.Matrix (width⁺ q) (width⁺ p)
  inside⁺ (inj₁ p) (inj₁ q) = inside p q
  inside⁺ (inj₁ p) (inj₂ _) = up p
  inside⁺ (inj₂ _) _        = M.εₘ

  _<⁺_ : Path⁺ → Path⁺ → Set
  _<⁺_ = lts (shape ∷ [])

  <⁺-order : IsStrictOrder _<⁺_
  <⁺-order = lts-order (shape ∷ [])

  <⁺-inside : ∀ p q (k : Fin (width⁺ q)) (l : Fin (width⁺ p)) → (p <⁺ q) ⊎ Prf (inside⁺ p q k l ≈ₛ εₛ)
  <⁺-inside (inj₁ p) (inj₁ q) k l = <-inside p q k l
  <⁺-inside (inj₁ p) (inj₂ _) k l = inj₁ tt
  <⁺-inside (inj₂ _) q        k l = inj₂ ⟪ ≈ₛ-refl ⟫

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

  FO : List (Vertex shape)
  FO = filterᵇ fo (vertices shape)

  fo-hidden : List (Vertex shape)
  fo-hidden = filterᵇ (λ q → not (fo q)) (vertices shape)

  fo-graph : Relation vertex-width
  fo-graph = hide-all vertex-width gr (map (λ q → inj₂ (inj₁ q)) fo-hidden)

  _<ᵥ_ : V → V → Set
  _<ᵥ_ = sum-< (λ _ _ → ⊥) _<⁺_

  <ᵥ-order : IsStrictOrder _<ᵥ_
  <ᵥ-order = sum-<-order none-order <⁺-order

  private
    module O = Ordered vertex-width _<ᵥ_ <ᵥ-order

  open O public using (Fwd; fwd-hide; fwd-hide-all; hide-all-perm)

  gr-forward : Fwd gr
  gr-forward (inj₁ _) (inj₂ q) k l = inj₁ tt
  gr-forward (inj₂ p) (inj₂ q) k l = <⁺-inside p q k l
  gr-forward (inj₁ _) (inj₁ _) k l = inj₂ ⟪ ≈ₛ-refl ⟫
  gr-forward (inj₂ p) (inj₁ _) k l = inj₂ ⟪ ≈ₛ-refl ⟫

  fo-forward : Fwd fo-graph
  fo-forward = fwd-hide-all (map (λ q → inj₂ (inj₁ q)) fo-hidden) gr-forward

private
  distrib-root : ∀ {m n k l} (P : M.Matrix m n) (X : M.Matrix n k) (Y : M.Matrix n l) (Z : M.Matrix l k) →
                 ((P ∘ X) M.+ₘ ((P ∘ Y) ∘ Z)) ≈ (P ∘ (X M.+ₘ (Y ∘ Z)))
  distrib-root P X Y Z =
    ≈-trans (M.+ₘ-cong ≈-refl (assoc P Y Z)) (≈-sym (M.comp-bilinear₂ P X (Y ∘ Z)))

  root-step : ∀ {m n l k} {P : M.Matrix m n} {G₁ : M.Matrix m k} {X : M.Matrix n k}
              {G₂ : M.Matrix m l} {Y : M.Matrix n l} {G₃ Z : M.Matrix l k} →
              G₁ ≈ (P ∘ X) → G₂ ≈ (P ∘ Y) → G₃ ≈ Z →
              (G₁ M.+ₘ (G₂ ∘ G₃)) ≈ (P ∘ (X M.+ₘ (Y ∘ Z)))
  root-step {P = P} {X = X} {Y = Y} {Z = Z} a b c = ≈-trans (M.+ₘ-cong a (∘-cong b c)) (distrib-root P X Y Z)

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
module _ {m n : ℕ} (B : Graph m n) where

  root-row : ∀ y → gr B (inj₂ (inj₂ root)) y ≈ M.εₘ
  root-row (inj₁ _) = ≈-refl {f = M.εₘ}
  root-row (inj₂ _) = ≈-refl {f = M.εₘ}

  hide-paths⁺ : hide-all (vertex-width B) (gr B) (map inj₂ (paths⁺ B)) (inj₁ input) (inj₂ (inj₂ root))
                ≈ collapse B
  hide-paths⁺ =
    ≈-trans (≡-to-≈ (≡-cong (λ l → hide-all (vertex-width B) (gr B) l (inj₁ input) (inj₂ (inj₂ root)))
                            (≡-cong (inj₂ (inj₂ root) ∷_) (≡-sym (map-∘ {g = inj₂} {f = inj₁} (vertices (Graph.shape B)))))))
            (hide-all-cong (vertex-width B) (map (λ q → inj₂ (inj₁ q)) (vertices (Graph.shape B)))
                           (hide-sink (vertex-width B) (gr B) (inj₂ (inj₂ root)) root-row)
                           (inj₁ input) (inj₂ (inj₂ root)))

module HidePremise
  {mB nB : ℕ} (B : Graph mB nB)
  {V : Set} (width : V → ℕ)
  (inp : V)
  (blk : Path⁺ B → V)
  {T : Set} (tgt : T → V)
  {m' : ℕ} (Φ : M.Matrix m' (width inp))
  (P : (t : T) → M.Matrix (width (tgt t)) (width (blk (inj₂ root))))
  (K : (t : T) → M.Matrix (width (tgt t)) (width inp))
  where

  record St : Set where
    field
      into   : (q : Path⁺ B) → M.Matrix (width (blk q)) m'
      inside : (p q : Path⁺ B) → M.Matrix (width (blk q)) (width (blk p))

  open St public

  step : St → (Path⁺ B) → St
  step H w .into q = H .into q M.+ₘ (H .inside w q ∘ H .into w)
  step H w .inside p q = H .inside p q M.+ₘ (H .inside w q ∘ H .inside p w)

  steps : St → List (Path⁺ B) → St
  steps = foldl step

  folds : ∀ {A V' : Set} (prem : A → St) (ι : Path⁺ B → V') (h' : A → V' → A) →
          (∀ G w → step (prem G) w ≡ prem (h' G (ι w))) →
          (ws : List (Path⁺ B)) (G : A) → steps (prem G) ws ≡ prem (foldl h' G (map ι ws))
  folds prem ι h' ok []       G = ≡-refl
  folds prem ι h' ok (w ∷ ws) G =
    ≡-trans (≡-cong (λ H → steps H ws) (ok G w)) (folds prem ι h' ok ws (h' G (ι w)))

  private
    Φ-step : ∀ (H : St) (w : (Path⁺ B)) (q : Path⁺ B) →
             (step H w .into q ∘ Φ)
             ≈ ((H .into q ∘ Φ) M.+ₘ (H .inside w q ∘ (H .into w ∘ Φ)))
    Φ-step H w q =
      ≈-trans (M.comp-bilinear₁ (H .into q) (H .inside w q ∘ H .into w) Φ)
              (M.+ₘ-cong ≈-refl (assoc (H .inside w q) (H .into w) Φ))

  record Agrees (G : Relation width) (H : St) : Set where
    field
      into-ok   : ∀ q → G inp (blk q) ≈ (H .into q ∘ Φ)
      inside-ok : ∀ p q → G (blk p) (blk q) ≈ H .inside p q
      tgt-ok    : ∀ t → G inp (tgt t) ≈ (K t M.+ₘ (P t ∘ (H .into (inj₂ root) ∘ Φ)))
      up-ok     : ∀ t (p : Vertex (Graph.shape B)) → G (blk (inj₁ p)) (tgt t)
                                ≈ (P t ∘ H .inside (inj₁ p) (inj₂ root))

  open Agrees public

  agrees-hide : ∀ {G H} (w : Vertex (Graph.shape B)) → Agrees G H → Agrees (hide width G (blk (inj₁ w))) (step H (inj₁ w))
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

  agrees-hide-all : ∀ {G H} (ws : List (Vertex (Graph.shape B))) → Agrees G H →
                    Agrees (hide-all width G (map (λ w → blk (inj₁ w)) ws)) (steps H (map inj₁ ws))
  agrees-hide-all []       s = s
  agrees-hide-all (w ∷ ws) s = agrees-hide-all ws (agrees-hide w s)

  -- The relations a rule contributes, before the graph's root is hidden. Every edge from the graph to
  -- a target leaves the graph's root, which here is a matter of the vertex set rather than a lemma.
  record Start (G : Relation width) (H : St) : Set where
    field
      into-start   : ∀ q → G inp (blk q) ≈ (H .into q ∘ Φ)
      inside-start : ∀ p q → G (blk p) (blk q) ≈ H .inside p q
      tgt-start    : ∀ t → G inp (tgt t) ≈ K t
      up-start     : ∀ t → G (blk (inj₂ root)) (tgt t) ≈ P t
      off-start    : ∀ t (p : Vertex (Graph.shape B)) → G (blk (inj₁ p)) (tgt t) ≈ M.εₘ
      sink         : ∀ q → H .inside (inj₂ root) q ≈ M.εₘ

  open Start public

  agrees-start : ∀ {G H} → Start G H → Agrees (hide width G (blk (inj₂ root))) (step H (inj₂ root))
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

  module Hidden (G₀ : Relation width) (prem : Relation (vertex-width B) → St)
                (prem-step : ∀ G w → step (prem G) w ≡ prem (hide (vertex-width B) G (inj₂ w))) where

    H⁰ : St
    H⁰ = prem (gr B)

    G : Relation width
    G = hide-all width (hide width G₀ (blk (inj₂ root))) (map (λ w → blk (inj₁ w)) (vertices (Graph.shape B)))

    H : St
    H = steps (step H⁰ (inj₂ root)) (map inj₁ (vertices (Graph.shape B)))

    done : Start G₀ H⁰ → Agrees G H
    done start = agrees-hide-all (vertices (Graph.shape B)) (agrees-start start)

    κ : H .into (inj₂ root) ≡ prem (hide-all (vertex-width B) (gr B) (map inj₂ (paths⁺ B))) .into (inj₂ root)
    κ = ≡-cong (λ H' → H' .into (inj₂ root)) (folds prem inj₂ (hide (vertex-width B)) prem-step (paths⁺ B) (gr B))

module NoEdgeIntoHidden
  {V : Set} (vertex-width : V → ℕ)
  {W : Set} (hid : W → V)
  {S : Set} (src : S → V)
  {T : Set} (col : T → V)
  (B : (s : S) (t : T) → M.Matrix (vertex-width (col t)) (vertex-width (src s)))
  where

  record Fixed (G : Relation vertex-width) : Set where
    field
      edge    : ∀ s t → G (src s) (col t) ≈ B s t
      no-edge : ∀ s w → G (src s) (hid w) ≈ M.εₘ

  open Fixed public

  fixed-hide : ∀ {G} (w : W) → Fixed G → Fixed (hide vertex-width G (hid w))
  fixed-hide {G} w k .edge s t =
    ≈-trans (M.+ₘ-cong (k .edge s t) (∘-cong₂ (k .no-edge s w)))
            (M.absorb₂ (B s t) (G (hid w) (col t)))
  fixed-hide {G} w k .no-edge s w' =
    ≈-trans (M.+ₘ-cong (k .no-edge s w') (∘-cong₂ (k .no-edge s w)))
            (M.absorb₂ M.εₘ (G (hid w) (hid w')))

  fixed-hide-all : ∀ {G} {W' : Set} (f : W' → W) (ws : List W') →
                   Fixed G → Fixed (hide-all vertex-width G (map (λ w → hid (f w)) ws))
  fixed-hide-all f []       k = k
  fixed-hide-all f (w ∷ ws) k = fixed-hide-all f ws (fixed-hide (f w) k)

  fixed-resp : ∀ {G G'} → G ≐ G' → Fixed G → Fixed G'
  fixed-resp e k .edge s t = ≈-trans (≈-sym (e (src s) (col t))) (k .edge s t)
  fixed-resp e k .no-edge s w = ≈-trans (≈-sym (e (src s) (hid w))) (k .no-edge s w)

private
  factor : ∀ {x y z w v} (A : M.Matrix z y) (r : M.Matrix y x) (l : M.Matrix y w)
           {h c : M.Matrix w v} (ρ : M.Matrix v x) → h ≈ c →
           ((A ∘ r) M.+ₘ ((A ∘ l) ∘ (h ∘ ρ))) ≈ (A ∘ (r M.+ₘ (l ∘ (c ∘ ρ))))
  factor A r l ρ e =
    ≈-trans (M.+ₘ-cong ≈-refl (≈-trans (∘-cong₂ (∘-cong₁ e)) (assoc A l (_ ∘ ρ))))
            (≈-sym (M.comp-bilinear₂ A r (l ∘ (_ ∘ ρ))))

module NoEdgeOutOfHidden
  {V : Set} (vertex-width : V → ℕ)
  {W : Set} (hid : W → V)
  {S : Set} (src : S → V)
  {T : Set} (col : T → V)
  (B : (s : S) (t : T) → M.Matrix (vertex-width (col t)) (vertex-width (src s)))
  where

  private
    module Into = NoEdgeIntoHidden vertex-width hid col src (λ t s → (B s t) M.ᵀ)

  record Fixed (G : Relation vertex-width) : Set where
    field
      edge    : ∀ s t → G (src s) (col t) ≈ B s t
      no-edge : ∀ w t → G (hid w) (col t) ≈ M.εₘ

  open Fixed public

  private
    to : ∀ {G} → Fixed G → Into.Fixed (flip G)
    to k .Into.edge t s i j = k .edge s t j i
    to k .Into.no-edge t w i j = k .no-edge w t j i

    from : ∀ {G} → Into.Fixed (flip G) → Fixed G
    from k .edge s t i j = k .Into.edge t s j i
    from k .no-edge w t i j = k .Into.no-edge t w j i

  fixed-hide : ∀ {G} (w : W) → Fixed G → Fixed (hide vertex-width G (hid w))
  fixed-hide {G} w k = from (Into.fixed-resp (flip-hide vertex-width G (hid w)) (Into.fixed-hide w (to k)))

  fixed-hide-all : ∀ {G} {W' : Set} (f : W' → W) (ws : List W') →
                   Fixed G → Fixed (hide-all vertex-width G (map (λ w → hid (f w)) ws))
  fixed-hide-all f []       k = k
  fixed-hide-all f (w ∷ ws) k = fixed-hide-all f ws (fixed-hide (f w) k)

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
  E .Graph.up = up-root⁺ B up-root

  private
    b : Path⁺ B → V E
    b q = inj₂ (inj₁ q)

    er : V E
    er = inj₂ (inj₂ root)

    module S = HidePremise B (vertex-width E) (inj₁ input) b (λ (_ : Root) → er) inputs (λ _ → up-root) (λ _ → out-root)

    prem : Relation (vertex-width B) → S.St
    prem G .S.into q = G (inj₁ input) (inj₂ q)
    prem G .S.inside p q = G (inj₂ p) (inj₂ q)

    module hidden = S.Hidden (gr E) prem (λ G w → ≡-refl)

    start : S.Start (gr E) hidden.H⁰
    start .S.into-start q = ≈-refl
    start .S.inside-start p q = ≈-refl
    start .S.tgt-start _ = ≈-refl {f = out-root}
    start .S.up-start _ = ≈-refl {f = up-root}
    start .S.off-start _ p = ≈-refl {f = M.εₘ}
    start .S.sink q = ≈-refl {f = M.εₘ}

    plumb : collapse E ≡ hidden.G (inj₁ input) er
    plumb = ≡-cong (λ l → hide-all (vertex-width E) (gr E) l (inj₁ input) er)
                   (≡-cong (b (inj₂ root) ∷_) (≡-sym (map-∘ {g = b} {f = inj₁} (vertices (Graph.shape B)))))

  agree : collapse E ≈ (out-root M.+ₘ (up-root ∘ (collapse B ∘ inputs)))
  agree =
    ≈-trans (≡-to-≈ plumb)
            (≈-trans (hidden.done start .S.tgt-ok root)
                     (M.+ₘ-cong ≈-refl (∘-cong₂ (∘-cong₁ (≈-trans (≡-to-≈ hidden.κ) (hide-paths⁺ B))))))

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
  E .Graph.<-inside (inj₁ (inj₁ p)) (inj₁ (inj₁ q)) k l = Graph.<-inside B₁ p q k l
  E .Graph.<-inside (inj₁ (inj₁ p)) (inj₁ (inj₂ _)) k l = inj₁ tt
  E .Graph.<-inside (inj₁ (inj₂ _)) (inj₁ _) k l = inj₂ ⟪ ≈ₛ-refl ⟫
  E .Graph.<-inside (inj₁ (inj₁ p)) (inj₂ q) k l = inj₁ tt
  E .Graph.<-inside (inj₁ (inj₂ _)) (inj₂ q) k l = inj₁ tt
  E .Graph.<-inside (inj₂ p)        (inj₁ q) k l = inj₂ ⟪ ≈ₛ-refl ⟫
  E .Graph.<-inside (inj₂ (inj₁ p)) (inj₂ (inj₁ q)) k l = Graph.<-inside B₂ p q k l
  E .Graph.<-inside (inj₂ (inj₁ p)) (inj₂ (inj₂ _)) k l = inj₁ tt
  E .Graph.<-inside (inj₂ (inj₂ _)) (inj₂ _) k l = inj₂ ⟪ ≈ₛ-refl ⟫
  E .Graph.out = out-root
  E .Graph.up (inj₁ p) = up-root⁺ B₁ up₁ p
  E .Graph.up (inj₂ s) = up-root⁺ B₂ up₂ s

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

    module S₁ = HidePremise B₁ (vertex-width E) (inj₁ input) b1 tgt₁ inputs₁ P₁ K₁

    prem₁ : Relation (vertex-width B₁) → S₁.St
    prem₁ G .S₁.into q = G (inj₁ input) (inj₂ q)
    prem₁ G .S₁.inside p q = G (inj₂ p) (inj₂ q)

    module hidden₁ = S₁.Hidden (gr E) prem₁ (λ G w → ≡-refl)

    start₁ : S₁.Start (gr E) hidden₁.H⁰
    start₁ .S₁.into-start q = ≈-refl
    start₁ .S₁.inside-start p q = ≈-refl
    start₁ .S₁.tgt-start (inj₁ q) = ≈-refl
    start₁ .S₁.tgt-start (inj₂ _) = ≈-refl {f = out-root}
    start₁ .S₁.up-start (inj₁ q) = ≈-refl
    start₁ .S₁.up-start (inj₂ _) = ≈-refl {f = up₁}
    start₁ .S₁.off-start (inj₁ q) p = ≈-refl {f = M.εₘ}
    start₁ .S₁.off-start (inj₂ _) p = ≈-refl {f = M.εₘ}
    start₁ .S₁.sink q = ≈-refl {f = M.εₘ}

    done₁ = hidden₁.done start₁
    κ₁ = ≈-trans (≡-to-≈ hidden₁.κ) (hide-paths⁺ B₁)

  Φ₂ : M.Matrix m₂ m
  Φ₂ = inputs₂ ∘ M.⟨ M.I , collapse B₁ ∘ inputs₁ ⟩

  private
    Φ₂' : M.Matrix m₂ m
    Φ₂' = from-inputs₂ M.+ₘ (from-root₁ ∘ (collapse B₁ ∘ inputs₁))

    Φ₂-split : Φ₂' ≈ Φ₂
    Φ₂-split = ≈-sym (≈-trans (M.∘-pair inputs₂ M.I (collapse B₁ ∘ inputs₁))
                              (M.+ₘ-cong (id-right {f = from-inputs₂}) (≈-refl {f = from-root₁ ∘ (collapse B₁ ∘ inputs₁)})))

    module S₂ = HidePremise B₂ (vertex-width E) (inj₁ input) b2 (λ (_ : Root) → er) Φ₂' (λ _ → up₂)
                            (λ _ → out-root M.+ₘ (up₁ ∘ (collapse B₁ ∘ inputs₁)))

    prem₂ : Relation (vertex-width B₂) → S₂.St
    prem₂ G .S₂.into q = G (inj₁ input) (inj₂ q)
    prem₂ G .S₂.inside p q = G (inj₂ p) (inj₂ q)

    module hidden₂ = S₂.Hidden hidden₁.G prem₂ (λ G w → ≡-refl)

    Bh : (s : Path⁺ B₂) (t : Path⁺ B₂ ⊎ Root) → M.Matrix (vertex-width E (tgt₁ t)) (width⁺ B₂ s)
    Bh s (inj₁ q) = inside⁺ B₂ s q
    Bh s (inj₂ _) = up-root⁺ B₂ up₂ s

    module IntoHidden = NoEdgeIntoHidden (vertex-width E) b1 b2 tgt₁ Bh

    fixed₀ : IntoHidden.Fixed (gr E)
    fixed₀ .IntoHidden.edge s (inj₁ q) = ≈-refl
    fixed₀ .IntoHidden.edge s (inj₂ _) = ≈-refl {f = up-root⁺ B₂ up₂ s}
    fixed₀ .IntoHidden.no-edge s w = ≈-refl {f = M.εₘ}

    fixed₁ : IntoHidden.Fixed hidden₁.G
    fixed₁ = IntoHidden.fixed-hide-all inj₁ ps₁ (IntoHidden.fixed-hide (inj₂ root) fixed₀)

    start₂ : S₂.Start hidden₁.G hidden₂.H⁰
    start₂ .S₂.into-start q =
      ≈-trans (done₁ .S₁.tgt-ok (inj₁ q)) (factor (into⁺ B₂ q) from-inputs₂ from-root₁ inputs₁ κ₁)
    start₂ .S₂.inside-start p q = fixed₁ .IntoHidden.edge p (inj₁ q)
    start₂ .S₂.tgt-start _ = ≈-trans (done₁ .S₁.tgt-ok (inj₂ root)) (M.+ₘ-cong ≈-refl (∘-cong₂ (∘-cong₁ κ₁)))
    start₂ .S₂.up-start _ = fixed₁ .IntoHidden.edge (inj₂ root) (inj₂ root)
    start₂ .S₂.off-start _ p = fixed₁ .IntoHidden.edge (inj₁ p) (inj₂ root)
    start₂ .S₂.sink q = ≈-refl {f = M.εₘ}

    lst : map (λ q → inj₂ {A = Input} (inj₁ q)) (vertices (Graph.shape E))
          ≡ (b1 (inj₂ root) ∷ map (λ w → b1 (inj₁ w)) ps₁)
            ++ (b2 (inj₂ root) ∷ map (λ w → b2 (inj₁ w)) ps₂)
    lst =
      ≡-trans (map-++ (λ q → inj₂ (inj₁ q)) (map inj₁ (paths⁺ B₁)) (map inj₂ (paths⁺ B₂)))
              (≡-cong₂ _++_
                (≡-trans (≡-sym (map-∘ {g = (λ q → inj₂ (inj₁ q))} {f = inj₁} (paths⁺ B₁)))
                         (≡-cong (b1 (inj₂ root) ∷_) (≡-sym (map-∘ {g = b1} {f = inj₁} ps₁))))
                (≡-trans (≡-sym (map-∘ {g = (λ q → inj₂ (inj₁ q))} {f = inj₂} (paths⁺ B₂)))
                         (≡-cong (b2 (inj₂ root) ∷_) (≡-sym (map-∘ {g = b2} {f = inj₁} ps₂)))))

    plumb : collapse E ≡ hidden₂.G (inj₁ input) er
    plumb =
      ≡-trans (≡-cong (λ l → hide-all (vertex-width E) (gr E) l (inj₁ input) er) lst)
              (≡-cong (λ G → G (inj₁ input) er)
                      (foldl-++ (hide (vertex-width E)) (gr E) (b1 (inj₂ root) ∷ map (λ w → b1 (inj₁ w)) ps₁) (b2 (inj₂ root) ∷ map (λ w → b2 (inj₁ w)) ps₂)))

  agree : collapse E ≈ ((out-root M.+ₘ (up₁ ∘ (collapse B₁ ∘ inputs₁))) M.+ₘ (up₂ ∘ (collapse B₂ ∘ Φ₂)))
  agree =
    ≈-trans (≡-to-≈ plumb)
            (≈-trans (hidden₂.done start₂ .S₂.tgt-ok root)
                     (M.+ₘ-cong ≈-refl (∘-cong₂ (∘-cong (≈-trans (≡-to-≈ hidden₂.κ) (hide-paths⁺ B₂)) Φ₂-split))))

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
  E .Graph.<-inside (inj₁ (inj₁ p)) (inj₁ (inj₁ q)) k l = Graph.<-inside B₁ p q k l
  E .Graph.<-inside (inj₁ (inj₁ p)) (inj₁ (inj₂ _)) k l = inj₁ tt
  E .Graph.<-inside (inj₁ (inj₂ _)) (inj₁ _) k l = inj₂ ⟪ ≈ₛ-refl ⟫
  E .Graph.<-inside (inj₁ (inj₁ p)) (inj₂ q) k l = inj₁ tt
  E .Graph.<-inside (inj₁ (inj₂ _)) (inj₂ q) k l = inj₁ tt
  E .Graph.<-inside (inj₂ (inj₁ p)) (inj₁ q) k l = inj₂ ⟪ ≈ₛ-refl ⟫
  E .Graph.<-inside (inj₂ (inj₂ p)) (inj₁ q) k l = inj₂ ⟪ ≈ₛ-refl ⟫
  E .Graph.<-inside (inj₂ (inj₁ (inj₁ p))) (inj₂ (inj₁ (inj₁ q))) k l = Graph.<-inside B₂ p q k l
  E .Graph.<-inside (inj₂ (inj₁ (inj₁ p))) (inj₂ (inj₁ (inj₂ _))) k l = inj₁ tt
  E .Graph.<-inside (inj₂ (inj₁ (inj₂ _))) (inj₂ (inj₁ _)) k l = inj₂ ⟪ ≈ₛ-refl ⟫
  E .Graph.<-inside (inj₂ (inj₁ (inj₁ p))) (inj₂ (inj₂ _)) k l = inj₁ tt
  E .Graph.<-inside (inj₂ (inj₁ (inj₂ _))) (inj₂ (inj₂ _)) k l = inj₁ tt
  E .Graph.<-inside (inj₂ (inj₂ _))        (inj₂ (inj₁ _)) k l = inj₂ ⟪ ≈ₛ-refl ⟫
  E .Graph.<-inside (inj₂ (inj₂ (inj₁ p))) (inj₂ (inj₂ (inj₁ q))) k l = Graph.<-inside B₃ p q k l
  E .Graph.<-inside (inj₂ (inj₂ (inj₁ p))) (inj₂ (inj₂ (inj₂ _))) k l = inj₁ tt
  E .Graph.<-inside (inj₂ (inj₂ (inj₂ _))) (inj₂ (inj₂ _)) k l = inj₂ ⟪ ≈ₛ-refl ⟫
  E .Graph.out = out-root
  E .Graph.up (inj₁ p)        = up-root⁺ B₁ up₁ p
  E .Graph.up (inj₂ (inj₁ p)) = up-root⁺ B₂ up₂ p
  E .Graph.up (inj₂ (inj₂ p)) = up-root⁺ B₃ up₃ p

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

    module S₁ = HidePremise B₁ (vertex-width E) (inj₁ input) b1 tgt inputs₁ P₁ K₁

    prem₁ : Relation (vertex-width B₁) → S₁.St
    prem₁ G .S₁.into q = G (inj₁ input) (inj₂ q)
    prem₁ G .S₁.inside p q = G (inj₂ p) (inj₂ q)

    module hidden₁ = S₁.Hidden (gr E) prem₁ (λ G w → ≡-refl)

    start₁ : S₁.Start (gr E) hidden₁.H⁰
    start₁ .S₁.into-start q = ≈-refl
    start₁ .S₁.inside-start p q = ≈-refl
    start₁ .S₁.tgt-start (inj₁ q) = ≈-refl
    start₁ .S₁.tgt-start (inj₂ _) = ≈-refl {f = out-root}
    start₁ .S₁.up-start (inj₁ q) = ≈-refl
    start₁ .S₁.up-start (inj₂ _) = ≈-refl {f = up₁}
    start₁ .S₁.off-start (inj₁ q) p = ≈-refl {f = M.εₘ}
    start₁ .S₁.off-start (inj₂ _) p = ≈-refl {f = M.εₘ}
    start₁ .S₁.sink q = ≈-refl {f = M.εₘ}

    done₁ = hidden₁.done start₁
    κ₁ = ≈-trans (≡-to-≈ hidden₁.κ) (hide-paths⁺ B₁)

    module OutOfHidden = NoEdgeOutOfHidden (vertex-width E) b1 (inj₁ {A = Input}) b2 (λ _ q → into⁺ B₂ q ∘ inputs₂)

    fixed₀ : OutOfHidden.Fixed (gr E)
    fixed₀ .OutOfHidden.edge _ q = ≈-refl
    fixed₀ .OutOfHidden.no-edge w q = ≈-refl {f = M.εₘ}

    fixed₁ : OutOfHidden.Fixed hidden₁.G
    fixed₁ = OutOfHidden.fixed-hide-all inj₁ ps₁ (OutOfHidden.fixed-hide (inj₂ root) fixed₀)

    cols₂ : Path⁺ B₂ ⊎ (Path⁺ B₃ ⊎ Root) → V E
    cols₂ (inj₁ q) = b2 q
    cols₂ (inj₂ t) = tgt t

    Bh₂ : (s : Path⁺ B₂) (t : Path⁺ B₂ ⊎ (Path⁺ B₃ ⊎ Root)) → M.Matrix (vertex-width E (cols₂ t)) (width⁺ B₂ s)
    Bh₂ s (inj₁ q)        = inside⁺ B₂ s q
    Bh₂ s (inj₂ (inj₁ q)) = e₂₃ s q
    Bh₂ s (inj₂ (inj₂ _)) = up-root⁺ B₂ up₂ s

    module IntoHidden₂ = NoEdgeIntoHidden (vertex-width E) b1 b2 cols₂ Bh₂

    fixed₂ : IntoHidden₂.Fixed hidden₁.G
    fixed₂ = IntoHidden₂.fixed-hide-all inj₁ ps₁ (IntoHidden₂.fixed-hide (inj₂ root) k₀)
      where
      k₀ : IntoHidden₂.Fixed (gr E)
      k₀ .IntoHidden₂.edge s (inj₁ q)        = ≈-refl
      k₀ .IntoHidden₂.edge s (inj₂ (inj₁ q)) = ≈-refl {f = e₂₃ s q}
      k₀ .IntoHidden₂.edge s (inj₂ (inj₂ _)) = ≈-refl {f = up-root⁺ B₂ up₂ s}
      k₀ .IntoHidden₂.no-edge s w = ≈-refl {f = M.εₘ}

    Φ₃₁ : M.Matrix m₃ m
    Φ₃₁ = from-inputs₃ M.+ₘ (from-root₁ ∘ c₁)

    P₂ : (t : Path⁺ B₃ ⊎ Root) → M.Matrix (vertex-width E (tgt t)) n₂
    P₂ (inj₁ q) = into⁺ B₃ q ∘ from-root₂
    P₂ (inj₂ _) = up₂

    K₂ : (t : Path⁺ B₃ ⊎ Root) → M.Matrix (vertex-width E (tgt t)) m
    K₂ (inj₁ q) = into⁺ B₃ q ∘ Φ₃₁
    K₂ (inj₂ _) = out-root M.+ₘ (up₁ ∘ c₁)

    module S₂ = HidePremise B₂ (vertex-width E) (inj₁ input) b2 tgt inputs₂ P₂ K₂

    prem₂ : Relation (vertex-width B₂) → S₂.St
    prem₂ G .S₂.into q = G (inj₁ input) (inj₂ q)
    prem₂ G .S₂.inside p q = G (inj₂ p) (inj₂ q)

    module hidden₂ = S₂.Hidden hidden₁.G prem₂ (λ G w → ≡-refl)

    start₂ : S₂.Start hidden₁.G hidden₂.H⁰
    start₂ .S₂.into-start q = fixed₁ .OutOfHidden.edge input q
    start₂ .S₂.inside-start p q = fixed₂ .IntoHidden₂.edge p (inj₁ q)
    start₂ .S₂.tgt-start (inj₁ q) =
      ≈-trans (done₁ .S₁.tgt-ok (inj₁ q)) (factor (into⁺ B₃ q) from-inputs₃ from-root₁ inputs₁ κ₁)
    start₂ .S₂.tgt-start (inj₂ _) =
      ≈-trans (done₁ .S₁.tgt-ok (inj₂ root))
              (M.+ₘ-cong ≈-refl (∘-cong₂ (∘-cong₁ κ₁)))
    start₂ .S₂.up-start (inj₁ q) = fixed₂ .IntoHidden₂.edge (inj₂ root) (inj₂ (inj₁ q))
    start₂ .S₂.up-start (inj₂ _) = fixed₂ .IntoHidden₂.edge (inj₂ root) (inj₂ (inj₂ root))
    start₂ .S₂.off-start (inj₁ q) p = fixed₂ .IntoHidden₂.edge (inj₁ p) (inj₂ (inj₁ q))
    start₂ .S₂.off-start (inj₂ _) p = fixed₂ .IntoHidden₂.edge (inj₁ p) (inj₂ (inj₂ root))
    start₂ .S₂.sink q = ≈-refl {f = M.εₘ}

    done₂ = hidden₂.done start₂
    κ₂ = ≈-trans (≡-to-≈ hidden₂.κ) (hide-paths⁺ B₂)

    hid₁₂ : Path⁺ B₁ ⊎ Path⁺ B₂ → V E
    hid₁₂ (inj₁ q) = b1 q
    hid₁₂ (inj₂ q) = b2 q

    Bh₃ : (s : Path⁺ B₃) (t : Path⁺ B₃ ⊎ Root) → M.Matrix (vertex-width E (tgt t)) (width⁺ B₃ s)
    Bh₃ s (inj₁ q) = inside⁺ B₃ s q
    Bh₃ s (inj₂ _) = up-root⁺ B₃ up₃ s

    module IntoHidden₃ = NoEdgeIntoHidden (vertex-width E) hid₁₂ b3 tgt Bh₃

    fixed₃ : IntoHidden₃.Fixed hidden₂.G
    fixed₃ =
      IntoHidden₃.fixed-hide-all (λ w → inj₂ (inj₁ w)) ps₂
        (IntoHidden₃.fixed-hide (inj₂ (inj₂ root))
          (IntoHidden₃.fixed-hide-all (λ w → inj₁ (inj₁ w)) ps₁
            (IntoHidden₃.fixed-hide (inj₁ (inj₂ root)) k₀)))
      where
      k₀ : IntoHidden₃.Fixed (gr E)
      k₀ .IntoHidden₃.edge s (inj₁ q) = ≈-refl
      k₀ .IntoHidden₃.edge s (inj₂ _) = ≈-refl {f = up-root⁺ B₃ up₃ s}
      k₀ .IntoHidden₃.no-edge s (inj₁ w) = ≈-refl {f = M.εₘ}
      k₀ .IntoHidden₃.no-edge s (inj₂ w) = ≈-refl {f = M.εₘ}

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

    module S₃ = HidePremise B₃ (vertex-width E) (inj₁ input) b3 (λ (_ : Root) → er) Φ₃' (λ _ → up₃)
                            (λ _ → (out-root M.+ₘ (up₁ ∘ c₁)) M.+ₘ (up₂ ∘ c₂))

    prem₃ : Relation (vertex-width B₃) → S₃.St
    prem₃ G .S₃.into q = G (inj₁ input) (inj₂ q)
    prem₃ G .S₃.inside p q = G (inj₂ p) (inj₂ q)

    module hidden₃ = S₃.Hidden hidden₂.G prem₃ (λ G w → ≡-refl)

    start₃ : S₃.Start hidden₂.G hidden₃.H⁰
    start₃ .S₃.into-start q =
      ≈-trans (done₂ .S₂.tgt-ok (inj₁ q)) (factor (into⁺ B₃ q) Φ₃₁ from-root₂ inputs₂ κ₂)
    start₃ .S₃.inside-start p q = fixed₃ .IntoHidden₃.edge p (inj₁ q)
    start₃ .S₃.tgt-start _ = ≈-trans (done₂ .S₂.tgt-ok (inj₂ root)) (M.+ₘ-cong ≈-refl (∘-cong₂ (∘-cong₁ κ₂)))
    start₃ .S₃.up-start _ = fixed₃ .IntoHidden₃.edge (inj₂ root) (inj₂ root)
    start₃ .S₃.off-start _ p = fixed₃ .IntoHidden₃.edge (inj₁ p) (inj₂ root)
    start₃ .S₃.sink q = ≈-refl {f = M.εₘ}

    l₁ l₂ l₃ : List (V E)
    l₁ = b1 (inj₂ root) ∷ map (λ w → b1 (inj₁ w)) ps₁
    l₂ = b2 (inj₂ root) ∷ map (λ w → b2 (inj₁ w)) ps₂
    l₃ = b3 (inj₂ root) ∷ map (λ w → b3 (inj₁ w)) ps₃

    lst : map (λ q → inj₂ {A = Input} (inj₁ q)) (vertices (Graph.shape E)) ≡ l₁ ++ (l₂ ++ l₃)
    lst =
      ≡-trans (map-++ (λ q → inj₂ (inj₁ q)) (map inj₁ (paths⁺ B₁))
                      (map inj₂ (map inj₁ (paths⁺ B₂) ++ map inj₂ (paths⁺ B₃))))
              (≡-cong₂ _++_
                (≡-trans (≡-sym (map-∘ {g = (λ q → inj₂ (inj₁ q))} {f = inj₁} (paths⁺ B₁)))
                         (≡-cong (b1 (inj₂ root) ∷_) (≡-sym (map-∘ {g = b1} {f = inj₁} ps₁))))
                (≡-trans (≡-sym (map-∘ {g = (λ q → inj₂ (inj₁ q))} {f = inj₂} (map inj₁ (paths⁺ B₂) ++ map inj₂ (paths⁺ B₃))))
                (≡-trans (map-++ (λ q → inj₂ (inj₁ (inj₂ q))) (map inj₁ (paths⁺ B₂))
                                 (map inj₂ (paths⁺ B₃)))
                         (≡-cong₂ _++_
                           (≡-trans (≡-sym (map-∘ {g = (λ q → inj₂ (inj₁ (inj₂ q)))} {f = inj₁} (paths⁺ B₂)))
                                    (≡-cong (b2 (inj₂ root) ∷_) (≡-sym (map-∘ {g = b2} {f = inj₁} ps₂))))
                           (≡-trans (≡-sym (map-∘ {g = (λ q → inj₂ (inj₁ (inj₂ q)))} {f = inj₂} (paths⁺ B₃)))
                                    (≡-cong (b3 (inj₂ root) ∷_) (≡-sym (map-∘ {g = b3} {f = inj₁} ps₃))))))))

    plumb : collapse E ≡ hidden₃.G (inj₁ input) er
    plumb =
      ≡-trans (≡-cong (λ l → hide-all (vertex-width E) (gr E) l (inj₁ input) er) lst)
              (≡-trans (≡-cong (λ G → G (inj₁ input) er)
                               (foldl-++ (hide (vertex-width E)) (gr E) l₁ (l₂ ++ l₃)))
                       (≡-cong (λ G → G (inj₁ input) er)
                               (foldl-++ (hide (vertex-width E)) hidden₁.G l₂ l₃)))

  agree : collapse E ≈ (((out-root M.+ₘ (up₁ ∘ c₁)) M.+ₘ (up₂ ∘ c₂)) M.+ₘ (up₃ ∘ (collapse B₃ ∘ Φ₃)))
  agree =
    ≈-trans (≡-to-≈ plumb)
            (≈-trans (hidden₃.done start₃ .S₃.tgt-ok root)
                     (M.+ₘ-cong ≈-refl (∘-cong₂ (∘-cong (≈-trans (≡-to-≈ hidden₃.κ) (hide-paths⁺ B₃)) Φ₃-split))))
