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
import semimodule

-- A dependence graph as a value rather than a family indexed by a derivation: a graph is a set of
-- interior vertices with widths, a distinguished root of given width, and the dependence relation
-- between each pair. The root has no outgoing relation, so it is a sink by construction.
module interaction.graph {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (let module Semiring = CommutativeSemiring S) (+-idem : ∀ x → (x Semiring.+ x) Semiring.≈ x) where

module SemiMod = semimodule S

open SemiMod using (Semimodule)
open import categories using (Category)
open Category SemiMod.cat
  using (_⇒_; _∘_; _≈_; ∘-cong; ∘-cong₁; ∘-cong₂; assoc; id-left; id-right; ≈-refl; ≈-sym; ≈-trans; ≡-to-≈)
open import cmon-enriched using (CMonEnriched; Biproduct)
private
  module CM = CMonEnriched SemiMod.cmon-enriched

infixl 21 _+ₘ_
_+ₘ_ : ∀ {X Y : Semimodule} → X ⇒ Y → X ⇒ Y → X ⇒ Y
_+ₘ_ = CM._+m_

εₘ : ∀ {X Y : Semimodule} → X ⇒ Y
εₘ {X} {Y} = CM.εm {X} {Y}

infixl 20 _⊕ᵥ_
_⊕ᵥ_ : Semimodule → Semimodule → Semimodule
_⊕ᵥ_ = SemiMod._⊕_

private
  module BP {X Y : Semimodule} = Biproduct (SemiMod.biproduct X Y)

I : ∀ {X : Semimodule} → X ⇒ X
I {X} = Category.id SemiMod.cat X

inb₁ : ∀ {X Y : Semimodule} → X ⇒ (X ⊕ᵥ Y)
inb₁ {X} {Y} = BP.in₁ {X} {Y}

inb₂ : ∀ {X Y : Semimodule} → Y ⇒ (X ⊕ᵥ Y)
inb₂ {X} {Y} = BP.in₂ {X} {Y}

pb₁ : ∀ {X Y : Semimodule} → (X ⊕ᵥ Y) ⇒ X
pb₁ {X} {Y} = BP.p₁ {X} {Y}

pb₂ : ∀ {X Y : Semimodule} → (X ⊕ᵥ Y) ⇒ Y
pb₂ {X} {Y} = BP.p₂ {X} {Y}

⟨_,_⟩ : ∀ {Z X Y : Semimodule} → Z ⇒ X → Z ⇒ Y → Z ⇒ (X ⊕ᵥ Y)
⟨ f , g ⟩ = (inb₁ ∘ f) +ₘ (inb₂ ∘ g)

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

record Graph (X Y : Semimodule) : Set₁ where
  field
    shape   : Shape
    object  : Vertex shape → Semimodule
    fo      : Vertex shape → Bool
    into    : (q : Vertex shape) → X ⇒ object q
    inside  : (p q : Vertex shape) → object p ⇒ object q
    -- Every non-zero relation between interior vertices runs strictly forward in the completion
    -- order. The inputs and the root need no condition, being below and above everything.
    <-inside : ∀ p q → lt shape p q ⊎ Prf (inside p q ≈ εₘ)
    fo-root : Bool
    out     : X ⇒ Y
    up      : (p : Vertex shape) → object p ⇒ Y

Relation : {V : Set} → (V → Semimodule) → Set
Relation {V} vertex-object = (x y : V) → vertex-object x ⇒ vertex-object y

hide : {V : Set} (vertex-object : V → Semimodule) → Relation vertex-object → V → Relation vertex-object
hide vertex-object G r x y = G x y +ₘ (G r y ∘ G x r)

hide-all : {V : Set} (vertex-object : V → Semimodule) → Relation vertex-object → List V → Relation vertex-object
hide-all vertex-object = foldl (hide vertex-object)

_≐_ : {V : Set} {vertex-object : V → Semimodule} → Relation vertex-object → Relation vertex-object → Prop
_≐_ {V} G G' = ∀ x y → G x y ≈ G' x y

private
  open import commutative-monoid using (CommutativeMonoid)

  +ₘ-cong : ∀ {X Y : Semimodule} {f f' g g' : X ⇒ Y} → f ≈ f' → g ≈ g' → (f +ₘ g) ≈ (f' +ₘ g')
  +ₘ-cong {X} {Y} = CommutativeMonoid.+-cong (CM.homCM X Y)

  +ₘ-assoc : ∀ {X Y : Semimodule} {f g h : X ⇒ Y} → ((f +ₘ g) +ₘ h) ≈ (f +ₘ (g +ₘ h))
  +ₘ-assoc {X} {Y} = CommutativeMonoid.+-assoc (CM.homCM X Y)

  +ₘ-comm : ∀ {X Y : Semimodule} {f g : X ⇒ Y} → (f +ₘ g) ≈ (g +ₘ f)
  +ₘ-comm {X} {Y} = CommutativeMonoid.+-comm (CM.homCM X Y)

  +ₘ-lunit : ∀ {X Y : Semimodule} (f : X ⇒ Y) → (εₘ +ₘ f) ≈ f
  +ₘ-lunit {X} {Y} f = CommutativeMonoid.+-lunit (CM.homCM X Y)

  +ₘ-runit : ∀ {X Y : Semimodule} (f : X ⇒ Y) → (f +ₘ εₘ) ≈ f
  +ₘ-runit f = ≈-trans +ₘ-comm (+ₘ-lunit f)

  +ₘ-swap-mid : ∀ {X Y : Semimodule} (f g h : X ⇒ Y) → (f +ₘ (g +ₘ h)) ≈ (g +ₘ (f +ₘ h))
  +ₘ-swap-mid f g h =
    ≈-trans (≈-sym +ₘ-assoc) (≈-trans (+ₘ-cong +ₘ-comm ≈-refl) +ₘ-assoc)

  absorb₁ : ∀ {X Y Z : Semimodule} (f : X ⇒ Y) (g : X ⇒ Z) → (f +ₘ (εₘ ∘ g)) ≈ f
  absorb₁ f g = ≈-trans (+ₘ-cong ≈-refl (CM.comp-bilinear-ε₁ g)) (+ₘ-runit f)

  absorb₂ : ∀ {X Y Z : Semimodule} (f : X ⇒ Y) (g : Z ⇒ Y) → (f +ₘ (g ∘ εₘ)) ≈ f
  absorb₂ f g = ≈-trans (+ₘ-cong ≈-refl (CM.comp-bilinear-ε₂ g)) (+ₘ-runit f)

  open SemiMod.Semimodule using ()
  open import prop-setoid using () renaming (_≃m_ to _≈s_)
  open SemiMod._⇒_ using (func; func-resp-≈)
  open SemiMod._≈m_

  +ₘ-idem : ∀ {X Y : Semimodule} (f : X ⇒ Y) → (f +ₘ f) ≈ f
  +ₘ-idem {X} {Y} f .*≈* ._≈s_.func-eq {x} {x'} x≈x' =
    N.trans (N.+-cong (f .func-resp-≈ x≈x') (f .func-resp-≈ x≈x')) (idem (f .func x'))
    where
    module N = SemiMod.Semimodule Y
    idem : ∀ a → (a N.+ a) N.≈ a
    idem a =
      N.trans (N.+-cong (N.sym N.·-unit) (N.sym N.·-unit))
        (N.trans (N.sym N.+-distribʳ)
          (N.trans (N.·-cong (+-idem Semiring.ι) N.refl) N.·-unit))

hide-cong : {V : Set} (vertex-object : V → Semimodule) {G G' : Relation vertex-object} (r : V) →
            G ≐ G' → hide vertex-object G r ≐ hide vertex-object G' r
hide-cong vertex-object r e x y = +ₘ-cong (e x y) (∘-cong (e r y) (e x r))

hide-all-cong : {V : Set} (vertex-object : V → Semimodule) {G G' : Relation vertex-object} (rs : List V) →
                G ≐ G' → hide-all vertex-object G rs ≐ hide-all vertex-object G' rs
hide-all-cong vertex-object []       e = e
hide-all-cong vertex-object (r ∷ rs) e = hide-all-cong vertex-object rs (hide-cong vertex-object r e)

hide-sink : {V : Set} (vertex-object : V → Semimodule) (G : Relation vertex-object) (r : V) →
            (∀ y → G r y ≈ εₘ) → hide vertex-object G r ≐ G
hide-sink vertex-object G r z x y =
  ≈-trans (+ₘ-cong (≈-refl {f = G x y}) (∘-cong₁ {f₁ = G r y} {f₂ = εₘ} {g = G x r} (z y)))
          (absorb₁ (G x y) (G x r))

module Hide (V : Set) (w : V → Semimodule) where
  Gr : Set
  Gr = Relation w

  h : Gr → V → Gr
  h = hide w

  private
    absorbˡ : ∀ {X Y : Semimodule} (f g : X ⇒ Y) → (f +ₘ (f +ₘ g)) ≈ (f +ₘ g)
    absorbˡ f g = ≈-trans (≈-sym +ₘ-assoc) (+ₘ-cong (+ₘ-idem f) ≈-refl)

    absorbʳ : ∀ {X Y : Semimodule} (f g : X ⇒ Y) → (f +ₘ (g +ₘ f)) ≈ (g +ₘ f)
    absorbʳ f g = ≈-trans (+ₘ-cong ≈-refl +ₘ-comm) (≈-trans (absorbˡ f g) +ₘ-comm)

    absorb-mono : ∀ {X Y : Semimodule} (f g h : X ⇒ Y) → f ≈ (g +ₘ f) → (h +ₘ g) ≈ g → f ≈ (h +ₘ f)
    absorb-mono f g h p q =
      ≈-trans p (≈-trans (+ₘ-cong (≈-sym q) ≈-refl) (≈-trans +ₘ-assoc (+ₘ-cong ≈-refl (≈-sym p))))

    shift : ∀ {X Y : Semimodule} (f g h : X ⇒ Y) → ((f +ₘ g) +ₘ h) ≈ ((f +ₘ h) +ₘ g)
    shift f g h = ≈-trans +ₘ-assoc (≈-trans (+ₘ-cong ≈-refl +ₘ-comm) (≈-sym +ₘ-assoc))

    insert : ∀ {X Y : Semimodule} (f g h : X ⇒ Y) → (f +ₘ g) ≈ g → (g +ₘ h) ≈ (g +ₘ (f +ₘ h))
    insert f g h q = ≈-sym (≈-trans (≈-sym +ₘ-assoc) (+ₘ-cong (≈-trans +ₘ-comm q) ≈-refl))

  zero-fold : ∀ {G : Gr} rs r₀ →
              ((∀ (z : V) → G r₀ z ≈ εₘ) ∧ (∀ (z : V) → G z r₀ ≈ εₘ)) →
              ((∀ (z : V) → foldl h G rs r₀ z ≈ εₘ) ∧ (∀ (z : V) → foldl h G rs z r₀ ≈ εₘ))
  zero-fold []           r₀ zz        = zz
  zero-fold {G} (r ∷ rs) r₀ (zr , zc) = zero-fold {h G r} rs r₀ (zr' , zc')
    where
    zr' : ∀ (z : V) → h G r r₀ z ≈ εₘ
    zr' z =
      ≈-trans (+ₘ-cong (zr z) (≈-trans {g = G r z ∘ εₘ {w r₀} {w r}} (∘-cong₂ {f = G r z} (zr r)) (CM.comp-bilinear-ε₂ {X = w r₀} (G r z)))) (+ₘ-lunit εₘ)

    zc' : ∀ (z : V) → h G r z r₀ ≈ εₘ
    zc' z =
      ≈-trans (+ₘ-cong (zc z) (≈-trans {g = εₘ {w r} {w r₀} ∘ G z r} (∘-cong₁ {f₁ = G r r₀} {f₂ = εₘ} {g = G z r} (zc r)) (CM.comp-bilinear-ε₁ {Z = w r₀} (G z r)))) (+ₘ-lunit εₘ)

  increasing : ∀ {G : Gr} rs x y → foldl h G rs x y ≈ (G x y +ₘ foldl h G rs x y)
  increasing {G} []       x y = ≈-sym (+ₘ-idem (G x y))
  increasing {G} (r ∷ rs) x y =
    absorb-mono (foldl h (h G r) rs x y) (h G r x y) (G x y)
                (increasing {h G r} rs x y)
                (absorbˡ (G x y) (G r y ∘ G x r))

  h-cong : ∀ {G G'} r → G ≐ G' → h G r ≐ h G' r
  h-cong = hide-cong w

  fold-cong : ∀ {G G'} rs → G ≐ G' → foldl h G rs ≐ foldl h G' rs
  fold-cong = hide-all-cong w

  add-inert : ∀ {G T : Gr} rs →
              All (λ r → Prf ((∀ (z : V) → T r z ≈ εₘ) ∧ (∀ (z : V) → T z r ≈ εₘ))) rs →
              ∀ x y →
              foldl h (λ x' y' → G x' y' +ₘ T x' y') rs x y ≈ (foldl h G rs x y +ₘ T x y)
  add-inert []               []                   x y = ≈-refl
  add-inert {G} {T} (r ∷ rs) (⟪ (zr , zc) ⟫ ∷ zs) x y =
    ≈-trans (fold-cong rs step x y) (add-inert {h G r} {T} rs zs x y)
    where
    step : h (λ x' y' → G x' y' +ₘ T x' y') r ≐ (λ x' y' → h G r x' y' +ₘ T x' y')
    step x' y' =
      ≈-trans
        (+ₘ-cong ≈-refl (∘-cong (≈-trans (+ₘ-cong ≈-refl (zr y')) (+ₘ-runit (G r y')))
                                (≈-trans (+ₘ-cong ≈-refl (zc x')) (+ₘ-runit (G x' r)))))
        (shift (G x' y') (T x' y') (G r y' ∘ G x' r))

  agree-add : ∀ {G G' : Gr} rs →
              (∀ x y → (G x y +ₘ G' x y) ≈ G' x y) →
              All (λ r → Prf ((∀ (z : V) → G' r z ≈ G r z) ∧ (∀ (z : V) → G' z r ≈ G z r))) rs →
              ∀ x y →
              foldl h G' rs x y ≈ (G' x y +ₘ foldl h G rs x y)
  agree-add {G} {G'} []       sub _                   x y = ≈-sym (≈-trans +ₘ-comm (sub x y))
  agree-add {G} {G'} (r ∷ rs) sub (⟪ (ar , ac) ⟫ ∷ as) x y =
    ≈-trans (agree-add {h G r} {h G' r} rs sub' all' x y)
    (≈-trans (+ₘ-cong (step x y) ≈-refl)
    (≈-trans +ₘ-assoc
             (+ₘ-cong ≈-refl (≈-sym (increasing {h G r} rs x y)))))
    where
    step : ∀ x' y' → h G' r x' y' ≈ (G' x' y' +ₘ h G r x' y')
    step x' y' =
      ≈-trans
        (+ₘ-cong ≈-refl (∘-cong (ar y') (ac x')))
        (insert (G x' y') (G' x' y') (G r y' ∘ G x' r) (sub x' y'))

    sub' : ∀ x' y' → (h G r x' y' +ₘ h G' r x' y') ≈ h G' r x' y'
    sub' x' y' =
      ≈-trans (+ₘ-cong ≈-refl (step x' y'))
      (≈-trans (absorbʳ (h G r x' y') (G' x' y')) (≈-sym (step x' y')))

    all' : All (λ r' → Prf ((∀ (z : V) → h G' r r' z ≈ h G r r' z)
                          ∧ (∀ (z : V) → h G' r z r' ≈ h G r z r'))) rs
    all' = All-map
      (λ {r'} pq →
        ⟪
          (λ z → ≈-trans (step r' z)
                 (≈-trans (+ₘ-cong (proj₁ (Prf.prf pq) z) ≈-refl)
                          (absorbˡ (G r' z) (G r z ∘ G r' r)))) ,
          (λ z → ≈-trans (step z r')
                 (≈-trans (+ₘ-cong (proj₂ (Prf.prf pq) z) ≈-refl)
                          (absorbˡ (G z r') (G r r' ∘ G z r)))) ⟫)
      as

module Ordered {V : Set} (vertex-object : V → Semimodule) (_<_ : V → V → Set) (o : IsStrictOrder _<_) where

  open IsStrictOrder o using (trans; asym)

  Fwd : Relation vertex-object → Set
  Fwd G = ∀ x y → (x < y) ⊎ Prf (G x y ≈ εₘ)

  private
    ⊥-elimₚ : ∀ {P : Prop} → ⊥ → P
    ⊥-elimₚ ()

  fwd-hide : ∀ {G} r → Fwd G → Fwd (hide vertex-object G r)
  fwd-hide {G} r fwd x y with fwd x y | fwd r y | fwd x r
  ... | inj₁ a     | _          | _          = inj₁ a
  ... | inj₂ _     | inj₁ ry    | inj₁ xr    = inj₁ (trans x r y xr ry)
  ... | inj₂ ⟪ z ⟫ | inj₂ ⟪ e ⟫ | _          =
    inj₂ ⟪ ≈-trans (+ₘ-cong z (≈-trans {g = εₘ {vertex-object r} {vertex-object y} ∘ G x r} (∘-cong₁ {f₁ = G r y} {f₂ = εₘ} {g = G x r} e) (CM.comp-bilinear-ε₁ {Z = vertex-object y} (G x r)))) (+ₘ-lunit εₘ) ⟫
  ... | inj₂ ⟪ z ⟫ | inj₁ _     | inj₂ ⟪ e ⟫ =
    inj₂ ⟪ ≈-trans (+ₘ-cong z (≈-trans {g = G r y ∘ εₘ {vertex-object x} {vertex-object r}} (∘-cong₂ {f = G r y} e) (CM.comp-bilinear-ε₂ {X = vertex-object x} (G r y)))) (+ₘ-lunit εₘ) ⟫

  fwd-hide-all : ∀ {G} rs → Fwd G → Fwd (hide-all vertex-object G rs)
  fwd-hide-all []       fwd = fwd
  fwd-hide-all (r ∷ rs) fwd = fwd-hide-all rs (fwd-hide r fwd)

  private
    cycle : ∀ {G} → Fwd G → ∀ r r' → (G r' r ∘ G r r') ≈ εₘ
    cycle {G} fwd r r' with fwd r' r | fwd r r'
    ... | inj₁ a     | inj₁ b     = ⊥-elimₚ (asym r' r a b)
    ... | inj₂ ⟪ e ⟫ | _          = ≈-trans {g = εₘ {vertex-object r'} {vertex-object r} ∘ G r r'} (∘-cong₁ {f₁ = G r' r} {f₂ = εₘ} {g = G r r'} e) (CM.comp-bilinear-ε₁ {Z = vertex-object r} (G r r'))
    ... | inj₁ _     | inj₂ ⟪ e ⟫ = ≈-trans {g = G r' r ∘ εₘ {vertex-object r} {vertex-object r'}} (∘-cong₂ {f = G r' r} e) (CM.comp-bilinear-ε₂ {X = vertex-object r} (G r' r))

    both : ∀ (G : Relation vertex-object) r r' x y → vertex-object x ⇒ vertex-object y
    both G r r' x y =
      (G x y +ₘ (G r y ∘ G x r)) +ₘ
      (((G r' y ∘ G x r') +ₘ (G r' y ∘ (G r r' ∘ G x r))) +ₘ ((G r y ∘ G r' r) ∘ G x r'))

    expand : ∀ {G} → Fwd G → ∀ r r' x y → hide vertex-object (hide vertex-object G r) r' x y ≈ both G r r' x y
    expand {G} fwd r r' x y =
      ≈-trans (+ₘ-cong ≈-refl (CM.comp-bilinear₁ (G r' y) (G r y ∘ G r' r) (G x r' +ₘ (G r r' ∘ G x r))))
      (≈-trans (+ₘ-cong ≈-refl (+ₘ-cong (CM.comp-bilinear₂ (G r' y) (G x r') (G r r' ∘ G x r))
                                        (CM.comp-bilinear₂ (G r y ∘ G r' r) (G x r') (G r r' ∘ G x r))))
               (+ₘ-cong ≈-refl (+ₘ-cong ≈-refl
                 (≈-trans (+ₘ-cong ≈-refl vanish) (+ₘ-runit ((G r y ∘ G r' r) ∘ G x r'))))))
      where
      vanish : ((G r y ∘ G r' r) ∘ (G r r' ∘ G x r)) ≈ εₘ
      vanish =
        ≈-trans (assoc (G r y) (G r' r) (G r r' ∘ G x r))
        (≈-trans (∘-cong₂ {f = G r y} (≈-sym (assoc (G r' r) (G r r') (G x r))))
        (≈-trans (∘-cong₂ {f = G r y} (∘-cong₁ {f₁ = G r' r ∘ G r r'} {f₂ = εₘ} {g = G x r} (cycle fwd r r')))
        (≈-trans (∘-cong₂ {f = G r y} (CM.comp-bilinear-ε₁ {Z = vertex-object r} (G x r)))
                 (CM.comp-bilinear-ε₂ {X = vertex-object x} (G r y)))))

    swap : ∀ G r r' x y → both G r r' x y ≈ both G r' r x y
    swap G r r' x y =
      ≈-trans (+ₘ-assoc {f = a} {g = b} {h = (c +ₘ d) +ₘ e})
      (≈-trans (+ₘ-cong ≈-refl (+ₘ-cong ≈-refl (+ₘ-assoc {f = c} {g = d} {h = e})))
      (≈-trans (+ₘ-cong ≈-refl (+ₘ-swap-mid b c (d +ₘ e)))
      (≈-trans (+ₘ-cong ≈-refl (+ₘ-cong ≈-refl (+ₘ-cong ≈-refl (+ₘ-comm {f = d} {g = e}))))
      (≈-trans (+ₘ-cong ≈-refl (+ₘ-cong ≈-refl (≈-sym (+ₘ-assoc {f = b} {g = e} {h = d}))))
      (≈-trans (≈-sym (+ₘ-assoc {f = a} {g = c} {h = (b +ₘ e) +ₘ d}))
               (+ₘ-cong ≈-refl (+ₘ-cong (+ₘ-cong ≈-refl (assoc (G r y) (G r' r) (G x r')))
                                        (≈-sym (assoc (G r' y) (G r r') (G x r))))))))))
      where
      a = G x y
      b = G r y ∘ G x r
      c = G r' y ∘ G x r'
      d = G r' y ∘ (G r r' ∘ G x r)
      e = (G r y ∘ G r' r) ∘ G x r'

    comm : ∀ {G} → Fwd G → ∀ r r' →
           hide vertex-object (hide vertex-object G r) r' ≐ hide vertex-object (hide vertex-object G r') r
    comm {G} fwd r r' x y =
      ≈-trans (expand fwd r r' x y) (≈-trans (swap G r r' x y) (≈-sym (expand fwd r' r x y)))

  hide-all-perm : ∀ {G rs rs'} → Fwd G → rs ↭ rs' → hide-all vertex-object G rs ≐ hide-all vertex-object G rs'
  hide-all-perm fwd ↭.refl x y = ≈-refl
  hide-all-perm fwd (↭.prep r p) = hide-all-perm (fwd-hide r fwd) p
  hide-all-perm fwd (↭.swap {xs = rs} a b p) x y =
    ≈-trans (hide-all-cong vertex-object rs (comm fwd a b) x y)
            (hide-all-perm (fwd-hide a (fwd-hide b fwd)) p x y)
  hide-all-perm fwd (↭.trans p q) x y = ≈-trans (hide-all-perm fwd p x y) (hide-all-perm fwd q x y)

module _ {X Y : Semimodule} (B : Graph X Y) where
  open Graph B

  Path⁺ : Set
  Path⁺ = Vertex shape ⊎ Root

  object⁺ : Path⁺ → Semimodule
  object⁺ = [ object , (λ _ → Y) ]

  fo⁺ : Path⁺ → Bool
  fo⁺ = [ fo , (λ _ → fo-root) ]

  into⁺ : (q : Path⁺) → X ⇒ object⁺ q
  into⁺ (inj₁ q) = into q
  into⁺ (inj₂ _) = out

  up-root⁺ : ∀ {K : Semimodule} → Y ⇒ K → (q : Path⁺) → object⁺ q ⇒ K
  up-root⁺ u (inj₁ _) = εₘ
  up-root⁺ u (inj₂ _) = u

  inside⁺ : (p q : Path⁺) → object⁺ p ⇒ object⁺ q
  inside⁺ (inj₁ p) (inj₁ q) = inside p q
  inside⁺ (inj₁ p) (inj₂ _) = up p
  inside⁺ (inj₂ _) _        = εₘ

  _<⁺_ : Path⁺ → Path⁺ → Set
  _<⁺_ = lts (shape ∷ [])

  <⁺-order : IsStrictOrder _<⁺_
  <⁺-order = lts-order (shape ∷ [])

  <⁺-inside : ∀ p q → (p <⁺ q) ⊎ Prf (inside⁺ p q ≈ εₘ)
  <⁺-inside (inj₁ p) (inj₁ q) = <-inside p q
  <⁺-inside (inj₁ p) (inj₂ _) = inj₁ tt
  <⁺-inside (inj₂ _) q        = inj₂ ⟪ ≈-refl ⟫

  paths⁺ : List Path⁺
  paths⁺ = inj₂ root ∷ map inj₁ (vertices shape)

  V : Set
  V = Input ⊎ Path⁺

  vertex-object : V → Semimodule
  vertex-object = [ (λ _ → X) , object⁺ ]

  gr : Relation vertex-object
  gr (inj₁ _) (inj₂ q) = into⁺ q
  gr (inj₂ p) (inj₂ q) = inside⁺ p q
  gr _        (inj₁ _) = εₘ

  collapse : X ⇒ Y
  collapse = hide-all vertex-object gr (map (λ q → inj₂ (inj₁ q)) (vertices shape)) (inj₁ input) (inj₂ (inj₂ root))

  FO : List (Vertex shape)
  FO = filterᵇ fo (vertices shape)

  fo-hidden : List (Vertex shape)
  fo-hidden = filterᵇ (λ q → not (fo q)) (vertices shape)

  fo-graph : Relation vertex-object
  fo-graph = hide-all vertex-object gr (map (λ q → inj₂ (inj₁ q)) fo-hidden)

  _<ᵥ_ : V → V → Set
  _<ᵥ_ = sum-< (λ _ _ → ⊥) _<⁺_

  <ᵥ-order : IsStrictOrder _<ᵥ_
  <ᵥ-order = sum-<-order none-order <⁺-order

  private
    module O = Ordered vertex-object _<ᵥ_ <ᵥ-order

  open O public using (Fwd; fwd-hide; fwd-hide-all; hide-all-perm)

  gr-forward : Fwd gr
  gr-forward (inj₁ _) (inj₂ q) = inj₁ tt
  gr-forward (inj₂ p) (inj₂ q) = <⁺-inside p q
  gr-forward (inj₁ _) (inj₁ _) = inj₂ ⟪ ≈-refl ⟫
  gr-forward (inj₂ p) (inj₁ _) = inj₂ ⟪ ≈-refl ⟫

  fo-forward : Fwd fo-graph
  fo-forward = fwd-hide-all (map (λ q → inj₂ (inj₁ q)) fo-hidden) gr-forward

private
  distrib-root : ∀ {W N K L : Semimodule} (P : N ⇒ W) (Xm : K ⇒ N) (Ym : L ⇒ N) (Zm : K ⇒ L) →
                 ((P ∘ Xm) +ₘ ((P ∘ Ym) ∘ Zm)) ≈ (P ∘ (Xm +ₘ (Ym ∘ Zm)))
  distrib-root P Xm Ym Zm =
    ≈-trans (+ₘ-cong ≈-refl (assoc P Ym Zm)) (≈-sym (CM.comp-bilinear₂ P Xm (Ym ∘ Zm)))

  root-step : ∀ {W N L K : Semimodule} {P : N ⇒ W} {G₁ : K ⇒ W} {Xm : K ⇒ N}
              {G₂ : L ⇒ W} {Ym : L ⇒ N} {G₃ Zm : K ⇒ L} →
              G₁ ≈ (P ∘ Xm) → G₂ ≈ (P ∘ Ym) → G₃ ≈ Zm →
              (G₁ +ₘ (G₂ ∘ G₃)) ≈ (P ∘ (Xm +ₘ (Ym ∘ Zm)))
  root-step {P = P} {Xm = Xm} {Ym = Ym} {Zm = Zm} a b c = ≈-trans (+ₘ-cong a (∘-cong b c)) (distrib-root P Xm Ym Zm)

  offset-step : ∀ {W N L K : Semimodule} {Km : K ⇒ W} {P : N ⇒ W} {G₁ : K ⇒ W}
                {Xm : K ⇒ N} {G₂ : L ⇒ W} {Ym : L ⇒ N} {G₃ Zm : K ⇒ L} →
                G₁ ≈ (Km +ₘ (P ∘ Xm)) → G₂ ≈ (P ∘ Ym) → G₃ ≈ Zm →
                (G₁ +ₘ (G₂ ∘ G₃)) ≈ (Km +ₘ (P ∘ (Xm +ₘ (Ym ∘ Zm))))
  offset-step {Km = Km} {P} {Xm = Xm} {Ym = Ym} {Zm = Zm} a b c =
    ≈-trans (+ₘ-cong a (∘-cong b c))
            (≈-trans (+ₘ-assoc {f = Km} {g = P ∘ Xm} {h = (P ∘ Ym) ∘ Zm}) (+ₘ-cong ≈-refl (distrib-root P Xm Ym Zm)))

-- Hiding one premise's vertices, one at a time, inside the conclusion's graph. The state records
-- the premise's own relations as they accumulate; Φ carries the premise's input columns to the
-- conclusion's, which for a premise evaluated in a substituted environment is not the identity.
module _ {X Y : Semimodule} (B : Graph X Y) where

  root-row : ∀ y → gr B (inj₂ (inj₂ root)) y ≈ εₘ
  root-row (inj₁ _) = ≈-refl {f = εₘ}
  root-row (inj₂ _) = ≈-refl {f = εₘ}

  hide-paths⁺ : hide-all (vertex-object B) (gr B) (map inj₂ (paths⁺ B)) (inj₁ input) (inj₂ (inj₂ root))
                ≈ collapse B
  hide-paths⁺ =
    ≈-trans (≡-to-≈ (≡-cong (λ l → hide-all (vertex-object B) (gr B) l (inj₁ input) (inj₂ (inj₂ root)))
                            (≡-cong (inj₂ (inj₂ root) ∷_) (≡-sym (map-∘ {g = inj₂} {f = inj₁} (vertices (Graph.shape B)))))))
            (hide-all-cong (vertex-object B) (map (λ q → inj₂ (inj₁ q)) (vertices (Graph.shape B)))
                           (hide-sink (vertex-object B) (gr B) (inj₂ (inj₂ root)) root-row)
                           (inj₁ input) (inj₂ (inj₂ root)))

module HidePremise
  {XB YB : Semimodule} (B : Graph XB YB)
  {V : Set} (object' : V → Semimodule)
  (inp : V)
  (blk : Path⁺ B → V)
  {T : Set} (tgt : T → V)
  {M' : Semimodule} (Φ : object' inp ⇒ M')
  (P : (t : T) → object' (blk (inj₂ root)) ⇒ object' (tgt t))
  (K : (t : T) → object' inp ⇒ object' (tgt t))
  where

  record St : Set where
    field
      into   : (q : Path⁺ B) → M' ⇒ object' (blk q)
      inside : (p q : Path⁺ B) → object' (blk p) ⇒ object' (blk q)

  open St public

  step : St → (Path⁺ B) → St
  step H w .into q = H .into q +ₘ (H .inside w q ∘ H .into w)
  step H w .inside p q = H .inside p q +ₘ (H .inside w q ∘ H .inside p w)

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
             ≈ ((H .into q ∘ Φ) +ₘ (H .inside w q ∘ (H .into w ∘ Φ)))
    Φ-step H w q =
      ≈-trans (CM.comp-bilinear₁ (H .into q) (H .inside w q ∘ H .into w) Φ)
              (+ₘ-cong ≈-refl (assoc (H .inside w q) (H .into w) Φ))

  record Agrees (G : Relation object') (H : St) : Set where
    field
      into-ok   : ∀ q → G inp (blk q) ≈ (H .into q ∘ Φ)
      inside-ok : ∀ p q → G (blk p) (blk q) ≈ H .inside p q
      tgt-ok    : ∀ t → G inp (tgt t) ≈ (K t +ₘ (P t ∘ (H .into (inj₂ root) ∘ Φ)))
      up-ok     : ∀ t (p : Vertex (Graph.shape B)) → G (blk (inj₁ p)) (tgt t)
                                ≈ (P t ∘ H .inside (inj₁ p) (inj₂ root))

  open Agrees public

  agrees-hide : ∀ {G H} (w : Vertex (Graph.shape B)) → Agrees G H → Agrees (hide object' G (blk (inj₁ w))) (step H (inj₁ w))
  agrees-hide {H = H} w s .into-ok q =
    ≈-trans (+ₘ-cong (s .into-ok q) (∘-cong (s .inside-ok (inj₁ w) q) (s .into-ok (inj₁ w))))
            (≈-sym (Φ-step H (inj₁ w) q))
  agrees-hide w s .inside-ok p q =
    +ₘ-cong (s .inside-ok p q) (∘-cong (s .inside-ok (inj₁ w) q) (s .inside-ok p (inj₁ w)))
  agrees-hide {H = H} w s .tgt-ok t =
    ≈-trans (offset-step {Km = K t} {P = P t}
                         {Xm = H .into (inj₂ root) ∘ Φ}
                         {Ym = H .inside (inj₁ w) (inj₂ root)}
                         {Zm = H .into (inj₁ w) ∘ Φ}
              (s .tgt-ok t) (s .up-ok t w) (s .into-ok (inj₁ w)))
            (+ₘ-cong ≈-refl (∘-cong₂ {f = P t} (≈-sym (Φ-step H (inj₁ w) (inj₂ root)))))
  agrees-hide {H = H} w s .up-ok t p =
    root-step {P = P t} {Xm = H .inside (inj₁ p) (inj₂ root)}
              {Ym = H .inside (inj₁ w) (inj₂ root)} {Zm = H .inside (inj₁ p) (inj₁ w)}
      (s .up-ok t p) (s .up-ok t w) (s .inside-ok (inj₁ p) (inj₁ w))

  agrees-hide-all : ∀ {G H} (ws : List (Vertex (Graph.shape B))) → Agrees G H →
                    Agrees (hide-all object' G (map (λ w → blk (inj₁ w)) ws)) (steps H (map inj₁ ws))
  agrees-hide-all []       s = s
  agrees-hide-all (w ∷ ws) s = agrees-hide-all ws (agrees-hide w s)

  -- The relations a rule contributes, before the graph's root is hidden. Every edge from the graph to
  -- a target leaves the graph's root, which here is a matter of the vertex set rather than a lemma.
  record Start (G : Relation object') (H : St) : Set where
    field
      into-start   : ∀ q → G inp (blk q) ≈ (H .into q ∘ Φ)
      inside-start : ∀ p q → G (blk p) (blk q) ≈ H .inside p q
      tgt-start    : ∀ t → G inp (tgt t) ≈ K t
      up-start     : ∀ t → G (blk (inj₂ root)) (tgt t) ≈ P t
      off-start    : ∀ t (p : Vertex (Graph.shape B)) → G (blk (inj₁ p)) (tgt t) ≈ εₘ
      sink         : ∀ q → H .inside (inj₂ root) q ≈ εₘ

  open Start public

  agrees-start : ∀ {G H} → Start G H → Agrees (hide object' G (blk (inj₂ root))) (step H (inj₂ root))
  agrees-start {H = H} r .into-ok q =
    ≈-trans (+ₘ-cong (r .into-start q)
                     (∘-cong (r .inside-start (inj₂ root) q) (r .into-start (inj₂ root))))
            (≈-sym (Φ-step H (inj₂ root) q))
  agrees-start r .inside-ok p q =
    +ₘ-cong (r .inside-start p q)
            (∘-cong (r .inside-start (inj₂ root) q) (r .inside-start p (inj₂ root)))
  agrees-start {H = H} r .tgt-ok t =
    ≈-trans (+ₘ-cong (r .tgt-start t)
                     (∘-cong (r .up-start t) (r .into-start (inj₂ root))))
            (+ₘ-cong ≈-refl (∘-cong₂ {f = P t} (≈-sym unchanged)))
    where
    unchanged : (step H (inj₂ root) .into (inj₂ root) ∘ Φ) ≈ (H .into (inj₂ root) ∘ Φ)
    unchanged =
      ≈-trans (Φ-step H (inj₂ root) (inj₂ root))
              (≈-trans (+ₘ-cong ≈-refl (∘-cong₁ {f₁ = H .inside (inj₂ root) (inj₂ root)} {f₂ = εₘ} {g = H .into (inj₂ root) ∘ Φ} (r .sink (inj₂ root))))
                       (absorb₁ (H .into (inj₂ root) ∘ Φ) (H .into (inj₂ root) ∘ Φ)))
  agrees-start {H = H} r .up-ok t p =
    ≈-trans (+ₘ-cong (r .off-start t p)
                     (∘-cong (r .up-start t) (r .inside-start (inj₁ p) (inj₂ root))))
    (≈-trans (+ₘ-lunit (P t ∘ H .inside (inj₁ p) (inj₂ root)))
             (∘-cong₂ {f = P t} (≈-sym unchanged)))
    where
    unchanged : step H (inj₂ root) .inside (inj₁ p) (inj₂ root)
                ≈ H .inside (inj₁ p) (inj₂ root)
    unchanged =
      ≈-trans (+ₘ-cong ≈-refl (∘-cong₁ {f₁ = H .inside (inj₂ root) (inj₂ root)} {f₂ = εₘ} {g = H .inside (inj₁ p) (inj₂ root)} (r .sink (inj₂ root))))
              (absorb₁ (H .inside (inj₁ p) (inj₂ root)) (H .inside (inj₁ p) (inj₂ root)))

  module Hidden (G₀ : Relation object') (prem : Relation (vertex-object B) → St)
                (prem-step : ∀ G w → step (prem G) w ≡ prem (hide (vertex-object B) G (inj₂ w))) where

    H⁰ : St
    H⁰ = prem (gr B)

    G : Relation object'
    G = hide-all object' (hide object' G₀ (blk (inj₂ root))) (map (λ w → blk (inj₁ w)) (vertices (Graph.shape B)))

    H : St
    H = steps (step H⁰ (inj₂ root)) (map inj₁ (vertices (Graph.shape B)))

    done : Start G₀ H⁰ → Agrees G H
    done start = agrees-hide-all (vertices (Graph.shape B)) (agrees-start start)

    κ : H .into (inj₂ root) ≡ prem (hide-all (vertex-object B) (gr B) (map inj₂ (paths⁺ B))) .into (inj₂ root)
    κ = ≡-cong (λ H' → H' .into (inj₂ root)) (folds prem inj₂ (hide (vertex-object B)) prem-step (paths⁺ B) (gr B))

module NoEdgeIntoHidden
  {V : Set} (vertex-object : V → Semimodule)
  {W : Set} (hid : W → V)
  {S : Set} (src : S → V)
  {T : Set} (col : T → V)
  (B : (s : S) (t : T) → vertex-object (src s) ⇒ vertex-object (col t))
  where

  record Fixed (G : Relation vertex-object) : Set where
    field
      edge    : ∀ s t → G (src s) (col t) ≈ B s t
      no-edge : ∀ s w → G (src s) (hid w) ≈ εₘ

  open Fixed public

  fixed-hide : ∀ {G} (w : W) → Fixed G → Fixed (hide vertex-object G (hid w))
  fixed-hide {G} w k .edge s t =
    ≈-trans (+ₘ-cong (k .edge s t) (∘-cong₂ {f = G (hid w) (col t)} (k .no-edge s w)))
            (absorb₂ (B s t) (G (hid w) (col t)))
  fixed-hide {G} w k .no-edge s w' =
    ≈-trans (+ₘ-cong (k .no-edge s w') (∘-cong₂ {f = G (hid w) (hid w')} (k .no-edge s w)))
            (absorb₂ εₘ (G (hid w) (hid w')))

  fixed-hide-all : ∀ {G} {W' : Set} (f : W' → W) (ws : List W') →
                   Fixed G → Fixed (hide-all vertex-object G (map (λ w → hid (f w)) ws))
  fixed-hide-all f []       k = k
  fixed-hide-all f (w ∷ ws) k = fixed-hide-all f ws (fixed-hide (f w) k)

  fixed-resp : ∀ {G G'} → G ≐ G' → Fixed G → Fixed G'
  fixed-resp e k .edge s t = ≈-trans (≈-sym (e (src s) (col t))) (k .edge s t)
  fixed-resp e k .no-edge s w = ≈-trans (≈-sym (e (src s) (hid w))) (k .no-edge s w)

private
  factor : ∀ {Xo Yo Zo Wo Vo : Semimodule} (A : Yo ⇒ Zo) (r : Xo ⇒ Yo) (l : Wo ⇒ Yo)
           {h c : Vo ⇒ Wo} (ρ : Xo ⇒ Vo) → h ≈ c →
           ((A ∘ r) +ₘ ((A ∘ l) ∘ (h ∘ ρ))) ≈ (A ∘ (r +ₘ (l ∘ (c ∘ ρ))))
  factor A r l {h} {c} ρ e =
    ≈-trans (+ₘ-cong ≈-refl (≈-trans (∘-cong₂ {f = A ∘ l} (∘-cong₁ {f₁ = h} {f₂ = c} {g = ρ} e)) (assoc A l (c ∘ ρ))))
            (≈-sym (CM.comp-bilinear₂ A r (l ∘ (c ∘ ρ))))

private
  ∘-pair : ∀ {L M2 N2 K : Semimodule} (A : (M2 ⊕ᵥ N2) ⇒ L) (Xm : K ⇒ M2) (Ym : K ⇒ N2) →
           (A ∘ ⟨ Xm , Ym ⟩) ≈ (((A ∘ inb₁) ∘ Xm) +ₘ ((A ∘ inb₂) ∘ Ym))
  ∘-pair A Xm Ym =
    ≈-trans (CM.comp-bilinear₂ A (inb₁ ∘ Xm) (inb₂ ∘ Ym))
            (+ₘ-cong (≈-sym (assoc A inb₁ Xm)) (≈-sym (assoc A inb₂ Ym)))

module NoEdgeOutOfHidden
  {V : Set} (vertex-object : V → Semimodule)
  {W : Set} (hid : W → V)
  {S : Set} (src : S → V)
  {T : Set} (col : T → V)
  (B : (s : S) (t : T) → vertex-object (src s) ⇒ vertex-object (col t))
  where

  record Fixed (G : Relation vertex-object) : Set where
    field
      edge    : ∀ s t → G (src s) (col t) ≈ B s t
      no-edge : ∀ w t → G (hid w) (col t) ≈ εₘ

  open Fixed public

  fixed-hide : ∀ {G} (w : W) → Fixed G → Fixed (hide vertex-object G (hid w))
  fixed-hide {G} w k .edge s t =
    ≈-trans (+ₘ-cong (k .edge s t)
                     (≈-trans {g = εₘ {vertex-object (hid w)} {vertex-object (col t)} ∘ G (src s) (hid w)}
                              (∘-cong₁ {f₁ = G (hid w) (col t)} {f₂ = εₘ} {g = G (src s) (hid w)} (k .no-edge w t))
                              (CM.comp-bilinear-ε₁ {Z = vertex-object (col t)} (G (src s) (hid w)))))
            (+ₘ-runit (B s t))
  fixed-hide {G} w k .no-edge w' t =
    ≈-trans (+ₘ-cong (k .no-edge w' t)
                     (≈-trans {g = εₘ {vertex-object (hid w)} {vertex-object (col t)} ∘ G (hid w') (hid w)}
                              (∘-cong₁ {f₁ = G (hid w) (col t)} {f₂ = εₘ} {g = G (hid w') (hid w)} (k .no-edge w t))
                              (CM.comp-bilinear-ε₁ {Z = vertex-object (col t)} (G (hid w') (hid w)))))
            (+ₘ-runit εₘ)

  fixed-hide-all : ∀ {G} {W' : Set} (f : W' → W) (ws : List W') →
                   Fixed G → Fixed (hide-all vertex-object G (map (λ w → hid (f w)) ws))
  fixed-hide-all f []       k = k
  fixed-hide-all f (w ∷ ws) k = fixed-hide-all f ws (fixed-hide (f w) k)

module Rule₀
  {X Y : Semimodule} (fo-root : Bool)
  (out-root : X ⇒ Y)
  where

  E : Graph X Y
  E .Graph.shape = node []
  E .Graph.object ()
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
  {X : Semimodule}
  {XB YB : Semimodule} (B : Graph XB YB)
  {Y : Semimodule}
  (inputs : X ⇒ XB)
  (fo-root : Bool)
  (out-root : X ⇒ Y)
  (up-root : YB ⇒ Y)
  where

  E : Graph X Y
  E .Graph.shape = node (Graph.shape B ∷ [])
  E .Graph.object = object⁺ B
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

    module S = HidePremise B (vertex-object E) (inj₁ input) b (λ (_ : Root) → er) inputs (λ _ → up-root) (λ _ → out-root)

    prem : Relation (vertex-object B) → S.St
    prem G .S.into q = G (inj₁ input) (inj₂ q)
    prem G .S.inside p q = G (inj₂ p) (inj₂ q)

    module hidden = S.Hidden (gr E) prem (λ G w → ≡-refl)

    start : S.Start (gr E) hidden.H⁰
    start .S.into-start q = ≈-refl
    start .S.inside-start p q = ≈-refl
    start .S.tgt-start _ = ≈-refl {f = out-root}
    start .S.up-start _ = ≈-refl {f = up-root}
    start .S.off-start _ p = ≈-refl {f = εₘ}
    start .S.sink q = ≈-refl {f = εₘ}

    plumb : collapse E ≡ hidden.G (inj₁ input) er
    plumb = ≡-cong (λ l → hide-all (vertex-object E) (gr E) l (inj₁ input) er)
                   (≡-cong (b (inj₂ root) ∷_) (≡-sym (map-∘ {g = b} {f = inj₁} (vertices (Graph.shape B)))))

  agree : collapse E ≈ (out-root +ₘ (up-root ∘ (collapse B ∘ inputs)))
  agree =
    ≈-trans (≡-to-≈ plumb)
            (≈-trans (hidden.done start .S.tgt-ok root)
                     (+ₘ-cong ≈-refl (∘-cong₂ {f = up-root} (∘-cong₁ {g = inputs} (≈-trans (≡-to-≈ hidden.κ) (hide-paths⁺ B))))))

module Rule₂
  {X : Semimodule}
  {X₁ Y₁ : Semimodule} (B₁ : Graph X₁ Y₁)
  {X₂ Y₂ : Semimodule} (B₂ : Graph X₂ Y₂)
  {Y : Semimodule}
  (inputs₁ : X ⇒ X₁)
  (inputs₂ : (X ⊕ᵥ Y₁) ⇒ X₂)
  (fo-root : Bool)
  (out-root : X ⇒ Y)
  (up₁ : Y₁ ⇒ Y)
  (up₂ : Y₂ ⇒ Y)
  where

  private
    from-inputs₂ : X ⇒ X₂
    from-inputs₂ = inputs₂ ∘ inb₁ {X} {Y₁}

    from-root₁ : Y₁ ⇒ X₂
    from-root₁ = inputs₂ ∘ inb₂ {X} {Y₁}

    ps₁ = vertices (Graph.shape B₁)
    ps₂ = vertices (Graph.shape B₂)

  E : Graph X Y
  E .Graph.shape = node (Graph.shape B₁ ∷ Graph.shape B₂ ∷ [])
  E .Graph.object = [ object⁺ B₁ , object⁺ B₂ ]
  E .Graph.fo = [ fo⁺ B₁ , fo⁺ B₂ ]
  E .Graph.into (inj₁ q) = into⁺ B₁ q ∘ inputs₁
  E .Graph.into (inj₂ q) = into⁺ B₂ q ∘ from-inputs₂
  E .Graph.inside (inj₁ p)        (inj₁ q) = inside⁺ B₁ p q
  E .Graph.inside (inj₁ (inj₁ p)) (inj₂ q) = εₘ
  E .Graph.inside (inj₁ (inj₂ _)) (inj₂ q) = into⁺ B₂ q ∘ from-root₁
  E .Graph.inside (inj₂ p)        (inj₁ q) = εₘ
  E .Graph.inside (inj₂ p)        (inj₂ q) = inside⁺ B₂ p q
  E .Graph.fo-root = fo-root
  E .Graph.<-inside (inj₁ (inj₁ p)) (inj₁ (inj₁ q)) = Graph.<-inside B₁ p q
  E .Graph.<-inside (inj₁ (inj₁ p)) (inj₁ (inj₂ _)) = inj₁ tt
  E .Graph.<-inside (inj₁ (inj₂ _)) (inj₁ _) = inj₂ ⟪ ≈-refl ⟫
  E .Graph.<-inside (inj₁ (inj₁ p)) (inj₂ q) = inj₁ tt
  E .Graph.<-inside (inj₁ (inj₂ _)) (inj₂ q) = inj₁ tt
  E .Graph.<-inside (inj₂ p)        (inj₁ q) = inj₂ ⟪ ≈-refl ⟫
  E .Graph.<-inside (inj₂ (inj₁ p)) (inj₂ (inj₁ q)) = Graph.<-inside B₂ p q
  E .Graph.<-inside (inj₂ (inj₁ p)) (inj₂ (inj₂ _)) = inj₁ tt
  E .Graph.<-inside (inj₂ (inj₂ _)) (inj₂ _) = inj₂ ⟪ ≈-refl ⟫
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

    P₁ : (t : Path⁺ B₂ ⊎ Root) → Y₁ ⇒ vertex-object E (tgt₁ t)
    P₁ (inj₁ q) = into⁺ B₂ q ∘ from-root₁
    P₁ (inj₂ _) = up₁

    K₁ : (t : Path⁺ B₂ ⊎ Root) → X ⇒ vertex-object E (tgt₁ t)
    K₁ (inj₁ q) = into⁺ B₂ q ∘ from-inputs₂
    K₁ (inj₂ _) = out-root

    module S₁ = HidePremise B₁ (vertex-object E) (inj₁ input) b1 tgt₁ inputs₁ P₁ K₁

    prem₁ : Relation (vertex-object B₁) → S₁.St
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
    start₁ .S₁.off-start (inj₁ q) p = ≈-refl {f = εₘ}
    start₁ .S₁.off-start (inj₂ _) p = ≈-refl {f = εₘ}
    start₁ .S₁.sink q = ≈-refl {f = εₘ}

    done₁ = hidden₁.done start₁
    κ₁ = ≈-trans (≡-to-≈ hidden₁.κ) (hide-paths⁺ B₁)

  Φ₂ : X ⇒ X₂
  Φ₂ = inputs₂ ∘ ⟨ I , collapse B₁ ∘ inputs₁ ⟩

  private
    Φ₂' : X ⇒ X₂
    Φ₂' = from-inputs₂ +ₘ (from-root₁ ∘ (collapse B₁ ∘ inputs₁))

    Φ₂-split : Φ₂' ≈ Φ₂
    Φ₂-split = ≈-sym (≈-trans (∘-pair inputs₂ I (collapse B₁ ∘ inputs₁))
                              (+ₘ-cong (id-right {f = from-inputs₂}) (≈-refl {f = from-root₁ ∘ (collapse B₁ ∘ inputs₁)})))

    module S₂ = HidePremise B₂ (vertex-object E) (inj₁ input) b2 (λ (_ : Root) → er) Φ₂' (λ _ → up₂)
                            (λ _ → out-root +ₘ (up₁ ∘ (collapse B₁ ∘ inputs₁)))

    prem₂ : Relation (vertex-object B₂) → S₂.St
    prem₂ G .S₂.into q = G (inj₁ input) (inj₂ q)
    prem₂ G .S₂.inside p q = G (inj₂ p) (inj₂ q)

    module hidden₂ = S₂.Hidden hidden₁.G prem₂ (λ G w → ≡-refl)

    Bh : (s : Path⁺ B₂) (t : Path⁺ B₂ ⊎ Root) → object⁺ B₂ s ⇒ vertex-object E (tgt₁ t)
    Bh s (inj₁ q) = inside⁺ B₂ s q
    Bh s (inj₂ _) = up-root⁺ B₂ up₂ s

    module IntoHidden = NoEdgeIntoHidden (vertex-object E) b1 b2 tgt₁ Bh

    fixed₀ : IntoHidden.Fixed (gr E)
    fixed₀ .IntoHidden.edge s (inj₁ q) = ≈-refl
    fixed₀ .IntoHidden.edge s (inj₂ _) = ≈-refl {f = up-root⁺ B₂ up₂ s}
    fixed₀ .IntoHidden.no-edge s w = ≈-refl {f = εₘ}

    fixed₁ : IntoHidden.Fixed hidden₁.G
    fixed₁ = IntoHidden.fixed-hide-all inj₁ ps₁ (IntoHidden.fixed-hide (inj₂ root) fixed₀)

    start₂ : S₂.Start hidden₁.G hidden₂.H⁰
    start₂ .S₂.into-start q =
      ≈-trans (done₁ .S₁.tgt-ok (inj₁ q))
              (factor (into⁺ B₂ q) from-inputs₂ from-root₁ {h = hidden₁.H .S₁.into (inj₂ root)} {c = collapse B₁} inputs₁ κ₁)
    start₂ .S₂.inside-start p q = fixed₁ .IntoHidden.edge p (inj₁ q)
    start₂ .S₂.tgt-start _ =
      ≈-trans {g = out-root +ₘ (up₁ ∘ (hidden₁.H .S₁.into (inj₂ root) ∘ inputs₁))}
              (done₁ .S₁.tgt-ok (inj₂ root)) (+ₘ-cong ≈-refl (∘-cong₂ {f = up₁} (∘-cong₁ {g = inputs₁} κ₁)))
    start₂ .S₂.up-start _ = fixed₁ .IntoHidden.edge (inj₂ root) (inj₂ root)
    start₂ .S₂.off-start _ p = fixed₁ .IntoHidden.edge (inj₁ p) (inj₂ root)
    start₂ .S₂.sink q = ≈-refl {f = εₘ}

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
      ≡-trans (≡-cong (λ l → hide-all (vertex-object E) (gr E) l (inj₁ input) er) lst)
              (≡-cong (λ G → G (inj₁ input) er)
                      (foldl-++ (hide (vertex-object E)) (gr E) (b1 (inj₂ root) ∷ map (λ w → b1 (inj₁ w)) ps₁) (b2 (inj₂ root) ∷ map (λ w → b2 (inj₁ w)) ps₂)))

  agree : collapse E ≈ ((out-root +ₘ (up₁ ∘ (collapse B₁ ∘ inputs₁))) +ₘ (up₂ ∘ (collapse B₂ ∘ Φ₂)))
  agree =
    ≈-trans (≡-to-≈ plumb)
            (≈-trans {g = (out-root +ₘ (up₁ ∘ (collapse B₁ ∘ inputs₁))) +ₘ (up₂ ∘ (hidden₂.H .S₂.into (inj₂ root) ∘ Φ₂'))}
                     (hidden₂.done start₂ .S₂.tgt-ok root)
                     (+ₘ-cong ≈-refl (∘-cong₂ {f = up₂} (∘-cong (≈-trans (≡-to-≈ hidden₂.κ) (hide-paths⁺ B₂)) Φ₂-split))))

module Rule₃
  {X : Semimodule}
  {X₁ Y₁ : Semimodule} (B₁ : Graph X₁ Y₁)
  {X₂ Y₂ : Semimodule} (B₂ : Graph X₂ Y₂)
  {X₃ Y₃ : Semimodule} (B₃ : Graph X₃ Y₃)
  {Y : Semimodule}
  (inputs₁ : X ⇒ X₁)
  (inputs₂ : X ⇒ X₂)
  (inputs₃ : ((X ⊕ᵥ Y₁) ⊕ᵥ Y₂) ⇒ X₃)
  (fo-root : Bool)
  (out-root : X ⇒ Y)
  (up₁ : Y₁ ⇒ Y)
  (up₂ : Y₂ ⇒ Y)
  (up₃ : Y₃ ⇒ Y)
  where

  private
    from-inputs₃ : X ⇒ X₃
    from-inputs₃ = (inputs₃ ∘ inb₁ {X ⊕ᵥ Y₁} {Y₂}) ∘ inb₁ {X} {Y₁}

    from-root₁ : Y₁ ⇒ X₃
    from-root₁ = (inputs₃ ∘ inb₁ {X ⊕ᵥ Y₁} {Y₂}) ∘ inb₂ {X} {Y₁}

    from-root₂ : Y₂ ⇒ X₃
    from-root₂ = inputs₃ ∘ inb₂ {X ⊕ᵥ Y₁} {Y₂}

    ps₁ = vertices (Graph.shape B₁)
    ps₂ = vertices (Graph.shape B₂)
    ps₃ = vertices (Graph.shape B₃)

    e₁₃ : (p : Path⁺ B₁) (q : Path⁺ B₃) → object⁺ B₁ p ⇒ object⁺ B₃ q
    e₁₃ (inj₁ _) q = εₘ
    e₁₃ (inj₂ _) q = into⁺ B₃ q ∘ from-root₁

    e₂₃ : (p : Path⁺ B₂) (q : Path⁺ B₃) → object⁺ B₂ p ⇒ object⁺ B₃ q
    e₂₃ (inj₁ _) q = εₘ
    e₂₃ (inj₂ _) q = into⁺ B₃ q ∘ from-root₂

  E : Graph X Y
  E .Graph.shape = node (Graph.shape B₁ ∷ Graph.shape B₂ ∷ Graph.shape B₃ ∷ [])
  E .Graph.object = [ object⁺ B₁ , [ object⁺ B₂ , object⁺ B₃ ] ]
  E .Graph.fo = [ fo⁺ B₁ , [ fo⁺ B₂ , fo⁺ B₃ ] ]
  E .Graph.into (inj₁ q)        = into⁺ B₁ q ∘ inputs₁
  E .Graph.into (inj₂ (inj₁ q)) = into⁺ B₂ q ∘ inputs₂
  E .Graph.into (inj₂ (inj₂ q)) = into⁺ B₃ q ∘ from-inputs₃
  E .Graph.inside (inj₁ p)        (inj₁ q)        = inside⁺ B₁ p q
  E .Graph.inside (inj₁ p)        (inj₂ (inj₁ q)) = εₘ
  E .Graph.inside (inj₁ p)        (inj₂ (inj₂ q)) = e₁₃ p q
  E .Graph.inside (inj₂ (inj₁ p)) (inj₁ q)        = εₘ
  E .Graph.inside (inj₂ (inj₂ p)) (inj₁ q)        = εₘ
  E .Graph.inside (inj₂ (inj₁ p)) (inj₂ (inj₁ q)) = inside⁺ B₂ p q
  E .Graph.inside (inj₂ (inj₂ p)) (inj₂ (inj₁ q)) = εₘ
  E .Graph.inside (inj₂ (inj₁ p)) (inj₂ (inj₂ q)) = e₂₃ p q
  E .Graph.inside (inj₂ (inj₂ p)) (inj₂ (inj₂ q)) = inside⁺ B₃ p q
  E .Graph.fo-root = fo-root
  E .Graph.<-inside (inj₁ (inj₁ p)) (inj₁ (inj₁ q)) = Graph.<-inside B₁ p q
  E .Graph.<-inside (inj₁ (inj₁ p)) (inj₁ (inj₂ _)) = inj₁ tt
  E .Graph.<-inside (inj₁ (inj₂ _)) (inj₁ _) = inj₂ ⟪ ≈-refl ⟫
  E .Graph.<-inside (inj₁ (inj₁ p)) (inj₂ q) = inj₁ tt
  E .Graph.<-inside (inj₁ (inj₂ _)) (inj₂ q) = inj₁ tt
  E .Graph.<-inside (inj₂ (inj₁ p)) (inj₁ q) = inj₂ ⟪ ≈-refl ⟫
  E .Graph.<-inside (inj₂ (inj₂ p)) (inj₁ q) = inj₂ ⟪ ≈-refl ⟫
  E .Graph.<-inside (inj₂ (inj₁ (inj₁ p))) (inj₂ (inj₁ (inj₁ q))) = Graph.<-inside B₂ p q
  E .Graph.<-inside (inj₂ (inj₁ (inj₁ p))) (inj₂ (inj₁ (inj₂ _))) = inj₁ tt
  E .Graph.<-inside (inj₂ (inj₁ (inj₂ _))) (inj₂ (inj₁ _)) = inj₂ ⟪ ≈-refl ⟫
  E .Graph.<-inside (inj₂ (inj₁ (inj₁ p))) (inj₂ (inj₂ _)) = inj₁ tt
  E .Graph.<-inside (inj₂ (inj₁ (inj₂ _))) (inj₂ (inj₂ _)) = inj₁ tt
  E .Graph.<-inside (inj₂ (inj₂ _))        (inj₂ (inj₁ _)) = inj₂ ⟪ ≈-refl ⟫
  E .Graph.<-inside (inj₂ (inj₂ (inj₁ p))) (inj₂ (inj₂ (inj₁ q))) = Graph.<-inside B₃ p q
  E .Graph.<-inside (inj₂ (inj₂ (inj₁ p))) (inj₂ (inj₂ (inj₂ _))) = inj₁ tt
  E .Graph.<-inside (inj₂ (inj₂ (inj₂ _))) (inj₂ (inj₂ _)) = inj₂ ⟪ ≈-refl ⟫
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

    c₁ : X ⇒ Y₁
    c₁ = collapse B₁ ∘ inputs₁

    c₂ : X ⇒ Y₂
    c₂ = collapse B₂ ∘ inputs₂

    P₁ : (t : Path⁺ B₃ ⊎ Root) → Y₁ ⇒ vertex-object E (tgt t)
    P₁ (inj₁ q) = into⁺ B₃ q ∘ from-root₁
    P₁ (inj₂ _) = up₁

    K₁ : (t : Path⁺ B₃ ⊎ Root) → X ⇒ vertex-object E (tgt t)
    K₁ (inj₁ q) = into⁺ B₃ q ∘ from-inputs₃
    K₁ (inj₂ _) = out-root

    module S₁ = HidePremise B₁ (vertex-object E) (inj₁ input) b1 tgt inputs₁ P₁ K₁

    prem₁ : Relation (vertex-object B₁) → S₁.St
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
    start₁ .S₁.off-start (inj₁ q) p = ≈-refl {f = εₘ}
    start₁ .S₁.off-start (inj₂ _) p = ≈-refl {f = εₘ}
    start₁ .S₁.sink q = ≈-refl {f = εₘ}

    done₁ = hidden₁.done start₁
    κ₁ = ≈-trans (≡-to-≈ hidden₁.κ) (hide-paths⁺ B₁)

    module OutOfHidden = NoEdgeOutOfHidden (vertex-object E) b1 (inj₁ {A = Input}) b2 (λ _ q → into⁺ B₂ q ∘ inputs₂)

    fixed₀ : OutOfHidden.Fixed (gr E)
    fixed₀ .OutOfHidden.edge _ q = ≈-refl
    fixed₀ .OutOfHidden.no-edge w q = ≈-refl {f = εₘ}

    fixed₁ : OutOfHidden.Fixed hidden₁.G
    fixed₁ = OutOfHidden.fixed-hide-all inj₁ ps₁ (OutOfHidden.fixed-hide (inj₂ root) fixed₀)

    cols₂ : Path⁺ B₂ ⊎ (Path⁺ B₃ ⊎ Root) → V E
    cols₂ (inj₁ q) = b2 q
    cols₂ (inj₂ t) = tgt t

    Bh₂ : (s : Path⁺ B₂) (t : Path⁺ B₂ ⊎ (Path⁺ B₃ ⊎ Root)) → object⁺ B₂ s ⇒ vertex-object E (cols₂ t)
    Bh₂ s (inj₁ q)        = inside⁺ B₂ s q
    Bh₂ s (inj₂ (inj₁ q)) = e₂₃ s q
    Bh₂ s (inj₂ (inj₂ _)) = up-root⁺ B₂ up₂ s

    module IntoHidden₂ = NoEdgeIntoHidden (vertex-object E) b1 b2 cols₂ Bh₂

    fixed₂ : IntoHidden₂.Fixed hidden₁.G
    fixed₂ = IntoHidden₂.fixed-hide-all inj₁ ps₁ (IntoHidden₂.fixed-hide (inj₂ root) k₀)
      where
      k₀ : IntoHidden₂.Fixed (gr E)
      k₀ .IntoHidden₂.edge s (inj₁ q)        = ≈-refl
      k₀ .IntoHidden₂.edge s (inj₂ (inj₁ q)) = ≈-refl {f = e₂₃ s q}
      k₀ .IntoHidden₂.edge s (inj₂ (inj₂ _)) = ≈-refl {f = up-root⁺ B₂ up₂ s}
      k₀ .IntoHidden₂.no-edge s w = ≈-refl {f = εₘ}

    Φ₃₁ : X ⇒ X₃
    Φ₃₁ = from-inputs₃ +ₘ (from-root₁ ∘ c₁)

    P₂ : (t : Path⁺ B₃ ⊎ Root) → Y₂ ⇒ vertex-object E (tgt t)
    P₂ (inj₁ q) = into⁺ B₃ q ∘ from-root₂
    P₂ (inj₂ _) = up₂

    K₂ : (t : Path⁺ B₃ ⊎ Root) → X ⇒ vertex-object E (tgt t)
    K₂ (inj₁ q) = into⁺ B₃ q ∘ Φ₃₁
    K₂ (inj₂ _) = out-root +ₘ (up₁ ∘ c₁)

    module S₂ = HidePremise B₂ (vertex-object E) (inj₁ input) b2 tgt inputs₂ P₂ K₂

    prem₂ : Relation (vertex-object B₂) → S₂.St
    prem₂ G .S₂.into q = G (inj₁ input) (inj₂ q)
    prem₂ G .S₂.inside p q = G (inj₂ p) (inj₂ q)

    module hidden₂ = S₂.Hidden hidden₁.G prem₂ (λ G w → ≡-refl)

    start₂ : S₂.Start hidden₁.G hidden₂.H⁰
    start₂ .S₂.into-start q = fixed₁ .OutOfHidden.edge input q
    start₂ .S₂.inside-start p q = fixed₂ .IntoHidden₂.edge p (inj₁ q)
    start₂ .S₂.tgt-start (inj₁ q) =
      ≈-trans (done₁ .S₁.tgt-ok (inj₁ q))
              (factor (into⁺ B₃ q) from-inputs₃ from-root₁ {h = hidden₁.H .S₁.into (inj₂ root)} {c = collapse B₁} inputs₁ κ₁)
    start₂ .S₂.tgt-start (inj₂ _) =
      ≈-trans {g = out-root +ₘ (up₁ ∘ (hidden₁.H .S₁.into (inj₂ root) ∘ inputs₁))}
              (done₁ .S₁.tgt-ok (inj₂ root))
              (+ₘ-cong ≈-refl (∘-cong₂ {f = up₁} (∘-cong₁ {g = inputs₁} κ₁)))
    start₂ .S₂.up-start (inj₁ q) = fixed₂ .IntoHidden₂.edge (inj₂ root) (inj₂ (inj₁ q))
    start₂ .S₂.up-start (inj₂ _) = fixed₂ .IntoHidden₂.edge (inj₂ root) (inj₂ (inj₂ root))
    start₂ .S₂.off-start (inj₁ q) p = fixed₂ .IntoHidden₂.edge (inj₁ p) (inj₂ (inj₁ q))
    start₂ .S₂.off-start (inj₂ _) p = fixed₂ .IntoHidden₂.edge (inj₁ p) (inj₂ (inj₂ root))
    start₂ .S₂.sink q = ≈-refl {f = εₘ}

    done₂ = hidden₂.done start₂
    κ₂ = ≈-trans (≡-to-≈ hidden₂.κ) (hide-paths⁺ B₂)

    hid₁₂ : Path⁺ B₁ ⊎ Path⁺ B₂ → V E
    hid₁₂ (inj₁ q) = b1 q
    hid₁₂ (inj₂ q) = b2 q

    Bh₃ : (s : Path⁺ B₃) (t : Path⁺ B₃ ⊎ Root) → object⁺ B₃ s ⇒ vertex-object E (tgt t)
    Bh₃ s (inj₁ q) = inside⁺ B₃ s q
    Bh₃ s (inj₂ _) = up-root⁺ B₃ up₃ s

    module IntoHidden₃ = NoEdgeIntoHidden (vertex-object E) hid₁₂ b3 tgt Bh₃

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
      k₀ .IntoHidden₃.no-edge s (inj₁ w) = ≈-refl {f = εₘ}
      k₀ .IntoHidden₃.no-edge s (inj₂ w) = ≈-refl {f = εₘ}

  Φ₃ : X ⇒ X₃
  Φ₃ = inputs₃ ∘ ⟨ ⟨ I , c₁ ⟩ , c₂ ⟩

  private
    Φ₃' : X ⇒ X₃
    Φ₃' = Φ₃₁ +ₘ (from-root₂ ∘ c₂)

    Φ₃-split : Φ₃' ≈ Φ₃
    Φ₃-split =
      ≈-sym (≈-trans (∘-pair inputs₃ ⟨ I , c₁ ⟩ c₂)
                     (+ₘ-cong (≈-trans (∘-pair (inputs₃ ∘ inb₁ {X ⊕ᵥ Y₁} {Y₂}) I c₁)
                                         (+ₘ-cong (id-right {f = from-inputs₃}) (≈-refl {f = from-root₁ ∘ c₁})))
                                (≈-refl {f = from-root₂ ∘ c₂})))

    module S₃ = HidePremise B₃ (vertex-object E) (inj₁ input) b3 (λ (_ : Root) → er) Φ₃' (λ _ → up₃)
                            (λ _ → (out-root +ₘ (up₁ ∘ c₁)) +ₘ (up₂ ∘ c₂))

    prem₃ : Relation (vertex-object B₃) → S₃.St
    prem₃ G .S₃.into q = G (inj₁ input) (inj₂ q)
    prem₃ G .S₃.inside p q = G (inj₂ p) (inj₂ q)

    module hidden₃ = S₃.Hidden hidden₂.G prem₃ (λ G w → ≡-refl)

    start₃ : S₃.Start hidden₂.G hidden₃.H⁰
    start₃ .S₃.into-start q =
      ≈-trans {g = (into⁺ B₃ q ∘ Φ₃₁) +ₘ ((into⁺ B₃ q ∘ from-root₂) ∘ (hidden₂.H .S₂.into (inj₂ root) ∘ inputs₂))}
              (done₂ .S₂.tgt-ok (inj₁ q))
              (factor (into⁺ B₃ q) Φ₃₁ from-root₂ {h = hidden₂.H .S₂.into (inj₂ root)} {c = collapse B₂} inputs₂ κ₂)
    start₃ .S₃.inside-start p q = fixed₃ .IntoHidden₃.edge p (inj₁ q)
    start₃ .S₃.tgt-start _ =
      ≈-trans {g = (out-root +ₘ (up₁ ∘ c₁)) +ₘ (up₂ ∘ (hidden₂.H .S₂.into (inj₂ root) ∘ inputs₂))}
              (done₂ .S₂.tgt-ok (inj₂ root)) (+ₘ-cong ≈-refl (∘-cong₂ {f = up₂} (∘-cong₁ {g = inputs₂} κ₂)))
    start₃ .S₃.up-start _ = fixed₃ .IntoHidden₃.edge (inj₂ root) (inj₂ root)
    start₃ .S₃.off-start _ p = fixed₃ .IntoHidden₃.edge (inj₁ p) (inj₂ root)
    start₃ .S₃.sink q = ≈-refl {f = εₘ}

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
      ≡-trans (≡-cong (λ l → hide-all (vertex-object E) (gr E) l (inj₁ input) er) lst)
              (≡-trans (≡-cong (λ G → G (inj₁ input) er)
                               (foldl-++ (hide (vertex-object E)) (gr E) l₁ (l₂ ++ l₃)))
                       (≡-cong (λ G → G (inj₁ input) er)
                               (foldl-++ (hide (vertex-object E)) hidden₁.G l₂ l₃)))

  agree : collapse E ≈ (((out-root +ₘ (up₁ ∘ c₁)) +ₘ (up₂ ∘ c₂)) +ₘ (up₃ ∘ (collapse B₃ ∘ Φ₃)))
  agree =
    ≈-trans (≡-to-≈ plumb)
            (≈-trans {g = ((out-root +ₘ (up₁ ∘ c₁)) +ₘ (up₂ ∘ c₂)) +ₘ (up₃ ∘ (hidden₃.H .S₃.into (inj₂ root) ∘ Φ₃'))}
                     (hidden₃.done start₃ .S₃.tgt-ok root)
                     (+ₘ-cong ≈-refl (∘-cong₂ {f = up₃} (∘-cong (≈-trans (≡-to-≈ hidden₃.κ) (hide-paths⁺ B₃)) Φ₃-split))))
