{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.Bool using (Bool; true; not; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; toℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; map; foldl; filterᵇ; upTo; applyUpTo)
open import Data.Bool.ListAction using (any)
open import Data.List.Properties using (++-identityʳ; map-++; map-∘; foldl-++)
open import Data.List.Relation.Unary.All using (All; []; _∷_; universal) renaming (map to All-map)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_) renaming (map to AllPairs-map)
import Data.List.Relation.Unary.All.Properties as AllP
import Data.List.Relation.Unary.AllPairs.Properties as AllPairsP
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Vec using (toList; tabulate)
import Data.List.Relation.Binary.Permutation.Propositional as ↭
open ↭ using (_↭_; ↭-refl; ↭-trans; ↭-reflexive)
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermutationP
open PermutationP using (map⁺; ++⁺; All-resp-↭)
open import Data.Unit using (tt) renaming (⊤ to Unit)

open import Relation.Binary
  using (DecidableEquality; StrictTotalOrder; IsStrictTotalOrder; IsStrictPartialOrder;
         Trichotomous; Tri; tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst₂; isEquivalence)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; cong to ≡-cong; cong₂ to ≡-cong₂)
open import Relation.Nullary.Decidable using (Dec; yes; no; ⌊_⌋)
import Data.Sum.Properties as SumP
open import Level using (0ℓ)
open import prop using (Prf; ⟪_⟫; _∧_; _,_; proj₁; proj₂; ∃ₛ)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import basics using (IsStrictOrder)
open import list using (filterᵇ-split)
import matrix
import Data.Nat.Show as ℕ-Show
open import Data.String using (String) renaming (_++_ to _++ₛ_)
import semimodule

-- A dependence graph over a derivation: the derivation fixes the vertices with their widths and
-- first-order markings, and the graph carries the dependence relation between each pair. The root
-- has no outgoing relation, so it is a sink by construction.
module interaction.graph {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (let module Semiring = CommutativeSemiring S) (+-idem : ∀ x → (x Semiring.+ x) Semiring.≈ x) where

module SemiMod = semimodule S

open SemiMod using (Semimodule)
open import categories using (Category)
open Category SemiMod.cat
  using (_⇒_; _∘_; _≈_; ∘-cong; ∘-cong₁; ∘-cong₂; assoc; id-left; id-right; ≈-refl; ≈-sym; ≈-trans; ≡-to-≈)
open import cmon-enriched using (CMonEnriched; Biproduct)
open import matrix-embedding S using (𝔽; 𝔽F-full; mat; mat-cong; mat-comp; mat-+)
private
  module CM = CMonEnriched SemiMod.cmon-enriched
  module M = matrix.Mat S

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

input-≟ : DecidableEquality Input
input-≟ input input = yes ≡-refl

-- A node carries the width and first-order marking of its output.
data Derivation : Set where
  node : ℕ → Bool → List Derivation → Derivation

out-width : Derivation → ℕ
out-width (node n _ _) = n

out-fo : Derivation → Bool
out-fo (node _ b _) = b

-- Positions of a premise in a premise list, in the style of list membership but with the premise
-- as an index rather than an equality.
data _∋_ : List Derivation → Derivation → Set where
  here  : ∀ {s ss} → (s ∷ ss) ∋ s
  there : ∀ {s s' ss} → ss ∋ s → (s' ∷ ss) ∋ s

-- A vertex of a derivation: the path to the subderivation whose conclusion it denotes, one premise
-- position per level. The empty path denotes the derivation's own conclusion.
data Path : Derivation → Set where
  ε    : ∀ {s} → Path s
  into : ∀ {n b ss s} → ss ∋ s → Path s → Path (node n b ss)

-- The subderivation whose conclusion a path reaches.
deriv-at : (s : Derivation) → Path s → Derivation
deriv-at s ε = s
deriv-at (node _ _ _) (into {s = s} i p) = deriv-at s p

width-at : (s : Derivation) → Path s → ℕ
width-at s q = out-width (deriv-at s q)

fo-at : (s : Derivation) → Path s → Bool
fo-at s q = out-fo (deriv-at s q)

object : (s : Derivation) → Path s → Semimodule
object s q = 𝔽 (width-at s q)

private
  into-here-injective : ∀ {n b s ss} {p q : Path s} →
                        into {n} {b} {s ∷ ss} here p ≡ into here q → p ≡ q
  into-here-injective ≡-refl = ≡-refl

  into-there-injective : ∀ {n b s' ss s₁ s₂} {i₁ : ss ∋ s₁} {i₂ : ss ∋ s₂}
                         {p : Path s₁} {q : Path s₂} →
                         into {n} {b} {s' ∷ ss} (there i₁) p ≡ into (there i₂) q →
                         into {n} {b} {ss} i₁ p ≡ into i₂ q
  into-there-injective ≡-refl = ≡-refl

mutual
  _≟_ : ∀ {s} → DecidableEquality (Path s)
  ε        ≟ ε        = yes ≡-refl
  ε        ≟ into _ _ = no (λ ())
  into _ _ ≟ ε        = no (λ ())
  into i p ≟ into j q = ≟-into i p j q

  ≟-into : ∀ {n b ss s s'} (i : ss ∋ s) (p : Path s) (j : ss ∋ s') (q : Path s') →
           Dec (into {n} {b} i p ≡ into j q)
  ≟-into here      p here      q with p ≟ q
  ... | yes ≡-refl = yes ≡-refl
  ... | no  ne     = no (λ e → ne (into-here-injective e))
  ≟-into here      _ (there _) _ = no (λ ())
  ≟-into (there _) _ here      _ = no (λ ())
  ≟-into (there i) p (there j) q with ≟-into i p j q
  ... | yes ≡-refl = yes ≡-refl
  ... | no  ne     = no (λ e → ne (into-there-injective e))

-- A path of the tail of a premise list, reused at the whole list: positions move one premise
-- along, and the empty path is fixed (it never occurs in the lists this is mapped over).
weaken : ∀ {n b s ss} → Path (node n b ss) → Path (node n b (s ∷ ss))
weaken ε          = ε
weaken (into i p) = into (there i) p

private
  weaken-injective : ∀ {n b s ss} {p q : Path (node n b ss)} →
                     weaken {n} {b} {s} p ≡ weaken q → p ≡ q
  weaken-injective {p = ε}        {q = ε}        _ = ≡-refl
  weaken-injective {p = ε}        {q = into _ _} ()
  weaken-injective {p = into _ _} {q = ε}        ()
  weaken-injective {p = into _ _} {q = into _ _} e with into-there-injective e
  ... | ≡-refl = ≡-refl

  weaken-no-ε : ∀ {n b s ss} {p : Path (node n b ss)} → p ≢ ε → weaken {n} {b} {s} p ≢ ε
  weaken-no-ε {p = ε}        ne _ = ne ≡-refl
  weaken-no-ε {p = into _ _} _  ()

-- The vertices of a derivation in evaluation order: each premise's interior, then its conclusion,
-- then the premises after it. The derivation's own conclusion is not listed.
mutual
  vertices : (s : Derivation) → List (Path s)
  vertices (node n b ss) = vertices-of n b ss

  vertices-of : (n : ℕ) (b : Bool) (ss : List Derivation) → List (Path (node n b ss))
  vertices-of n b []       = []
  vertices-of n b (s ∷ ss) =
    map (into here) (vertices s ++ (ε ∷ [])) ++ map weaken (vertices-of n b ss)

mutual
  vertices-no-ε : (s : Derivation) → All (_≢ ε) (vertices s)
  vertices-no-ε (node n b ss) = vertices-of-no-ε n b ss

  vertices-of-no-ε : ∀ n b ss → All (_≢ ε) (vertices-of n b ss)
  vertices-of-no-ε n b []       = []
  vertices-of-no-ε n b (s ∷ ss) =
    AllP.++⁺ (AllP.map⁺ (universal (λ _ ()) (vertices s ++ (ε ∷ []))))
             (AllP.map⁺ (All-map weaken-no-ε (vertices-of-no-ε n b ss)))

private
  into-here-≢-weaken : ∀ {n b s ss} (x : Path s) {y : Path (node n b ss)} →
                       y ≢ ε → into {n} {b} {s ∷ ss} here x ≢ weaken y
  into-here-≢-weaken x {y = ε}        ne _ = ne ≡-refl
  into-here-≢-weaken x {y = into _ _} _  ()

mutual
  distinct : (s : Derivation) → AllPairs _≢_ (vertices s)
  distinct (node n b ss) = distinct-of n b ss

  distinct-of : ∀ n b ss → AllPairs _≢_ (vertices-of n b ss)
  distinct-of n b []       = []
  distinct-of n b (s ∷ ss) =
    AllPairsP.++⁺
      (AllPairsP.map⁺ (AllPairs-map (λ h e → h (into-here-injective e)) (distinct-one s)))
      (AllPairsP.map⁺ (AllPairs-map (λ h e → h (weaken-injective e)) (distinct-of n b ss)))
      (AllP.map⁺ (universal (λ x → AllP.map⁺ (All-map (into-here-≢-weaken x)
                                                      (vertices-of-no-ε n b ss)))
                            (vertices s ++ (ε ∷ []))))

  distinct-one : (s : Derivation) → AllPairs _≢_ (vertices s ++ (ε ∷ []))
  distinct-one s =
    AllPairsP.++⁺ (distinct s) ([] ∷ [])
                  (All-map (λ h → h ∷ []) (vertices-no-ε s))


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

-- The evaluation order: a premise's interior before its conclusion, every premise before those
-- after it, and the derivation's own conclusion above everything. The derivation is explicit,
-- since it cannot be recovered from a path.
mutual
  lt : (s : Derivation) → Path s → Path s → Set
  lt _              ε          _          = ⊥
  lt _              (into _ _) ε          = Unit
  lt (node _ _ ss)  (into i p) (into j q) = lt∋ ss i p j q

  lt∋ : (ss : List Derivation) {s s' : Derivation} → ss ∋ s → Path s → ss ∋ s' → Path s' → Set
  lt∋ (s ∷ _)  here      p here      q = lt s p q
  lt∋ _        here      _ (there _) _ = Unit
  lt∋ _        (there _) _ here      _ = ⊥
  lt∋ (_ ∷ ss) (there i) p (there j) q = lt∋ ss i p j q

private
  mutual
    lt-trans : ∀ s (p q r : Path s) → lt s p q → lt s q r → lt s p r
    lt-trans _             ε          _          _          () _
    lt-trans _             (into _ _) ε          _          _  ()
    lt-trans _             (into _ _) (into _ _) ε          _  _ = tt
    lt-trans (node _ _ ss) (into i p) (into j q) (into k r) a  b = lt∋-trans ss i p j q k r a b

    lt∋-trans : ∀ ss {s₁ s₂ s₃} (i : ss ∋ s₁) (p : Path s₁) (j : ss ∋ s₂) (q : Path s₂)
                (k : ss ∋ s₃) (r : Path s₃) →
                lt∋ ss i p j q → lt∋ ss j q k r → lt∋ ss i p k r
    lt∋-trans (s ∷ _)  here      p here      q here      r a  b = lt-trans s p q r a b
    lt∋-trans _        here      _ here      _ (there _) _  _  _ = tt
    lt∋-trans _        here      _ (there _) _ (there _) _  _  _ = tt
    lt∋-trans _        here      _ (there _) _ here      _  _  ()
    lt∋-trans _        (there _) _ here      _ _         _  ()
    lt∋-trans (_ ∷ ss) (there i) p (there j) q (there k) r a  b = lt∋-trans ss i p j q k r a b
    lt∋-trans _        (there _) _ (there _) _ here      _  _  ()

  mutual
    lt-asym : ∀ s (p q : Path s) → lt s p q → lt s q p → ⊥
    lt-asym _             ε          _          () _
    lt-asym _             (into _ _) ε          _  ()
    lt-asym (node _ _ ss) (into i p) (into j q) a  b = lt∋-asym ss i p j q a b

    lt∋-asym : ∀ ss {s₁ s₂} (i : ss ∋ s₁) (p : Path s₁) (j : ss ∋ s₂) (q : Path s₂) →
               lt∋ ss i p j q → lt∋ ss j q i p → ⊥
    lt∋-asym (s ∷ _)  here      p here      q a  b = lt-asym s p q a b
    lt∋-asym _        here      _ (there _) _ _  ()
    lt∋-asym _        (there _) _ here      _ () _
    lt∋-asym (_ ∷ ss) (there i) p (there j) q a  b = lt∋-asym ss i p j q a b

lt-order : (s : Derivation) → IsStrictOrder (lt s)
lt-order s .IsStrictOrder.trans = lt-trans s
lt-order s .IsStrictOrder.asym  = lt-asym s

mutual
  lt-compare : (s : Derivation) → Trichotomous _≡_ (lt s)
  lt-compare _             ε          ε          = tri≈ (λ ()) ≡-refl (λ ())
  lt-compare _             ε          (into _ _) = tri> (λ ()) (λ ()) tt
  lt-compare _             (into _ _) ε          = tri< tt (λ ()) (λ ())
  lt-compare (node _ _ ss) (into i p) (into j q) = lt∋-compare ss i p j q

  lt∋-compare : ∀ {n b} ss {s₁ s₂} (i : ss ∋ s₁) (p : Path s₁) (j : ss ∋ s₂) (q : Path s₂) →
                Tri (lt∋ ss i p j q) (into {n} {b} i p ≡ into j q) (lt∋ ss j q i p)
  lt∋-compare (s ∷ _) here p here q with lt-compare s p q
  ... | tri< a ¬b ¬c = tri< a (λ e → ¬b (into-here-injective e)) ¬c
  ... | tri≈ ¬a e ¬c = tri≈ ¬a (≡-cong (into here) e) ¬c
  ... | tri> ¬a ¬b c = tri> ¬a (λ e → ¬b (into-here-injective e)) c
  lt∋-compare _        here      _ (there _) _ = tri< tt (λ ()) (λ ())
  lt∋-compare _        (there _) _ here      _ = tri> (λ ()) (λ ()) tt
  lt∋-compare (_ ∷ ss) (there i) p (there j) q with lt∋-compare ss i p j q
  ... | tri< a ¬b ¬c = tri< a (λ e → ¬b (into-there-injective e)) ¬c
  ... | tri≈ ¬a e ¬c = tri≈ ¬a (there-≡ e) ¬c
    where
    there-≡ : ∀ {n b s' ss s₁ s₂} {i : ss ∋ s₁} {j : ss ∋ s₂} {p : Path s₁} {q : Path s₂} →
              into {n} {b} {ss} i p ≡ into j q →
              into {n} {b} {s' ∷ ss} (there i) p ≡ into (there j) q
    there-≡ ≡-refl = ≡-refl
  ... | tri> ¬a ¬b c = tri> ¬a (λ e → ¬b (into-there-injective e)) c

private
  lt-strict-total : (s : Derivation) → IsStrictTotalOrder _≡_ (lt s)
  lt-strict-total s .IsStrictTotalOrder.isStrictPartialOrder .IsStrictPartialOrder.isEquivalence =
    isEquivalence
  lt-strict-total s .IsStrictTotalOrder.isStrictPartialOrder .IsStrictPartialOrder.irrefl {x} ≡-refl =
    IsStrictOrder.irrefl (lt-order s) x
  lt-strict-total s .IsStrictTotalOrder.isStrictPartialOrder .IsStrictPartialOrder.trans {p} {q} {r} =
    IsStrictOrder.trans (lt-order s) p q r
  lt-strict-total s .IsStrictTotalOrder.isStrictPartialOrder .IsStrictPartialOrder.<-resp-≈ =
    (λ { ≡-refl l → l }) , (λ { ≡-refl l → l })
  lt-strict-total s .IsStrictTotalOrder.compare = lt-compare s

vertex-order : (s : Derivation) → StrictTotalOrder 0ℓ 0ℓ 0ℓ
vertex-order s .StrictTotalOrder.Carrier = Path s
vertex-order s .StrictTotalOrder._≈_ = _≡_
vertex-order s .StrictTotalOrder._<_ = lt s
vertex-order s .StrictTotalOrder.isStrictTotalOrder = lt-strict-total s

EdgeLabels : {V : Set} → (V → Semimodule) → Set
EdgeLabels {V} vertex-object = (x y : V) → vertex-object x ⇒ vertex-object y

record Graph (m : ℕ) (D : Derivation) : Set₁ where
  field
    from-input : (q : Path D) → 𝔽 m ⇒ object D q
    interior   : EdgeLabels (object D)
    -- Every non-zero relation runs strictly forward in the evaluation order. The inputs are below
    -- everything, and the conclusion above everything, so it is a sink by construction.
    <-interior : ∀ p q → lt D p q ⊎ Prf (interior p q ≈ εₘ)

hide : {V : Set} (vertex-object : V → Semimodule) → EdgeLabels vertex-object → V → EdgeLabels vertex-object
hide vertex-object G r x y = G x y +ₘ (G r y ∘ G x r)

hide-all : {V : Set} (vertex-object : V → Semimodule) → EdgeLabels vertex-object → List V → EdgeLabels vertex-object
hide-all vertex-object = foldl (hide vertex-object)

_≐_ : {V : Set} {vertex-object : V → Semimodule} → EdgeLabels vertex-object → EdgeLabels vertex-object → Prop
_≐_ {V} G G' = ∀ x y → G x y ≈ G' x y

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

hide-cong : {V : Set} (vertex-object : V → Semimodule) {G G' : EdgeLabels vertex-object} (r : V) →
            G ≐ G' → hide vertex-object G r ≐ hide vertex-object G' r
hide-cong vertex-object r e x y = +ₘ-cong (e x y) (∘-cong (e r y) (e x r))

hide-all-cong : {V : Set} (vertex-object : V → Semimodule) {G G' : EdgeLabels vertex-object} (rs : List V) →
                G ≐ G' → hide-all vertex-object G rs ≐ hide-all vertex-object G' rs
hide-all-cong vertex-object []       e = e
hide-all-cong vertex-object (r ∷ rs) e = hide-all-cong vertex-object rs (hide-cong vertex-object r e)

hide-sink : {V : Set} (vertex-object : V → Semimodule) (G : EdgeLabels vertex-object) (r : V) →
            (∀ y → G r y ≈ εₘ) → hide vertex-object G r ≐ G
hide-sink vertex-object G r z x y =
  ≈-trans (+ₘ-cong (≈-refl {f = G x y}) (∘-cong₁ {f₁ = G r y} {f₂ = εₘ} {g = G x r} (z y)))
          (absorb₁ (G x y) (G x r))

hide-all-sink : {V : Set} (vertex-object : V → Semimodule) (G : EdgeLabels vertex-object) (r : V)
                (rs : List V) → (∀ y → G r y ≈ εₘ) → ∀ y → hide-all vertex-object G rs r y ≈ εₘ
hide-all-sink vertex-object G r []        z = z
hide-all-sink vertex-object G r (r' ∷ rs) z =
  hide-all-sink vertex-object (hide vertex-object G r') r rs
    (λ y → ≈-trans (+ₘ-cong (z y)
                            (≈-trans {g = G r' y ∘ εₘ {vertex-object r} {vertex-object r'}}
                                     (∘-cong₂ {f = G r' y} (z r'))
                                     (CM.comp-bilinear-ε₂ {X = vertex-object r} (G r' y))))
                   (+ₘ-lunit εₘ))

hide-all-source : {V : Set} (vertex-object : V → Semimodule) (G : EdgeLabels vertex-object) (r : V)
                  (rs : List V) → (∀ x → G x r ≈ εₘ) → ∀ x → hide-all vertex-object G rs x r ≈ εₘ
hide-all-source vertex-object G r []        z = z
hide-all-source vertex-object G r (r' ∷ rs) z =
  hide-all-source vertex-object (hide vertex-object G r') r rs
    (λ x → ≈-trans (+ₘ-cong (z x)
                            (≈-trans {g = εₘ {vertex-object r'} {vertex-object r} ∘ G x r'}
                                     (∘-cong₁ {f₁ = G r' r} {f₂ = εₘ} {g = G x r'} (z r'))
                                     (CM.comp-bilinear-ε₁ {Z = vertex-object r} (G x r'))))
                   (+ₘ-lunit εₘ))

module Hide (V : Set) (w : V → Semimodule) where
  Gr : Set
  Gr = EdgeLabels w

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

  Tables : V → List V → Set
  Tables x = All (λ u → w x ⇒ w u)

  through : Gr → (x y : V) {us : List V} → Tables x us → w x ⇒ w y
  through G x y []               = G x y
  through G x y {u ∷ _} (T ∷ Ts) = (G u y ∘ T) +ₘ through G x y Ts

  summaries : Gr → (x : V) {us : List V} → Tables x us → (vs : List V) → Tables x vs
  summaries G x Ts []       = []
  summaries G x Ts (v ∷ vs) = Tv ∷ summaries G x (AllP.++⁺ Ts (Tv ∷ [])) vs
    where
    Tv = through G x v Ts

  through-snoc : ∀ {G x y us} (Ts : Tables x us) {v} (T : w x ⇒ w v) →
                 through G x y (AllP.++⁺ Ts (T ∷ [])) ≈ (through G x y Ts +ₘ (G v y ∘ T))
  through-snoc []        T = +ₘ-comm
  through-snoc (T' ∷ Ts) T = ≈-trans (+ₘ-cong ≈-refl (through-snoc Ts T)) (≈-sym +ₘ-assoc)

  private
    through-empty : ∀ {G x y us} (Ts : Tables x us) → through G x y (AllP.++⁺ Ts []) ≈ through G x y Ts
    through-empty []       = ≈-refl
    through-empty (T ∷ Ts) = +ₘ-cong ≈-refl (through-empty Ts)

    through-assoc : ∀ {G x y us vs} (Ts : Tables x us) {v} (T : w x ⇒ w v) (Us : Tables x vs) →
                    through G x y (AllP.++⁺ (AllP.++⁺ Ts (T ∷ [])) Us) ≈
                    through G x y (AllP.++⁺ Ts (T ∷ Us))
    through-assoc []        T Us = ≈-refl
    through-assoc (T' ∷ Ts) T Us = +ₘ-cong ≈-refl (through-assoc Ts T Us)

    Zeros : ∀ {x us} → Tables x us → Set
    Zeros []       = Unit
    Zeros (T ∷ Ts) = Prf (T ≈ εₘ) × Zeros Ts

    zeros-snoc : ∀ {x us v} (Ts : Tables x us) {T : w x ⇒ w v} →
                 Zeros Ts → Prf (T ≈ εₘ) → Zeros (AllP.++⁺ Ts (T ∷ []))
    zeros-snoc []        _         z = z , tt
    zeros-snoc (T' ∷ Ts) (z' , zs) z = z' , zeros-snoc Ts zs z

    through-zeros : ∀ {G : Gr} {x y us} (Ts : Tables x us) → Zeros Ts → through G x y Ts ≈ G x y
    through-zeros []                         _            = ≈-refl
    through-zeros {G} {x} {y} (_∷_ {u} T Ts) (⟪ z ⟫ , zs) =
      ≈-trans (+ₘ-cong (≈-trans {g = G u y ∘ εₘ {w x} {w u}} (∘-cong₂ {f = G u y} z)
                                (CM.comp-bilinear-ε₂ {X = w x} (G u y)))
                       (through-zeros Ts zs))
              (+ₘ-lunit (G x y))

    fold-tables : ∀ rest {us} {G G' : Gr} (Tab : ∀ v → Tables v us) →
                  (∀ x y → G' x y ≈ through G x y (Tab x)) →
                  All (λ v → Zeros (Tab v)) rest →
                  AllPairs (λ v u → Prf (G u v ≈ εₘ)) rest →
                  ∀ x y → foldl h G' rest x y ≈ through G x y (AllP.++⁺ (Tab x) (summaries G x (Tab x) rest))
    fold-tables []         Tab agree _         _             x y =
      ≈-trans (agree x y) (≈-sym (through-empty (Tab x)))
    fold-tables (v ∷ rest) {us} {G} {G'} Tab agree (zv ∷ zs) (ev ∷ pairs) x y =
      ≈-trans (fold-tables rest Tab' agree' (zip zs ev) pairs x y)
              (through-assoc (Tab x) (through G x v (Tab x)) (summaries G x (Tab' x) rest))
      where
      Tab' : ∀ u → Tables u (us ++ v ∷ [])
      Tab' u = AllP.++⁺ (Tab u) (through G u v (Tab u) ∷ [])

      agree' : ∀ x' y' → h G' v x' y' ≈ through G x' y' (Tab' x')
      agree' x' y' =
        ≈-trans (+ₘ-cong (agree x' y')
                         (∘-cong (≈-trans (agree v y') (through-zeros (Tab v) zv)) (agree x' v)))
                (≈-sym (through-snoc (Tab x') (through G x' v (Tab x'))))

      zip : ∀ {vs} → All (λ u → Zeros (Tab u)) vs → All (λ u → Prf (G u v ≈ εₘ)) vs →
            All (λ u → Zeros (Tab' u)) vs
      zip []                  []           = []
      zip (_∷_ {u} z zs') (⟪ e ⟫ ∷ es) =
        zeros-snoc (Tab u) z ⟪ ≈-trans (through-zeros (Tab u) z) e ⟫ ∷ zip zs' es

  fold-through : ∀ {G : Gr} rs → AllPairs (λ v u → Prf (G u v ≈ εₘ)) rs →
                 ∀ x y → foldl h G rs x y ≈ through G x y (summaries G x [] rs)
  fold-through rs pairs = fold-tables rs (λ _ → []) (λ _ _ → ≈-refl) (universal (λ _ → tt) rs) pairs


⊥-elimₚ : ∀ {P : Prop} → ⊥ → P
⊥-elimₚ ()

module Ordered {V : Set} (vertex-object : V → Semimodule) (_<_ : V → V → Set) (o : IsStrictOrder _<_) where

  open IsStrictOrder o using (trans; asym)

  Fwd : EdgeLabels vertex-object → Set
  Fwd G = ∀ x y → (x < y) ⊎ Prf (G x y ≈ εₘ)

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

    both : ∀ (G : EdgeLabels vertex-object) r r' x y → vertex-object x ⇒ vertex-object y
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

-- The vertices of a derivation with each premise's conclusion before its interior: the schedule by
-- which the agreement proofs hide a premise's graph.
mutual
  vertices-result-first : (s : Derivation) → List (Path s)
  vertices-result-first (node n b ss) = vertices-of-result-first n b ss

  vertices-of-result-first : (n : ℕ) (b : Bool) (ss : List Derivation) → List (Path (node n b ss))
  vertices-of-result-first n b []       = []
  vertices-of-result-first n b (s ∷ ss) =
    map (into here) (ε ∷ vertices-result-first s) ++ map weaken (vertices-of-result-first n b ss)

-- The result-first enumeration is a permutation of the canonical one.
mutual
  vertices-perm : (s : Derivation) → vertices s ↭ vertices-result-first s
  vertices-perm (node n b ss) = vertices-of-perm n b ss

  vertices-of-perm : ∀ n b ss → vertices-of n b ss ↭ vertices-of-result-first n b ss
  vertices-of-perm n b []       = ↭-refl
  vertices-of-perm n b (s ∷ ss) =
    ++⁺ (map⁺ (into here) (vertices-one-perm s)) (map⁺ weaken (vertices-of-perm n b ss))

  vertices-one-perm : (s : Derivation) → (vertices s ++ (ε ∷ [])) ↭ (ε ∷ vertices-result-first s)
  vertices-one-perm s =
    ↭-trans (PermutationP.shift ε (vertices s) [])
            (↭.prep ε (↭-trans (↭-reflexive (++-identityʳ (vertices s))) (vertices-perm s)))

vertices-result-first-no-ε : (s : Derivation) → All (_≢ ε) (vertices-result-first s)
vertices-result-first-no-ε s = All-resp-↭ (vertices-perm s) (vertices-no-ε s)

module _ {m : ℕ} {D : Derivation} (B : Graph m D) where
  open Graph B

  V : Set
  V = Input ⊎ Path D

  vertex-width : V → ℕ
  vertex-width = [ (λ _ → m) , width-at D ]

  vertex-object : V → Semimodule
  vertex-object v = 𝔽 (vertex-width v)

  edge-labels : EdgeLabels vertex-object
  edge-labels (inj₁ _) (inj₂ q) = from-input q
  edge-labels (inj₂ p) (inj₂ q) = interior p q
  edge-labels _        (inj₁ _) = εₘ

  collapse : 𝔽 m ⇒ 𝔽 (out-width D)
  collapse =
    hide-all vertex-object edge-labels (map inj₂ (vertices-result-first D)) (inj₁ input) (inj₂ ε)

  paths⁺ : List (Path D)
  paths⁺ = ε ∷ vertices-result-first D

  FO : List (Path D)
  FO = filterᵇ (fo-at D) (vertices D)

  fo-hidden : List (Path D)
  fo-hidden = filterᵇ (λ q → not (fo-at D q)) (vertices D)

  fo-graph : EdgeLabels vertex-object
  fo-graph = hide-all vertex-object edge-labels (map inj₂ fo-hidden)

  _<ᵥ_ : V → V → Set
  _<ᵥ_ = sum-< (λ _ _ → ⊥) (lt D)

  <ᵥ-order : IsStrictOrder _<ᵥ_
  <ᵥ-order = sum-<-order none-order (lt-order D)

  private
    module O = Ordered vertex-object _<ᵥ_ <ᵥ-order

  open O public using (Fwd; hide-all-perm)

  edge-labels-forward : Fwd edge-labels
  edge-labels-forward (inj₁ _) (inj₂ q) = inj₁ tt
  edge-labels-forward (inj₂ p) (inj₂ q) = <-interior p q
  edge-labels-forward (inj₁ _) (inj₁ _) = inj₂ ⟪ ≈-refl ⟫
  edge-labels-forward (inj₂ p) (inj₁ _) = inj₂ ⟪ ≈-refl ⟫

  fo-forward : Fwd fo-graph
  fo-forward = O.fwd-hide-all (map inj₂ fo-hidden) edge-labels-forward

  -- Hiding the remaining vertices of the first-order graph collapses the graph: the two stages
  -- together hide every interior vertex exactly once, and reordering into result-first order is
  -- sound because every nonzero edge of the raw graph runs forward.
  fo-collapse : hide-all vertex-object fo-graph (map inj₂ FO) (inj₁ input) (inj₂ ε) ≈ collapse
  fo-collapse =
    ≈-trans (≡-to-≈ (≡-cong (λ G → G (inj₁ input) (inj₂ ε)) two-stage))
            (hide-all-perm edge-labels-forward (map⁺ inj₂ interior-perm) (inj₁ input) (inj₂ ε))
    where
    two-stage : hide-all vertex-object fo-graph (map inj₂ FO)
                ≡ hide-all vertex-object edge-labels (map inj₂ (fo-hidden ++ FO))
    two-stage =
      ≡-trans (≡-sym (foldl-++ (hide vertex-object) edge-labels (map inj₂ fo-hidden) (map inj₂ FO)))
              (≡-cong (hide-all vertex-object edge-labels) (≡-sym (map-++ inj₂ fo-hidden FO)))

    interior-perm : (fo-hidden ++ FO) ↭ vertices-result-first D
    interior-perm = ↭-trans (filterᵇ-split (fo-at D) (vertices D)) (vertices-perm D)

-- Hiding in evaluation order: with the hidden vertices listed so that every nonzero edge among
-- them runs forward, one traversal materialises for each vertex the relation reaching it from the
-- source through the vertices before it, as a stored table. Each raw edge is read once, where
-- hide-all rewrites the whole relation at each hidden vertex. The tick hook marks each edge
-- tabulation and each vertex summary, firing when the value is demanded; hide-in-evaluation-order
-- below specialises it to the identity.
module Tabulated {m : ℕ} {D : Derivation} (B : Graph m D) (G : EdgeLabels (vertex-object B))
                 (tick : {A : Set} → String → A → A) where

  private
    wd : V B → ℕ
    wd = vertex-width B

  open M public using (Table; nth; to-table; look)

  entry : ∀ (x y : V B) → vertex-object B x ⇒ vertex-object B y → M.Matrix (wd y) (wd x)
  entry x y f = ∃ₛ.fst (𝔽F-full f)

  edge : (u v : V B) → Table
  edge u v = tick "edge" (to-table (entry u v (G u v)))

  sum : List Semiring.Carrier → Semiring.Carrier
  sum []       = Semiring.ε
  sum (x ∷ xs) = x Semiring.+ sum xs

  add : ℕ → ℕ → Table → Table → Table
  add r c T U =
    map (λ i → map (λ j → nth Semiring.ε j (nth [] i T) Semiring.+ nth Semiring.ε j (nth [] i U)) (upTo c))
        (upTo r)

  mul : ℕ → ℕ → ℕ → Table → Table → Table
  mul r m c T U =
    map (λ i → map (λ j → sum (map (λ t → nth Semiring.ε t (nth [] i T) Semiring.· nth Semiring.ε j (nth [] t U))
                                   (upTo m)))
                   (upTo c))
        (upTo r)

  through : (a v : V B) → List (V B × Table) → Table
  through a v []             = edge a v
  through a v ((u , T) ∷ us) = add (wd v) (wd a) (mul (wd v) (wd u) (wd a) (edge u v) T) (through a v us)

  summaries : ℕ → (a : V B) → List (V B × Table) → List (V B) → List (V B × Table)
  summaries k a acc []       = acc
  summaries k a acc (v ∷ vs) =
    summaries (suc k) a (acc ++ (v , tick ("summary " ++ₛ ℕ-Show.show k) (through a v acc)) ∷ []) vs

  hide-in-evaluation-order : List (V B) → (a b : V B) → M.Matrix (wd b) (wd a)
  hide-in-evaluation-order hid a b = look (through a b (summaries 0 a [] hid))

module _ {m : ℕ} {D : Derivation} (B : Graph m D) where

  hide-in-evaluation-order : List (V B) → (a b : V B) →
                             M.Matrix (vertex-width B b) (vertex-width B a)
  hide-in-evaluation-order = Tabulated.hide-in-evaluation-order B (edge-labels B) (λ _ x → x)

-- A graph tabulated once: the relations stored as tables, one row per source vertex with one slot
-- per target, both in evaluation order (the inputs vertex first, the conclusion last). An empty
-- slot is the zero relation, so a read forces only the slot it consults.
record Tabulation : Set where
  field
    widths : List ℕ
    edges  : List (List (Maybe M.Table))

open Tabulation public using (widths; edges)

module _ {m : ℕ} {D : Derivation} (B : Graph m D) where

  all-vertices : List (V B)
  all-vertices = inj₁ input ∷ map inj₂ (vertices D) ++ (inj₂ ε ∷ [])

  vertex-at : ℕ → V B
  vertex-at i = M.nth (inj₂ ε) i (all-vertices)

  private
    _≟ᵥ_ : DecidableEquality (V B)
    _≟ᵥ_ = SumP.≡-dec input-≟ (_≟_ {D})

  index-of : V B → ℕ
  index-of x = scan 0 all-vertices
    where
    scan : ℕ → List (V B) → ℕ
    scan k []       = k
    scan k (y ∷ ys) = if ⌊ x ≟ᵥ y ⌋ then k else scan (suc k) ys

module _ {m : ℕ} {D : Derivation} (B : Graph m D)
         (ε-dec : (x : Semiring.Carrier) → Dec (x ≡ Semiring.ε))
         (tick : {A : Set} → String → A → A) where

  private
    module TB = Tabulated B (edge-labels B) tick

    nonzero : Semiring.Carrier → Bool
    nonzero x = not ⌊ ε-dec x ⌋

    nonzero-table : M.Table → Bool
    nonzero-table = any (any nonzero)

    slot : M.Table → Maybe M.Table
    slot t = if nonzero-table t then just t else nothing

    row : V B → List (Maybe M.Table)
    row x = map (λ y → slot (TB.edge x y)) (all-vertices B)

  tabulation : Tabulation
  tabulation .Tabulation.widths = map (vertex-width B) (all-vertices B)
  tabulation .Tabulation.edges  = map row (all-vertices B)

module _ {m : ℕ} {D : Derivation} (B : Graph m D) where

  table-at : Tabulation → ℕ → ℕ → Maybe M.Table
  table-at T i j = M.nth nothing j (M.nth [] i (T .edges))

  read-edge : Tabulation → (x y : V B) → vertex-object B x ⇒ vertex-object B y
  read-edge T x y with table-at T (index-of B x) (index-of B y)
  ... | just t  = mat (M.look {vertex-width B y} {vertex-width B x} t)
  ... | nothing = εₘ

-- Hiding in evaluation order over a tabulation: as hide-in-evaluation-order, but reading stored
-- tables by vertex number and skipping absent edges. The tick hook marks each vertex summary.
module TabulatedHide (T : Tabulation) (tick : {A : Set} → String → A → A) where

  private
    wd : ℕ → ℕ
    wd i = M.nth 0 i (T .widths)

  edge : ℕ → ℕ → Maybe M.Table
  edge i j = M.nth nothing j (M.nth [] i (T .edges))

  private
    sum : List Semiring.Carrier → Semiring.Carrier
    sum []       = Semiring.ε
    sum (x ∷ xs) = x Semiring.+ sum xs

    add : ℕ → ℕ → M.Table → M.Table → M.Table
    add r c t u =
      map (λ i → map (λ j → M.nth Semiring.ε j (M.nth [] i t) Semiring.+ M.nth Semiring.ε j (M.nth [] i u))
                     (upTo c))
          (upTo r)

    mul : ℕ → ℕ → ℕ → M.Table → M.Table → M.Table
    mul r k c t u =
      map (λ i → map (λ j → sum (map (λ l → M.nth Semiring.ε l (M.nth [] i t) Semiring.·
                                            M.nth Semiring.ε j (M.nth [] l u))
                                     (upTo k)))
                     (upTo c))
          (upTo r)

    add? : ℕ → ℕ → Maybe M.Table → Maybe M.Table → Maybe M.Table
    add? r c nothing  u        = u
    add? r c t        nothing  = t
    add? r c (just t) (just u) = just (add r c t u)

  through : (a v : ℕ) → List (ℕ × M.Table) → Maybe M.Table
  through a v []             = edge a v
  through a v ((u , t) ∷ us) with edge u v
  ... | nothing = through a v us
  ... | just e  = add? (wd v) (wd a) (just (mul (wd v) (wd u) (wd a) e t)) (through a v us)

  summaries : ℕ → (a : ℕ) → List (ℕ × M.Table) → List ℕ → List (ℕ × M.Table)
  summaries k a acc []       = acc
  summaries k a acc (v ∷ vs) with tick ("summary " ++ₛ ℕ-Show.show k) (through a v acc)
  ... | nothing = summaries (suc k) a acc vs
  ... | just t  = summaries (suc k) a (acc ++ (v , t) ∷ []) vs

  hide-tabulated : List ℕ → (a b : ℕ) → Maybe M.Table
  hide-tabulated hid a b = through a b (summaries 0 a [] hid)

  hide-table : List ℕ → (a b : ℕ) → M.Table
  hide-table hid a b with hide-tabulated hid a b
  ... | just t  = t
  ... | nothing = map (λ _ → map (λ _ → Semiring.ε) (upTo (wd a))) (upTo (wd b))


module _ {m : ℕ} {D : Derivation} (B : Graph m D) (G : EdgeLabels (vertex-object B)) where

  private
    module T = Tabulated B G (λ _ x → x)
    module HB = Hide (V B) (vertex-object B)

    wd : V B → ℕ
    wd = vertex-width B

    ≈-of-≡ : ∀ {x y : Semiring.Carrier} → x ≡ y → x Semiring.≈ y
    ≈-of-≡ ≡-refl = Semiring.refl

    nth-tabulate : {C : Set} (d : C) {k : ℕ} (f : Fin k → C) (i : Fin k) →
                   T.nth d (toℕ i) (toList (tabulate f)) ≡ f i
    nth-tabulate d f zero    = ≡-refl
    nth-tabulate d f (suc i) = nth-tabulate d (λ k → f (suc k)) i

    nth-applyUpTo : {C : Set} (d : C) (g : ℕ → C) {r : ℕ} (h : ℕ → ℕ) (i : Fin r) →
                    T.nth d (toℕ i) (map g (applyUpTo h r)) ≡ g (h (toℕ i))
    nth-applyUpTo d g h zero    = ≡-refl
    nth-applyUpTo d g h (suc i) = nth-applyUpTo d g (λ k → h (suc k)) i

    sum-Σ : (g : ℕ → Semiring.Carrier) {r : ℕ} (h : ℕ → ℕ) →
            T.sum (map g (applyUpTo h r)) ≡ M.Σ {r} (λ k → g (h (toℕ k)))
    sum-Σ g {zero}  h = ≡-refl
    sum-Σ g {suc r} h = ≡-cong (λ z → g (h 0) Semiring.+ z) (sum-Σ g {r} (λ k → h (suc k)))

    look-to-table : ∀ {r c} (R : M.Matrix r c) (i : Fin r) (j : Fin c) →
                    T.look (T.to-table R) i j ≡ R i j
    look-to-table R i j =
      ≡-trans (≡-cong (T.nth Semiring.ε (toℕ j)) (nth-tabulate [] _ i)) (nth-tabulate Semiring.ε _ j)

    look-add : ∀ {r c} (t u : T.Table) (i : Fin r) (j : Fin c) →
               T.look (T.add r c t u) i j ≡ (T.look t i j Semiring.+ T.look u i j)
    look-add t u i j =
      ≡-trans (≡-cong (T.nth Semiring.ε (toℕ j)) (nth-applyUpTo [] _ (λ k → k) i))
              (nth-applyUpTo Semiring.ε _ (λ k → k) j)

    look-mul : ∀ {r s c} (t u : T.Table) (i : Fin r) (j : Fin c) →
               T.look (T.mul r s c t u) i j ≡ M._∘_ (T.look {r} {s} t) (T.look {s} {c} u) i j
    look-mul {s = s} t u i j =
      ≡-trans (≡-cong (T.nth Semiring.ε (toℕ j)) (nth-applyUpTo [] _ (λ k → k) i))
              (≡-trans (nth-applyUpTo Semiring.ε _ (λ k → k) j)
                       (sum-Σ (λ k → T.nth Semiring.ε k (T.nth [] (toℕ i) t) Semiring.·
                                     T.nth Semiring.ε (toℕ j) (T.nth [] k u)) {s} (λ k → k)))

    edge-rep : ∀ (u v : V B) → mat (T.look {wd v} {wd u} (T.edge u v)) ≈ G u v
    edge-rep u v =
      ≈-trans (mat-cong (λ i j → ≈-of-≡ (look-to-table (T.entry u v (G u v)) i j)))
              (∃ₛ.snd (𝔽F-full (G u v)))

    data Acc (a : V B) : List (V B × T.Table) → {us : List (V B)} → HB.Tables a us → Set where
      nil  : Acc a [] []
      cons : ∀ {u t acc us} {Ts : HB.Tables a us} {T : vertex-object B a ⇒ vertex-object B u} →
             Prf (mat (T.look {wd u} {wd a} t) ≈ T) → Acc a acc Ts →
             Acc a ((u , t) ∷ acc) (_∷_ {x = u} T Ts)

    through-rep : ∀ {a v acc us} {Ts : HB.Tables a us} → Acc a acc Ts →
                  mat (T.look {wd v} {wd a} (T.through a v acc)) ≈ HB.through G a v Ts
    through-rep {a} {v} nil = edge-rep a v
    through-rep {a} {v} (cons {u} {t} {acc} {T = Tm} ⟪ rep ⟫ K) =
      ≈-trans (mat-cong (λ i j → ≈-of-≡
                 (look-add (T.mul (wd v) (wd u) (wd a) (T.edge u v) t) (T.through a v acc) i j)))
      (≈-trans (mat-+ (T.look (T.mul (wd v) (wd u) (wd a) (T.edge u v) t))
                      (T.look (T.through a v acc)))
      (+ₘ-cong
        (≈-trans (mat-cong (λ i j → ≈-of-≡ (look-mul {wd v} {wd u} {wd a} (T.edge u v) t i j)))
        (≈-trans (mat-comp (T.look {wd v} {wd u} (T.edge u v)) (T.look {wd u} {wd a} t))
                 (∘-cong (edge-rep u v) rep)))
        (through-rep K)))

    acc-nil : ∀ {a acc us} {Ts : HB.Tables a us} → Acc a acc Ts → Acc a acc (AllP.++⁺ Ts [])
    acc-nil nil        = nil
    acc-nil (cons r K) = cons r (acc-nil K)

    acc-snoc : ∀ {a acc us} {Ts : HB.Tables a us} {v t} {T : vertex-object B a ⇒ vertex-object B v} →
               Acc a acc Ts → Prf (mat (T.look {wd v} {wd a} t) ≈ T) →
               Acc a (acc ++ (v , t) ∷ []) (AllP.++⁺ Ts (_∷_ {x = v} T []))
    acc-snoc nil        r = cons r nil
    acc-snoc (cons s K) r = cons s (acc-snoc K r)

    acc-shift : ∀ {a acc us vs} {Ts : HB.Tables a us} {v} {T : vertex-object B a ⇒ vertex-object B v}
                {Us : HB.Tables a vs} →
                Acc a acc (AllP.++⁺ (AllP.++⁺ Ts (_∷_ {x = v} T [])) Us) →
                Acc a acc (AllP.++⁺ Ts (_∷_ {x = v} T Us))
    acc-shift {Ts = []}       K          = K
    acc-shift {Ts = T' ∷ Ts'} (cons s K) = cons s (acc-shift {Ts = Ts'} K)

    summaries-rep : ∀ {a acc us} {Ts : HB.Tables a us} → Acc a acc Ts → ∀ k vs →
                    Acc a (T.summaries k a acc vs) (AllP.++⁺ Ts (HB.summaries G a Ts vs))
    summaries-rep K k []       = acc-nil K
    summaries-rep {Ts = Ts} K k (v ∷ vs) =
      acc-shift {Ts = Ts} (summaries-rep (acc-snoc K ⟪ through-rep K ⟫) (suc k) vs)

  tabulated-hide-all : ∀ hid (a b : V B) → AllPairs (λ v u → Prf (G u v ≈ εₘ)) hid →
                       mat (Tabulated.hide-in-evaluation-order B G (λ _ x → x) hid a b) ≈
                       hide-all (vertex-object B) G hid a b
  tabulated-hide-all hid a b pairs =
    ≈-trans (through-rep (summaries-rep nil 0 hid)) (≈-sym (HB.fold-through hid pairs a b))

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
module _ {m : ℕ} {D : Derivation} (B : Graph m D) where

  root-row : ∀ y → edge-labels B (inj₂ ε) y ≈ εₘ
  root-row (inj₁ _) = ≈-refl {f = εₘ}
  root-row (inj₂ q) with Graph.<-interior B ε q
  ... | inj₁ ()
  ... | inj₂ ⟪ e ⟫ = e

  hide-paths⁺ : hide-all (vertex-object B) (edge-labels B) (map inj₂ (paths⁺ B)) (inj₁ input) (inj₂ ε)
                ≈ collapse B
  hide-paths⁺ =
    hide-all-cong (vertex-object B) (map inj₂ (vertices-result-first D))
                  (hide-sink (vertex-object B) (edge-labels B) (inj₂ ε) root-row)
                  (inj₁ input) (inj₂ ε)

module HidePremise
  {mB : ℕ} {DB : Derivation} (B : Graph mB DB)
  {V : Set} (object' : V → Semimodule)
  (inp : V)
  (blk : Path DB → V)
  {T : Set} (tgt : T → V)
  {M' : Semimodule} (Φ : object' inp ⇒ M')
  (P : (t : T) → object' (blk ε) ⇒ object' (tgt t))
  (K : (t : T) → object' inp ⇒ object' (tgt t))
  where

  record St : Set where
    field
      from-input   : (q : Path DB) → M' ⇒ object' (blk q)
      interior : (p q : Path DB) → object' (blk p) ⇒ object' (blk q)

  open St public

  step : St → Path DB → St
  step H w .from-input q = H .from-input q +ₘ (H .interior w q ∘ H .from-input w)
  step H w .interior p q = H .interior p q +ₘ (H .interior w q ∘ H .interior p w)

  steps : St → List (Path DB) → St
  steps = foldl step

  folds : ∀ {A V' : Set} (prem : A → St) (ι : Path DB → V') (h' : A → V' → A) →
          (∀ G w → step (prem G) w ≡ prem (h' G (ι w))) →
          (ws : List (Path DB)) (G : A) → steps (prem G) ws ≡ prem (foldl h' G (map ι ws))
  folds prem ι h' ok []       G = ≡-refl
  folds prem ι h' ok (w ∷ ws) G =
    ≡-trans (≡-cong (λ H → steps H ws) (ok G w)) (folds prem ι h' ok ws (h' G (ι w)))

  private
    Φ-step : ∀ (H : St) (w : Path DB) (q : Path DB) →
             (step H w .from-input q ∘ Φ)
             ≈ ((H .from-input q ∘ Φ) +ₘ (H .interior w q ∘ (H .from-input w ∘ Φ)))
    Φ-step H w q =
      ≈-trans (CM.comp-bilinear₁ (H .from-input q) (H .interior w q ∘ H .from-input w) Φ)
              (+ₘ-cong ≈-refl (assoc (H .interior w q) (H .from-input w) Φ))

  record Agrees (G : EdgeLabels object') (H : St) : Set where
    field
      into-ok   : ∀ q → G inp (blk q) ≈ (H .from-input q ∘ Φ)
      interior-ok : ∀ p q → G (blk p) (blk q) ≈ H .interior p q
      tgt-ok    : ∀ t → G inp (tgt t) ≈ (K t +ₘ (P t ∘ (H .from-input ε ∘ Φ)))
      up-ok     : ∀ t (p : Path DB) → p ≢ ε → G (blk p) (tgt t) ≈ (P t ∘ H .interior p ε)

  open Agrees public

  agrees-hide : ∀ {G H} (w : Path DB) → w ≢ ε → Agrees G H → Agrees (hide object' G (blk w)) (step H w)
  agrees-hide {H = H} w _ s .into-ok q =
    ≈-trans (+ₘ-cong (s .into-ok q) (∘-cong (s .interior-ok w q) (s .into-ok w)))
            (≈-sym (Φ-step H w q))
  agrees-hide w _ s .interior-ok p q =
    +ₘ-cong (s .interior-ok p q) (∘-cong (s .interior-ok w q) (s .interior-ok p w))
  agrees-hide {H = H} w w≢ε s .tgt-ok t =
    ≈-trans (offset-step {Km = K t} {P = P t}
                         {Xm = H .from-input ε ∘ Φ}
                         {Ym = H .interior w ε}
                         {Zm = H .from-input w ∘ Φ}
              (s .tgt-ok t) (s .up-ok t w w≢ε) (s .into-ok w))
            (+ₘ-cong ≈-refl (∘-cong₂ {f = P t} (≈-sym (Φ-step H w ε))))
  agrees-hide {H = H} w w≢ε s .up-ok t p p≢ε =
    root-step {P = P t} {Xm = H .interior p ε}
              {Ym = H .interior w ε} {Zm = H .interior p w}
      (s .up-ok t p p≢ε) (s .up-ok t w w≢ε) (s .interior-ok p w)

  agrees-hide-all : ∀ {G H} (ws : List (Path DB)) → All (_≢ ε) ws → Agrees G H →
                    Agrees (hide-all object' G (map blk ws)) (steps H ws)
  agrees-hide-all []       []         s = s
  agrees-hide-all (w ∷ ws) (w≢ε ∷ hs) s = agrees-hide-all ws hs (agrees-hide w w≢ε s)

  -- The relations a rule contributes, before the graph's root is hidden. Every edge from the graph to
  -- a target leaves the graph's root, which here is a matter of the vertex set rather than a lemma.
  record Start (G : EdgeLabels object') (H : St) : Set where
    field
      into-start   : ∀ q → G inp (blk q) ≈ (H .from-input q ∘ Φ)
      interior-start : ∀ p q → G (blk p) (blk q) ≈ H .interior p q
      tgt-start    : ∀ t → G inp (tgt t) ≈ K t
      up-start     : ∀ t → G (blk ε) (tgt t) ≈ P t
      off-start    : ∀ t (p : Path DB) → p ≢ ε → G (blk p) (tgt t) ≈ εₘ
      sink         : ∀ q → H .interior ε q ≈ εₘ

  open Start public

  agrees-start : ∀ {G H} → Start G H → Agrees (hide object' G (blk ε)) (step H ε)
  agrees-start {H = H} r .into-ok q =
    ≈-trans (+ₘ-cong (r .into-start q)
                     (∘-cong (r .interior-start ε q) (r .into-start ε)))
            (≈-sym (Φ-step H ε q))
  agrees-start r .interior-ok p q =
    +ₘ-cong (r .interior-start p q)
            (∘-cong (r .interior-start ε q) (r .interior-start p ε))
  agrees-start {H = H} r .tgt-ok t =
    ≈-trans (+ₘ-cong (r .tgt-start t)
                     (∘-cong (r .up-start t) (r .into-start ε)))
            (+ₘ-cong ≈-refl (∘-cong₂ {f = P t} (≈-sym unchanged)))
    where
    unchanged : (step H ε .from-input ε ∘ Φ) ≈ (H .from-input ε ∘ Φ)
    unchanged =
      ≈-trans (Φ-step H ε ε)
              (≈-trans (+ₘ-cong ≈-refl (∘-cong₁ {f₁ = H .interior ε ε} {f₂ = εₘ} {g = H .from-input ε ∘ Φ} (r .sink ε)))
                       (absorb₁ (H .from-input ε ∘ Φ) (H .from-input ε ∘ Φ)))
  agrees-start {H = H} r .up-ok t p p≢ε =
    ≈-trans (+ₘ-cong (r .off-start t p p≢ε)
                     (∘-cong (r .up-start t) (r .interior-start p ε)))
    (≈-trans (+ₘ-lunit (P t ∘ H .interior p ε))
             (∘-cong₂ {f = P t} (≈-sym unchanged)))
    where
    unchanged : step H ε .interior p ε ≈ H .interior p ε
    unchanged =
      ≈-trans (+ₘ-cong ≈-refl (∘-cong₁ {f₁ = H .interior ε ε} {f₂ = εₘ} {g = H .interior p ε} (r .sink ε)))
              (absorb₁ (H .interior p ε) (H .interior p ε))

  module Hidden (G₀ : EdgeLabels object') (prem : EdgeLabels (vertex-object B) → St)
                (prem-step : ∀ G w → step (prem G) w ≡ prem (hide (vertex-object B) G (inj₂ w))) where

    H⁰ : St
    H⁰ = prem (edge-labels B)

    G : EdgeLabels object'
    G = hide-all object' (hide object' G₀ (blk ε)) (map blk (vertices-result-first DB))

    H : St
    H = steps (step H⁰ ε) (vertices-result-first DB)

    done : Start G₀ H⁰ → Agrees G H
    done start =
      agrees-hide-all (vertices-result-first DB) (vertices-result-first-no-ε DB) (agrees-start start)

    κ : H .from-input ε ≡ prem (hide-all (vertex-object B) (edge-labels B) (map inj₂ (paths⁺ B))) .from-input ε
    κ = ≡-cong (λ H' → H' .from-input ε) (folds prem inj₂ (hide (vertex-object B)) prem-step (paths⁺ B) (edge-labels B))

module NoEdgeIntoHidden
  {V : Set} (vertex-object : V → Semimodule)
  {W : Set} (hid : W → V)
  {S : Set} (src : S → V)
  {T : Set} (col : T → V)
  (B : (s : S) (t : T) → vertex-object (src s) ⇒ vertex-object (col t))
  where

  record Fixed (G : EdgeLabels vertex-object) : Set where
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

  record Fixed (G : EdgeLabels vertex-object) : Set where
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
  {m n : ℕ} (fo-output : Bool)
  (input-to-output : 𝔽 m ⇒ 𝔽 n)
  where

  E : Graph m (node n fo-output [])
  E .Graph.from-input ε = input-to-output
  E .Graph.from-input (into () _)
  E .Graph.interior ε ε = εₘ
  E .Graph.interior ε (into () _)
  E .Graph.interior (into () _) _
  E .Graph.<-interior ε ε = inj₂ ⟪ ≈-refl ⟫
  E .Graph.<-interior ε (into () _)
  E .Graph.<-interior (into () _) _

  agree : collapse E ≈ input-to-output
  agree = ≈-refl {f = input-to-output}

module Rule₁
  {m : ℕ}
  {mB : ℕ} {DB : Derivation} (B : Graph mB DB)
  {n : ℕ}
  (inputs : 𝔽 m ⇒ 𝔽 mB)
  (fo-output : Bool)
  (input-to-output : 𝔽 m ⇒ 𝔽 n)
  (up-root : 𝔽 (out-width DB) ⇒ 𝔽 n)
  where

  private
    out-edge : (p : Path (node n fo-output (DB ∷ []))) →
               object (node n fo-output (DB ∷ [])) p ⇒ 𝔽 n
    out-edge ε                     = εₘ
    out-edge (into here ε)         = up-root
    out-edge (into here (into i p)) = εₘ
    out-edge (into (there ()) _)

    to-premise : (p : Path (node n fo-output (DB ∷ []))) (q : Path DB) →
                 object (node n fo-output (DB ∷ [])) p ⇒ object DB q
    to-premise ε             q = εₘ
    to-premise (into here p) q = Graph.interior B p q
    to-premise (into (there ()) _) _

  E : Graph m (node n fo-output (DB ∷ []))
  E .Graph.from-input ε            = input-to-output
  E .Graph.from-input (into here q)        = Graph.from-input B q ∘ inputs
  E .Graph.from-input (into (there ()) _)
  E .Graph.interior p ε             = out-edge p
  E .Graph.interior p (into here q) = to-premise p q
  E .Graph.interior p (into (there ()) _)
  E .Graph.<-interior (into here p) (into here q) = Graph.<-interior B p q
  E .Graph.<-interior (into here p) ε             = inj₁ tt
  E .Graph.<-interior ε             ε             = inj₂ ⟪ ≈-refl ⟫
  E .Graph.<-interior ε             (into here q) = inj₂ ⟪ ≈-refl ⟫
  E .Graph.<-interior (into (there ()) _) _
  E .Graph.<-interior _ (into (there ()) _)

  private
    b : Path DB → V E
    b q = inj₂ (into here q)

    er : V E
    er = inj₂ ε

    module S = HidePremise B (vertex-object E) (inj₁ input) b (λ (_ : Unit) → er) inputs (λ _ → up-root) (λ _ → input-to-output)

    prem : EdgeLabels (vertex-object B) → S.St
    prem G .S.from-input q = G (inj₁ input) (inj₂ q)
    prem G .S.interior p q = G (inj₂ p) (inj₂ q)

    module hidden = S.Hidden (edge-labels E) prem (λ G w → ≡-refl)

    start : S.Start (edge-labels E) hidden.H⁰
    start .S.into-start q = ≈-refl
    start .S.interior-start p q = ≈-refl
    start .S.tgt-start _ = ≈-refl {f = input-to-output}
    start .S.up-start _ = ≈-refl {f = up-root}
    start .S.off-start _ ε          ne = ⊥-elimₚ (ne ≡-refl)
    start .S.off-start _ (into i p) _  = ≈-refl {f = εₘ}
    start .S.sink q = root-row B (inj₂ q)

    plumb : collapse E ≡ hidden.G (inj₁ input) er
    plumb = ≡-cong (λ l → hide-all (vertex-object E) (edge-labels E) l (inj₁ input) er)
                   (≡-trans (≡-cong (map inj₂) (++-identityʳ (map (into here) (ε ∷ vertices-result-first DB))))
                            (≡-sym (map-∘ {g = inj₂} {f = into here} (ε ∷ vertices-result-first DB))))

  agree : collapse E ≈ (input-to-output +ₘ (up-root ∘ (collapse B ∘ inputs)))
  agree =
    ≈-trans (≡-to-≈ plumb)
            (≈-trans (hidden.done start .S.tgt-ok tt)
                     (+ₘ-cong ≈-refl (∘-cong₂ {f = up-root} (∘-cong₁ {g = inputs} (≈-trans (≡-to-≈ hidden.κ) (hide-paths⁺ B))))))

module Rule₂
  {m : ℕ}
  {m₁ : ℕ} {D₁ : Derivation} (B₁ : Graph m₁ D₁)
  {m₂ : ℕ} {D₂ : Derivation} (B₂ : Graph m₂ D₂)
  (let n₁ = out-width D₁) (let n₂ = out-width D₂)
  {n : ℕ}
  (inputs₁ : 𝔽 m ⇒ 𝔽 m₁)
  (inputs₂ : (𝔽 m ⊕ᵥ 𝔽 n₁) ⇒ 𝔽 m₂)
  (fo-output : Bool)
  (input-to-output : 𝔽 m ⇒ 𝔽 n)
  (up₁ : 𝔽 n₁ ⇒ 𝔽 n)
  (up₂ : 𝔽 n₂ ⇒ 𝔽 n)
  where

  private
    from-inputs₂ : (𝔽 m) ⇒ (𝔽 m₂)
    from-inputs₂ = inputs₂ ∘ inb₁ {(𝔽 m)} {(𝔽 n₁)}

    from-root₁ : (𝔽 n₁) ⇒ (𝔽 m₂)
    from-root₁ = inputs₂ ∘ inb₂ {(𝔽 m)} {(𝔽 n₁)}

    ps₁ = vertices-result-first D₁
    ps₂ = vertices-result-first D₂

  private
    out-edge : (p : Path (node n fo-output (D₁ ∷ D₂ ∷ []))) →
               object (node n fo-output (D₁ ∷ D₂ ∷ [])) p ⇒ 𝔽 n
    out-edge ε                                  = εₘ
    out-edge (into here ε)                      = up₁
    out-edge (into here (into i p))             = εₘ
    out-edge (into (there here) ε)              = up₂
    out-edge (into (there here) (into i p))     = εₘ
    out-edge (into (there (there ())) _)

    to-first : (p : Path (node n fo-output (D₁ ∷ D₂ ∷ []))) (q : Path D₁) →
               object (node n fo-output (D₁ ∷ D₂ ∷ [])) p ⇒ object D₁ q
    to-first ε                    q = εₘ
    to-first (into here p)        q = Graph.interior B₁ p q
    to-first (into (there here) p) q = εₘ
    to-first (into (there (there ())) _) _

    to-second : (p : Path (node n fo-output (D₁ ∷ D₂ ∷ []))) (q : Path D₂) →
                object (node n fo-output (D₁ ∷ D₂ ∷ [])) p ⇒ object D₂ q
    to-second ε                        q = εₘ
    to-second (into here ε)            q = Graph.from-input B₂ q ∘ from-root₁
    to-second (into here (into i p))   q = εₘ
    to-second (into (there here) p)    q = Graph.interior B₂ p q
    to-second (into (there (there ())) _) _

  E : Graph m (node n fo-output (D₁ ∷ D₂ ∷ []))
  E .Graph.from-input ε                        = input-to-output
  E .Graph.from-input (into here q)            = Graph.from-input B₁ q ∘ inputs₁
  E .Graph.from-input (into (there here) q)    = Graph.from-input B₂ q ∘ from-inputs₂
  E .Graph.from-input (into (there (there ())) _)
  E .Graph.interior p ε                     = out-edge p
  E .Graph.interior p (into here q)         = to-first p q
  E .Graph.interior p (into (there here) q) = to-second p q
  E .Graph.interior p (into (there (there ())) _)
  E .Graph.<-interior (into here p)         (into here q)         = Graph.<-interior B₁ p q
  E .Graph.<-interior (into here p)         (into (there here) q) = inj₁ tt
  E .Graph.<-interior (into (there here) p) (into here q)         = inj₂ ⟪ ≈-refl ⟫
  E .Graph.<-interior (into (there here) p) (into (there here) q) = Graph.<-interior B₂ p q
  E .Graph.<-interior (into here p)         ε = inj₁ tt
  E .Graph.<-interior (into (there here) p) ε = inj₁ tt
  E .Graph.<-interior ε ε             = inj₂ ⟪ ≈-refl ⟫
  E .Graph.<-interior ε (into here q) = inj₂ ⟪ ≈-refl ⟫
  E .Graph.<-interior ε (into (there here) q) = inj₂ ⟪ ≈-refl ⟫
  E .Graph.<-interior (into (there (there ())) _) _
  E .Graph.<-interior _ (into (there (there ())) _)

  private
    b1 : Path D₁ → V E
    b1 q = inj₂ (into here q)

    b2 : Path D₂ → V E
    b2 q = inj₂ (into (there here) q)

    er : V E
    er = inj₂ ε

    tgt₁ : Path D₂ ⊎ Unit → V E
    tgt₁ (inj₁ q) = b2 q
    tgt₁ (inj₂ _) = er

    P₁ : (t : Path D₂ ⊎ Unit) → (𝔽 n₁) ⇒ vertex-object E (tgt₁ t)
    P₁ (inj₁ q) = Graph.from-input B₂ q ∘ from-root₁
    P₁ (inj₂ _) = up₁

    K₁ : (t : Path D₂ ⊎ Unit) → (𝔽 m) ⇒ vertex-object E (tgt₁ t)
    K₁ (inj₁ q) = Graph.from-input B₂ q ∘ from-inputs₂
    K₁ (inj₂ _) = input-to-output

    module S₁ = HidePremise B₁ (vertex-object E) (inj₁ input) b1 tgt₁ inputs₁ P₁ K₁

    prem₁ : EdgeLabels (vertex-object B₁) → S₁.St
    prem₁ G .S₁.from-input q = G (inj₁ input) (inj₂ q)
    prem₁ G .S₁.interior p q = G (inj₂ p) (inj₂ q)

    module hidden₁ = S₁.Hidden (edge-labels E) prem₁ (λ G w → ≡-refl)

    start₁ : S₁.Start (edge-labels E) hidden₁.H⁰
    start₁ .S₁.into-start q = ≈-refl
    start₁ .S₁.interior-start p q = ≈-refl
    start₁ .S₁.tgt-start (inj₁ q) = ≈-refl
    start₁ .S₁.tgt-start (inj₂ _) = ≈-refl {f = input-to-output}
    start₁ .S₁.up-start (inj₁ q) = ≈-refl
    start₁ .S₁.up-start (inj₂ _) = ≈-refl {f = up₁}
    start₁ .S₁.off-start t        ε          ne = ⊥-elimₚ (ne ≡-refl)
    start₁ .S₁.off-start (inj₁ q) (into i p) _  = ≈-refl {f = εₘ}
    start₁ .S₁.off-start (inj₂ _) (into i p) _  = ≈-refl {f = εₘ}
    start₁ .S₁.sink q = root-row B₁ (inj₂ q)

    done₁ = hidden₁.done start₁
    κ₁ = ≈-trans (≡-to-≈ hidden₁.κ) (hide-paths⁺ B₁)

  Φ₂ : (𝔽 m) ⇒ (𝔽 m₂)
  Φ₂ = inputs₂ ∘ ⟨ I , collapse B₁ ∘ inputs₁ ⟩

  private
    Φ₂' : (𝔽 m) ⇒ (𝔽 m₂)
    Φ₂' = from-inputs₂ +ₘ (from-root₁ ∘ (collapse B₁ ∘ inputs₁))

    Φ₂-split : Φ₂' ≈ Φ₂
    Φ₂-split = ≈-sym (≈-trans (∘-pair inputs₂ I (collapse B₁ ∘ inputs₁))
                              (+ₘ-cong (id-right {f = from-inputs₂}) (≈-refl {f = from-root₁ ∘ (collapse B₁ ∘ inputs₁)})))

    module S₂ = HidePremise B₂ (vertex-object E) (inj₁ input) b2 (λ (_ : Unit) → er) Φ₂' (λ _ → up₂)
                            (λ _ → input-to-output +ₘ (up₁ ∘ (collapse B₁ ∘ inputs₁)))

    prem₂ : EdgeLabels (vertex-object B₂) → S₂.St
    prem₂ G .S₂.from-input q = G (inj₁ input) (inj₂ q)
    prem₂ G .S₂.interior p q = G (inj₂ p) (inj₂ q)

    module hidden₂ = S₂.Hidden hidden₁.G prem₂ (λ G w → ≡-refl)

    Bh : (s : Path D₂) (t : Path D₂ ⊎ Unit) → object D₂ s ⇒ vertex-object E (tgt₁ t)
    Bh s          (inj₁ q) = Graph.interior B₂ s q
    Bh ε          (inj₂ _) = up₂
    Bh (into i p) (inj₂ _) = εₘ

    module IntoHidden = NoEdgeIntoHidden (vertex-object E) b1 b2 tgt₁ Bh

    fixed₀ : IntoHidden.Fixed (edge-labels E)
    fixed₀ .IntoHidden.edge s          (inj₁ q) = ≈-refl
    fixed₀ .IntoHidden.edge ε          (inj₂ _) = ≈-refl {f = up₂}
    fixed₀ .IntoHidden.edge (into i p) (inj₂ _) = ≈-refl {f = εₘ}
    fixed₀ .IntoHidden.no-edge s w = ≈-refl {f = εₘ}

    fixed₁ : IntoHidden.Fixed hidden₁.G
    fixed₁ = IntoHidden.fixed-hide-all (λ w → w) ps₁ (IntoHidden.fixed-hide ε fixed₀)

    start₂ : S₂.Start hidden₁.G hidden₂.H⁰
    start₂ .S₂.into-start q =
      ≈-trans (done₁ .S₁.tgt-ok (inj₁ q))
              (factor (Graph.from-input B₂ q) from-inputs₂ from-root₁ {h = hidden₁.H .S₁.from-input ε} {c = collapse B₁} inputs₁ κ₁)
    start₂ .S₂.interior-start p q = fixed₁ .IntoHidden.edge p (inj₁ q)
    start₂ .S₂.tgt-start _ =
      ≈-trans {g = input-to-output +ₘ (up₁ ∘ (hidden₁.H .S₁.from-input ε ∘ inputs₁))}
              (done₁ .S₁.tgt-ok (inj₂ tt)) (+ₘ-cong ≈-refl (∘-cong₂ {f = up₁} (∘-cong₁ {g = inputs₁} κ₁)))
    start₂ .S₂.up-start _ = fixed₁ .IntoHidden.edge ε (inj₂ tt)
    start₂ .S₂.off-start _ ε          ne = ⊥-elimₚ (ne ≡-refl)
    start₂ .S₂.off-start _ (into i p) _  = fixed₁ .IntoHidden.edge (into i p) (inj₂ tt)
    start₂ .S₂.sink q = root-row B₂ (inj₂ q)

    lst : map inj₂ (vertices-result-first (node n fo-output (D₁ ∷ D₂ ∷ [])))
          ≡ (b1 ε ∷ map b1 ps₁) ++ (b2 ε ∷ map b2 ps₂)
    lst =
      ≡-trans (≡-cong (map inj₂)
                (≡-cong (map (into here) (ε ∷ ps₁) ++_)
                        (≡-cong (map weaken) (++-identityʳ (map (into here) (ε ∷ ps₂))))))
      (≡-trans (map-++ inj₂ (map (into here) (ε ∷ ps₁)) (map weaken (map (into here) (ε ∷ ps₂))))
               (≡-cong₂ _++_
                 (≡-sym (map-∘ {g = inj₂} {f = into here} (ε ∷ ps₁)))
                 (≡-trans (≡-cong (map inj₂) (≡-sym (map-∘ {g = weaken} {f = into here} (ε ∷ ps₂))))
                          (≡-sym (map-∘ {g = inj₂} {f = λ q → weaken (into here q)} (ε ∷ ps₂))))))

    plumb : collapse E ≡ hidden₂.G (inj₁ input) er
    plumb =
      ≡-trans (≡-cong (λ l → hide-all (vertex-object E) (edge-labels E) l (inj₁ input) er) lst)
              (≡-cong (λ G → G (inj₁ input) er)
                      (foldl-++ (hide (vertex-object E)) (edge-labels E) (b1 ε ∷ map b1 ps₁) (b2 ε ∷ map b2 ps₂)))

  agree : collapse E ≈ ((input-to-output +ₘ (up₁ ∘ (collapse B₁ ∘ inputs₁))) +ₘ (up₂ ∘ (collapse B₂ ∘ Φ₂)))
  agree =
    ≈-trans (≡-to-≈ plumb)
            (≈-trans {g = (input-to-output +ₘ (up₁ ∘ (collapse B₁ ∘ inputs₁))) +ₘ (up₂ ∘ (hidden₂.H .S₂.from-input ε ∘ Φ₂'))}
                     (hidden₂.done start₂ .S₂.tgt-ok tt)
                     (+ₘ-cong ≈-refl (∘-cong₂ {f = up₂} (∘-cong (≈-trans (≡-to-≈ hidden₂.κ) (hide-paths⁺ B₂)) Φ₂-split))))

module Rule₃
  {m : ℕ}
  {m₁ : ℕ} {D₁ : Derivation} (B₁ : Graph m₁ D₁)
  {m₂ : ℕ} {D₂ : Derivation} (B₂ : Graph m₂ D₂)
  {m₃ : ℕ} {D₃ : Derivation} (B₃ : Graph m₃ D₃)
  (let n₁ = out-width D₁) (let n₂ = out-width D₂) (let n₃ = out-width D₃)
  {n : ℕ}
  (inputs₁ : 𝔽 m ⇒ 𝔽 m₁)
  (inputs₂ : 𝔽 m ⇒ 𝔽 m₂)
  (inputs₃ : ((𝔽 m ⊕ᵥ 𝔽 n₁) ⊕ᵥ 𝔽 n₂) ⇒ 𝔽 m₃)
  (fo-output : Bool)
  (input-to-output : 𝔽 m ⇒ 𝔽 n)
  (up₁ : 𝔽 n₁ ⇒ 𝔽 n)
  (up₂ : 𝔽 n₂ ⇒ 𝔽 n)
  (up₃ : 𝔽 n₃ ⇒ 𝔽 n)
  where

  private
    from-inputs₃ : (𝔽 m) ⇒ (𝔽 m₃)
    from-inputs₃ = (inputs₃ ∘ inb₁ {(𝔽 m) ⊕ᵥ (𝔽 n₁)} {(𝔽 n₂)}) ∘ inb₁ {(𝔽 m)} {(𝔽 n₁)}

    from-root₁ : (𝔽 n₁) ⇒ (𝔽 m₃)
    from-root₁ = (inputs₃ ∘ inb₁ {(𝔽 m) ⊕ᵥ (𝔽 n₁)} {(𝔽 n₂)}) ∘ inb₂ {(𝔽 m)} {(𝔽 n₁)}

    from-root₂ : (𝔽 n₂) ⇒ (𝔽 m₃)
    from-root₂ = inputs₃ ∘ inb₂ {(𝔽 m) ⊕ᵥ (𝔽 n₁)} {(𝔽 n₂)}

    ps₁ = vertices-result-first D₁
    ps₂ = vertices-result-first D₂
    ps₃ = vertices-result-first D₃

    e₁₃ : (p : Path D₁) (q : Path D₃) → object D₁ p ⇒ object D₃ q
    e₁₃ (into _ _) q = εₘ
    e₁₃ ε          q = Graph.from-input B₃ q ∘ from-root₁

    e₂₃ : (p : Path D₂) (q : Path D₃) → object D₂ p ⇒ object D₃ q
    e₂₃ (into _ _) q = εₘ
    e₂₃ ε          q = Graph.from-input B₃ q ∘ from-root₂

  private
    out-edge : (p : Path (node n fo-output (D₁ ∷ D₂ ∷ D₃ ∷ []))) →
               object (node n fo-output (D₁ ∷ D₂ ∷ D₃ ∷ [])) p ⇒ 𝔽 n
    out-edge ε                                          = εₘ
    out-edge (into here ε)                              = up₁
    out-edge (into here (into i p))                     = εₘ
    out-edge (into (there here) ε)                      = up₂
    out-edge (into (there here) (into i p))             = εₘ
    out-edge (into (there (there here)) ε)              = up₃
    out-edge (into (there (there here)) (into i p))     = εₘ
    out-edge (into (there (there (there ()))) _)

    to-first : (p : Path (node n fo-output (D₁ ∷ D₂ ∷ D₃ ∷ []))) (q : Path D₁) →
               object (node n fo-output (D₁ ∷ D₂ ∷ D₃ ∷ [])) p ⇒ object D₁ q
    to-first ε                            q = εₘ
    to-first (into here p)                q = Graph.interior B₁ p q
    to-first (into (there here) p)        q = εₘ
    to-first (into (there (there here)) p) q = εₘ
    to-first (into (there (there (there ()))) _) _

    to-second : (p : Path (node n fo-output (D₁ ∷ D₂ ∷ D₃ ∷ []))) (q : Path D₂) →
                object (node n fo-output (D₁ ∷ D₂ ∷ D₃ ∷ [])) p ⇒ object D₂ q
    to-second ε                            q = εₘ
    to-second (into here p)                q = εₘ
    to-second (into (there here) p)        q = Graph.interior B₂ p q
    to-second (into (there (there here)) p) q = εₘ
    to-second (into (there (there (there ()))) _) _

    to-third : (p : Path (node n fo-output (D₁ ∷ D₂ ∷ D₃ ∷ []))) (q : Path D₃) →
               object (node n fo-output (D₁ ∷ D₂ ∷ D₃ ∷ [])) p ⇒ object D₃ q
    to-third ε                            q = εₘ
    to-third (into here p)                q = e₁₃ p q
    to-third (into (there here) p)        q = e₂₃ p q
    to-third (into (there (there here)) p) q = Graph.interior B₃ p q
    to-third (into (there (there (there ()))) _) _

  E : Graph m (node n fo-output (D₁ ∷ D₂ ∷ D₃ ∷ []))
  E .Graph.from-input ε                                = input-to-output
  E .Graph.from-input (into here q)                    = Graph.from-input B₁ q ∘ inputs₁
  E .Graph.from-input (into (there here) q)            = Graph.from-input B₂ q ∘ inputs₂
  E .Graph.from-input (into (there (there here)) q)    = Graph.from-input B₃ q ∘ from-inputs₃
  E .Graph.from-input (into (there (there (there ()))) _)
  E .Graph.interior p ε                                 = out-edge p
  E .Graph.interior p (into here q)                     = to-first p q
  E .Graph.interior p (into (there here) q)             = to-second p q
  E .Graph.interior p (into (there (there here)) q)     = to-third p q
  E .Graph.interior p (into (there (there (there ()))) _)
  E .Graph.<-interior (into here p)                 (into here q)                 = Graph.<-interior B₁ p q
  E .Graph.<-interior (into here p)                 (into (there here) q)         = inj₁ tt
  E .Graph.<-interior (into here p)                 (into (there (there here)) q) = inj₁ tt
  E .Graph.<-interior (into (there here) p)         (into here q)                 = inj₂ ⟪ ≈-refl ⟫
  E .Graph.<-interior (into (there here) p)         (into (there here) q)         = Graph.<-interior B₂ p q
  E .Graph.<-interior (into (there here) p)         (into (there (there here)) q) = inj₁ tt
  E .Graph.<-interior (into (there (there here)) p) (into here q)                 = inj₂ ⟪ ≈-refl ⟫
  E .Graph.<-interior (into (there (there here)) p) (into (there here) q)         = inj₂ ⟪ ≈-refl ⟫
  E .Graph.<-interior (into (there (there here)) p) (into (there (there here)) q) = Graph.<-interior B₃ p q
  E .Graph.<-interior (into i p) ε = inj₁ tt
  E .Graph.<-interior ε ε                             = inj₂ ⟪ ≈-refl ⟫
  E .Graph.<-interior ε (into here q)                 = inj₂ ⟪ ≈-refl ⟫
  E .Graph.<-interior ε (into (there here) q)         = inj₂ ⟪ ≈-refl ⟫
  E .Graph.<-interior ε (into (there (there here)) q) = inj₂ ⟪ ≈-refl ⟫
  E .Graph.<-interior (into (there (there (there ()))) _) _
  E .Graph.<-interior _ (into (there (there (there ()))) _)

  private
    b1 : Path D₁ → V E
    b1 q = inj₂ (into here q)

    b2 : Path D₂ → V E
    b2 q = inj₂ (into (there here) q)

    b3 : Path D₃ → V E
    b3 q = inj₂ (into (there (there here)) q)

    er : V E
    er = inj₂ ε

    tgt : Path D₃ ⊎ Unit → V E
    tgt (inj₁ q) = b3 q
    tgt (inj₂ _) = er

    c₁ : (𝔽 m) ⇒ (𝔽 n₁)
    c₁ = collapse B₁ ∘ inputs₁

    c₂ : (𝔽 m) ⇒ (𝔽 n₂)
    c₂ = collapse B₂ ∘ inputs₂

    P₁ : (t : Path D₃ ⊎ Unit) → (𝔽 n₁) ⇒ vertex-object E (tgt t)
    P₁ (inj₁ q) = Graph.from-input B₃ q ∘ from-root₁
    P₁ (inj₂ _) = up₁

    K₁ : (t : Path D₃ ⊎ Unit) → (𝔽 m) ⇒ vertex-object E (tgt t)
    K₁ (inj₁ q) = Graph.from-input B₃ q ∘ from-inputs₃
    K₁ (inj₂ _) = input-to-output

    module S₁ = HidePremise B₁ (vertex-object E) (inj₁ input) b1 tgt inputs₁ P₁ K₁

    prem₁ : EdgeLabels (vertex-object B₁) → S₁.St
    prem₁ G .S₁.from-input q = G (inj₁ input) (inj₂ q)
    prem₁ G .S₁.interior p q = G (inj₂ p) (inj₂ q)

    module hidden₁ = S₁.Hidden (edge-labels E) prem₁ (λ G w → ≡-refl)

    start₁ : S₁.Start (edge-labels E) hidden₁.H⁰
    start₁ .S₁.into-start q = ≈-refl
    start₁ .S₁.interior-start p q = ≈-refl
    start₁ .S₁.tgt-start (inj₁ q) = ≈-refl
    start₁ .S₁.tgt-start (inj₂ _) = ≈-refl {f = input-to-output}
    start₁ .S₁.up-start (inj₁ q) = ≈-refl
    start₁ .S₁.up-start (inj₂ _) = ≈-refl {f = up₁}
    start₁ .S₁.off-start t        ε          ne = ⊥-elimₚ (ne ≡-refl)
    start₁ .S₁.off-start (inj₁ q) (into i p) _  = ≈-refl {f = εₘ}
    start₁ .S₁.off-start (inj₂ _) (into i p) _  = ≈-refl {f = εₘ}
    start₁ .S₁.sink q = root-row B₁ (inj₂ q)

    done₁ = hidden₁.done start₁
    κ₁ = ≈-trans (≡-to-≈ hidden₁.κ) (hide-paths⁺ B₁)

    module OutOfHidden = NoEdgeOutOfHidden (vertex-object E) b1 (inj₁ {A = Input}) b2
                                           (λ _ q → Graph.from-input B₂ q ∘ inputs₂)

    fixed₀ : OutOfHidden.Fixed (edge-labels E)
    fixed₀ .OutOfHidden.edge _ q = ≈-refl
    fixed₀ .OutOfHidden.no-edge w q = ≈-refl {f = εₘ}

    fixed₁ : OutOfHidden.Fixed hidden₁.G
    fixed₁ = OutOfHidden.fixed-hide-all (λ w → w) ps₁ (OutOfHidden.fixed-hide ε fixed₀)

    cols₂ : Path D₂ ⊎ (Path D₃ ⊎ Unit) → V E
    cols₂ (inj₁ q) = b2 q
    cols₂ (inj₂ t) = tgt t

    Bh₂ : (s : Path D₂) (t : Path D₂ ⊎ (Path D₃ ⊎ Unit)) → object D₂ s ⇒ vertex-object E (cols₂ t)
    Bh₂ s          (inj₁ q)        = Graph.interior B₂ s q
    Bh₂ s          (inj₂ (inj₁ q)) = e₂₃ s q
    Bh₂ ε          (inj₂ (inj₂ _)) = up₂
    Bh₂ (into i p) (inj₂ (inj₂ _)) = εₘ

    module IntoHidden₂ = NoEdgeIntoHidden (vertex-object E) b1 b2 cols₂ Bh₂

    fixed₂ : IntoHidden₂.Fixed hidden₁.G
    fixed₂ = IntoHidden₂.fixed-hide-all (λ w → w) ps₁ (IntoHidden₂.fixed-hide ε k₀)
      where
      k₀ : IntoHidden₂.Fixed (edge-labels E)
      k₀ .IntoHidden₂.edge s          (inj₁ q)        = ≈-refl
      k₀ .IntoHidden₂.edge s          (inj₂ (inj₁ q)) = ≈-refl {f = e₂₃ s q}
      k₀ .IntoHidden₂.edge ε          (inj₂ (inj₂ _)) = ≈-refl {f = up₂}
      k₀ .IntoHidden₂.edge (into i p) (inj₂ (inj₂ _)) = ≈-refl {f = εₘ}
      k₀ .IntoHidden₂.no-edge s w = ≈-refl {f = εₘ}

    Φ₃₁ : (𝔽 m) ⇒ (𝔽 m₃)
    Φ₃₁ = from-inputs₃ +ₘ (from-root₁ ∘ c₁)

    P₂ : (t : Path D₃ ⊎ Unit) → (𝔽 n₂) ⇒ vertex-object E (tgt t)
    P₂ (inj₁ q) = Graph.from-input B₃ q ∘ from-root₂
    P₂ (inj₂ _) = up₂

    K₂ : (t : Path D₃ ⊎ Unit) → (𝔽 m) ⇒ vertex-object E (tgt t)
    K₂ (inj₁ q) = Graph.from-input B₃ q ∘ Φ₃₁
    K₂ (inj₂ _) = input-to-output +ₘ (up₁ ∘ c₁)

    module S₂ = HidePremise B₂ (vertex-object E) (inj₁ input) b2 tgt inputs₂ P₂ K₂

    prem₂ : EdgeLabels (vertex-object B₂) → S₂.St
    prem₂ G .S₂.from-input q = G (inj₁ input) (inj₂ q)
    prem₂ G .S₂.interior p q = G (inj₂ p) (inj₂ q)

    module hidden₂ = S₂.Hidden hidden₁.G prem₂ (λ G w → ≡-refl)

    start₂ : S₂.Start hidden₁.G hidden₂.H⁰
    start₂ .S₂.into-start q = fixed₁ .OutOfHidden.edge input q
    start₂ .S₂.interior-start p q = fixed₂ .IntoHidden₂.edge p (inj₁ q)
    start₂ .S₂.tgt-start (inj₁ q) =
      ≈-trans (done₁ .S₁.tgt-ok (inj₁ q))
              (factor (Graph.from-input B₃ q) from-inputs₃ from-root₁ {h = hidden₁.H .S₁.from-input ε} {c = collapse B₁} inputs₁ κ₁)
    start₂ .S₂.tgt-start (inj₂ _) =
      ≈-trans {g = input-to-output +ₘ (up₁ ∘ (hidden₁.H .S₁.from-input ε ∘ inputs₁))}
              (done₁ .S₁.tgt-ok (inj₂ tt))
              (+ₘ-cong ≈-refl (∘-cong₂ {f = up₁} (∘-cong₁ {g = inputs₁} κ₁)))
    start₂ .S₂.up-start (inj₁ q) = fixed₂ .IntoHidden₂.edge ε (inj₂ (inj₁ q))
    start₂ .S₂.up-start (inj₂ _) = fixed₂ .IntoHidden₂.edge ε (inj₂ (inj₂ tt))
    start₂ .S₂.off-start t        ε          ne = ⊥-elimₚ (ne ≡-refl)
    start₂ .S₂.off-start (inj₁ q) (into i p) _  = fixed₂ .IntoHidden₂.edge (into i p) (inj₂ (inj₁ q))
    start₂ .S₂.off-start (inj₂ _) (into i p) _  = fixed₂ .IntoHidden₂.edge (into i p) (inj₂ (inj₂ tt))
    start₂ .S₂.sink q = root-row B₂ (inj₂ q)

    done₂ = hidden₂.done start₂
    κ₂ = ≈-trans (≡-to-≈ hidden₂.κ) (hide-paths⁺ B₂)

    hid₁₂ : Path D₁ ⊎ Path D₂ → V E
    hid₁₂ (inj₁ q) = b1 q
    hid₁₂ (inj₂ q) = b2 q

    Bh₃ : (s : Path D₃) (t : Path D₃ ⊎ Unit) → object D₃ s ⇒ vertex-object E (tgt t)
    Bh₃ s          (inj₁ q) = Graph.interior B₃ s q
    Bh₃ ε          (inj₂ _) = up₃
    Bh₃ (into i p) (inj₂ _) = εₘ

    module IntoHidden₃ = NoEdgeIntoHidden (vertex-object E) hid₁₂ b3 tgt Bh₃

    fixed₃ : IntoHidden₃.Fixed hidden₂.G
    fixed₃ =
      IntoHidden₃.fixed-hide-all inj₂ ps₂
        (IntoHidden₃.fixed-hide (inj₂ ε)
          (IntoHidden₃.fixed-hide-all inj₁ ps₁
            (IntoHidden₃.fixed-hide (inj₁ ε) k₀)))
      where
      k₀ : IntoHidden₃.Fixed (edge-labels E)
      k₀ .IntoHidden₃.edge s          (inj₁ q) = ≈-refl
      k₀ .IntoHidden₃.edge ε          (inj₂ _) = ≈-refl {f = up₃}
      k₀ .IntoHidden₃.edge (into i p) (inj₂ _) = ≈-refl {f = εₘ}
      k₀ .IntoHidden₃.no-edge s (inj₁ w) = ≈-refl {f = εₘ}
      k₀ .IntoHidden₃.no-edge s (inj₂ w) = ≈-refl {f = εₘ}

  Φ₃ : (𝔽 m) ⇒ (𝔽 m₃)
  Φ₃ = inputs₃ ∘ ⟨ ⟨ I , c₁ ⟩ , c₂ ⟩

  private
    Φ₃' : (𝔽 m) ⇒ (𝔽 m₃)
    Φ₃' = Φ₃₁ +ₘ (from-root₂ ∘ c₂)

    Φ₃-split : Φ₃' ≈ Φ₃
    Φ₃-split =
      ≈-sym (≈-trans (∘-pair inputs₃ ⟨ I , c₁ ⟩ c₂)
                     (+ₘ-cong (≈-trans (∘-pair (inputs₃ ∘ inb₁ {(𝔽 m) ⊕ᵥ (𝔽 n₁)} {(𝔽 n₂)}) I c₁)
                                         (+ₘ-cong (id-right {f = from-inputs₃}) (≈-refl {f = from-root₁ ∘ c₁})))
                                (≈-refl {f = from-root₂ ∘ c₂})))

    module S₃ = HidePremise B₃ (vertex-object E) (inj₁ input) b3 (λ (_ : Unit) → er) Φ₃' (λ _ → up₃)
                            (λ _ → (input-to-output +ₘ (up₁ ∘ c₁)) +ₘ (up₂ ∘ c₂))

    prem₃ : EdgeLabels (vertex-object B₃) → S₃.St
    prem₃ G .S₃.from-input q = G (inj₁ input) (inj₂ q)
    prem₃ G .S₃.interior p q = G (inj₂ p) (inj₂ q)

    module hidden₃ = S₃.Hidden hidden₂.G prem₃ (λ G w → ≡-refl)

    start₃ : S₃.Start hidden₂.G hidden₃.H⁰
    start₃ .S₃.into-start q =
      ≈-trans {g = (Graph.from-input B₃ q ∘ Φ₃₁) +ₘ ((Graph.from-input B₃ q ∘ from-root₂) ∘ (hidden₂.H .S₂.from-input ε ∘ inputs₂))}
              (done₂ .S₂.tgt-ok (inj₁ q))
              (factor (Graph.from-input B₃ q) Φ₃₁ from-root₂ {h = hidden₂.H .S₂.from-input ε} {c = collapse B₂} inputs₂ κ₂)
    start₃ .S₃.interior-start p q = fixed₃ .IntoHidden₃.edge p (inj₁ q)
    start₃ .S₃.tgt-start _ =
      ≈-trans {g = (input-to-output +ₘ (up₁ ∘ c₁)) +ₘ (up₂ ∘ (hidden₂.H .S₂.from-input ε ∘ inputs₂))}
              (done₂ .S₂.tgt-ok (inj₂ tt)) (+ₘ-cong ≈-refl (∘-cong₂ {f = up₂} (∘-cong₁ {g = inputs₂} κ₂)))
    start₃ .S₃.up-start _ = fixed₃ .IntoHidden₃.edge ε (inj₂ tt)
    start₃ .S₃.off-start _ ε          ne = ⊥-elimₚ (ne ≡-refl)
    start₃ .S₃.off-start _ (into i p) _  = fixed₃ .IntoHidden₃.edge (into i p) (inj₂ tt)
    start₃ .S₃.sink q = root-row B₃ (inj₂ q)

    l₁ l₂ l₃ : List (V E)
    l₁ = b1 ε ∷ map b1 ps₁
    l₂ = b2 ε ∷ map b2 ps₂
    l₃ = b3 ε ∷ map b3 ps₃

    lst : map inj₂ (vertices-result-first (node n fo-output (D₁ ∷ D₂ ∷ D₃ ∷ []))) ≡ l₁ ++ (l₂ ++ l₃)
    lst =
      ≡-trans (≡-cong (λ z → map inj₂ (map (into here) (ε ∷ ps₁) ++ map weaken z))
                (≡-trans (≡-cong (map (into here) (ε ∷ ps₂) ++_)
                                 (≡-cong (map weaken) (++-identityʳ (map (into here) (ε ∷ ps₃)))))
                         ≡-refl))
      (≡-trans (map-++ inj₂ (map (into here) (ε ∷ ps₁))
                       (map weaken (map (into here) (ε ∷ ps₂) ++ map weaken (map (into here) (ε ∷ ps₃)))))
      (≡-cong₂ _++_
        (≡-sym (map-∘ {g = inj₂} {f = into here} (ε ∷ ps₁)))
        (≡-trans (≡-cong (map inj₂) (map-++ weaken (map (into here) (ε ∷ ps₂))
                                            (map weaken (map (into here) (ε ∷ ps₃)))))
        (≡-trans (map-++ inj₂ (map weaken (map (into here) (ε ∷ ps₂)))
                         (map weaken (map weaken (map (into here) (ε ∷ ps₃)))))
        (≡-cong₂ _++_
          (≡-trans (≡-cong (map inj₂) (≡-sym (map-∘ {g = weaken} {f = into here} (ε ∷ ps₂))))
                   (≡-sym (map-∘ {g = inj₂} {f = λ q → weaken (into here q)} (ε ∷ ps₂))))
          (≡-trans (≡-cong (λ z → map inj₂ (map weaken z)) (≡-sym (map-∘ {g = weaken} {f = into here} (ε ∷ ps₃))))
          (≡-trans (≡-cong (map inj₂) (≡-sym (map-∘ {g = weaken} {f = λ q → weaken (into here q)} (ε ∷ ps₃))))
                   (≡-sym (map-∘ {g = inj₂} {f = λ q → weaken (weaken (into here q))} (ε ∷ ps₃))))))))))

    plumb : collapse E ≡ hidden₃.G (inj₁ input) er
    plumb =
      ≡-trans (≡-cong (λ l → hide-all (vertex-object E) (edge-labels E) l (inj₁ input) er) lst)
              (≡-trans (≡-cong (λ G → G (inj₁ input) er)
                               (foldl-++ (hide (vertex-object E)) (edge-labels E) l₁ (l₂ ++ l₃)))
                       (≡-cong (λ G → G (inj₁ input) er)
                               (foldl-++ (hide (vertex-object E)) hidden₁.G l₂ l₃)))

  agree : collapse E ≈ (((input-to-output +ₘ (up₁ ∘ c₁)) +ₘ (up₂ ∘ c₂)) +ₘ (up₃ ∘ (collapse B₃ ∘ Φ₃)))
  agree =
    ≈-trans (≡-to-≈ plumb)
            (≈-trans {g = ((input-to-output +ₘ (up₁ ∘ c₁)) +ₘ (up₂ ∘ c₂)) +ₘ (up₃ ∘ (hidden₃.H .S₃.from-input ε ∘ Φ₃'))}
                     (hidden₃.done start₃ .S₃.tgt-ok tt)
                     (+ₘ-cong ≈-refl (∘-cong₂ {f = up₃} (∘-cong (≈-trans (≡-to-≈ hidden₃.κ) (hide-paths⁺ B₃)) Φ₃-split))))

-- A premise of a rule whose premises run in parallel, with its wiring into the rule's inputs and root.
record Premise (m n : ℕ) (DB : Derivation) : Set₁ where
  constructor premise
  field
    {mB}    : ℕ
    B       : Graph mB DB
    inputs  : 𝔽 m ⇒ 𝔽 mB
    to-output      : 𝔽 (out-width DB) ⇒ 𝔽 n

-- A rule with a list of premises in parallel: each premise reads the rule's inputs through its
-- own input map and reaches the root through its own up map, with no edges between premises. The
-- premises are indexed by their derivations, one per premise position of the rule's graph.
module Ruleₛ {m n : ℕ} where

  open Premise

  from-inputs : ∀ {Ds s} (Ps : All (Premise m n) Ds) (i : Ds ∋ s) (q : Path s) →
                𝔽 m ⇒ object s q
  from-inputs []       ()        _
  from-inputs (P ∷ Ps) here      q = Graph.from-input (P .B) q ∘ P .inputs
  from-inputs (P ∷ Ps) (there i) q = from-inputs Ps i q

  interiors : ∀ {Ds s s'} (Ps : All (Premise m n) Ds) (i : Ds ∋ s) (p : Path s)
              (j : Ds ∋ s') (q : Path s') → object s p ⇒ object s' q
  interiors []       ()        _ _         _
  interiors (P ∷ Ps) here      p here      q = Graph.interior (P .B) p q
  interiors (P ∷ Ps) here      p (there j) q = εₘ
  interiors (P ∷ Ps) (there i) p here      q = εₘ
  interiors (P ∷ Ps) (there i) p (there j) q = interiors Ps i p j q

  to-outputs : ∀ {Ds s} (Ps : All (Premise m n) Ds) (i : Ds ∋ s) (p : Path s) →
               object s p ⇒ 𝔽 n
  to-outputs []       ()        _
  to-outputs (P ∷ Ps) here      ε          = P .to-output
  to-outputs (P ∷ Ps) here      (into j p) = εₘ
  to-outputs (P ∷ Ps) (there i) p          = to-outputs Ps i p

  <-interiors : ∀ {Ds s s'} (Ps : All (Premise m n) Ds) (i : Ds ∋ s) (p : Path s)
                (j : Ds ∋ s') (q : Path s') →
                lt∋ Ds i p j q ⊎ Prf (interiors Ps i p j q ≈ εₘ)
  <-interiors []       ()        _ _         _
  <-interiors (P ∷ Ps) here      p here      q = Graph.<-interior (P .B) p q
  <-interiors (P ∷ Ps) here      p (there j) q = inj₁ tt
  <-interiors (P ∷ Ps) (there i) p here      q = inj₂ ⟪ ≈-refl ⟫
  <-interiors (P ∷ Ps) (there i) p (there j) q = <-interiors Ps i p j q

  E : ∀ {Ds} (fo-output : Bool) → 𝔽 m ⇒ 𝔽 n → All (Premise m n) Ds → Graph m (node n fo-output Ds)
  E fo-output input-to-output Ps .Graph.from-input ε          = input-to-output
  E fo-output input-to-output Ps .Graph.from-input (into i q) = from-inputs Ps i q
  E fo-output input-to-output Ps .Graph.interior (into i p) (into j q) = interiors Ps i p j q
  E fo-output input-to-output Ps .Graph.interior (into i p) ε          = to-outputs Ps i p
  E fo-output input-to-output Ps .Graph.interior ε          _          = εₘ
  E fo-output input-to-output Ps .Graph.<-interior (into i p) (into j q) = <-interiors Ps i p j q
  E fo-output input-to-output Ps .Graph.<-interior (into i p) ε          = inj₁ tt
  E fo-output input-to-output Ps .Graph.<-interior ε ε          = inj₂ ⟪ ≈-refl ⟫
  E fo-output input-to-output Ps .Graph.<-interior ε (into j q) = inj₂ ⟪ ≈-refl ⟫

  rel : ∀ {Ds} → All (Premise m n) Ds → 𝔽 m ⇒ 𝔽 n
  rel []       = εₘ
  rel (P ∷ Ps) = (P .to-output ∘ (collapse (P .B) ∘ P .inputs)) +ₘ rel Ps

  -- Hiding the first premise folds its contribution into the root edge, leaving the same rule
  -- with one premise fewer; the remaining hiding is that rule's collapse read at its own vertices.
  private
    module Step {m₁ : ℕ} {D₁ : Derivation} (B₁ : Graph m₁ D₁) (inputs₁ : 𝔽 m ⇒ 𝔽 m₁)
                (up₁ : 𝔽 (out-width D₁) ⇒ 𝔽 n)
                {Ds : List Derivation} (Ps : All (Premise m n) Ds)
                (fo-output : Bool) (input-to-output : 𝔽 m ⇒ 𝔽 n) where

      whole = E fo-output input-to-output (premise B₁ inputs₁ up₁ ∷ Ps)
      out' = input-to-output +ₘ (up₁ ∘ (collapse B₁ ∘ inputs₁))
      rest = E fo-output out' Ps

      private
        b1 : Path D₁ → V whole
        b1 q = inj₂ (into here q)

        bt : Path (node n fo-output Ds) → V whole
        bt p = inj₂ (weaken p)

        er : V whole
        er = inj₂ ε

        Pt : (t : Path (node n fo-output Ds)) → 𝔽 (out-width D₁) ⇒ vertex-object whole (bt t)
        Pt ε          = up₁
        Pt (into i q) = εₘ

        Kt : (t : Path (node n fo-output Ds)) → 𝔽 m ⇒ vertex-object whole (bt t)
        Kt ε          = input-to-output
        Kt (into i q) = from-inputs Ps i q

        module S₁ = HidePremise B₁ (vertex-object whole) (inj₁ input) b1 bt inputs₁ Pt Kt

        prem₁ : EdgeLabels (vertex-object B₁) → S₁.St
        prem₁ G .S₁.from-input q = G (inj₁ input) (inj₂ q)
        prem₁ G .S₁.interior p q = G (inj₂ p) (inj₂ q)

        module hidden₁ = S₁.Hidden (edge-labels whole) prem₁ (λ G w → ≡-refl)

        start₁ : S₁.Start (edge-labels whole) hidden₁.H⁰
        start₁ .S₁.into-start q = ≈-refl
        start₁ .S₁.interior-start p q = ≈-refl
        start₁ .S₁.tgt-start ε          = ≈-refl {f = input-to-output}
        start₁ .S₁.tgt-start (into i q) = ≈-refl
        start₁ .S₁.up-start ε          = ≈-refl {f = up₁}
        start₁ .S₁.up-start (into i q) = ≈-refl {f = εₘ}
        start₁ .S₁.off-start t          ε          ne = ⊥-elimₚ (ne ≡-refl)
        start₁ .S₁.off-start ε          (into j p) _  = ≈-refl {f = εₘ}
        start₁ .S₁.off-start (into i q) (into j p) _  = ≈-refl {f = εₘ}
        start₁ .S₁.sink q = root-row B₁ (inj₂ q)

        done₁ = hidden₁.done start₁
        κ₁ = ≈-trans (≡-to-≈ hidden₁.κ) (hide-paths⁺ B₁)

        ps₁ = vertices-result-first D₁
        psᵣ = vertices-result-first (node n fo-output Ds)

        Bh : (s t : Path (node n fo-output Ds)) → vertex-object whole (bt s) ⇒ vertex-object whole (bt t)
        Bh (into i p) (into j q) = interiors Ps i p j q
        Bh (into i p) ε          = to-outputs Ps i p
        Bh ε          _          = εₘ

        module IntoH = NoEdgeIntoHidden (vertex-object whole) b1 bt bt Bh

        fixed₁ : IntoH.Fixed hidden₁.G
        fixed₁ = IntoH.fixed-hide-all (λ w → w) ps₁ (IntoH.fixed-hide ε fixed₀)
          where
          fixed₀ : IntoH.Fixed (edge-labels whole)
          fixed₀ .IntoH.edge (into i p) (into j q) = ≈-refl
          fixed₀ .IntoH.edge (into i p) ε          = ≈-refl
          fixed₀ .IntoH.edge ε          (into j q) = ≈-refl {f = εₘ}
          fixed₀ .IntoH.edge ε          ε          = ≈-refl {f = εₘ}
          fixed₀ .IntoH.no-edge (into i p) w = ≈-refl {f = εₘ}
          fixed₀ .IntoH.no-edge ε          w = ≈-refl {f = εₘ}

        sink₁ : ∀ y → hidden₁.G er y ≈ εₘ
        sink₁ = hide-all-sink (vertex-object whole) (edge-labels whole) er
                  (b1 ε ∷ map b1 ps₁) (root-row whole)

        source₁ : ∀ x → hidden₁.G x (inj₁ input) ≈ εₘ
        source₁ = hide-all-source (vertex-object whole) (edge-labels whole) (inj₁ input)
                    (b1 ε ∷ map b1 ps₁) input-col
          where
          input-col : ∀ x → edge-labels whole x (inj₁ input) ≈ εₘ
          input-col (inj₁ _) = ≈-refl {f = εₘ}
          input-col (inj₂ _) = ≈-refl {f = εₘ}

        -- The remaining relation read at the vertices of the rest, whose root is the rule's own.
        restrict : EdgeLabels (vertex-object whole) → EdgeLabels (vertex-object rest)
        restrict G (inj₁ _)            (inj₁ _)            = G (inj₁ input) (inj₁ input)
        restrict G (inj₁ _)            (inj₂ ε)            = G (inj₁ input) er
        restrict G (inj₁ _)            (inj₂ (into j q))   = G (inj₁ input) (bt (into j q))
        restrict G (inj₂ ε)            (inj₁ _)            = G er (inj₁ input)
        restrict G (inj₂ ε)            (inj₂ ε)            = G er er
        restrict G (inj₂ ε)            (inj₂ (into j q))   = G er (bt (into j q))
        restrict G (inj₂ (into i p))   (inj₁ _)            = G (bt (into i p)) (inj₁ input)
        restrict G (inj₂ (into i p))   (inj₂ ε)            = G (bt (into i p)) er
        restrict G (inj₂ (into i p))   (inj₂ (into j q))   = G (bt (into i p)) (bt (into j q))

        restrict-hide : ∀ G {s} (i : Ds ∋ s) (w : Path s) →
                        restrict (hide (vertex-object whole) G (bt (into i w))) ≐
                        hide (vertex-object rest) (restrict G) (inj₂ (into i w))
        restrict-hide G i w (inj₁ _)          (inj₁ _)          = ≈-refl
        restrict-hide G i w (inj₁ _)          (inj₂ ε)          = ≈-refl
        restrict-hide G i w (inj₁ _)          (inj₂ (into _ _)) = ≈-refl
        restrict-hide G i w (inj₂ ε)          (inj₁ _)          = ≈-refl
        restrict-hide G i w (inj₂ ε)          (inj₂ ε)          = ≈-refl
        restrict-hide G i w (inj₂ ε)          (inj₂ (into _ _)) = ≈-refl
        restrict-hide G i w (inj₂ (into _ _)) (inj₁ _)          = ≈-refl
        restrict-hide G i w (inj₂ (into _ _)) (inj₂ ε)          = ≈-refl
        restrict-hide G i w (inj₂ (into _ _)) (inj₂ (into _ _)) = ≈-refl

        restrict-hide-all : ∀ G ws → All (_≢ ε) ws →
                            restrict (hide-all (vertex-object whole) G (map bt ws)) ≐
                            hide-all (vertex-object rest) (restrict G) (map inj₂ ws)
        restrict-hide-all G []              _          x y = ≈-refl
        restrict-hide-all G (ε ∷ ws)        (ne ∷ _)   x y = ⊥-elimₚ (ne ≡-refl)
        restrict-hide-all G (into i w ∷ ws) (_ ∷ hs)   x y =
          ≈-trans (restrict-hide-all (hide (vertex-object whole) G (bt (into i w))) ws hs x y)
                  (hide-all-cong (vertex-object rest) (map inj₂ ws) (restrict-hide G i w) x y)

        agree-rest : restrict hidden₁.G ≐ edge-labels rest
        agree-rest (inj₁ _)          (inj₁ _)          = source₁ (inj₁ input)
        agree-rest (inj₁ _)          (inj₂ (into j q)) =
          ≈-trans (done₁ .S₁.tgt-ok (into j q))
                  (absorb₁ (from-inputs Ps j q) (hidden₁.H .S₁.from-input ε ∘ inputs₁))
        agree-rest (inj₁ _)          (inj₂ ε)          =
          ≈-trans (done₁ .S₁.tgt-ok ε)
                  (+ₘ-cong ≈-refl (∘-cong₂ {f = up₁} (∘-cong₁ {g = inputs₁} κ₁)))
        agree-rest (inj₂ (into i p)) (inj₁ _)          = source₁ (bt (into i p))
        agree-rest (inj₂ ε)          (inj₁ _)          = source₁ er
        agree-rest (inj₂ (into i p)) (inj₂ (into j q)) = fixed₁ .IntoH.edge (into i p) (into j q)
        agree-rest (inj₂ (into i p)) (inj₂ ε)          = fixed₁ .IntoH.edge (into i p) ε
        agree-rest (inj₂ ε)          (inj₂ (into j q)) = sink₁ (bt (into j q))
        agree-rest (inj₂ ε)          (inj₂ ε)          = sink₁ er

        lst : map inj₂ (vertices-result-first (node n fo-output (D₁ ∷ Ds)))
              ≡ (b1 ε ∷ map b1 ps₁) ++ map bt psᵣ
        lst =
          ≡-trans (map-++ inj₂ (map (into here) (ε ∷ ps₁)) (map weaken psᵣ))
                  (≡-cong₂ _++_
                    (≡-sym (map-∘ {g = inj₂} {f = into here} (ε ∷ ps₁)))
                    (≡-sym (map-∘ {g = inj₂} {f = weaken} psᵣ)))

        plumb : collapse whole ≡
                hide-all (vertex-object whole) hidden₁.G (map bt psᵣ) (inj₁ input) er
        plumb =
          ≡-trans (≡-cong (λ l → hide-all (vertex-object whole) (edge-labels whole) l (inj₁ input) er) lst)
                  (≡-cong (λ G → G (inj₁ input) er)
                          (foldl-++ (hide (vertex-object whole)) (edge-labels whole)
                                    (b1 ε ∷ map b1 ps₁) (map bt psᵣ)))

      reduce : collapse whole ≈ collapse rest
      reduce =
        ≈-trans (≡-to-≈ plumb)
        (≈-trans (restrict-hide-all hidden₁.G psᵣ (vertices-result-first-no-ε (node n fo-output Ds))
                                    (inj₁ input) (inj₂ ε))
                 (hide-all-cong (vertex-object rest) (map inj₂ psᵣ) agree-rest
                                (inj₁ input) (inj₂ ε)))

  agree : ∀ {Ds} (fo-output : Bool) (input-to-output : 𝔽 m ⇒ 𝔽 n) (Ps : All (Premise m n) Ds) →
          collapse (E fo-output input-to-output Ps) ≈ (input-to-output +ₘ rel Ps)
  agree fo-output input-to-output [] = ≈-sym (+ₘ-runit input-to-output)
  agree fo-output input-to-output (P ∷ Ps) =
    ≈-trans (Step.reduce (P .B) (P .inputs) (P .to-output) Ps fo-output input-to-output)
    (≈-trans (agree fo-output (input-to-output +ₘ (P .to-output ∘ (collapse (P .B) ∘ P .inputs))) Ps)
             (+ₘ-assoc {f = input-to-output} {g = P .to-output ∘ (collapse (P .B) ∘ P .inputs)} {h = rel Ps}))
