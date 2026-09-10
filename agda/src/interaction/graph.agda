{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.Bool using (Bool; true; false; not; _∨_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; toℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; map; mapMaybe; foldl; filterᵇ; length; upTo;
                             applyUpTo; reverse)
open import Agda.Builtin.Strict using (primForce)
open import Data.Bool.ListAction using (any)
open import Data.List.Properties using (++-identityʳ; map-++; map-∘; foldl-++; length-map)
open import Data.List.Relation.Unary.All using (All; []; _∷_; universal)
  renaming (map to All-map; lookup to All-lookup)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_) renaming (map to AllPairs-map)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-++⁺ˡ; ∈-++⁺ʳ)
import Data.List.Relation.Unary.All.Properties as AllP
import Data.List.Relation.Unary.AllPairs.Properties as AllPairsP
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_; _<ᵇ_; _+_; _*_; _∸_; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-suc; +-identityʳ; <⇒≢)
open import Data.Product using (Σ; _×_; _,_)
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
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst; subst₂; isEquivalence)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; cong to ≡-cong; cong₂ to ≡-cong₂)
open import Relation.Nullary using (¬_)
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
open import matrix-embedding S using (𝔽; 𝔽F-full; mat; mat-cong; mat-comp; mat-+; mat-ε)
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

-- A node carries the width of its input, and the width and first-order marking of its output.
data Derivation : Set where
  node : ℕ → ℕ → Bool → List Derivation → Derivation

in-width : Derivation → ℕ
in-width (node m _ _ _) = m

out-width : Derivation → ℕ
out-width (node _ n _ _) = n

out-fo : Derivation → Bool
out-fo (node _ _ b _) = b

-- Positions of a premise in a premise list, in the style of list membership but with the premise
-- as an index rather than an equality.
data _∋_ : List Derivation → Derivation → Set where
  here  : ∀ {D Ds} → (D ∷ Ds) ∋ D
  there : ∀ {D D' Ds} → Ds ∋ D → (D' ∷ Ds) ∋ D

-- A vertex of a derivation: the path to the subderivation whose conclusion it denotes, one premise
-- position per level. The empty path denotes the derivation's own conclusion.
data Path : Derivation → Set where
  ε    : ∀ {D} → Path D
  into : ∀ {m n b Ds D} → Ds ∋ D → Path D → Path (node m n b Ds)

-- The subderivation whose conclusion a path reaches.
deriv-at : (D : Derivation) → Path D → Derivation
deriv-at D ε = D
deriv-at (node _ _ _ _) (into {D = D} i p) = deriv-at D p

in-width-at : (D : Derivation) → Path D → ℕ
in-width-at D q = in-width (deriv-at D q)

width-at : (D : Derivation) → Path D → ℕ
width-at D q = out-width (deriv-at D q)

fo-at : (D : Derivation) → Path D → Bool
fo-at D q = out-fo (deriv-at D q)

child : (Ds : List Derivation) → ℕ → Maybe (Σ Derivation (Ds ∋_))
child []       _       = nothing
child (D ∷ Ds) zero    = just (D , here)
child (D ∷ Ds) (suc k) with child Ds k
... | just (D' , i) = just (D' , there i)
... | nothing       = nothing

-- The path through given premise positions, when each position exists.
path-at : (D : Derivation) → List ℕ → Maybe (Path D)
path-at D             []       = just ε
path-at (node m n b Ds) (k ∷ ks) with child Ds k
... | nothing       = nothing
... | just (D' , i) with path-at D' ks
...   | nothing = nothing
...   | just p  = just (into i p)

object : (D : Derivation) → Path D → Semimodule
object D q = 𝔽 (width-at D q)

private
  into-here-injective : ∀ {m n b D Ds} {p q : Path D} →
                        into {m} {n} {b} {D ∷ Ds} here p ≡ into here q → p ≡ q
  into-here-injective ≡-refl = ≡-refl

  into-there-injective : ∀ {m n b D' Ds D₁ D₂} {i₁ : Ds ∋ D₁} {i₂ : Ds ∋ D₂}
                         {p : Path D₁} {q : Path D₂} →
                         into {m} {n} {b} {D' ∷ Ds} (there i₁) p ≡ into (there i₂) q →
                         into {m} {n} {b} {Ds} i₁ p ≡ into i₂ q
  into-there-injective ≡-refl = ≡-refl

mutual
  _≟_ : ∀ {D} → DecidableEquality (Path D)
  ε        ≟ ε        = yes ≡-refl
  ε        ≟ into _ _ = no (λ ())
  into _ _ ≟ ε        = no (λ ())
  into i p ≟ into j q = ≟-into i p j q

  ≟-into : ∀ {m n b Ds D D'} (i : Ds ∋ D) (p : Path D) (j : Ds ∋ D') (q : Path D') →
           Dec (into {m} {n} {b} i p ≡ into j q)
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
weaken : ∀ {m n b D Ds} → Path (node m n b Ds) → Path (node m n b (D ∷ Ds))
weaken ε          = ε
weaken (into i p) = into (there i) p

private
  weaken-injective : ∀ {m n b D Ds} {p q : Path (node m n b Ds)} →
                     weaken {m} {n} {b} {D} p ≡ weaken q → p ≡ q
  weaken-injective {p = ε}        {q = ε}        _ = ≡-refl
  weaken-injective {p = ε}        {q = into _ _} ()
  weaken-injective {p = into _ _} {q = ε}        ()
  weaken-injective {p = into _ _} {q = into _ _} e with into-there-injective e
  ... | ≡-refl = ≡-refl

  weaken-no-ε : ∀ {m n b D Ds} {p : Path (node m n b Ds)} → p ≢ ε → weaken {m} {n} {b} {D} p ≢ ε
  weaken-no-ε {p = ε}        ne _ = ne ≡-refl
  weaken-no-ε {p = into _ _} _  ()

-- The vertices of a derivation in evaluation order: each premise's interior, then its conclusion,
-- then the premises after it. The derivation's own conclusion is not listed.
mutual
  vertices : (D : Derivation) → List (Path D)
  vertices (node m n b Ds) = vertices-of m n b Ds

  vertices-of : (m n : ℕ) (b : Bool) (Ds : List Derivation) → List (Path (node m n b Ds))
  vertices-of m n b []       = []
  vertices-of m n b (D ∷ Ds) =
    map (into here) (vertices D ++ (ε ∷ [])) ++ map weaken (vertices-of m n b Ds)

mutual
  vertices-no-ε : (D : Derivation) → All (_≢ ε) (vertices D)
  vertices-no-ε (node m n b Ds) = vertices-of-no-ε m n b Ds

  vertices-of-no-ε : ∀ m n b Ds → All (_≢ ε) (vertices-of m n b Ds)
  vertices-of-no-ε m n b []       = []
  vertices-of-no-ε m n b (D ∷ Ds) =
    AllP.++⁺ (AllP.map⁺ (universal (λ _ ()) (vertices D ++ (ε ∷ []))))
             (AllP.map⁺ (All-map weaken-no-ε (vertices-of-no-ε m n b Ds)))

private
  into-here-≢-weaken : ∀ {m n b D Ds} (x : Path D) {y : Path (node m n b Ds)} →
                       y ≢ ε → into {m} {n} {b} {D ∷ Ds} here x ≢ weaken y
  into-here-≢-weaken x {y = ε}        ne _ = ne ≡-refl
  into-here-≢-weaken x {y = into _ _} _  ()

mutual
  distinct : (D : Derivation) → AllPairs _≢_ (vertices D)
  distinct (node m n b Ds) = distinct-of m n b Ds

  distinct-of : ∀ m n b Ds → AllPairs _≢_ (vertices-of m n b Ds)
  distinct-of m n b []       = []
  distinct-of m n b (D ∷ Ds) =
    AllPairsP.++⁺
      (AllPairsP.map⁺ (AllPairs-map (λ h e → h (into-here-injective e)) (distinct-one D)))
      (AllPairsP.map⁺ (AllPairs-map (λ h e → h (weaken-injective e)) (distinct-of m n b Ds)))
      (AllP.map⁺ (universal (λ x → AllP.map⁺ (All-map (into-here-≢-weaken x)
                                                      (vertices-of-no-ε m n b Ds)))
                            (vertices D ++ (ε ∷ []))))

  distinct-one : (D : Derivation) → AllPairs _≢_ (vertices D ++ (ε ∷ []))
  distinct-one D =
    AllPairsP.++⁺ (distinct D) ([] ∷ [])
                  (All-map (λ h → h ∷ []) (vertices-no-ε D))

mutual
  ∈-vertices : {D : Derivation} (p : Path D) → p ≢ ε → p ∈ vertices D
  ∈-vertices {node m n b Ds} ε          ne = ⊥-elim (ne ≡-refl)
  ∈-vertices {node m n b Ds} (into i q) _  = ∈-vertices-of i q

  ∈-vertices-of : {m n : ℕ} {b : Bool} {Ds : List Derivation} {D : Derivation}
                  (i : Ds ∋ D) (q : Path D) → into {m} {n} {b} i q ∈ vertices-of m n b Ds
  ∈-vertices-of {Ds = D ∷ Ds} here      q = ∈-++⁺ˡ (∈-map⁺ (into here) q-mem)
    where
    q-mem : q ∈ (vertices D ++ (ε ∷ []))
    q-mem with q ≟ ε
    ... | yes ≡-refl = ∈-++⁺ʳ (vertices D) (here ≡-refl)
    ... | no  ne     = ∈-++⁺ˡ (∈-vertices q ne)
  ∈-vertices-of {Ds = D ∷ Ds} (there i) q =
    ∈-++⁺ʳ (map (into here) (vertices D ++ (ε ∷ []))) (∈-map⁺ weaken (∈-vertices-of i q))


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
  lt : (D : Derivation) → Path D → Path D → Set
  lt _              ε          _          = ⊥
  lt _              (into _ _) ε          = Unit
  lt (node _ _ _ Ds)  (into i p) (into j q) = lt∋ Ds i p j q

  lt∋ : (Ds : List Derivation) {D D' : Derivation} → Ds ∋ D → Path D → Ds ∋ D' → Path D' → Set
  lt∋ (D ∷ _)  here      p here      q = lt D p q
  lt∋ _        here      _ (there _) _ = Unit
  lt∋ _        (there _) _ here      _ = ⊥
  lt∋ (_ ∷ Ds) (there i) p (there j) q = lt∋ Ds i p j q

private
  mutual
    lt-trans : ∀ D (p q r : Path D) → lt D p q → lt D q r → lt D p r
    lt-trans _             ε          _          _          () _
    lt-trans _             (into _ _) ε          _          _  ()
    lt-trans _             (into _ _) (into _ _) ε          _  _ = tt
    lt-trans (node _ _ _ Ds) (into i p) (into j q) (into k r) a  b = lt∋-trans Ds i p j q k r a b

    lt∋-trans : ∀ Ds {D₁ D₂ D₃} (i : Ds ∋ D₁) (p : Path D₁) (j : Ds ∋ D₂) (q : Path D₂)
                (k : Ds ∋ D₃) (r : Path D₃) →
                lt∋ Ds i p j q → lt∋ Ds j q k r → lt∋ Ds i p k r
    lt∋-trans (D ∷ _)  here      p here      q here      r a  b = lt-trans D p q r a b
    lt∋-trans _        here      _ here      _ (there _) _  _  _ = tt
    lt∋-trans _        here      _ (there _) _ (there _) _  _  _ = tt
    lt∋-trans _        here      _ (there _) _ here      _  _  ()
    lt∋-trans _        (there _) _ here      _ _         _  ()
    lt∋-trans (_ ∷ Ds) (there i) p (there j) q (there k) r a  b = lt∋-trans Ds i p j q k r a b
    lt∋-trans _        (there _) _ (there _) _ here      _  _  ()

  mutual
    lt-asym : ∀ D (p q : Path D) → lt D p q → lt D q p → ⊥
    lt-asym _             ε          _          () _
    lt-asym _             (into _ _) ε          _  ()
    lt-asym (node _ _ _ Ds) (into i p) (into j q) a  b = lt∋-asym Ds i p j q a b

    lt∋-asym : ∀ Ds {D₁ D₂} (i : Ds ∋ D₁) (p : Path D₁) (j : Ds ∋ D₂) (q : Path D₂) →
               lt∋ Ds i p j q → lt∋ Ds j q i p → ⊥
    lt∋-asym (D ∷ _)  here      p here      q a  b = lt-asym D p q a b
    lt∋-asym _        here      _ (there _) _ _  ()
    lt∋-asym _        (there _) _ here      _ () _
    lt∋-asym (_ ∷ Ds) (there i) p (there j) q a  b = lt∋-asym Ds i p j q a b

lt-order : (D : Derivation) → IsStrictOrder (lt D)
lt-order D .IsStrictOrder.trans = lt-trans D
lt-order D .IsStrictOrder.asym  = lt-asym D

mutual
  lt-compare : (D : Derivation) → Trichotomous _≡_ (lt D)
  lt-compare _             ε          ε          = tri≈ (λ ()) ≡-refl (λ ())
  lt-compare _             ε          (into _ _) = tri> (λ ()) (λ ()) tt
  lt-compare _             (into _ _) ε          = tri< tt (λ ()) (λ ())
  lt-compare (node _ _ _ Ds) (into i p) (into j q) = lt∋-compare Ds i p j q

  lt∋-compare : ∀ {m n b} Ds {D₁ D₂} (i : Ds ∋ D₁) (p : Path D₁) (j : Ds ∋ D₂) (q : Path D₂) →
                Tri (lt∋ Ds i p j q) (into {m} {n} {b} i p ≡ into j q) (lt∋ Ds j q i p)
  lt∋-compare (D ∷ _) here p here q with lt-compare D p q
  ... | tri< a ¬b ¬c = tri< a (λ e → ¬b (into-here-injective e)) ¬c
  ... | tri≈ ¬a e ¬c = tri≈ ¬a (≡-cong (into here) e) ¬c
  ... | tri> ¬a ¬b c = tri> ¬a (λ e → ¬b (into-here-injective e)) c
  lt∋-compare _        here      _ (there _) _ = tri< tt (λ ()) (λ ())
  lt∋-compare _        (there _) _ here      _ = tri> (λ ()) (λ ()) tt
  lt∋-compare (_ ∷ Ds) (there i) p (there j) q with lt∋-compare Ds i p j q
  ... | tri< a ¬b ¬c = tri< a (λ e → ¬b (into-there-injective e)) ¬c
  ... | tri≈ ¬a e ¬c = tri≈ ¬a (there-≡ e) ¬c
    where
    there-≡ : ∀ {m n b D' Ds D₁ D₂} {i : Ds ∋ D₁} {j : Ds ∋ D₂} {p : Path D₁} {q : Path D₂} →
              into {m} {n} {b} {Ds} i p ≡ into j q →
              into {m} {n} {b} {D' ∷ Ds} (there i) p ≡ into (there j) q
    there-≡ ≡-refl = ≡-refl
  ... | tri> ¬a ¬b c = tri> ¬a (λ e → ¬b (into-there-injective e)) c

private
  lt-strict-total : (D : Derivation) → IsStrictTotalOrder _≡_ (lt D)
  lt-strict-total D .IsStrictTotalOrder.isStrictPartialOrder .IsStrictPartialOrder.isEquivalence =
    isEquivalence
  lt-strict-total D .IsStrictTotalOrder.isStrictPartialOrder .IsStrictPartialOrder.irrefl {x} ≡-refl =
    IsStrictOrder.irrefl (lt-order D) x
  lt-strict-total D .IsStrictTotalOrder.isStrictPartialOrder .IsStrictPartialOrder.trans {p} {q} {r} =
    IsStrictOrder.trans (lt-order D) p q r
  lt-strict-total D .IsStrictTotalOrder.isStrictPartialOrder .IsStrictPartialOrder.<-resp-≈ =
    (λ { ≡-refl l → l }) , (λ { ≡-refl l → l })
  lt-strict-total D .IsStrictTotalOrder.compare = lt-compare D

vertex-order : (D : Derivation) → StrictTotalOrder 0ℓ 0ℓ 0ℓ
vertex-order D .StrictTotalOrder.Carrier = Path D
vertex-order D .StrictTotalOrder._≈_ = _≡_
vertex-order D .StrictTotalOrder._<_ = lt D
vertex-order D .StrictTotalOrder.isStrictTotalOrder = lt-strict-total D

EdgeLabels : {V : Set} → (V → Semimodule) → Set
EdgeLabels {V} vertex-object = (x y : V) → vertex-object x ⇒ vertex-object y

table-of : ∀ {a b : ℕ} → 𝔽 a ⇒ 𝔽 b → M.Table
table-of f = M.to-table (∃ₛ.fst (𝔽F-full f))

record Graph (m : ℕ) (D : Derivation) : Set₁ where
  field
    from-input : (q : Path D) → 𝔽 m ⇒ object D q
    interior   : EdgeLabels (object D)
    -- Every non-zero relation runs strictly forward in the evaluation order. The inputs are below
    -- everything, and the conclusion above everything, so it is a sink by construction.
    <-interior : ∀ p q → lt D p q ⊎ Prf (interior p q ≈ εₘ)
    -- In-neighbours of each vertex (inj₁ the inputs vertex): unlisted sources relate to it by zero.
    in-neighbours : (q : Path D) → List (Input ⊎ Path D)
    -- "input" here is the input of the rule concluding at q, not the graph's inputs vertex.
    parent-to-input : Path D → M.Table
    roots-to-input  : Path D → List (Path D × M.Table)
    input-to-output : Path D → M.Table

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
  vertices-result-first : (D : Derivation) → List (Path D)
  vertices-result-first (node m n b Ds) = vertices-of-result-first m n b Ds

  vertices-of-result-first : (m n : ℕ) (b : Bool) (Ds : List Derivation) → List (Path (node m n b Ds))
  vertices-of-result-first m n b []       = []
  vertices-of-result-first m n b (D ∷ Ds) =
    map (into here) (ε ∷ vertices-result-first D) ++ map weaken (vertices-of-result-first m n b Ds)

-- The result-first enumeration is a permutation of the canonical one.
mutual
  vertices-perm : (D : Derivation) → vertices D ↭ vertices-result-first D
  vertices-perm (node m n b Ds) = vertices-of-perm m n b Ds

  vertices-of-perm : ∀ m n b Ds → vertices-of m n b Ds ↭ vertices-of-result-first m n b Ds
  vertices-of-perm m n b []       = ↭-refl
  vertices-of-perm m n b (D ∷ Ds) =
    ++⁺ (map⁺ (into here) (vertices-one-perm D)) (map⁺ weaken (vertices-of-perm m n b Ds))

  vertices-one-perm : (D : Derivation) → (vertices D ++ (ε ∷ [])) ↭ (ε ∷ vertices-result-first D)
  vertices-one-perm D =
    ↭-trans (PermutationP.shift ε (vertices D) [])
            (↭.prep ε (↭-trans (↭-reflexive (++-identityʳ (vertices D))) (vertices-perm D)))

vertices-result-first-no-ε : (D : Derivation) → All (_≢ ε) (vertices-result-first D)
vertices-result-first-no-ε D = All-resp-↭ (vertices-perm D) (vertices-no-ε D)

module _ {m : ℕ} {D : Derivation} (𝒢 : Graph m D) where
  open Graph 𝒢

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

-- A graph tabulated once: the vertices named by their numbers in the underlying derivation graph,
-- and the relations stored as tables, one row per source vertex with one slot per target, both in
-- evaluation order (the inputs vertex first, the conclusion last). An empty slot is the zero
-- relation, so a read forces only the slot it consults. Rows, slots and widths are indexed by
-- position in the vertex list, not by vertex number.
record Tabulation : Set where
  field
    numbers : List ℕ
    widths  : List ℕ
    edges   : List (List (Maybe M.Table))

open Tabulation public using (widths; edges)

private
  sum : List Semiring.Carrier → Semiring.Carrier
  sum []       = Semiring.ε
  sum (x ∷ xs) = x Semiring.+ sum xs

  mul : ℕ → ℕ → ℕ → M.Table → M.Table → M.Table
  mul r k c t u =
    map (λ i → map (λ j → sum (map (λ l → M.nth Semiring.ε l (M.nth [] i t) Semiring.·
                                          M.nth Semiring.ε j (M.nth [] l u))
                                   (upTo k)))
                   (upTo c))
        (upTo r)

vertex-count : Derivation → ℕ
vertex-count-of : List Derivation → ℕ
vertex-count (node m n b Ds)   = vertex-count-of Ds
vertex-count-of []           = 0
vertex-count-of (D ∷ Ds)     = suc (vertex-count D) + vertex-count-of Ds

-- Index of a path in (vertices D ++ (ε ∷ [])).
path-position : (D : Derivation) → Path D → ℕ
path-position-of : (Ds : List Derivation) {D : Derivation} → Ds ∋ D → Path D → ℕ
path-position (node m n b Ds) ε             = vertex-count-of Ds
path-position (node m n b Ds) (into i q)    = path-position-of Ds i q
path-position-of (D ∷ Ds) here      q = path-position D q
path-position-of (D ∷ Ds) (there i) q = suc (vertex-count D) + path-position-of Ds i q

module _ {m : ℕ} {D : Derivation} (𝒢 : Graph m D) where

  all-vertices : List (V 𝒢)
  all-vertices = inj₁ input ∷ map inj₂ (vertices D) ++ (inj₂ ε ∷ [])

  private
    _≟ᵥ_ : DecidableEquality (V 𝒢)
    _≟ᵥ_ = SumP.≡-dec input-≟ (_≟_ {D})

  find-vertex : V 𝒢 → ℕ → List (V 𝒢) → ℕ
  find-vertex x k []       = k
  find-vertex x k (y ∷ ys) = if ⌊ x ≟ᵥ y ⌋ then k else find-vertex x (suc k) ys

  index-of : V 𝒢 → ℕ
  index-of x = find-vertex x 0 all-vertices

module _ {m : ℕ} {D : Derivation} (𝒢 : Graph m D)
         (ε-dec : (x : Semiring.Carrier) → Dec (x ≡ Semiring.ε))
         (tick : {A : Set} → String → A → A) where

  edge-table : (u v : V 𝒢) → M.Table
  edge-table u v = tick "edge" (M.to-table (∃ₛ.fst (𝔽F-full (edge-labels 𝒢 u v))))

  nonzero-entry : Semiring.Carrier → Bool
  nonzero-entry x = not ⌊ ε-dec x ⌋

  nonzero-slot : M.Table → Bool
  nonzero-slot = any (any nonzero-entry)

  edge-slot : M.Table → Maybe M.Table
  edge-slot t = if nonzero-slot t then just t else nothing

  edge-row : V 𝒢 → List (Maybe M.Table)
  edge-row x = map (λ y → edge-slot (edge-table x y)) (all-vertices 𝒢)

  tabulation : Tabulation
  tabulation .Tabulation.numbers = upTo (length (all-vertices 𝒢))
  tabulation .Tabulation.widths   = map (vertex-width 𝒢) (all-vertices 𝒢)
  tabulation .Tabulation.edges    = map edge-row (all-vertices 𝒢)


find-number : ℕ → ℕ → List ℕ → Maybe ℕ
find-number i k []       = nothing
find-number i k (j ∷ js) = if i ≡ᵇ j then just k else find-number i (suc k) js

position : Tabulation → ℕ → Maybe ℕ
position T i = find-number i 0 (Tabulation.numbers T)

table-at : Tabulation → ℕ → ℕ → Maybe M.Table
table-at T i j = M.nth nothing j (M.nth [] i (T .edges))

zero-table : ℕ → ℕ → M.Table
zero-table r c = map (λ _ → map (λ _ → Semiring.ε) (upTo c)) (upTo r)

add-table : ℕ → ℕ → M.Table → M.Table → M.Table
add-table r c t u =
  map (λ i → map (λ j → M.nth Semiring.ε j (M.nth [] i t) Semiring.+ M.nth Semiring.ε j (M.nth [] i u))
             (upTo c))
      (upTo r)

read-table : Tabulation → ℕ → ℕ → M.Table
read-table T i j with table-at T i j
... | just t  = t
... | nothing = zero-table (M.nth 0 j (T .widths)) (M.nth 0 i (T .widths))

mask-slots : (ℕ → Bool) → Bool → List ℕ → List (Maybe M.Table) → List (Maybe M.Table)
mask-slots member keep-row _        []       = []
mask-slots member keep-row []       _        = []
mask-slots member keep-row (m ∷ ms) (t ∷ ts) =
  (if keep-row ∨ member m then t else nothing) ∷ mask-slots member keep-row ms ts

mask-rows : (ℕ → Bool) → List ℕ → List ℕ → List (List (Maybe M.Table)) →
            List (List (Maybe M.Table))
mask-rows member all-ns _        []       = []
mask-rows member all-ns []       _        = []
mask-rows member all-ns (n ∷ ns) (r ∷ rs) =
  mask-slots member (member n) all-ns r ∷ mask-rows member all-ns ns rs

restrict : List ℕ → Tabulation → Tabulation
restrict region T .Tabulation.numbers = Tabulation.numbers T
restrict region T .Tabulation.widths  = T .widths
restrict region T .Tabulation.edges   =
  mask-rows (λ n → any (n ≡ᵇ_) region) (Tabulation.numbers T) (Tabulation.numbers T) (T .edges)

module _ {m : ℕ} {D : Derivation} (𝒢 : Graph m D) where

  table-morphism : (x y : V 𝒢) → Maybe M.Table → vertex-object 𝒢 x ⇒ vertex-object 𝒢 y
  table-morphism x y (just t) = mat (M.look {vertex-width 𝒢 y} {vertex-width 𝒢 x} t)
  table-morphism x y nothing  = εₘ

  read-slot : Tabulation → (x y : V 𝒢) → Maybe ℕ → Maybe ℕ → vertex-object 𝒢 x ⇒ vertex-object 𝒢 y
  read-slot T x y (just a) (just b) = table-morphism x y (table-at T a b)
  read-slot T x y _        _        = εₘ

  read-edge : Tabulation → (x y : V 𝒢) → vertex-object 𝒢 x ⇒ vertex-object 𝒢 y
  read-edge T x y = read-slot T x y (position T (index-of 𝒢 x)) (position T (index-of 𝒢 y))

-- Hiding over a tabulation, with the hidden vertices listed so that every nonzero edge among
-- them runs forward.
module Tabulated (T : Tabulation) (tick : {A : Set} → String → A → A) where

  wd : ℕ → ℕ
  wd i = M.nth 0 i (T .widths)

  edge : ℕ → ℕ → Maybe M.Table
  edge i j = M.nth nothing j (M.nth [] i (T .edges))

  add? : ℕ → ℕ → Maybe M.Table → Maybe M.Table → Maybe M.Table
  add? r c nothing  u        = u
  add? r c t        nothing  = t
  add? r c (just t) (just u) = just (add-table r c t u)

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

  -- The hidden vertices are given by number, not position; one not in the graph is ignored. Each
  -- surviving row threads one summary list through its slots, so a row's summaries are forced at
  -- most once however many slots are read. The zero test visits every entry rather than
  -- short-circuiting, so a stored table is fully evaluated and holds no thunks over the input
  -- graph.
  module HideGraph (ε-dec : (x : Semiring.Carrier) → Dec (x ≡ Semiring.ε)) (hid : List ℕ) where
    hid-pos survivors : List ℕ
    hid-pos   = mapMaybe (position T) hid
    survivors = filterᵇ (λ p → not (any (p ≡ᵇ_) hid-pos)) (upTo (length (T .widths)))

    or! : Bool → Bool → Bool
    or! false b     = b
    or! true  false = true
    or! true  true  = true

    nonzero-row : List Semiring.Carrier → Bool
    nonzero-row []       = false
    nonzero-row (x ∷ xs) = or! (not ⌊ ε-dec x ⌋) (nonzero-row xs)

    nonzero-table : M.Table → Bool
    nonzero-table []       = false
    nonzero-table (r ∷ rs) = or! (nonzero-row r) (nonzero-table rs)

    keep : Maybe M.Table → Maybe M.Table
    keep nothing  = nothing
    keep (just t) = if nonzero-table t then just t else nothing

    row-slots : ℕ → List (ℕ × M.Table) → List (Maybe M.Table)
    row-slots a acc = map (λ b → keep (through a b acc)) survivors

    row : ℕ → List (Maybe M.Table)
    row a = row-slots a (summaries 0 a [] hid-pos)

    result : Tabulation
    result .Tabulation.numbers = map (λ p → M.nth 0 p (Tabulation.numbers T)) survivors
    result .Tabulation.widths  = map wd survivors
    result .Tabulation.edges   = map row survivors

  hide-graph : ((x : Semiring.Carrier) → Dec (x ≡ Semiring.ε)) → List ℕ → Tabulation
  hide-graph ε-dec hid = HideGraph.result ε-dec hid

-- Hiding with edge labels applied as functions to the row blocks propagated from the region's
-- sources; tables are assembled only for stored summaries and emitted columns. Hidden vertices
-- are given by position.
module FunctionHide {m : ℕ} {D : Derivation} (𝒢 : Graph m D)
  (ε-dec : (x : Semiring.Carrier) → Dec (x ≡ Semiring.ε))
  (tick : {A : Set} → String → A → A) (hid : List ℕ) where

  private
    total-positions : ℕ
    total-positions = suc (suc (vertex-count D))

    visible : List ℕ
    visible = filterᵇ (λ p → not (any (p ≡ᵇ_) hid)) (upTo total-positions)

    -- Nonzero in-edges only, keyed by the source's index among the visible vertices, in order.
    InEdges : Set
    InEdges = List (ℕ × M.Table)

    data Origin : Set where
      source  : ℕ → Origin
      summary : InEdges → Origin

    or-strict : Bool → Bool → Bool
    or-strict false b     = b
    or-strict true  false = true
    or-strict true  true  = true

    nonzero-row : List Semiring.Carrier → Bool
    nonzero-row []       = false
    nonzero-row (x ∷ xs) = or-strict (not ⌊ ε-dec x ⌋) (nonzero-row xs)

    nonzero-table : M.Table → Bool
    nonzero-table []       = false
    nonzero-table (r ∷ rs) = or-strict (nonzero-row r) (nonzero-table rs)

    drop-zeros : InEdges → InEdges
    drop-zeros []             = []
    drop-zeros ((i , t) ∷ es) = if nonzero-table t then (i , t) ∷ drop-zeros es else drop-zeros es

    force-in-edges : {A : Set} → InEdges → A → A
    force-in-edges []            x = x
    force-in-edges ((_ , _) ∷ B) x = force-in-edges B x

    scale-row : Semiring.Carrier → List Semiring.Carrier → List Semiring.Carrier
    scale-row D = map (D Semiring.·_)

    add-rows : List Semiring.Carrier → List Semiring.Carrier → List Semiring.Carrier
    add-rows []       ys       = ys
    add-rows xs       []       = xs
    add-rows (x ∷ xs) (y ∷ ys) = (x Semiring.+ y) ∷ add-rows xs ys

    weighted-rows : List Semiring.Carrier → List (List Semiring.Carrier) → List Semiring.Carrier
    weighted-rows []       _        = []
    weighted-rows _        []       = []
    weighted-rows (w ∷ ws) (r ∷ rs) = add-rows (scale-row w r) (weighted-rows ws rs)

    first-row : List (List Semiring.Carrier) → List Semiring.Carrier
    first-row []      = []
    first-row (r ∷ _) = r

    -- Product by traversal: rows of the left table weight and sum the rows of the right.
    table-product : M.Table → M.Table → M.Table
    table-product W T =
      tick ("cells-product " ++ₛ ℕ-Show.show (length W * length T * length (first-row T)))
           (map (λ wr → weighted-rows wr T) W)

    table-sum : M.Table → M.Table → M.Table
    table-sum []       us       = us
    table-sum ts       []       = ts
    table-sum (t ∷ ts) (u ∷ us) = add-rows t u ∷ table-sum ts us

    add-in-edges : InEdges → InEdges → InEdges
    add-in-edges []            C = C
    add-in-edges ((i , t) ∷ B) C = merge-one i t B C
      where
      merge-one : ℕ → M.Table → InEdges → InEdges → InEdges
      merge-one i t B []             = (i , t) ∷ B
      merge-one i t B ((j , u) ∷ C) with i ≡ᵇ j | i <ᵇ j
      ... | true  | _     = (i , table-sum t u) ∷ add-in-edges B C
      ... | false | true  = (i , t) ∷ add-in-edges B ((j , u) ∷ C)
      ... | false | false = (j , u) ∷ merge-one i t B C

    drop-first-column : List (List Semiring.Carrier) → List (List Semiring.Carrier)
    drop-first-column = map (λ { [] → [] ; (_ ∷ r) → r })

    first-column : List (List Semiring.Carrier) → List Semiring.Carrier
    first-column = map (λ { [] → Semiring.ε ; (x ∷ _) → x })

    transpose-to : ℕ → List (List Semiring.Carrier) → List (List Semiring.Carrier)
    transpose-to zero    _  = []
    transpose-to (suc n) rs = first-column rs ∷ transpose-to n (drop-first-column rs)

    -- Label applied to a block entry, one function application per column.
    label-on-table : ∀ {a b : ℕ} → 𝔽 a ⇒ 𝔽 b → M.Table → M.Table
    label-on-table {a} {b} ℓ T =
      tick ("cells-label " ++ₛ ℕ-Show.show (length (first-row T) * (a * b + a + b)))
           (transpose-to b (map app-col (transpose-to (length (first-row T)) T)))
      where
      app-col : List Semiring.Carrier → List Semiring.Carrier
      app-col cl = toList (tabulate (ℓ .func (λ i → M.nth Semiring.ε (toℕ i) cl)))

    basis-table : ℕ → M.Table
    basis-table w =
      applyUpTo (λ i → applyUpTo (λ j → if i ≡ᵇ j then Semiring.ι else Semiring.ε) w) w

    keep-in-edge : ℕ → M.Table → InEdges → InEdges
    keep-in-edge i t es = if nonzero-table t then (i , t) ∷ es else tick "dead" es

    apply-table : M.Table → InEdges → InEdges
    apply-table W []             = []
    apply-table W ((i , t) ∷ es) = keep-in-edge i (tick "apply" (table-product W t)) (apply-table W es)

    apply-label : ∀ {a b : ℕ} → 𝔽 a ⇒ 𝔽 b → InEdges → InEdges
    apply-label ℓ []             = []
    apply-label ℓ ((i , t) ∷ es) = keep-in-edge i (tick "apply" (label-on-table ℓ t)) (apply-label ℓ es)

    no-in-edges : InEdges
    no-in-edges = []

    unit-at : ℕ → M.Table → InEdges
    unit-at r t = (r , t) ∷ []

    expand : List ℕ → InEdges → List (Maybe M.Table)
    expand sv es = walk 0 sv es
      where
      walk : ℕ → List ℕ → InEdges → List (Maybe M.Table)
      walk i []       _              = []
      walk i (_ ∷ Ds) []             = nothing ∷ walk (suc i) Ds []
      walk i (_ ∷ Ds) ((j , t) ∷ es) =
        if i ≡ᵇ j then just t ∷ walk (suc i) Ds es else nothing ∷ walk (suc i) Ds ((j , t) ∷ es)

    set-at : ℕ → Origin → List Origin → List Origin
    set-at _       _ []        = []
    set-at zero    o (_ ∷ os)  = o ∷ os
    set-at (suc p) o (o' ∷ os) = o' ∷ set-at p o os

    origin-at : ℕ → List Origin → Origin
    origin-at _       []       = summary []
    origin-at zero    (o ∷ _)  = o
    origin-at (suc p) (_ ∷ os) = origin-at p os

    from-origin : M.Table → Origin → InEdges
    from-origin W (source r)  = unit-at r W
    from-origin W (summary B) = apply-table W B

    from-roots : List (Path D × M.Table) → List Origin → InEdges
    from-roots []             st = no-in-edges
    from-roots ((r , W) ∷ fs) st =
      add-in-edges
        (from-origin (tick "root-to-input" W)
                     (tick ("state " ++ₛ ℕ-Show.show (suc (path-position D r)))
                           (origin-at (suc (path-position D r)) st)))
        (from-roots fs st)

    to-conclusion : Path D → Path D → Origin → InEdges
    to-conclusion rp vp (source r) =
      unit-at r (tick "apply" (label-on-table (Graph.interior 𝒢 rp vp) (basis-table (width-at D rp))))
    to-conclusion rp vp (summary B) = apply-label (Graph.interior 𝒢 rp vp) B

    record Out (X : Set) : Set where
      constructor out
      field
        oacc : X
        org  : Origin
        opos : ℕ
        ok   : ℕ
        ost  : List Origin

    record Res (X : Set) : Set where
      constructor res
      field
        racc : X
        rups : InEdges
        rpos : ℕ
        rk   : ℕ
        rst  : List Origin

    go-node : {X : Set} → (X → InEdges → X) → (D' : Derivation) → (Path D' → Path D) →
              ℕ → ℕ → List Origin → InEdges → X → Out X
    go-prems : {X : Set} → (X → InEdges → X) → (Ds : List Derivation) →
               (∀ {Dᵢ} → Ds ∋ Dᵢ → Path Dᵢ → Path D) → Path D →
               ℕ → ℕ → List Origin → InEdges → X → Res X
    go-node consume (node m' n' b' Ds) emb pos k st A acc =
      emit (go-prems consume Ds (λ i p → emb (into i p)) (emb ε) pos k st A acc)
      where
      emit : Res _ → Out _
      emit (res acc' ups vpos k' st') =
        decide (add-in-edges (apply-table (tick "to-output" (Graph.input-to-output 𝒢 (emb ε))) A)
                             ups)
        where
        decide : InEdges → Out _
        decide B with any (vpos ≡ᵇ_) hid
        ... | true  = store (tick ("block " ++ₛ ℕ-Show.show vpos) (drop-zeros B))
          where
          store : InEdges → Out _
          store Bk =
            force-in-edges Bk
              (out acc' (summary Bk) (suc vpos) k'
                   (tick ("state " ++ₛ ℕ-Show.show vpos) (set-at vpos (summary Bk) st')))
        ... | false = give (tick ("column " ++ₛ ℕ-Show.show vpos) (drop-zeros B))
          where
          give : InEdges → Out _
          give Ck =
            primForce (consume acc' Ck)
              (λ a → out a (source k') (suc vpos) (suc k')
                         (tick ("state " ++ₛ ℕ-Show.show vpos) (set-at vpos (source k') st')))
    go-prems consume []          emb vp pos k st A acc = res acc no-in-edges pos k st
    go-prems consume (Dᵢ ∷ rest) emb vp pos k st A acc = enter (emb here ε)
      where
      enter : Path D → Res _
      enter rp =
        step (go-node consume Dᵢ (λ p → emb here p) pos k st
                (add-in-edges (apply-table (tick "to-input" (Graph.parent-to-input 𝒢 rp)) A)
                              (from-roots (Graph.roots-to-input 𝒢 rp) st))
                acc)
        where
        step : Out _ → Res _
        step (out acc' org pos' k' st') =
          pack (to-conclusion rp vp org)
               (go-prems consume rest (λ i p → emb (there i) p) vp pos' k' st' A acc')
          where
          pack : InEdges → Res _ → Res _
          pack up (res acc₂ ups pos₂ k₂ st₂) =
            res acc₂ (add-in-edges up ups) pos₂ k₂ st₂

  -- Visible vertices in evaluation order.
  fold-result : {X : Set} → (X → List (ℕ × M.Table) → X) → X → X
  fold-result {X} consume x₀ =
    Out.oacc (go-node consume D (λ p → p) 1 1
                (set-at 0 (source 0) (applyUpTo (λ _ → summary []) total-positions))
                (unit-at 0 (basis-table m))
                (primForce (consume x₀ (tick "column 0" no-in-edges)) (λ a → a)))

  result : List (List (Maybe M.Table))
  result = start visible
    where
    start : List ℕ → List (List (Maybe M.Table))
    start sv = reverse (fold-result (λ acc c → expand sv c ∷ acc) [])

hide-graph-functional : {m : ℕ} {D : Derivation} (𝒢 : Graph m D) →
                        ((x : Semiring.Carrier) → Dec (x ≡ Semiring.ε)) →
                        ({A : Set} → String → A → A) → List ℕ → List (List (Maybe M.Table))
hide-graph-functional 𝒢 ε-dec tick hid = FunctionHide.result 𝒢 ε-dec tick hid

hide-graph-fold : {m : ℕ} {D : Derivation} (𝒢 : Graph m D) →
                  ((x : Semiring.Carrier) → Dec (x ≡ Semiring.ε)) →
                  ({A : Set} → String → A → A) → List ℕ →
                  {X : Set} → (X → List (ℕ × M.Table) → X) → X → X
hide-graph-fold 𝒢 ε-dec tick hid = FunctionHide.fold-result 𝒢 ε-dec tick hid

private
  nth? : {C : Set} → ℕ → List C → Maybe C
  nth? _       []       = nothing
  nth? zero    (x ∷ _)  = just x
  nth? (suc n) (_ ∷ xs) = nth? n xs

  nth?-map : {C C' : Set} (f : C → C') (p : ℕ) (xs : List C) {x : C} →
             nth? p xs ≡ just x → nth? p (map f xs) ≡ just (f x)
  nth?-map f zero    (_ ∷ _)  ≡-refl = ≡-refl
  nth?-map f (suc p) (_ ∷ xs) h      = nth?-map f p xs h

  nth?-nth : {C : Set} (d : C) (p : ℕ) (xs : List C) {x : C} →
             nth? p xs ≡ just x → M.nth d p xs ≡ x
  nth?-nth d zero    (_ ∷ _)  ≡-refl = ≡-refl
  nth?-nth d (suc p) (_ ∷ xs) h      = nth?-nth d p xs h

  nth?-∈ : {C : Set} {p : ℕ} {xs : List C} {x : C} → nth? p xs ≡ just x → x ∈ xs
  nth?-∈ {p = zero}  {_ ∷ _} ≡-refl = here ≡-refl
  nth?-∈ {p = suc p} {_ ∷ _} h      = there (nth?-∈ {p = p} h)

  ∈-nth? : {C : Set} {x : C} {xs : List C} → x ∈ xs → Σ ℕ (λ p → nth? p xs ≡ just x)
  ∈-nth? (here ≡-refl) = 0 , ≡-refl
  ∈-nth? (there h) with ∈-nth? h
  ... | (p , e) = suc p , e

  nth-All : {C : Set} {P : C → Set} (d : C) (n : ℕ) {xs : List C} → P d → All P xs → P (M.nth d n xs)
  nth-All d n       pd []        = pd
  nth-All d zero    pd (px ∷ _)  = px
  nth-All d (suc n) pd (_ ∷ ps)  = nth-All d n pd ps

  ≡ᵇ-refl : (n : ℕ) → (n ≡ᵇ n) ≡ true
  ≡ᵇ-refl zero    = ≡-refl
  ≡ᵇ-refl (suc n) = ≡ᵇ-refl n

  ≡ᵇ-false : (i j : ℕ) → i ≢ j → (i ≡ᵇ j) ≡ false
  ≡ᵇ-false zero    zero    ne = ⊥-elim (ne ≡-refl)
  ≡ᵇ-false zero    (suc j) ne = ≡-refl
  ≡ᵇ-false (suc i) zero    ne = ≡-refl
  ≡ᵇ-false (suc i) (suc j) ne = ≡ᵇ-false i j (λ e → ne (≡-cong suc e))

  find-hit : (i k : ℕ) {p : ℕ} (js : List ℕ) → AllPairs _≢_ js → nth? p js ≡ just i →
             find-number i k js ≡ just (k + p)
  find-hit i k {zero}  (_ ∷ js) _         ≡-refl rewrite ≡ᵇ-refl i = ≡-cong just (≡-sym (+-identityʳ k))
  find-hit i k {suc p} (j ∷ js) (hj ∷ ps) h
    rewrite ≡ᵇ-false i j (λ e → All-lookup hj (nth?-∈ {p = p} h) (≡-sym e)) =
    ≡-trans (find-hit i (suc k) {p} js ps h) (≡-cong just (≡-sym (+-suc k p)))

  applyUpTo-≡ : {C : Set} (f g : ℕ → C) (n : ℕ) → ((i : ℕ) → f i ≡ g i) →
                applyUpTo f n ≡ applyUpTo g n
  applyUpTo-≡ f g zero    e = ≡-refl
  applyUpTo-≡ f g (suc n) e =
    ≡-cong₂ _∷_ (e 0) (applyUpTo-≡ (λ i → f (suc i)) (λ i → g (suc i)) n (λ i → e (suc i)))

  map-≡ : {C C' : Set} {f g : C → C'} {xs : List C} → All (λ x → f x ≡ g x) xs → map f xs ≡ map g xs
  map-≡ []       = ≡-refl
  map-≡ (e ∷ es) = ≡-cong₂ _∷_ e (map-≡ es)

  true≢false : true ≡ false → ⊥
  true≢false ()

  ∨-false : {a b : Bool} → (a ∨ b) ≡ false → (a ≡ false) × (b ≡ false)
  ∨-false {false} e = ≡-refl , e
  ∨-false {true}  e = ⊥-elim (true≢false e)

  any-false : {C : Set} (f : C → Bool) (xs : List C) → any f xs ≡ false →
              All (λ x → f x ≡ false) xs
  any-false f []       _ = []
  any-false f (x ∷ xs) e with ∨-false {f x} e
  ... | (e₁ , e₂) = e₁ ∷ any-false f xs e₂

  dec-just : {P : Set} (d : Dec P) → ⌊ d ⌋ ≡ true → P
  dec-just (yes p) _  = p
  dec-just (no _)  ()

  not-false : {b : Bool} → not b ≡ false → b ≡ true
  not-false {true}  _  = ≡-refl
  not-false {false} ()

  nth-tabulate : {C : Set} (d : C) {k : ℕ} (f : Fin k → C) (i : Fin k) →
                 M.nth d (toℕ i) (toList (tabulate f)) ≡ f i
  nth-tabulate d f zero    = ≡-refl
  nth-tabulate d f (suc i) = nth-tabulate d (λ k → f (suc k)) i

  look-to-table : ∀ {r c} (R : M.Matrix r c) (i : Fin r) (j : Fin c) →
                  M.look (M.to-table R) i j ≡ R i j
  look-to-table R i j =
    ≡-trans (≡-cong (M.nth Semiring.ε (toℕ j)) (nth-tabulate [] _ i)) (nth-tabulate Semiring.ε _ j)

  nth-applyUpTo : {C : Set} (d : C) (g : ℕ → C) {r : ℕ} (h : ℕ → ℕ) (i : Fin r) →
                  M.nth d (toℕ i) (map g (applyUpTo h r)) ≡ g (h (toℕ i))
  nth-applyUpTo d g h zero    = ≡-refl
  nth-applyUpTo d g h (suc i) = nth-applyUpTo d g (λ k → h (suc k)) i

  just-inj : {C : Set} {u v : C} → just u ≡ just v → u ≡ v
  just-inj ≡-refl = ≡-refl

  nth?-defined : {C : Set} (p : ℕ) (xs : List C) → p < length xs → Σ C (λ z → nth? p xs ≡ just z)
  nth?-defined zero    (x ∷ _)  _        = x , ≡-refl
  nth?-defined (suc p) (_ ∷ xs) (s≤s lt) = nth?-defined p xs lt

  nth?-length : {C : Set} (p : ℕ) (xs : List C) {x : C} → nth? p xs ≡ just x → p < length xs
  nth?-length zero    (_ ∷ _)  _  = s≤s z≤n
  nth?-length (suc p) (_ ∷ xs) h  = s≤s (nth?-length p xs h)
  nth?-length zero    []       ()
  nth?-length (suc p) []       ()

  applyUpTo-All : (h : ℕ → ℕ) (n : ℕ) {P : ℕ → Set} →
                  ((p : ℕ) → p < n → P (h p)) → All P (applyUpTo h n)
  applyUpTo-All h zero    f = []
  applyUpTo-All h (suc n) f =
    f 0 (s≤s z≤n) ∷ applyUpTo-All (λ i → h (suc i)) n (λ p lt → f (suc p) (s≤s lt))

  <-applyUpTo : (h : ℕ → ℕ) {p n : ℕ} → p < n → h p ∈ applyUpTo h n
  <-applyUpTo h {zero}  {suc n} _        = here ≡-refl
  <-applyUpTo h {suc p} {suc n} (s≤s lt) = there (<-applyUpTo (λ i → h (suc i)) {p} lt)

  filterᵇ-All : {C : Set} {P : C → Set} (f : C → Bool) {xs : List C} →
                All P xs → All P (filterᵇ f xs)
  filterᵇ-All f {[]}     []        = []
  filterᵇ-All f {x ∷ xs} (px ∷ ps) with f x
  ... | true  = px ∷ filterᵇ-All f ps
  ... | false = filterᵇ-All f ps

  filterᵇ-AllPairs : {C : Set} {P : C → C → Set} (f : C → Bool) {xs : List C} →
                     AllPairs P xs → AllPairs P (filterᵇ f xs)
  filterᵇ-AllPairs f {[]}     []        = []
  filterᵇ-AllPairs f {x ∷ xs} (hx ∷ ps) with f x
  ... | true  = filterᵇ-All f hx ∷ filterᵇ-AllPairs f ps
  ... | false = filterᵇ-AllPairs f ps

  all-any-false : {C : Set} (f : C → Bool) (xs : List C) → All (λ x → f x ≡ false) xs →
                  any f xs ≡ false
  all-any-false f []       []        = ≡-refl
  all-any-false f (x ∷ xs) (e ∷ es) rewrite e = all-any-false f xs es

  ∈-filterᵇ : {C : Set} (f : C → Bool) {x : C} {xs : List C} → x ∈ xs → f x ≡ true →
              x ∈ filterᵇ f xs
  ∈-filterᵇ f (here ≡-refl) e rewrite e = here ≡-refl
  ∈-filterᵇ f {xs = y ∷ xs} (there m) e with f y
  ... | true  = there (∈-filterᵇ f m e)
  ... | false = ∈-filterᵇ f m e

  ∈-mapMaybe : {C C' : Set} {f : C → Maybe C'} {x : C'} {qs : List C} {q : C} →
               q ∈ qs → f q ≡ just x → x ∈ mapMaybe f qs
  ∈-mapMaybe (here ≡-refl) e rewrite e = here ≡-refl
  ∈-mapMaybe {f = f} {qs = q' ∷ qs} (there m) e with f q'
  ... | just z  = there (∈-mapMaybe m e)
  ... | nothing = ∈-mapMaybe m e

  nth?-applyUpTo : (h : ℕ → ℕ) {p n : ℕ} → p < n → nth? p (applyUpTo h n) ≡ just (h p)
  nth?-applyUpTo h {zero}  {suc n} _        = ≡-refl
  nth?-applyUpTo h {suc p} {suc n} (s≤s lt) = nth?-applyUpTo (λ i → h (suc i)) {p} lt

  if-nothing : (c : Bool) {w : Maybe M.Table} → w ≡ nothing →
               (if c then w else nothing) ≡ nothing
  if-nothing false e = ≡-refl
  if-nothing true  e = e

  mask-col : (member : ℕ → Bool) (keep : Bool) (ms : List ℕ) (ts : List (Maybe M.Table))
             (b : ℕ) {nb : ℕ} → nth? b ms ≡ just nb →
             M.nth nothing b (mask-slots member keep ms ts)
             ≡ (if keep ∨ member nb then M.nth nothing b ts else nothing)
  mask-col member keep []       ts       b       ()
  mask-col member keep (m ∷ ms) []       b  {nb} hb = ≡-sym (if-nothing (keep ∨ member nb) ≡-refl)
  mask-col member keep (m ∷ ms) (t ∷ ts) zero    ≡-refl = ≡-refl
  mask-col member keep (m ∷ ms) (t ∷ ts) (suc b) hb = mask-col member keep ms ts b hb

  mask-row : (member : ℕ → Bool) (all-ns ns : List ℕ) (rs : List (List (Maybe M.Table)))
             (a : ℕ) {na : ℕ} → nth? a ns ≡ just na →
             M.nth [] a (mask-rows member all-ns ns rs)
             ≡ mask-slots member (member na) all-ns (M.nth [] a rs)
  mask-row member all-ns []       rs       a       ()
  mask-row member all-ns (n ∷ ns) []       a       ha = ≡-refl
  mask-row member all-ns (n ∷ ns) (r ∷ rs) zero    ≡-refl = ≡-refl
  mask-row member all-ns (n ∷ ns) (r ∷ rs) (suc a) ha = mask-row member all-ns ns rs a ha

look-add : ∀ {r c} (t u : M.Table) (i : Fin r) (j : Fin c) →
           M.look (add-table r c t u) i j ≡ (M.look t i j Semiring.+ M.look u i j)
look-add t u i j =
  ≡-trans (≡-cong (M.nth Semiring.ε (toℕ j)) (nth-applyUpTo [] _ (λ k → k) i))
          (nth-applyUpTo Semiring.ε _ (λ k → k) j)

-- A tabulation represents a graph at a vertex list when its numbers and widths read off that list
-- and every slot's morphism is the graph's edge.
module _ {m : ℕ} {D : Derivation} (𝒢 : Graph m D) where

  private
    ≈-of-≡ : ∀ {x y : Semiring.Carrier} → x ≡ y → x Semiring.≈ y
    ≈-of-≡ ≡-refl = Semiring.refl

  zero-table-morphism : (x y : V 𝒢) (r c : ℕ) →
                        mat (M.look {vertex-width 𝒢 y} {vertex-width 𝒢 x} (zero-table r c)) ≈ εₘ
  zero-table-morphism x y r c =
    ≈-trans (mat-cong (λ i j → ≈-of-≡ (entry i j))) mat-ε
    where
    entry : (i : Fin (vertex-width 𝒢 y)) (j : Fin (vertex-width 𝒢 x)) →
            M.look (zero-table r c) i j ≡ Semiring.ε
    entry i j =
      nth-All {P = λ row → M.nth Semiring.ε (toℕ j) row ≡ Semiring.ε} [] (toℕ i) ≡-refl
              (AllP.map⁺ (universal (λ _ →
                 nth-All {P = λ e → e ≡ Semiring.ε} Semiring.ε (toℕ j) ≡-refl
                         (AllP.map⁺ (universal (λ _ → ≡-refl) (upTo c))))
                 (upTo r)))

  read-table-rep : (T : Tabulation) (x y : V 𝒢) (p q : ℕ) →
                   mat (M.look {vertex-width 𝒢 y} {vertex-width 𝒢 x} (read-table T p q))
                   ≈ table-morphism 𝒢 x y (table-at T p q)
  read-table-rep T x y p q with table-at T p q
  ... | just t  = ≈-refl
  ... | nothing =
    zero-table-morphism x y (M.nth 0 q (Tabulation.widths T)) (M.nth 0 p (Tabulation.widths T))

  record Represents (T : Tabulation) (vs : List (V 𝒢)) (G : EdgeLabels (vertex-object 𝒢)) : Set where
    field
      numbers-eq       : Tabulation.numbers T ≡ map (index-of 𝒢) vs
      widths-eq        : T .widths ≡ map (vertex-width 𝒢) vs
      numbers-distinct : AllPairs _≢_ (Tabulation.numbers T)
      slots            : ∀ {a b : ℕ} {x y : V 𝒢} → nth? a vs ≡ just x → nth? b vs ≡ just y →
                         Prf (table-morphism 𝒢 x y (table-at T a b) ≈ G x y)

  open Represents public

  locate : {T : Tabulation} {vs : List (V 𝒢)} {G : EdgeLabels (vertex-object 𝒢)} →
           Represents T vs G → {p : ℕ} {x : V 𝒢} → nth? p vs ≡ just x →
           position T (index-of 𝒢 x) ≡ just p
  locate {T} {vs} R {p} {x} h =
    subst (λ ns → find-number (index-of 𝒢 x) 0 ns ≡ just p) (≡-sym (R .numbers-eq))
          (find-hit (index-of 𝒢 x) 0 {p} (map (index-of 𝒢) vs)
                    (subst (AllPairs _≢_) (R .numbers-eq) (R .numbers-distinct))
                    (nth?-map (index-of 𝒢) p vs h))

  read-edge-rep : {T : Tabulation} {vs : List (V 𝒢)} {G : EdgeLabels (vertex-object 𝒢)} →
                  Represents T vs G → {x y : V 𝒢} → x ∈ vs → y ∈ vs →
                  read-edge 𝒢 T x y ≈ G x y
  read-edge-rep {T} {vs} {G} R {x} {y} mx my with ∈-nth? mx | ∈-nth? my
  ... | (p , hp) | (q , hq) =
    ≈-trans (≡-to-≈ (≡-cong₂ (λ u v → read-slot 𝒢 T x y u v) (locate R hp) (locate R hq)))
            (Prf.prf (R .slots hp hq))

  private
    eqv : DecidableEquality (V 𝒢)
    eqv = SumP.≡-dec input-≟ (_≟_ {D})

    ⌊⌋-refl : (x : V 𝒢) → ⌊ eqv x x ⌋ ≡ true
    ⌊⌋-refl x with eqv x x
    ... | yes _  = ≡-refl
    ... | no  ne = ⊥-elim (ne ≡-refl)

    ⌊⌋-false : {x y : V 𝒢} → x ≢ y → ⌊ eqv x y ⌋ ≡ false
    ⌊⌋-false {x} {y} ne with eqv x y
    ... | yes e = ⊥-elim (ne e)
    ... | no  _ = ≡-refl

    all-distinct : AllPairs _≢_ (all-vertices 𝒢)
    all-distinct = head-≢ ∷ tail-distinct
      where
      head-≢ : All (inj₁ input ≢_) (map inj₂ (vertices D) ++ (inj₂ ε ∷ []))
      head-≢ = AllP.++⁺ (AllP.map⁺ (universal (λ _ ()) (vertices D))) ((λ ()) ∷ [])

      tail-distinct : AllPairs _≢_ (map inj₂ (vertices D) ++ (inj₂ ε ∷ []))
      tail-distinct =
        subst (AllPairs _≢_) (map-++ inj₂ (vertices D) (ε ∷ []))
              (AllPairsP.map⁺ (AllPairs-map (λ h e → h (SumP.inj₂-injective e)) (distinct-one D)))

    find-self : (xs : List (V 𝒢)) → AllPairs _≢_ xs → (k : ℕ) →
                map (λ x → find-vertex 𝒢 x k xs) xs ≡ applyUpTo (λ i → k + i) (length xs)
    find-self []       []        k = ≡-refl
    find-self (x ∷ xs) (hx ∷ ps) k =
      ≡-cong₂ _∷_ head-eq
        (≡-trans (map-≡ (All-map skip hx))
        (≡-trans (find-self xs ps (suc k))
                 (applyUpTo-≡ (λ i → suc k + i) (λ i → k + suc i) (length xs)
                              (λ i → ≡-sym (+-suc k i)))))
      where
      head-eq : find-vertex 𝒢 x k (x ∷ xs) ≡ k + 0
      head-eq = ≡-trans (≡-cong (λ b → if b then k else find-vertex 𝒢 x (suc k) xs) (⌊⌋-refl x))
                        (≡-sym (+-identityʳ k))

      skip : ∀ {y} → x ≢ y → find-vertex 𝒢 y k (x ∷ xs) ≡ find-vertex 𝒢 y (suc k) xs
      skip {y} ne =
        ≡-cong (λ b → if b then k else find-vertex 𝒢 y (suc k) xs) (⌊⌋-false (λ e → ne (≡-sym e)))

    numbers-self : upTo (length (all-vertices 𝒢)) ≡ map (index-of 𝒢) (all-vertices 𝒢)
    numbers-self = ≡-sym (find-self (all-vertices 𝒢) all-distinct 0)

    upTo-distinct : (n : ℕ) → AllPairs _≢_ (upTo n)
    upTo-distinct n = AllPairsP.applyUpTo⁺₁ _ n (λ i<j _ → <⇒≢ i<j)

  tabulation-rep : (ε-dec : (x : Semiring.Carrier) → Dec (x ≡ Semiring.ε)) →
                   Represents (tabulation 𝒢 ε-dec (λ _ x → x)) (all-vertices 𝒢) (edge-labels 𝒢)
  tabulation-rep ε-dec .numbers-eq       = numbers-self
  tabulation-rep ε-dec .widths-eq        = ≡-refl
  tabulation-rep ε-dec .numbers-distinct = upTo-distinct (length (all-vertices 𝒢))
  tabulation-rep ε-dec .slots {a} {b} {x} {y} ha hb =
    subst (λ w → Prf (table-morphism 𝒢 x y w ≈ edge-labels 𝒢 x y)) (≡-sym table-eq) at-slot
    where
    idt : {C : Set} → String → C → C
    idt _ c = c

    R = ∃ₛ.fst (𝔽F-full (edge-labels 𝒢 x y))

    table-eq : table-at (tabulation 𝒢 ε-dec idt) a b
               ≡ edge-slot 𝒢 ε-dec idt (edge-table 𝒢 ε-dec idt x y)
    table-eq =
      ≡-trans (≡-cong (M.nth nothing b)
                      (nth?-nth [] a (map (edge-row 𝒢 ε-dec idt) (all-vertices 𝒢))
                                (nth?-map (edge-row 𝒢 ε-dec idt) a (all-vertices 𝒢) ha)))
              (nth?-nth nothing b
                        (map (λ y' → edge-slot 𝒢 ε-dec idt (edge-table 𝒢 ε-dec idt x y'))
                             (all-vertices 𝒢))
                        (nth?-map (λ y' → edge-slot 𝒢 ε-dec idt (edge-table 𝒢 ε-dec idt x y'))
                                  b (all-vertices 𝒢) hb))

    at-slot : Prf (table-morphism 𝒢 x y (edge-slot 𝒢 ε-dec idt (edge-table 𝒢 ε-dec idt x y))
                   ≈ edge-labels 𝒢 x y)
    at-slot with nonzero-slot 𝒢 ε-dec idt (edge-table 𝒢 ε-dec idt x y) in nz
    ... | true  =
      ⟪ ≈-trans (mat-cong (λ i j → ≈-of-≡ (look-to-table R i j)))
                (∃ₛ.snd (𝔽F-full (edge-labels 𝒢 x y))) ⟫
    ... | false = ⟪ ≈-sym zero-case ⟫
      where
      all-ε : All (All (λ e → e ≡ Semiring.ε)) (M.to-table R)
      all-ε = All-map (λ rf → All-map (λ ef → dec-just (ε-dec _) (not-false ef)) (any-false _ _ rf))
                      (any-false _ (M.to-table R) nz)

      entry-ε : ∀ i j → R i j ≡ Semiring.ε
      entry-ε i j =
        ≡-trans (≡-sym (look-to-table R i j))
                (nth-All [] (toℕ i) ≡-refl
                         (All-map (λ rz → nth-All Semiring.ε (toℕ j) ≡-refl rz) all-ε))

      zero-case : edge-labels 𝒢 x y ≈ εₘ
      zero-case =
        ≈-trans (≈-sym (∃ₛ.snd (𝔽F-full (edge-labels 𝒢 x y))))
                (≈-trans (mat-cong (λ i j → ≈-of-≡ (entry-ε i j))) mat-ε)

  ∈-all-vertices : (v : V 𝒢) → v ∈ all-vertices 𝒢
  ∈-all-vertices (inj₁ input)      = here ≡-refl
  ∈-all-vertices (inj₂ ε)          = there (∈-++⁺ʳ (map inj₂ (vertices D)) (here ≡-refl))
  ∈-all-vertices (inj₂ (into i q)) = there (∈-++⁺ˡ (∈-map⁺ inj₂ (∈-vertices (into i q) (λ ()))))

  index-of-injective : {u v : V 𝒢} → index-of 𝒢 u ≡ index-of 𝒢 v → u ≡ v
  index-of-injective {u} {v} e with ∈-nth? (∈-all-vertices u) | ∈-nth? (∈-all-vertices v)
  ... | (pu , eu) | (pv , ev) =
    just-inj (≡-trans (≡-sym eu)
             (≡-trans (≡-cong (λ p → nth? p (all-vertices 𝒢)) same-pos) ev))
    where
    idx-at : {p : ℕ} {z : V 𝒢} → nth? p (all-vertices 𝒢) ≡ just z → index-of 𝒢 z ≡ p
    idx-at {p} {z} h =
      ≡-sym (just-inj
        (≡-trans (≡-sym (nth?-applyUpTo (λ i → i) (nth?-length p (all-vertices 𝒢) h)))
                 (subst (λ l → nth? p l ≡ just (index-of 𝒢 z)) (≡-sym numbers-self)
                        (nth?-map (index-of 𝒢) p (all-vertices 𝒢) h))))

    same-pos : pu ≡ pv
    same-pos = ≡-trans (≡-sym (idx-at eu)) (≡-trans e (idx-at ev))

  rep-cong : {T : Tabulation} {vs : List (V 𝒢)} {G G' : EdgeLabels (vertex-object 𝒢)} →
             ((x y : V 𝒢) → G x y ≈ G' x y) →
             Represents T vs G → Represents T vs G'
  rep-cong e R .numbers-eq       = R .numbers-eq
  rep-cong e R .widths-eq        = R .widths-eq
  rep-cong e R .numbers-distinct = R .numbers-distinct
  rep-cong e R .slots {a} {b} {x} {y} ha hb = ⟪ ≈-trans (Prf.prf (R .slots ha hb)) (e x y) ⟫

  -- The graph the restricted tabulation stores: an edge survives when either endpoint's number
  -- lies in the region.
  restrict-mask : List (V 𝒢) → EdgeLabels (vertex-object 𝒢) → EdgeLabels (vertex-object 𝒢)
  restrict-mask ws' G x y =
    if any (index-of 𝒢 x ≡ᵇ_) (map (index-of 𝒢) ws')
       ∨ any (index-of 𝒢 y ≡ᵇ_) (map (index-of 𝒢) ws')
    then G x y else εₘ

  restrict-rep : {T : Tabulation} {vs : List (V 𝒢)} {G : EdgeLabels (vertex-object 𝒢)} →
                 Represents T vs G → (ws' : List (V 𝒢)) →
                 Represents (restrict (map (index-of 𝒢) ws') T) vs (restrict-mask ws' G)
  restrict-rep R ws' .numbers-eq       = R .numbers-eq
  restrict-rep R ws' .widths-eq        = R .widths-eq
  restrict-rep R ws' .numbers-distinct = R .numbers-distinct
  restrict-rep {T} {vs} {G} R ws' .slots {a} {b} {x} {y} ha hb =
    subst (λ w → Prf (table-morphism 𝒢 x y w ≈ restrict-mask ws' G x y)) (≡-sym slot-eq) at-mask
    where
    member : ℕ → Bool
    member n = any (n ≡ᵇ_) (map (index-of 𝒢) ws')

    na-eq : nth? a (Tabulation.numbers T) ≡ just (index-of 𝒢 x)
    na-eq = subst (λ ns → nth? a ns ≡ just (index-of 𝒢 x)) (≡-sym (R .numbers-eq))
                  (nth?-map (index-of 𝒢) a vs ha)

    nb-eq : nth? b (Tabulation.numbers T) ≡ just (index-of 𝒢 y)
    nb-eq = subst (λ ns → nth? b ns ≡ just (index-of 𝒢 y)) (≡-sym (R .numbers-eq))
                  (nth?-map (index-of 𝒢) b vs hb)

    slot-eq : table-at (restrict (map (index-of 𝒢) ws') T) a b
              ≡ (if member (index-of 𝒢 x) ∨ member (index-of 𝒢 y)
                 then table-at T a b else nothing)
    slot-eq =
      ≡-trans (≡-cong (M.nth nothing b)
                      (mask-row member (Tabulation.numbers T) (Tabulation.numbers T)
                                (Tabulation.edges T) a na-eq))
              (mask-col member (member (index-of 𝒢 x)) (Tabulation.numbers T)
                        (M.nth [] a (Tabulation.edges T)) b nb-eq)

    at-mask : Prf (table-morphism 𝒢 x y
                     (if member (index-of 𝒢 x) ∨ member (index-of 𝒢 y)
                      then table-at T a b else nothing)
                   ≈ restrict-mask ws' G x y)
    at-mask with member (index-of 𝒢 x) ∨ member (index-of 𝒢 y)
    ... | true  = R .slots ha hb
    ... | false = ⟪ ≈-refl ⟫

  -- Hiding over a represented tabulation represents hiding in the graph: with the hidden vertices
  -- stored, listed without repeats, and carrying no backward edge among them, the result
  -- represents hide-all at the surviving vertices.
  module HideRepresents
      (ε-dec : (x : Semiring.Carrier) → Dec (x ≡ Semiring.ε))
      {T : Tabulation} {vs : List (V 𝒢)} {G : EdgeLabels (vertex-object 𝒢)}
      (R : Represents T vs G)
      (ws : List (V 𝒢)) (ws-mem : All (_∈ vs) ws)
      (pairs : AllPairs (λ v u → Prf (G u v ≈ εₘ)) ws) where

    private
      module TB = Tabulated T (λ _ c → c)
      module HG = TB.HideGraph ε-dec (map (index-of 𝒢) ws)
      module H𝒢 = Hide (V 𝒢) (vertex-object 𝒢)

    remaining : List (V 𝒢)
    remaining = mapMaybe (λ p → nth? p vs) HG.survivors

    private
      wd-at : {p : ℕ} {x : V 𝒢} → nth? p vs ≡ just x → TB.wd p ≡ vertex-width 𝒢 x
      wd-at {p} {x} h =
        ≡-trans (≡-cong (M.nth 0 p) (R .widths-eq))
                (nth?-nth 0 p (map (vertex-width 𝒢) vs) (nth?-map (vertex-width 𝒢) p vs h))

      num-at : {p : ℕ} {x : V 𝒢} → nth? p vs ≡ just x →
               M.nth 0 p (Tabulation.numbers T) ≡ index-of 𝒢 x
      num-at {p} {x} h =
        ≡-trans (≡-cong (M.nth 0 p) (R .numbers-eq))
                (nth?-nth 0 p (map (index-of 𝒢) vs) (nth?-map (index-of 𝒢) p vs h))

      nth?-num : {p : ℕ} {x : V 𝒢} → nth? p vs ≡ just x →
                 nth? p (Tabulation.numbers T) ≡ just (index-of 𝒢 x)
      nth?-num {p} {x} h =
        subst (λ ns → nth? p ns ≡ just (index-of 𝒢 x)) (≡-sym (R .numbers-eq))
              (nth?-map (index-of 𝒢) p vs h)

      len-eq : length (Tabulation.widths T) ≡ length vs
      len-eq = ≡-trans (≡-cong length (R .widths-eq)) (length-map (vertex-width 𝒢) vs)

      data PosOf : List ℕ → List (V 𝒢) → Set where
        []  : PosOf [] []
        _∷_ : ∀ {p w ps ws'} → nth? p vs ≡ just w → PosOf ps ws' → PosOf (p ∷ ps) (w ∷ ws')

      pos-of : (ws' : List (V 𝒢)) → All (_∈ vs) ws' →
               PosOf (mapMaybe (position T) (map (index-of 𝒢) ws')) ws'
      pos-of []        []         = []
      pos-of (w ∷ ws') (mw ∷ mws) with ∈-nth? mw
      ... | (p , e) rewrite locate R e = e ∷ pos-of ws' mws

      data Acc (x : V 𝒢) : List (ℕ × M.Table) → {us : List (V 𝒢)} → H𝒢.Tables x us → Set where
        nil  : Acc x [] []
        keep : ∀ {u : ℕ} {y : V 𝒢} {t : M.Table} {acc : List (ℕ × M.Table)} {us : List (V 𝒢)}
               {Ts : H𝒢.Tables x us} {S : vertex-object 𝒢 x ⇒ vertex-object 𝒢 y} →
               nth? u vs ≡ just y →
               Prf (mat (M.look {vertex-width 𝒢 y} {vertex-width 𝒢 x} t) ≈ S) →
               Acc x acc Ts → Acc x ((u , t) ∷ acc) (_∷_ {x = y} S Ts)
        skip : ∀ {y : V 𝒢} {acc : List (ℕ × M.Table)} {us : List (V 𝒢)}
               {Ts : H𝒢.Tables x us} {S : vertex-object 𝒢 x ⇒ vertex-object 𝒢 y} →
               Prf (S ≈ εₘ) → Acc x acc Ts → Acc x acc (_∷_ {x = y} S Ts)

      sum-Σ : (g : ℕ → Semiring.Carrier) {r : ℕ} (h : ℕ → ℕ) →
              sum (map g (applyUpTo h r)) ≡ M.Σ {r} (λ k → g (h (toℕ k)))
      sum-Σ g {zero}  h = ≡-refl
      sum-Σ g {suc r} h = ≡-cong (λ z → g (h 0) Semiring.+ z) (sum-Σ g {r} (λ k → h (suc k)))

      look-mul : ∀ {r D c} (t u : M.Table) (i : Fin r) (j : Fin c) →
                 M.look (mul r D c t u) i j ≡ M._∘_ (M.look {r} {D} t) (M.look {D} {c} u) i j
      look-mul {D = D} t u i j =
        ≡-trans (≡-cong (M.nth Semiring.ε (toℕ j)) (nth-applyUpTo [] _ (λ k → k) i))
                (≡-trans (nth-applyUpTo Semiring.ε _ (λ k → k) j)
                         (sum-Σ (λ k → M.nth Semiring.ε k (M.nth [] (toℕ i) t) Semiring.·
                                       M.nth Semiring.ε (toℕ j) (M.nth [] k u)) {D} (λ k → k)))

      through-rep : (pa pb : ℕ) {x y : V 𝒢} → nth? pa vs ≡ just x → nth? pb vs ≡ just y →
                    (acc : List (ℕ × M.Table)) {us : List (V 𝒢)} {Ts : H𝒢.Tables x us} →
                    Acc x acc Ts →
                    Prf (table-morphism 𝒢 x y (TB.through pa pb acc) ≈ H𝒢.through G x y Ts)
      through-rep pa pb ha hb _ nil = R .slots ha hb
      through-rep pa pb {x} {y} ha hb _ (keep {u} {y'} {t} {acc} {Ts = Ts} {S = S} hu ⟪ tr ⟫ K)
        with table-at T u pb | Prf.prf (R .slots hu hb)
      ... | nothing | z =
        ⟪ ≈-trans (Prf.prf (through-rep pa pb ha hb acc K))
                  (≈-sym (≈-trans (+ₘ-cong (≈-trans {g = εₘ {vertex-object 𝒢 y'} {vertex-object 𝒢 y} ∘ S}
                                                    (∘-cong₁ {f₁ = G y' y} {f₂ = εₘ} {g = S} (≈-sym z))
                                                    (CM.comp-bilinear-ε₁ {Z = vertex-object 𝒢 y} S))
                                           ≈-refl)
                                  (+ₘ-lunit (H𝒢.through G x y Ts)))) ⟫
      ... | just e  | z
        rewrite wd-at hb | wd-at hu | wd-at ha
        with TB.through pa pb acc | Prf.prf (through-rep pa pb ha hb acc K)
      ...   | nothing | ihz =
        ⟪ ≈-trans mul-rep
                  (≈-sym (≈-trans (+ₘ-cong ≈-refl (≈-sym ihz)) (+ₘ-runit (G y' y ∘ S)))) ⟫
        where
        mul-rep : mat (M.look {vertex-width 𝒢 y} {vertex-width 𝒢 x}
                       (mul (vertex-width 𝒢 y) (vertex-width 𝒢 y') (vertex-width 𝒢 x) e t))
                  ≈ (G y' y ∘ S)
        mul-rep =
          ≈-trans (mat-cong (λ i j → ≈-of-≡ (look-mul {D = vertex-width 𝒢 y'} e t i j)))
                  (≈-trans (mat-comp (M.look e) (M.look t)) (∘-cong z tr))
      ...   | just t' | ihe =
        ⟪ ≈-trans (mat-cong (λ i j → ≈-of-≡
                    (look-add (mul (vertex-width 𝒢 y) (vertex-width 𝒢 y') (vertex-width 𝒢 x) e t)
                              t' i j)))
          (≈-trans (mat-+ (M.look (mul (vertex-width 𝒢 y) (vertex-width 𝒢 y') (vertex-width 𝒢 x) e t))
                          (M.look t'))
                   (+ₘ-cong mul-rep ihe)) ⟫
        where
        mul-rep : mat (M.look {vertex-width 𝒢 y} {vertex-width 𝒢 x}
                       (mul (vertex-width 𝒢 y) (vertex-width 𝒢 y') (vertex-width 𝒢 x) e t))
                  ≈ (G y' y ∘ S)
        mul-rep =
          ≈-trans (mat-cong (λ i j → ≈-of-≡ (look-mul {D = vertex-width 𝒢 y'} e t i j)))
                  (≈-trans (mat-comp (M.look e) (M.look t)) (∘-cong z tr))
      through-rep pa pb {x} {y} ha hb acc (skip {y''} {Ts = Ts} {S = S} ⟪ sz ⟫ K) =
        ⟪ ≈-trans (Prf.prf (through-rep pa pb ha hb acc K))
                  (≈-sym (≈-trans (+ₘ-cong (≈-trans {g = G y'' y ∘ εₘ {vertex-object 𝒢 x} {vertex-object 𝒢 y''}}
                                                    (∘-cong₂ {f = G y'' y} sz)
                                                    (CM.comp-bilinear-ε₂ {X = vertex-object 𝒢 x} (G y'' y)))
                                           ≈-refl)
                                  (+ₘ-lunit (H𝒢.through G x y Ts)))) ⟫

      acc-nil : ∀ {x acc us} {Ts : H𝒢.Tables x us} → Acc x acc Ts → Acc x acc (AllP.++⁺ Ts [])
      acc-nil nil           = nil
      acc-nil (keep e r K)  = keep e r (acc-nil K)
      acc-nil (skip z K)    = skip z (acc-nil K)

      acc-snoc-keep : ∀ {x acc us} {Ts : H𝒢.Tables x us} {u : ℕ} {y : V 𝒢} {t : M.Table}
                      {S : vertex-object 𝒢 x ⇒ vertex-object 𝒢 y} →
                      Acc x acc Ts → nth? u vs ≡ just y →
                      Prf (mat (M.look {vertex-width 𝒢 y} {vertex-width 𝒢 x} t) ≈ S) →
                      Acc x (acc ++ (u , t) ∷ []) (AllP.++⁺ Ts (_∷_ {x = y} S []))
      acc-snoc-keep nil           e r = keep e r nil
      acc-snoc-keep (keep e' r' K) e r = keep e' r' (acc-snoc-keep K e r)
      acc-snoc-keep (skip z K)    e r = skip z (acc-snoc-keep K e r)

      acc-snoc-skip : ∀ {x acc us} {Ts : H𝒢.Tables x us} {y : V 𝒢}
                      {S : vertex-object 𝒢 x ⇒ vertex-object 𝒢 y} →
                      Acc x acc Ts → Prf (S ≈ εₘ) → Acc x acc (AllP.++⁺ Ts (_∷_ {x = y} S []))
      acc-snoc-skip nil           z = skip z nil
      acc-snoc-skip (keep e r K)  z = keep e r (acc-snoc-skip K z)
      acc-snoc-skip (skip z' K)   z = skip z' (acc-snoc-skip K z)

      acc-shift : ∀ {x acc us vs'} {Ts : H𝒢.Tables x us} {v : V 𝒢}
                  {S : vertex-object 𝒢 x ⇒ vertex-object 𝒢 v} {Us : H𝒢.Tables x vs'} →
                  Acc x acc (AllP.++⁺ (AllP.++⁺ Ts (_∷_ {x = v} S [])) Us) →
                  Acc x acc (AllP.++⁺ Ts (_∷_ {x = v} S Us))
      acc-shift {Ts = []}       K            = K
      acc-shift {Ts = T' ∷ Ts'} (keep e r K) = keep e r (acc-shift {Ts = Ts'} K)
      acc-shift {Ts = T' ∷ Ts'} (skip z K)   = skip z (acc-shift {Ts = Ts'} K)

      summaries-rep : {x : V 𝒢} (pa : ℕ) → nth? pa vs ≡ just x →
                      (acc : List (ℕ × M.Table)) {us : List (V 𝒢)} {Ts : H𝒢.Tables x us} →
                      Acc x acc Ts → (k : ℕ) {ps : List ℕ} {ws' : List (V 𝒢)} → PosOf ps ws' →
                      Acc x (TB.summaries k pa acc ps) (AllP.++⁺ Ts (H𝒢.summaries G x Ts ws'))
      summaries-rep pa ha acc K k [] = acc-nil K
      summaries-rep {x} pa ha acc {Ts = Ts} K k (_∷_ {p} {w} hp P)
        with TB.through pa p acc | Prf.prf (through-rep pa p ha hp acc K)
      ... | nothing | z =
        acc-shift {Ts = Ts} (summaries-rep pa ha acc (acc-snoc-skip K ⟪ ≈-sym z ⟫) (suc k) P)
      ... | just t  | e =
        acc-shift {Ts = Ts}
                  (summaries-rep pa ha (acc ++ (p , t) ∷ []) (acc-snoc-keep K hp ⟪ e ⟫) (suc k) P)

      hidden-rep : {x y : V 𝒢} (pa pb : ℕ) → nth? pa vs ≡ just x → nth? pb vs ≡ just y →
                   Prf (table-morphism 𝒢 x y (TB.through pa pb (TB.summaries 0 pa [] HG.hid-pos))
                        ≈ hide-all (vertex-object 𝒢) G ws x y)
      hidden-rep {x} {y} pa pb ha hb =
        ⟪ ≈-trans (Prf.prf (through-rep pa pb ha hb (TB.summaries 0 pa [] HG.hid-pos)
                                        (summaries-rep pa ha [] nil 0 (pos-of ws ws-mem))))
                  (≈-sym (H𝒢.fold-through ws pairs x y)) ⟫

      or!-false : (a b : Bool) → HG.or! a b ≡ false → (a ≡ false) × (b ≡ false)
      or!-false false b     e = ≡-refl , e
      or!-false true  false e = ⊥-elim (true≢false e)
      or!-false true  true  e = ⊥-elim (true≢false e)

      row-false : (r : List Semiring.Carrier) → HG.nonzero-row r ≡ false →
                  All (λ e → e ≡ Semiring.ε) r
      row-false []      _ = []
      row-false (c ∷ r) e with or!-false (not ⌊ ε-dec c ⌋) (HG.nonzero-row r) e
      ... | (e₁ , e₂) = dec-just (ε-dec c) (not-false e₁) ∷ row-false r e₂

      tab-false : (t : M.Table) → HG.nonzero-table t ≡ false →
                  All (All (λ e → e ≡ Semiring.ε)) t
      tab-false []      _ = []
      tab-false (r ∷ t) e with or!-false (HG.nonzero-row r) (HG.nonzero-table t) e
      ... | (e₁ , e₂) = row-false r e₁ ∷ tab-false t e₂

      look-εₘ : (x y : V 𝒢) (t : M.Table) → All (All (λ e → e ≡ Semiring.ε)) t →
                mat (M.look {vertex-width 𝒢 y} {vertex-width 𝒢 x} t) ≈ εₘ
      look-εₘ x y t z =
        ≈-trans (mat-cong (λ i j → ≈-of-≡
                  (nth-All [] (toℕ i) ≡-refl
                           (All-map (λ rz → nth-All Semiring.ε (toℕ j) ≡-refl rz) z))))
                mat-ε

      keep-rep : (x y : V 𝒢) (w : Maybe M.Table) →
                 table-morphism 𝒢 x y (HG.keep w) ≈ table-morphism 𝒢 x y w
      keep-rep x y nothing  = ≈-refl
      keep-rep x y (just t) with HG.nonzero-table t in nz
      ... | true  = ≈-refl
      ... | false = ≈-sym (look-εₘ x y t (tab-false t nz))

      survivors-just : All (λ p → Σ (V 𝒢) (λ z → nth? p vs ≡ just z)) HG.survivors
      survivors-just =
        All-map (λ {p} lt → nth?-defined p vs lt)
                (filterᵇ-All (λ p → not (any (p ≡ᵇ_) HG.hid-pos))
                             (applyUpTo-All (λ i → i) (length (Tabulation.widths T))
                                            (λ p lt → subst (p <_) len-eq lt)))

      extract : ∀ {ps} → All (λ p → Σ (V 𝒢) (λ z → nth? p vs ≡ just z)) ps → List (V 𝒢)
      extract []             = []
      extract ((z , _) ∷ sj) = z ∷ extract sj

      mapMaybe-just : ∀ {ps} (sj : All (λ p → Σ (V 𝒢) (λ z → nth? p vs ≡ just z)) ps) →
                      mapMaybe (λ p → nth? p vs) ps ≡ extract sj
      mapMaybe-just []               = ≡-refl
      mapMaybe-just (_∷_ (z , e) sj) rewrite e = ≡-cong (z ∷_) (mapMaybe-just sj)

      at-extract : ∀ {ps} (sj : All (λ p → Σ (V 𝒢) (λ z → nth? p vs ≡ just z)) ps) {a : ℕ}
                   {x : V 𝒢} → nth? a (extract sj) ≡ just x →
                   Σ ℕ (λ p → (nth? a ps ≡ just p) × (nth? p vs ≡ just x))
      at-extract (_∷_ {p₀} (z , e) sj) {zero}  ≡-refl = p₀ , ≡-refl , e
      at-extract (_∷_ {p₀} (z , e) sj) {suc a} h with at-extract sj {a} h
      ... | (p , sa , sx) = p , sa , sx

      nums-eq : ∀ {ps} (sj : All (λ p → Σ (V 𝒢) (λ z → nth? p vs ≡ just z)) ps) →
                map (λ p → M.nth 0 p (Tabulation.numbers T)) ps
                ≡ map (index-of 𝒢) (mapMaybe (λ p → nth? p vs) ps)
      nums-eq []               = ≡-refl
      nums-eq (_∷_ (z , e) sj) rewrite e = ≡-cong₂ _∷_ (num-at e) (nums-eq sj)

      wids-eq : ∀ {ps} (sj : All (λ p → Σ (V 𝒢) (λ z → nth? p vs ≡ just z)) ps) →
                map TB.wd ps ≡ map (vertex-width 𝒢) (mapMaybe (λ p → nth? p vs) ps)
      wids-eq []               = ≡-refl
      wids-eq (_∷_ (z , e) sj) rewrite e = ≡-cong₂ _∷_ (wd-at e) (wids-eq sj)

      nth-differ : (js : List ℕ) → AllPairs _≢_ js → {p q : ℕ} {a b : ℕ} → p ≢ q →
                   nth? p js ≡ just a → nth? q js ≡ just b → a ≢ b
      nth-differ (j ∷ js) (hj ∷ ps) {zero}  {zero}  pq _      _  = ⊥-elim (pq ≡-refl)
      nth-differ (j ∷ js) (hj ∷ ps) {zero}  {suc q} pq ≡-refl eb =
        λ ab → All-lookup hj (nth?-∈ {p = q} eb) ab
      nth-differ (j ∷ js) (hj ∷ ps) {suc p} {zero}  pq ea ≡-refl =
        λ ab → All-lookup hj (nth?-∈ {p = p} ea) (≡-sym ab)
      nth-differ (j ∷ js) (hj ∷ ps) {suc p} {suc q} pq ea eb =
        nth-differ js ps (λ e → pq (≡-cong suc e)) ea eb

      map-nth-distinct : ∀ {ps} → All (λ p → Σ (V 𝒢) (λ z → nth? p vs ≡ just z)) ps →
                         AllPairs _≢_ ps →
                         AllPairs _≢_ (map (λ p → M.nth 0 p (Tabulation.numbers T)) ps)
      map-nth-distinct []                   []          = []
      map-nth-distinct (_∷_ {p} (z , e) sj) (hp ∷ dps) =
        AllP.map⁺ (heads sj hp) ∷ map-nth-distinct sj dps
        where
        heads : ∀ {qs} → All (λ q → Σ (V 𝒢) (λ z' → nth? q vs ≡ just z')) qs → All (p ≢_) qs →
                All (λ q → M.nth 0 p (Tabulation.numbers T) ≢ M.nth 0 q (Tabulation.numbers T)) qs
        heads []                      []         = []
        heads (_∷_ {q} (z' , e') sj') (ne ∷ nes) =
          (λ eq → nth-differ (Tabulation.numbers T) (R .numbers-distinct) ne
                             (nth?-num e) (nth?-num e')
                             (≡-trans (≡-sym (num-at e)) (≡-trans eq (num-at e'))))
          ∷ heads sj' nes

      avoid : ∀ {ps ws'} → PosOf ps ws' → {p : ℕ} {x : V 𝒢} → nth? p vs ≡ just x →
              ¬ (x ∈ ws') → All (λ q → (p ≡ᵇ q) ≡ false) ps
      avoid []                _  _  = []
      avoid (_∷_ {q} {w} e P) {p} hp nx =
        ≡ᵇ-false p q (λ pq →
          nx (here (just-inj (≡-trans (≡-sym (subst (λ r → nth? r vs ≡ just _) pq hp)) e))))
        ∷ avoid P hp (λ h → nx (there h))

    ∈-remaining : {x : V 𝒢} → x ∈ vs → ¬ (x ∈ ws) → x ∈ remaining
    ∈-remaining {x} mx nw with ∈-nth? mx
    ... | (p , hp) =
      ∈-mapMaybe (∈-filterᵇ (λ p' → not (any (p' ≡ᵇ_) HG.hid-pos)) up-mem surv) hp
      where
      up-mem : p ∈ upTo (length (Tabulation.widths T))
      up-mem = subst (λ n → p ∈ upTo n) (≡-sym len-eq)
                     (<-applyUpTo (λ i → i) (nth?-length p vs hp))
      surv : not (any (p ≡ᵇ_) HG.hid-pos) ≡ true
      surv = ≡-cong not (all-any-false (p ≡ᵇ_) HG.hid-pos (avoid (pos-of ws ws-mem) hp nw))

    hide-rep : Represents (TB.hide-graph ε-dec (map (index-of 𝒢) ws)) remaining
               (hide-all (vertex-object 𝒢) G ws)
    hide-rep .numbers-eq       = nums-eq survivors-just
    hide-rep .widths-eq        = wids-eq survivors-just
    hide-rep .numbers-distinct =
      map-nth-distinct survivors-just
                       (filterᵇ-AllPairs (λ p → not (any (p ≡ᵇ_) HG.hid-pos))
                                         (upTo-distinct (length (Tabulation.widths T))))
    hide-rep .slots {a'} {b'} {x} {y} ha' hb'
      with at-extract survivors-just
                      (subst (λ l → nth? a' l ≡ just x) (mapMaybe-just survivors-just) ha')
         | at-extract survivors-just
                      (subst (λ l → nth? b' l ≡ just y) (mapMaybe-just survivors-just) hb')
    ... | (pa , spa , hpa) | (pb , spb , hpb) =
      subst (λ w → Prf (table-morphism 𝒢 x y w ≈ hide-all (vertex-object 𝒢) G ws x y))
            (≡-sym slot-eq)
            ⟪ ≈-trans (keep-rep x y (TB.through pa pb (TB.summaries 0 pa [] HG.hid-pos)))
                      (Prf.prf (hidden-rep pa pb hpa hpb)) ⟫
      where
      acc₀ = TB.summaries 0 pa [] HG.hid-pos

      slot-eq : table-at (TB.hide-graph ε-dec (map (index-of 𝒢) ws)) a' b'
                ≡ HG.keep (TB.through pa pb acc₀)
      slot-eq =
        ≡-trans (≡-cong (M.nth nothing b')
                        (nth?-nth [] a' (map HG.row HG.survivors)
                                  (nth?-map HG.row a' HG.survivors spa)))
                (nth?-nth nothing b'
                          (map (λ b → HG.keep (TB.through pa b acc₀)) HG.survivors)
                          (nth?-map (λ b → HG.keep (TB.through pa b acc₀)) b' HG.survivors spb))

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
module _ {m : ℕ} {D : Derivation} (𝒢 : Graph m D) where

  root-row : ∀ y → edge-labels 𝒢 (inj₂ ε) y ≈ εₘ
  root-row (inj₁ _) = ≈-refl {f = εₘ}
  root-row (inj₂ q) with Graph.<-interior 𝒢 ε q
  ... | inj₁ ()
  ... | inj₂ ⟪ e ⟫ = e

  hide-paths⁺ : hide-all (vertex-object 𝒢) (edge-labels 𝒢) (map inj₂ (paths⁺ 𝒢)) (inj₁ input) (inj₂ ε)
                ≈ collapse 𝒢
  hide-paths⁺ =
    hide-all-cong (vertex-object 𝒢) (map inj₂ (vertices-result-first D))
                  (hide-sink (vertex-object 𝒢) (edge-labels 𝒢) (inj₂ ε) root-row)
                  (inj₁ input) (inj₂ ε)

module HidePremise
  {m : ℕ} {D : Derivation} (𝒢 : Graph m D)
  {V : Set} (object' : V → Semimodule)
  (inp : V)
  (blk : Path D → V)
  {T : Set} (tgt : T → V)
  {M' : Semimodule} (Φ : object' inp ⇒ M')
  (P : (t : T) → object' (blk ε) ⇒ object' (tgt t))
  (K : (t : T) → object' inp ⇒ object' (tgt t))
  where

  record St : Set where
    field
      from-input   : (q : Path D) → M' ⇒ object' (blk q)
      interior : (p q : Path D) → object' (blk p) ⇒ object' (blk q)

  open St public

  step : St → Path D → St
  step st w .from-input q = st .from-input q +ₘ (st .interior w q ∘ st .from-input w)
  step st w .interior p q = st .interior p q +ₘ (st .interior w q ∘ st .interior p w)

  steps : St → List (Path D) → St
  steps = foldl step

  folds : ∀ {A V' : Set} (prem : A → St) (ι : Path D → V') (h' : A → V' → A) →
          (∀ a w → step (prem a) w ≡ prem (h' a (ι w))) →
          (ws : List (Path D)) (a : A) → steps (prem a) ws ≡ prem (foldl h' a (map ι ws))
  folds prem ι h' ok []       a = ≡-refl
  folds prem ι h' ok (w ∷ ws) a =
    ≡-trans (≡-cong (λ st → steps st ws) (ok a w)) (folds prem ι h' ok ws (h' a (ι w)))

  private
    Φ-step : ∀ (st : St) (w : Path D) (q : Path D) →
             (step st w .from-input q ∘ Φ)
             ≈ ((st .from-input q ∘ Φ) +ₘ (st .interior w q ∘ (st .from-input w ∘ Φ)))
    Φ-step st w q =
      ≈-trans (CM.comp-bilinear₁ (st .from-input q) (st .interior w q ∘ st .from-input w) Φ)
              (+ₘ-cong ≈-refl (assoc (st .interior w q) (st .from-input w) Φ))

  record Agrees (G : EdgeLabels object') (st : St) : Set where
    field
      into-ok   : ∀ q → G inp (blk q) ≈ (st .from-input q ∘ Φ)
      interior-ok : ∀ p q → G (blk p) (blk q) ≈ st .interior p q
      tgt-ok    : ∀ t → G inp (tgt t) ≈ (K t +ₘ (P t ∘ (st .from-input ε ∘ Φ)))
      up-ok     : ∀ t (p : Path D) → p ≢ ε → G (blk p) (tgt t) ≈ (P t ∘ st .interior p ε)

  open Agrees public

  agrees-hide : ∀ {G st} (w : Path D) → w ≢ ε → Agrees G st → Agrees (hide object' G (blk w)) (step st w)
  agrees-hide {st = st} w _ D .into-ok q =
    ≈-trans (+ₘ-cong (D .into-ok q) (∘-cong (D .interior-ok w q) (D .into-ok w)))
            (≈-sym (Φ-step st w q))
  agrees-hide w _ D .interior-ok p q =
    +ₘ-cong (D .interior-ok p q) (∘-cong (D .interior-ok w q) (D .interior-ok p w))
  agrees-hide {st = st} w w≢ε D .tgt-ok t =
    ≈-trans (offset-step {Km = K t} {P = P t}
                         {Xm = st .from-input ε ∘ Φ}
                         {Ym = st .interior w ε}
                         {Zm = st .from-input w ∘ Φ}
              (D .tgt-ok t) (D .up-ok t w w≢ε) (D .into-ok w))
            (+ₘ-cong ≈-refl (∘-cong₂ {f = P t} (≈-sym (Φ-step st w ε))))
  agrees-hide {st = st} w w≢ε D .up-ok t p p≢ε =
    root-step {P = P t} {Xm = st .interior p ε}
              {Ym = st .interior w ε} {Zm = st .interior p w}
      (D .up-ok t p p≢ε) (D .up-ok t w w≢ε) (D .interior-ok p w)

  agrees-hide-all : ∀ {G st} (ws : List (Path D)) → All (_≢ ε) ws → Agrees G st →
                    Agrees (hide-all object' G (map blk ws)) (steps st ws)
  agrees-hide-all []       []         D = D
  agrees-hide-all (w ∷ ws) (w≢ε ∷ hs) D = agrees-hide-all ws hs (agrees-hide w w≢ε D)

  -- The relations a rule contributes, before the graph's root is hidden. Every edge from the graph to
  -- a target leaves the graph's root, which here is a matter of the vertex set rather than a lemma.
  record Start (G : EdgeLabels object') (st : St) : Set where
    field
      into-start   : ∀ q → G inp (blk q) ≈ (st .from-input q ∘ Φ)
      interior-start : ∀ p q → G (blk p) (blk q) ≈ st .interior p q
      tgt-start    : ∀ t → G inp (tgt t) ≈ K t
      up-start     : ∀ t → G (blk ε) (tgt t) ≈ P t
      off-start    : ∀ t (p : Path D) → p ≢ ε → G (blk p) (tgt t) ≈ εₘ
      sink         : ∀ q → st .interior ε q ≈ εₘ

  open Start public

  agrees-start : ∀ {G st} → Start G st → Agrees (hide object' G (blk ε)) (step st ε)
  agrees-start {st = st} r .into-ok q =
    ≈-trans (+ₘ-cong (r .into-start q)
                     (∘-cong (r .interior-start ε q) (r .into-start ε)))
            (≈-sym (Φ-step st ε q))
  agrees-start r .interior-ok p q =
    +ₘ-cong (r .interior-start p q)
            (∘-cong (r .interior-start ε q) (r .interior-start p ε))
  agrees-start {st = st} r .tgt-ok t =
    ≈-trans (+ₘ-cong (r .tgt-start t)
                     (∘-cong (r .up-start t) (r .into-start ε)))
            (+ₘ-cong ≈-refl (∘-cong₂ {f = P t} (≈-sym unchanged)))
    where
    unchanged : (step st ε .from-input ε ∘ Φ) ≈ (st .from-input ε ∘ Φ)
    unchanged =
      ≈-trans (Φ-step st ε ε)
              (≈-trans (+ₘ-cong ≈-refl (∘-cong₁ {f₁ = st .interior ε ε} {f₂ = εₘ} {g = st .from-input ε ∘ Φ} (r .sink ε)))
                       (absorb₁ (st .from-input ε ∘ Φ) (st .from-input ε ∘ Φ)))
  agrees-start {st = st} r .up-ok t p p≢ε =
    ≈-trans (+ₘ-cong (r .off-start t p p≢ε)
                     (∘-cong (r .up-start t) (r .interior-start p ε)))
    (≈-trans (+ₘ-lunit (P t ∘ st .interior p ε))
             (∘-cong₂ {f = P t} (≈-sym unchanged)))
    where
    unchanged : step st ε .interior p ε ≈ st .interior p ε
    unchanged =
      ≈-trans (+ₘ-cong ≈-refl (∘-cong₁ {f₁ = st .interior ε ε} {f₂ = εₘ} {g = st .interior p ε} (r .sink ε)))
              (absorb₁ (st .interior p ε) (st .interior p ε))

  module Hidden (G₀ : EdgeLabels object') (prem : EdgeLabels (vertex-object 𝒢) → St)
                (prem-step : ∀ G w → step (prem G) w ≡ prem (hide (vertex-object 𝒢) G (inj₂ w))) where

    st⁰ : St
    st⁰ = prem (edge-labels 𝒢)

    G : EdgeLabels object'
    G = hide-all object' (hide object' G₀ (blk ε)) (map blk (vertices-result-first D))

    st : St
    st = steps (step st⁰ ε) (vertices-result-first D)

    done : Start G₀ st⁰ → Agrees G st
    done start =
      agrees-hide-all (vertices-result-first D) (vertices-result-first-no-ε D) (agrees-start start)

    κ : st .from-input ε ≡ prem (hide-all (vertex-object 𝒢) (edge-labels 𝒢) (map inj₂ (paths⁺ 𝒢))) .from-input ε
    κ = ≡-cong (λ st' → st' .from-input ε) (folds prem inj₂ (hide (vertex-object 𝒢)) prem-step (paths⁺ 𝒢) (edge-labels 𝒢))

module NoEdgeIntoHidden
  {V : Set} (vertex-object : V → Semimodule)
  {W : Set} (hid : W → V)
  {S : Set} (src : S → V)
  {T : Set} (col : T → V)
  (𝒢 : (s : S) (t : T) → vertex-object (src s) ⇒ vertex-object (col t))
  where

  record Fixed (G : EdgeLabels vertex-object) : Set where
    field
      edge    : ∀ s t → G (src s) (col t) ≈ 𝒢 s t
      no-edge : ∀ s w → G (src s) (hid w) ≈ εₘ

  open Fixed public

  fixed-hide : ∀ {G} (w : W) → Fixed G → Fixed (hide vertex-object G (hid w))
  fixed-hide {G} w k .edge s t =
    ≈-trans (+ₘ-cong (k .edge s t) (∘-cong₂ {f = G (hid w) (col t)} (k .no-edge s w)))
            (absorb₂ (𝒢 s t) (G (hid w) (col t)))
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
  (𝒢 : (s : S) (t : T) → vertex-object (src s) ⇒ vertex-object (col t))
  where

  record Fixed (G : EdgeLabels vertex-object) : Set where
    field
      edge    : ∀ s t → G (src s) (col t) ≈ 𝒢 s t
      no-edge : ∀ w t → G (hid w) (col t) ≈ εₘ

  open Fixed public

  fixed-hide : ∀ {G} (w : W) → Fixed G → Fixed (hide vertex-object G (hid w))
  fixed-hide {G} w k .edge s t =
    ≈-trans (+ₘ-cong (k .edge s t)
                     (≈-trans {g = εₘ {vertex-object (hid w)} {vertex-object (col t)} ∘ G (src s) (hid w)}
                              (∘-cong₁ {f₁ = G (hid w) (col t)} {f₂ = εₘ} {g = G (src s) (hid w)} (k .no-edge w t))
                              (CM.comp-bilinear-ε₁ {Z = vertex-object (col t)} (G (src s) (hid w)))))
            (+ₘ-runit (𝒢 s t))
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

-- In-neighbours of a premise vertex lifted to the enclosing rule.
premise-ins : ∀ {m n b Ds D} (i : Ds ∋ D) → List (Input ⊎ Path (node m n b Ds)) →
              List (Input ⊎ Path D) → List (Input ⊎ Path (node m n b Ds))
premise-ins i srcs []            = []
premise-ins i srcs (inj₁ _ ∷ xs) = srcs ++ premise-ins i srcs xs
premise-ins i srcs (inj₂ p ∷ xs) = inj₂ (into i p) ∷ premise-ins i srcs xs

lift-roots : ∀ {m n b Ds D} (i : Ds ∋ D) → List (Path D × M.Table) →
             List (Path (node m n b Ds) × M.Table)
lift-roots i []             = []
lift-roots i ((r , t) ∷ fs) = (into i r , t) ∷ lift-roots i fs

weaken-roots : ∀ {m n b D Ds} → List (Path (node m n b Ds) × M.Table) →
               List (Path (node m n b (D ∷ Ds)) × M.Table)
weaken-roots []             = []
weaken-roots ((r , t) ∷ fs) = (weaken r , t) ∷ weaken-roots fs

module Rule₀
  {m n : ℕ} (fo-output : Bool)
  (input-to-output : 𝔽 m ⇒ 𝔽 n)
  where

  E : Graph m (node m n fo-output [])
  E .Graph.from-input ε = input-to-output
  E .Graph.from-input (into () _)
  E .Graph.interior ε ε = εₘ
  E .Graph.interior ε (into () _)
  E .Graph.interior (into () _) _
  E .Graph.<-interior ε ε = inj₂ ⟪ ≈-refl ⟫
  E .Graph.<-interior ε (into () _)
  E .Graph.<-interior (into () _) _
  E .Graph.in-neighbours ε = inj₁ input ∷ []
  E .Graph.in-neighbours (into () _)
  E .Graph.parent-to-input ε = table-of (I {𝔽 m})
  E .Graph.parent-to-input (into () _)
  E .Graph.roots-to-input ε = []
  E .Graph.roots-to-input (into () _)
  E .Graph.input-to-output ε = table-of input-to-output
  E .Graph.input-to-output (into () _)

  agree : collapse E ≈ input-to-output
  agree = ≈-refl {f = input-to-output}

module Rule₁
  {m : ℕ}
  {m₁ : ℕ} {D₁ : Derivation} (𝒢 : Graph m₁ D₁)
  {n : ℕ}
  (inputs : 𝔽 m ⇒ 𝔽 m₁)
  (fo-output : Bool)
  (input-to-output : 𝔽 m ⇒ 𝔽 n)
  (up-root : 𝔽 (out-width D₁) ⇒ 𝔽 n)
  where

  private
    out-edge : (p : Path (node m n fo-output (D₁ ∷ []))) →
               object (node m n fo-output (D₁ ∷ [])) p ⇒ 𝔽 n
    out-edge ε                     = εₘ
    out-edge (into here ε)         = up-root
    out-edge (into here (into i p)) = εₘ
    out-edge (into (there ()) _)

    to-premise : (p : Path (node m n fo-output (D₁ ∷ []))) (q : Path D₁) →
                 object (node m n fo-output (D₁ ∷ [])) p ⇒ object D₁ q
    to-premise ε             q = εₘ
    to-premise (into here p) q = Graph.interior 𝒢 p q
    to-premise (into (there ()) _) _

  E : Graph m (node m n fo-output (D₁ ∷ []))
  E .Graph.from-input ε            = input-to-output
  E .Graph.from-input (into here q)        = Graph.from-input 𝒢 q ∘ inputs
  E .Graph.from-input (into (there ()) _)
  E .Graph.interior p ε             = out-edge p
  E .Graph.interior p (into here q) = to-premise p q
  E .Graph.interior p (into (there ()) _)
  E .Graph.<-interior (into here p) (into here q) = Graph.<-interior 𝒢 p q
  E .Graph.<-interior (into here p) ε             = inj₁ tt
  E .Graph.<-interior ε             ε             = inj₂ ⟪ ≈-refl ⟫
  E .Graph.<-interior ε             (into here q) = inj₂ ⟪ ≈-refl ⟫
  E .Graph.<-interior (into (there ()) _) _
  E .Graph.<-interior _ (into (there ()) _)
  E .Graph.in-neighbours ε             = inj₁ input ∷ inj₂ (into here ε) ∷ []
  E .Graph.in-neighbours (into here q) =
    premise-ins here (inj₁ input ∷ []) (Graph.in-neighbours 𝒢 q)
  E .Graph.in-neighbours (into (there ()) _)
  E .Graph.parent-to-input ε                      = table-of (I {𝔽 m})
  E .Graph.parent-to-input (into here ε)          = table-of inputs
  E .Graph.parent-to-input (into here (into j q)) = Graph.parent-to-input 𝒢 (into j q)
  E .Graph.parent-to-input (into (there ()) _)
  E .Graph.roots-to-input ε             = []
  E .Graph.roots-to-input (into here q) = lift-roots here (Graph.roots-to-input 𝒢 q)
  E .Graph.roots-to-input (into (there ()) _)
  E .Graph.input-to-output ε             = table-of input-to-output
  E .Graph.input-to-output (into here q) = Graph.input-to-output 𝒢 q
  E .Graph.input-to-output (into (there ()) _)

  private
    b : Path D₁ → V E
    b q = inj₂ (into here q)

    er : V E
    er = inj₂ ε

    module S = HidePremise 𝒢 (vertex-object E) (inj₁ input) b (λ (_ : Unit) → er) inputs (λ _ → up-root) (λ _ → input-to-output)

    prem : EdgeLabels (vertex-object 𝒢) → S.St
    prem G .S.from-input q = G (inj₁ input) (inj₂ q)
    prem G .S.interior p q = G (inj₂ p) (inj₂ q)

    module hidden = S.Hidden (edge-labels E) prem (λ G w → ≡-refl)

    start : S.Start (edge-labels E) hidden.st⁰
    start .S.into-start q = ≈-refl
    start .S.interior-start p q = ≈-refl
    start .S.tgt-start _ = ≈-refl {f = input-to-output}
    start .S.up-start _ = ≈-refl {f = up-root}
    start .S.off-start _ ε          ne = ⊥-elimₚ (ne ≡-refl)
    start .S.off-start _ (into i p) _  = ≈-refl {f = εₘ}
    start .S.sink q = root-row 𝒢 (inj₂ q)

    plumb : collapse E ≡ hidden.G (inj₁ input) er
    plumb = ≡-cong (λ l → hide-all (vertex-object E) (edge-labels E) l (inj₁ input) er)
                   (≡-trans (≡-cong (map inj₂) (++-identityʳ (map (into here) (ε ∷ vertices-result-first D₁))))
                            (≡-sym (map-∘ {g = inj₂} {f = into here} (ε ∷ vertices-result-first D₁))))

  agree : collapse E ≈ (input-to-output +ₘ (up-root ∘ (collapse 𝒢 ∘ inputs)))
  agree =
    ≈-trans (≡-to-≈ plumb)
            (≈-trans (hidden.done start .S.tgt-ok tt)
                     (+ₘ-cong ≈-refl (∘-cong₂ {f = up-root} (∘-cong₁ {g = inputs} (≈-trans (≡-to-≈ hidden.κ) (hide-paths⁺ 𝒢))))))

module Rule₂
  {m : ℕ}
  {m₁ : ℕ} {D₁ : Derivation} (𝒢₁ : Graph m₁ D₁)
  {m₂ : ℕ} {D₂ : Derivation} (𝒢₂ : Graph m₂ D₂)
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
    out-edge : (p : Path (node m n fo-output (D₁ ∷ D₂ ∷ []))) →
               object (node m n fo-output (D₁ ∷ D₂ ∷ [])) p ⇒ 𝔽 n
    out-edge ε                                  = εₘ
    out-edge (into here ε)                      = up₁
    out-edge (into here (into i p))             = εₘ
    out-edge (into (there here) ε)              = up₂
    out-edge (into (there here) (into i p))     = εₘ
    out-edge (into (there (there ())) _)

    to-first : (p : Path (node m n fo-output (D₁ ∷ D₂ ∷ []))) (q : Path D₁) →
               object (node m n fo-output (D₁ ∷ D₂ ∷ [])) p ⇒ object D₁ q
    to-first ε                    q = εₘ
    to-first (into here p)        q = Graph.interior 𝒢₁ p q
    to-first (into (there here) p) q = εₘ
    to-first (into (there (there ())) _) _

    to-second : (p : Path (node m n fo-output (D₁ ∷ D₂ ∷ []))) (q : Path D₂) →
                object (node m n fo-output (D₁ ∷ D₂ ∷ [])) p ⇒ object D₂ q
    to-second ε                        q = εₘ
    to-second (into here ε)            q = Graph.from-input 𝒢₂ q ∘ from-root₁
    to-second (into here (into i p))   q = εₘ
    to-second (into (there here) p)    q = Graph.interior 𝒢₂ p q
    to-second (into (there (there ())) _) _

  E : Graph m (node m n fo-output (D₁ ∷ D₂ ∷ []))
  E .Graph.from-input ε                        = input-to-output
  E .Graph.from-input (into here q)            = Graph.from-input 𝒢₁ q ∘ inputs₁
  E .Graph.from-input (into (there here) q)    = Graph.from-input 𝒢₂ q ∘ from-inputs₂
  E .Graph.from-input (into (there (there ())) _)
  E .Graph.interior p ε                     = out-edge p
  E .Graph.interior p (into here q)         = to-first p q
  E .Graph.interior p (into (there here) q) = to-second p q
  E .Graph.interior p (into (there (there ())) _)
  E .Graph.<-interior (into here p)         (into here q)         = Graph.<-interior 𝒢₁ p q
  E .Graph.<-interior (into here p)         (into (there here) q) = inj₁ tt
  E .Graph.<-interior (into (there here) p) (into here q)         = inj₂ ⟪ ≈-refl ⟫
  E .Graph.<-interior (into (there here) p) (into (there here) q) = Graph.<-interior 𝒢₂ p q
  E .Graph.<-interior (into here p)         ε = inj₁ tt
  E .Graph.<-interior (into (there here) p) ε = inj₁ tt
  E .Graph.<-interior ε ε             = inj₂ ⟪ ≈-refl ⟫
  E .Graph.<-interior ε (into here q) = inj₂ ⟪ ≈-refl ⟫
  E .Graph.<-interior ε (into (there here) q) = inj₂ ⟪ ≈-refl ⟫
  E .Graph.<-interior (into (there (there ())) _) _
  E .Graph.<-interior _ (into (there (there ())) _)
  E .Graph.in-neighbours ε =
    inj₁ input ∷ inj₂ (into here ε) ∷ inj₂ (into (there here) ε) ∷ []
  E .Graph.in-neighbours (into here q) =
    premise-ins here (inj₁ input ∷ []) (Graph.in-neighbours 𝒢₁ q)
  E .Graph.in-neighbours (into (there here) q) =
    premise-ins (there here) (inj₁ input ∷ inj₂ (into here ε) ∷ []) (Graph.in-neighbours 𝒢₂ q)
  E .Graph.in-neighbours (into (there (there ())) _)
  E .Graph.parent-to-input ε                              = table-of (I {𝔽 m})
  E .Graph.parent-to-input (into here ε)                  = table-of inputs₁
  E .Graph.parent-to-input (into here (into j q))         = Graph.parent-to-input 𝒢₁ (into j q)
  E .Graph.parent-to-input (into (there here) ε)          = table-of from-inputs₂
  E .Graph.parent-to-input (into (there here) (into j q)) = Graph.parent-to-input 𝒢₂ (into j q)
  E .Graph.parent-to-input (into (there (there ())) _)
  E .Graph.roots-to-input ε                     = []
  E .Graph.roots-to-input (into here q)         = lift-roots here (Graph.roots-to-input 𝒢₁ q)
  E .Graph.roots-to-input (into (there here) ε) = (into here ε , table-of from-root₁) ∷ []
  E .Graph.roots-to-input (into (there here) (into j q)) =
    lift-roots (there here) (Graph.roots-to-input 𝒢₂ (into j q))
  E .Graph.roots-to-input (into (there (there ())) _)
  E .Graph.input-to-output ε                     = table-of input-to-output
  E .Graph.input-to-output (into here q)         = Graph.input-to-output 𝒢₁ q
  E .Graph.input-to-output (into (there here) q) = Graph.input-to-output 𝒢₂ q
  E .Graph.input-to-output (into (there (there ())) _)

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
    P₁ (inj₁ q) = Graph.from-input 𝒢₂ q ∘ from-root₁
    P₁ (inj₂ _) = up₁

    K₁ : (t : Path D₂ ⊎ Unit) → (𝔽 m) ⇒ vertex-object E (tgt₁ t)
    K₁ (inj₁ q) = Graph.from-input 𝒢₂ q ∘ from-inputs₂
    K₁ (inj₂ _) = input-to-output

    module S₁ = HidePremise 𝒢₁ (vertex-object E) (inj₁ input) b1 tgt₁ inputs₁ P₁ K₁

    prem₁ : EdgeLabels (vertex-object 𝒢₁) → S₁.St
    prem₁ G .S₁.from-input q = G (inj₁ input) (inj₂ q)
    prem₁ G .S₁.interior p q = G (inj₂ p) (inj₂ q)

    module hidden₁ = S₁.Hidden (edge-labels E) prem₁ (λ G w → ≡-refl)

    start₁ : S₁.Start (edge-labels E) hidden₁.st⁰
    start₁ .S₁.into-start q = ≈-refl
    start₁ .S₁.interior-start p q = ≈-refl
    start₁ .S₁.tgt-start (inj₁ q) = ≈-refl
    start₁ .S₁.tgt-start (inj₂ _) = ≈-refl {f = input-to-output}
    start₁ .S₁.up-start (inj₁ q) = ≈-refl
    start₁ .S₁.up-start (inj₂ _) = ≈-refl {f = up₁}
    start₁ .S₁.off-start t        ε          ne = ⊥-elimₚ (ne ≡-refl)
    start₁ .S₁.off-start (inj₁ q) (into i p) _  = ≈-refl {f = εₘ}
    start₁ .S₁.off-start (inj₂ _) (into i p) _  = ≈-refl {f = εₘ}
    start₁ .S₁.sink q = root-row 𝒢₁ (inj₂ q)

    done₁ = hidden₁.done start₁
    κ₁ = ≈-trans (≡-to-≈ hidden₁.κ) (hide-paths⁺ 𝒢₁)

  Φ₂ : (𝔽 m) ⇒ (𝔽 m₂)
  Φ₂ = inputs₂ ∘ ⟨ I , collapse 𝒢₁ ∘ inputs₁ ⟩

  private
    Φ₂' : (𝔽 m) ⇒ (𝔽 m₂)
    Φ₂' = from-inputs₂ +ₘ (from-root₁ ∘ (collapse 𝒢₁ ∘ inputs₁))

    Φ₂-split : Φ₂' ≈ Φ₂
    Φ₂-split = ≈-sym (≈-trans (∘-pair inputs₂ I (collapse 𝒢₁ ∘ inputs₁))
                              (+ₘ-cong (id-right {f = from-inputs₂}) (≈-refl {f = from-root₁ ∘ (collapse 𝒢₁ ∘ inputs₁)})))

    module S₂ = HidePremise 𝒢₂ (vertex-object E) (inj₁ input) b2 (λ (_ : Unit) → er) Φ₂' (λ _ → up₂)
                            (λ _ → input-to-output +ₘ (up₁ ∘ (collapse 𝒢₁ ∘ inputs₁)))

    prem₂ : EdgeLabels (vertex-object 𝒢₂) → S₂.St
    prem₂ G .S₂.from-input q = G (inj₁ input) (inj₂ q)
    prem₂ G .S₂.interior p q = G (inj₂ p) (inj₂ q)

    module hidden₂ = S₂.Hidden hidden₁.G prem₂ (λ G w → ≡-refl)

    Bh : (p : Path D₂) (t : Path D₂ ⊎ Unit) → object D₂ p ⇒ vertex-object E (tgt₁ t)
    Bh p          (inj₁ q) = Graph.interior 𝒢₂ p q
    Bh ε          (inj₂ _) = up₂
    Bh (into i p) (inj₂ _) = εₘ

    module IntoHidden = NoEdgeIntoHidden (vertex-object E) b1 b2 tgt₁ Bh

    fixed₀ : IntoHidden.Fixed (edge-labels E)
    fixed₀ .IntoHidden.edge D          (inj₁ q) = ≈-refl
    fixed₀ .IntoHidden.edge ε          (inj₂ _) = ≈-refl {f = up₂}
    fixed₀ .IntoHidden.edge (into i p) (inj₂ _) = ≈-refl {f = εₘ}
    fixed₀ .IntoHidden.no-edge D w = ≈-refl {f = εₘ}

    fixed₁ : IntoHidden.Fixed hidden₁.G
    fixed₁ = IntoHidden.fixed-hide-all (λ w → w) ps₁ (IntoHidden.fixed-hide ε fixed₀)

    start₂ : S₂.Start hidden₁.G hidden₂.st⁰
    start₂ .S₂.into-start q =
      ≈-trans (done₁ .S₁.tgt-ok (inj₁ q))
              (factor (Graph.from-input 𝒢₂ q) from-inputs₂ from-root₁ {h = hidden₁.st .S₁.from-input ε} {c = collapse 𝒢₁} inputs₁ κ₁)
    start₂ .S₂.interior-start p q = fixed₁ .IntoHidden.edge p (inj₁ q)
    start₂ .S₂.tgt-start _ =
      ≈-trans {g = input-to-output +ₘ (up₁ ∘ (hidden₁.st .S₁.from-input ε ∘ inputs₁))}
              (done₁ .S₁.tgt-ok (inj₂ tt)) (+ₘ-cong ≈-refl (∘-cong₂ {f = up₁} (∘-cong₁ {g = inputs₁} κ₁)))
    start₂ .S₂.up-start _ = fixed₁ .IntoHidden.edge ε (inj₂ tt)
    start₂ .S₂.off-start _ ε          ne = ⊥-elimₚ (ne ≡-refl)
    start₂ .S₂.off-start _ (into i p) _  = fixed₁ .IntoHidden.edge (into i p) (inj₂ tt)
    start₂ .S₂.sink q = root-row 𝒢₂ (inj₂ q)

    lst : map inj₂ (vertices-result-first (node m n fo-output (D₁ ∷ D₂ ∷ [])))
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

  agree : collapse E ≈ ((input-to-output +ₘ (up₁ ∘ (collapse 𝒢₁ ∘ inputs₁))) +ₘ (up₂ ∘ (collapse 𝒢₂ ∘ Φ₂)))
  agree =
    ≈-trans (≡-to-≈ plumb)
            (≈-trans {g = (input-to-output +ₘ (up₁ ∘ (collapse 𝒢₁ ∘ inputs₁))) +ₘ (up₂ ∘ (hidden₂.st .S₂.from-input ε ∘ Φ₂'))}
                     (hidden₂.done start₂ .S₂.tgt-ok tt)
                     (+ₘ-cong ≈-refl (∘-cong₂ {f = up₂} (∘-cong (≈-trans (≡-to-≈ hidden₂.κ) (hide-paths⁺ 𝒢₂)) Φ₂-split))))

module Rule₃
  {m : ℕ}
  {m₁ : ℕ} {D₁ : Derivation} (𝒢₁ : Graph m₁ D₁)
  {m₂ : ℕ} {D₂ : Derivation} (𝒢₂ : Graph m₂ D₂)
  {m₃ : ℕ} {D₃ : Derivation} (𝒢₃ : Graph m₃ D₃)
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
    e₁₃ ε          q = Graph.from-input 𝒢₃ q ∘ from-root₁

    e₂₃ : (p : Path D₂) (q : Path D₃) → object D₂ p ⇒ object D₃ q
    e₂₃ (into _ _) q = εₘ
    e₂₃ ε          q = Graph.from-input 𝒢₃ q ∘ from-root₂

  private
    out-edge : (p : Path (node m n fo-output (D₁ ∷ D₂ ∷ D₃ ∷ []))) →
               object (node m n fo-output (D₁ ∷ D₂ ∷ D₃ ∷ [])) p ⇒ 𝔽 n
    out-edge ε                                          = εₘ
    out-edge (into here ε)                              = up₁
    out-edge (into here (into i p))                     = εₘ
    out-edge (into (there here) ε)                      = up₂
    out-edge (into (there here) (into i p))             = εₘ
    out-edge (into (there (there here)) ε)              = up₃
    out-edge (into (there (there here)) (into i p))     = εₘ
    out-edge (into (there (there (there ()))) _)

    to-first : (p : Path (node m n fo-output (D₁ ∷ D₂ ∷ D₃ ∷ []))) (q : Path D₁) →
               object (node m n fo-output (D₁ ∷ D₂ ∷ D₃ ∷ [])) p ⇒ object D₁ q
    to-first ε                            q = εₘ
    to-first (into here p)                q = Graph.interior 𝒢₁ p q
    to-first (into (there here) p)        q = εₘ
    to-first (into (there (there here)) p) q = εₘ
    to-first (into (there (there (there ()))) _) _

    to-second : (p : Path (node m n fo-output (D₁ ∷ D₂ ∷ D₃ ∷ []))) (q : Path D₂) →
                object (node m n fo-output (D₁ ∷ D₂ ∷ D₃ ∷ [])) p ⇒ object D₂ q
    to-second ε                            q = εₘ
    to-second (into here p)                q = εₘ
    to-second (into (there here) p)        q = Graph.interior 𝒢₂ p q
    to-second (into (there (there here)) p) q = εₘ
    to-second (into (there (there (there ()))) _) _

    to-third : (p : Path (node m n fo-output (D₁ ∷ D₂ ∷ D₃ ∷ []))) (q : Path D₃) →
               object (node m n fo-output (D₁ ∷ D₂ ∷ D₃ ∷ [])) p ⇒ object D₃ q
    to-third ε                            q = εₘ
    to-third (into here p)                q = e₁₃ p q
    to-third (into (there here) p)        q = e₂₃ p q
    to-third (into (there (there here)) p) q = Graph.interior 𝒢₃ p q
    to-third (into (there (there (there ()))) _) _

  E : Graph m (node m n fo-output (D₁ ∷ D₂ ∷ D₃ ∷ []))
  E .Graph.from-input ε                                = input-to-output
  E .Graph.from-input (into here q)                    = Graph.from-input 𝒢₁ q ∘ inputs₁
  E .Graph.from-input (into (there here) q)            = Graph.from-input 𝒢₂ q ∘ inputs₂
  E .Graph.from-input (into (there (there here)) q)    = Graph.from-input 𝒢₃ q ∘ from-inputs₃
  E .Graph.from-input (into (there (there (there ()))) _)
  E .Graph.interior p ε                                 = out-edge p
  E .Graph.interior p (into here q)                     = to-first p q
  E .Graph.interior p (into (there here) q)             = to-second p q
  E .Graph.interior p (into (there (there here)) q)     = to-third p q
  E .Graph.interior p (into (there (there (there ()))) _)
  E .Graph.<-interior (into here p)                 (into here q)                 = Graph.<-interior 𝒢₁ p q
  E .Graph.<-interior (into here p)                 (into (there here) q)         = inj₁ tt
  E .Graph.<-interior (into here p)                 (into (there (there here)) q) = inj₁ tt
  E .Graph.<-interior (into (there here) p)         (into here q)                 = inj₂ ⟪ ≈-refl ⟫
  E .Graph.<-interior (into (there here) p)         (into (there here) q)         = Graph.<-interior 𝒢₂ p q
  E .Graph.<-interior (into (there here) p)         (into (there (there here)) q) = inj₁ tt
  E .Graph.<-interior (into (there (there here)) p) (into here q)                 = inj₂ ⟪ ≈-refl ⟫
  E .Graph.<-interior (into (there (there here)) p) (into (there here) q)         = inj₂ ⟪ ≈-refl ⟫
  E .Graph.<-interior (into (there (there here)) p) (into (there (there here)) q) = Graph.<-interior 𝒢₃ p q
  E .Graph.<-interior (into i p) ε = inj₁ tt
  E .Graph.<-interior ε ε                             = inj₂ ⟪ ≈-refl ⟫
  E .Graph.<-interior ε (into here q)                 = inj₂ ⟪ ≈-refl ⟫
  E .Graph.<-interior ε (into (there here) q)         = inj₂ ⟪ ≈-refl ⟫
  E .Graph.<-interior ε (into (there (there here)) q) = inj₂ ⟪ ≈-refl ⟫
  E .Graph.<-interior (into (there (there (there ()))) _) _
  E .Graph.<-interior _ (into (there (there (there ()))) _)
  E .Graph.in-neighbours ε =
    inj₁ input ∷ inj₂ (into here ε) ∷ inj₂ (into (there here) ε) ∷
    inj₂ (into (there (there here)) ε) ∷ []
  E .Graph.in-neighbours (into here q) =
    premise-ins here (inj₁ input ∷ []) (Graph.in-neighbours 𝒢₁ q)
  E .Graph.in-neighbours (into (there here) q) =
    premise-ins (there here) (inj₁ input ∷ []) (Graph.in-neighbours 𝒢₂ q)
  E .Graph.in-neighbours (into (there (there here)) q) =
    premise-ins (there (there here))
                (inj₁ input ∷ inj₂ (into here ε) ∷ inj₂ (into (there here) ε) ∷ [])
                (Graph.in-neighbours 𝒢₃ q)
  E .Graph.in-neighbours (into (there (there (there ()))) _)
  E .Graph.parent-to-input ε                                      = table-of (I {𝔽 m})
  E .Graph.parent-to-input (into here ε)                          = table-of inputs₁
  E .Graph.parent-to-input (into here (into j q))                 = Graph.parent-to-input 𝒢₁ (into j q)
  E .Graph.parent-to-input (into (there here) ε)                  = table-of inputs₂
  E .Graph.parent-to-input (into (there here) (into j q))         = Graph.parent-to-input 𝒢₂ (into j q)
  E .Graph.parent-to-input (into (there (there here)) ε)          = table-of from-inputs₃
  E .Graph.parent-to-input (into (there (there here)) (into j q)) = Graph.parent-to-input 𝒢₃ (into j q)
  E .Graph.parent-to-input (into (there (there (there ()))) _)
  E .Graph.roots-to-input ε                             = []
  E .Graph.roots-to-input (into here q)                 = lift-roots here (Graph.roots-to-input 𝒢₁ q)
  E .Graph.roots-to-input (into (there here) q)         =
    lift-roots (there here) (Graph.roots-to-input 𝒢₂ q)
  E .Graph.roots-to-input (into (there (there here)) ε) =
    (into here ε , table-of from-root₁) ∷ (into (there here) ε , table-of from-root₂) ∷ []
  E .Graph.roots-to-input (into (there (there here)) (into j q)) =
    lift-roots (there (there here)) (Graph.roots-to-input 𝒢₃ (into j q))
  E .Graph.roots-to-input (into (there (there (there ()))) _)
  E .Graph.input-to-output ε                             = table-of input-to-output
  E .Graph.input-to-output (into here q)                 = Graph.input-to-output 𝒢₁ q
  E .Graph.input-to-output (into (there here) q)         = Graph.input-to-output 𝒢₂ q
  E .Graph.input-to-output (into (there (there here)) q) = Graph.input-to-output 𝒢₃ q
  E .Graph.input-to-output (into (there (there (there ()))) _)

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
    c₁ = collapse 𝒢₁ ∘ inputs₁

    c₂ : (𝔽 m) ⇒ (𝔽 n₂)
    c₂ = collapse 𝒢₂ ∘ inputs₂

    P₁ : (t : Path D₃ ⊎ Unit) → (𝔽 n₁) ⇒ vertex-object E (tgt t)
    P₁ (inj₁ q) = Graph.from-input 𝒢₃ q ∘ from-root₁
    P₁ (inj₂ _) = up₁

    K₁ : (t : Path D₃ ⊎ Unit) → (𝔽 m) ⇒ vertex-object E (tgt t)
    K₁ (inj₁ q) = Graph.from-input 𝒢₃ q ∘ from-inputs₃
    K₁ (inj₂ _) = input-to-output

    module S₁ = HidePremise 𝒢₁ (vertex-object E) (inj₁ input) b1 tgt inputs₁ P₁ K₁

    prem₁ : EdgeLabels (vertex-object 𝒢₁) → S₁.St
    prem₁ G .S₁.from-input q = G (inj₁ input) (inj₂ q)
    prem₁ G .S₁.interior p q = G (inj₂ p) (inj₂ q)

    module hidden₁ = S₁.Hidden (edge-labels E) prem₁ (λ G w → ≡-refl)

    start₁ : S₁.Start (edge-labels E) hidden₁.st⁰
    start₁ .S₁.into-start q = ≈-refl
    start₁ .S₁.interior-start p q = ≈-refl
    start₁ .S₁.tgt-start (inj₁ q) = ≈-refl
    start₁ .S₁.tgt-start (inj₂ _) = ≈-refl {f = input-to-output}
    start₁ .S₁.up-start (inj₁ q) = ≈-refl
    start₁ .S₁.up-start (inj₂ _) = ≈-refl {f = up₁}
    start₁ .S₁.off-start t        ε          ne = ⊥-elimₚ (ne ≡-refl)
    start₁ .S₁.off-start (inj₁ q) (into i p) _  = ≈-refl {f = εₘ}
    start₁ .S₁.off-start (inj₂ _) (into i p) _  = ≈-refl {f = εₘ}
    start₁ .S₁.sink q = root-row 𝒢₁ (inj₂ q)

    done₁ = hidden₁.done start₁
    κ₁ = ≈-trans (≡-to-≈ hidden₁.κ) (hide-paths⁺ 𝒢₁)

    module OutOfHidden = NoEdgeOutOfHidden (vertex-object E) b1 (inj₁ {A = Input}) b2
                                           (λ _ q → Graph.from-input 𝒢₂ q ∘ inputs₂)

    fixed₀ : OutOfHidden.Fixed (edge-labels E)
    fixed₀ .OutOfHidden.edge _ q = ≈-refl
    fixed₀ .OutOfHidden.no-edge w q = ≈-refl {f = εₘ}

    fixed₁ : OutOfHidden.Fixed hidden₁.G
    fixed₁ = OutOfHidden.fixed-hide-all (λ w → w) ps₁ (OutOfHidden.fixed-hide ε fixed₀)

    cols₂ : Path D₂ ⊎ (Path D₃ ⊎ Unit) → V E
    cols₂ (inj₁ q) = b2 q
    cols₂ (inj₂ t) = tgt t

    Bh₂ : (p : Path D₂) (t : Path D₂ ⊎ (Path D₃ ⊎ Unit)) → object D₂ p ⇒ vertex-object E (cols₂ t)
    Bh₂ p          (inj₁ q)        = Graph.interior 𝒢₂ p q
    Bh₂ p          (inj₂ (inj₁ q)) = e₂₃ p q
    Bh₂ ε          (inj₂ (inj₂ _)) = up₂
    Bh₂ (into i p) (inj₂ (inj₂ _)) = εₘ

    module IntoHidden₂ = NoEdgeIntoHidden (vertex-object E) b1 b2 cols₂ Bh₂

    fixed₂ : IntoHidden₂.Fixed hidden₁.G
    fixed₂ = IntoHidden₂.fixed-hide-all (λ w → w) ps₁ (IntoHidden₂.fixed-hide ε k₀)
      where
      k₀ : IntoHidden₂.Fixed (edge-labels E)
      k₀ .IntoHidden₂.edge D          (inj₁ q)        = ≈-refl
      k₀ .IntoHidden₂.edge D          (inj₂ (inj₁ q)) = ≈-refl {f = e₂₃ D q}
      k₀ .IntoHidden₂.edge ε          (inj₂ (inj₂ _)) = ≈-refl {f = up₂}
      k₀ .IntoHidden₂.edge (into i p) (inj₂ (inj₂ _)) = ≈-refl {f = εₘ}
      k₀ .IntoHidden₂.no-edge D w = ≈-refl {f = εₘ}

    Φ₃₁ : (𝔽 m) ⇒ (𝔽 m₃)
    Φ₃₁ = from-inputs₃ +ₘ (from-root₁ ∘ c₁)

    P₂ : (t : Path D₃ ⊎ Unit) → (𝔽 n₂) ⇒ vertex-object E (tgt t)
    P₂ (inj₁ q) = Graph.from-input 𝒢₃ q ∘ from-root₂
    P₂ (inj₂ _) = up₂

    K₂ : (t : Path D₃ ⊎ Unit) → (𝔽 m) ⇒ vertex-object E (tgt t)
    K₂ (inj₁ q) = Graph.from-input 𝒢₃ q ∘ Φ₃₁
    K₂ (inj₂ _) = input-to-output +ₘ (up₁ ∘ c₁)

    module S₂ = HidePremise 𝒢₂ (vertex-object E) (inj₁ input) b2 tgt inputs₂ P₂ K₂

    prem₂ : EdgeLabels (vertex-object 𝒢₂) → S₂.St
    prem₂ G .S₂.from-input q = G (inj₁ input) (inj₂ q)
    prem₂ G .S₂.interior p q = G (inj₂ p) (inj₂ q)

    module hidden₂ = S₂.Hidden hidden₁.G prem₂ (λ G w → ≡-refl)

    start₂ : S₂.Start hidden₁.G hidden₂.st⁰
    start₂ .S₂.into-start q = fixed₁ .OutOfHidden.edge input q
    start₂ .S₂.interior-start p q = fixed₂ .IntoHidden₂.edge p (inj₁ q)
    start₂ .S₂.tgt-start (inj₁ q) =
      ≈-trans (done₁ .S₁.tgt-ok (inj₁ q))
              (factor (Graph.from-input 𝒢₃ q) from-inputs₃ from-root₁ {h = hidden₁.st .S₁.from-input ε} {c = collapse 𝒢₁} inputs₁ κ₁)
    start₂ .S₂.tgt-start (inj₂ _) =
      ≈-trans {g = input-to-output +ₘ (up₁ ∘ (hidden₁.st .S₁.from-input ε ∘ inputs₁))}
              (done₁ .S₁.tgt-ok (inj₂ tt))
              (+ₘ-cong ≈-refl (∘-cong₂ {f = up₁} (∘-cong₁ {g = inputs₁} κ₁)))
    start₂ .S₂.up-start (inj₁ q) = fixed₂ .IntoHidden₂.edge ε (inj₂ (inj₁ q))
    start₂ .S₂.up-start (inj₂ _) = fixed₂ .IntoHidden₂.edge ε (inj₂ (inj₂ tt))
    start₂ .S₂.off-start t        ε          ne = ⊥-elimₚ (ne ≡-refl)
    start₂ .S₂.off-start (inj₁ q) (into i p) _  = fixed₂ .IntoHidden₂.edge (into i p) (inj₂ (inj₁ q))
    start₂ .S₂.off-start (inj₂ _) (into i p) _  = fixed₂ .IntoHidden₂.edge (into i p) (inj₂ (inj₂ tt))
    start₂ .S₂.sink q = root-row 𝒢₂ (inj₂ q)

    done₂ = hidden₂.done start₂
    κ₂ = ≈-trans (≡-to-≈ hidden₂.κ) (hide-paths⁺ 𝒢₂)

    hid₁₂ : Path D₁ ⊎ Path D₂ → V E
    hid₁₂ (inj₁ q) = b1 q
    hid₁₂ (inj₂ q) = b2 q

    Bh₃ : (p : Path D₃) (t : Path D₃ ⊎ Unit) → object D₃ p ⇒ vertex-object E (tgt t)
    Bh₃ p          (inj₁ q) = Graph.interior 𝒢₃ p q
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
      k₀ .IntoHidden₃.edge D          (inj₁ q) = ≈-refl
      k₀ .IntoHidden₃.edge ε          (inj₂ _) = ≈-refl {f = up₃}
      k₀ .IntoHidden₃.edge (into i p) (inj₂ _) = ≈-refl {f = εₘ}
      k₀ .IntoHidden₃.no-edge D (inj₁ w) = ≈-refl {f = εₘ}
      k₀ .IntoHidden₃.no-edge D (inj₂ w) = ≈-refl {f = εₘ}

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

    module S₃ = HidePremise 𝒢₃ (vertex-object E) (inj₁ input) b3 (λ (_ : Unit) → er) Φ₃' (λ _ → up₃)
                            (λ _ → (input-to-output +ₘ (up₁ ∘ c₁)) +ₘ (up₂ ∘ c₂))

    prem₃ : EdgeLabels (vertex-object 𝒢₃) → S₃.St
    prem₃ G .S₃.from-input q = G (inj₁ input) (inj₂ q)
    prem₃ G .S₃.interior p q = G (inj₂ p) (inj₂ q)

    module hidden₃ = S₃.Hidden hidden₂.G prem₃ (λ G w → ≡-refl)

    start₃ : S₃.Start hidden₂.G hidden₃.st⁰
    start₃ .S₃.into-start q =
      ≈-trans {g = (Graph.from-input 𝒢₃ q ∘ Φ₃₁) +ₘ ((Graph.from-input 𝒢₃ q ∘ from-root₂) ∘ (hidden₂.st .S₂.from-input ε ∘ inputs₂))}
              (done₂ .S₂.tgt-ok (inj₁ q))
              (factor (Graph.from-input 𝒢₃ q) Φ₃₁ from-root₂ {h = hidden₂.st .S₂.from-input ε} {c = collapse 𝒢₂} inputs₂ κ₂)
    start₃ .S₃.interior-start p q = fixed₃ .IntoHidden₃.edge p (inj₁ q)
    start₃ .S₃.tgt-start _ =
      ≈-trans {g = (input-to-output +ₘ (up₁ ∘ c₁)) +ₘ (up₂ ∘ (hidden₂.st .S₂.from-input ε ∘ inputs₂))}
              (done₂ .S₂.tgt-ok (inj₂ tt)) (+ₘ-cong ≈-refl (∘-cong₂ {f = up₂} (∘-cong₁ {g = inputs₂} κ₂)))
    start₃ .S₃.up-start _ = fixed₃ .IntoHidden₃.edge ε (inj₂ tt)
    start₃ .S₃.off-start _ ε          ne = ⊥-elimₚ (ne ≡-refl)
    start₃ .S₃.off-start _ (into i p) _  = fixed₃ .IntoHidden₃.edge (into i p) (inj₂ tt)
    start₃ .S₃.sink q = root-row 𝒢₃ (inj₂ q)

    l₁ l₂ l₃ : List (V E)
    l₁ = b1 ε ∷ map b1 ps₁
    l₂ = b2 ε ∷ map b2 ps₂
    l₃ = b3 ε ∷ map b3 ps₃

    lst : map inj₂ (vertices-result-first (node m n fo-output (D₁ ∷ D₂ ∷ D₃ ∷ []))) ≡ l₁ ++ (l₂ ++ l₃)
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

  agree : collapse E ≈ (((input-to-output +ₘ (up₁ ∘ c₁)) +ₘ (up₂ ∘ c₂)) +ₘ (up₃ ∘ (collapse 𝒢₃ ∘ Φ₃)))
  agree =
    ≈-trans (≡-to-≈ plumb)
            (≈-trans {g = ((input-to-output +ₘ (up₁ ∘ c₁)) +ₘ (up₂ ∘ c₂)) +ₘ (up₃ ∘ (hidden₃.st .S₃.from-input ε ∘ Φ₃'))}
                     (hidden₃.done start₃ .S₃.tgt-ok tt)
                     (+ₘ-cong ≈-refl (∘-cong₂ {f = up₃} (∘-cong (≈-trans (≡-to-≈ hidden₃.κ) (hide-paths⁺ 𝒢₃)) Φ₃-split))))

-- A premise of a rule whose premises run in parallel.
record Premise (m n : ℕ) (D : Derivation) : Set₁ where
  constructor premise
  field
    {m𝒢}    : ℕ
    𝒢       : Graph m𝒢 D
    inputs  : 𝔽 m ⇒ 𝔽 m𝒢
    to-output      : 𝔽 (out-width D) ⇒ 𝔽 n

-- A rule with a list of premises in parallel: each premise reads the rule's inputs through its
-- own input map and reaches the root through its own up map, with no edges between premises. The
-- premises are indexed by their derivations, one per premise position of the rule's graph.
module Ruleₛ {m n : ℕ} where

  open Premise

  from-inputs : ∀ {Ds D} (Ps : All (Premise m n) Ds) (i : Ds ∋ D) (q : Path D) →
                𝔽 m ⇒ object D q
  from-inputs []       ()        _
  from-inputs (P ∷ Ps) here      q = Graph.from-input (P .𝒢) q ∘ P .inputs
  from-inputs (P ∷ Ps) (there i) q = from-inputs Ps i q

  interiors : ∀ {Ds D D'} (Ps : All (Premise m n) Ds) (i : Ds ∋ D) (p : Path D)
              (j : Ds ∋ D') (q : Path D') → object D p ⇒ object D' q
  interiors []       ()        _ _         _
  interiors (P ∷ Ps) here      p here      q = Graph.interior (P .𝒢) p q
  interiors (P ∷ Ps) here      p (there j) q = εₘ
  interiors (P ∷ Ps) (there i) p here      q = εₘ
  interiors (P ∷ Ps) (there i) p (there j) q = interiors Ps i p j q

  to-outputs : ∀ {Ds D} (Ps : All (Premise m n) Ds) (i : Ds ∋ D) (p : Path D) →
               object D p ⇒ 𝔽 n
  to-outputs []       ()        _
  to-outputs (P ∷ Ps) here      ε          = P .to-output
  to-outputs (P ∷ Ps) here      (into j p) = εₘ
  to-outputs (P ∷ Ps) (there i) p          = to-outputs Ps i p

  <-interiors : ∀ {Ds D D'} (Ps : All (Premise m n) Ds) (i : Ds ∋ D) (p : Path D)
                (j : Ds ∋ D') (q : Path D') →
                lt∋ Ds i p j q ⊎ Prf (interiors Ps i p j q ≈ εₘ)
  <-interiors []       ()        _ _         _
  <-interiors (P ∷ Ps) here      p here      q = Graph.<-interior (P .𝒢) p q
  <-interiors (P ∷ Ps) here      p (there j) q = inj₁ tt
  <-interiors (P ∷ Ps) (there i) p here      q = inj₂ ⟪ ≈-refl ⟫
  <-interiors (P ∷ Ps) (there i) p (there j) q = <-interiors Ps i p j q

  weaken-in : ∀ {b D Ds} → Input ⊎ Path (node m n b Ds) → Input ⊎ Path (node m n b (D ∷ Ds))
  weaken-in (inj₁ x) = inj₁ x
  weaken-in (inj₂ p) = inj₂ (weaken p)

  premise-in-neighbours : ∀ {b Ds D} (Ps : All (Premise m n) Ds) (i : Ds ∋ D) (q : Path D) →
                          List (Input ⊎ Path (node m n b Ds))
  premise-in-neighbours []       ()        _
  premise-in-neighbours (P ∷ Ps) here      q =
    premise-ins here (inj₁ input ∷ []) (Graph.in-neighbours (P .𝒢) q)
  premise-in-neighbours (P ∷ Ps) (there i) q = map weaken-in (premise-in-neighbours Ps i q)

  root-in-neighbours : ∀ {b Ds} → All (Premise m n) Ds → List (Input ⊎ Path (node m n b Ds))
  root-in-neighbours []       = []
  root-in-neighbours (P ∷ Ps) = inj₂ (into here ε) ∷ map weaken-in (root-in-neighbours Ps)

  parent-of : ∀ {Ds D} → All (Premise m n) Ds → Ds ∋ D → Path D → M.Table
  parent-of []       ()        _
  parent-of (P ∷ Ps) here      ε          = table-of (P .inputs)
  parent-of (P ∷ Ps) here      (into j q) = Graph.parent-to-input (P .𝒢) (into j q)
  parent-of (P ∷ Ps) (there i) q          = parent-of Ps i q

  roots-of : ∀ {b Ds D} → All (Premise m n) Ds → Ds ∋ D → Path D →
             List (Path (node m n b Ds) × M.Table)
  roots-of []       ()        _
  roots-of (P ∷ Ps) here      q = lift-roots here (Graph.roots-to-input (P .𝒢) q)
  roots-of (P ∷ Ps) (there i) q = weaken-roots (roots-of Ps i q)

  output-of : ∀ {Ds D} → All (Premise m n) Ds → Ds ∋ D → Path D → M.Table
  output-of []       ()        _
  output-of (P ∷ Ps) here      q = Graph.input-to-output (P .𝒢) q
  output-of (P ∷ Ps) (there i) q = output-of Ps i q

  E : ∀ {Ds} (fo-output : Bool) → 𝔽 m ⇒ 𝔽 n → All (Premise m n) Ds → Graph m (node m n fo-output Ds)
  E fo-output input-to-output Ps .Graph.from-input ε          = input-to-output
  E fo-output input-to-output Ps .Graph.from-input (into i q) = from-inputs Ps i q
  E fo-output input-to-output Ps .Graph.interior (into i p) (into j q) = interiors Ps i p j q
  E fo-output input-to-output Ps .Graph.interior (into i p) ε          = to-outputs Ps i p
  E fo-output input-to-output Ps .Graph.interior ε          _          = εₘ
  E fo-output input-to-output Ps .Graph.<-interior (into i p) (into j q) = <-interiors Ps i p j q
  E fo-output input-to-output Ps .Graph.<-interior (into i p) ε          = inj₁ tt
  E fo-output input-to-output Ps .Graph.<-interior ε ε          = inj₂ ⟪ ≈-refl ⟫
  E fo-output input-to-output Ps .Graph.<-interior ε (into j q) = inj₂ ⟪ ≈-refl ⟫
  E fo-output input-to-output Ps .Graph.in-neighbours ε          = inj₁ input ∷ root-in-neighbours Ps
  E fo-output input-to-output Ps .Graph.in-neighbours (into i q) = premise-in-neighbours Ps i q
  E fo-output input-to-output Ps .Graph.parent-to-input ε          = table-of (I {𝔽 m})
  E fo-output input-to-output Ps .Graph.parent-to-input (into i q) = parent-of Ps i q
  E fo-output input-to-output Ps .Graph.roots-to-input ε          = []
  E fo-output input-to-output Ps .Graph.roots-to-input (into i q) = roots-of Ps i q
  E fo-output input-to-output Ps .Graph.input-to-output ε          = table-of input-to-output
  E fo-output input-to-output Ps .Graph.input-to-output (into i q) = output-of Ps i q

  rel : ∀ {Ds} → All (Premise m n) Ds → 𝔽 m ⇒ 𝔽 n
  rel []       = εₘ
  rel (P ∷ Ps) = (P .to-output ∘ (collapse (P .𝒢) ∘ P .inputs)) +ₘ rel Ps

  -- Hiding the first premise folds its contribution into the root edge, leaving the same rule
  -- with one premise fewer; the remaining hiding is that rule's collapse read at its own vertices.
  private
    module Step {m₁ : ℕ} {D₁ : Derivation} (𝒢₁ : Graph m₁ D₁) (inputs₁ : 𝔽 m ⇒ 𝔽 m₁)
                (up₁ : 𝔽 (out-width D₁) ⇒ 𝔽 n)
                {Ds : List Derivation} (Ps : All (Premise m n) Ds)
                (fo-output : Bool) (input-to-output : 𝔽 m ⇒ 𝔽 n) where

      whole = E fo-output input-to-output (premise 𝒢₁ inputs₁ up₁ ∷ Ps)
      out' = input-to-output +ₘ (up₁ ∘ (collapse 𝒢₁ ∘ inputs₁))
      rest = E fo-output out' Ps

      private
        b1 : Path D₁ → V whole
        b1 q = inj₂ (into here q)

        bt : Path (node m n fo-output Ds) → V whole
        bt p = inj₂ (weaken p)

        er : V whole
        er = inj₂ ε

        Pt : (t : Path (node m n fo-output Ds)) → 𝔽 (out-width D₁) ⇒ vertex-object whole (bt t)
        Pt ε          = up₁
        Pt (into i q) = εₘ

        Kt : (t : Path (node m n fo-output Ds)) → 𝔽 m ⇒ vertex-object whole (bt t)
        Kt ε          = input-to-output
        Kt (into i q) = from-inputs Ps i q

        module S₁ = HidePremise 𝒢₁ (vertex-object whole) (inj₁ input) b1 bt inputs₁ Pt Kt

        prem₁ : EdgeLabels (vertex-object 𝒢₁) → S₁.St
        prem₁ G .S₁.from-input q = G (inj₁ input) (inj₂ q)
        prem₁ G .S₁.interior p q = G (inj₂ p) (inj₂ q)

        module hidden₁ = S₁.Hidden (edge-labels whole) prem₁ (λ G w → ≡-refl)

        start₁ : S₁.Start (edge-labels whole) hidden₁.st⁰
        start₁ .S₁.into-start q = ≈-refl
        start₁ .S₁.interior-start p q = ≈-refl
        start₁ .S₁.tgt-start ε          = ≈-refl {f = input-to-output}
        start₁ .S₁.tgt-start (into i q) = ≈-refl
        start₁ .S₁.up-start ε          = ≈-refl {f = up₁}
        start₁ .S₁.up-start (into i q) = ≈-refl {f = εₘ}
        start₁ .S₁.off-start t          ε          ne = ⊥-elimₚ (ne ≡-refl)
        start₁ .S₁.off-start ε          (into j p) _  = ≈-refl {f = εₘ}
        start₁ .S₁.off-start (into i q) (into j p) _  = ≈-refl {f = εₘ}
        start₁ .S₁.sink q = root-row 𝒢₁ (inj₂ q)

        done₁ = hidden₁.done start₁
        κ₁ = ≈-trans (≡-to-≈ hidden₁.κ) (hide-paths⁺ 𝒢₁)

        ps₁ = vertices-result-first D₁
        psᵣ = vertices-result-first (node m n fo-output Ds)

        Bh : (p t : Path (node m n fo-output Ds)) → vertex-object whole (bt p) ⇒ vertex-object whole (bt t)
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
        onto-rest : EdgeLabels (vertex-object whole) → EdgeLabels (vertex-object rest)
        onto-rest G (inj₁ _)            (inj₁ _)            = G (inj₁ input) (inj₁ input)
        onto-rest G (inj₁ _)            (inj₂ ε)            = G (inj₁ input) er
        onto-rest G (inj₁ _)            (inj₂ (into j q))   = G (inj₁ input) (bt (into j q))
        onto-rest G (inj₂ ε)            (inj₁ _)            = G er (inj₁ input)
        onto-rest G (inj₂ ε)            (inj₂ ε)            = G er er
        onto-rest G (inj₂ ε)            (inj₂ (into j q))   = G er (bt (into j q))
        onto-rest G (inj₂ (into i p))   (inj₁ _)            = G (bt (into i p)) (inj₁ input)
        onto-rest G (inj₂ (into i p))   (inj₂ ε)            = G (bt (into i p)) er
        onto-rest G (inj₂ (into i p))   (inj₂ (into j q))   = G (bt (into i p)) (bt (into j q))

        onto-rest-hide : ∀ G {D} (i : Ds ∋ D) (w : Path D) →
                        onto-rest (hide (vertex-object whole) G (bt (into i w))) ≐
                        hide (vertex-object rest) (onto-rest G) (inj₂ (into i w))
        onto-rest-hide G i w (inj₁ _)          (inj₁ _)          = ≈-refl
        onto-rest-hide G i w (inj₁ _)          (inj₂ ε)          = ≈-refl
        onto-rest-hide G i w (inj₁ _)          (inj₂ (into _ _)) = ≈-refl
        onto-rest-hide G i w (inj₂ ε)          (inj₁ _)          = ≈-refl
        onto-rest-hide G i w (inj₂ ε)          (inj₂ ε)          = ≈-refl
        onto-rest-hide G i w (inj₂ ε)          (inj₂ (into _ _)) = ≈-refl
        onto-rest-hide G i w (inj₂ (into _ _)) (inj₁ _)          = ≈-refl
        onto-rest-hide G i w (inj₂ (into _ _)) (inj₂ ε)          = ≈-refl
        onto-rest-hide G i w (inj₂ (into _ _)) (inj₂ (into _ _)) = ≈-refl

        onto-rest-hide-all : ∀ G ws → All (_≢ ε) ws →
                            onto-rest (hide-all (vertex-object whole) G (map bt ws)) ≐
                            hide-all (vertex-object rest) (onto-rest G) (map inj₂ ws)
        onto-rest-hide-all G []              _          x y = ≈-refl
        onto-rest-hide-all G (ε ∷ ws)        (ne ∷ _)   x y = ⊥-elimₚ (ne ≡-refl)
        onto-rest-hide-all G (into i w ∷ ws) (_ ∷ hs)   x y =
          ≈-trans (onto-rest-hide-all (hide (vertex-object whole) G (bt (into i w))) ws hs x y)
                  (hide-all-cong (vertex-object rest) (map inj₂ ws) (onto-rest-hide G i w) x y)

        agree-rest : onto-rest hidden₁.G ≐ edge-labels rest
        agree-rest (inj₁ _)          (inj₁ _)          = source₁ (inj₁ input)
        agree-rest (inj₁ _)          (inj₂ (into j q)) =
          ≈-trans (done₁ .S₁.tgt-ok (into j q))
                  (absorb₁ (from-inputs Ps j q) (hidden₁.st .S₁.from-input ε ∘ inputs₁))
        agree-rest (inj₁ _)          (inj₂ ε)          =
          ≈-trans (done₁ .S₁.tgt-ok ε)
                  (+ₘ-cong ≈-refl (∘-cong₂ {f = up₁} (∘-cong₁ {g = inputs₁} κ₁)))
        agree-rest (inj₂ (into i p)) (inj₁ _)          = source₁ (bt (into i p))
        agree-rest (inj₂ ε)          (inj₁ _)          = source₁ er
        agree-rest (inj₂ (into i p)) (inj₂ (into j q)) = fixed₁ .IntoH.edge (into i p) (into j q)
        agree-rest (inj₂ (into i p)) (inj₂ ε)          = fixed₁ .IntoH.edge (into i p) ε
        agree-rest (inj₂ ε)          (inj₂ (into j q)) = sink₁ (bt (into j q))
        agree-rest (inj₂ ε)          (inj₂ ε)          = sink₁ er

        lst : map inj₂ (vertices-result-first (node m n fo-output (D₁ ∷ Ds)))
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
        (≈-trans (onto-rest-hide-all hidden₁.G psᵣ (vertices-result-first-no-ε (node m n fo-output Ds))
                                    (inj₁ input) (inj₂ ε))
                 (hide-all-cong (vertex-object rest) (map inj₂ psᵣ) agree-rest
                                (inj₁ input) (inj₂ ε)))

  agree : ∀ {Ds} (fo-output : Bool) (input-to-output : 𝔽 m ⇒ 𝔽 n) (Ps : All (Premise m n) Ds) →
          collapse (E fo-output input-to-output Ps) ≈ (input-to-output +ₘ rel Ps)
  agree fo-output input-to-output [] = ≈-sym (+ₘ-runit input-to-output)
  agree fo-output input-to-output (P ∷ Ps) =
    ≈-trans (Step.reduce (P .𝒢) (P .inputs) (P .to-output) Ps fo-output input-to-output)
    (≈-trans (agree fo-output (input-to-output +ₘ (P .to-output ∘ (collapse (P .𝒢) ∘ P .inputs))) Ps)
             (+ₘ-assoc {f = input-to-output} {g = P .to-output ∘ (collapse (P .𝒢) ∘ P .inputs)} {h = rel Ps}))
