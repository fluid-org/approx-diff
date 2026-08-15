{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.Bool using (Bool; true; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map; foldl; filterᵇ)
open import Data.List.Relation.Unary.All using (All; []; _∷_; universal)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_) renaming (map to AllPairs-map)
import Data.List.Relation.Unary.All.Properties as AllP
import Data.List.Relation.Unary.AllPairs.Properties as AllPairsP
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
import Data.List.Relation.Binary.Permutation.Propositional as ↭
open ↭ using (_↭_)
open import Data.Unit.Polymorphic using () renaming (⊤ to Unit; tt to unit)
open import Level using (Level; Lift) renaming (suc to lsuc)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
  renaming (refl to ≡-refl; trans to ≡-trans; cong to ≡-cong; cong₂ to ≡-cong₂)
open import Relation.Nullary.Decidable using (yes)
import Data.Sum.Properties as SumP
open import basics using (IsStrictOrder)
import matrix
import two

-- A dependence graph as a value rather than a family indexed by a derivation: a graph is a set of
-- interior vertices with widths, a distinguished root of given width, and the entries between them.
-- The root has no outgoing entries, so it is a sink by construction.
module interaction.graph-algebra (ℓ : Level) where

private
  module M = matrix.Mat two.semiring

open M using (Linear; Link; ap; ap-+; ap-∘; ap-cong; at; at-+; at-∘; at-cong;
              id-linear; no-link; extend; rule₁-result; rule₂-result; rule₃-result)

open import categories using (Category)
open Category M.cat using (_∘_; _≈_; ∘-cong; ∘-cong₁; ∘-cong₂; assoc; id-left; ≈-refl; ≈-sym; ≈-trans)

≈-of-≡ : ∀ {m n} {X Y : M.Matrix m n} → X ≡ Y → X ≈ Y
≈-of-≡ ≡-refl = ≈-refl

data Root : Set ℓ where
  root : Root

Void : Set ℓ
Void = Lift ℓ ⊥

-- The completion order on a coproduct: every vertex of the first summand precedes every vertex of
-- the second.
sum-< : {A B : Set ℓ} → (A → A → Set ℓ) → (B → B → Set ℓ) → A ⊎ B → A ⊎ B → Set ℓ
sum-< R S (inj₁ p) (inj₁ q) = R p q
sum-< R S (inj₁ _) (inj₂ _) = Unit
sum-< R S (inj₂ _) (inj₁ _) = Void
sum-< R S (inj₂ p) (inj₂ q) = S p q

-- Injecting two enumerations into a coproduct keeps each vertex listed once.
sum-distinct : {A B : Set ℓ} {xs : List A} {ys : List B} →
               AllPairs _≢_ xs → AllPairs _≢_ ys →
               AllPairs _≢_ (map inj₁ xs ++ map inj₂ ys)
sum-distinct {xs = xs} {ys = ys} dx dy =
  AllPairsP.++⁺ (AllPairsP.map⁺ (AllPairs-map (λ h e → h (SumP.inj₁-injective e)) dx))
                (AllPairsP.map⁺ (AllPairs-map (λ h e → h (SumP.inj₂-injective e)) dy))
                (AllP.map⁺ (universal (λ _ → AllP.map⁺ (universal (λ _ ()) ys)) xs))

none-order : {A : Set ℓ} → IsStrictOrder {A = A} (λ _ _ → Void)
none-order .IsStrictOrder.trans _ _ _ ()
none-order .IsStrictOrder.asym _ _ ()

sum-<-order : {A B : Set ℓ} {R : A → A → Set ℓ} {S : B → B → Set ℓ} →
              IsStrictOrder R → IsStrictOrder S → IsStrictOrder (sum-< R S)
sum-<-order o₁ o₂ .IsStrictOrder.trans (inj₁ p) (inj₁ q) (inj₁ r) a b =
  o₁ .IsStrictOrder.trans p q r a b
sum-<-order o₁ o₂ .IsStrictOrder.trans (inj₁ p) (inj₁ q) (inj₂ r) a b = unit
sum-<-order o₁ o₂ .IsStrictOrder.trans (inj₁ p) (inj₂ q) (inj₁ r) a ()
sum-<-order o₁ o₂ .IsStrictOrder.trans (inj₁ p) (inj₂ q) (inj₂ r) a b = unit
sum-<-order o₁ o₂ .IsStrictOrder.trans (inj₂ p) (inj₁ q) r        () b
sum-<-order o₁ o₂ .IsStrictOrder.trans (inj₂ p) (inj₂ q) (inj₁ r) a ()
sum-<-order o₁ o₂ .IsStrictOrder.trans (inj₂ p) (inj₂ q) (inj₂ r) a b =
  o₂ .IsStrictOrder.trans p q r a b
sum-<-order o₁ o₂ .IsStrictOrder.asym (inj₁ p) (inj₁ q) a b = o₁ .IsStrictOrder.asym p q a b
sum-<-order o₁ o₂ .IsStrictOrder.asym (inj₁ p) (inj₂ q) a ()
sum-<-order o₁ o₂ .IsStrictOrder.asym (inj₂ p) (inj₁ q) () b
sum-<-order o₁ o₂ .IsStrictOrder.asym (inj₂ p) (inj₂ q) a b = o₂ .IsStrictOrder.asym p q a b

root-≟ : DecidableEquality Root
root-≟ root root = yes ≡-refl

void-≟ : DecidableEquality Void
void-≟ ()

record Graph (Inp : Set ℓ) (iw : Inp → ℕ) (n : ℕ) : Set (lsuc ℓ) where
  field
    Path    : Set ℓ
    width   : Path → ℕ
    fo      : Path → Bool
    _≟_     : DecidableEquality Path
    paths   : List Path
    -- The enumeration lists each interior vertex once.
    distinct : AllPairs _≢_ paths
    into    : (i : Inp) (q : Path) → M.Matrix (width q) (iw i)
    inside  : (p q : Path) → M.Matrix (width q) (width p)
    -- Completion order: every entry between interior vertices runs strictly forward in it, and the
    -- inputs and the root need no condition, being below and above everything.
    _<_      : Path → Path → Set ℓ
    <-order  : IsStrictOrder _<_
    <-inside : ∀ p q (k : Fin (width q)) (l : Fin (width p)) →
               inside p q k l ≡ two.I → p < q
    fo-root : Bool
    out     : (i : Inp) → M.Matrix n (iw i)
    up      : (p : Path) → M.Matrix n (width p)

-- Entries over an arbitrary vertex set, and hiding, as in interaction.hide-algebra but stated at
-- the ≈ of the matrix category rather than entrywise.
Entries : {V : Set ℓ} → (V → ℕ) → Set ℓ
Entries {V} vw = (x y : V) → M.Matrix (vw y) (vw x)

hide : {V : Set ℓ} (vw : V → ℕ) → Entries vw → V → Entries vw
hide vw G r x y = G x y M.+ₘ (G r y ∘ G x r)

hide-all : {V : Set ℓ} (vw : V → ℕ) → Entries vw → List V → Entries vw
hide-all vw = foldl (hide vw)

_≐_ : {V : Set ℓ} {vw : V → ℕ} → Entries vw → Entries vw → Prop ℓ
_≐_ {V} G G' = ∀ x y → G x y ≈ G' x y

hide-cong : {V : Set ℓ} (vw : V → ℕ) {G G' : Entries vw} (r : V) →
            G ≐ G' → hide vw G r ≐ hide vw G' r
hide-cong vw r e x y = M.+ₘ-cong (e x y) (∘-cong (e r y) (e x r))

hide-all-cong : {V : Set ℓ} (vw : V → ℕ) {G G' : Entries vw} (rs : List V) →
                G ≐ G' → hide-all vw G rs ≐ hide-all vw G' rs
hide-all-cong vw []       e = e
hide-all-cong vw (r ∷ rs) e = hide-all-cong vw rs (hide-cong vw r e)

-- Hiding a sink leaves every entry unchanged.
hide-sink : {V : Set ℓ} (vw : V → ℕ) (G : Entries vw) (r : V) →
            (∀ y → G r y ≈ M.εₘ) → hide vw G r ≐ G
hide-sink vw G r z x y = ≈-trans (M.+ₘ-cong ≈-refl (∘-cong₁ (z y))) (M.absorb₁ (G x y) (G x r))

hide-all-++ : {V : Set ℓ} (vw : V → ℕ) (G : Entries vw) (xs ys : List V) →
              hide-all vw G (xs ++ ys) ≡ hide-all vw (hide-all vw G xs) ys
hide-all-++ vw G []       ys = ≡-refl
hide-all-++ vw G (x ∷ xs) ys = hide-all-++ vw (hide vw G x) xs ys

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
module Ordered {V : Set ℓ} (vw : V → ℕ) (_<_ : V → V → Set ℓ) (o : IsStrictOrder _<_) where

  open IsStrictOrder o using (trans; asym)

  Fwd : Entries vw → Set ℓ
  Fwd G = ∀ x y (i : Fin (vw y)) (j : Fin (vw x)) → G x y i j ≡ two.I → x < y

  private
    _≐e_ : Entries vw → Entries vw → Set ℓ
    G ≐e G' = ∀ x y (i : Fin (vw y)) (j : Fin (vw x)) → G x y i j ≡ G' x y i j

    fold-cong : ∀ {G G'} rs → G ≐e G' → hide-all vw G rs ≐e hide-all vw G' rs
    fold-cong []       e = e
    fold-cong (r ∷ rs) e =
      fold-cong rs (λ x y i j → ≡-cong₂ two._⊔_ (e x y i j)
                                 (M.Σ-cong-≡ (λ k → ≡-cong₂ two._⊓_ (e r y i k) (e x r k j))))

  fwd-hide : ∀ {G} r → Fwd G → Fwd (hide vw G r)
  fwd-hide {G} r fwd x y i j e with two.⊔-I (G x y i j) ((G r y ∘ G x r) i j) e
  ... | inj₁ a = fwd x y i j a
  ... | inj₂ a with ∘-I (G r y) (G x r) i j a
  ...   | (k , (e₁ , e₂)) = trans x r y (fwd x r k j e₂) (fwd r y i k e₁)

  fwd-hide-all : ∀ {G} rs → Fwd G → Fwd (hide-all vw G rs)
  fwd-hide-all []       fwd = fwd
  fwd-hide-all (r ∷ rs) fwd = fwd-hide-all rs (fwd-hide r fwd)

  private
    into : ∀ {G} → Fwd G → ∀ r r' x y (i : Fin (vw y)) (j : Fin (vw x)) →
           hide vw (hide vw G r) r' x y i j ≡ two.I →
           hide vw (hide vw G r') r x y i j ≡ two.I
    into {G} fwd r r' x y i j e
      with two.⊔-I (hide vw G r x y i j) ((hide vw G r r' y ∘ hide vw G r x r') i j) e
    into {G} fwd r r' x y i j e | inj₁ a with two.⊔-I (G x y i j) ((G r y ∘ G x r) i j) a
    ... | inj₁ a₁ = two.⊔-I-inl (two.⊔-I-inl a₁)
    ... | inj₂ a₂ with ∘-I (G r y) (G x r) i j a₂
    ...   | (k , (e₁ , e₂)) =
      two.⊔-I-inr (hide vw G r' x y i j)
        (∘-I-at (hide vw G r' r y) (hide vw G r' x r) i j k (two.⊔-I-inl e₁) (two.⊔-I-inl e₂))
    into {G} fwd r r' x y i j e | inj₂ b
      with ∘-I (hide vw G r r' y) (hide vw G r x r') i j b
    ... | (m , (c , d)) with two.⊔-I (G r' y i m) ((G r y ∘ G r' r) i m) c
                           | two.⊔-I (G x r' m j) ((G r r' ∘ G x r) m j) d
    ...   | inj₁ c₁ | inj₁ d₁ =
      two.⊔-I-inl (two.⊔-I-inr (G x y i j) (∘-I-at (G r' y) (G x r') i j m c₁ d₁))
    ...   | inj₁ c₁ | inj₂ d₂ with ∘-I (G r r') (G x r) m j d₂
    ...     | (k , (d₁' , d₂')) =
      two.⊔-I-inr (hide vw G r' x y i j)
        (∘-I-at (hide vw G r' r y) (hide vw G r' x r) i j k
          (two.⊔-I-inr (G r y i k) (∘-I-at (G r' y) (G r r') i k m c₁ d₁'))
          (two.⊔-I-inl d₂'))
    into {G} fwd r r' x y i j e | inj₂ b | (m , (c , d)) | inj₂ c₂ | inj₁ d₁
      with ∘-I (G r y) (G r' r) i m c₂
    ...     | (k , (c₁' , c₂')) =
      two.⊔-I-inr (hide vw G r' x y i j)
        (∘-I-at (hide vw G r' r y) (hide vw G r' x r) i j k
          (two.⊔-I-inl c₁')
          (two.⊔-I-inr (G x r k j) (∘-I-at (G r' r) (G x r') k j m c₂' d₁)))
    into {G} fwd r r' x y i j e | inj₂ b | (m , (c , d)) | inj₂ c₂ | inj₂ d₂
      with ∘-I (G r y) (G r' r) i m c₂ | ∘-I (G r r') (G x r) m j d₂
    ...     | (k , (_ , c₂')) | (k' , (d₁' , _)) =
      ⊥-elim (asym r' r (fwd r' r k m c₂') (fwd r r' m k' d₁'))

    comm : ∀ {G} → Fwd G → ∀ r r' x y (i : Fin (vw y)) (j : Fin (vw x)) →
           hide vw (hide vw G r) r' x y i j ≡ hide vw (hide vw G r') r x y i j
    comm fwd r r' x y i j = two.I-antisym (into fwd r r' x y i j) (into fwd r' r x y i j)

  hide-all-perm : ∀ {G rs rs'} → Fwd G → rs ↭ rs' → hide-all vw G rs ≐e hide-all vw G rs'
  hide-all-perm fwd ↭.refl x y i j = ≡-refl
  hide-all-perm fwd (↭.prep r p) = hide-all-perm (fwd-hide r fwd) p
  hide-all-perm fwd (↭.swap {xs = rs} a b p) x y i j =
    ≡-trans (fold-cong rs (comm fwd a b) x y i j)
            (hide-all-perm (fwd-hide a (fwd-hide b fwd)) p x y i j)
  hide-all-perm fwd (↭.trans p q) x y i j =
    ≡-trans (hide-all-perm fwd p x y i j) (hide-all-perm fwd q x y i j)

module _ {Inp : Set ℓ} {iw : Inp → ℕ} {n : ℕ} (B : Graph Inp iw n) where
  open Graph B

  -- The interior vertices with the root adjoined: what a graph contributes to a larger graph.
  Path⁺ : Set ℓ
  Path⁺ = Path ⊎ Root

  width⁺ : Path⁺ → ℕ
  width⁺ = [ width , (λ _ → n) ]

  fo⁺ : Path⁺ → Bool
  fo⁺ = [ fo , (λ _ → fo-root) ]

  _≟⁺_ : DecidableEquality Path⁺
  _≟⁺_ = SumP.≡-dec _≟_ root-≟

  into⁺ : (i : Inp) (q : Path⁺) → M.Matrix (width⁺ q) (iw i)
  into⁺ i (inj₁ q) = into i q
  into⁺ i (inj₂ _) = out i

  inside⁺ : (p q : Path⁺) → M.Matrix (width⁺ q) (width⁺ p)
  inside⁺ (inj₁ p) (inj₁ q) = inside p q
  inside⁺ (inj₁ p) (inj₂ _) = up p
  inside⁺ (inj₂ _) _        = M.εₘ

  _<⁺_ : Path⁺ → Path⁺ → Set ℓ
  _<⁺_ = sum-< _<_ (λ _ _ → Void)

  <⁺-order : IsStrictOrder _<⁺_
  <⁺-order = sum-<-order <-order none-order

  <⁺-inside : ∀ p q (k : Fin (width⁺ q)) (l : Fin (width⁺ p)) →
              inside⁺ p q k l ≡ two.I → p <⁺ q
  <⁺-inside (inj₁ p) (inj₁ q) k l h = <-inside p q k l h
  <⁺-inside (inj₁ p) (inj₂ _) k l h = unit
  <⁺-inside (inj₂ _) q        k l ()

  paths⁺ : List Path⁺
  paths⁺ = inj₂ root ∷ map inj₁ paths

  distinct⁺ : AllPairs _≢_ paths⁺
  distinct⁺ =
    AllP.map⁺ (universal (λ _ ()) paths)
    ∷ AllPairsP.map⁺ (AllPairs-map (λ h e → h (SumP.inj₁-injective e)) distinct)

  V : Set ℓ
  V = Inp ⊎ Path⁺

  vw : V → ℕ
  vw = [ iw , width⁺ ]

  gr : Entries vw
  gr (inj₁ i) (inj₂ q) = into⁺ i q
  gr (inj₂ p) (inj₂ q) = inside⁺ p q
  gr _        (inj₁ _) = M.εₘ

  collapse : (i : Inp) → M.Matrix n (iw i)
  collapse i = hide-all vw gr (map (λ q → inj₂ (inj₁ q)) paths) (inj₁ i) (inj₂ (inj₂ root))

  -- The interior vertices whose values are first-order, and their complement.
  FO : List Path
  FO = filterᵇ fo paths

  fo-hidden : List Path
  fo-hidden = filterᵇ (λ q → not (fo q)) paths

  -- The first-order graph: every intermediate whose value is not first-order is hidden, so the
  -- live vertices are the inputs, the root and FO.
  fo-graph : Entries vw
  fo-graph = hide-all vw gr (map (λ q → inj₂ (inj₁ q)) fo-hidden)

  -- The completion order on all the vertices: the inputs first, then the interior, then the root.
  _<ᵥ_ : V → V → Set ℓ
  _<ᵥ_ = sum-< (λ _ _ → Void) _<⁺_

  <ᵥ-order : IsStrictOrder _<ᵥ_
  <ᵥ-order = sum-<-order none-order <⁺-order

  private
    module O = Ordered vw _<ᵥ_ <ᵥ-order

  open O public using (Fwd; fwd-hide; fwd-hide-all; hide-all-perm)

  -- Every entry of a graph runs strictly forward, and the first-order graph inherits it.
  gr-forward : Fwd gr
  gr-forward (inj₁ i) (inj₂ q) k l h = unit
  gr-forward (inj₂ p) (inj₂ q) k l h = <⁺-inside p q k l h
  gr-forward (inj₁ i) (inj₁ _) k l ()
  gr-forward (inj₂ p) (inj₁ _) k l ()

  fo-forward : Fwd fo-graph
  fo-forward = fwd-hide-all (map (λ q → inj₂ (inj₁ q)) fo-hidden) gr-forward

-- Hiding one premise's vertices, one at a time, inside the conclusion's graph. The state records
-- the premise's own entries as they accumulate; Φ carries the premise's input columns to the
-- conclusion's, which for a premise evaluated in a substituted environment is not the identity.
module HidePremise
  {V : Set ℓ} (vw : V → ℕ)
  {Inp : Set ℓ} (inp : Inp → V)
  {Path : Set ℓ} (blk : Path ⊎ Root → V)
  {T : Set ℓ} (tgt : T → V)
  {Inp' : Set ℓ} {iw' : Inp' → ℕ}
  (Φ : Linear iw' (λ i → vw (inp i)))
  (P : (t : T) → M.Matrix (vw (tgt t)) (vw (blk (inj₂ root))))
  (K : (t : T) (i : Inp) → M.Matrix (vw (tgt t)) (vw (inp i)))
  where

  record St : Set ℓ where
    field
      into   : (i' : Inp') (q : Path ⊎ Root) → M.Matrix (vw (blk q)) (iw' i')
      inside : (p q : Path ⊎ Root) → M.Matrix (vw (blk q)) (vw (blk p))

  open St public

  step : St → (Path ⊎ Root) → St
  step H w .into i' q = H .into i' q M.+ₘ (H .inside w q ∘ H .into i' w)
  step H w .inside p q = H .inside p q M.+ₘ (H .inside w q ∘ H .inside p w)

  steps : St → List (Path ⊎ Root) → St
  steps = foldl step

  folds : ∀ {A V' : Set ℓ} (prem : A → St) (ι : Path ⊎ Root → V') (h' : A → V' → A) →
          (∀ G w → step (prem G) w ≡ prem (h' G (ι w))) →
          (ws : List (Path ⊎ Root)) (G : A) → steps (prem G) ws ≡ prem (foldl h' G (map ι ws))
  folds prem ι h' ok []       G = ≡-refl
  folds prem ι h' ok (w ∷ ws) G =
    ≡-trans (≡-cong (λ H → steps H ws) (ok G w)) (folds prem ι h' ok ws (h' G (ι w)))

  private
    Φ-step : ∀ (H : St) (w : (Path ⊎ Root)) (i : Inp) (q : Path ⊎ Root) →
             Φ .ap (λ i' → step H w .into i' q) i
             ≈ (Φ .ap (λ i' → H .into i' q) i M.+ₘ (H .inside w q ∘ Φ .ap (λ i' → H .into i' w) i))
    Φ-step H w i q =
      ≈-trans (Φ .ap-+ (λ i' → H .into i' q) (λ i' → H .inside w q ∘ H .into i' w) i)
              (M.+ₘ-cong ≈-refl (Φ .ap-∘ (H .inside w q) (λ i' → H .into i' w) i))

  record Agrees (G : Entries vw) (H : St) : Set ℓ where
    field
      into-ok   : ∀ i q → G (inp i) (blk q) ≈ Φ .ap (λ i' → H .into i' q) i
      inside-ok : ∀ p q → G (blk p) (blk q) ≈ H .inside p q
      tgt-ok    : ∀ t i → G (inp i) (tgt t)
                          ≈ (K t i M.+ₘ (P t ∘ Φ .ap (λ i' → H .into i' (inj₂ root)) i))
      up-ok     : ∀ t (p : Path) → G (blk (inj₁ p)) (tgt t)
                                ≈ (P t ∘ H .inside (inj₁ p) (inj₂ root))

  open Agrees public

  agrees-hide : ∀ {G H} (w : Path) → Agrees G H → Agrees (hide vw G (blk (inj₁ w))) (step H (inj₁ w))
  agrees-hide {H = H} w s .into-ok i q =
    ≈-trans (M.+ₘ-cong (s .into-ok i q) (∘-cong (s .inside-ok (inj₁ w) q) (s .into-ok i (inj₁ w))))
            (≈-sym (Φ-step H (inj₁ w) i q))
  agrees-hide w s .inside-ok p q =
    M.+ₘ-cong (s .inside-ok p q) (∘-cong (s .inside-ok (inj₁ w) q) (s .inside-ok p (inj₁ w)))
  agrees-hide {H = H} w s .tgt-ok t i =
    ≈-trans (M.offset-step {K = K t i} {P = P t}
                         {X = Φ .ap (λ i' → H .into i' (inj₂ root)) i}
                         {Y = H .inside (inj₁ w) (inj₂ root)}
                         {Z = Φ .ap (λ i' → H .into i' (inj₁ w)) i}
              (s .tgt-ok t i) (s .up-ok t w) (s .into-ok i (inj₁ w)))
            (M.+ₘ-cong ≈-refl (∘-cong₂ (≈-sym (Φ-step H (inj₁ w) i (inj₂ root)))))
  agrees-hide {H = H} w s .up-ok t p =
    M.root-step {P = P t} {X = H .inside (inj₁ p) (inj₂ root)}
              {Y = H .inside (inj₁ w) (inj₂ root)} {Z = H .inside (inj₁ p) (inj₁ w)}
      (s .up-ok t p) (s .up-ok t w) (s .inside-ok (inj₁ p) (inj₁ w))

  agrees-hide-all : ∀ {G H} (ws : List Path) → Agrees G H →
                    Agrees (hide-all vw G (map (λ w → blk (inj₁ w)) ws)) (steps H (map inj₁ ws))
  agrees-hide-all []       s = s
  agrees-hide-all (w ∷ ws) s = agrees-hide-all ws (agrees-hide w s)

  -- The entries a rule contributes, before the graph's root is hidden. Every edge from the graph to
  -- a target leaves the graph's root, which here is a matter of the vertex set rather than a lemma.
  record Start (G : Entries vw) (H : St) : Set ℓ where
    field
      into-start   : ∀ i q → G (inp i) (blk q) ≈ Φ .ap (λ i' → H .into i' q) i
      inside-start : ∀ p q → G (blk p) (blk q) ≈ H .inside p q
      tgt-start    : ∀ t i → G (inp i) (tgt t) ≈ K t i
      up-start     : ∀ t → G (blk (inj₂ root)) (tgt t) ≈ P t
      off-start    : ∀ t (p : Path) → G (blk (inj₁ p)) (tgt t) ≈ M.εₘ
      sink         : ∀ q → H .inside (inj₂ root) q ≈ M.εₘ

  open Start public

  agrees-start : ∀ {G H} → Start G H →
                 Agrees (hide vw G (blk (inj₂ root))) (step H (inj₂ root))
  agrees-start {H = H} r .into-ok i q =
    ≈-trans (M.+ₘ-cong (r .into-start i q)
                     (∘-cong (r .inside-start (inj₂ root) q) (r .into-start i (inj₂ root))))
            (≈-sym (Φ-step H (inj₂ root) i q))
  agrees-start r .inside-ok p q =
    M.+ₘ-cong (r .inside-start p q)
            (∘-cong (r .inside-start (inj₂ root) q) (r .inside-start p (inj₂ root)))
  agrees-start {H = H} r .tgt-ok t i =
    ≈-trans (M.+ₘ-cong (r .tgt-start t i)
                     (∘-cong (r .up-start t) (r .into-start i (inj₂ root))))
            (M.+ₘ-cong ≈-refl (∘-cong₂ (≈-sym unchanged)))
    where
    unchanged : Φ .ap (λ i' → step H (inj₂ root) .into i' (inj₂ root)) i
                ≈ Φ .ap (λ i' → H .into i' (inj₂ root)) i
    unchanged =
      ≈-trans (Φ-step H (inj₂ root) i (inj₂ root))
              (≈-trans (M.+ₘ-cong ≈-refl (∘-cong₁ (r .sink (inj₂ root))))
                       (M.absorb₁ (Φ .ap (λ i' → H .into i' (inj₂ root)) i)
                               (Φ .ap (λ i' → H .into i' (inj₂ root)) i)))
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

-- Rows out of vertices that have no entries into the hidden set survive hiding.
module Behind
  {V : Set ℓ} (vw : V → ℕ)
  {W : Set ℓ} (hid : W → V)
  {S : Set ℓ} (src : S → V)
  {T : Set ℓ} (col : T → V)
  (B : (s : S) (t : T) → M.Matrix (vw (col t)) (vw (src s)))
  where

  record Keeps (G : Entries vw) : Set ℓ where
    field
      keeps : ∀ s t → G (src s) (col t) ≈ B s t
      blind : ∀ s w → G (src s) (hid w) ≈ M.εₘ

  open Keeps public

  keeps-hide : ∀ {G} (w : W) → Keeps G → Keeps (hide vw G (hid w))
  keeps-hide {G} w k .keeps s t =
    ≈-trans (M.+ₘ-cong (k .keeps s t) (∘-cong₂ (k .blind s w)))
            (M.absorb₂ (B s t) (G (hid w) (col t)))
  keeps-hide {G} w k .blind s w' =
    ≈-trans (M.+ₘ-cong (k .blind s w') (∘-cong₂ (k .blind s w)))
            (M.absorb₂ M.εₘ (G (hid w) (hid w')))

  keeps-hide-all : ∀ {G} {W' : Set ℓ} (f : W' → W) (ws : List W') →
                   Keeps G → Keeps (hide-all vw G (map (λ w → hid (f w)) ws))
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
-- entries, so hiding it changes nothing.
module _ {Inp : Set ℓ} {iw : Inp → ℕ} {n : ℕ} (B : Graph Inp iw n) where

  root-row : ∀ y → gr B (inj₂ (inj₂ root)) y ≈ M.εₘ
  root-row (inj₁ _) = ≈-refl {f = M.εₘ}
  root-row (inj₂ _) = ≈-refl {f = M.εₘ}

  hide-paths⁺ : ∀ (i : Inp) →
             hide-all (vw B) (gr B) (map inj₂ (paths⁺ B)) (inj₁ i) (inj₂ (inj₂ root))
             ≈ collapse B i
  hide-paths⁺ i =
    ≈-trans (≈-of-≡ (≡-cong (λ l → hide-all (vw B) (gr B) l (inj₁ i) (inj₂ (inj₂ root)))
                            (≡-cong (inj₂ (inj₂ root) ∷_) (map-map inj₂ inj₁ (Graph.paths B)))))
            (hide-all-cong (vw B) (map (λ q → inj₂ (inj₁ q)) (Graph.paths B))
                           (hide-sink (vw B) (gr B) (inj₂ (inj₂ root)) root-row)
                           (inj₁ i) (inj₂ (inj₂ root)))

-- Two graphs in sequence: the second graph's inputs are supplied by the conclusion's inputs
-- through route and by the first graph's root through link, and the conclusion's root is fed by
-- Columns into vertices that the hidden set has no entries into survive hiding.
module Frozen
  {V : Set ℓ} (vw : V → ℕ)
  {W : Set ℓ} (hid : W → V)
  {S : Set ℓ} (src : S → V)
  {T : Set ℓ} (col : T → V)
  (B : (s : S) (t : T) → M.Matrix (vw (col t)) (vw (src s)))
  where

  record Keeps (G : Entries vw) : Set ℓ where
    field
      keeps : ∀ s t → G (src s) (col t) ≈ B s t
      blind : ∀ w t → G (hid w) (col t) ≈ M.εₘ

  open Keeps public

  keeps-hide : ∀ {G} (w : W) → Keeps G → Keeps (hide vw G (hid w))
  keeps-hide {G} w k .keeps s t =
    ≈-trans (M.+ₘ-cong (k .keeps s t) (∘-cong₁ (k .blind w t)))
            (M.absorb₁ (B s t) (G (src s) (hid w)))
  keeps-hide {G} w k .blind w' t =
    ≈-trans (M.+ₘ-cong (k .blind w' t) (∘-cong₁ (k .blind w t)))
            (M.absorb₁ M.εₘ (G (hid w') (hid w)))

  keeps-hide-all : ∀ {G} {W' : Set ℓ} (f : W' → W) (ws : List W') →
                   Keeps G → Keeps (hide-all vw G (map (λ w → hid (f w)) ws))
  keeps-hide-all f []       k = k
  keeps-hide-all f (w ∷ ws) k = keeps-hide-all f ws (keeps-hide (f w) k)


-- A rule with no premises: the root and the inputs, and nothing between.
module Rule₀
  {Inp : Set ℓ} {iw : Inp → ℕ} {n : ℕ} (fo-root : Bool)
  (out-root : (i : Inp) → M.Matrix n (iw i))
  where

  E : Graph Inp iw n
  E .Graph.Path = Void
  E .Graph.width ()
  E .Graph.fo ()
  E .Graph._≟_ = void-≟
  E .Graph.paths = []
  E .Graph.distinct = []
  E .Graph._<_ ()
  E .Graph.<-order .IsStrictOrder.trans ()
  E .Graph.<-order .IsStrictOrder.asym ()
  E .Graph.<-inside ()
  E .Graph.fo-root = fo-root
  E .Graph.into i ()
  E .Graph.inside ()
  E .Graph.out = out-root
  E .Graph.up ()

  agree : ∀ i → collapse E i ≈ out-root i
  agree i = ≈-refl {f = out-root i}

-- A rule with one premise: the conclusion's root is the premise's root through up-root, offset by
-- out-root, and the premise's inputs are the conclusion's through route.
module Rule₁
  {Inp : Set ℓ} {iw : Inp → ℕ}
  {Inp' : Set ℓ} {iw' : Inp' → ℕ} {n₀ : ℕ} (B : Graph Inp' iw' n₀)
  {n : ℕ}
  (route : Linear iw' iw)
  (fo-root : Bool)
  (out-root : (i : Inp) → M.Matrix n (iw i))
  (up-root : M.Matrix n n₀)
  where

  E : Graph Inp iw n
  E .Graph.Path = Path⁺ B
  E .Graph.width = width⁺ B
  E .Graph.fo = fo⁺ B
  E .Graph._≟_ = _≟⁺_ B
  E .Graph.paths = paths⁺ B
  E .Graph.distinct = distinct⁺ B
  E .Graph.into i q = route .ap (λ i' → into⁺ B i' q) i
  E .Graph.inside = inside⁺ B
  E .Graph._<_ = _<⁺_ B
  E .Graph.<-order = <⁺-order B
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

    module S = HidePremise (vw E) inj₁ b (λ (_ : Root) → er) route (λ _ → up-root) (λ _ → out-root)

    H⁰ : S.St
    H⁰ .S.into i' q = into⁺ B i' q
    H⁰ .S.inside p q = inside⁺ B p q

    start : S.Start (gr E) H⁰
    start .S.into-start i q = ≈-refl
    start .S.inside-start p q = ≈-refl
    start .S.tgt-start _ i = ≈-refl {f = out-root i}
    start .S.up-start _ = ≈-refl {f = up-root}
    start .S.off-start _ p = ≈-refl {f = M.εₘ}
    start .S.sink q = ≈-refl {f = M.εₘ}

    H : S.St
    H = S.steps (S.step H⁰ (inj₂ root)) (map inj₁ (Graph.paths B))

    done : S.Agrees (hide-all (vw E) (hide (vw E) (gr E) (b (inj₂ root)))
                              (map (λ w → b (inj₁ w)) (Graph.paths B))) H
    done = S.agrees-hide-all (Graph.paths B) (S.agrees-start start)

    prem : Entries (vw B) → S.St
    prem G .S.into i' q = G (inj₁ i') (inj₂ q)
    prem G .S.inside p q = G (inj₂ p) (inj₂ q)

    κ : ∀ i' → H .S.into i' (inj₂ root) ≈ collapse B i'
    κ i' =
      ≈-trans (≈-of-≡ (≡-cong (λ H' → H' .S.into i' (inj₂ root))
                              (S.folds prem inj₂ (hide (vw B)) (λ G w → ≡-refl)
                                       (paths⁺ B) (gr B))))
              (hide-paths⁺ B i')

    plumb : ∀ i → collapse E i
                  ≡ hide-all (vw E) (hide (vw E) (gr E) (b (inj₂ root)))
                             (map (λ w → b (inj₁ w)) (Graph.paths B)) (inj₁ i) er
    plumb i = ≡-cong (λ l → hide-all (vw E) (gr E) l (inj₁ i) er)
                     (≡-cong (b (inj₂ root) ∷_) (map-map b inj₁ (Graph.paths B)))

  agree : ∀ i → collapse E i ≈ rule₁-result route out-root up-root (collapse B) i
  agree i =
    ≈-trans (≈-of-≡ (plumb i))
            (≈-trans (done .S.tgt-ok root i)
                     (M.+ₘ-cong ≈-refl (∘-cong₂ (route .ap-cong κ i))))

-- Two premises in sequence: each reaches the conclusion's inputs through its own routing, and the
-- second also reaches the first premise's root through link. Both roots feed the conclusion's.
module Rule₂
  {Inp : Set ℓ} {iw : Inp → ℕ}
  {Inp₁ : Set ℓ} {iw₁ : Inp₁ → ℕ} {n₁ : ℕ} (B₁ : Graph Inp₁ iw₁ n₁)
  {Inp₂ : Set ℓ} {iw₂ : Inp₂ → ℕ} {n₂ : ℕ} (B₂ : Graph Inp₂ iw₂ n₂)
  {n : ℕ}
  (route₁ : Linear iw₁ iw)
  (route₂ : Linear iw₂ iw)
  (link : Link iw₂ n₁)
  (fo-root : Bool)
  (out-root : (i : Inp) → M.Matrix n (iw i))
  (up₁ : M.Matrix n n₁)
  (up₂ : M.Matrix n n₂)
  where

  private
    ps₁ = Graph.paths B₁
    ps₂ = Graph.paths B₂

    upE : (s : Path⁺ B₂) → M.Matrix n (width⁺ B₂ s)
    upE (inj₁ _) = M.εₘ
    upE (inj₂ _) = up₂

  E : Graph Inp iw n
  E .Graph.Path = Path⁺ B₁ ⊎ Path⁺ B₂
  E .Graph.width = [ width⁺ B₁ , width⁺ B₂ ]
  E .Graph.fo = [ fo⁺ B₁ , fo⁺ B₂ ]
  E .Graph._≟_ = SumP.≡-dec (_≟⁺_ B₁) (_≟⁺_ B₂)
  E .Graph.paths = map inj₁ (paths⁺ B₁) ++ map inj₂ (paths⁺ B₂)
  E .Graph.distinct = sum-distinct (distinct⁺ B₁) (distinct⁺ B₂)
  E .Graph.into i (inj₁ q) = route₁ .ap (λ i' → into⁺ B₁ i' q) i
  E .Graph.into i (inj₂ q) = route₂ .ap (λ i' → into⁺ B₂ i' q) i
  E .Graph.inside (inj₁ p)        (inj₁ q) = inside⁺ B₁ p q
  E .Graph.inside (inj₁ (inj₁ p)) (inj₂ q) = M.εₘ
  E .Graph.inside (inj₁ (inj₂ _)) (inj₂ q) = link .at (λ i' → into⁺ B₂ i' q)
  E .Graph.inside (inj₂ p)        (inj₁ q) = M.εₘ
  E .Graph.inside (inj₂ p)        (inj₂ q) = inside⁺ B₂ p q
  E .Graph.fo-root = fo-root
  E .Graph._<_ = sum-< (_<⁺_ B₁) (_<⁺_ B₂)
  E .Graph.<-order = sum-<-order (<⁺-order B₁) (<⁺-order B₂)
  E .Graph.<-inside (inj₁ p) (inj₁ q) k l h = <⁺-inside B₁ p q k l h
  E .Graph.<-inside (inj₁ p) (inj₂ q) k l h = unit
  E .Graph.<-inside (inj₂ p) (inj₁ q) k l ()
  E .Graph.<-inside (inj₂ p) (inj₂ q) k l h = <⁺-inside B₂ p q k l h
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

    P₁ : (t : Path⁺ B₂ ⊎ Root) → M.Matrix (vw E (tgt₁ t)) n₁
    P₁ (inj₁ q) = link .at (λ i' → into⁺ B₂ i' q)
    P₁ (inj₂ _) = up₁

    K₁ : (t : Path⁺ B₂ ⊎ Root) (i : Inp) → M.Matrix (vw E (tgt₁ t)) (iw i)
    K₁ (inj₁ q) i = route₂ .ap (λ i' → into⁺ B₂ i' q) i
    K₁ (inj₂ _) i = out-root i

    module S1 = HidePremise (vw E) inj₁ b1 tgt₁ route₁ P₁ K₁

    H₁⁰ : S1.St
    H₁⁰ .S1.into i q = into⁺ B₁ i q
    H₁⁰ .S1.inside p q = inside⁺ B₁ p q

    start₁ : S1.Start (gr E) H₁⁰
    start₁ .S1.into-start i q = ≈-refl
    start₁ .S1.inside-start p q = ≈-refl
    start₁ .S1.tgt-start (inj₁ q) i = ≈-refl
    start₁ .S1.tgt-start (inj₂ _) i = ≈-refl {f = out-root i}
    start₁ .S1.up-start (inj₁ q) = ≈-refl
    start₁ .S1.up-start (inj₂ _) = ≈-refl {f = up₁}
    start₁ .S1.off-start (inj₁ q) p = ≈-refl {f = M.εₘ}
    start₁ .S1.off-start (inj₂ _) p = ≈-refl {f = M.εₘ}
    start₁ .S1.sink q = ≈-refl {f = M.εₘ}

    G₁ : Entries (vw E)
    G₁ = hide-all (vw E) (hide (vw E) (gr E) (b1 (inj₂ root))) (map (λ w → b1 (inj₁ w)) ps₁)

    H₁ : S1.St
    H₁ = S1.steps (S1.step H₁⁰ (inj₂ root)) (map inj₁ ps₁)

    done₁ : S1.Agrees G₁ H₁
    done₁ = S1.agrees-hide-all ps₁ (S1.agrees-start start₁)

    prem₁ : Entries (vw B₁) → S1.St
    prem₁ G .S1.into i q = G (inj₁ i) (inj₂ q)
    prem₁ G .S1.inside p q = G (inj₂ p) (inj₂ q)

    κ₁ : ∀ i → H₁ .S1.into i (inj₂ root) ≈ collapse B₁ i
    κ₁ i =
      ≈-trans (≈-of-≡ (≡-cong (λ H → H .S1.into i (inj₂ root))
                              (S1.folds prem₁ inj₂ (hide (vw B₁)) (λ G w → ≡-refl)
                                        (paths⁺ B₁) (gr B₁))))
              (hide-paths⁺ B₁ i)

  -- The second premise's inputs once the first premise has collapsed.
  Φ₂ : Linear iw₂ iw
  Φ₂ = extend route₂ link (λ i → route₁ .ap (collapse B₁) i)

  private
    P₂ : (t : Root) → M.Matrix n n₂
    P₂ _ = up₂

    K₂ : (t : Root) (i : Inp) → M.Matrix n (iw i)
    K₂ _ i = out-root i M.+ₘ (up₁ ∘ route₁ .ap (collapse B₁) i)

    module S2 = HidePremise (vw E) inj₁ b2 (λ (_ : Root) → er) Φ₂ P₂ K₂

    col₂ : Path⁺ B₂ ⊎ Root → V E
    col₂ (inj₁ q) = b2 q
    col₂ (inj₂ _) = er

    Bh : (s : Path⁺ B₂) (t : Path⁺ B₂ ⊎ Root) → M.Matrix (vw E (col₂ t)) (width⁺ B₂ s)
    Bh s (inj₁ q) = inside⁺ B₂ s q
    Bh s (inj₂ _) = upE s

    module Bd = Behind (vw E) b1 b2 col₂ Bh

    keeps₀ : Bd.Keeps (gr E)
    keeps₀ .Bd.keeps s (inj₁ q) = ≈-refl
    keeps₀ .Bd.keeps s (inj₂ _) = ≈-refl {f = upE s}
    keeps₀ .Bd.blind s w = ≈-refl {f = M.εₘ}

    keeps₁ : Bd.Keeps G₁
    keeps₁ = Bd.keeps-hide-all inj₁ ps₁ (Bd.keeps-hide (inj₂ root) keeps₀)

    H₂⁰ : S2.St
    H₂⁰ .S2.into i' q = into⁺ B₂ i' q
    H₂⁰ .S2.inside p q = inside⁺ B₂ p q

    start₂ : S2.Start G₁ H₂⁰
    start₂ .S2.into-start i q =
      ≈-trans (done₁ .S1.tgt-ok (inj₁ q) i)
              (M.+ₘ-cong ≈-refl (∘-cong₂ (route₁ .ap-cong κ₁ i)))
    start₂ .S2.inside-start p q = keeps₁ .Bd.keeps p (inj₁ q)
    start₂ .S2.tgt-start _ i =
      ≈-trans (done₁ .S1.tgt-ok (inj₂ root) i)
              (M.+ₘ-cong ≈-refl (∘-cong₂ (route₁ .ap-cong κ₁ i)))
    start₂ .S2.up-start _ = keeps₁ .Bd.keeps (inj₂ root) (inj₂ root)
    start₂ .S2.off-start _ p = keeps₁ .Bd.keeps (inj₁ p) (inj₂ root)
    start₂ .S2.sink q = ≈-refl {f = M.εₘ}

    G₂ : Entries (vw E)
    G₂ = hide-all (vw E) (hide (vw E) G₁ (b2 (inj₂ root))) (map (λ w → b2 (inj₁ w)) ps₂)

    H₂ : S2.St
    H₂ = S2.steps (S2.step H₂⁰ (inj₂ root)) (map inj₁ ps₂)

    done₂ : S2.Agrees G₂ H₂
    done₂ = S2.agrees-hide-all ps₂ (S2.agrees-start start₂)

    prem₂ : Entries (vw B₂) → S2.St
    prem₂ G .S2.into i' q = G (inj₁ i') (inj₂ q)
    prem₂ G .S2.inside p q = G (inj₂ p) (inj₂ q)

    κ₂ : ∀ i' → H₂ .S2.into i' (inj₂ root) ≈ collapse B₂ i'
    κ₂ i' =
      ≈-trans (≈-of-≡ (≡-cong (λ H → H .S2.into i' (inj₂ root))
                              (S2.folds prem₂ inj₂ (hide (vw B₂)) (λ G w → ≡-refl)
                                        (paths⁺ B₂) (gr B₂))))
              (hide-paths⁺ B₂ i')

    lst : map (λ q → inj₂ {A = Inp} (inj₁ q)) (Graph.paths E)
          ≡ (b1 (inj₂ root) ∷ map (λ w → b1 (inj₁ w)) ps₁)
            ++ (b2 (inj₂ root) ∷ map (λ w → b2 (inj₁ w)) ps₂)
    lst =
      ≡-trans (map-++ (λ q → inj₂ (inj₁ q)) (map inj₁ (paths⁺ B₁)) (map inj₂ (paths⁺ B₂)))
              (≡-cong₂ _++_
                (≡-trans (map-map (λ q → inj₂ (inj₁ q)) inj₁ (paths⁺ B₁))
                         (≡-cong (b1 (inj₂ root) ∷_) (map-map b1 inj₁ ps₁)))
                (≡-trans (map-map (λ q → inj₂ (inj₁ q)) inj₂ (paths⁺ B₂))
                         (≡-cong (b2 (inj₂ root) ∷_) (map-map b2 inj₁ ps₂))))

    plumb : ∀ i → collapse E i ≡ G₂ (inj₁ i) er
    plumb i =
      ≡-trans (≡-cong (λ l → hide-all (vw E) (gr E) l (inj₁ i) er) lst)
              (≡-cong (λ G → G (inj₁ i) er)
                      (hide-all-++ (vw E) (gr E)
                        (b1 (inj₂ root) ∷ map (λ w → b1 (inj₁ w)) ps₁)
                        (b2 (inj₂ root) ∷ map (λ w → b2 (inj₁ w)) ps₂)))

  agree : ∀ i → collapse E i
                ≈ rule₂-result route₁ route₂ link out-root up₁ up₂ (collapse B₁) (collapse B₂) i
  agree i =
    ≈-trans (≈-of-≡ (plumb i))
            (≈-trans (done₂ .S2.tgt-ok root i)
                     (M.+ₘ-cong ≈-refl (∘-cong₂ (Φ₂ .ap-cong κ₂ i))))

-- Three premises in sequence, the third reaching both earlier roots. The first two have no entries
-- between them.
module Rule₃
  {Inp : Set ℓ} {iw : Inp → ℕ}
  {Inp₁ : Set ℓ} {iw₁ : Inp₁ → ℕ} {n₁ : ℕ} (B₁ : Graph Inp₁ iw₁ n₁)
  {Inp₂ : Set ℓ} {iw₂ : Inp₂ → ℕ} {n₂ : ℕ} (B₂ : Graph Inp₂ iw₂ n₂)
  {Inp₃ : Set ℓ} {iw₃ : Inp₃ → ℕ} {n₃ : ℕ} (B₃ : Graph Inp₃ iw₃ n₃)
  {n : ℕ}
  (route₁ : Linear iw₁ iw)
  (route₂ : Linear iw₂ iw)
  (route₃ : Linear iw₃ iw)
  (link₁ : Link iw₃ n₁)
  (link₂ : Link iw₃ n₂)
  (fo-root : Bool)
  (out-root : (i : Inp) → M.Matrix n (iw i))
  (up₁ : M.Matrix n n₁)
  (up₂ : M.Matrix n n₂)
  (up₃ : M.Matrix n n₃)
  where

  private
    ps₁ = Graph.paths B₁
    ps₂ = Graph.paths B₂
    ps₃ = Graph.paths B₃

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
    e₁₃ (inj₂ _) q = link₁ .at (λ i' → into⁺ B₃ i' q)

    e₂₃ : (p : Path⁺ B₂) (q : Path⁺ B₃) → M.Matrix (width⁺ B₃ q) (width⁺ B₂ p)
    e₂₃ (inj₁ _) q = M.εₘ
    e₂₃ (inj₂ _) q = link₂ .at (λ i' → into⁺ B₃ i' q)

  E : Graph Inp iw n
  E .Graph.Path = Path⁺ B₁ ⊎ (Path⁺ B₂ ⊎ Path⁺ B₃)
  E .Graph.width = [ width⁺ B₁ , [ width⁺ B₂ , width⁺ B₃ ] ]
  E .Graph.fo = [ fo⁺ B₁ , [ fo⁺ B₂ , fo⁺ B₃ ] ]
  E .Graph._≟_ = SumP.≡-dec (_≟⁺_ B₁) (SumP.≡-dec (_≟⁺_ B₂) (_≟⁺_ B₃))
  E .Graph.paths =
    map inj₁ (paths⁺ B₁) ++ map inj₂ (map inj₁ (paths⁺ B₂) ++ map inj₂ (paths⁺ B₃))
  E .Graph.distinct = sum-distinct (distinct⁺ B₁) (sum-distinct (distinct⁺ B₂) (distinct⁺ B₃))
  E .Graph.into i (inj₁ q)        = route₁ .ap (λ i' → into⁺ B₁ i' q) i
  E .Graph.into i (inj₂ (inj₁ q)) = route₂ .ap (λ i' → into⁺ B₂ i' q) i
  E .Graph.into i (inj₂ (inj₂ q)) = route₃ .ap (λ i' → into⁺ B₃ i' q) i
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
  E .Graph._<_ = sum-< (_<⁺_ B₁) (sum-< (_<⁺_ B₂) (_<⁺_ B₃))
  E .Graph.<-order = sum-<-order (<⁺-order B₁) (sum-<-order (<⁺-order B₂) (<⁺-order B₃))
  E .Graph.<-inside (inj₁ p)        (inj₁ q)        k l h = <⁺-inside B₁ p q k l h
  E .Graph.<-inside (inj₁ p)        (inj₂ q)        k l h = unit
  E .Graph.<-inside (inj₂ (inj₁ p)) (inj₁ q)        k l ()
  E .Graph.<-inside (inj₂ (inj₂ p)) (inj₁ q)        k l ()
  E .Graph.<-inside (inj₂ (inj₁ p)) (inj₂ (inj₁ q)) k l h = <⁺-inside B₂ p q k l h
  E .Graph.<-inside (inj₂ (inj₁ p)) (inj₂ (inj₂ q)) k l h = unit
  E .Graph.<-inside (inj₂ (inj₂ p)) (inj₂ (inj₁ q)) k l ()
  E .Graph.<-inside (inj₂ (inj₂ p)) (inj₂ (inj₂ q)) k l h = <⁺-inside B₃ p q k l h
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

    c₁ : (i : Inp) → M.Matrix n₁ (iw i)
    c₁ i = route₁ .ap (collapse B₁) i

    c₂ : (i : Inp) → M.Matrix n₂ (iw i)
    c₂ i = route₂ .ap (collapse B₂) i

    P₁ : (t : Path⁺ B₃ ⊎ Root) → M.Matrix (vw E (tgt t)) n₁
    P₁ (inj₁ q) = link₁ .at (λ i' → into⁺ B₃ i' q)
    P₁ (inj₂ _) = up₁

    K₁ : (t : Path⁺ B₃ ⊎ Root) (i : Inp) → M.Matrix (vw E (tgt t)) (iw i)
    K₁ (inj₁ q) i = route₃ .ap (λ i' → into⁺ B₃ i' q) i
    K₁ (inj₂ _) i = out-root i

    module S1 = HidePremise (vw E) inj₁ b1 tgt route₁ P₁ K₁

    H₁⁰ : S1.St
    H₁⁰ .S1.into i q = into⁺ B₁ i q
    H₁⁰ .S1.inside p q = inside⁺ B₁ p q

    start₁ : S1.Start (gr E) H₁⁰
    start₁ .S1.into-start i q = ≈-refl
    start₁ .S1.inside-start p q = ≈-refl
    start₁ .S1.tgt-start (inj₁ q) i = ≈-refl
    start₁ .S1.tgt-start (inj₂ _) i = ≈-refl {f = out-root i}
    start₁ .S1.up-start (inj₁ q) = ≈-refl
    start₁ .S1.up-start (inj₂ _) = ≈-refl {f = up₁}
    start₁ .S1.off-start (inj₁ q) p = ≈-refl {f = M.εₘ}
    start₁ .S1.off-start (inj₂ _) p = ≈-refl {f = M.εₘ}
    start₁ .S1.sink q = ≈-refl {f = M.εₘ}

    G₁ : Entries (vw E)
    G₁ = hide-all (vw E) (hide (vw E) (gr E) (b1 (inj₂ root))) (map (λ w → b1 (inj₁ w)) ps₁)

    H₁ : S1.St
    H₁ = S1.steps (S1.step H₁⁰ (inj₂ root)) (map inj₁ ps₁)

    done₁ : S1.Agrees G₁ H₁
    done₁ = S1.agrees-hide-all ps₁ (S1.agrees-start start₁)

    prem₁ : Entries (vw B₁) → S1.St
    prem₁ G .S1.into i q = G (inj₁ i) (inj₂ q)
    prem₁ G .S1.inside p q = G (inj₂ p) (inj₂ q)

    κ₁ : ∀ i → H₁ .S1.into i (inj₂ root) ≈ collapse B₁ i
    κ₁ i =
      ≈-trans (≈-of-≡ (≡-cong (λ H → H .S1.into i (inj₂ root))
                              (S1.folds prem₁ inj₂ (hide (vw B₁)) (λ G w → ≡-refl)
                                        (paths⁺ B₁) (gr B₁))))
              (hide-paths⁺ B₁ i)

    -- The second premise's columns are untouched by the first premise's sweep.
    module Fz = Frozen (vw E) b1 inj₁ b2 (λ i q → route₂ .ap (λ i' → into⁺ B₂ i' q) i)

    frozen₀ : Fz.Keeps (gr E)
    frozen₀ .Fz.keeps i q = ≈-refl
    frozen₀ .Fz.blind w q = ≈-refl {f = M.εₘ}

    frozen₁ : Fz.Keeps G₁
    frozen₁ = Fz.keeps-hide-all inj₁ ps₁ (Fz.keeps-hide (inj₂ root) frozen₀)

    -- The second and third premises' rows are untouched by earlier sweeps.
    cols₂ : Path⁺ B₂ ⊎ (Path⁺ B₃ ⊎ Root) → V E
    cols₂ (inj₁ q) = b2 q
    cols₂ (inj₂ t) = tgt t

    Bh₂ : (s : Path⁺ B₂) (t : Path⁺ B₂ ⊎ (Path⁺ B₃ ⊎ Root)) → M.Matrix (vw E (cols₂ t)) (width⁺ B₂ s)
    Bh₂ s (inj₁ q)        = inside⁺ B₂ s q
    Bh₂ s (inj₂ (inj₁ q)) = e₂₃ s q
    Bh₂ s (inj₂ (inj₂ _)) = r₂ s

    module Bd₂ = Behind (vw E) b1 b2 cols₂ Bh₂

    behind₂ : Bd₂.Keeps G₁
    behind₂ = Bd₂.keeps-hide-all inj₁ ps₁ (Bd₂.keeps-hide (inj₂ root) k₀)
      where
      k₀ : Bd₂.Keeps (gr E)
      k₀ .Bd₂.keeps s (inj₁ q)        = ≈-refl
      k₀ .Bd₂.keeps s (inj₂ (inj₁ q)) = ≈-refl {f = e₂₃ s q}
      k₀ .Bd₂.keeps s (inj₂ (inj₂ _)) = ≈-refl {f = r₂ s}
      k₀ .Bd₂.blind s w = ≈-refl {f = M.εₘ}

    Φ₃₁ : Linear iw₃ iw
    Φ₃₁ = extend route₃ link₁ c₁

    P₂ : (t : Path⁺ B₃ ⊎ Root) → M.Matrix (vw E (tgt t)) n₂
    P₂ (inj₁ q) = link₂ .at (λ i' → into⁺ B₃ i' q)
    P₂ (inj₂ _) = up₂

    K₂ : (t : Path⁺ B₃ ⊎ Root) (i : Inp) → M.Matrix (vw E (tgt t)) (iw i)
    K₂ (inj₁ q) i = Φ₃₁ .ap (λ i' → into⁺ B₃ i' q) i
    K₂ (inj₂ _) i = out-root i M.+ₘ (up₁ ∘ c₁ i)

    module S2 = HidePremise (vw E) inj₁ b2 tgt route₂ P₂ K₂

    H₂⁰ : S2.St
    H₂⁰ .S2.into i q = into⁺ B₂ i q
    H₂⁰ .S2.inside p q = inside⁺ B₂ p q

    start₂ : S2.Start G₁ H₂⁰
    start₂ .S2.into-start i q = frozen₁ .Fz.keeps i q
    start₂ .S2.inside-start p q = behind₂ .Bd₂.keeps p (inj₁ q)
    start₂ .S2.tgt-start (inj₁ q) i =
      ≈-trans (done₁ .S1.tgt-ok (inj₁ q) i)
              (M.+ₘ-cong ≈-refl (∘-cong₂ (route₁ .ap-cong κ₁ i)))
    start₂ .S2.tgt-start (inj₂ _) i =
      ≈-trans (done₁ .S1.tgt-ok (inj₂ root) i)
              (M.+ₘ-cong ≈-refl (∘-cong₂ (route₁ .ap-cong κ₁ i)))
    start₂ .S2.up-start (inj₁ q) = behind₂ .Bd₂.keeps (inj₂ root) (inj₂ (inj₁ q))
    start₂ .S2.up-start (inj₂ _) = behind₂ .Bd₂.keeps (inj₂ root) (inj₂ (inj₂ root))
    start₂ .S2.off-start (inj₁ q) p = behind₂ .Bd₂.keeps (inj₁ p) (inj₂ (inj₁ q))
    start₂ .S2.off-start (inj₂ _) p = behind₂ .Bd₂.keeps (inj₁ p) (inj₂ (inj₂ root))
    start₂ .S2.sink q = ≈-refl {f = M.εₘ}

    G₂ : Entries (vw E)
    G₂ = hide-all (vw E) (hide (vw E) G₁ (b2 (inj₂ root))) (map (λ w → b2 (inj₁ w)) ps₂)

    H₂ : S2.St
    H₂ = S2.steps (S2.step H₂⁰ (inj₂ root)) (map inj₁ ps₂)

    done₂ : S2.Agrees G₂ H₂
    done₂ = S2.agrees-hide-all ps₂ (S2.agrees-start start₂)

    prem₂ : Entries (vw B₂) → S2.St
    prem₂ G .S2.into i q = G (inj₁ i) (inj₂ q)
    prem₂ G .S2.inside p q = G (inj₂ p) (inj₂ q)

    κ₂ : ∀ i → H₂ .S2.into i (inj₂ root) ≈ collapse B₂ i
    κ₂ i =
      ≈-trans (≈-of-≡ (≡-cong (λ H → H .S2.into i (inj₂ root))
                              (S2.folds prem₂ inj₂ (hide (vw B₂)) (λ G w → ≡-refl)
                                        (paths⁺ B₂) (gr B₂))))
              (hide-paths⁺ B₂ i)

    hid₁₂ : Path⁺ B₁ ⊎ Path⁺ B₂ → V E
    hid₁₂ (inj₁ q) = b1 q
    hid₁₂ (inj₂ q) = b2 q

    cols₃ : Path⁺ B₃ ⊎ Root → V E
    cols₃ = tgt

    Bh₃ : (s : Path⁺ B₃) (t : Path⁺ B₃ ⊎ Root) → M.Matrix (vw E (cols₃ t)) (width⁺ B₃ s)
    Bh₃ s (inj₁ q) = inside⁺ B₃ s q
    Bh₃ s (inj₂ _) = r₃ s

    module Bd₃ = Behind (vw E) hid₁₂ b3 cols₃ Bh₃

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

  Φ₃ : Linear iw₃ iw
  Φ₃ = extend Φ₃₁ link₂ c₂

  private
    P₃ : (t : Root) → M.Matrix n n₃
    P₃ _ = up₃

    K₃ : (t : Root) (i : Inp) → M.Matrix n (iw i)
    K₃ _ i = (out-root i M.+ₘ (up₁ ∘ c₁ i)) M.+ₘ (up₂ ∘ c₂ i)

    module S3 = HidePremise (vw E) inj₁ b3 (λ (_ : Root) → er) Φ₃ P₃ K₃

    H₃⁰ : S3.St
    H₃⁰ .S3.into i q = into⁺ B₃ i q
    H₃⁰ .S3.inside p q = inside⁺ B₃ p q

    start₃ : S3.Start G₂ H₃⁰
    start₃ .S3.into-start i q =
      ≈-trans (done₂ .S2.tgt-ok (inj₁ q) i)
              (M.+ₘ-cong ≈-refl (∘-cong₂ (route₂ .ap-cong κ₂ i)))
    start₃ .S3.inside-start p q = behind₃ .Bd₃.keeps p (inj₁ q)
    start₃ .S3.tgt-start _ i =
      ≈-trans (done₂ .S2.tgt-ok (inj₂ root) i)
              (M.+ₘ-cong ≈-refl (∘-cong₂ (route₂ .ap-cong κ₂ i)))
    start₃ .S3.up-start _ = behind₃ .Bd₃.keeps (inj₂ root) (inj₂ root)
    start₃ .S3.off-start _ p = behind₃ .Bd₃.keeps (inj₁ p) (inj₂ root)
    start₃ .S3.sink q = ≈-refl {f = M.εₘ}

    G₃ : Entries (vw E)
    G₃ = hide-all (vw E) (hide (vw E) G₂ (b3 (inj₂ root))) (map (λ w → b3 (inj₁ w)) ps₃)

    H₃ : S3.St
    H₃ = S3.steps (S3.step H₃⁰ (inj₂ root)) (map inj₁ ps₃)

    done₃ : S3.Agrees G₃ H₃
    done₃ = S3.agrees-hide-all ps₃ (S3.agrees-start start₃)

    prem₃ : Entries (vw B₃) → S3.St
    prem₃ G .S3.into i q = G (inj₁ i) (inj₂ q)
    prem₃ G .S3.inside p q = G (inj₂ p) (inj₂ q)

    κ₃ : ∀ i → H₃ .S3.into i (inj₂ root) ≈ collapse B₃ i
    κ₃ i =
      ≈-trans (≈-of-≡ (≡-cong (λ H → H .S3.into i (inj₂ root))
                              (S3.folds prem₃ inj₂ (hide (vw B₃)) (λ G w → ≡-refl)
                                        (paths⁺ B₃) (gr B₃))))
              (hide-paths⁺ B₃ i)

    l₁ l₂ l₃ : List (V E)
    l₁ = b1 (inj₂ root) ∷ map (λ w → b1 (inj₁ w)) ps₁
    l₂ = b2 (inj₂ root) ∷ map (λ w → b2 (inj₁ w)) ps₂
    l₃ = b3 (inj₂ root) ∷ map (λ w → b3 (inj₁ w)) ps₃

    lst : map (λ q → inj₂ {A = Inp} (inj₁ q)) (Graph.paths E) ≡ l₁ ++ (l₂ ++ l₃)
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

    plumb : ∀ i → collapse E i ≡ G₃ (inj₁ i) er
    plumb i =
      ≡-trans (≡-cong (λ l → hide-all (vw E) (gr E) l (inj₁ i) er) lst)
              (≡-trans (≡-cong (λ G → G (inj₁ i) er)
                               (hide-all-++ (vw E) (gr E) l₁ (l₂ ++ l₃)))
                       (≡-cong (λ G → G (inj₁ i) er)
                               (hide-all-++ (vw E) G₁ l₂ l₃)))

  agree : ∀ i → collapse E i
                ≈ rule₃-result route₁ route₂ route₃ link₁ link₂ out-root up₁ up₂ up₃
                              (collapse B₁) (collapse B₂) (collapse B₃) i
  agree i =
    ≈-trans (≈-of-≡ (plumb i))
            (≈-trans (done₃ .S3.tgt-ok root i)
                     (M.+ₘ-cong ≈-refl (∘-cong₂ (Φ₃ .ap-cong κ₃ i))))
