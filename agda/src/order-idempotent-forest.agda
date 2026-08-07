{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (0ℓ)
open import Data.Nat using (ℕ; suc) renaming (_+_ to _+ℕ_)
open import Data.Fin using (Fin; zero; suc; _↑ˡ_; _↑ʳ_; splitAt)
open import Data.Fin.Properties using (_≟_; splitAt⁻¹-↑ˡ; splitAt⁻¹-↑ʳ)
open import Data.Sum using (_⊎_) renaming (inj₁ to left; inj₂ to right)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import prop using (_∨_; inj₁; inj₂)
open import prop-setoid using (Setoid)
open import basics using (IsPreorder; IsJoin; IsBottom)
open import commutative-semiring using (CommutativeSemiring)
import matrix
import order-idempotent

-- Forest orders: every ancestor set is a chain. The value fibres of the operational semantics are
-- forests, so the concrete objects can be restricted to them while the general position orders
-- remain the ambient setting. Closure under the discrete orders, the biproduct and the lifting;
-- the block entries are bounded through the biproduct laws rather than computed.
module order-idempotent-forest
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (let open CommutativeSemiring S hiding (_≈_; trans; sym; refl); open Setoid A)
  (∨-idem    : ∀ {x} → x + x ≈ x)
  (∧-idem    : ∀ {x} → x · x ≈ x)
  (⊤-add-top : ∀ {x} → ι + x ≈ ι)
  where

open order-idempotent S (λ {x} → ∨-idem {x}) (λ {x} → ∧-idem {x}) (λ {x} → ⊤-add-top {x})
open matrix.Mat S
  using (e; I; εₘ; _≈ₘ_; ∘-cong; assoc; id-right; p₁; p₂; in₁; in₂;
         id-1; id-2; zero-1; zero-2; comp-bilinear-ε₂)
  renaming (_∘_ to _∘ₘ_)
open IsPreorder L.≤-isPreorder using () renaming (refl to ≤-refl; trans to ≤-trans)

private
  ·-runit : ∀ {x} → (x · ι) ≈ x
  ·-runit = trans ·-comm ·-lunit

  ε-least : ∀ {x} → ε L.≤ x
  ε-least = IsBottom.≤-bottom L.⊥-isBottom

  ι≤ε-elim : ∀ {x} → ι L.≤ ε → ι L.≤ x
  ι≤ε-elim h = ≤-trans h ε-least

  ∨-map : {P₁ P₂ Q₁ Q₂ : Prop 0ℓ} → (P₁ → Q₁) → (P₂ → Q₂) → P₁ ∨ P₂ → Q₁ ∨ Q₂
  ∨-map f g (inj₁ x) = inj₁ (f x)
  ∨-map f g (inj₂ y) = inj₂ (g y)

-- A position order is a forest when the ancestors of any position form a chain.
Forest : Pos → Prop
Forest P = ∀ q r p → ι L.≤ P .ord q p → ι L.≤ P .ord r p →
           (ι L.≤ P .ord q r) ∨ (ι L.≤ P .ord r q)

-- The off-diagonal entries of the identity are zero.
e-off : ∀ {n} {i j : Fin n} → ¬ i ≡ j → e i j ≈ ε
e-off {i = zero}  {zero}  i≢j with i≢j PE.refl
... | ()
e-off {i = zero}  {suc j} i≢j = refl
e-off {i = suc i} {zero}  i≢j = refl
e-off {i = suc i} {suc j} i≢j = e-off (λ eq → i≢j (PE.cong suc eq))

forest-disc : ∀ n → Forest (disc n)
forest-disc n q r p hq hr with q ≟ r
... | yes PE.refl = inj₁ (L.≈→≤ (sym (I-diag q)))
... | no q≢r with q ≟ p
...   | no q≢p     = inj₁ (ι≤ε-elim (≤-trans hq (L.≈→≤ (e-off q≢p))))
...   | yes PE.refl = inₗ
  where
    inₗ = inj₁ (ι≤ε-elim (≤-trans hr (L.≈→≤ (e-off (λ r≡q → q≢r (PE.sym r≡q))))))

forest-𝟘p : Forest 𝟘p
forest-𝟘p = forest-disc 0

-- The lifting adds a root below everything, so it is comparable to every ancestor.
forest-Lp : ∀ P → Forest P → Forest (Lp P)
forest-Lp P FP zero    r       p       hq hr = inj₁ ≤-refl
forest-Lp P FP (suc q) zero    p       hq hr = inj₂ ≤-refl
forest-Lp P FP (suc q) (suc r) zero    hq hr = inj₁ (ι≤ε-elim hq)
forest-Lp P FP (suc q) (suc r) (suc p) hq hr = FP q r p hq hr

-- The selected entries of the projections and injections.
p₁-sel : ∀ {m n} (i : Fin m) → p₁ {m} {n} i (i ↑ˡ n) ≈ ι
p₁-sel zero    = refl
p₁-sel (suc i) = p₁-sel i

in₁-sel : ∀ {m n} (i : Fin m) → in₁ {m} {n} (i ↑ˡ n) i ≈ ι
in₁-sel zero    = refl
in₁-sel (suc i) = in₁-sel i

p₂-sel : ∀ m {n} (i : Fin n) → p₂ {m} {n} i (m ↑ʳ i) ≈ ι
p₂-sel ℕ.zero  i = I-diag i
p₂-sel (suc m) i = p₂-sel m i

in₂-sel : ∀ m {n} (i : Fin n) → in₂ {m} {n} (m ↑ʳ i) i ≈ ι
in₂-sel ℕ.zero  i = I-diag i
in₂-sel (suc m) i = in₂-sel m i

-- Bounds on the block order's entries: a block entry is sandwiched between a summand of the block
-- matrix and a composite that the biproduct laws collapse, so the diagonal blocks agree with the
-- component orders and the off-diagonal blocks vanish.
module Blocks (P Q : Pos) where
  private
    m = P .dim
    n = Q .dim
    M = B P Q

  ll-≤ : ∀ i k → M (i ↑ˡ n) (k ↑ˡ n) L.≤ P .ord i k
  ll-≤ i k = ≤-trans step₁ (≤-trans step₂ (L.≈→≤ (fuse i k)))
    where
    step₁ : M (i ↑ˡ n) (k ↑ˡ n) L.≤ (M ∘ₘ in₁ {m} {n}) (i ↑ˡ n) k
    step₁ = ≤-trans (L.≈→≤ (sym (trans (·-cong refl (in₁-sel k)) ·-runit)))
                    (L.Σ-ub (λ b → M (i ↑ˡ n) b · in₁ {m} {n} b k) (k ↑ˡ n))
    step₂ : (M ∘ₘ in₁ {m} {n}) (i ↑ˡ n) k L.≤ (p₁ {m} {n} ∘ₘ (M ∘ₘ in₁ {m} {n})) i k
    step₂ = ≤-trans (L.≈→≤ (sym (trans (·-cong (p₁-sel i) refl) ·-lunit)))
                    (L.Σ-ub (λ a → p₁ {m} {n} i a · (M ∘ₘ in₁ {m} {n}) a k) (i ↑ˡ n))
    fuse : (p₁ {m} {n} ∘ₘ (M ∘ₘ in₁ {m} {n})) ≈ₘ P .ord
    fuse = ≈ₘ-trans (≈ₘ-sym (assoc (p₁ {m} {n}) M (in₁ {m} {n})))
           (≈ₘ-trans (∘-cong (p₁-B P Q) (≈ₘ-refl {M = in₁ {m} {n}}))
           (≈ₘ-trans (assoc (P .ord) (p₁ {m} {n}) (in₁ {m} {n}))
           (≈ₘ-trans (∘-cong (≈ₘ-refl {M = P .ord}) (id-1 m n))
                     (id-right {M = P .ord}))))

  ll-≥ : ∀ i k → P .ord i k L.≤ M (i ↑ˡ n) (k ↑ˡ n)
  ll-≥ i k =
    ≤-trans step-a
    (≤-trans (L.≈→≤ (sym (trans (·-cong refl (p₁-sel k)) ·-runit)))
    (≤-trans (L.Σ-ub (λ a → (in₁ {m} {n} ∘ₘ P .ord) (i ↑ˡ n) a · p₁ {m} {n} a (k ↑ˡ n)) k)
             (IsJoin.inl L.∨-isJoin)))
    where
    step-a : P .ord i k L.≤ (in₁ {m} {n} ∘ₘ P .ord) (i ↑ˡ n) k
    step-a = ≤-trans (L.≈→≤ (sym (trans (·-cong (in₁-sel i) refl) ·-lunit)))
                     (L.Σ-ub (λ b → in₁ {m} {n} (i ↑ˡ n) b · P .ord b k) i)

  rr-≤ : ∀ i k → M (m ↑ʳ i) (m ↑ʳ k) L.≤ Q .ord i k
  rr-≤ i k = ≤-trans step₁ (≤-trans step₂ (L.≈→≤ (fuse i k)))
    where
    step₁ : M (m ↑ʳ i) (m ↑ʳ k) L.≤ (M ∘ₘ in₂ {m} {n}) (m ↑ʳ i) k
    step₁ = ≤-trans (L.≈→≤ (sym (trans (·-cong refl (in₂-sel m k)) ·-runit)))
                    (L.Σ-ub (λ b → M (m ↑ʳ i) b · in₂ {m} {n} b k) (m ↑ʳ k))
    step₂ : (M ∘ₘ in₂ {m} {n}) (m ↑ʳ i) k L.≤ (p₂ {m} {n} ∘ₘ (M ∘ₘ in₂ {m} {n})) i k
    step₂ = ≤-trans (L.≈→≤ (sym (trans (·-cong (p₂-sel m i) refl) ·-lunit)))
                    (L.Σ-ub (λ a → p₂ {m} {n} i a · (M ∘ₘ in₂ {m} {n}) a k) (m ↑ʳ i))
    fuse : (p₂ {m} {n} ∘ₘ (M ∘ₘ in₂ {m} {n})) ≈ₘ Q .ord
    fuse = ≈ₘ-trans (≈ₘ-sym (assoc (p₂ {m} {n}) M (in₂ {m} {n})))
           (≈ₘ-trans (∘-cong (p₂-B P Q) (≈ₘ-refl {M = in₂ {m} {n}}))
           (≈ₘ-trans (assoc (Q .ord) (p₂ {m} {n}) (in₂ {m} {n}))
           (≈ₘ-trans (∘-cong (≈ₘ-refl {M = Q .ord}) (id-2 m n))
                     (id-right {M = Q .ord}))))

  rr-≥ : ∀ i k → Q .ord i k L.≤ M (m ↑ʳ i) (m ↑ʳ k)
  rr-≥ i k =
    ≤-trans step-a
    (≤-trans (L.≈→≤ (sym (trans (·-cong refl (p₂-sel m k)) ·-runit)))
    (≤-trans (L.Σ-ub (λ a → (in₂ {m} {n} ∘ₘ Q .ord) (m ↑ʳ i) a · p₂ {m} {n} a (m ↑ʳ k)) k)
             (IsJoin.inr L.∨-isJoin)))
    where
    step-a : Q .ord i k L.≤ (in₂ {m} {n} ∘ₘ Q .ord) (m ↑ʳ i) k
    step-a = ≤-trans (L.≈→≤ (sym (trans (·-cong (in₂-sel m i) refl) ·-lunit)))
                     (L.Σ-ub (λ b → in₂ {m} {n} (m ↑ʳ i) b · Q .ord b k) i)

  lr-ε : ∀ i k → M (i ↑ˡ n) (m ↑ʳ k) L.≤ ε
  lr-ε i k = ≤-trans step₁ (≤-trans step₂ (L.≈→≤ (fuse i k)))
    where
    step₁ : M (i ↑ˡ n) (m ↑ʳ k) L.≤ (M ∘ₘ in₂ {m} {n}) (i ↑ˡ n) k
    step₁ = ≤-trans (L.≈→≤ (sym (trans (·-cong refl (in₂-sel m k)) ·-runit)))
                    (L.Σ-ub (λ b → M (i ↑ˡ n) b · in₂ {m} {n} b k) (m ↑ʳ k))
    step₂ : (M ∘ₘ in₂ {m} {n}) (i ↑ˡ n) k L.≤ (p₁ {m} {n} ∘ₘ (M ∘ₘ in₂ {m} {n})) i k
    step₂ = ≤-trans (L.≈→≤ (sym (trans (·-cong (p₁-sel i) refl) ·-lunit)))
                    (L.Σ-ub (λ a → p₁ {m} {n} i a · (M ∘ₘ in₂ {m} {n}) a k) (i ↑ˡ n))
    fuse : (p₁ {m} {n} ∘ₘ (M ∘ₘ in₂ {m} {n})) ≈ₘ εₘ
    fuse = ≈ₘ-trans (≈ₘ-sym (assoc (p₁ {m} {n}) M (in₂ {m} {n})))
           (≈ₘ-trans (∘-cong (p₁-B P Q) (≈ₘ-refl {M = in₂ {m} {n}}))
           (≈ₘ-trans (assoc (P .ord) (p₁ {m} {n}) (in₂ {m} {n}))
           (≈ₘ-trans (∘-cong (≈ₘ-refl {M = P .ord}) (zero-1 m n))
                     (comp-bilinear-ε₂ (P .ord)))))

  rl-ε : ∀ i k → M (m ↑ʳ i) (k ↑ˡ n) L.≤ ε
  rl-ε i k = ≤-trans step₁ (≤-trans step₂ (L.≈→≤ (fuse i k)))
    where
    step₁ : M (m ↑ʳ i) (k ↑ˡ n) L.≤ (M ∘ₘ in₁ {m} {n}) (m ↑ʳ i) k
    step₁ = ≤-trans (L.≈→≤ (sym (trans (·-cong refl (in₁-sel k)) ·-runit)))
                    (L.Σ-ub (λ b → M (m ↑ʳ i) b · in₁ {m} {n} b k) (k ↑ˡ n))
    step₂ : (M ∘ₘ in₁ {m} {n}) (m ↑ʳ i) k L.≤ (p₂ {m} {n} ∘ₘ (M ∘ₘ in₁ {m} {n})) i k
    step₂ = ≤-trans (L.≈→≤ (sym (trans (·-cong (p₂-sel m i) refl) ·-lunit)))
                    (L.Σ-ub (λ a → p₂ {m} {n} i a · (M ∘ₘ in₁ {m} {n}) a k) (m ↑ʳ i))
    fuse : (p₂ {m} {n} ∘ₘ (M ∘ₘ in₁ {m} {n})) ≈ₘ εₘ
    fuse = ≈ₘ-trans (≈ₘ-sym (assoc (p₂ {m} {n}) M (in₁ {m} {n})))
           (≈ₘ-trans (∘-cong (p₂-B P Q) (≈ₘ-refl {M = in₁ {m} {n}}))
           (≈ₘ-trans (assoc (Q .ord) (p₂ {m} {n}) (in₁ {m} {n}))
           (≈ₘ-trans (∘-cong (≈ₘ-refl {M = Q .ord}) (zero-2 m n))
                     (comp-bilinear-ε₂ (Q .ord)))))

-- Every index of the biproduct is an image of one of the injections.
private
  view : ∀ m {n} (i : Fin (m +ℕ n)) →
         (Σ[ i' ∈ Fin m ] (i' ↑ˡ n) ≡ i) ⊎ (Σ[ i' ∈ Fin n ] (m ↑ʳ i') ≡ i)
  view m i with splitAt m i in eq
  ... | left  i' = left  (i' , splitAt⁻¹-↑ˡ eq)
  ... | right i' = right (i' , splitAt⁻¹-↑ʳ eq)

forest-⊕ : ∀ P Q → Forest P → Forest Q → Forest (P ⊕ Q)
forest-⊕ P Q FP FQ q r p hq hr
  with view (P .dim) q | view (P .dim) r | view (P .dim) p
... | left  (q' , PE.refl) | left  (r' , PE.refl) | left  (p' , PE.refl) =
      ∨-map (λ h → ≤-trans h (Blocks.ll-≥ P Q q' r')) (λ h → ≤-trans h (Blocks.ll-≥ P Q r' q'))
            (FP q' r' p' (≤-trans hq (Blocks.ll-≤ P Q q' p')) (≤-trans hr (Blocks.ll-≤ P Q r' p')))
... | left  (q' , PE.refl) | left  (r' , PE.refl) | right (p' , PE.refl) =
      inj₁ (ι≤ε-elim (≤-trans hq (Blocks.lr-ε P Q q' p')))
... | left  (q' , PE.refl) | right (r' , PE.refl) | left  (p' , PE.refl) =
      inj₁ (ι≤ε-elim (≤-trans hr (Blocks.rl-ε P Q r' p')))
... | left  (q' , PE.refl) | right (r' , PE.refl) | right (p' , PE.refl) =
      inj₁ (ι≤ε-elim (≤-trans hq (Blocks.lr-ε P Q q' p')))
... | right (q' , PE.refl) | left  (r' , PE.refl) | left  (p' , PE.refl) =
      inj₁ (ι≤ε-elim (≤-trans hq (Blocks.rl-ε P Q q' p')))
... | right (q' , PE.refl) | left  (r' , PE.refl) | right (p' , PE.refl) =
      inj₁ (ι≤ε-elim (≤-trans hr (Blocks.lr-ε P Q r' p')))
... | right (q' , PE.refl) | right (r' , PE.refl) | left  (p' , PE.refl) =
      inj₁ (ι≤ε-elim (≤-trans hq (Blocks.rl-ε P Q q' p')))
... | right (q' , PE.refl) | right (r' , PE.refl) | right (p' , PE.refl) =
      ∨-map (λ h → ≤-trans h (Blocks.rr-≥ P Q q' r')) (λ h → ≤-trans h (Blocks.rr-≥ P Q r' q'))
            (FQ q' r' p' (≤-trans hq (Blocks.rr-≤ P Q q' p')) (≤-trans hr (Blocks.rr-≤ P Q r' p')))
