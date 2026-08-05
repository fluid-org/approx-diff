{-# OPTIONS --prop --postfix-projections --safe #-}

-- The block biproduct as vector operations: the product object is still the block order P ⊕ Q,
-- but the structure morphisms split and append selections instead of applying the block matrices,
-- so evaluation costs constant work per position rather than a matrix sum per entry lookup. This
-- is the ⊕ case of the action-primary representation of position orders, and the profiled fix for
-- the readback cost: the entry-oriented block combinators dominated both time and allocation.
open import Level using (0ℓ)
open import Data.Nat using (zero; suc) renaming (_+_ to _+ℕ_)
open import Data.Fin using (Fin; zero; suc; splitAt; join; _↑ˡ_; _↑ʳ_)
open import Data.Fin.Properties using (splitAt-↑ˡ; splitAt-↑ʳ; join-splitAt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl) renaming (sym to ≡-sym; trans to ≡-trans; cong to ≡-cong)
open import prop using (∃ₛ) renaming (_,_ to _,ₚ_)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import cmon-enriched using (Biproduct)
import matrix
import order-idempotent

module order-idempotent-blocks
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (let open CommutativeSemiring S hiding (_≈_; trans; sym; refl))
  (let open Setoid A)
  (∨-idem    : ∀ {x} → x + x ≈ x)
  (∧-idem    : ∀ {x} → x · x ≈ x)
  (⊤-add-top : ∀ {x} → ι + x ≈ ι)
  where

open CommutativeSemiring S using () renaming (trans to ≈-trans; sym to ≈-sym; refl to ≈-refl)
module M = matrix.Mat S
open matrix.Mat S using () renaming (_∘_ to _∘ₘ_)
open order-idempotent S ∨-idem ∧-idem ⊤-add-top
  using (Pos; dim; ord; _⊕_; Fixed; app; app-ε; app-+ₘ; app-∘; cmon; module SemiMod)

open SemiMod._⇒_
open SemiMod._≈m_
open Biproduct

private
  Cr = Setoid.Carrier A

-- Splitting and appending selections.
appendV : ∀ {m n} → M.Vec m → M.Vec n → M.Vec (m +ℕ n)
appendV {m} u w i with splitAt m i
... | inj₁ j = u j
... | inj₂ k = w k

leftV : ∀ {m n} → M.Vec (m +ℕ n) → M.Vec m
leftV {m} {n} v j = v (j ↑ˡ n)

rightV : ∀ {m n} → M.Vec (m +ℕ n) → M.Vec n
rightV {m} {n} v k = v (m ↑ʳ k)

appendV-↑ˡ : ∀ m n (u : M.Vec m) (w : M.Vec n) (j : Fin m) → appendV u w (j ↑ˡ n) ≈ u j
appendV-↑ˡ m n u w j rewrite splitAt-↑ˡ m j n = ≈-refl

appendV-↑ʳ : ∀ m n (u : M.Vec m) (w : M.Vec n) (k : Fin n) → appendV u w (m ↑ʳ k) ≈ w k
appendV-↑ʳ m n u w k rewrite splitAt-↑ʳ m n k = ≈-refl

-- The index of a block position, recovered from its split.
split-eqˡ : ∀ {m n} (i : Fin (m +ℕ n)) {j : Fin m} → splitAt m i ≡ inj₁ j → (j ↑ˡ n) ≡ i
split-eqˡ {m} {n} i {j} eq = ≡-trans (≡-cong (join m n) (≡-sym eq)) (join-splitAt m n i)

split-eqʳ : ∀ {m n} (i : Fin (m +ℕ n)) {k : Fin n} → splitAt m i ≡ inj₂ k → (m ↑ʳ k) ≡ i
split-eqʳ {m} {n} i {k} eq = ≡-trans (≡-cong (join m n) (≡-sym eq)) (join-splitAt m n i)

-- A sum over a block index set splits into sums over the blocks.
Σ-split : ∀ {m n} (f : Fin (m +ℕ n) → Cr) →
          M.Σ {m +ℕ n} f ≈ (M.Σ {m} (λ j → f (j ↑ˡ n)) + M.Σ {n} (λ k → f (m ↑ʳ k)))
Σ-split {zero}  {n} f = ≈-sym +-lunit
Σ-split {suc m} {n} f =
  ≈-trans (+-cong ≈-refl (Σ-split {m} {n} (λ i → f (suc i)))) (≈-sym +-assoc)

private
  Σε : ∀ {m} (f : Fin m → Cr) → M.Σ {m} (λ j → ε · f j) ≈ ε
  Σε {m} f = ≈-trans (M.Σ-cong {m} (λ j → ε-annihilₗ)) (M.Σ-ε {m})

  +ε : ∀ {x} → (x + ε) ≈ x
  +ε = ≈-trans +-comm +-lunit

-- The block matrices at split indices reduce to identity entries or zero.
in₁-↑ˡ : ∀ m n (j j' : Fin m) → M.in₁ {m} {n} (j ↑ˡ n) j' ≈ M.e j j'
in₁-↑ˡ (suc m) n zero    zero     = ≈-refl
in₁-↑ˡ (suc m) n zero    (suc j') = ≈-refl
in₁-↑ˡ (suc m) n (suc j) zero     = ≈-refl
in₁-↑ˡ (suc m) n (suc j) (suc j') = in₁-↑ˡ m n j j'

in₁-↑ʳ : ∀ m n (k : Fin n) (j' : Fin m) → M.in₁ {m} {n} (m ↑ʳ k) j' ≈ ε
in₁-↑ʳ (suc m) n k zero     = ≈-refl
in₁-↑ʳ (suc m) n k (suc j') = in₁-↑ʳ m n k j'

in₂-↑ˡ : ∀ m n (j : Fin m) (k : Fin n) → M.in₂ {m} {n} (j ↑ˡ n) k ≈ ε
in₂-↑ˡ (suc m) n zero    k = ≈-refl
in₂-↑ˡ (suc m) n (suc j) k = in₂-↑ˡ m n j k

in₂-↑ʳ : ∀ m n (k k' : Fin n) → M.in₂ {m} {n} (m ↑ʳ k) k' ≈ M.e k k'
in₂-↑ʳ zero n k k' = ≈-refl
in₂-↑ʳ (suc m) n k k' = in₂-↑ʳ m n k k'

p₁-↑ˡ : ∀ m n (j j' : Fin m) → M.p₁ {m} {n} j (j' ↑ˡ n) ≈ M.e j j'
p₁-↑ˡ (suc m) n zero    zero     = ≈-refl
p₁-↑ˡ (suc m) n zero    (suc j') = ≈-refl
p₁-↑ˡ (suc m) n (suc j) zero     = ≈-refl
p₁-↑ˡ (suc m) n (suc j) (suc j') = p₁-↑ˡ m n j j'

p₁-↑ʳ : ∀ m n (j : Fin m) (k : Fin n) → M.p₁ {m} {n} j (m ↑ʳ k) ≈ ε
p₁-↑ʳ (suc m) n zero    k = ≈-refl
p₁-↑ʳ (suc m) n (suc j) k = p₁-↑ʳ m n j k

p₂-↑ˡ : ∀ m n (k : Fin n) (j : Fin m) → M.p₂ {m} {n} k (j ↑ˡ n) ≈ ε
p₂-↑ˡ (suc m) n k zero    = ≈-refl
p₂-↑ˡ (suc m) n k (suc j) = p₂-↑ˡ m n k j

p₂-↑ʳ : ∀ m n (k k' : Fin n) → M.p₂ {m} {n} k (m ↑ʳ k') ≈ M.e k k'
p₂-↑ʳ zero n k k' = ≈-refl
p₂-↑ʳ (suc m) n k k' = p₂-↑ʳ m n k k'

-- Actions of the block matrices: projections split, injections pad with zero.
module _ (P Q : Pos) where

  private
    m = P .dim
    n = Q .dim

  p₁-app : ∀ (v : M.Vec (m +ℕ n)) (j : Fin m) → app (M.p₁ {m} {n}) v j ≈ leftV v j
  p₁-app v j =
    ≈-trans (Σ-split {m} {n} (λ i → M.p₁ j i · v i))
    (≈-trans (+-cong (M.Σ-cong {m} (λ j' → ·-cong (p₁-↑ˡ m n j j') ≈-refl))
                     (≈-trans (M.Σ-cong {n} (λ k → ·-cong (p₁-↑ʳ m n j k) ≈-refl)) (Σε {n} _)))
    (≈-trans (+-cong (M.Σ-unit j (leftV v)) ≈-refl) +ε))

  p₂-app : ∀ (v : M.Vec (m +ℕ n)) (k : Fin n) → app (M.p₂ {m} {n}) v k ≈ rightV v k
  p₂-app v k =
    ≈-trans (Σ-split {m} {n} (λ i → M.p₂ k i · v i))
    (≈-trans (+-cong (≈-trans (M.Σ-cong {m} (λ j → ·-cong (p₂-↑ˡ m n k j) ≈-refl)) (Σε {m} _))
                     (M.Σ-cong {n} (λ k' → ·-cong (p₂-↑ʳ m n k k') ≈-refl)))
    (≈-trans +-lunit (M.Σ-unit k (rightV v))))

  in₁-app-↑ˡ : ∀ (u : M.Vec m) (j : Fin m) → app (M.in₁ {m} {n}) u (j ↑ˡ n) ≈ u j
  in₁-app-↑ˡ u j =
    ≈-trans (M.Σ-cong {m} (λ j' → ·-cong (in₁-↑ˡ m n j j') ≈-refl)) (M.Σ-unit j u)

  in₁-app-↑ʳ : ∀ (u : M.Vec m) (k : Fin n) → app (M.in₁ {m} {n}) u (m ↑ʳ k) ≈ ε
  in₁-app-↑ʳ u k =
    ≈-trans (M.Σ-cong {m} (λ j' → ·-cong (in₁-↑ʳ m n k j') ≈-refl)) (Σε {m} _)

  in₂-app-↑ˡ : ∀ (w : M.Vec n) (j : Fin m) → app (M.in₂ {m} {n}) w (j ↑ˡ n) ≈ ε
  in₂-app-↑ˡ w j =
    ≈-trans (M.Σ-cong {n} (λ k → ·-cong (in₂-↑ˡ m n j k) ≈-refl)) (Σε {n} _)

  in₂-app-↑ʳ : ∀ (w : M.Vec n) (k : Fin n) → app (M.in₂ {m} {n}) w (m ↑ʳ k) ≈ w k
  in₂-app-↑ʳ w k =
    ≈-trans (M.Σ-cong {n} (λ k' → ·-cong (in₂-↑ʳ m n k k') ≈-refl)) (M.Σ-unit k w)

  -- The block order acts blockwise.
  B₁ = (M.in₁ {m} {n}) ∘ₘ (P .ord) ∘ₘ (M.p₁ {m} {n})
  B₂ = (M.in₂ {m} {n}) ∘ₘ (Q .ord) ∘ₘ (M.p₂ {m} {n})

  ⊕-app-↑ˡ : ∀ (v : M.Vec (m +ℕ n)) (j : Fin m) →
             app ((P ⊕ Q) .ord) v (j ↑ˡ n) ≈ app (P .ord) (leftV v) j
  ⊕-app-↑ˡ v j =
    ≈-trans (app-+ₘ B₁ B₂ v (j ↑ˡ n))
    (≈-trans (+-cong first second) +ε)
    where
    first : app B₁ v (j ↑ˡ n) ≈ app (P .ord) (leftV v) j
    first =
      ≈-trans (app-∘ ((M.in₁ {m} {n}) ∘ₘ (P .ord)) (M.p₁ {m} {n}) v (j ↑ˡ n))
      (≈-trans (app-∘ (M.in₁ {m} {n}) (P .ord) (app (M.p₁ {m} {n}) v) (j ↑ˡ n))
      (≈-trans (in₁-app-↑ˡ (app (P .ord) (app (M.p₁ {m} {n}) v)) j)
               (M.Σ-cong {m} (λ j' → ·-cong ≈-refl (p₁-app v j')))))

    second : app B₂ v (j ↑ˡ n) ≈ ε
    second =
      ≈-trans (app-∘ ((M.in₂ {m} {n}) ∘ₘ (Q .ord)) (M.p₂ {m} {n}) v (j ↑ˡ n))
      (≈-trans (app-∘ (M.in₂ {m} {n}) (Q .ord) (app (M.p₂ {m} {n}) v) (j ↑ˡ n))
               (in₂-app-↑ˡ (app (Q .ord) (app (M.p₂ {m} {n}) v)) j))

  ⊕-app-↑ʳ : ∀ (v : M.Vec (m +ℕ n)) (k : Fin n) →
             app ((P ⊕ Q) .ord) v (m ↑ʳ k) ≈ app (Q .ord) (rightV v) k
  ⊕-app-↑ʳ v k =
    ≈-trans (app-+ₘ B₁ B₂ v (m ↑ʳ k))
    (≈-trans (+-cong first second) +-lunit)
    where
    first : app B₁ v (m ↑ʳ k) ≈ ε
    first =
      ≈-trans (app-∘ ((M.in₁ {m} {n}) ∘ₘ (P .ord)) (M.p₁ {m} {n}) v (m ↑ʳ k))
      (≈-trans (app-∘ (M.in₁ {m} {n}) (P .ord) (app (M.p₁ {m} {n}) v) (m ↑ʳ k))
               (in₁-app-↑ʳ (app (P .ord) (app (M.p₁ {m} {n}) v)) k))

    second : app B₂ v (m ↑ʳ k) ≈ app (Q .ord) (rightV v) k
    second =
      ≈-trans (app-∘ ((M.in₂ {m} {n}) ∘ₘ (Q .ord)) (M.p₂ {m} {n}) v (m ↑ʳ k))
      (≈-trans (app-∘ (M.in₂ {m} {n}) (Q .ord) (app (M.p₂ {m} {n}) v) (m ↑ʳ k))
      (≈-trans (in₂-app-↑ʳ (app (Q .ord) (app (M.p₂ {m} {n}) v)) k)
               (M.Σ-cong {n} (λ k' → ·-cong ≈-refl (p₂-app v k')))))

  -- Down-closure at a block order, blockwise.
  ⊕-fixed-left : ∀ {v} → Fixed (P ⊕ Q) v → Fixed P (leftV v)
  ⊕-fixed-left {v} fx j = ≈-trans (≈-sym (⊕-app-↑ˡ v j)) (fx (j ↑ˡ n))

  ⊕-fixed-right : ∀ {v} → Fixed (P ⊕ Q) v → Fixed Q (rightV v)
  ⊕-fixed-right {v} fx k = ≈-trans (≈-sym (⊕-app-↑ʳ v k)) (fx (m ↑ʳ k))

  ⊕-fixed-append : ∀ {u w} → Fixed P u → Fixed Q w → Fixed (P ⊕ Q) (appendV u w)
  ⊕-fixed-append {u} {w} fu fw i with splitAt m i in eq
  ... | inj₁ j rewrite ≡-sym (split-eqˡ i eq) =
    ≈-trans (⊕-app-↑ˡ (appendV u w) j)
    (≈-trans (M.Σ-cong {m} (λ j' → ·-cong ≈-refl (appendV-↑ˡ m n u w j')))
             (fu j))
  ... | inj₂ k rewrite ≡-sym (split-eqʳ i eq) =
    ≈-trans (⊕-app-↑ʳ (appendV u w) k)
    (≈-trans (M.Σ-cong {n} (λ k' → ·-cong ≈-refl (appendV-↑ʳ m n u w k')))
             (fw k))

-- The split-and-append biproduct witness on any pair of position orders.
blocks-biproduct : ∀ P Q → Biproduct cmon P Q
blocks-biproduct P Q .prod = P ⊕ Q
blocks-biproduct P Q .p₁ .*→* .prop-setoid._⇒_.func (v ,ₚ fx) =
  leftV v ,ₚ ⊕-fixed-left P Q fx
blocks-biproduct P Q .p₁ .*→* .prop-setoid._⇒_.func-resp-≈ e j = e (j ↑ˡ Q .dim)
blocks-biproduct P Q .p₁ .preserve-ze j = ≈-refl
blocks-biproduct P Q .p₁ .preserve-+ j = ≈-refl
blocks-biproduct P Q .p₁ .preserve-· j = ≈-refl
blocks-biproduct P Q .p₂ .*→* .prop-setoid._⇒_.func (v ,ₚ fx) =
  rightV v ,ₚ ⊕-fixed-right P Q fx
blocks-biproduct P Q .p₂ .*→* .prop-setoid._⇒_.func-resp-≈ e k = e (P .dim ↑ʳ k)
blocks-biproduct P Q .p₂ .preserve-ze k = ≈-refl
blocks-biproduct P Q .p₂ .preserve-+ k = ≈-refl
blocks-biproduct P Q .p₂ .preserve-· k = ≈-refl
blocks-biproduct P Q .in₁ .*→* .prop-setoid._⇒_.func (u ,ₚ fu) =
  appendV u (λ _ → ε) ,ₚ ⊕-fixed-append P Q fu (λ k → app-ε (Q .ord) k)
blocks-biproduct P Q .in₁ .*→* .prop-setoid._⇒_.func-resp-≈ {u₁ ,ₚ _} {u₂ ,ₚ _} e i
  with splitAt (P .dim) i
... | inj₁ j = e j
... | inj₂ k = ≈-refl
blocks-biproduct P Q .in₁ .preserve-ze i with splitAt (P .dim) i
... | inj₁ j = ≈-refl
... | inj₂ k = ≈-refl
blocks-biproduct P Q .in₁ .preserve-+ i with splitAt (P .dim) i
... | inj₁ j = ≈-refl
... | inj₂ k = ≈-sym +-lunit
blocks-biproduct P Q .in₁ .preserve-· i with splitAt (P .dim) i
... | inj₁ j = ≈-refl
... | inj₂ k = ≈-sym ε-annihilᵣ
blocks-biproduct P Q .in₂ .*→* .prop-setoid._⇒_.func (w ,ₚ fw) =
  appendV (λ _ → ε) w ,ₚ ⊕-fixed-append P Q (λ j → app-ε (P .ord) j) fw
blocks-biproduct P Q .in₂ .*→* .prop-setoid._⇒_.func-resp-≈ {w₁ ,ₚ _} {w₂ ,ₚ _} e i
  with splitAt (P .dim) i
... | inj₁ j = ≈-refl
... | inj₂ k = e k
blocks-biproduct P Q .in₂ .preserve-ze i with splitAt (P .dim) i
... | inj₁ j = ≈-refl
... | inj₂ k = ≈-refl
blocks-biproduct P Q .in₂ .preserve-+ i with splitAt (P .dim) i
... | inj₁ j = ≈-sym +-lunit
... | inj₂ k = ≈-refl
blocks-biproduct P Q .in₂ .preserve-· i with splitAt (P .dim) i
... | inj₁ j = ≈-sym ε-annihilᵣ
... | inj₂ k = ≈-refl
blocks-biproduct P Q .id-1 .*≈* .prop-setoid._≃m_.func-eq {u₁ ,ₚ _} {u₂ ,ₚ _} e j =
  ≈-trans (appendV-↑ˡ (P .dim) (Q .dim) u₁ (λ _ → ε) j) (e j)
blocks-biproduct P Q .id-2 .*≈* .prop-setoid._≃m_.func-eq {w₁ ,ₚ _} {w₂ ,ₚ _} e k =
  ≈-trans (appendV-↑ʳ (P .dim) (Q .dim) (λ _ → ε) w₁ k) (e k)
blocks-biproduct P Q .zero-1 .*≈* .prop-setoid._≃m_.func-eq {w₁ ,ₚ _} {w₂ ,ₚ _} e j =
  appendV-↑ˡ (P .dim) (Q .dim) (λ _ → ε) w₁ j
blocks-biproduct P Q .zero-2 .*≈* .prop-setoid._≃m_.func-eq {u₁ ,ₚ _} {u₂ ,ₚ _} e k =
  appendV-↑ʳ (P .dim) (Q .dim) u₁ (λ _ → ε) k
blocks-biproduct P Q .id-+ .*≈* .prop-setoid._≃m_.func-eq {v₁ ,ₚ _} {v₂ ,ₚ _} e i
  with splitAt (P .dim) i in eq
... | inj₁ j rewrite ≡-sym (split-eqˡ i eq) = ≈-trans +ε (e (j ↑ˡ Q .dim))
... | inj₂ k rewrite ≡-sym (split-eqʳ i eq) = ≈-trans +-lunit (e (P .dim ↑ʳ k))
