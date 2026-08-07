{-# OPTIONS --prop --postfix-projections --safe #-}

-- The rooted lifting of position orders as a biproduct: the root is one fresh position, unordered
-- against the payload, so a down-closed selection of the lifted order is a free root scalar beside
-- a down-closed selection of the payload. This replaces the dominated lifting, whose prefix
-- closure between root and payload identified every eliminator that reads a root with the support
-- map; here reading the root is the projection, distinct from reading anything else. Prefix
-- closure of reported dependencies, when wanted, is a closure applied to answers, not a property
-- of the carriers.
--
-- The biproduct witness on (𝟙p, P) is hand-written: its product object is the block order 𝟙p ⊕ P,
-- but its structure morphisms are head-and-tail vector operations rather than actions of the
-- block matrices, so evaluation costs constant work per position instead of a sum over the whole
-- dimension at every lifting layer.
open import Level using (0ℓ)
open import Data.Nat using (suc)
open import Data.Fin using (Fin; zero; suc)
open import prop using (∃ₛ) renaming (_,_ to _,ₚ_)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import cmon-enriched using (Biproduct)
open import lifting using (Lifting)
import lifting-biproduct
import matrix
import semimodule
import order-idempotent

module order-idempotent-roots
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
open order-idempotent S ∨-idem ∧-idem ⊤-add-top hiding (Lp; Lp-app-tail; Lp-fixed-tail)

open SemiMod._⇒_
open SemiMod._≈m_
open Biproduct

-- One position, so a selection of it is a scalar; the roots live here.
𝟙p : Pos
𝟙p = disc 1

-- The lifted order is the biproduct with the unit order, root first, so the lifted dimension and
-- the column layout agree with the dominated lifting it replaces.
Lp : Pos → Pos
Lp P = 𝟙p ⊕ P

-- Discrete orders fix every vector.
disc-fixed : ∀ {n} (v : M.Vec n) → Fixed (disc n) v
disc-fixed v i = M.Σ-unit i v

private
  cons : ∀ {n} → Setoid.Carrier A → M.Vec n → M.Vec (suc n)
  cons a u zero    = a
  cons a u (suc i) = u i

-- The action of the lifted order at the root and under it: the root row selects the root alone,
-- and the payload rows act as the payload order on the tail.
module _ (P : Pos) where

  private
    n = P .dim

    Σε : ∀ {m} (f : Fin m → Setoid.Carrier A) → M.Σ {m} (λ j → ε · f j) ≈ ε
    Σε {m} f = ≈-trans (M.Σ-cong {m} (λ j → ε-annihilₗ)) (M.Σ-ε {m})

    +ε : ∀ {x} → (x + ε) ≈ x
    +ε = ≈-trans +-comm +-lunit

  Lp-app-head : ∀ (v : M.Vec (suc n)) → app (Lp P .ord) v zero ≈ v zero
  Lp-app-head v =
    ≈-trans (app-+ₘ ((M.in₁ {1} {n}) ∘ₘ (𝟙p .ord) ∘ₘ (M.p₁ {1} {n}))
                    ((M.in₂ {1} {n}) ∘ₘ (P .ord) ∘ₘ (M.p₂ {1} {n})) v zero)
    (≈-trans (+-cong first second) +ε)
    where
    u = app (M.p₁ {1} {n}) v

    u-head : u zero ≈ v zero
    u-head =
      ≈-trans (+-cong ·-lunit (Σε {n} (λ j → v (suc j)))) +ε

    first : app ((M.in₁ {1} {n}) ∘ₘ (𝟙p .ord) ∘ₘ (M.p₁ {1} {n})) v zero ≈ v zero
    first =
      ≈-trans (app-∘ ((M.in₁ {1} {n}) ∘ₘ (𝟙p .ord)) (M.p₁ {1} {n}) v zero)
      (≈-trans (app-∘ (M.in₁ {1} {n}) (𝟙p .ord) u zero)
      (≈-trans (+-cong ·-lunit (M.Σ-ε {0}))
      (≈-trans +ε
      (≈-trans (+-cong ·-lunit (M.Σ-ε {0}))
      (≈-trans +ε u-head)))))

    second : app ((M.in₂ {1} {n}) ∘ₘ (P .ord) ∘ₘ (M.p₂ {1} {n})) v zero ≈ ε
    second =
      ≈-trans (app-∘ ((M.in₂ {1} {n}) ∘ₘ (P .ord)) (M.p₂ {1} {n}) v zero)
      (≈-trans (app-∘ (M.in₂ {1} {n}) (P .ord) (app (M.p₂ {1} {n}) v) zero)
               (Σε {n} _))

  Lp-app-tail : ∀ (v : M.Vec (suc n)) (i : Fin n) →
                app (Lp P .ord) v (suc i) ≈ app (P .ord) (tail v) i
  Lp-app-tail v i =
    ≈-trans (app-+ₘ ((M.in₁ {1} {n}) ∘ₘ (𝟙p .ord) ∘ₘ (M.p₁ {1} {n}))
                    ((M.in₂ {1} {n}) ∘ₘ (P .ord) ∘ₘ (M.p₂ {1} {n})) v (suc i))
    (≈-trans (+-cong first second) +-lunit)
    where
    u = app (M.p₁ {1} {n}) v

    u' = app (M.p₂ {1} {n}) v

    u'-tail : ∀ k → u' k ≈ v (suc k)
    u'-tail k =
      ≈-trans (+-cong ε-annihilₗ (M.Σ-unit k (λ j → v (suc j)))) +-lunit

    first : app ((M.in₁ {1} {n}) ∘ₘ (𝟙p .ord) ∘ₘ (M.p₁ {1} {n})) v (suc i) ≈ ε
    first =
      ≈-trans (app-∘ ((M.in₁ {1} {n}) ∘ₘ (𝟙p .ord)) (M.p₁ {1} {n}) v (suc i))
      (≈-trans (app-∘ (M.in₁ {1} {n}) (𝟙p .ord) u (suc i))
      (≈-trans (+-cong ε-annihilₗ (M.Σ-ε {0})) +-lunit))

    second : app ((M.in₂ {1} {n}) ∘ₘ (P .ord) ∘ₘ (M.p₂ {1} {n})) v (suc i)
               ≈ app (P .ord) (tail v) i
    second =
      ≈-trans (app-∘ ((M.in₂ {1} {n}) ∘ₘ (P .ord)) (M.p₂ {1} {n}) v (suc i))
      (≈-trans (app-∘ (M.in₂ {1} {n}) (P .ord) u' (suc i))
      (≈-trans (M.Σ-unit i (app (P .ord) u'))
               (M.Σ-cong {n} (λ j → ·-cong ≈-refl (u'-tail j)))))

  -- With the root isolated, a lifted selection is fixed exactly when its payload is; the root
  -- coordinate is unconstrained.
  Lp-fixed-tail : ∀ (v : M.Vec (suc n)) → Fixed (Lp P) v → Fixed P (tail v)
  Lp-fixed-tail v fx i = ≈-trans (≈-sym (Lp-app-tail v i)) (fx (suc i))

  Lp-fixed-cons : ∀ a {u : M.Vec n} → Fixed P u → Fixed (Lp P) (cons a u)
  Lp-fixed-cons a {u} fu zero    = Lp-app-head (cons a u)
  Lp-fixed-cons a {u} fu (suc i) = ≈-trans (Lp-app-tail (cons a u) i) (fu i)

-- The hand-written biproduct witness on (𝟙p, P): the block order as the product object, with
-- head-and-tail structure morphisms.
root-biproduct : ∀ P → Biproduct cmon 𝟙p P
root-biproduct P .prod = Lp P
root-biproduct P .p₁ .*→* .prop-setoid._⇒_.func (v ,ₚ _) =
  (λ _ → v zero) ,ₚ disc-fixed (λ _ → v zero)
root-biproduct P .p₁ .*→* .prop-setoid._⇒_.func-resp-≈ e i = e zero
root-biproduct P .p₁ .preserve-ze i = ≈-refl
root-biproduct P .p₁ .preserve-+ i = ≈-refl
root-biproduct P .p₁ .preserve-· i = ≈-refl
root-biproduct P .p₂ .*→* .prop-setoid._⇒_.func (v ,ₚ fx) =
  tail v ,ₚ Lp-fixed-tail P v fx
root-biproduct P .p₂ .*→* .prop-setoid._⇒_.func-resp-≈ e i = e (suc i)
root-biproduct P .p₂ .preserve-ze i = ≈-refl
root-biproduct P .p₂ .preserve-+ i = ≈-refl
root-biproduct P .p₂ .preserve-· i = ≈-refl
root-biproduct P .in₁ .*→* .prop-setoid._⇒_.func (s ,ₚ _) =
  cons (s zero) (λ _ → ε) ,ₚ Lp-fixed-cons P (s zero) (λ i → app-ε (P .ord) i)
root-biproduct P .in₁ .*→* .prop-setoid._⇒_.func-resp-≈ e = λ where
  zero    → e zero
  (suc i) → ≈-refl
root-biproduct P .in₁ .preserve-ze = λ where
  zero    → ≈-refl
  (suc i) → ≈-refl
root-biproduct P .in₁ .preserve-+ = λ where
  zero    → ≈-refl
  (suc i) → ≈-sym +-lunit
root-biproduct P .in₁ .preserve-· = λ where
  zero    → ≈-refl
  (suc i) → ≈-sym ε-annihilᵣ
root-biproduct P .in₂ .*→* .prop-setoid._⇒_.func (u ,ₚ fu) =
  cons ε u ,ₚ Lp-fixed-cons P ε fu
root-biproduct P .in₂ .*→* .prop-setoid._⇒_.func-resp-≈ e = λ where
  zero    → ≈-refl
  (suc i) → e i
root-biproduct P .in₂ .preserve-ze = λ where
  zero    → ≈-refl
  (suc i) → ≈-refl
root-biproduct P .in₂ .preserve-+ = λ where
  zero    → ≈-sym +-lunit
  (suc i) → ≈-refl
root-biproduct P .in₂ .preserve-· = λ where
  zero    → ≈-sym ε-annihilᵣ
  (suc i) → ≈-refl
root-biproduct P .id-1 .*≈* .prop-setoid._≃m_.func-eq e = λ { zero → e zero }
root-biproduct P .id-2 .*≈* .prop-setoid._≃m_.func-eq e i = e i
root-biproduct P .zero-1 .*≈* .prop-setoid._≃m_.func-eq e i = ≈-refl
root-biproduct P .zero-2 .*≈* .prop-setoid._≃m_.func-eq e i = ≈-refl
root-biproduct P .id-+ .*≈* .prop-setoid._≃m_.func-eq e = λ where
  zero    → ≈-trans (≈-trans +-comm +-lunit) (e zero)
  (suc i) → ≈-trans +-lunit (e (suc i))

module LpB = lifting-biproduct cmon 𝟙p root-biproduct

Lp-lifting : Lifting cmon 𝟙p
Lp-lifting = LpB.biproduct-lifting

-- Reading the root and dropping it are the projections.
tag : ∀ {P} → Lp P ⇒ 𝟙p
tag {P} = root-biproduct P .p₁

payload : ∀ {P} → Lp P ⇒ P
payload {P} = root-biproduct P .p₂
