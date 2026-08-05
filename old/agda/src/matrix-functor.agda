{-# OPTIONS --prop --postfix-projections --safe #-}

-- Entrywise action of a map of scalars on matrices. A semiring homomorphism preserves identities,
-- transpose and composition exactly; a lax homomorphism into an additively idempotent semiring
-- preserves composition only laxly, E (M ∘ N) ⊑ E M ∘ E N pointwise in the target's additive
-- preorder.
module matrix-functor where

open import Level using (Level)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
open import prop-setoid using (Setoid)
open import categories using (Category)
open import commutative-semiring using (CommutativeSemiring; _⇒ˡ_; _⇒h_)
open import functor using (Functor)
import commutative-monoid
import matrix

-- The part common to both cases: the entrywise action preserves equality, identities and
-- transpose for any map of scalars respecting equality and the units.
module Entrywise
  {o₁ e₁ o₂ e₂ : Level} {A : Setoid o₁ e₁} {B : Setoid o₂ e₂}
  (S : CommutativeSemiring A) (T : CommutativeSemiring B)
  (f : Setoid.Carrier A → Setoid.Carrier B)
  (f-cong : ∀ {a b} → Setoid._≈_ A a b → Setoid._≈_ B (f a) (f b))
  (f-ε : Setoid._≈_ B (f (CommutativeSemiring.ε S)) (CommutativeSemiring.ε T))
  (f-ι : Setoid._≈_ B (f (CommutativeSemiring.ι S)) (CommutativeSemiring.ι T))
  where

  private
    module T = CommutativeSemiring T
    module Mat-S = matrix.Mat S
    module Mat-T = matrix.Mat T

  E : ∀ {m n} → Mat-S.Matrix m n → Mat-T.Matrix m n
  E M i j = f (M i j)

  E-cong : ∀ {m n} {M N : Mat-S.Matrix m n} → M Mat-S.≈ₘ N → E M Mat-T.≈ₘ E N
  E-cong e i j = f-cong (e i j)

  E-I : ∀ {n} → E (Mat-S.I {n}) Mat-T.≈ₘ Mat-T.I {n}
  E-I zero zero = f-ι
  E-I zero (suc j) = f-ε
  E-I (suc i) zero = f-ε
  E-I (suc i) (suc j) = E-I i j

  E-ᵀ : ∀ {m n} (M : Mat-S.Matrix m n) → E (M Mat-S.ᵀ) Mat-T.≈ₘ (E M Mat-T.ᵀ)
  E-ᵀ M i j = T.refl

-- A homomorphism acts functorially: composition is preserved exactly.
module Strict
  {o₁ e₁ o₂ e₂ : Level} {A : Setoid o₁ e₁} {B : Setoid o₂ e₂}
  {S : CommutativeSemiring A} {T : CommutativeSemiring B}
  (h : S ⇒h T)
  where

  private
    module S = CommutativeSemiring S
    module T = CommutativeSemiring T
    module Mat-S = matrix.Mat S
    module Mat-T = matrix.Mat T

  open _⇒h_ h
  open Entrywise S T f f-cong f-ε f-ι public

  private
    open Mat-T.+-to-Σ T._≈_ T.refl T.+-cong using (Σ-preserves)

    f-Σ : ∀ {n} (g : Fin n → S.Carrier) → f (Mat-S.Σ g) T.≈ Mat-T.Σ (λ i → f (g i))
    f-Σ {ℕ.zero} g = f-ε
    f-Σ {ℕ.suc n} g = T.trans f-+ (T.+-cong T.refl (f-Σ (λ i → g (suc i))))

  E-∘ : ∀ {m n k} (M : Mat-S.Matrix m n) (N : Mat-S.Matrix n k) →
        E (M Mat-S.∘ N) Mat-T.≈ₘ (E M Mat-T.∘ E N)
  E-∘ M N i j = T.trans (f-Σ (λ l → M i l S.· N l j)) (Σ-preserves (λ l → f-· {M i l} {N l j}))

  -- The entrywise action packaged as a functor, so that composing it with an embedding of matrices
  -- into a category inherits that embedding's laws instead of restating them.
  functor : Functor Mat-S.cat Mat-T.cat
  functor .Functor.fobj n = n
  functor .Functor.fmor = E
  functor .Functor.fmor-cong = E-cong
  functor .Functor.fmor-id = E-I
  functor .Functor.fmor-comp = E-∘

-- A lax homomorphism into an additively idempotent semiring acts laxly: composition is preserved
-- up to the additive preorder.
module Lax
  {o₁ e₁ o₂ e₂ : Level} {A : Setoid o₁ e₁} {B : Setoid o₂ e₂}
  {S : CommutativeSemiring A} {T : CommutativeSemiring B}
  (h : S ⇒ˡ T)
  (let module T = CommutativeSemiring T)
  (T-idem : ∀ {x} → (x T.+ x) T.≈ x)
  where

  private
    module S = CommutativeSemiring S
    module Mat-S = matrix.Mat S
    module Mat-T = matrix.Mat T

  open _⇒ˡ_ h
  open Entrywise S T f f-cong f-ε f-ι public
  open commutative-monoid.AdditivePreorder T.additive T-idem
    using (≈→⊑; ⊑-refl; ⊑-trans; +-mono-⊑)

  private
    open Mat-T.+-to-Σ _⊑_ ⊑-refl +-mono-⊑ using (Σ-preserves)

    f-Σ : ∀ {n} (g : Fin n → S.Carrier) → f (Mat-S.Σ g) ⊑ Mat-T.Σ (λ i → f (g i))
    f-Σ {ℕ.zero} g = ≈→⊑ f-ε
    f-Σ {ℕ.suc n} g = ⊑-trans f-+ (+-mono-⊑ ⊑-refl (f-Σ (λ i → g (suc i))))

  E-∘ : ∀ {m n k} (M : Mat-S.Matrix m n) (N : Mat-S.Matrix n k) →
        ∀ i j → E (M Mat-S.∘ N) i j ⊑ (E M Mat-T.∘ E N) i j
  E-∘ M N i j = ⊑-trans (f-Σ (λ l → M i l S.· N l j)) (Σ-preserves (λ l → f-· {M i l} {N l j}))
