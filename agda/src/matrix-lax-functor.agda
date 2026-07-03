{-# OPTIONS --prop --postfix-projections --safe #-}

-- A lax semiring homomorphism h : S ⇒ˡ T with additively idempotent T acts entrywise on matrices,
-- preserving identities and transpose exactly and composition laxly: E (M ∘ N) ⊑ E M ∘ E N pointwise,
-- in the target's additive preorder.
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring; _⇒ˡ_)

module matrix-lax-functor
  {o₁ e₁ o₂ e₂} {A : Setoid o₁ e₁} {B : Setoid o₂ e₂}
  {S : CommutativeSemiring A} {T : CommutativeSemiring B}
  (h : S ⇒ˡ T)
  (let module T = CommutativeSemiring T)
  (T-idem : ∀ {x} → (x T.+ x) T.≈ x)
  where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
import matrix

private
  module S = CommutativeSemiring S
  module SM = matrix.Mat S
  module TM = matrix.Mat T

open _⇒ˡ_ h

≈→⊑ : ∀ {x y} → x T.≈ y → x ⊑ y
≈→⊑ e = T.trans (T.+-cong e T.refl) T-idem

⊑-refl : ∀ {x} → x ⊑ x
⊑-refl = ≈→⊑ T.refl

⊑-trans : ∀ {x y z} → x ⊑ y → y ⊑ z → x ⊑ z
⊑-trans p q =
  T.trans (T.+-cong T.refl (T.sym q))
    (T.trans (T.sym T.+-assoc) (T.trans (T.+-cong p T.refl) q))

+-mono-⊑ : ∀ {x₁ x₂ y₁ y₂} → x₁ ⊑ y₁ → x₂ ⊑ y₂ → (x₁ T.+ x₂) ⊑ (y₁ T.+ y₂)
+-mono-⊑ {x₁} {x₂} {y₁} {y₂} p q =
  T.trans T.+-assoc
    (T.trans (T.+-cong T.refl (T.trans (T.sym T.+-assoc)
      (T.trans (T.+-cong T.+-comm T.refl) T.+-assoc)))
      (T.trans (T.sym T.+-assoc) (T.+-cong p q)))

private
  open TM.+-to-Σ _⊑_ ⊑-refl +-mono-⊑ using (Σ-preserves)

  f-Σ : ∀ {n} (g : Fin n → S.Carrier) → f (SM.Σ g) ⊑ TM.Σ (λ i → f (g i))
  f-Σ {ℕ.zero} g = ≈→⊑ f-ε
  f-Σ {ℕ.suc n} g = ⊑-trans f-+ (+-mono-⊑ ⊑-refl (f-Σ (λ i → g (suc i))))

-- The entrywise action.
E : ∀ {m n} → SM.Matrix m n → TM.Matrix m n
E M i j = f (M i j)

E-cong : ∀ {m n} {M N : SM.Matrix m n} → M SM.≈ₘ N → E M TM.≈ₘ E N
E-cong e i j = f-cong (e i j)

E-I : ∀ {n} → E (SM.I {n}) TM.≈ₘ TM.I {n}
E-I zero zero = f-ι
E-I zero (suc j) = f-ε
E-I (suc i) zero = f-ε
E-I (suc i) (suc j) = E-I i j

E-ᵀ : ∀ {m n} (M : SM.Matrix m n) → E (M SM.ᵀ) TM.≈ₘ (E M TM.ᵀ)
E-ᵀ M i j = T.refl

E-∘ : ∀ {m n k} (M : SM.Matrix m n) (N : SM.Matrix n k) →
      ∀ i j → E (M SM.∘ N) i j ⊑ (E M TM.∘ E N) i j
E-∘ M N i j = ⊑-trans (f-Σ (λ l → M i l S.· N l j)) (Σ-preserves (λ l → f-· {M i l} {N l j}))
