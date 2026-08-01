{-# OPTIONS --prop --postfix-projections --safe #-}

-- The supported realisation of a position order: the semimodule of its fixed vectors, with the join
-- of the coordinates as the support. Realising a lifted order gives the lift of the realisation:
-- a fixed vector of Lp P is exactly a scalar dominating a fixed tail, which is an element of the
-- supported lift. This is the object-level comparison between the lifting on position orders and
-- the lifting on supported semimodules.
open import Level using (0ℓ)
open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_,_; _×_)
open import prop using (_∧_; ∃ₛ) renaming (_,_ to _,ₚ_)
open import prop-setoid using (Setoid; IsEquivalence)
open import commutative-monoid using (CommutativeMonoid)
open import commutative-semiring using (CommutativeSemiring)
open import categories using (Category)
import matrix
import semimodule
import order-idempotent
import order-idempotent-support
import supported-semimod

module order-idempotent-supported
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (let module S = CommutativeSemiring S)
  (∨-idem    : ∀ {x} → (x S.+ x) S.≈ x)
  (∧-idem    : ∀ {x} → (x S.· x) S.≈ x)
  (⊤-add-top : ∀ {x} → (S.ι S.+ x) S.≈ S.ι)
  where

module M = matrix.Mat S
module OI = order-idempotent S ∨-idem ∧-idem ⊤-add-top
module OS = order-idempotent-support S ∨-idem ∧-idem ⊤-add-top
module SemiMod = semimodule S
module SS = supported-semimod S ∨-idem

open OI using (Pos; dim; ord; Lp)
open SemiMod using (Semimodule; 𝕀; _⇒_)
open Semimodule
open SemiMod._⇒_
open SemiMod._≈m_

-- The action of a matrix is linear in the vector.
app-+ : ∀ {m n} (R : M.Matrix m n) (u v : M.Vec n) (i : Fin m) →
        OS.app R (λ j → u j S.+ v j) i S.≈ (OS.app R u i S.+ OS.app R v i)
app-+ {m} {n} R u v i =
  S.trans (M.Σ-cong {n} (λ j → S.·-+-distribₗ))
          (S.sym (M.Σ-+ {n} (λ j → R i j S.· u j) (λ j → R i j S.· v j)))

app-· : ∀ {m n} (R : M.Matrix m n) (s : S.Carrier) (u : M.Vec n) (i : Fin m) →
        OS.app R (λ j → s S.· u j) i S.≈ (s S.· OS.app R u i)
app-· {m} {n} R s u i =
  S.trans (M.Σ-cong {n} (λ j → S.trans (S.sym S.·-assoc)
                               (S.trans (S.·-cong S.·-comm S.refl) S.·-assoc)))
          (S.sym (M.Σ-·-distribₗ {n} s (λ j → R i j S.· u j)))

app-ε : ∀ {m n} (R : M.Matrix m n) (i : Fin m) → OS.app R (λ _ → S.ε) i S.≈ S.ε
app-ε {m} {n} R i = S.trans (M.Σ-cong {n} (λ j → S.ε-annihilᵣ)) (M.Σ-ε {n})

-- The semimodule of fixed vectors: the down-closed selections, pointwise.
𝓥sm : Pos → Semimodule
𝓥sm P .setoid .Setoid.Carrier = ∃ₛ (M.Vec (P .dim)) (OS.Fixed P)
𝓥sm P .setoid .Setoid._≈_ (u ,ₚ _) (v ,ₚ _) = ∀ i → u i S.≈ v i
𝓥sm P .setoid .Setoid.isEquivalence .IsEquivalence.refl i = S.refl
𝓥sm P .setoid .Setoid.isEquivalence .IsEquivalence.sym e i = S.sym (e i)
𝓥sm P .setoid .Setoid.isEquivalence .IsEquivalence.trans e e' i = S.trans (e i) (e' i)
𝓥sm P .additive .CommutativeMonoid.ε = (λ _ → S.ε) ,ₚ λ i → app-ε (P .ord) i
𝓥sm P .additive .CommutativeMonoid._+_ (u ,ₚ p) (v ,ₚ q) =
  (λ i → u i S.+ v i) ,ₚ λ i → S.trans (app-+ (P .ord) u v i) (S.+-cong (p i) (q i))
𝓥sm P .additive .CommutativeMonoid.+-cong e e' i = S.+-cong (e i) (e' i)
𝓥sm P .additive .CommutativeMonoid.+-lunit i = S.+-lunit
𝓥sm P .additive .CommutativeMonoid.+-assoc i = S.+-assoc
𝓥sm P .additive .CommutativeMonoid.+-comm i = S.+-comm
𝓥sm P ._·_ s (u ,ₚ p) =
  (λ i → s S.· u i) ,ₚ λ i → S.trans (app-· (P .ord) s u i) (S.·-cong S.refl (p i))
𝓥sm P .·-cong e e' i = S.·-cong e (e' i)
𝓥sm P .·-mul i = S.·-assoc
𝓥sm P .·-unit i = S.·-lunit
𝓥sm P .+-distribʳ i = S.·-+-distribᵣ
𝓥sm P .+-distribˡ i = S.·-+-distribₗ
𝓥sm P .zero-distribʳ i = S.ε-annihilₗ
𝓥sm P .zero-distribˡ i = S.ε-annihilᵣ

supp-𝓥 : ∀ P → 𝓥sm P ⇒ 𝕀
supp-𝓥 P .*→* .prop-setoid._⇒_.func (u ,ₚ _) = OS.supp {P .dim} u
supp-𝓥 P .*→* .prop-setoid._⇒_.func-resp-≈ e = M.Σ-cong e
supp-𝓥 P .preserve-ze = M.Σ-ε {P .dim}
supp-𝓥 P .preserve-+ {u ,ₚ _} {v ,ₚ _} = S.sym (M.Σ-+ {P .dim} u v)
supp-𝓥 P .preserve-· {s} {u ,ₚ _} = S.sym (M.Σ-·-distribₗ {P .dim} s u)

-- The supported object of a position order.
𝓥 : Pos → SS.Sup.Obj
𝓥 P .SS.Sup.carrier = 𝓥sm P
𝓥 P .SS.Sup.supp = supp-𝓥 P

private
  cons : ∀ {n} → S.Carrier → M.Vec n → M.Vec (suc n)
  cons a u zero    = a
  cons a u (suc i) = u i

-- Realising a lifted order is lifting the realisation: head and tail against pairing.
𝓥-Lp-fwd : ∀ P → SS.Sup.Mor (𝓥 (Lp P)) (SS.Ls (𝓥 P))
𝓥-Lp-fwd P .SS.Sup.mor .*→* .prop-setoid._⇒_.func (v ,ₚ fx) =
  (v zero , (OS.tail v ,ₚ OS.Lp-fixed-tail P v fx)) ,ₚ OS.Lp-fixed-root P v fx
𝓥-Lp-fwd P .SS.Sup.mor .*→* .prop-setoid._⇒_.func-resp-≈ e = e zero ,ₚ λ i → e (suc i)
𝓥-Lp-fwd P .SS.Sup.mor .preserve-ze = S.refl ,ₚ λ i → S.refl
𝓥-Lp-fwd P .SS.Sup.mor .preserve-+ = S.refl ,ₚ λ i → S.refl
𝓥-Lp-fwd P .SS.Sup.mor .preserve-· = S.refl ,ₚ λ i → S.refl
𝓥-Lp-fwd P .SS.Sup.bound .*≈* .prop-setoid._≃m_.func-eq {v₁ ,ₚ _} {v₂ ,ₚ _} e =
  S.trans (OI.L.Σ-ub v₁ zero) (M.Σ-cong e)

𝓥-Lp-bwd : ∀ P → SS.Sup.Mor (SS.Ls (𝓥 P)) (𝓥 (Lp P))
𝓥-Lp-bwd P .SS.Sup.mor .*→* .prop-setoid._⇒_.func ((a , (u ,ₚ fu)) ,ₚ dom) =
  cons a u ,ₚ OS.Lp-fixed P (cons a u) fu dom
𝓥-Lp-bwd P .SS.Sup.mor .*→* .prop-setoid._⇒_.func-resp-≈ (e₁ ,ₚ e₂) = λ where
  zero    → e₁
  (suc i) → e₂ i
𝓥-Lp-bwd P .SS.Sup.mor .preserve-ze = λ where
  zero    → S.refl
  (suc i) → S.refl
𝓥-Lp-bwd P .SS.Sup.mor .preserve-+ = λ where
  zero    → S.refl
  (suc i) → S.refl
𝓥-Lp-bwd P .SS.Sup.mor .preserve-· = λ where
  zero    → S.refl
  (suc i) → S.refl
𝓥-Lp-bwd P .SS.Sup.bound .*≈* .prop-setoid._≃m_.func-eq
    {(a₁ , (u₁ ,ₚ _)) ,ₚ _} {(a₂ , (u₂ ,ₚ _)) ,ₚ dom₂} (e₁ ,ₚ e₂) =
  S.trans S.+-comm
  (S.trans (S.sym S.+-assoc)
  (S.trans (S.+-cong ∨-idem S.refl)
  (S.trans S.+-comm
  (S.trans (S.+-cong (M.Σ-cong e₂) e₁) dom₂))))

𝓥-Lp-iso : ∀ P → Category.Iso SS.Sup.cat (𝓥 (Lp P)) (SS.Ls (𝓥 P))
𝓥-Lp-iso P .Category.Iso.fwd = 𝓥-Lp-fwd P
𝓥-Lp-iso P .Category.Iso.bwd = 𝓥-Lp-bwd P
𝓥-Lp-iso P .Category.Iso.fwd∘bwd≈id .*≈* .prop-setoid._≃m_.func-eq e = e
𝓥-Lp-iso P .Category.Iso.bwd∘fwd≈id .*≈* .prop-setoid._≃m_.func-eq e = λ where
  zero    → e zero
  (suc i) → e (suc i)
