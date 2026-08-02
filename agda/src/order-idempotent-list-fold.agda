{-# OPTIONS --prop --postfix-projections --safe #-}

-- The fused initial-algebra laws at one inductive type. The fibre of a list value is the spine
-- order: a cons cell lifts the element order together with the tail's fibre, and nil is a bare tag.
-- An algebra is branch data in the sense of order-idempotent-freeness: a context part, a constant,
-- and a linear part, the linear part of the cons branch acting on the element together with the
-- already-folded tail. The fold consumes each tag once, through the constant, and never rebuilds a
-- cell, so it never needs to map a cell in context, which is the map the lifting does not admit.
-- The laws come in two clauses per constructor, one for what the root alone determines and one for
-- the payload, and those two clauses pin the fold down.
open import Level using (0ℓ)
open import Data.Nat using (ℕ; zero; suc)
open import prop-setoid using (Setoid) renaming (_⇒_ to _⇒s_; _≃m_ to _≃s_)
open import commutative-semiring using (CommutativeSemiring)
open import commutative-monoid using (CommutativeMonoid)
open import cmon-enriched using (Biproduct)
import order-idempotent
import order-idempotent-freeness

module order-idempotent-list-fold
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (let open CommutativeSemiring S hiding (_≈_; trans; sym; refl); open Setoid A)
  (∨-idem    : ∀ {x} → x + x ≈ x)
  (∧-idem    : ∀ {x} → x · x ≈ x)
  (⊤-add-top : ∀ {x} → ι + x ≈ ι)
  where

open order-idempotent S ∨-idem ∧-idem ⊤-add-top
open order-idempotent-freeness S ∨-idem ∧-idem ⊤-add-top hiding (payload)
open SemiMod using (Semimodule)
open SemiMod._⇒_
open SemiMod._≈m_

-- The spine order of a list value of a given length.
Fib : Pos → ℕ → Pos
Fib E zero    = Lp 𝟘p
Fib E (suc n) = Lp (E ⊕ Fib E n)

cop : ∀ {P Q R} → P ⇒ R → Q ⇒ R → (P ⊕ Q) ⇒ R
cop {P} {Q} f g = Biproduct.copair (biproduct P Q) f g

⊕-map : ∀ {P Q P' Q'} → P ⇒ P' → Q ⇒ Q' → (P ⊕ Q) ⇒ (P' ⊕ Q')
⊕-map {P} {Q} {P'} {Q'} f g = Biproduct.pair (biproduct P' Q') (f ∘ π₁ P Q) (g ∘ π₂ P Q)

⊕-map-cong : ∀ {P Q P' Q'} (f f' : P ⇒ P') (g g' : Q ⇒ Q') →
             f ≈p f' → g ≈p g' → ⊕-map f g ≈p ⊕-map f' g'
⊕-map-cong {P} {Q} {P'} {Q'} f f' g g' ef eg =
  Biproduct.pair-cong (biproduct P' Q')
    {f₁ = f ∘ π₁ P Q} {f₂ = f' ∘ π₁ P Q} {g₁ = g ∘ π₂ P Q} {g₂ = g' ∘ π₂ P Q}
    (∘p-cong ef (≈p-refl {f = π₁ P Q}))
    (∘p-cong eg (≈p-refl {f = π₂ P Q}))

-- Two morphisms out of a biproduct agreeing on both injections are equal.
biproduct-ext : ∀ {P Q R} (f g : (P ⊕ Q) ⇒ R) →
                (f ∘ ι₁ P Q) ≈p (g ∘ ι₁ P Q) → (f ∘ ι₂ P Q) ≈p (g ∘ ι₂ P Q) → f ≈p g
biproduct-ext {P} {Q} f g e₁ e₂ =
  ≈p-trans (≈p-sym (Biproduct.copair-ext (biproduct P Q) f))
  (≈p-trans (Biproduct.copair-cong (biproduct P Q)
               {f₁ = f ∘ ι₁ P Q} {f₂ = g ∘ ι₁ P Q} {g₁ = f ∘ ι₂ P Q} {g₂ = g ∘ ι₂ P Q} e₁ e₂)
            (Biproduct.copair-ext (biproduct P Q) g))

-- The empty order has one selection, so any two morphisms out of it agree.
𝟘p-ext : ∀ {R} (f g : 𝟘p ⇒ R) → f ≈p g
𝟘p-ext {R} f g .*≈* ._≃s_.func-eq {x₁} {x₂} e i =
  trans (f .func-resp-≈ {x₁} {εsel} (λ ()) i)
  (trans (f .preserve-ze i)
  (trans (sym (g .preserve-ze i))
         (g .func-resp-≈ {εsel} {x₂} (λ ()) i)))
  where
  εsel = 𝒟 𝟘p .Semimodule.additive .CommutativeMonoid.ε

record ListAlg (W E R : Pos) : Set where
  field
    nil-ctx  : W ⇒ R
    nil-tag  : 𝟙p ⇒ R
    cons-ctx : W ⇒ R
    cons-tag : 𝟙p ⇒ R
    -- The cons branch reads the element together with the folded tail. The context reaches it
    -- through cons-ctx, never under the tag.
    cons-arg : (E ⊕ R) ⇒ R

module _ {W E R : Pos} (alg : ListAlg W E R) where

  open ListAlg alg

  -- What the cons branch determines from the payload, once the tail is folded, with the branch's
  -- constant joined in as absorption requires.
  cons-payload : ∀ n → (Fib E n ⇒ R) → (E ⊕ Fib E n) ⇒ R
  cons-payload n X = body-of (affine cons-tag (cons-arg ∘ ⊕-map (id E) X))

  cons-payload-cong : ∀ n (X Y : Fib E n ⇒ R) → X ≈p Y → cons-payload n X ≈p cons-payload n Y
  cons-payload-cong n X Y e =
    body-of-cong
      (affine-cong (≈p-refl {f = cons-tag})
        (∘p-cong (≈p-refl {f = cons-arg}) (⊕-map-cong (id E) (id E) X Y (≈p-refl {f = id E}) e)))

  -- The fold, in two components: what the context determines and what the value determines.
  cellf : ∀ n → Fib E n ⇒ R
  ctxf  : ℕ → W ⇒ R

  cellf zero    = affine nil-tag (εp {𝟘p} {R})
  cellf (suc n) = affine cons-tag (cons-arg ∘ ⊕-map (id E) (cellf n))

  ctxf zero    = nil-ctx
  ctxf (suc n) = cons-ctx +p (cons-arg ∘ ι₂ E R ∘ ctxf n)

  fold : ∀ n → (W ⊕ Fib E n) ⇒ R
  fold n = cop (ctxf n) (cellf n)

  -- The fused laws, on the two components. At each constructor the root clause fixes the constant
  -- and the payload clause fixes the linear part, with the tail folded by the same candidate. Nil
  -- has no payload, so its root clause is the whole story.
  record IsFold (hc : ℕ → W ⇒ R) (hf : ∀ n → Fib E n ⇒ R) : Prop where
    field
      nil-root  : (hf 0 ∘ root {𝟘p}) ≈p nil-tag
      nil-cxt   : hc 0 ≈p nil-ctx
      cons-root : ∀ n → (hf (suc n) ∘ root {E ⊕ Fib E n}) ≈p cons-tag
      cons-cxt  : ∀ n → hc (suc n) ≈p (cons-ctx +p (cons-arg ∘ ι₂ E R ∘ hc n))
      cons-arg-law : ∀ n → (hf (suc n) ∘ inj {E ⊕ Fib E n}) ≈p cons-payload n (hf n)

  open IsFold

  fold-is-fold : IsFold ctxf cellf
  fold-is-fold .nil-root =
    ≈p-trans (root-tag {P = 𝟘p} (cellf 0)) (affine-tag {P = 𝟘p} nil-tag (εp {𝟘p} {R}))
  fold-is-fold .nil-cxt = ≈p-refl {f = nil-ctx}
  fold-is-fold .cons-root n =
    ≈p-trans (root-tag {P = E ⊕ Fib E n} (cellf (suc n)))
             (affine-tag {P = E ⊕ Fib E n} cons-tag (cons-arg ∘ ⊕-map (id E) (cellf n)))
  fold-is-fold .cons-cxt n = ≈p-refl {f = ctxf (suc n)}
  fold-is-fold .cons-arg-law n = inj-body {P = E ⊕ Fib E n} (cellf (suc n))

  -- The decisive statement: the fused laws determine the fold. The value component of a candidate
  -- is reassembled from its two restrictions, and the tail is handled by the induction hypothesis.
  cell-unique : ∀ {hc kc : ℕ → W ⇒ R} {hf kf : ∀ n → Fib E n ⇒ R} →
                IsFold hc hf → IsFold kc kf → ∀ n → hf n ≈p kf n
  cell-unique {hf = hf} {kf} H K zero =
    lifting-ext {P = 𝟘p} (hf 0) (kf 0)
      (≈p-trans (H .nil-root) (≈p-sym (K .nil-root)))
      (𝟘p-ext (hf 0 ∘ inj {𝟘p}) (kf 0 ∘ inj {𝟘p}))
  cell-unique {hf = hf} {kf} H K (suc n) =
    lifting-ext {P = E ⊕ Fib E n} (hf (suc n)) (kf (suc n))
      (≈p-trans (H .cons-root n) (≈p-sym (K .cons-root n)))
      (≈p-trans (H .cons-arg-law n)
        (≈p-trans (cons-payload-cong n (hf n) (kf n) (cell-unique H K n))
                  (≈p-sym (K .cons-arg-law n))))

  ctx-unique : ∀ {hc kc : ℕ → W ⇒ R} {hf kf : ∀ n → Fib E n ⇒ R} →
               IsFold hc hf → IsFold kc kf → ∀ n → hc n ≈p kc n
  ctx-unique H K zero = ≈p-trans (H .nil-cxt) (≈p-sym (K .nil-cxt))
  ctx-unique {hc = hc} {kc} H K (suc n) =
    ≈p-trans (H .cons-cxt n)
    (≈p-trans (+p-cong (≈p-refl {f = cons-ctx})
                (∘p-cong (≈p-refl {f = cons-arg ∘ ι₂ E R}) (ctx-unique H K n)))
              (≈p-sym (K .cons-cxt n)))

  -- So any two candidates assemble to the same morphism out of the context paired with the value.
  fold-unique : ∀ {hc kc : ℕ → W ⇒ R} {hf kf : ∀ n → Fib E n ⇒ R} →
                IsFold hc hf → IsFold kc kf → ∀ n → cop (hc n) (hf n) ≈p cop (kc n) (kf n)
  fold-unique {hc = hc} {kc} {hf} {kf} H K n =
    Biproduct.copair-cong (biproduct W (Fib E n))
      {f₁ = hc n} {f₂ = kc n} {g₁ = hf n} {g₂ = kf n}
      (ctx-unique H K n) (cell-unique H K n)
