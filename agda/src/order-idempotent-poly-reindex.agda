{-# OPTIONS --prop --postfix-projections --safe #-}

-- Changing the context commutes with the step that consumes a root. This is the law that failed for
-- the strength, where the root row of a lifted morphism was full and so picked up context the
-- reindexing had already discarded. Here the root column is data carried by the continuation, and a
-- change of context touches only the context component, so it passes through untouched.
open import Level using (0ℓ)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import cmon-enriched using (Biproduct)
import matrix
import order-idempotent
import order-idempotent-freeness
import order-idempotent-poly-fold

module order-idempotent-poly-reindex
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (let open CommutativeSemiring S hiding (_≈_; trans; sym; refl); open Setoid A)
  (∨-idem    : ∀ {x} → x + x ≈ x)
  (∧-idem    : ∀ {x} → x · x ≈ x)
  (⊤-add-top : ∀ {x} → ι + x ≈ ι)
  where

open matrix.Mat S using (_≈ₘ_; ∘-cong; assoc; comp-bilinear-ε₂)
open order-idempotent S ∨-idem ∧-idem ⊤-add-top
open order-idempotent-freeness S ∨-idem ∧-idem ⊤-add-top
open order-idempotent-poly-fold S ∨-idem ∧-idem ⊤-add-top

module _ (W W' R : Pos) (u : W' ⇒ W) where

  -- A change of context, leaving the payload alone.
  ctx-map : ∀ (F : Pos) → (W' ⊕ F) ⇒ (W ⊕ F)
  ctx-map F = Biproduct.pair (biproduct W F) (u ∘ π₁ W' F) (π₂ W' F)

  ctx-map-ι₁ : ∀ (F : Pos) → (ctx-map F ∘ ι₁ W' F) ≈p (ι₁ W F ∘ u)
  ctx-map-ι₁ F =
    ≈ₘ-trans (Biproduct.pair-natural (biproduct W F) (u ∘ π₁ W' F) (π₂ W' F) (ι₁ W' F))
    (≈ₘ-trans (Biproduct.pair-cong (biproduct W F)
                 {f₁ = (u ∘ π₁ W' F) ∘ ι₁ W' F} {f₂ = u}
                 {g₁ = π₂ W' F ∘ ι₁ W' F} {g₂ = εp {W'} {F}}
                 (≈ₘ-trans (assoc (u .mat) (π₁ W' F .mat) (ι₁ W' F .mat))
                           (≈ₘ-trans (∘-cong (≈ₘ-refl {M = u .mat})
                                             (Biproduct.id-1 (biproduct W' F)))
                                     (absorb-right u)))
                 (Biproduct.zero-2 (biproduct W' F)))
              (bp-ι₁ W F u))
    where
    -- Pairing a morphism with the zero morphism is the first injection after it.
    bp-ι₁ : ∀ (X Y : Pos) {Z} (f : Z ⇒ X) →
            Biproduct.pair (biproduct X Y) f (εp {Z} {Y}) ≈p (ι₁ X Y ∘ f)
    bp-ι₁ X Y f q p =
      trans (+-cong refl (comp-bilinear-ε₂ (ι₂ X Y .mat) q p)) (trans +-comm +-lunit)

  ctx-map-ι₂ : ∀ (F : Pos) → (ctx-map F ∘ ι₂ W' F) ≈p ι₂ W F
  ctx-map-ι₂ F =
    ≈ₘ-trans (Biproduct.pair-natural (biproduct W F) (u ∘ π₁ W' F) (π₂ W' F) (ι₂ W' F))
    (≈ₘ-trans (Biproduct.pair-cong (biproduct W F)
                 {f₁ = (u ∘ π₁ W' F) ∘ ι₂ W' F} {f₂ = εp {F} {W}}
                 {g₁ = π₂ W' F ∘ ι₂ W' F} {g₂ = id F}
                 (≈ₘ-trans (assoc (u .mat) (π₁ W' F .mat) (ι₂ W' F .mat))
                           (≈ₘ-trans (∘-cong (≈ₘ-refl {M = u .mat})
                                             (Biproduct.zero-1 (biproduct W' F)))
                                     (comp-bilinear-ε₂ (u .mat))))
                 (Biproduct.id-2 (biproduct W' F)))
              (bp-ι₂ W F))
    where
    bp-ι₂ : ∀ (X Y : Pos) → Biproduct.pair (biproduct X Y) (εp {Y} {X}) (id Y) ≈p ι₂ X Y
    bp-ι₂ X Y =
      ≈ₘ-trans (λ q p → trans (+-cong (comp-bilinear-ε₂ (ι₁ X Y .mat) q p) refl) +-lunit)
               (absorb-right (ι₂ X Y))

  -- Two morphisms out of a biproduct agreeing on the injections are equal.
  biproduct-ext : ∀ (P Q : Pos) {T} (f g : (P ⊕ Q) ⇒ T) →
                  (f ∘ ι₁ P Q) ≈p (g ∘ ι₁ P Q) → (f ∘ ι₂ P Q) ≈p (g ∘ ι₂ P Q) → f ≈p g
  biproduct-ext P Q f g e₁ e₂ =
    ≈ₘ-trans (≈ₘ-sym (Biproduct.copair-ext (biproduct P Q) f))
    (≈ₘ-trans (Biproduct.copair-cong (biproduct P Q)
                 {f₁ = f ∘ ι₁ P Q} {f₂ = g ∘ ι₁ P Q} {g₁ = f ∘ ι₂ P Q} {g₂ = g ∘ ι₂ P Q} e₁ e₂)
              (Biproduct.copair-ext (biproduct P Q) g))

  -- Copairing after a change of context: only the context component moves.
  cop-ctx : ∀ {F : Pos} (f : W ⇒ R) (g : F ⇒ R) →
            (cop f g ∘ ctx-map F) ≈p cop (f ∘ u) g
  cop-ctx {F} f g =
    biproduct-ext W' F (cop f g ∘ ctx-map F) (cop (f ∘ u) g)
      (≈ₘ-trans (assoc (cop f g .mat) (ctx-map F .mat) (ι₁ W' F .mat))
      (≈ₘ-trans (∘-cong (≈ₘ-refl {M = cop f g .mat}) (ctx-map-ι₁ F))
      (≈ₘ-trans (≈ₘ-sym (assoc (cop f g .mat) (ι₁ W F .mat) (u .mat)))
      (≈ₘ-trans (∘-cong (Biproduct.copair-in₁ (biproduct W F) f g) (≈ₘ-refl {M = u .mat}))
                (≈ₘ-sym (Biproduct.copair-in₁ (biproduct W' F) (f ∘ u) g))))))
      (≈ₘ-trans (assoc (cop f g .mat) (ctx-map F .mat) (ι₂ W' F .mat))
      (≈ₘ-trans (∘-cong (≈ₘ-refl {M = cop f g .mat}) (ctx-map-ι₂ F))
      (≈ₘ-trans (Biproduct.copair-in₂ (biproduct W F) f g)
                (≈ₘ-sym (Biproduct.copair-in₂ (biproduct W' F) (f ∘ u) g)))))

  -- The step that consumes a root commutes with a change of context: the constant it installs comes
  -- from the continuation's root column, which the change of context does not touch.
  rootStep-ctx : ∀ (X F : Pos) (k : (W ⊕ Lp X) ⇒ R) (r : (W ⊕ F) ⇒ R) →
                 (rootStep W R X F k r ∘ ctx-map (Lp F))
                 ≈p rootStep W' R X F (k ∘ ctx-map (Lp X)) (r ∘ ctx-map F)
  rootStep-ctx X F k r =
    ≈ₘ-trans (cop-ctx (r ∘ ι₁ W F)
                      (affine {P = F} (tag-of {P = X} (k ∘ ι₂ W (Lp X))) (r ∘ ι₂ W F)))
             (cop-cong W' (Lp F) R
               ((r ∘ ι₁ W F) ∘ u) ((r ∘ ctx-map F) ∘ ι₁ W' F)
               (affine {P = F} (tag-of {P = X} (k ∘ ι₂ W (Lp X))) (r ∘ ι₂ W F))
               (affine {P = F} (tag-of {P = X} ((k ∘ ctx-map (Lp X)) ∘ ι₂ W' (Lp X)))
                       ((r ∘ ctx-map F) ∘ ι₂ W' F))
               ctx-part cell-part)
    where
    ctx-part : ((r ∘ ι₁ W F) ∘ u) ≈p ((r ∘ ctx-map F) ∘ ι₁ W' F)
    ctx-part =
      ≈ₘ-trans (assoc (r .mat) (ι₁ W F .mat) (u .mat))
      (≈ₘ-trans (∘-cong (≈ₘ-refl {M = r .mat}) (≈ₘ-sym (ctx-map-ι₁ F)))
                (≈ₘ-sym (assoc (r .mat) (ctx-map F .mat) (ι₁ W' F .mat))))

    -- The payload component, and with it the constant, is unchanged.
    payload : (r ∘ ι₂ W F) ≈p ((r ∘ ctx-map F) ∘ ι₂ W' F)
    payload =
      ≈ₘ-trans (∘-cong (≈ₘ-refl {M = r .mat}) (≈ₘ-sym (ctx-map-ι₂ F)))
               (≈ₘ-sym (assoc (r .mat) (ctx-map F .mat) (ι₂ W' F .mat)))

    constant : (k ∘ ι₂ W (Lp X)) ≈p ((k ∘ ctx-map (Lp X)) ∘ ι₂ W' (Lp X))
    constant =
      ≈ₘ-trans (∘-cong (≈ₘ-refl {M = k .mat}) (≈ₘ-sym (ctx-map-ι₂ (Lp X))))
               (≈ₘ-sym (assoc (k .mat) (ctx-map (Lp X) .mat) (ι₂ W' (Lp X) .mat)))

    cell-part : affine {P = F} (tag-of {P = X} (k ∘ ι₂ W (Lp X))) (r ∘ ι₂ W F)
                ≈p affine {P = F} (tag-of {P = X} ((k ∘ ctx-map (Lp X)) ∘ ι₂ W' (Lp X)))
                          ((r ∘ ctx-map F) ∘ ι₂ W' F)
    cell-part =
      affine-cong {P = F} {C = R}
        {c = tag-of {P = X} (k ∘ ι₂ W (Lp X))}
        {c' = tag-of {P = X} ((k ∘ ctx-map (Lp X)) ∘ ι₂ W' (Lp X))}
        {M = r ∘ ι₂ W F} {M' = (r ∘ ctx-map F) ∘ ι₂ W' F}
        (tag-of-cong {P = X} {C = R}
          {h = k ∘ ι₂ W (Lp X)} {k = (k ∘ ctx-map (Lp X)) ∘ ι₂ W' (Lp X)} constant)
        payload
