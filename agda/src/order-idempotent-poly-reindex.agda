{-# OPTIONS --prop --postfix-projections --safe #-}

-- Changing the context commutes with the step that consumes a root. This is the law that failed for
-- the strength, where the root row of a lifted morphism was full and so picked up context the
-- reindexing had already discarded. Here the root column is data carried by the continuation, and a
-- change of context touches only the context component, so it passes through untouched.
open import Level using (0ℓ)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import cmon-enriched using (Biproduct; CMonEnriched)
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

open order-idempotent S ∨-idem ∧-idem ⊤-add-top
open order-idempotent-freeness S ∨-idem ∧-idem ⊤-add-top
open order-idempotent-poly-fold S ∨-idem ∧-idem ⊤-add-top

module _ (W W' R : Pos) (u : W' ⇒ W) where

  -- A change of context, leaving the payload alone.
  ctx-map : ∀ (F : Pos) → (W' ⊕ F) ⇒ (W ⊕ F)
  ctx-map F = Biproduct.pair (biproduct W F) (u ∘ π₁ W' F) (π₂ W' F)

  ctx-map-ι₁ : ∀ (F : Pos) → (ctx-map F ∘ ι₁ W' F) ≈p (ι₁ W F ∘ u)
  ctx-map-ι₁ F =
    ≈p-trans (Biproduct.pair-natural (biproduct W F) (u ∘ π₁ W' F) (π₂ W' F) (ι₁ W' F))
    (≈p-trans (Biproduct.pair-cong (biproduct W F)
                 {f₁ = (u ∘ π₁ W' F) ∘ ι₁ W' F} {f₂ = u}
                 {g₁ = π₂ W' F ∘ ι₁ W' F} {g₂ = εp {W'} {F}}
                 (≈p-trans (SMC.assoc u (π₁ W' F) (ι₁ W' F))
                           (≈p-trans (∘p-cong (≈p-refl {f = u})
                                             (Biproduct.id-1 (biproduct W' F)))
                                     (SMC.id-right {f = u})))
                 (Biproduct.zero-2 (biproduct W' F)))
              (bp-ι₁ W F u))
    where
    -- Pairing a morphism with the zero morphism is the first injection after it.
    bp-ι₁ : ∀ (X Y : Pos) {Z} (f : Z ⇒ X) →
            Biproduct.pair (biproduct X Y) f (εp {Z} {Y}) ≈p (ι₁ X Y ∘ f)
    bp-ι₁ X Y {Z} f =
      ≈p-trans (+p-cong (≈p-refl {f = ι₁ X Y ∘ f})
                        (CMonEnriched.comp-bilinear-ε₂ SemiMod.cmon-enriched (ι₂ X Y)))
               (+p-runit {f = ι₁ X Y ∘ f})

  ctx-map-ι₂ : ∀ (F : Pos) → (ctx-map F ∘ ι₂ W' F) ≈p ι₂ W F
  ctx-map-ι₂ F =
    ≈p-trans (Biproduct.pair-natural (biproduct W F) (u ∘ π₁ W' F) (π₂ W' F) (ι₂ W' F))
    (≈p-trans (Biproduct.pair-cong (biproduct W F)
                 {f₁ = (u ∘ π₁ W' F) ∘ ι₂ W' F} {f₂ = εp {F} {W}}
                 {g₁ = π₂ W' F ∘ ι₂ W' F} {g₂ = id F}
                 (≈p-trans (SMC.assoc u (π₁ W' F) (ι₂ W' F))
                           (≈p-trans (∘p-cong (≈p-refl {f = u})
                                             (Biproduct.zero-1 (biproduct W' F)))
                                     (CMonEnriched.comp-bilinear-ε₂ SemiMod.cmon-enriched u)))
                 (Biproduct.id-2 (biproduct W' F)))
              (bp-ι₂ W F))
    where
    bp-ι₂ : ∀ (X Y : Pos) → Biproduct.pair (biproduct X Y) (εp {Y} {X}) (id Y) ≈p ι₂ X Y
    bp-ι₂ X Y =
      ≈p-trans (+p-cong (CMonEnriched.comp-bilinear-ε₂ SemiMod.cmon-enriched (ι₁ X Y))
                        (SMC.id-right {f = ι₂ X Y}))
               (+p-lunit {f = ι₂ X Y})

  -- Two morphisms out of a biproduct agreeing on the injections are equal.
  biproduct-ext : ∀ (P Q : Pos) {T} (f g : (P ⊕ Q) ⇒ T) →
                  (f ∘ ι₁ P Q) ≈p (g ∘ ι₁ P Q) → (f ∘ ι₂ P Q) ≈p (g ∘ ι₂ P Q) → f ≈p g
  biproduct-ext P Q f g e₁ e₂ =
    ≈p-trans (≈p-sym (Biproduct.copair-ext (biproduct P Q) f))
    (≈p-trans (Biproduct.copair-cong (biproduct P Q)
                 {f₁ = f ∘ ι₁ P Q} {f₂ = g ∘ ι₁ P Q} {g₁ = f ∘ ι₂ P Q} {g₂ = g ∘ ι₂ P Q} e₁ e₂)
              (Biproduct.copair-ext (biproduct P Q) g))

  -- Copairing after a change of context: only the context component moves.
  cop-ctx : ∀ {F : Pos} (f : W ⇒ R) (g : F ⇒ R) →
            (cop f g ∘ ctx-map F) ≈p cop (f ∘ u) g
  cop-ctx {F} f g =
    biproduct-ext W' F (cop f g ∘ ctx-map F) (cop (f ∘ u) g)
      (≈p-trans (SMC.assoc (cop f g) (ctx-map F) (ι₁ W' F))
      (≈p-trans (∘p-cong (≈p-refl {f = cop f g}) (ctx-map-ι₁ F))
      (≈p-trans (≈p-sym (SMC.assoc (cop f g) (ι₁ W F) u))
      (≈p-trans (∘p-cong (Biproduct.copair-in₁ (biproduct W F) f g) (≈p-refl {f = u}))
                (≈p-sym (Biproduct.copair-in₁ (biproduct W' F) (f ∘ u) g))))))
      (≈p-trans (SMC.assoc (cop f g) (ctx-map F) (ι₂ W' F))
      (≈p-trans (∘p-cong (≈p-refl {f = cop f g}) (ctx-map-ι₂ F))
      (≈p-trans (Biproduct.copair-in₂ (biproduct W F) f g)
                (≈p-sym (Biproduct.copair-in₂ (biproduct W' F) (f ∘ u) g)))))

  -- The step that consumes a root commutes with a change of context: the constant it installs comes
  -- from the continuation's root column, which the change of context does not touch.
  rootStep-ctx : ∀ (X F : Pos) (k : (W ⊕ Lp X) ⇒ R) (r : (W ⊕ F) ⇒ R) →
                 (rootStep W R X F k r ∘ ctx-map (Lp F))
                 ≈p rootStep W' R X F (k ∘ ctx-map (Lp X)) (r ∘ ctx-map F)
  rootStep-ctx X F k r =
    ≈p-trans (cop-ctx (r ∘ ι₁ W F)
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
      ≈p-trans (SMC.assoc r (ι₁ W F) u)
      (≈p-trans (∘p-cong (≈p-refl {f = r}) (≈p-sym (ctx-map-ι₁ F)))
                (≈p-sym (SMC.assoc r (ctx-map F) (ι₁ W' F))))

    -- The payload component, and with it the constant, is unchanged.
    payload-eq : (r ∘ ι₂ W F) ≈p ((r ∘ ctx-map F) ∘ ι₂ W' F)
    payload-eq =
      ≈p-trans (∘p-cong (≈p-refl {f = r}) (≈p-sym (ctx-map-ι₂ F)))
               (≈p-sym (SMC.assoc r (ctx-map F) (ι₂ W' F)))

    constant : (k ∘ ι₂ W (Lp X)) ≈p ((k ∘ ctx-map (Lp X)) ∘ ι₂ W' (Lp X))
    constant =
      ≈p-trans (∘p-cong (≈p-refl {f = k}) (≈p-sym (ctx-map-ι₂ (Lp X))))
               (≈p-sym (SMC.assoc k (ctx-map (Lp X)) (ι₂ W' (Lp X))))

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
        payload-eq

  -- The projections of a change of context.
  ctx-map-π₁ : ∀ (F : Pos) → (π₁ W F ∘ ctx-map F) ≈p (u ∘ π₁ W' F)
  ctx-map-π₁ F = Biproduct.pair-p₁ (biproduct W F) (u ∘ π₁ W' F) (π₂ W' F)

  ctx-map-π₂ : ∀ (F : Pos) → (π₂ W F ∘ ctx-map F) ≈p π₂ W' F
  ctx-map-π₂ F = Biproduct.pair-p₂ (biproduct W F) (u ∘ π₁ W' F) (π₂ W' F)

  -- Feeding a folded sub-value commutes with a change of context.
  varStep-ctx : ∀ (X : Pos) (k : (W ⊕ R) ⇒ R) (g : (W ⊕ X) ⇒ R) →
                (varStep W R X k g ∘ ctx-map X)
                ≈p varStep W' R X (k ∘ ctx-map R) (g ∘ ctx-map X)
  varStep-ctx X k g =
    ≈p-trans (SMC.assoc k (Biproduct.pair (biproduct W R) (π₁ W X) g) (ctx-map X))
    (≈p-trans (∘p-cong (≈p-refl {f = k}) inner)
              (≈p-sym (SMC.assoc k (ctx-map R)
                             (Biproduct.pair (biproduct W' R) (π₁ W' X) (g ∘ ctx-map X)))))
    where
    -- Both sides pair the context, changed by u, with the folded sub-value.
    inner : (Biproduct.pair (biproduct W R) (π₁ W X) g ∘ ctx-map X)
            ≈p (ctx-map R ∘ Biproduct.pair (biproduct W' R) (π₁ W' X) (g ∘ ctx-map X))
    inner =
      ≈p-trans (Biproduct.pair-natural (biproduct W R) (π₁ W X) g (ctx-map X))
      (≈p-trans (Biproduct.pair-cong (biproduct W R)
                   {f₁ = π₁ W X ∘ ctx-map X} {f₂ = u ∘ π₁ W' X}
                   {g₁ = g ∘ ctx-map X} {g₂ = g ∘ ctx-map X}
                   (Biproduct.pair-p₁ (biproduct W X) (u ∘ π₁ W' X) (π₂ W' X))
                   (≈p-refl {f = g ∘ ctx-map X}))
                (≈p-sym right))
      where
      right : (ctx-map R ∘ Biproduct.pair (biproduct W' R) (π₁ W' X) (g ∘ ctx-map X))
              ≈p Biproduct.pair (biproduct W R) (u ∘ π₁ W' X) (g ∘ ctx-map X)
      right =
        ≈p-trans (Biproduct.pair-natural (biproduct W R) (u ∘ π₁ W' R) (π₂ W' R)
                    (Biproduct.pair (biproduct W' R) (π₁ W' X) (g ∘ ctx-map X)))
                 (Biproduct.pair-cong (biproduct W R)
                    {f₁ = (u ∘ π₁ W' R) ∘ Biproduct.pair (biproduct W' R) (π₁ W' X) (g ∘ ctx-map X)}
                    {f₂ = u ∘ π₁ W' X}
                    {g₁ = π₂ W' R ∘ Biproduct.pair (biproduct W' R) (π₁ W' X) (g ∘ ctx-map X)}
                    {g₂ = g ∘ ctx-map X}
                    (≈p-trans (SMC.assoc u (π₁ W' R)
                                 (Biproduct.pair (biproduct W' R) (π₁ W' X) (g ∘ ctx-map X)))
                              (∘p-cong (≈p-refl {f = u})
                                 (Biproduct.pair-p₁ (biproduct W' R) (π₁ W' X) (g ∘ ctx-map X))))
                    (Biproduct.pair-p₂ (biproduct W' R) (π₁ W' X) (g ∘ ctx-map X)))

  -- Pushing a change of context through the injections.
  push-ι₁ : ∀ (F : Pos) {T} (f : (W ⊕ F) ⇒ T) → ((f ∘ ι₁ W F) ∘ u) ≈p ((f ∘ ctx-map F) ∘ ι₁ W' F)
  push-ι₁ F f =
    ≈p-trans (SMC.assoc f (ι₁ W F) u)
    (≈p-trans (∘p-cong (≈p-refl {f = f}) (≈p-sym (ctx-map-ι₁ F)))
              (≈p-sym (SMC.assoc f (ctx-map F) (ι₁ W' F))))

  push-ι₂ : ∀ (F : Pos) {T} (f : (W ⊕ F) ⇒ T) → (f ∘ ι₂ W F) ≈p ((f ∘ ctx-map F) ∘ ι₂ W' F)
  push-ι₂ F f =
    ≈p-trans (∘p-cong (≈p-refl {f = f}) (≈p-sym (ctx-map-ι₂ F)))
             (≈p-sym (SMC.assoc f (ctx-map F) (ι₂ W' F)))

  -- The continuations at a product and at a root commute with a change of context.
  prodCont₁-ctx : ∀ (X₁ X₂ : Pos) (k : (W ⊕ (X₁ ⊕ X₂)) ⇒ R) →
                  (prodCont₁ W R X₁ X₂ k ∘ ctx-map X₁)
                  ≈p prodCont₁ W' R X₁ X₂ (k ∘ ctx-map (X₁ ⊕ X₂))
  prodCont₁-ctx X₁ X₂ k =
    ≈p-trans (cop-ctx (k ∘ ι₁ W (X₁ ⊕ X₂)) (k ∘ ι₂ W (X₁ ⊕ X₂) ∘ ι₁ X₁ X₂))
             (cop-cong W' X₁ R
               ((k ∘ ι₁ W (X₁ ⊕ X₂)) ∘ u) ((k ∘ ctx-map (X₁ ⊕ X₂)) ∘ ι₁ W' (X₁ ⊕ X₂))
               (k ∘ ι₂ W (X₁ ⊕ X₂) ∘ ι₁ X₁ X₂)
               ((k ∘ ctx-map (X₁ ⊕ X₂)) ∘ ι₂ W' (X₁ ⊕ X₂) ∘ ι₁ X₁ X₂)
               (push-ι₁ (X₁ ⊕ X₂) k)
               (∘p-cong (push-ι₂ (X₁ ⊕ X₂) k) (≈p-refl {f = ι₁ X₁ X₂})))

  prodCont₂-ctx : ∀ (X₁ X₂ : Pos) (k : (W ⊕ (X₁ ⊕ X₂)) ⇒ R) →
                  (prodCont₂ W R X₁ X₂ k ∘ ctx-map X₂)
                  ≈p prodCont₂ W' R X₁ X₂ (k ∘ ctx-map (X₁ ⊕ X₂))
  prodCont₂-ctx X₁ X₂ k =
    ≈p-trans (cop-ctx (εp {W} {R}) (k ∘ ι₂ W (X₁ ⊕ X₂) ∘ ι₂ X₁ X₂))
             (cop-cong W' X₂ R
               (εp {W} {R} ∘ u) (εp {W'} {R})
               (k ∘ ι₂ W (X₁ ⊕ X₂) ∘ ι₂ X₁ X₂)
               ((k ∘ ctx-map (X₁ ⊕ X₂)) ∘ ι₂ W' (X₁ ⊕ X₂) ∘ ι₂ X₁ X₂)
               (CMonEnriched.comp-bilinear-ε₁ SemiMod.cmon-enriched u)
               (∘p-cong (push-ι₂ (X₁ ⊕ X₂) k) (≈p-refl {f = ι₂ X₁ X₂})))

  rootCont-ctx : ∀ (X : Pos) (k : (W ⊕ Lp X) ⇒ R) →
                 (rootCont W R X k ∘ ctx-map X) ≈p rootCont W' R X (k ∘ ctx-map (Lp X))
  rootCont-ctx X k =
    ≈p-trans (cop-ctx (k ∘ ι₁ W (Lp X)) (body-of {P = X} (k ∘ ι₂ W (Lp X))))
             (cop-cong W' X R
               ((k ∘ ι₁ W (Lp X)) ∘ u) ((k ∘ ctx-map (Lp X)) ∘ ι₁ W' (Lp X))
               (body-of {P = X} (k ∘ ι₂ W (Lp X)))
               (body-of {P = X} ((k ∘ ctx-map (Lp X)) ∘ ι₂ W' (Lp X)))
               (push-ι₁ (Lp X) k)
               (body-of-cong {P = X} {C = R}
                 {h = k ∘ ι₂ W (Lp X)} {k = (k ∘ ctx-map (Lp X)) ∘ ι₂ W' (Lp X)}
                 (push-ι₂ (Lp X) k)))

  -- The additive split at a product commutes with a change of context, the context reaching the
  -- first component only, as it does on both sides.
  prodStep-ctx : ∀ (F₁ F₂ : Pos) (r₁ : (W ⊕ F₁) ⇒ R) (r₂ : (W ⊕ F₂) ⇒ R) →
                 (prodStep W R F₁ F₂ r₁ r₂ ∘ ctx-map (F₁ ⊕ F₂))
                 ≈p prodStep W' R F₁ F₂ (r₁ ∘ ctx-map F₁) (r₂ ∘ ctx-map F₂)
  prodStep-ctx F₁ F₂ r₁ r₂ =
    ≈p-trans (cop-ctx ((r₁ ∘ ι₁ W F₁) +p (r₂ ∘ ι₁ W F₂))
                      (cop (r₁ ∘ ι₂ W F₁) (r₂ ∘ ι₂ W F₂)))
             (cop-cong W' (F₁ ⊕ F₂) R
               (((r₁ ∘ ι₁ W F₁) +p (r₂ ∘ ι₁ W F₂)) ∘ u)
               (((r₁ ∘ ctx-map F₁) ∘ ι₁ W' F₁) +p ((r₂ ∘ ctx-map F₂) ∘ ι₁ W' F₂))
               (cop (r₁ ∘ ι₂ W F₁) (r₂ ∘ ι₂ W F₂))
               (cop ((r₁ ∘ ctx-map F₁) ∘ ι₂ W' F₁) ((r₂ ∘ ctx-map F₂) ∘ ι₂ W' F₂))
               (≈p-trans (CMonEnriched.comp-bilinear₁ SemiMod.cmon-enriched (r₁ ∘ ι₁ W F₁) (r₂ ∘ ι₁ W F₂) u)
                         (+p-cong (push-ι₁ F₁ r₁) (push-ι₁ F₂ r₂)))
               (cop-cong F₁ F₂ R
                 (r₁ ∘ ι₂ W F₁) ((r₁ ∘ ctx-map F₁) ∘ ι₂ W' F₁)
                 (r₂ ∘ ι₂ W F₂) ((r₂ ∘ ctx-map F₂) ∘ ι₂ W' F₂)
                 (push-ι₂ F₁ r₁) (push-ι₂ F₂ r₂)))
