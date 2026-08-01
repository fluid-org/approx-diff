{-# OPTIONS --prop --postfix-projections --safe #-}

-- The fused initial-algebra laws over a grammar of shapes, generalising the list case. Every value
-- former carries a root position: the fibre of a value puts a root above each product and each
-- injection, so a selection of positions is a prefix of the value, and the bottom of a former is
-- distinct from the former applied to bottoms. The carrier interpretation carries the same roots,
-- so an algebra is an ordinary morphism out of it, which by freeness is a constant together with a
-- linear part at every node.
--
-- The fold never maps a tagged cell in context, the map the lifting does not admit. Instead it
-- applies the algebra to a payload whose recursive positions are already folded, splitting the
-- continuation where the structure demands: at a sum into its constant and its linear part, at a
-- product additively, so that the context is not counted twice.
open import Level using (0ℓ)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import cmon-enriched using (Biproduct)
import matrix
import order-idempotent
import order-idempotent-freeness

module order-idempotent-poly-fold
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (let open CommutativeSemiring S hiding (_≈_; trans; sym; refl); open Setoid A)
  (∨-idem    : ∀ {x} → x + x ≈ x)
  (∧-idem    : ∀ {x} → x · x ≈ x)
  (⊤-add-top : ∀ {x} → ι + x ≈ ι)
  where

open matrix.Mat S using (_≈ₘ_; ∘-cong)
open order-idempotent S ∨-idem ∧-idem ⊤-add-top
open order-idempotent-freeness S ∨-idem ∧-idem ⊤-add-top

infixr 30 _⊗_
infixr 25 _⊞_

data Poly : Set where
  konst : Pos → Poly
  var   : Poly
  _⊗_   : Poly → Poly → Poly
  _⊞_   : Poly → Poly → Poly

-- Values of the inductive type, and the index data of one layer: which branch each sum took, and
-- the sub-values at the recursive positions.
mutual
  data Val (B : Poly) : Set where
    sup : Shape B B → Val B

  data Shape (B : Poly) : Poly → Set where
    kon : ∀ {K} → Shape B (konst K)
    rec : Val B → Shape B var
    prd : ∀ {Q₁ Q₂} → Shape B Q₁ → Shape B Q₂ → Shape B (Q₁ ⊗ Q₂)
    inl : ∀ {Q₁ Q₂} → Shape B Q₁ → Shape B (Q₁ ⊞ Q₂)
    inr : ∀ {Q₁ Q₂} → Shape B Q₂ → Shape B (Q₁ ⊞ Q₂)

-- The fibre of a value: the positions of the branches taken, with a root above each sum.
mutual
  fibV : ∀ {B} → Val B → Pos
  fibV (sup s) = fibS s

  fibS : ∀ {B Q} → Shape B Q → Pos
  fibS (kon {K})   = K
  fibS (rec v)     = fibV v
  fibS (prd s₁ s₂) = Lp (fibS s₁ ⊕ fibS s₂)
  fibS (inl s)     = Lp (fibS s)
  fibS (inr s)     = Lp (fibS s)

cop : ∀ {P Q R} → P ⇒ R → Q ⇒ R → (P ⊕ Q) ⇒ R
cop {P} {Q} f g = Biproduct.copair (biproduct P Q) f g

-- The morphisms are explicit throughout: an equation of morphisms mentions them only under the
-- matrix projection, so they cannot be solved from one.
cop-cong : ∀ (P Q R : Pos) (f f' : P ⇒ R) (g g' : Q ⇒ R) →
           f ≈p f' → g ≈p g' → cop f g ≈p cop f' g'
cop-cong P Q R f f' g g' ef eg =
  Biproduct.copair-cong (biproduct P Q) {f₁ = f} {f₂ = f'} {g₁ = g} {g₂ = g'} ef eg

-- The carrier interpretation of a layer: the same structure, with the carrier at the recursive
-- positions and the roots kept.
sh : ∀ (R : Pos) {B Q} → Shape B Q → Pos
sh R (kon {K})   = K
sh R (rec v)     = R
sh R (prd s₁ s₂) = Lp (sh R s₁ ⊕ sh R s₂)
sh R (inl s)     = Lp (sh R s)
sh R (inr s)     = Lp (sh R s)

module _ (W R : Pos) where

  ⟦_⟧ : ∀ {B Q} → Shape B Q → Pos
  ⟦_⟧ = sh R

  -- One step of the recursion at each node. At a recursive position the folded sub-value is fed to
  -- the continuation with the context retained.
  varStep : ∀ (X : Pos) → (W ⊕ R) ⇒ R → (W ⊕ X) ⇒ R → (W ⊕ X) ⇒ R
  varStep X k g = k ∘ Biproduct.pair (biproduct W R) (π₁ W X) g

  varStep-cong : ∀ (X : Pos) (k : (W ⊕ R) ⇒ R) (g g' : (W ⊕ X) ⇒ R) →
                 g ≈p g' → varStep X k g ≈p varStep X k g'
  varStep-cong X k g g' e =
    ∘-cong (≈ₘ-refl {M = k .mat})
           (Biproduct.pair-cong (biproduct W R)
              {f₁ = π₁ W X} {f₂ = π₁ W X} {g₁ = g} {g₂ = g'}
              (≈ₘ-refl {M = π₁ W X .mat}) e)

  -- Under a root, a product splits the continuation additively, the context going to the first
  -- component only, so that it is not counted twice.
  prodCont₁ : ∀ (X₁ X₂ : Pos) → (W ⊕ (X₁ ⊕ X₂)) ⇒ R → (W ⊕ X₁) ⇒ R
  prodCont₁ X₁ X₂ k = cop (k ∘ ι₁ W (X₁ ⊕ X₂)) (k ∘ ι₂ W (X₁ ⊕ X₂) ∘ ι₁ X₁ X₂)

  prodCont₂ : ∀ (X₁ X₂ : Pos) → (W ⊕ (X₁ ⊕ X₂)) ⇒ R → (W ⊕ X₂) ⇒ R
  prodCont₂ X₁ X₂ k = cop (εp {W} {R}) (k ∘ ι₂ W (X₁ ⊕ X₂) ∘ ι₂ X₁ X₂)

  prodStep : ∀ (F₁ F₂ : Pos) → (W ⊕ F₁) ⇒ R → (W ⊕ F₂) ⇒ R → (W ⊕ (F₁ ⊕ F₂)) ⇒ R
  prodStep F₁ F₂ r₁ r₂ =
    cop ((r₁ ∘ ι₁ W F₁) +p (r₂ ∘ ι₁ W F₂)) (cop (r₁ ∘ ι₂ W F₁) (r₂ ∘ ι₂ W F₂))

  prodStep-cong : ∀ (F₁ F₂ : Pos) (r₁ r₁' : (W ⊕ F₁) ⇒ R) (r₂ r₂' : (W ⊕ F₂) ⇒ R) →
                  r₁ ≈p r₁' → r₂ ≈p r₂' → prodStep F₁ F₂ r₁ r₂ ≈p prodStep F₁ F₂ r₁' r₂'
  prodStep-cong F₁ F₂ r₁ r₁' r₂ r₂' e₁ e₂ =
    cop-cong W (F₁ ⊕ F₂) R
      ((r₁ ∘ ι₁ W F₁) +p (r₂ ∘ ι₁ W F₂)) ((r₁' ∘ ι₁ W F₁) +p (r₂' ∘ ι₁ W F₂))
      (cop (r₁ ∘ ι₂ W F₁) (r₂ ∘ ι₂ W F₂)) (cop (r₁' ∘ ι₂ W F₁) (r₂' ∘ ι₂ W F₂))
      (+ₘ-cong (∘-cong e₁ (≈ₘ-refl {M = ι₁ W F₁ .mat}))
               (∘-cong e₂ (≈ₘ-refl {M = ι₁ W F₂ .mat})))
      (cop-cong F₁ F₂ R (r₁ ∘ ι₂ W F₁) (r₁' ∘ ι₂ W F₁) (r₂ ∘ ι₂ W F₂) (r₂' ∘ ι₂ W F₂)
        (∘-cong e₁ (≈ₘ-refl {M = ι₂ W F₁ .mat}))
        (∘-cong e₂ (≈ₘ-refl {M = ι₂ W F₂ .mat})))

  -- At a root the continuation is split by freeness into its constant and its linear part. The
  -- constant is what the former alone determines and passes through untouched; the linear part
  -- becomes the continuation of the payload. No cell is rebuilt.
  rootCont : ∀ (X : Pos) → (W ⊕ Lp X) ⇒ R → (W ⊕ X) ⇒ R
  rootCont X k = cop (k ∘ ι₁ W (Lp X)) (body-of {P = X} (k ∘ ι₂ W (Lp X)))

  rootStep : ∀ (X F : Pos) → (W ⊕ Lp X) ⇒ R → (W ⊕ F) ⇒ R → (W ⊕ Lp F) ⇒ R
  rootStep X F k r =
    cop (r ∘ ι₁ W F) (affine {P = F} (tag-of {P = X} (k ∘ ι₂ W (Lp X))) (r ∘ ι₂ W F))

  rootStep-cong : ∀ (X F : Pos) (k : (W ⊕ Lp X) ⇒ R) (r r' : (W ⊕ F) ⇒ R) →
                 r ≈p r' → rootStep X F k r ≈p rootStep X F k r'
  rootStep-cong X F k r r' e =
    cop-cong W (Lp F) R (r ∘ ι₁ W F) (r' ∘ ι₁ W F)
      (affine {P = F} (tag-of {P = X} (k ∘ ι₂ W (Lp X))) (r ∘ ι₂ W F))
      (affine {P = F} (tag-of {P = X} (k ∘ ι₂ W (Lp X))) (r' ∘ ι₂ W F))
      (∘-cong e (≈ₘ-refl {M = ι₁ W F .mat}))
      (affine-cong {P = F} (≈ₘ-refl {M = tag-of {P = X} (k ∘ ι₂ W (Lp X)) .mat})
                   (∘-cong e (≈ₘ-refl {M = ι₂ W F .mat})))

  Cand : Poly → Set
  Cand B = (v : Val B) → (W ⊕ fibV v) ⇒ R

  -- Applying an algebra to a payload whose recursive positions have already been folded.
  applyG : ∀ {B} → Cand B → ∀ {Q} (s : Shape B Q) → (W ⊕ ⟦ s ⟧) ⇒ R → (W ⊕ fibS s) ⇒ R
  applyG f kon         k = k
  applyG f (rec v)     k = varStep (fibV v) k (f v)
  applyG f (prd s₁ s₂) k =
    rootStep (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) (fibS s₁ ⊕ fibS s₂) k
      (prodStep (fibS s₁) (fibS s₂)
        (applyG f s₁ (prodCont₁ ⟦ s₁ ⟧ ⟦ s₂ ⟧ (rootCont (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) k)))
        (applyG f s₂ (prodCont₂ ⟦ s₁ ⟧ ⟦ s₂ ⟧ (rootCont (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) k))))
  applyG f (inl s) k = rootStep ⟦ s ⟧ (fibS s) k (applyG f s (rootCont ⟦ s ⟧ k))
  applyG f (inr s) k = rootStep ⟦ s ⟧ (fibS s) k (applyG f s (rootCont ⟦ s ⟧ k))

  module _ {B : Poly} (alg : (s : Shape B B) → (W ⊕ ⟦ s ⟧) ⇒ R) where

    -- The fold repeats that recursion with itself at the recursive positions, which is what makes
    -- it structurally recursive.
    mutual
      fold : Cand B
      fold (sup s) = foldS s (alg s)

      foldS : ∀ {Q} (s : Shape B Q) → (W ⊕ ⟦ s ⟧) ⇒ R → (W ⊕ fibS s) ⇒ R
      foldS kon         k = k
      foldS (rec v)     k = varStep (fibV v) k (fold v)
      foldS (prd s₁ s₂) k =
        rootStep (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) (fibS s₁ ⊕ fibS s₂) k
          (prodStep (fibS s₁) (fibS s₂)
            (foldS s₁ (prodCont₁ ⟦ s₁ ⟧ ⟦ s₂ ⟧ (rootCont (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) k)))
            (foldS s₂ (prodCont₂ ⟦ s₁ ⟧ ⟦ s₂ ⟧ (rootCont (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) k))))
      foldS (inl s) k = rootStep ⟦ s ⟧ (fibS s) k (foldS s (rootCont ⟦ s ⟧ k))
      foldS (inr s) k = rootStep ⟦ s ⟧ (fibS s) k (foldS s (rootCont ⟦ s ⟧ k))

    -- The fused law: one equation per value, with the algebra applied to the folded payload.
    IsFold : Cand B → Prop
    IsFold h = ∀ (s : Shape B B) → h (sup s) ≈p applyG h s (alg s)

    -- The two shape recursions agree, so the fold satisfies the law.
    foldS-applyG : ∀ {Q} (s : Shape B Q) (k : (W ⊕ ⟦ s ⟧) ⇒ R) → foldS s k ≈p applyG fold s k
    foldS-applyG kon k = ≈ₘ-refl {M = k .mat}
    foldS-applyG (rec v) k = ≈ₘ-refl {M = varStep (fibV v) k (fold v) .mat}
    foldS-applyG (prd s₁ s₂) k =
      rootStep-cong (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) (fibS s₁ ⊕ fibS s₂) k
        (prodStep (fibS s₁) (fibS s₂)
          (foldS s₁ (prodCont₁ ⟦ s₁ ⟧ ⟦ s₂ ⟧ (rootCont (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) k)))
          (foldS s₂ (prodCont₂ ⟦ s₁ ⟧ ⟦ s₂ ⟧ (rootCont (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) k))))
        (prodStep (fibS s₁) (fibS s₂)
          (applyG fold s₁ (prodCont₁ ⟦ s₁ ⟧ ⟦ s₂ ⟧ (rootCont (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) k)))
          (applyG fold s₂ (prodCont₂ ⟦ s₁ ⟧ ⟦ s₂ ⟧ (rootCont (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) k))))
        (prodStep-cong (fibS s₁) (fibS s₂)
          (foldS s₁ (prodCont₁ ⟦ s₁ ⟧ ⟦ s₂ ⟧ (rootCont (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) k)))
          (applyG fold s₁ (prodCont₁ ⟦ s₁ ⟧ ⟦ s₂ ⟧ (rootCont (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) k)))
          (foldS s₂ (prodCont₂ ⟦ s₁ ⟧ ⟦ s₂ ⟧ (rootCont (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) k)))
          (applyG fold s₂ (prodCont₂ ⟦ s₁ ⟧ ⟦ s₂ ⟧ (rootCont (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) k)))
          (foldS-applyG s₁ (prodCont₁ ⟦ s₁ ⟧ ⟦ s₂ ⟧ (rootCont (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) k)))
          (foldS-applyG s₂ (prodCont₂ ⟦ s₁ ⟧ ⟦ s₂ ⟧ (rootCont (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) k))))
    foldS-applyG (inl s) k =
      rootStep-cong ⟦ s ⟧ (fibS s) k
        (foldS s (rootCont ⟦ s ⟧ k)) (applyG fold s (rootCont ⟦ s ⟧ k))
        (foldS-applyG s (rootCont ⟦ s ⟧ k))
    foldS-applyG (inr s) k =
      rootStep-cong ⟦ s ⟧ (fibS s) k
        (foldS s (rootCont ⟦ s ⟧ k)) (applyG fold s (rootCont ⟦ s ⟧ k))
        (foldS-applyG s (rootCont ⟦ s ⟧ k))

    fold-is-fold : IsFold fold
    fold-is-fold s = foldS-applyG s (alg s)

    -- The law determines the fold, by induction on the value together with its shape. There is no
    -- strength anywhere, and no separate extensionality law.
    mutual
      fold-unique : (h : Cand B) → IsFold h → ∀ v → h v ≈p fold v
      fold-unique h H (sup s) = ≈ₘ-trans (H s) (fold-uniqueS h H s (alg s))

      fold-uniqueS : (h : Cand B) → IsFold h → ∀ {Q} (s : Shape B Q) (k : (W ⊕ ⟦ s ⟧) ⇒ R) →
                     applyG h s k ≈p foldS s k
      fold-uniqueS h H kon k = ≈ₘ-refl {M = k .mat}
      fold-uniqueS h H (rec v) k = varStep-cong (fibV v) k (h v) (fold v) (fold-unique h H v)
      fold-uniqueS h H (prd s₁ s₂) k =
        rootStep-cong (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) (fibS s₁ ⊕ fibS s₂) k
          (prodStep (fibS s₁) (fibS s₂)
            (applyG h s₁ (prodCont₁ ⟦ s₁ ⟧ ⟦ s₂ ⟧ (rootCont (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) k)))
            (applyG h s₂ (prodCont₂ ⟦ s₁ ⟧ ⟦ s₂ ⟧ (rootCont (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) k))))
          (prodStep (fibS s₁) (fibS s₂)
            (foldS s₁ (prodCont₁ ⟦ s₁ ⟧ ⟦ s₂ ⟧ (rootCont (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) k)))
            (foldS s₂ (prodCont₂ ⟦ s₁ ⟧ ⟦ s₂ ⟧ (rootCont (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) k))))
          (prodStep-cong (fibS s₁) (fibS s₂)
            (applyG h s₁ (prodCont₁ ⟦ s₁ ⟧ ⟦ s₂ ⟧ (rootCont (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) k)))
            (foldS s₁ (prodCont₁ ⟦ s₁ ⟧ ⟦ s₂ ⟧ (rootCont (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) k)))
            (applyG h s₂ (prodCont₂ ⟦ s₁ ⟧ ⟦ s₂ ⟧ (rootCont (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) k)))
            (foldS s₂ (prodCont₂ ⟦ s₁ ⟧ ⟦ s₂ ⟧ (rootCont (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) k)))
            (fold-uniqueS h H s₁ (prodCont₁ ⟦ s₁ ⟧ ⟦ s₂ ⟧ (rootCont (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) k)))
            (fold-uniqueS h H s₂ (prodCont₂ ⟦ s₁ ⟧ ⟦ s₂ ⟧ (rootCont (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) k))))
      fold-uniqueS h H (inl s) k =
        rootStep-cong ⟦ s ⟧ (fibS s) k
          (applyG h s (rootCont ⟦ s ⟧ k)) (foldS s (rootCont ⟦ s ⟧ k))
          (fold-uniqueS h H s (rootCont ⟦ s ⟧ k))
      fold-uniqueS h H (inr s) k =
        rootStep-cong ⟦ s ⟧ (fibS s) k
          (applyG h s (rootCont ⟦ s ⟧ k)) (foldS s (rootCont ⟦ s ⟧ k))
          (fold-uniqueS h H s (rootCont ⟦ s ⟧ k))
